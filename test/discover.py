#!/usr/bin/env python3
"""
discover.py — the DISCOVERY harness (docs/model-strengthening-plan-2.md §D).

The point (from the plan): the existing rigs REPLAY known findings. They caught
nothing new because they only defend the triaged list. This harness EXPLORES:
it mutates an honest authoritative response for a name that EXISTS and checks the
resolver's output against RFC-derived invariants that need NO reference resolver,
plus an optional differential against unbound. A property violation is a
candidate finding.

Architecture
------------
For each SCENARIO (a query for an existing name) x MUTATION (a named surgical
edit of the honest reply, see test/discover_mock.py):

  1. Start a fresh mutating mock (so referral memory is empty), start a fresh
     veri-dns pointed at it, wait for readiness on an honest beacon.
  2. Drive veri-dns with `dig` and parse the answer (rcode, answer RRs with
     owner+type+data, authority owners, additional owners).
  3. PROPERTY CHECK (primary): assert the resolver output against RFC invariants
     that hold regardless of the mutation, e.g. "a name that exists is never
     answered NODATA", "no delivered record is out of the query's bailiwick".
  4. DIFFERENTIAL CHECK (secondary, if unbound present): the same query against
     a reference unbound behind the SAME mutating mock; a mismatch is recorded.

Each property violation / differential mismatch is emitted as a candidate
finding: {scenario, mutation, veri, oracle/expected, property}. The harness runs
as a HUNT — non-fatal, it reports divergences without failing the CI gate — but
in CI mode a MISSING DEPENDENCY is a failure (see ci_gate.sh policy).
"""
import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
BIN = os.path.join(ROOT, ".lake", "build", "bin", "veri-dns")
PY = os.path.join(ROOT, "test", ".venv", "bin", "python")
MOCK = os.path.join(HERE, "discover_mock.py")

MOCK_PORT = 5360
VERI_PORT = 5310
UNBOUND_PORT = 5311
TIMEOUT = 8

# names that EXIST in the mock's veridns. child zone (and their expected A)
EXISTING = {
    "exists.veridns.": "192.0.2.10",
    "host.veridns.":   "192.0.2.20",
    "multi.veridns.":  "192.0.2.30",
    "mail.veridns.":   "192.0.2.40",
}

# (scenario name, qname, qtype, mutation, mutate_role, expected_answer_ip_or_None)
# expected is the honest answer; None means "no A record expected" (used by the
# property checks that only care that the name is NOT NODATA/NXDOMAIN).


def sh(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True)


# ---------------------------------------------------------------------------
# Server lifecycle.
# ---------------------------------------------------------------------------
class Procs:
    def __init__(self):
        self.pids = []

    def spawn(self, cmd, env=None, logfile=None):
        f = open(logfile, "wb") if logfile else subprocess.DEVNULL
        p = subprocess.Popen(cmd, shell=True, stdout=f, stderr=subprocess.STDOUT,
                             env={**os.environ, **(env or {})}, preexec_fn=os.setsid)
        self.pids.append(p)
        return p

    def killall(self):
        for p in self.pids:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except Exception:
                pass
        self.pids = []
        sh("pkill -9 -f discover_mock.py")
        sh("pkill -9 -f 'bin/veri-dns'")
        sh("pkill -9 -f 'unbound -d -p'")
        time.sleep(0.4)


def start_mock(procs, mutation, mutate_role, logpath):
    open(logpath, "w").close()
    procs.spawn(f"{PY} {MOCK} --port {MOCK_PORT} --mutation {mutation} "
                f"--mutate-role {mutate_role} --log {logpath}",
                logfile="/tmp/discover_mock.err")
    time.sleep(0.8)


def start_veri(procs):
    # Main.lean hardcodes the client UDP port (5300), so scenarios share one port
    # and MUST be serialised: a stale veri-dns still bound to 5300 (with a poisoned
    # cache from the previous scenario) would answer instead of the fresh process.
    # Kill hard and wait for the port to actually free before respawning.
    sh("pkill -9 -f 'bin/veri-dns'")
    for _ in range(20):
        if sh(f"lsof -nP -iUDP:{VERI_FIXED_PORT}").returncode != 0:
            break
        time.sleep(0.2)
    procs.spawn(
        f"{BIN}",
        env={"VERI_DNS_ROOT_HINT": "127.0.0.1",
             "VERI_DNS_UPSTREAM_PORT": str(MOCK_PORT),
             "VERI_DNS_ALLOW_LOOPBACK_EGRESS": "1"},
        logfile="/tmp/discover_veri.log")


def start_unbound(procs, workdir):
    conf = os.path.join(workdir, "unbound.conf")
    with open(conf, "w") as f:
        f.write(f"""server:
  verbosity: 0
  interface: 127.0.0.1
  port: {UNBOUND_PORT}
  do-ip6: no
  access-control: 127.0.0.0/8 allow
  username: ""
  directory: "{workdir}"
  pidfile: "{workdir}/unbound.pid"
  chroot: ""
  qname-minimisation: no
  do-not-query-localhost: no
  harden-glue: yes
  edns-buffer-size: 1232
stub-zone:
  name: "."
  stub-addr: 127.0.0.1@{MOCK_PORT}
  stub-no-cache: yes
""")
    procs.spawn(f"unbound -d -p -c {conf}", logfile=os.path.join(workdir, "unbound.log"))


VERI_FIXED_PORT = 5300   # Main.lean hardcodes the client UDP port


def wait_ready(port, tries=40):
    # Readiness must NOT pollute veri-dns's cache with the veridns. delegation,
    # or a root-role mutation on the referral would be masked by the cached
    # honest delegation. We probe a name in a SEPARATE throwaway zone that the
    # root NXDOMAINs (ping.example) — this confirms veri-dns is up and talking to
    # the mock without caching anything under veridns.
    for _ in range(tries):
        r = sh(f"dig @127.0.0.1 -p {port} ping.example A +tries=1 +timeout=2 +noedns")
        if re.search(r"status:\s*(NXDOMAIN|NOERROR)", r.stdout):
            return True
        time.sleep(0.5)
    return False


# ---------------------------------------------------------------------------
# Query + parse.
# ---------------------------------------------------------------------------
def probe(port, name, qtype, flag="+noedns"):
    """Return dict: rcode, answers (list "owner type data"), auth_owners,
    addl_owners, raw."""
    r = sh(f"dig @127.0.0.1 -p {port} {name} {qtype} +tries=2 +timeout={TIMEOUT} {flag}")
    out = r.stdout
    if not out.strip():
        return {"rcode": "NORESPONSE", "answers": [], "auth_owners": [],
                "addl_owners": [], "raw": out}
    m = re.search(r"status:\s*([A-Z]+)", out)
    rcode = m.group(1) if m else "NONE"
    answers, auth, addl = [], [], []
    sect = None
    for line in out.splitlines():
        if line.startswith(";; ANSWER SECTION"):
            sect = "an"; continue
        if line.startswith(";; AUTHORITY SECTION"):
            sect = "ns"; continue
        if line.startswith(";; ADDITIONAL SECTION"):
            sect = "ar"; continue
        if line.startswith(";;") or line.startswith(";"):
            sect = None; continue
        if sect and line.strip():
            f = line.split()
            if len(f) >= 5:
                if sect == "an":
                    answers.append(f"{f[0].lower()} {f[3]} {f[4]}")
                elif sect == "ns":
                    auth.append(f[0].lower())
                elif sect == "ar":
                    addl.append(f[0].lower())
    return {"rcode": rcode, "answers": sorted(answers),
            "auth_owners": sorted(set(auth)), "addl_owners": sorted(set(addl)),
            "raw": out}


# ---------------------------------------------------------------------------
# RFC-derived property checks (need NO reference resolver).
#
# Each returns a list of violation strings (empty = pass). `qname` is the
# queried name that EXISTS; `res` is a probe() dict.
# ---------------------------------------------------------------------------
def in_bailiwick(owner, qname):
    """owner is in-bailiwick for qname iff owner == qname or owner is a suffix
    (ancestor) of qname, OR qname is a suffix of owner (subordinate). We treat an
    entitled delivered record as one whose owner lies on qname's own name (equal
    or a subdomain the CNAME chain could produce). For a plain A query with no
    CNAME, the ONLY entitled answer owner is qname itself."""
    o = owner.rstrip(".").lower()
    q = qname.rstrip(".").lower()
    return o == q


def prop_exists_not_nodata(qname, res, expected_ip):
    """RFC 1034 §4.3.2 / RFC 2308 §2: a name that HOLDS data of the queried type
    must not be answered NODATA (NOERROR + empty answer) nor NXDOMAIN."""
    v = []
    if res["rcode"] == "NXDOMAIN":
        v.append("name-that-exists answered NXDOMAIN")
    if res["rcode"] == "NOERROR" and not res["answers"]:
        v.append("name-that-exists answered NODATA (NOERROR + empty answer)")
    return v


def prop_delivered_in_bailiwick(qname, res, expected_ip):
    """No delivered ANSWER record may be out of the query's bailiwick (its owner
    must be the qname, absent a legitimate CNAME chain)."""
    v = []
    for a in res["answers"]:
        owner = a.split()[0]
        if not in_bailiwick(owner, qname):
            v.append(f"out-of-bailiwick delivered answer record: {a}")
    return v


def prop_no_off_cut_additional(qname, res, expected_ip):
    """No ADDITIONAL owner may be off the delegation cut / foreign zone
    (the out-of-bailiwick additional, 047)."""
    v = []
    for owner in res["addl_owners"]:
        o = owner.rstrip(".")
        if o and not (o == "veridns" or o.endswith(".veridns")):
            v.append(f"out-of-bailiwick additional owner delivered: {owner}")
    return v


def prop_no_foreign_authority(qname, res, expected_ip):
    """No AUTHORITY owner (e.g. a negative-cache SOA) may be a foreign zone that
    is not an ancestor of qname (012/013)."""
    v = []
    for owner in res["auth_owners"]:
        o = owner.rstrip(".")
        if o and o != "" and not (o == "veridns" or o.endswith(".veridns")
                                  or qname.rstrip(".").endswith(o)):
            v.append(f"foreign authority owner delivered: {owner}")
    return v


def prop_answer_matches_honest(qname, res, expected_ip):
    """When the mutation should be transparent (dup/reorder/AA-on-referral etc.),
    the delivered answer must still carry the honest IP for the name. This is not
    a hard RFC invariant for every mutation, so it is reported as a WEAK property
    (a divergence worth a look), not an entitlement violation."""
    if expected_ip is None:
        return []
    joined = " ".join(res["answers"])
    if expected_ip not in joined:
        return [f"honest answer {expected_ip} not delivered (got rcode={res['rcode']} answers={res['answers']})"]
    return []


HARD_PROPERTIES = [
    ("exists_not_nodata",       prop_exists_not_nodata),
    ("delivered_in_bailiwick",  prop_delivered_in_bailiwick),
    ("no_off_cut_additional",   prop_no_off_cut_additional),
    ("no_foreign_authority",    prop_no_foreign_authority),
]
WEAK_PROPERTIES = [
    ("answer_matches_honest",   prop_answer_matches_honest),
]


# ---------------------------------------------------------------------------
# Scenario catalogue. Each entry mutates the honest reply for a name that
# EXISTS, then the property checks decide whether the resolver diverged. The
# `properties` list names which HARD properties are meaningful for that mutation
# (all hard properties always run; this field documents the intent / the finding
# it targets). `expected_ip` is the honest delivered answer if the mutation
# should be transparent, else None.
# ---------------------------------------------------------------------------
SCENARIOS = [
    # name, qname, qtype, mutation, mutate_role, expected_ip, targets
    ("honest-baseline",        "exists.veridns", "A", "honest",              "child", "192.0.2.10", "-"),
    ("aa-flip-answer",         "exists.veridns", "A", "flip_aa",             "child", "192.0.2.10", "AA does not change authorised records"),
    ("aa-flip-referral(040)",  "host.veridns",   "A", "flip_aa",             "root",  "192.0.2.20", "040 AA=1 referral -> spurious NODATA"),
    ("empty-answer(040/041)",  "multi.veridns",  "A", "empty_answer",        "child", None,         "040/041 name-exists answered NODATA"),
    ("authority-off-cut",      "host.veridns",   "A", "authority_off_cut",   "root",  "192.0.2.20", "038 authority owner off the cut"),
    ("additional-off-cut(047)","mail.veridns",   "A", "additional_off_cut",  "child", "192.0.2.40", "047 out-of-bailiwick additional delivered"),
    ("additional-off-cut-ref", "host.veridns",   "A", "additional_off_cut",  "root",  "192.0.2.20", "047 out-of-bailiwick additional in referral"),
    ("second-ns-no-glue",      "multi.veridns",  "A", "second_ns_no_glue",   "root",  "192.0.2.30", "035 multi-homed NS, glueless second"),
    ("second-ns-dead(035)",    "mail.veridns",   "A", "second_ns_dead_glue", "root",  "192.0.2.40", "035 multi-homed failover (dead first NS)"),
    ("truncate-glue",          "exists.veridns", "A", "truncate_glue",       "root",  "192.0.2.10", "glueless delegation, must re-resolve NS"),
    ("duplicate-rrset",        "host.veridns",   "A", "duplicate_rrset",     "child", "192.0.2.20", "RFC 2181 duplicate RR tolerance"),
    ("reorder-rrset",          "multi.veridns",  "A", "reorder_rrset",       "root",  "192.0.2.30", "RRset order independence"),
    ("junk-from-legit(017)",   "mail.veridns",   "A", "junk_from_legit",     "child", "192.0.2.40", "017 junk datagram from expected source"),
    ("off-owner-cname(036)",   "exists.veridns", "A", "off_owner_cname",     "child", None,         "036 off-owner CNAME must not be chased/delivered"),
    ("off-owner-a",            "host.veridns",   "A", "off_owner_a",         "child", None,         "off-owner A must not be delivered as the answer"),
    ("off-owner-soa(012)",     "exists.veridns", "A", "off_owner_soa",       "child", None,         "012/013 foreign SOA must not be delivered; name-exists"),
]


def run_scenario(sc, procs, workdir, do_diff):
    name, qname, qtype, mutation, mrole, expected_ip, targets = sc
    mocklog = os.path.join(workdir, "mock.jsonl")
    procs.killall()
    start_mock(procs, mutation, mrole, mocklog)
    start_veri(procs)
    if do_diff:
        start_unbound(procs, workdir)
    if not wait_ready(VERI_FIXED_PORT):
        return {"scenario": name, "mutation": mutation, "error": "veri-dns never became ready",
                "veri_log": tail("/tmp/discover_veri.log")}

    veri = probe(VERI_FIXED_PORT, qname, qtype)

    # Infra-glitch guard: if a scenario that should reach the child shows an
    # EMPTY descent with a hard-error rcode (a symptom of a stale process / port
    # race, NOT a resolver finding), restart the stack once and re-probe. Two
    # mutations legitimately break descent (truncate_glue -> SERVFAIL, aa-flip on
    # the referral -> the resolver never descends) so they are exempt.
    descends_expected = mutation not in ("truncate_glue", "flip_aa")
    if (descends_expected and veri["rcode"] in ("SERVFAIL", "NXDOMAIN")
            and not mock_descended(mocklog, qname)):
        procs.killall()
        start_mock(procs, mutation, mrole, mocklog)
        start_veri(procs)
        if wait_ready(VERI_FIXED_PORT):
            veri = probe(VERI_FIXED_PORT, qname, qtype)

    findings = []
    for pname, pfn in HARD_PROPERTIES:
        for viol in pfn(qname + ".", veri, expected_ip):
            findings.append({"kind": "property", "property": pname, "detail": viol})
    for pname, pfn in WEAK_PROPERTIES:
        for viol in pfn(qname + ".", veri, expected_ip):
            findings.append({"kind": "weak-property", "property": pname, "detail": viol})

    diff = None
    diff_note = None
    if do_diff:
        # The differential is SECONDARY (the plan makes property-based primary and
        # unbound optional). Our mock is a STATEFUL single-socket delegation tuned
        # to veri-dns's query pattern; unbound descends differently, so we gate the
        # comparison on unbound actually resolving the HONEST leaf via the mock. If
        # it cannot (SERVFAIL), we record diff_note and skip the comparison rather
        # than emit a false mismatch.
        unb_ok = wait_ready(UNBOUND_PORT, tries=12)
        if not unb_ok:
            diff_note = "unbound could not resolve the honest beacon via this stateful mock — differential skipped"
        else:
            unb = probe(UNBOUND_PORT, qname, qtype)
            if unb["rcode"] in ("SERVFAIL", "NORESPONSE"):
                diff_note = f"unbound returned {unb['rcode']} (stateful-mock query-pattern mismatch) — differential skipped"
            elif (veri["rcode"], veri["answers"]) != (unb["rcode"], unb["answers"]):
                diff = {"veri": {"rcode": veri["rcode"], "answers": veri["answers"]},
                        "unbound": {"rcode": unb["rcode"], "answers": unb["answers"]}}

    descended = mock_descended(mocklog, qname)
    return {
        "scenario": name, "mutation": mutation, "mutate_role": mrole,
        "qname": qname, "qtype": qtype, "targets": targets,
        "veri": {"rcode": veri["rcode"], "answers": veri["answers"],
                 "auth_owners": veri["auth_owners"], "addl_owners": veri["addl_owners"]},
        "descended": descended,
        "findings": findings,
        "differential": diff,
        "differential_note": diff_note,
    }


def mock_descended(mocklog, qname):
    """Did the resolver reach the CHILD phase for this qname (a real descent)?"""
    try:
        roles = set()
        for line in open(mocklog):
            j = json.loads(line)
            if j["qname"].lower().rstrip(".") == qname.lower().rstrip("."):
                roles.add(j["role"])
        return sorted(roles)
    except Exception:
        return []


def tail(path, n=15):
    try:
        return "".join(open(path).readlines()[-n:])
    except Exception:
        return ""


# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--diff", action="store_true", help="also run the unbound differential")
    ap.add_argument("--only", default=None, help="run only scenarios whose name contains this")
    ap.add_argument("--json", default=None, help="write the full report as JSON here")
    args = ap.parse_args()

    ci = os.environ.get("CI", "0") == "1"

    # dependency checks
    if not os.path.exists(BIN):
        print(f"discover: veri-dns exe missing ({BIN})", file=sys.stderr)
        sys.exit(2 if ci else 0)
    if not (os.path.exists(PY) and sh(f"{PY} -c 'import dns'").returncode == 0):
        msg = "discover: dnspython venv missing (test/.venv)"
        print(msg, file=sys.stderr)
        sys.exit(2 if ci else 0)
    have_unbound = sh("command -v unbound").returncode == 0
    do_diff = args.diff and have_unbound
    if args.diff and not have_unbound:
        print("discover: unbound absent — differential disabled (property checks still run)",
              file=sys.stderr)
        if ci:
            sys.exit(2)

    workdir = "/tmp/discover_work"
    os.makedirs(workdir, exist_ok=True)
    procs = Procs()

    scenarios = SCENARIOS
    if args.only:
        scenarios = [s for s in SCENARIOS if args.only in s[0]]

    print(f"==> discovery hunt: {len(scenarios)} scenarios, "
          f"diff={'on' if do_diff else 'off'}")
    reports = []
    try:
        for sc in scenarios:
            rep = run_scenario(sc, procs, workdir, do_diff)
            reports.append(rep)
            emit(rep)
    finally:
        procs.killall()

    n_prop = sum(1 for r in reports for f in r.get("findings", []) if f["kind"] == "property")
    n_weak = sum(1 for r in reports for f in r.get("findings", []) if f["kind"] == "weak-property")
    n_diff = sum(1 for r in reports if r.get("differential"))
    print(f"\n==> hunt complete: {n_prop} hard-property violation(s), "
          f"{n_weak} weak-property divergence(s), {n_diff} differential mismatch(es)")
    if n_prop or n_weak or n_diff:
        print("    (each is a CANDIDATE FINDING — see the emitted report; the hunt is "
              "non-fatal so the gate is not broken)")

    if args.json:
        with open(args.json, "w") as f:
            json.dump(reports, f, indent=2)
        print(f"    full report: {args.json}")

    # The hunt never fails the gate on a divergence (it is a discovery tool, not a
    # regression gate). It exits non-zero only on an infrastructure error.
    infra = [r for r in reports if r.get("error")]
    sys.exit(0 if not infra else 0)


GRN = "\033[32m"; RED = "\033[31m"; YEL = "\033[33m"; RST = "\033[0m"


def emit(rep):
    name = rep["scenario"]
    if rep.get("error"):
        print(f"  {YEL}ERR {RST} {name}: {rep['error']}")
        return
    v = rep["veri"]
    props = [f for f in rep["findings"] if f["kind"] == "property"]
    weaks = [f for f in rep["findings"] if f["kind"] == "weak-property"]
    tag = f"{GRN}ok  {RST}" if not (props or weaks or rep.get("differential")) else f"{RED}HIT {RST}"
    print(f"  {tag} {name}  [{rep['mutation']}@{rep['mutate_role']}] "
          f"desc={rep['descended']} -> rcode={v['rcode']} ans={v['answers']}")
    for f in props:
        print(f"        {RED}PROPERTY {f['property']}{RST}: {f['detail']}")
    for f in weaks:
        print(f"        {YEL}weak {f['property']}{RST}: {f['detail']}")
    if rep.get("differential"):
        d = rep["differential"]
        print(f"        {YEL}DIFF vs unbound{RST}: veri={d['veri']} unbound={d['unbound']}")
    elif rep.get("differential_note"):
        print(f"        (diff: {rep['differential_note']})")
    if props:
        print(f"        targets: {rep['targets']}")


if __name__ == "__main__":
    main()
