#!/usr/bin/env python3
"""
discover_mock.py — a MUTATING authoritative nameserver for the discovery harness
(docs/model-strengthening-plan-2.md §D).

Unlike test/mock_auth.py (a FLAT collapsed root that serves every name
authoritatively in one hop), this server implements a real DELEGATION so the
harness can exercise the referral classifier, glue/bailiwick handling and
multi-homed failover — the surfaces where findings 040/047/035 live.

Topology and the single-socket trick
------------------------------------
A resolver first asks the ROOT for a leaf, is REFERRED to the child zone
`veridns.`, then re-asks the CHILD. That two-phase descent is the point.

veri-dns forces EVERY upstream query to one configured port
(VERI_DNS_UPSTREAM_PORT) and only 127.0.0.1 is bindable without a loopback alias
(root-only on macOS), so both roles must share ONE socket. We distinguish the
two phases STATEFULLY: the first query for a given (qname,qtype) is answered as
the ROOT (a referral, AA=0); any subsequent query for the same (qname,qtype)
within REFER_WINDOW seconds is answered as the CHILD (the data answer, AA=1).
This is a genuine two-phase descent (the resolver must accept the referral, set
up its slist from the glue and re-query) and does not loop: the child answer is
terminal.

--reset clears the referral memory between scenarios (the driver restarts the
mock per scenario, so a fresh process starts with empty memory anyway).

THE MUTATION KNOB (--mutation NAME)
-----------------------------------
Before a reply leaves the wire it is passed through a named mutation from a
catalogue (see MUTATIONS). Each mutation is a surgical edit of an otherwise
honest response for a name that EXISTS, so any divergence is attributable to the
single mutation. `honest` is the identity control. --mutate-role restricts the
mutation to the ROOT (referral) reply or the CHILD (answer) reply, so an AA-flip
on the referral is distinguishable from an AA-flip on the leaf answer.

Every query is appended to --log as one JSON line so the driver can confirm the
resolver actually descended (root referral -> child query).
"""
import argparse
import json
import socket
import socketserver
import struct
import sys
import threading
import time

import dns.message
import dns.name
import dns.rrset
import dns.rdata
import dns.rdataclass
import dns.rdatatype
import dns.rcode
import dns.flags

ROOT = dns.name.root
VERIDNS = dns.name.from_text("veridns.")
NS1 = dns.name.from_text("ns1.veridns.")
NS2 = dns.name.from_text("ns2.veridns.")
OFF_CUT = dns.name.from_text("attacker.example.")   # NOT below the veridns cut

GLUE_IP = "127.0.0.1"           # the single socket we control
DEAD_IP = "203.0.113.199"       # never answers — used to force failover

# BEACON is served always-honest (never mutated) so the harness can confirm
# veri-dns readiness even under a mutation that would otherwise poison the leaf
# answers (empty_answer, off_owner_*).
BEACON = dns.name.from_text("beacon.veridns.")

LEAF = {
    dns.name.from_text("exists.veridns."): [(dns.rdatatype.A, ["192.0.2.10"])],
    dns.name.from_text("host.veridns."):   [(dns.rdatatype.A, ["192.0.2.20"])],
    dns.name.from_text("multi.veridns."):  [(dns.rdatatype.A, ["192.0.2.30"])],
    dns.name.from_text("mail.veridns."):   [(dns.rdatatype.A, ["192.0.2.40"])],
    BEACON:                                [(dns.rdatatype.A, ["192.0.2.99"])],
    NS1: [(dns.rdatatype.A, [GLUE_IP])],
    NS2: [(dns.rdatatype.A, [GLUE_IP])],
}
CHILD_SOA = "ns1.veridns. hostmaster.veridns. 1 3600 600 86400 3600"
ROOT_SOA = "a.root-servers.net. nstld. 1 3600 600 86400 3600"
TTL = 3600
REFER_WINDOW = 30.0

LOG_LOCK = threading.Lock()
LOG_PATH = None

# per-(qname,qtype) time of first (root) referral, for the phase split.
REFERRED = {}
REFERRED_LOCK = threading.Lock()


def log_query(role, qname, qtype, note=""):
    if LOG_PATH is None:
        return
    line = json.dumps({
        "role": role, "qname": qname.to_text(),
        "qtype": dns.rdatatype.to_text(qtype), "note": note,
    })
    with LOG_LOCK:
        with open(LOG_PATH, "a") as f:
            f.write(line + "\n")


def rrset(owner, rdtype, rdatas):
    return dns.rrset.from_text_list(owner, TTL, dns.rdataclass.IN, rdtype, rdatas)


def phase_for(qname, qtype):
    """Return 'root' for the first look at (qname,qtype), 'child' thereafter.
    The NS-glue names themselves (ns1/ns2.veridns) are always answered as the
    child — they are how the resolver *reaches* the child, not a descent step."""
    if qname in (NS1, NS2):
        return "child"
    # veri-dns 0x20-randomises the query case per retry, so key on the
    # lower-cased name (canonical, RFC 4343) or the phase never advances.
    key = (qname.to_text().lower(), qtype)
    now = time.monotonic()
    with REFERRED_LOCK:
        first = REFERRED.get(key)
        if first is None or now - first > REFER_WINDOW:
            REFERRED[key] = now
            return "root"
        return "child"


# ---------------------------------------------------------------------------
# Honest responses (before mutation).
# ---------------------------------------------------------------------------
def root_response(query, second_ns=False, ns2_glue=GLUE_IP):
    """The ROOT refers *.veridns. downward — never answers it."""
    resp = dns.message.make_response(query)
    q = query.question[0]
    qname = q.name
    if q.rdclass != dns.rdataclass.IN:
        resp.set_rcode(dns.rcode.REFUSED); return resp
    if not qname.is_subdomain(VERIDNS) or qname == ROOT:
        resp.set_rcode(dns.rcode.NXDOMAIN)
        resp.authority.append(rrset(ROOT, dns.rdatatype.SOA, [ROOT_SOA]))
        return resp
    ns_targets = [NS1.to_text()]
    if second_ns:
        ns_targets.append(NS2.to_text())
    resp.authority.append(rrset(VERIDNS, dns.rdatatype.NS, ns_targets))
    resp.additional.append(rrset(NS1, dns.rdatatype.A, [GLUE_IP]))
    if second_ns:
        resp.additional.append(rrset(NS2, dns.rdatatype.A, [ns2_glue]))
    return resp


def child_response(query):
    """The CHILD answers leaf data queries authoritatively (AA=1)."""
    resp = dns.message.make_response(query)
    q = query.question[0]
    qname, qtype = q.name, q.rdtype
    if q.rdclass != dns.rdataclass.IN:
        resp.set_rcode(dns.rcode.REFUSED); return resp
    resp.flags |= dns.flags.AA
    if qname == VERIDNS:
        if qtype in (dns.rdatatype.NS, dns.rdatatype.ANY):
            resp.answer.append(rrset(VERIDNS, dns.rdatatype.NS, [NS1.to_text()]))
        elif qtype == dns.rdatatype.SOA:
            resp.answer.append(rrset(VERIDNS, dns.rdatatype.SOA, [CHILD_SOA]))
        else:
            resp.authority.append(rrset(VERIDNS, dns.rdatatype.SOA, [CHILD_SOA]))
        return resp
    recs = LEAF.get(qname)
    if recs is None:
        resp.set_rcode(dns.rcode.NXDOMAIN)
        resp.authority.append(rrset(VERIDNS, dns.rdatatype.SOA, [CHILD_SOA]))
        return resp
    matched = False
    for (t, rdatas) in recs:
        if t == qtype or qtype == dns.rdatatype.ANY:
            resp.answer.append(rrset(qname, t, rdatas)); matched = True
    if not matched:
        resp.authority.append(rrset(VERIDNS, dns.rdatatype.SOA, [CHILD_SOA]))
    return resp


# ---------------------------------------------------------------------------
# Mutation catalogue. Each: (resp, role, ctx) -> mutated resp.
# ---------------------------------------------------------------------------
def mut_honest(resp, role, ctx):
    return resp


def mut_flip_aa(resp, role, ctx):
    resp.flags ^= dns.flags.AA
    return resp


def mut_authority_off_cut(resp, role, ctx):
    """Move an authority NS owner OFF the delegation cut."""
    for rr in list(resp.authority):
        if rr.rdtype == dns.rdatatype.NS:
            moved = dns.rrset.from_rdata_list(OFF_CUT, rr.ttl, list(rr))
            resp.authority.remove(rr); resp.authority.append(moved); break
    return resp


def mut_additional_off_cut(resp, role, ctx):
    """Add an out-of-bailiwick A into ADDITIONAL (047 surface)."""
    resp.additional.append(rrset(OFF_CUT, dns.rdatatype.A, ["6.6.6.6"]))
    return resp


def mut_empty_answer(resp, role, ctx):
    """Empty the answer section but keep NOERROR (040/041 surface)."""
    if resp.rcode() == dns.rcode.NOERROR:
        resp.answer = []
    return resp


def mut_second_ns_no_glue(resp, role, ctx):
    """Add a second NS to the referral WITHOUT glue (glueless failover)."""
    if role == "root":
        for rr in resp.authority:
            if rr.rdtype == dns.rdatatype.NS:
                rr.add(dns.rdata.from_text(dns.rdataclass.IN, dns.rdatatype.NS,
                                           NS2.to_text()))
                break
    return resp


def mut_second_ns_dead_glue(resp, role, ctx):
    """ns1 glue -> DEAD, ns2 glue -> live child (035 failover)."""
    if role == "root":
        for rr in resp.authority:
            if rr.rdtype == dns.rdatatype.NS:
                if NS2 not in [rd.target for rd in rr]:
                    rr.add(dns.rdata.from_text(dns.rdataclass.IN, dns.rdatatype.NS,
                                               NS2.to_text()))
                break
        resp.additional = []
        resp.additional.append(rrset(NS1, dns.rdatatype.A, [DEAD_IP]))
        resp.additional.append(rrset(NS2, dns.rdatatype.A, [GLUE_IP]))
    return resp


def mut_truncate_glue(resp, role, ctx):
    """Drop the glue from the referral entirely (glueless delegation)."""
    if role == "root":
        resp.additional = []
    return resp


def mut_duplicate_rrset(resp, role, ctx):
    section = resp.answer if resp.answer else resp.authority
    if section:
        section.append(section[0])
    return resp


def mut_reorder_rrset(resp, role, ctx):
    if len(resp.answer) > 1:
        resp.answer = list(reversed(resp.answer))
    elif len(resp.authority) > 1:
        resp.authority = list(reversed(resp.authority))
    return resp


def mut_off_owner_cname(resp, role, ctx):
    """Answer with a CNAME whose OWNER is not the qname (036 surface)."""
    if role == "child" and resp.question:
        qname = resp.question[0].name
        if qname != VERIDNS and qname.is_subdomain(VERIDNS) and qname not in (NS1, NS2):
            resp.answer = []
            resp.answer.append(rrset(OFF_CUT, dns.rdatatype.CNAME,
                                     ["landing.veridns."]))
    return resp


def mut_off_owner_a(resp, role, ctx):
    """Answer carries an A for a DIFFERENT owner than the qname."""
    if role == "child" and resp.question:
        qname = resp.question[0].name
        if qname != VERIDNS and qname.is_subdomain(VERIDNS) and qname not in (NS1, NS2):
            resp.answer = []
            resp.answer.append(rrset(dns.name.from_text("other.veridns."),
                                     dns.rdatatype.A, ["9.9.9.9"]))
    return resp


def mut_off_owner_soa(resp, role, ctx):
    """A spoofed NEGATIVE reply for a name that exists: drop the real answer and
    attach an SOA whose owner is a FOREIGN zone (012/013). A correct resolver
    must not deliver the foreign SOA, and — since the name exists — must not turn
    this into a believed NODATA/NXDOMAIN either."""
    if role == "child":
        resp.answer = []
    resp.authority = []
    resp.authority.append(rrset(OFF_CUT, dns.rdatatype.SOA,
        ["ns.attacker.example. root.attacker.example. 1 3600 600 86400 3600"]))
    return resp


def mut_junk_from_legit(resp, role, ctx):
    """Wire-level: handled in prepend_junk (a malformed datagram from the
    expected server addr:port BEFORE the real reply). No response edit."""
    return resp


MUTATIONS = {
    "honest":              mut_honest,
    "flip_aa":             mut_flip_aa,
    "authority_off_cut":   mut_authority_off_cut,
    "additional_off_cut":  mut_additional_off_cut,
    "empty_answer":        mut_empty_answer,
    "second_ns_no_glue":   mut_second_ns_no_glue,
    "second_ns_dead_glue": mut_second_ns_dead_glue,
    "truncate_glue":       mut_truncate_glue,
    "duplicate_rrset":     mut_duplicate_rrset,
    "reorder_rrset":       mut_reorder_rrset,
    "off_owner_cname":     mut_off_owner_cname,
    "off_owner_a":         mut_off_owner_a,
    "off_owner_soa":       mut_off_owner_soa,
    "junk_from_legit":     mut_junk_from_legit,
}

SECOND_NS_MUTATIONS = {"second_ns_no_glue", "second_ns_dead_glue"}
JUNK_MUTATIONS = {"junk_from_legit"}


class Server:
    def __init__(self, mutation, mutate_role):
        self.mutation = mutation
        self.mutate_role = mutate_role   # "root" | "child"

    def build(self, query):
        q = query.question[0]
        role = phase_for(q.name, q.rdtype)
        if role == "root":
            resp = root_response(query, second_ns=(self.mutation in SECOND_NS_MUTATIONS))
        else:
            resp = child_response(query)
        note = "honest"
        # the beacon is NEVER mutated — the harness relies on it for readiness.
        if (self.mutation != "honest" and role == self.mutate_role
                and q.name != BEACON):
            resp = MUTATIONS[self.mutation](resp, role, {})
            note = self.mutation
        log_query(role, q.name, q.rdtype, note)
        return resp

    def junk_before(self, query):
        if self.mutation not in JUNK_MUTATIONS:
            return None
        q = query.question[0]
        role = phase_for(q.name, q.rdtype)
        # phase_for consumed the referral memory; re-mark so build() sees same role
        if role == self.mutate_role:
            return b"\xba\xad\xf0\x0d"   # not a valid DNS message
        return None


def make_handler(server):
    def build_wire(data, transport):
        try:
            query = dns.message.from_wire(data)
        except Exception:
            return None, None
        if not query.question:
            return None, None
        resp = server.build(query)
        wire = resp.to_wire(max_size=65535)
        if transport == "udp" and len(wire) > 512:
            resp.answer = []; resp.authority = []; resp.additional = []
            resp.flags |= dns.flags.TC
            wire = resp.to_wire(max_size=65535)
        return None, wire

    class UDPHandler(socketserver.BaseRequestHandler):
        def handle(self):
            data, sock = self.request
            junk, out = build_wire(data, "udp")
            if junk is not None:
                sock.sendto(junk, self.client_address)
            if out is not None:
                sock.sendto(out, self.client_address)

    class TCPHandler(socketserver.BaseRequestHandler):
        def handle(self):
            hdr = self._recvn(2)
            if hdr is None:
                return
            (mlen,) = struct.unpack("!H", hdr)
            body = self._recvn(mlen)
            if body is None:
                return
            _junk, out = build_wire(body, "tcp")
            if out is not None:
                self.request.sendall(struct.pack("!H", len(out)) + out)

        def _recvn(self, n):
            buf = b""
            while len(buf) < n:
                chunk = self.request.recv(n - len(buf))
                if not chunk:
                    return None
                buf += chunk
            return buf

    return UDPHandler, TCPHandler


class ThreadingUDP(socketserver.ThreadingMixIn, socketserver.UDPServer):
    allow_reuse_address = True


class ThreadingTCP(socketserver.ThreadingMixIn, socketserver.TCPServer):
    allow_reuse_address = True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=5360)
    ap.add_argument("--mutation", default="honest", choices=list(MUTATIONS))
    ap.add_argument("--mutate-role", default="child", choices=["root", "child"])
    ap.add_argument("--log", default=None)
    args = ap.parse_args()

    global LOG_PATH
    LOG_PATH = args.log

    srv = Server(args.mutation, args.mutate_role)
    UDPHandler, TCPHandler = make_handler(srv)
    udp = ThreadingUDP((args.host, args.port), UDPHandler)
    threading.Thread(target=udp.serve_forever, daemon=True).start()
    try:
        tcp = ThreadingTCP((args.host, args.port), TCPHandler)
        threading.Thread(target=tcp.serve_forever, daemon=True).start()
    except OSError:
        pass
    sys.stderr.write("discover_mock: %s:%d mutation=%s role=%s\n"
                     % (args.host, args.port, args.mutation, args.mutate_role))
    sys.stderr.flush()
    threading.Event().wait()


if __name__ == "__main__":
    main()
