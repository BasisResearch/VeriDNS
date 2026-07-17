#!/usr/bin/env bash
# Adversarial injection differential test for veri-dns vs unbound (W5 corpus).
#
# The plan's mutation contract says the resolver must deliver and cache only the
# records a query is entitled to (W1 Entitled family). This rig drives the mock
# authoritative server (test/mock_auth.py), which decorates legitimate answers with
# off-entitlement riders, and asserts veri-dns behaves identically to a reference
# unbound — both drop the poison. It also documents-and-locks today's behaviour for
# two served-but-previously-uncovered surfaces: qtype=ANY and class=CHAOS.
#
# One sub-test per finding:
#   1. 004        — subdomain rider on an answer section
#   2. Kaminsky   — unsolicited ADDITIONAL glue never promoted to the answer cache
#   3. 036        — off-owner CNAME not chased
#   4. 012/013    — off-owner (foreign) SOA not delivered / not negatively cached
#   5. RFC 8482   — qtype=ANY parity
#   6. class=CH   — non-IN class parity
#
# The mock stays a FLAT authoritative root (collapsed root+child provokes a descent
# hang); entitlement scrubbing is about the delivered answer relative to the client's
# qname, so it is meaningfully exercised without any delegation depth.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
PY="$ROOT/test/.venv/bin/python"
MOCK="$ROOT/test/mock_auth.py"

MOCK_PORT=5354
VERI_PORT=5300
UNBOUND_PORT=5399
TIMEOUT=15

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/veridns-inject.XXXXXX")"
MOCK_LOG="$WORKDIR/mock.jsonl"
UNBOUND_CONF="$WORKDIR/unbound.conf"

MOCK_PID=""; UNBOUND_PID=""; VERI_PID=""
cleanup() {
  for p in "$MOCK_PID" "$UNBOUND_PID" "$VERI_PID"; do [ -n "$p" ] && kill "$p" 2>/dev/null; done
  pkill -f 'bin/veri-dns' 2>/dev/null
  pkill -f 'mock_auth.py' 2>/dev/null
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

fail=0
pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad()  { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fail=1; }

start_mock() {
  : > "$MOCK_LOG"
  "$PY" "$MOCK" --port "$MOCK_PORT" --log "$MOCK_LOG" >"$WORKDIR/mock.err" 2>&1 &
  MOCK_PID=$!
  sleep 1
}
start_unbound() {
  cat > "$UNBOUND_CONF" <<EOF
server:
  verbosity: 0
  interface: 127.0.0.1
  port: $UNBOUND_PORT
  do-ip6: no
  access-control: 127.0.0.0/8 allow
  username: ""
  directory: "$WORKDIR"
  pidfile: "$WORKDIR/unbound.pid"
  chroot: ""
  qname-minimisation: no
  do-not-query-localhost: no
  edns-buffer-size: 1232
forward-zone:
  name: "."
  forward-addr: 127.0.0.1@$MOCK_PORT
EOF
  unbound -d -p -c "$UNBOUND_CONF" >"$WORKDIR/unbound.log" 2>&1 &
  UNBOUND_PID=$!
}
start_veri() {
  pkill -f 'bin/veri-dns' 2>/dev/null; sleep 0.4
  VERI_DNS_ROOT_HINT=127.0.0.1 \
  VERI_DNS_UPSTREAM_PORT="$MOCK_PORT" \
  VERI_DNS_ALLOW_LOOPBACK_EGRESS=1 \
    "$BIN" >"$WORKDIR/veri.log" 2>&1 &
  VERI_PID=$!
}

wait_ready() {
  local i
  for i in $(seq 1 40); do
    if dig @127.0.0.1 -p "$1" "$3" A +tries=1 +timeout=2 +short 2>/dev/null | grep -q '127.0.0.1'; then
      echo "  ($2 ready ~${i}s, beacon $3)"; return 0
    fi
    sleep 1
  done
  echo "  !! $2 never resolved $3"; return 1
}

# probe: "<rcode>|<answer-set>" — answer section, owner+type+data sorted, ; separated.
probe() {
  local out rcode ans
  out="$(dig @127.0.0.1 -p "$1" "$2" "$3" +tries=3 +timeout="$TIMEOUT" "$4" 2>/dev/null)"
  [ -z "$out" ] && { echo "NORESPONSE|"; return; }
  rcode="$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$out" | head -1)"
  ans="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{print $1, $4, $5}' <<<"$out" | sort | tr '\n' ';')"
  echo "${rcode:-NONE}|$ans"
}

# authority owners (for the off-owner SOA delivery check).
authority_owners() {
  dig @127.0.0.1 -p "$1" "$2" "$3" +tries=3 +timeout="$TIMEOUT" 2>/dev/null \
    | awk '/^;; AUTHORITY SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{print $1}' | sort | tr '\n' ';'
}

# diff_parity NAME TYPE [EXPECT_RCODE] [+digflag] — assert veri==unbound.
diff_parity() {
  local name="$1" typ="$2" want="${3:-}" flag="${4:-+noedns}"
  local v u
  v="$(probe "$VERI_PORT" "$name" "$typ" "$flag")"
  u="$(probe "$UNBOUND_PORT" "$name" "$typ" "$flag")"
  if [ "$v" != "$u" ]; then
    bad "$name $typ: veri=[$v] != unbound=[$u]"; return
  fi
  if [ -n "$want" ] && [ "${v%%|*}" != "$want" ]; then
    bad "$name $typ: veri==unbound=[$v] but expected rcode $want"; return
  fi
  pass "$name $typ: veri==unbound ($v)"
}

echo "==> starting mock (UDP+TCP), unbound, veri-dns"
start_mock
start_unbound
start_veri
wait_ready "$UNBOUND_PORT" unbound small.veridns || exit 2
wait_ready "$VERI_PORT" veri-dns small.veridns || { cat "$WORKDIR/veri.log"; exit 2; }

echo "==> sub-test 1: subdomain rider on answer (004) — rider.veridns A"
# The mock riders piggyback.rider.veridns 6.6.6.6 into the answer. A correct resolver
# delivers only rider.veridns's own A; the rider owner must not appear in either answer.
diff_parity rider.veridns A NOERROR
v="$(probe "$VERI_PORT" rider.veridns A +noedns)"
if grep -q 'piggyback' <<<"$v"; then bad "veri delivered the subdomain rider: $v"; else pass "veri answer carries no subdomain rider"; fi
# and the ridden name must not be served from a poisoned cache: fresh query hits the mock (NXDOMAIN).
diff_parity piggyback.rider.veridns A NXDOMAIN

echo "==> sub-test 2: unsolicited ADDITIONAL never cached (Kaminsky) — poison.veridns A then bankofsteal.veridns A"
diff_parity poison.veridns A NOERROR
# bankofsteal.veridns was injected only as spoofed additional glue; it owns no record,
# so if the poison was NOT cached both resolvers return NXDOMAIN.
diff_parity bankofsteal.veridns A NXDOMAIN

echo "==> sub-test 3: off-owner CNAME not chased (036) — alias.veridns A"
# Under entitledAnswerB (commit 38f8b57: a foreign answer is not an answer), an
# off-owner CNAME response carries no record the query is entitled to, so veri-dns
# treats it as no usable answer and SERVFAILs rather than delivering/chasing the
# off-owner CNAME. This is the INTENDED hardening, not a regression: unbound is
# more lenient here (NOERROR with the alias's own record), so this is a documented
# deviation. We assert veri=SERVFAIL and, crucially, that it never chased/served
# the off-owner CNAME target.
v="$(probe "$VERI_PORT" alias.veridns A +noedns)"
if [ "${v%%|*}" = "SERVFAIL" ]; then
  pass "alias.veridns A: veri=SERVFAIL (entitledAnswerB: off-owner CNAME is not an entitled answer)"
else
  bad "alias.veridns A: veri=[$v] (expected SERVFAIL under entitledAnswerB — update the pin if intentional)"
fi
if grep -qE 'landing|evil' <<<"$v"; then bad "veri chased/served the off-owner CNAME: $v"; else pass "veri did not chase the off-owner CNAME"; fi

echo "==> sub-test 4: off-owner (foreign) SOA not delivered (012/013) — ghost.veridns A"
diff_parity ghost.veridns A NXDOMAIN
va="$(authority_owners "$VERI_PORT" ghost.veridns A)"
if grep -q 'evil.example' <<<"$va"; then bad "veri delivered the foreign SOA in authority: $va"; else pass "veri did not deliver the foreign SOA (authority owners: ${va:-none})"; fi

echo "==> sub-test 5: qtype=ANY → RFC 8482 §4.2 minimal response — small.veridns ANY"
# RFC 8482 §4.2: a QTYPE=ANY query is answered at the serve boundary with a single
# synthesized HINFO RRset (CPU="RFC8482", OS=null) instead of a full multi-type
# resolution. veri-dns returns NOERROR + exactly one HINFO record. (unbound's ANY
# handling differs — it does full resolution — so this is a deliberate deviation,
# asserted against the RFC 8482 shape, not against unbound.)
vany="$(dig @127.0.0.1 -p "$VERI_PORT" small.veridns ANY +tries=3 +timeout="$TIMEOUT" +noedns 2>/dev/null)"
vrcode="$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$vany" | head -1)"
vhinfo="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{print $4}' <<<"$vany" | sort -u | tr '\n' ';')"
vcount="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5' <<<"$vany" | wc -l | tr -d ' ')"
if [ "${vrcode:-NONE}" = "NOERROR" ] && [ "$vhinfo" = "HINFO;" ] && [ "$vcount" = "1" ]; then
  pass "small.veridns ANY: veri=NOERROR, single HINFO RRset (RFC 8482 §4.2 minimal)"
else
  bad "small.veridns ANY: veri=[rcode=${vrcode:-NONE} types=${vhinfo:-none} count=${vcount:-0}] (expected NOERROR + single HINFO per RFC 8482 §4.2)"
fi
# The synthesized HINFO carries the RFC8482 marker in its CPU field.
if grep -qi 'RFC8482' <<<"$vany"; then pass "veri ANY HINFO carries the RFC8482 CPU marker"; else bad "veri ANY HINFO missing the RFC8482 marker: $(grep -i hinfo <<<"$vany")"; fi

echo "==> sub-test 6: class=CHAOS behaviour (non-IN → REFUSED, plan-2 Query-shape row)"
# The plan-2 Query-shape row is closed for non-IN: queryProblem now rejects any
# non-Internet-class query with REFUSED at ingress (before resolution), matching a
# stock recursive resolver (unbound). The serve capstones no longer carry the
# qclass=IN gate (it is derived from queryProblem = none). This test asserts
# veri==unbound: both REFUSE version.bind CH.
# dig's class is a separate arg (-c CH), so this uses a dedicated probe.
vch="$(dig @127.0.0.1 -p "$VERI_PORT" -c CH version.bind TXT +tries=3 +timeout="$TIMEOUT" +noedns 2>/dev/null | sed -n 's/.*status: \([A-Z]*\).*/\1/p' | head -1)"
uch="$(dig @127.0.0.1 -p "$UNBOUND_PORT" -c CH version.bind TXT +tries=3 +timeout="$TIMEOUT" +noedns 2>/dev/null | sed -n 's/.*status: \([A-Z]*\).*/\1/p' | head -1)"
if [ "${vch:-NONE}" = "REFUSED" ] && [ "${uch:-NONE}" = "REFUSED" ]; then
  pass "version.bind CH TXT: veri=REFUSED unbound=REFUSED (non-IN → REFUSED, plan-2 Query-shape)"
else
  bad "version.bind CH TXT: veri=[${vch:-NONE}] unbound=[${uch:-NONE}] (expected REFUSED/REFUSED — non-IN must be refused at ingress)"
fi

echo
[ "$fail" -eq 0 ] && echo "==> INJECT ALL PASS" || echo "==> INJECT FAILURES"
exit "$fail"
