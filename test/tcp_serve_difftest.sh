#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
PY="$ROOT/test/.venv/bin/python"
MOCK="$ROOT/test/mock_auth.py"

MOCK_PORT=5354
VERI_PORT=5300
UNBOUND_PORT=5399
TIMEOUT=15

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/veridns-tcpserve.XXXXXX")"
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

probe_tcp() {
  local out rcode ans
  out="$(dig +tcp @127.0.0.1 -p "$1" "$2" "$3" +tries=3 +timeout="$TIMEOUT" 2>/dev/null)"
  [ -z "$out" ] && { echo "NORESPONSE|"; return; }
  rcode="$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$out" | head -1)"
  ans="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{$1=$2=$3=$4="";sub(/^ +/,"");print}' <<<"$out" | sort | tr '\n' ';')"
  echo "${rcode:-NONE}|$ans"
}

diff_tcp() {
  local v u
  v="$(probe_tcp "$VERI_PORT" "$1" "$2")"
  u="$(probe_tcp "$UNBOUND_PORT" "$1" "$2")"
  if [ "$v" = "$u" ] && [ "${v%%|*}" = "$3" ]; then
    pass "$1 $2 over TCP: veri==unbound ($v)"
  else
    bad "$1 $2 over TCP: veri=[$v] unbound=[$u] (want $3)"
  fi
}

echo "==> starting mock (UDP+TCP), unbound, veri-dns"
start_mock
start_unbound
start_veri
wait_ready "$UNBOUND_PORT" unbound small.veridns || exit 2
wait_ready "$VERI_PORT" veri-dns small.veridns || { cat "$WORKDIR/veri.log"; exit 2; }

echo "==> sub-test 1: basic TCP serving parity (small.veridns A)"
diff_tcp small.veridns A NOERROR

echo "==> sub-test 2: forced-TC name served over +tcp (forcetc.veridns A)"
diff_tcp forcetc.veridns A NOERROR

echo "==> sub-test 3: oversized RRset delivered IN FULL over TCP (big.veridns TXT, ~2 KB)"
vbig="$(dig +tcp @127.0.0.1 -p "$VERI_PORT" big.veridns TXT +tries=3 +timeout="$TIMEOUT" 2>/dev/null)"
vsize="$(sed -n 's/.*MSG SIZE  rcvd: \([0-9]*\).*/\1/p' <<<"$vbig" | head -1)"
vtc="$(grep -q ' tc ' <<<"$vbig" && echo 1 || echo 0)"
if [ "$vtc" = 0 ] && [ "${vsize:-0}" -gt 1500 ]; then
  pass "veri-dns served the full ~2 KB TXT over TCP (rcvd=${vsize}B, TC=0 — no truncation)"
else
  bad "big.veridns TXT over TCP: TC=$vtc size=${vsize:-?} (expected TC=0 and >1500B)"
fi
diff_tcp big.veridns TXT NOERROR

echo "==> sub-test 4: NXDOMAIN parity over TCP (nx.veridns A)"
diff_tcp nx.veridns A NXDOMAIN

echo "==> sub-test 5: stalled clients must not block others (057/067)"
# Hold two connections open that never send a byte; a third client's query
# must still be answered promptly (old serial accept loop: each stalled
# connection blocked the loop for the full 3 s read timeout).
( sleep 8 | nc 127.0.0.1 "$VERI_PORT" ) >/dev/null 2>&1 &
STALL1=$!
( sleep 8 | nc 127.0.0.1 "$VERI_PORT" ) >/dev/null 2>&1 &
STALL2=$!
sleep 0.5
t0="$($PY -c 'import time; print(time.time())')"
stalled_out="$(dig +tcp @127.0.0.1 -p "$VERI_PORT" small.veridns A +tries=1 +timeout=3 2>/dev/null)"
t1="$($PY -c 'import time; print(time.time())')"
elapsed="$($PY -c "print('%.2f' % ($t1 - $t0))")"
kill "$STALL1" "$STALL2" 2>/dev/null
if grep -q 'status: NOERROR' <<<"$stalled_out" \
    && $PY -c "import sys; sys.exit(0 if $elapsed < 2.0 else 1)"; then
  pass "query answered in ${elapsed}s while 2 stalled connections were held open"
else
  bad "stalled-client hang: elapsed=${elapsed}s, rcode=$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$stalled_out" | head -1)"
fi

echo "==> sub-test 6: TCP connection reuse, 2 pipelined queries (058, RFC 7766)"
reuse_out="$("$PY" - "$VERI_PORT" <<'PYEOF'
import socket, struct, sys
import dns.message, dns.rcode

port = int(sys.argv[1])

def recvn(s, n):
    b = b""
    while len(b) < n:
        c = s.recv(n - len(b))
        if not c:
            raise EOFError("connection closed before %d bytes" % n)
        b += c
    return b

def read_msg(s):
    (l,) = struct.unpack(">H", recvn(s, 2))
    return recvn(s, l)

q1 = dns.message.make_query("small.veridns.", "A")
q2 = dns.message.make_query("nx.veridns.", "A")
w1, w2 = q1.to_wire(), q2.to_wire()
s = socket.create_connection(("127.0.0.1", port), timeout=10)
s.sendall(struct.pack(">H", len(w1)) + w1 + struct.pack(">H", len(w2)) + w2)
r1 = dns.message.from_wire(read_msg(s))
r2 = dns.message.from_wire(read_msg(s))
s.close()
assert r1.id == q1.id, "first response id mismatch"
assert r2.id == q2.id, "second response id mismatch (connection not reused?)"
rc1, rc2 = dns.rcode.to_text(r1.rcode()), dns.rcode.to_text(r2.rcode())
assert rc1 == "NOERROR", "q1 rcode %s" % rc1
assert rc2 == "NXDOMAIN", "q2 rcode %s" % rc2
print("OK: both pipelined queries answered on one connection (%s, %s)" % (rc1, rc2))
PYEOF
)" && reuse_rc=0 || reuse_rc=1
if [ "$reuse_rc" = 0 ]; then
  pass "connection reuse: $reuse_out"
else
  bad "connection reuse failed: $reuse_out"
fi

echo "==> sub-test 7: 300-record ~24 KB RRset assembles fast over TCP (060c)"
# First query populates the cache (upstream fetch + ingest + assembly);
# second is a pure cache-hit + reply-assembly, which must be fast.
vhuge1="$(dig +tcp @127.0.0.1 -p "$VERI_PORT" huge.veridns TXT +tries=1 +timeout=25 2>/dev/null)"
h0="$($PY -c 'import time; print(time.time())')"
vhuge2="$(dig +tcp @127.0.0.1 -p "$VERI_PORT" huge.veridns TXT +tries=1 +timeout=25 2>/dev/null)"
h1="$($PY -c 'import time; print(time.time())')"
helapsed="$($PY -c "print('%.2f' % ($h1 - $h0))")"
hcount="$(sed -n 's/.*ANSWER: \([0-9]*\).*/\1/p' <<<"$vhuge2" | head -1)"
hsize="$(sed -n 's/.*MSG SIZE  rcvd: \([0-9]*\).*/\1/p' <<<"$vhuge2" | head -1)"
if [ "${hcount:-0}" -eq 300 ] \
    && $PY -c "import sys; sys.exit(0 if $helapsed < 2.0 else 1)"; then
  pass "300-record TXT served over TCP in ${helapsed}s (rcvd=${hsize}B)"
else
  bad "huge.veridns TXT: answers=${hcount:-?} size=${hsize:-?} elapsed=${helapsed}s (want 300 answers, <2s)"
fi
diff_tcp huge.veridns TXT NOERROR

echo
[ "$fail" -eq 0 ] && echo "==> STAGE S ALL PASS" || echo "==> STAGE S FAILURES"
exit "$fail"
