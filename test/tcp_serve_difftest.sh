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

echo
[ "$fail" -eq 0 ] && echo "==> STAGE S ALL PASS" || echo "==> STAGE S FAILURES"
exit "$fail"
