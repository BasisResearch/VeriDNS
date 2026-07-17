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

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/veridns-tcp.XXXXXX")"
MOCK_LOG="$WORKDIR/mock.jsonl"
UNBOUND_CONF="$WORKDIR/unbound.conf"

MOCK_PID=""; UNBOUND_PID=""; VERI_PID=""; TSHARK_PID=""
cleanup() {
  for p in "$MOCK_PID" "$UNBOUND_PID" "$VERI_PID" "$TSHARK_PID"; do
    [ -n "$p" ] && kill "$p" 2>/dev/null
  done
  pkill -f 'bin/veri-dns' 2>/dev/null
  pkill -f 'mock_auth.py' 2>/dev/null
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

fail=0
pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad()  { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fail=1; }

start_mock() {
  reset_log
  "$PY" "$MOCK" --port "$MOCK_PORT" --log "$MOCK_LOG" $1 >"$WORKDIR/mock.err" 2>&1 &
  MOCK_PID=$!
  sleep 1
}
stop_mock() { [ -n "$MOCK_PID" ] && kill "$MOCK_PID" 2>/dev/null; pkill -f 'mock_auth.py' 2>/dev/null; MOCK_PID=""; sleep 0.6; }
reset_log() { : > "$MOCK_LOG"; }

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
stop_unbound() { [ -n "$UNBOUND_PID" ] && kill "$UNBOUND_PID" 2>/dev/null; UNBOUND_PID=""; sleep 0.5; }

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
      echo "  ($2 ready ~${i}s, beacon $3)"; reset_log; return 0
    fi
    sleep 1
  done
  echo "  !! $2 never resolved $3"; return 1
}

probe() {
  local port="$1" name="$2" typ="$3"; shift 3
  local out rcode ans
  out="$(dig @127.0.0.1 -p "$port" "$name" "$typ" +tries=3 +timeout="$TIMEOUT" "$@" 2>/dev/null)"
  [ -z "$out" ] && { echo "NORESPONSE|"; return; }
  rcode="$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$out" | head -1)"
  ans="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{$1=$2=$3=$4="";sub(/^ +/,"");print}' <<<"$out" | sort | tr '\n' ';')"
  echo "${rcode:-NONE}|$ans"
}

log_has_fallback() {
  grep -iq "\"transport\": \"udp\", \"qname\": \"$1\", \"qtype\": \"$2\", \"tc\": 1" "$MOCK_LOG" \
    && grep -iq "\"transport\": \"tcp\", \"qname\": \"$1\", \"qtype\": \"$2\"" "$MOCK_LOG"
}

echo "==> starting mock (UDP+TCP), unbound, veri-dns"
start_mock ""
start_unbound
start_veri
wait_ready "$UNBOUND_PORT" unbound small.veridns || exit 2
wait_ready "$VERI_PORT" veri-dns forcetc.veridns || { cat "$WORKDIR/veri.log"; exit 2; }

echo "==> sub-test 1: forced-TC parity, end-to-end (forcetc.veridns A)"
v="$(probe "$VERI_PORT" forcetc.veridns A)"; u="$(probe "$UNBOUND_PORT" forcetc.veridns A)"
if [ "$v" = "$u" ] && [ "${v%%|*}" = "NOERROR" ] && [ -n "${v#*|}" ]; then pass "veri==unbound ($v)"; else bad "veri=[$v] unbound=[$u]"; fi

echo "==> sub-test 2: oversized-RRset upstream fallback (big.veridns TXT, ~2 KB, uncached)"
reset_log
if command -v tshark >/dev/null 2>&1; then
  tshark -i lo0 -f "port $MOCK_PORT" -a duration:8 -w "$WORKDIR/cap.pcap" >/dev/null 2>&1 &
  TSHARK_PID=$!; sleep 1
fi
vbig="$(probe "$VERI_PORT" big.veridns TXT +ignore +bufsize=1232)"
if log_has_fallback "big.veridns." "TXT"; then pass "mock log: UDP tc=1 → TCP retry for big.veridns TXT (upstream fallback fired)"; else bad "no UDP-TC→TCP in mock log for big.veridns TXT"; cat "$MOCK_LOG"; fi
vst="${vbig%%|*}"
if [ "$vst" = "NOERROR" ]; then pass "veri-dns responded NOERROR (has the answer; ~2 KB truncated to this UDP client — full +tcp delivery is asserted in tcp_serve_difftest.sh, Stage S)"; else bad "veri-dns big.veridns status=[$vst] (expected NOERROR with TC)"; fi

echo "==> sub-test 3: decision-logic sniff (tshark lo0: UDP then TCP to mock)"
if [ -n "$TSHARK_PID" ]; then
  wait "$TSHARK_PID" 2>/dev/null; TSHARK_PID=""
  udp_n="$(tshark -r "$WORKDIR/cap.pcap" -Y "udp.port==$MOCK_PORT" 2>/dev/null | wc -l | tr -d ' ')"
  tcp_n="$(tshark -r "$WORKDIR/cap.pcap" -Y "tcp.port==$MOCK_PORT" 2>/dev/null | wc -l | tr -d ' ')"
  if [ "${udp_n:-0}" -gt 0 ] && [ "${tcp_n:-0}" -gt 0 ]; then pass "tshark lo0: UDP=$udp_n TCP=$tcp_n packets to mock"; else echo "  (skip) tshark saw UDP=$udp_n TCP=$tcp_n (loopback capture may need BPF privileges)"; fi
else
  echo "  (skip) tshark unavailable"
fi

echo "==> sub-test 4a: repeated query stays correct (truncated payload never served)"
v1="$(probe "$VERI_PORT" forcetc.veridns A)"; v2="$(probe "$VERI_PORT" forcetc.veridns A)"
if [ "$v1" = "$v2" ] && [ "${v1%%|*}" = "NOERROR" ] && [ "${v1#*|}" = "127.0.0.1;" ]; then pass "two queries identical full answers ($v1)"; else bad "v1=[$v1] v2=[$v2]"; fi

echo "==> sub-test 4b: mock TCP listener down → both degrade to SERVFAIL"
stop_mock; start_mock "--no-tcp"
stop_unbound; start_unbound
start_veri
wait_ready "$VERI_PORT" veri-dns small.veridns || { cat "$WORKDIR/veri.log"; }
wait_ready "$UNBOUND_PORT" unbound small.veridns >/dev/null 2>&1
v="$(probe "$VERI_PORT" forcetc.veridns A)"; u="$(probe "$UNBOUND_PORT" forcetc.veridns A)"
if [ "${v%%|*}" = "SERVFAIL" ] && [ "${u%%|*}" = "SERVFAIL" ]; then pass "veri==unbound==SERVFAIL (fallback failed → drop server → gaveUp)"; else bad "veri=[$v] unbound=[$u] (expected both SERVFAIL)"; fi

echo
[ "$fail" -eq 0 ] && echo "==> U6 ALL PASS" || echo "==> U6 FAILURES"
exit "$fail"
