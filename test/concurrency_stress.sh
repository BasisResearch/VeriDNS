#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
PY="$ROOT/test/.venv/bin/python"
MOCK="$ROOT/test/mock_auth.py"

MOCK_PORT=5354
VERI_PORT=5300

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/veridns-conc.XXXXXX")"
MOCK_LOG="$WORKDIR/mock.jsonl"

MOCK_PID=""; VERI_PID=""
cleanup() {
  for p in "$MOCK_PID" "$VERI_PID"; do [ -n "$p" ] && kill "$p" 2>/dev/null; done
  pkill -f 'bin/veri-dns' 2>/dev/null
  pkill -f 'mock_auth.py' 2>/dev/null
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

fail=0
pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad()  { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fail=1; }
now_ms() { "$PY" -c 'import time;print(int(time.time()*1000))'; }

start_mock() {
  : > "$MOCK_LOG"
  "$PY" "$MOCK" --port "$MOCK_PORT" --log "$MOCK_LOG" >"$WORKDIR/mock.err" 2>&1 &
  MOCK_PID=$!
  sleep 1
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
    if dig @127.0.0.1 -p "$VERI_PORT" small.veridns A +tries=1 +timeout=2 +short 2>/dev/null \
        | grep -q '127.0.0.1'; then
      echo "  (veri-dns ready ~${i}s)"; return 0
    fi
    sleep 1
  done
  echo "  !! veri-dns never came up"; cat "$WORKDIR/veri.log"; return 1
}

probe() {
  local tcp="" out rcode ans
  [ "${3:-}" = tcp ] && tcp="+tcp"
  out="$(dig $tcp @127.0.0.1 -p "$VERI_PORT" "$1" "$2" +tries=1 +timeout=4 2>/dev/null)"
  [ -z "$out" ] && { echo "NORESPONSE|"; return; }
  rcode="$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$out" | head -1)"
  ans="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{print $5}' <<<"$out" | sort | tr '\n' ';')"
  echo "${rcode:-NONE}|$ans"
}

noblock() {
  local slowname="$1" st="$2" ft="$3" label="$4"
  sleep 0.5; probe small.veridns A >/dev/null
  ( s=$(now_ms); probe "$slowname" A "$st" >/dev/null 2>&1; echo $(( $(now_ms) - s )) > "$WORKDIR/slowdt" ) &
  local bg=$!
  sleep 0.3
  local t0 t1 fast
  t0=$(now_ms); fast="$(probe small.veridns A "$ft")"; t1=$(now_ms)
  wait "$bg" 2>/dev/null
  local slowdt fastdt
  slowdt="$(cat "$WORKDIR/slowdt" 2>/dev/null || echo 0)"
  fastdt=$(( t1 - t0 ))
  if [ "${fast%%|*}" = NOERROR ] && [ "$fastdt" -lt $(( slowdt / 2 )) ] && [ "$fastdt" -lt 700 ]; then
    pass "$label: fast ${ft^^} client ${fastdt}ms ≪ concurrent slow resolution ${slowdt}ms"
  else
    bad "$label: fast=${fastdt}ms slow=${slowdt}ms answer=[$fast] (fast must be < slow/2 and < 700ms)"
  fi
}

echo "==> starting mock + veri-dns (hermetic)"
start_mock
start_veri
wait_ready || exit 2

echo "==> warming cache"
for n in forcetc.veridns nx.veridns; do probe "$n" A >/dev/null; done
probe big.veridns TXT >/dev/null

echo "==> check A1: slow UDP resolution must not block a concurrent fast TCP client"
noblock slow.veridns "" tcp A1
echo "==> check A2: slow TCP resolution must not block a concurrent fast UDP client"
noblock slow2.veridns tcp "" A2

echo "==> check B: correctness + cache consistency under a concurrent UDP+TCP burst"
declare -a NAMES=(small.veridns forcetc.veridns big.veridns nx.veridns)
: > "$WORKDIR/burst.out"
burst_pids=()
for i in $(seq 1 16); do
  name="${NAMES[$(( i % 4 ))]}"
  transport=""; [ $(( i % 2 )) -eq 0 ] && transport=tcp
  ty=A; [ "$name" = big.veridns ] && ty=TXT
  (
    r="$(probe "$name" "$ty" "$transport")"
    want=NOERROR; [ "$name" = nx.veridns ] && want=NXDOMAIN
    if [ "${r%%|*}" = "$want" ]; then echo "ok $name" ; else echo "BAD $name [$r]"; fi
  ) >> "$WORKDIR/burst.out" &
  burst_pids+=($!)
done
for p in "${burst_pids[@]}"; do wait "$p" 2>/dev/null; done
nbad="$(grep -c '^BAD' "$WORKDIR/burst.out" 2>/dev/null || true)"; nbad=${nbad:-0}
nok="$(grep -c '^ok' "$WORKDIR/burst.out" 2>/dev/null || true)"; nok=${nok:-0}
if [ "$nbad" -eq 0 ] && [ "$nok" -eq 16 ]; then
  pass "all 16 concurrent UDP+TCP clients got the correct answer (no race/merge corruption)"
else
  bad "concurrent burst: $nok ok, $nbad bad"; grep '^BAD' "$WORKDIR/burst.out" 2>/dev/null
fi

post="$(probe small.veridns A)"
if [ "$post" = "NOERROR|127.0.0.1;" ]; then
  pass "cache still serves correct data after concurrent merges ($post)"
else
  bad "post-burst cache check: [$post] (want NOERROR|127.0.0.1;)"
fi

echo
[ "$fail" -eq 0 ] && echo "==> L6 CONCURRENCY ALL PASS" || echo "==> L6 CONCURRENCY FAILURES"
exit "$fail"
