#!/usr/bin/env bash
# inject_difftest.sh — finding 017 rig.
#
# Reproduces 017's original repro: a junk datagram sent from the LEGITIMATE
# upstream source:port, before the real reply. The prior "fix" filtered only
# on source address, so junk from the right source consumed the round and the
# real reply was dropped. The read-until-match floor (veri_dns_exchange skips a
# datagram that fails the id/question content match and keeps reading until a
# matching reply or the round deadline) must let veri-dns still deliver the
# real answer. The mock is a FLAT authoritative root (test/mock_auth.py) run
# with --inject-junk, so every real UDP reply is preceded by two same-source
# junk datagrams.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
PY="$ROOT/test/.venv/bin/python"
MOCK="$ROOT/test/mock_auth.py"

# Distinct ports (not the 5300/5354/5399 used by the other rigs) so this rig can
# run alongside a sibling worktree's mock/veri-dns without a bind collision.
MOCK_PORT=5364
VERI_PORT=5310
UNBOUND_PORT=5409
TIMEOUT=15

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/veridns-inject.XXXXXX")"
MOCK_LOG="$WORKDIR/mock.jsonl"
UNBOUND_CONF="$WORKDIR/unbound.conf"

MOCK_PID=""; UNBOUND_PID=""; VERI_PID=""
cleanup() {
  # Kill only our own children by PID — never pkill by name, so a sibling
  # worktree's mock/veri-dns on the default ports is left untouched.
  for p in "$MOCK_PID" "$UNBOUND_PID" "$VERI_PID"; do
    [ -n "$p" ] && kill "$p" 2>/dev/null
  done
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

fail=0
pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad()  { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fail=1; }

start_mock() {
  : > "$MOCK_LOG"
  "$PY" "$MOCK" --port "$MOCK_PORT" --log "$MOCK_LOG" $1 >"$WORKDIR/mock.err" 2>&1 &
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
  [ -n "$VERI_PID" ] && kill "$VERI_PID" 2>/dev/null; sleep 0.4
  VERI_DNS_ROOT_HINT=127.0.0.1 \
  VERI_DNS_UPSTREAM_PORT="$MOCK_PORT" \
  VERI_DNS_LISTEN_PORT="$VERI_PORT" \
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

probe() {
  local port="$1" name="$2" typ="$3"; shift 3
  local out rcode ans
  out="$(dig @127.0.0.1 -p "$port" "$name" "$typ" +tries=3 +timeout="$TIMEOUT" "$@" 2>/dev/null)"
  [ -z "$out" ] && { echo "NORESPONSE|"; return; }
  rcode="$(sed -n 's/.*status: \([A-Z]*\).*/\1/p' <<<"$out" | head -1)"
  ans="$(awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && $1!~/^;/ && NF>=5{$1=$2=$3=$4="";sub(/^ +/,"");print}' <<<"$out" | sort | tr '\n' ';')"
  echo "${rcode:-NONE}|$ans"
}

echo "==> starting mock (--inject-junk: same-source junk before every reply), unbound, veri-dns"
start_mock "--inject-junk"
start_unbound
start_veri
# Primary gate: veri-dns must deliver the real answer through same-source junk.
# The beacon (small.veridns) itself must resolve through the injecting mock.
if ! wait_ready "$VERI_PORT" veri-dns small.veridns; then
  echo "--- veri.log ---"; tail -30 "$WORKDIR/veri.log"
  bad "veri-dns never resolved small.veridns through same-source junk"
  echo; echo "==> 017 INJECT RIG FAILURES"; exit 1
fi

echo "==> sub-test 1 (017): real answer survives same-source junk (small.veridns A)"
v="$(probe "$VERI_PORT" small.veridns A)"
if [ "${v%%|*}" = "NOERROR" ] && [ "${v#*|}" = "127.0.0.1;" ]; then
  pass "veri-dns delivered the real answer despite same-source junk ($v)"
else
  bad "veri-dns=[$v] (expected NOERROR 127.0.0.1); real reply lost behind junk"
  echo "--- veri.log ---"; tail -30 "$WORKDIR/veri.log"
fi

echo "==> sub-test 2 (017): a distinct uncached name is equally unaffected (slow2.veridns A)"
v2="$(probe "$VERI_PORT" slow2.veridns A)"
if [ "${v2%%|*}" = "NOERROR" ] && [ "${v2#*|}" = "127.0.0.1;" ]; then
  pass "second uncached name delivered through junk ($v2)"
else
  bad "veri-dns=[$v2] (expected NOERROR 127.0.0.1)"
  echo "--- veri.log ---"; tail -20 "$WORKDIR/veri.log"
fi

# Secondary cross-check: unbound as an oracle, best-effort. Real unbound may
# itself stumble on same-source question-mismatch junk (it is not a read-until-
# match reference under this fault), so a mismatch here is reported, not failed.
echo "==> cross-check (best-effort): unbound under the same injecting mock"
if wait_ready "$UNBOUND_PORT" unbound small.veridns >/dev/null 2>&1; then
  u="$(probe "$UNBOUND_PORT" small.veridns A)"
  if [ "$v" = "$u" ]; then pass "veri==unbound ($v)"; else echo "  (note) unbound=[$u] differs from veri=[$v] under injection"; fi
else
  echo "  (skip) unbound did not resolve through the injecting mock"
fi

echo
[ "$fail" -eq 0 ] && echo "==> 017 INJECT RIG ALL PASS" || echo "==> 017 INJECT RIG FAILURES"
exit "$fail"
