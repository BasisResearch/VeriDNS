#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
CORPUS="$ROOT/test/corpus.txt"

VERI_PORT=5300
UNBOUND_PORT=5399
TIMEOUT=15

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/veridns-difftest.XXXXXX")"
UNBOUND_CONF="$WORKDIR/unbound.conf"
VERI_LOG="$WORKDIR/veri.log"
UNBOUND_LOG="$WORKDIR/unbound.log"

cleanup() {
  [ -n "${VERI_PID:-}" ] && kill "$VERI_PID" 2>/dev/null
  [ -n "${UNBOUND_PID:-}" ] && kill "$UNBOUND_PID" 2>/dev/null
  pkill -f 'bin/veri-dns' 2>/dev/null
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

cat > "$UNBOUND_CONF" <<EOF
server:
  verbosity: 0
  interface: 127.0.0.1
  port: $UNBOUND_PORT
  do-ip6: no
  access-control: 127.0.0.0/8 allow
  username: ""
  directory: "$WORKDIR"
  logfile: "$UNBOUND_LOG"
  pidfile: "$WORKDIR/unbound.pid"
  chroot: ""
  hide-identity: yes
  hide-version: yes
  qname-minimisation: no
  harden-glue: yes
EOF

start_servers() {
  echo "==> starting unbound on 127.0.0.1:$UNBOUND_PORT"
  unbound -d -p -c "$UNBOUND_CONF" >"$UNBOUND_LOG" 2>&1 &
  UNBOUND_PID=$!

  echo "==> starting veri-dns on 127.0.0.1:$VERI_PORT"
  pkill -f 'bin/veri-dns' 2>/dev/null
  "$BIN" >"$VERI_LOG" 2>&1 &
  VERI_PID=$!

  sleep 2
  if ! kill -0 "$UNBOUND_PID" 2>/dev/null; then
    echo "!! unbound failed to start:"; cat "$UNBOUND_LOG"; exit 2
  fi
  if ! kill -0 "$VERI_PID" 2>/dev/null; then
    echo "!! veri-dns failed to start:"; cat "$VERI_LOG"; exit 2
  fi

  dig @127.0.0.1 -p "$VERI_PORT" example.net A +tries=1 +timeout="$TIMEOUT" >/dev/null 2>&1 || true
  dig @127.0.0.1 -p "$UNBOUND_PORT" example.net A +tries=1 +timeout="$TIMEOUT" >/dev/null 2>&1 || true
}

probe() {
  local port="$1" name="$2" typ="$3"
  local out rcode tc ans
  out="$(dig @127.0.0.1 -p "$port" "$name" "$typ" +tries=1 +timeout="$TIMEOUT" 2>/dev/null)"
  if [ -z "$out" ]; then echo "STATUS|NORESPONSE|TC|0|"; return; fi
  rcode="$(printf '%s\n' "$out" | sed -n 's/.*status: \([A-Z]*\).*/\1/p' | head -1)"
  if printf '%s\n' "$out" | grep -q ' tc '; then tc=1; else tc=0; fi
  ans="$(printf '%s\n' "$out" | awk '/^;; ANSWER SECTION:/{f=1;next} /^;;/{f=0} f && NF>=5 && $1!~/^;/{ $1=$2=$3=$4=""; sub(/^ +/,""); print }' | sort | tr '\n' ';')"
  echo "STATUS|${rcode:-NONE}|TC|$tc|$ans"
}

run_one() {
  local name="$1" typ="$2"
  local v u vstat ustat vtc utc vans uans
  v="$(probe "$VERI_PORT" "$name" "$typ")"
  u="$(probe "$UNBOUND_PORT" "$name" "$typ")"
  vstat="$(cut -d'|' -f2 <<<"$v")"; utc="$(cut -d'|' -f4 <<<"$u")"
  ustat="$(cut -d'|' -f2 <<<"$u")"; vtc="$(cut -d'|' -f4 <<<"$v")"
  vans="$(cut -d'|' -f5 <<<"$v")"; uans="$(cut -d'|' -f5 <<<"$u")"

  if [ "$vstat" != "$ustat" ]; then
    printf '  %-40s %-6s DIFF   veri=%s unbound=%s\n' "$name" "$typ" "$vstat" "$ustat"
    return 1
  fi
  if [ "$vstat" = "NOERROR" ]; then
    if [ -z "$vans" ] && [ -n "$uans" ]; then
      printf '  %-40s %-6s DIFF   veri answer empty, unbound non-empty\n' "$name" "$typ"
      return 1
    fi
  fi
  printf '  %-40s %-6s OK     %s\n' "$name" "$typ" "$vstat"
  return 0
}

start_servers

fails=0; total=0
if [ "$#" -ge 2 ]; then
  total=1
  run_one "$1" "$2" || fails=1
else
  echo "==> replaying corpus $CORPUS"
  while read -r line; do
    line="${line%%#*}"
    [ -z "${line// }" ] && continue
    name="${line%% *}"; typ="${line##* }"
    total=$((total+1))
    run_one "$name" "$typ" || fails=$((fails+1))
  done < "$CORPUS"
fi

echo "==> $((total-fails))/$total matched unbound"
[ "$fails" -eq 0 ]
