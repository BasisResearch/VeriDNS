#!/usr/bin/env bash
# restart-verid.sh -- HOST-side: re-stage the freshly built veri-dns binary and
# restart ONLY the resolver-under-test unit inside the VM (leaves the fake
# hierarchy and unbound untouched). Use after `lake build`.
set -euo pipefail
REPO=/home/yiyun/Experiments/VeriDNS
PENN="$REPO/penn-testing"
BIN="$REPO/.lake/build/bin/veri-dns"
[ -x "$BIN" ] || { echo "no binary at $BIN -- run 'lake build'"; exit 1; }
cp -a "$BIN" "$PENN/_vmdns/veri-dns"          # -> /root/dev/_vmdns/veri-dns in VM
timeout 60 "$PENN/vm/ssh.sh" '
  systemctl stop veridns-verid 2>/dev/null || true
  rm -f /opt/dnsenv/veri-dns
  cp -a /root/dev/_vmdns/veri-dns /opt/dnsenv/veri-dns
  chmod +x /opt/dnsenv/veri-dns
  : > /run/veridns-verid.log
  systemctl reset-failed veridns-verid 2>/dev/null || true
  systemd-run --unit=veridns-verid --collect \
    -p StandardOutput=append:/run/veridns-verid.log \
    -p StandardError=append:/run/veridns-verid.log \
    ip netns exec verid /opt/dnsenv/veri-dns
  sleep 1
  systemctl is-active veridns-verid
  ip netns exec attacker dig @203.0.113.2 -p 5300 host.example.test A +short'
