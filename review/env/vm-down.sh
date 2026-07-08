#!/usr/bin/env bash
# vm-down.sh — runs INSIDE the test VM as root. Tears the rig down: stops the
# daemons and removes the namespaces + bridge. Safe to run repeatedly.
set -u

# stop every transient veridns-* systemd unit (started by vm-up.sh). Enumerate
# so stale units from older runs are caught too -- a lingering unit keeps its
# netns + veth alive and makes the next bring-up fail with "File exists".
for u in $(systemctl list-units --all --plain --no-legend 'veridns*' 2>/dev/null | awk '{print $1}'); do
  systemctl stop "$u"         >/dev/null 2>&1 || true
  systemctl reset-failed "$u" >/dev/null 2>&1 || true
done
# belt and braces
pkill -f 'veri-dns' >/dev/null 2>&1 || true
pkill -x nsd        >/dev/null 2>&1 || true
pkill -x unbound    >/dev/null 2>&1 || true

for ns in auth verid unbound attacker; do
  ip netns del "$ns" 2>/dev/null || true
done
ip link del brdns 2>/dev/null || true

echo ">> environment down."
