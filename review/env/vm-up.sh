#!/usr/bin/env bash
# vm-up.sh — runs INSIDE the test VM as root. Builds the network-namespace
# topology and starts the fake authoritative hierarchy + both resolvers.
#
# Topology (all on bridge brdns, 10.53.0.0/24, in the VM root netns):
#
#   +-----------+   +-----------+   +-----------+   +------------+
#   |   auth    |   |  verid    |   | unbound   |   |  attacker  |
#   | 10.53.0.10|   | 10.53.0.2 |   | 10.53.0.3 |   | 10.53.0.99 |
#   | +.11 .12  |   | veri-dns  |   | unbound   |   | dig/spoof  |
#   | +root IPs |   |  :5300    |   |  :5301    |   |            |
#   |  nsd :53  |   +-----------+   +-----------+   +------------+
#   +-----------+          \             |             /
#         \                 \            |            /
#          `--------------- brdns (10.53.0.1) -------'
#
# The 5 real root-server IPs (hardcoded in VeriDNS/Main.lean) are bound on
# `auth`; verid/unbound/attacker get /32 on-link routes to them, so veri-dns's
# hardcoded root queries land on our fake root.
set -euo pipefail

STAGE_SRC="$(cd "$(dirname "$0")" && pwd)"   # e.g. /root/dev/_vmdns
DEST=/opt/dnsenv

# Real root-server IPs hardcoded in VeriDNS/Main.lean (a..e.root-servers.net).
ROOT_IPS="198.41.0.4 199.9.14.201 192.33.14.30 199.7.91.13 192.203.230.10"

log(){ printf '>> %s\n' "$*"; }

# --- 0. stage a stable, writable copy of configs/zones/binary -----------------
rm -rf "$DEST"; mkdir -p "$DEST"
cp -a "$STAGE_SRC/nsd" "$STAGE_SRC/unbound" "$DEST"/
cp -a "$STAGE_SRC/veri-dns" "$DEST"/veri-dns
cp -a "$STAGE_SRC/spoof.py" "$DEST"/spoof.py 2>/dev/null || true
chmod +x "$DEST/veri-dns"

# --- 1. clean any previous run ------------------------------------------------
"$STAGE_SRC/vm-down.sh" >/dev/null 2>&1 || true

# --- 2. bridge in the root netns ---------------------------------------------
log "creating bridge brdns 10.53.0.1/24"
ip link add brdns type bridge
ip addr add 10.53.0.1/24 dev brdns
ip link set brdns up

# helper: make_ns <name> <ip>
make_ns(){
  local ns="$1" ip="$2"
  ip netns add "$ns"
  ip link add "v-$ns" type veth peer name "p-$ns"
  ip link set "p-$ns" master brdns
  ip link set "p-$ns" up
  ip link set "v-$ns" netns "$ns"
  ip netns exec "$ns" ip link set lo up
  ip netns exec "$ns" ip link set "v-$ns" up
  ip netns exec "$ns" ip addr add "$ip/24" dev "v-$ns"
}

log "creating namespaces auth/verid/unbound/attacker"
make_ns auth     10.53.0.10
make_ns verid    10.53.0.2
make_ns unbound  10.53.0.3
make_ns attacker 10.53.0.99

# auth also owns the TLD/leaf NS addresses and the fake-root IPs.
ip netns exec auth ip addr add 10.53.0.11/24 dev v-auth
ip netns exec auth ip addr add 10.53.0.12/24 dev v-auth
for rip in $ROOT_IPS; do
  ip netns exec auth ip addr add "$rip/32" dev v-auth
done

# resolvers + attacker need on-link /32 routes to reach the fake-root IPs.
for ns in verid unbound attacker; do
  for rip in $ROOT_IPS; do
    ip netns exec "$ns" ip route add "$rip/32" dev "v-$ns"
  done
done

# Daemons run as transient systemd units so they survive the ssh session that
# launches them (a plain background process gets reaped when the session scope
# is torn down on logout). `svc <unit> <netns> <cmd...>` starts one.
svc(){
  local unit="$1" ns="$2"; shift 2
  systemctl reset-failed "$unit" 2>/dev/null || true
  systemd-run --unit="$unit" --collect \
    -p "StandardOutput=append:/run/$unit.log" \
    -p "StandardError=append:/run/$unit.log" \
    ip netns exec "$ns" "$@"
}

# --- 3. start the authoritative servers (one nsd per hierarchy level) --------
# Each level serves ONLY its own zone so it hands out proper referrals; a single
# nsd serving all zones on all IPs would answer grandchild names authoritatively
# and a correct resolver (unbound) would reject that as out-of-bailiwick.
log "starting nsd root/tld/leaf (authoritative) in auth ns"
for lvl in root tld leaf; do
  nsd-checkconf "$DEST/nsd/nsd-$lvl.conf"
  : > "/run/veridns-auth-$lvl.log"
  svc "veridns-auth-$lvl" auth nsd -c "$DEST/nsd/nsd-$lvl.conf" -d
done

# --- 4. start the reference resolver -----------------------------------------
log "starting unbound (reference resolver) in unbound ns"
unbound-checkconf "$DEST/unbound/unbound.conf"
: > /run/veridns-ref.log
svc veridns-ref unbound unbound -d -c "$DEST/unbound/unbound.conf"

# --- 5. start the resolver under test ----------------------------------------
log "starting veri-dns (resolver under test) in verid ns"
: > /run/veridns-verid.log
svc veridns-verid verid "$DEST/veri-dns"

sleep 2
log "environment up. listeners:"
ip netns exec auth    ss -ulnp 2>/dev/null | grep -E ':53 '   || true
ip netns exec unbound ss -ulnp 2>/dev/null | grep -E ':5301'  || true
ip netns exec verid   ss -ulnp 2>/dev/null | grep -E ':5300'  || true
log "units:"; systemctl --no-legend list-units 'veridns-*' 2>/dev/null || true
log "done."
