#!/usr/bin/env bash
# vm-up.sh — runs INSIDE the test VM as root. Builds the network-namespace
# topology and starts the fake authoritative hierarchy + both resolvers.
#
# Topology (all on bridge brdns, 203.0.113.0/24, in the VM root netns):
#
#   +---------------+  +---------------+  +---------------+  +---------------+
#   |     auth      |  |     verid     |  |    unbound    |  |   attacker    |
#   | 203.0.113.10  |  | 203.0.113.2   |  | 203.0.113.3   |  | 192.168.53.99 |
#   | + .11  .12    |  |   veri-dns    |  |    unbound    |  |  dig / spoof  |
#   | + root IPs    |  |    :5300      |  |    :5301      |  |  (CLIENT ACL) |
#   |   nsd :53     |  +---------------+  +---------------+  +---------------+
#   +---------------+           \                |                 /
#           \                    \               |                /
#            `-------------- brdns (203.0.113.1/24) -------------'
#
# Two subnets share the one bridge: the rig runs on 203.0.113.0/24 and the
# client on 192.168.53.0/24. That split is FORCED by veri-dns -- see 2b.
#
# The 5 real root-server IPs (hardcoded in VeriDNS/Main.lean) are bound on
# `auth`; verid/unbound/attacker get /32 on-link routes to them, so veri-dns's
# hardcoded root queries land on our fake root.
#
# WHY 203.0.113.0/24 (TEST-NET-3) AND NOT 10.53.0.0/24: veri-dns ships an
# egress filter (`doNotQueryNets`, VeriDNS/Impl/Server.lean) that refuses to
# query 0/8, 127/8, 10/8, 100.64/10, 169.254/16, 172.16/12, 192.168/16, 240/4.
# On the old 10.53.0.0/24 addresses the resolver would refuse to talk to its
# own auth servers and every test would fail spuriously. TEST-NET-3 is not in
# that list, so the shipped filter stays ACTIVE and honest -- do NOT paper over
# this with VERI_DNS_ALLOW_LOOPBACK_EGRESS=1, which disables the filter and
# would mask real egress bugs.
set -euo pipefail

STAGE_SRC="$(cd "$(dirname "$0")" && pwd)"   # e.g. /root/dev/_vmdns
DEST=/opt/dnsenv

# Real root-server IPs hardcoded in VeriDNS/Main.lean (a..e.root-servers.net).
ROOT_IPS="198.41.0.4 199.9.14.201 192.33.14.30 199.7.91.13 192.203.230.10"

# Client/attacker vantage. MUST live inside veri-dns's defaultAcl (127/8, 10/8,
# 172.16/12, 192.168/16) or its queries are silently dropped. See the long
# comment in section 2b.
CLIENT_NET="192.168.53.0/24"
CLIENT_IP="192.168.53.99"

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
log "creating bridge brdns 203.0.113.1/24"
ip link add brdns type bridge
ip addr add 203.0.113.1/24 dev brdns
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
make_ns auth     203.0.113.10
make_ns verid    203.0.113.2
make_ns unbound  203.0.113.3
# NOTE: the attacker/client sits on 192.168.53.0/24, NOT on 203.0.113.0/24.
# See "WHY THE CLIENT IS NOT ON TEST-NET-3" below -- this is forced by
# veri-dns's client ACL and is NOT an arbitrary choice.
make_ns attacker "$CLIENT_IP"

# auth also owns the TLD/leaf NS addresses and the fake-root IPs.
ip netns exec auth ip addr add 203.0.113.11/24 dev v-auth
ip netns exec auth ip addr add 203.0.113.12/24 dev v-auth
for rip in $ROOT_IPS; do
  ip netns exec auth ip addr add "$rip/32" dev v-auth
done

# resolvers + attacker need on-link /32 routes to reach the fake-root IPs.
for ns in verid unbound attacker; do
  for rip in $ROOT_IPS; do
    ip netns exec "$ns" ip route add "$rip/32" dev "v-$ns"
  done
done

# --- 2b. cross-subnet on-link routes (client <-> resolvers) -------------------
# WHY THE CLIENT IS NOT ON TEST-NET-3 -- veri-dns pins us from both sides:
#
#   doNotQueryNets (egress, Impl/Server.lean): refuses to QUERY
#       0/8, 127/8, 10/8, 100.64/10, 169.254/16, 172.16/12, 192.168/16, 240/4
#   defaultAcl     (ingress, Impl/Server.lean): only accepts CLIENTS from
#       127/8, 10/8, 172.16/12, 192.168/16      <-- an exact SUBSET of the above
#
# So the set of addresses veri-dns will both talk to AND accept queries from is
# EMPTY. One subnet cannot host both the auth servers and the client:
#   * auth servers MUST be outside doNotQueryNets  -> 203.0.113.0/24 (TEST-NET-3)
#   * the client   MUST be inside  defaultAcl      -> 192.168.53.0/24
# A client address is never an egress target, so putting the client in
# 192.168/16 does NOT weaken the egress filter: it stays ACTIVE and honest, and
# VERI_DNS_ALLOW_LOOPBACK_EGRESS is NOT set. On 203.0.113.99 the client's
# queries are SILENTLY DROPPED by `if !permitted acl clientAddr then return
# cache` (UDP: timeout; TCP: accept-then-EOF) -- which is what a resolver should
# do to a stranger, not a bug. It just means the rig must split the two roles.
#
# Everything shares bridge brdns, so plain on-link routes suffice (ARP resolves
# across the two subnets on the same L2 segment).
log "wiring client subnet $CLIENT_NET <-> rig subnet 203.0.113.0/24 (on-link)"
ip netns exec attacker ip route add 203.0.113.0/24 dev v-attacker
for ns in verid unbound; do
  ip netns exec "$ns" ip route add "$CLIENT_NET" dev "v-$ns"
done
# auth too, so the client can dig the authoritative servers directly.
ip netns exec auth ip route add "$CLIENT_NET" dev v-auth

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
