#!/usr/bin/env bash
# up.sh -- HOST-side one-command bring-up of the VeriDNS differential-testing
# rig. Stages the configs + the freshly built veri-dns binary into the VM's
# bind mount, makes sure the VM has the packages it needs, then builds the
# network-namespace topology and starts everything inside the VM.
#
# Prerequisite: the test VM must already be booted in another terminal:
#     cd penn-testing && make vm      # leave it running
# Then:
#     review/env/up.sh
set -euo pipefail

REPO=/home/yiyun/Experiments/VeriDNS
ENVDIR="$REPO/review/env"
PENN="$REPO/penn-testing"
SSH="$PENN/vm/ssh.sh"
BIN="$REPO/.lake/build/bin/veri-dns"

# penn-testing/ is the tree bind-mounted at /root/dev inside the VM, so files
# placed under STAGE_HOST appear at STAGE_VM in the guest.
STAGE_HOST="$PENN/_vmdns"
STAGE_VM="/root/dev/_vmdns"

log(){ printf '\n== %s ==\n' "$*"; }

[ -x "$BIN" ] || { echo "veri-dns binary not found at $BIN -- run 'lake build'"; exit 1; }

log "0. checking the VM is reachable over vsock"
if ! timeout 20 "$SSH" true 2>/dev/null; then
  echo "VM not reachable. Boot it first:  cd $PENN && make vm"
  exit 1
fi

log "1. staging configs + veri-dns binary into $STAGE_HOST"
# NOTE: /root/dev is a *virtiofs* share. Do NOT `rm -rf "$STAGE_HOST"` and
# recreate it: the new directory gets a new inode while the guest still has the
# old one cached, so every child lookup inside the VM fails with ENOENT
# ("bash: /root/dev/_vmdns/vm-up.sh: No such file or directory", exit 127) until
# the dentry cache revalidates. That made `down.sh && up.sh` fail on the first
# try and succeed on a retry. Keep the directory inode stable and overwrite the
# contents in place instead.
mkdir -p "$STAGE_HOST"
find "$STAGE_HOST" -mindepth 1 -maxdepth 1 -exec rm -rf {} +
cp -a "$ENVDIR/nsd" "$ENVDIR/unbound" "$STAGE_HOST"/
cp -a "$ENVDIR/vm-up.sh" "$ENVDIR/vm-down.sh" "$ENVDIR/spoof.py" "$STAGE_HOST"/
cp -a "$BIN" "$STAGE_HOST/veri-dns"
chmod +x "$STAGE_HOST"/vm-up.sh "$STAGE_HOST"/vm-down.sh

# Belt-and-braces: wait until the guest actually sees the staged files, so any
# residual virtiofs attr/dentry caching can't turn step 3 into a spurious 127.
for _i in $(seq 1 20); do
  if timeout 20 "$SSH" "test -f $STAGE_VM/vm-up.sh && test -x $STAGE_VM/veri-dns" 2>/dev/null; then
    break
  fi
  sleep 0.5
done
timeout 20 "$SSH" "test -f $STAGE_VM/vm-up.sh && test -x $STAGE_VM/veri-dns" \
  || { echo "staged files not visible in the VM at $STAGE_VM (virtiofs sync)"; exit 1; }

log "2. ensuring the VM has unbound / nsd / dig (idempotent)"
timeout 300 "$SSH" 'bash -s' <<'PREP'
set -e
grep -q "^Server" /etc/pacman.d/mirrorlist 2>/dev/null || \
  printf "Server = https://geo.mirror.pkgbuild.com/\$repo/os/\$arch\n" > /etc/pacman.d/mirrorlist
grep -q "nameserver" /etc/resolv.conf 2>/dev/null || \
  printf "nameserver 10.0.2.3\n" > /etc/resolv.conf
# throwaway test VM: skip signature checking (no keyring baked into the image)
grep -q "^SigLevel = Never" /etc/pacman.conf || sed -i "s/^SigLevel.*/SigLevel = Never/" /etc/pacman.conf
grep -q "^SigLevel = Never" /etc/pacman.conf || echo "SigLevel = Never" >> /etc/pacman.conf
if ! command -v unbound >/dev/null || ! command -v nsd >/dev/null || ! command -v dig >/dev/null; then
  pacman -Sy --noconfirm --needed unbound nsd bind >/dev/null
fi
echo "packages present: $(command -v unbound) $(command -v nsd) $(command -v dig)"
PREP

log "3. building the netns topology + starting services inside the VM"
timeout 120 "$SSH" "bash $STAGE_VM/vm-up.sh"

log "4. done. Query the resolvers with review/env/query.sh, e.g.:"
echo "   review/env/query.sh verid   host.example.test A"
echo "   review/env/query.sh unbound host.example.test A"
