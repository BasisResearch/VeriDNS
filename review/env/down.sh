#!/usr/bin/env bash
# down.sh -- HOST-side teardown of the rig inside the VM (leaves the VM booted).
set -euo pipefail
PENN=/home/yiyun/Experiments/VeriDNS/penn-testing
timeout 60 "$PENN/vm/ssh.sh" "bash /root/dev/_vmdns/vm-down.sh"
