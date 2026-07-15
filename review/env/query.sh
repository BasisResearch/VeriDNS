#!/usr/bin/env bash
# query.sh -- HOST-side convenience wrapper to dig a resolver in the VM.
#   query.sh verid   <name> [type]   # veri-dns  (10.53.0.2:5300)
#   query.sh unbound <name> [type]   # unbound   (10.53.0.3:5301)
# Runs dig from the attacker namespace (the client vantage) inside the VM.
set -euo pipefail
PENN=/home/yiyun/Experiments/VeriDNS/penn-testing
target="${1:?usage: query.sh <verid|unbound> <name> [type]}"
name="${2:?usage: query.sh <verid|unbound> <name> [type]}"
type="${3:-A}"
case "$target" in
  verid)   ip=10.53.0.2;  port=5300 ;;
  unbound) ip=10.53.0.3;  port=5301 ;;
  *) echo "unknown target '$target' (use verid|unbound)"; exit 1 ;;
esac
exec "$PENN/vm/ssh.sh" \
  "ip netns exec attacker dig @$ip -p $port $name $type +noall +question +answer +authority +comments"
