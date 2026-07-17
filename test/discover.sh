#!/usr/bin/env bash
# discover.sh — wrapper for the DISCOVERY hunt (docs/model-strengthening-plan-2.md §D).
#
# This is NOT a regression gate. It is an adversarial GENERATOR: it mutates an
# honest authoritative response for a name that EXISTS and asserts the resolver's
# output against RFC-derived properties (primary, no reference resolver needed)
# and, when unbound is present, differentially against it (secondary). Every
# property violation / differential mismatch is a CANDIDATE FINDING — the hunt is
# non-fatal, it reports divergences without failing the CI gate.
#
# Missing-dependency policy mirrors ci_gate.sh:
#   * CI mode (CI=1): a missing dependency is a FAILURE.
#   * Local mode:     a missing dependency SKIPS with a message.
#
# Usage: test/discover.sh [--diff] [--only SUBSTR] [--json PATH]
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
VENV="$ROOT/test/.venv"
PY="$VENV/bin/python"
CI_MODE="${CI:-0}"

YEL=$'\033[33m'; RST=$'\033[0m'

skip_or_fail() {
  local what="$1"
  if [ "$CI_MODE" = "1" ]; then
    echo "  FAIL  $what missing — required in CI mode"; exit 1
  else
    echo "  ${YEL}SKIP${RST}  $what missing — discovery hunt skipped (local mode)"; exit 0
  fi
}

have() { command -v "$1" >/dev/null 2>&1; }

[ -x "$BIN" ] || skip_or_fail "veri-dns exe"
have dig || skip_or_fail "dig"

# Ensure the dnspython venv exists (git-ignored, absent in fresh worktrees).
ensure_venv() {
  if [ -x "$PY" ] && "$PY" -c 'import dns' >/dev/null 2>&1; then return 0; fi
  if have uv; then
    (cd "$ROOT/test" && uv venv .venv >/dev/null 2>&1 \
       && uv pip install --python .venv/bin/python dnspython >/dev/null 2>&1)
  fi
  [ -x "$PY" ] && "$PY" -c 'import dns' >/dev/null 2>&1
}
ensure_venv || skip_or_fail "dnspython venv"

# Clear stray servers on the shared ports first.
pkill -f 'bin/veri-dns' 2>/dev/null
pkill -f 'discover_mock.py' 2>/dev/null
pkill -f 'unbound -d -p' 2>/dev/null
sleep 1

# The differential (--diff, vs unbound) is SECONDARY and OPT-IN. The mock is a
# stateful single-socket delegation tuned to veri-dns's query pattern; unbound
# descends differently, so the differential is best-effort and slow. The primary
# mechanism is the property-based hunt, which needs no reference resolver and is
# what runs in CI. Pass --diff explicitly to also run the (gated) differential.
exec "$PY" -u "$ROOT/test/discover.py" "$@"
