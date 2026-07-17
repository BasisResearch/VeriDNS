#!/usr/bin/env bash
# CI validation gate for veri-dns (docs/model-strengthening-plan.md, W5).
#
# Builds the executables and runs the whole differential/runtime harness as one
# pass/fail gate against a reference resolver (unbound) and a hermetic mock
# authoritative server (dnspython):
#
#   1. id-entropy runtime test   — the W2 entropy obligation at the FFI boundary
#   2. difftest.sh               — live-network parity vs unbound (recursive)
#   3. inject_difftest.sh        — adversarial injection corpus (one case per finding)
#   4. tcp_difftest.sh           — upstream TC→TCP fallback (hermetic mock)
#   5. tcp_serve_difftest.sh     — client TCP serving parity (hermetic mock)
#   6. discover.sh               — DISCOVERY hunt (non-fatal; plan-2 §D)
#
# Missing-dependency policy (made explicit):
#   * CI mode  (env CI=1): a missing dependency is a FAILURE — the gate must not
#     silently pass with reduced coverage on the CI runner.
#   * Local mode (CI unset/0): a missing dependency SKIPS the affected sub-test
#     with a clear message, so a developer without unbound/tshark still gets the
#     sub-tests they can run.
#
# Usage: test/ci_gate.sh [--no-build]
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/veri-dns"
VENV="$ROOT/test/.venv"
PY="$VENV/bin/python"

CI_MODE="${CI:-0}"
NO_BUILD=0
[ "${1:-}" = "--no-build" ] && NO_BUILD=1

RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; RST=$'\033[0m'
fails=0; skips=0; passes=0
FAILED=(); SKIPPED=()

section() { printf '\n\033[1m==> %s\033[0m\n' "$1"; }
ok()   { printf '  %sPASS%s  %s\n' "$GRN" "$RST" "$1"; passes=$((passes+1)); }
skip() { printf '  %sSKIP%s  %s\n' "$YEL" "$RST" "$1"; skips=$((skips+1)); SKIPPED+=("$1"); }
die()  { printf '  %sFAIL%s  %s\n' "$RED" "$RST" "$1"; fails=$((fails+1)); FAILED+=("$1"); }

# Missing dependency: FAIL in CI, SKIP locally. Returns 0 if the caller should
# proceed (dep present), 1 if it should stop this sub-test.
need() {
  local what="$1" why="$2"
  if [ "$CI_MODE" = "1" ]; then
    die "$what missing ($why) — required in CI mode"
  else
    skip "$what missing ($why) — skipped (local mode)"
  fi
  return 1
}

have() { command -v "$1" >/dev/null 2>&1; }

# Serialise hermetic rigs: clear any stray servers on the shared ports first.
clear_ports() {
  pkill -f 'bin/veri-dns' 2>/dev/null
  pkill -f 'mock_auth.py' 2>/dev/null
  pkill -f 'discover_mock.py' 2>/dev/null
  pkill -f 'unbound -d -p' 2>/dev/null
  sleep 1
}

# ---------------------------------------------------------------------------
section "environment"
echo "  CI mode: $([ "$CI_MODE" = 1 ] && echo yes || echo no)   ROOT: $ROOT"
for c in dig unbound uv tshark; do
  printf '  %-8s %s\n' "$c" "$(command -v "$c" 2>/dev/null || echo '(absent)')"
done

# ---------------------------------------------------------------------------
section "build executables"
if [ "$NO_BUILD" = 1 ]; then
  echo "  --no-build: skipping lake build"
else
  if ! have lake; then
    if [ "$CI_MODE" = 1 ]; then die "lake missing — cannot build in CI"; else skip "lake missing — cannot build"; fi
  elif (cd "$ROOT" && lake build veri-dns exchange-junk-test id-entropy-test) >/tmp/ci_gate_build.log 2>&1; then
    ok "lake build veri-dns exchange-junk-test id-entropy-test"
  else
    die "lake build failed (see /tmp/ci_gate_build.log)"; tail -20 /tmp/ci_gate_build.log
  fi
fi

# Ensure the dnspython venv the hermetic mock needs exists (git-ignored, absent in
# fresh checkouts and worktrees). Create it with uv when possible.
ensure_venv() {
  if [ -x "$PY" ] && "$PY" -c 'import dns' >/dev/null 2>&1; then return 0; fi
  if have uv; then
    echo "  creating $VENV (uv venv + dnspython)"
    (cd "$ROOT/test" && uv venv .venv >/dev/null 2>&1 && uv pip install --python .venv/bin/python dnspython >/dev/null 2>&1)
  fi
  [ -x "$PY" ] && "$PY" -c 'import dns' >/dev/null 2>&1
}

# ---------------------------------------------------------------------------
section "1. id-entropy runtime test (W2 entropy obligation)"
# The sampler draws 4096 UInt16 transaction ids and asserts: ≥3850 distinct values
# (expected ~3968 by the birthday bound), every bit set within 2048±192, and modal
# adjacent delta ≤64. Those thresholds are the statistically-sane gate; the gate
# just requires the exe to exit 0. Run twice to defeat a rare statistical false-neg.
ENTROPY_BIN="$ROOT/.lake/build/bin/id-entropy-test"
if [ ! -x "$ENTROPY_BIN" ]; then
  die "id-entropy-test exe not built"
else
  attempt=0; entropy_ok=0
  while [ $attempt -lt 2 ]; do
    if out="$("$ENTROPY_BIN" 2>&1)"; then entropy_ok=1; break; fi
    attempt=$((attempt+1))
  done
  if [ "$entropy_ok" = 1 ]; then
    ok "$(printf '%s\n' "$out" | grep -m1 '^id-entropy:' | sed 's/^id-entropy: //')"
  else die "id-entropy-test failed twice: $out"; fi
fi

# ---------------------------------------------------------------------------
section "2. difftest.sh — live-network parity vs unbound"
if [ ! -x "$BIN" ]; then die "veri-dns exe not built (difftest)"
elif ! have dig; then need "dig" "difftest needs a DNS client"
elif ! have unbound; then need "unbound" "difftest diffs against a reference resolver"
else
  clear_ports
  if timeout 240 bash "$ROOT/test/difftest.sh" >/tmp/ci_difftest.log 2>&1; then
    ok "difftest.sh ($(grep -oE '[0-9]+/[0-9]+ matched unbound' /tmp/ci_difftest.log | tail -1))"
  else
    die "difftest.sh failed"; tail -25 /tmp/ci_difftest.log
  fi
fi

# ---------------------------------------------------------------------------
section "3. inject_difftest.sh — adversarial injection corpus"
if [ ! -x "$BIN" ]; then die "veri-dns exe not built (inject)"
elif ! have dig; then need "dig" "inject rig needs a DNS client"
elif ! have unbound; then need "unbound" "inject rig diffs against unbound"
elif ! ensure_venv; then need "dnspython venv" "inject rig needs the mock authoritative server"
elif [ ! -f "$ROOT/test/inject_difftest.sh" ]; then skip "inject_difftest.sh absent in this checkout"
else
  clear_ports
  if timeout 200 bash "$ROOT/test/inject_difftest.sh" >/tmp/ci_inject.log 2>&1; then
    ok "inject_difftest.sh (subdomain rider / Kaminsky / off-owner CNAME / foreign SOA / ANY / CH)"
  else
    die "inject_difftest.sh failed"; tail -30 /tmp/ci_inject.log
  fi
fi

# ---------------------------------------------------------------------------
section "3b. junk_difftest.sh — finding 017 same-source junk (read-until-match)"
if [ ! -x "$BIN" ]; then die "veri-dns exe not built (junk)"
elif ! have dig; then need "dig" "junk rig needs a DNS client"
elif ! ensure_venv; then need "dnspython venv" "junk rig needs the mock authoritative server"
else
  clear_ports
  if timeout 200 bash "$ROOT/test/junk_difftest.sh" >/tmp/ci_junk.log 2>&1; then
    ok "junk_difftest.sh (real reply survives same-source junk)"
  else
    die "junk_difftest.sh failed"; tail -30 /tmp/ci_junk.log
  fi
fi

# ---------------------------------------------------------------------------
section "4. tcp_difftest.sh — upstream TC→TCP fallback (hermetic)"
if [ ! -x "$BIN" ]; then die "veri-dns exe not built (tcp_difftest)"
elif ! have dig; then need "dig" "tcp_difftest needs a DNS client"
elif ! have unbound; then need "unbound" "tcp_difftest diffs against unbound"
elif ! ensure_venv; then need "dnspython venv" "tcp_difftest needs the mock authoritative server"
else
  have tshark || echo "  (note) tshark absent — the packet-sniff sub-test self-skips"
  clear_ports
  if timeout 240 bash "$ROOT/test/tcp_difftest.sh" >/tmp/ci_tcp.log 2>&1; then
    ok "tcp_difftest.sh (U6: forced-TC parity, oversized fallback, degrade-to-SERVFAIL)"
  else
    die "tcp_difftest.sh failed"; tail -30 /tmp/ci_tcp.log
  fi
fi

# ---------------------------------------------------------------------------
section "5. tcp_serve_difftest.sh — client TCP serving parity (hermetic)"
if [ ! -x "$BIN" ]; then die "veri-dns exe not built (tcp_serve)"
elif ! have dig; then need "dig" "tcp_serve needs a DNS client"
elif ! have unbound; then need "unbound" "tcp_serve diffs against unbound"
elif ! ensure_venv; then need "dnspython venv" "tcp_serve needs the mock authoritative server"
else
  clear_ports
  if timeout 200 bash "$ROOT/test/tcp_serve_difftest.sh" >/tmp/ci_tcpserve.log 2>&1; then
    ok "tcp_serve_difftest.sh (Stage S: small/forcetc/oversized-full/NXDOMAIN over TCP)"
  else
    die "tcp_serve_difftest.sh failed"; tail -30 /tmp/ci_tcpserve.log
  fi
fi

clear_ports

# ---------------------------------------------------------------------------
section "6. discover.sh — discovery hunt (NON-FATAL, docs/model-strengthening-plan-2.md §D)"
# This stage is a HUNT, not a gate: it mutates honest authoritative responses and
# asserts the resolver against RFC-derived properties, reporting divergences as
# candidate findings. A divergence must NOT fail the CI gate (that would make it a
# regression rig again). We still surface the count so a hunt HIT is visible in CI.
# Missing-dependency policy still applies (FAIL in CI, SKIP locally). Only an
# INFRASTRUCTURE error in the hunt (harness crash) is a gate failure.
if [ ! -x "$BIN" ]; then die "veri-dns exe not built (discover)"
elif ! have dig; then need "dig" "discover hunt needs a DNS client"
elif ! ensure_venv; then need "dnspython venv" "discover hunt needs the mock authoritative server"
else
  clear_ports
  DISC_JSON="/tmp/ci_discover.json"
  if timeout 500 bash "$ROOT/test/discover.sh" --json "$DISC_JSON" >/tmp/ci_discover.log 2>&1; then
    hits="$(grep -oE '[0-9]+ hard-property violation' /tmp/ci_discover.log | grep -oE '^[0-9]+' | head -1)"
    diffs="$(grep -oE '[0-9]+ differential mismatch' /tmp/ci_discover.log | grep -oE '^[0-9]+' | head -1)"
    if [ "${hits:-0}" -gt 0 ] || [ "${diffs:-0}" -gt 0 ]; then
      # A HIT is a CANDIDATE FINDING, not a gate failure: report as PASS-with-note.
      ok "discover.sh ran; ${hits:-0} property violation(s), ${diffs:-0} differential mismatch(es) — candidate findings (non-fatal), see /tmp/ci_discover.log + $DISC_JSON"
    else
      ok "discover.sh ran; no new divergences on this build"
    fi
  else
    # The hunt harness itself broke (infra error) — worth flagging.
    die "discover.sh harness error (infra, not a resolver finding — see /tmp/ci_discover.log)"; tail -20 /tmp/ci_discover.log
  fi
fi

clear_ports

# ---------------------------------------------------------------------------
section "gate summary"
printf '  passed=%d  failed=%d  skipped=%d\n' "$passes" "$fails" "$skips"
if [ "$skips" -gt 0 ]; then printf '  skipped:\n'; for s in "${SKIPPED[@]}"; do printf '    - %s\n' "$s"; done; fi
if [ "$fails" -gt 0 ]; then
  printf '  %sfailed:%s\n' "$RED" "$RST"; for f in "${FAILED[@]}"; do printf '    - %s\n' "$f"; done
  printf '\n%sGATE FAILED%s\n' "$RED" "$RST"; exit 1
fi
printf '\n%sGATE PASSED%s\n' "$GRN" "$RST"; exit 0
