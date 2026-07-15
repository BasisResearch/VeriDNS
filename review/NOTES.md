# VeriDNS review — running log

## Phase 0 (foundation) — status
- [x] **0a. Binary runnable.** Fixed `arc4random` link failure (finding 000); `veri-dns` now builds and starts on UDP 5300. Stable baseline copied to `review/veri-dns`.
- [x] **0b. Axiom audit — CLEAN.** `#print axioms` on `ioResumeLoop_sound` (both), `resolveWithIO_sound`, `scrubAnswerB_excludes_foreign`/`_authentic`/`_delivered_model_authentic` → only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no bespoke `axiom` anywhere (grep-clean). Proofs are genuine at the meta level.
- [x] **0c. Execution-path map** → `review/pathmap.md`. Verification is largely load-bearing (monad-polymorphic core). Off-path/decorative items and the trust boundary catalogued.
- [x] **0d. Environment** DONE → `review/ENV.md`. One VM (~2 GiB), netns: veri-dns @10.53.0.2:5300, unbound @10.53.0.3:5301, nsd root/tld/leaf, attacker @10.53.0.99. Both resolvers verified answering from the fake hierarchy. Rig runs inside the VM; reach via `penn-testing/vm/ssh.sh`; reload mutant via `review/env/restart-verid.sh`.
  - Env agent surfaced two diffs vs unbound (seeded into bug-hunt): (a) **veri-dns accepts a grandchild answered authoritatively from the root IP; unbound rejects out-of-bailiwick** — possible bailiwick leniency; (b) no RFC 6761 `.test` special-casing.

## Phase 1 status
- ffi fix committed on branch `review/bug-hunt` (so mutant `git checkout` reverts to the WORKING baseline, not arc4random).
- **Mutation is now INTEGRATED into the loop** (was a disconnected one-shot). `bug-hunt.mjs` v2 carries a knowledge base across rounds; each round: finders → mutation SYNTHESIS (informed by finder diffs + KB + WHY prior mutants were caught, routing around brittle proof scripts) → serial weaponize+verify (distinguishes semantic catch vs proof-script brittleness; attempts minimal script repair to reveal real spec holes) → runtime verify → KB update. Loops until dry (≤4 rounds). Curated list folded in as SEED_MUTANTS. `mutation.mjs` superseded.
- Earlier one-shot mutation run (stopped) yielded: case-sensitive→proof-caught (real, A=a example); overcollapse→proof-caught-BRITTLE (script+traces, not semantic — 001 refined); constant-qid→coverage-gap (002).
- `bug-hunt.mjs` v2 LAUNCHED (task wdaxt5rjy).
- `REPORT.md` skeleton drafted (verdict/findings finalize after the loop).

## Leads to chase (seeded into the workflow)
1. **FLAGSHIP — over-collapse case fold (bad-spec candidate).** `foldByte`/`foldCaseByte` are TRUSTED concrete definitions; `rfc_proves` only embeds RFC text, and all downstream case theorems are *invariance-under-the-fold*. An over-collapsing fold (all letters → one) keeps the generated `namespace_compare_*` props satisfiable and every invariance proof green, yet collides distinct names → wrong records served. Weaponized as the `overcollapse-fold` mutant. If proofs stay green + collision observable → the case-insensitivity spec is not load-bearing.
2. **Honesty-oracle / network arm.** `Refinement.resolveWithIO_simulates` (:9700): at `M=IO` the network disjunct takes `HasVerdict`/`NetworkConsistent` as a PREMISE, discharged constructively only at `M=Prog`. Characterize what the oracle assumes and whether it assumes away anti-poisoning.
3. **`ioResumeLoop_sound` hypothesis stack (~25).** Check `q.rd=false` (clients require rd=1 at `Server.lean:98-99` — sub-query only, or vacuity?), `qtype≠star`, class IN, clock/seen bounds for vacuity/coverage.
4. **No end-to-end `serveOne`/`serverLoop` theorem.** Composition decode→hygiene→resolveWithIO→scrub→truncate→send is verified piecewise only.
5. **`recvfrom.c:100`** `veri_dns_recvfrom` returns empty ByteArray on timeout instead of an error — check for a mishandled-timeout path.
6. **`retryOption_pure`** assumes a deterministic network action; real networks are not — informal argument, not a proof about IO.

## Workflow scripts (written, awaiting env for dynamic stages)
- `review/workflows/mutation.mjs` — curated on-path mutation batch (serial, main build tree).
- `review/workflows/bug-hunt.mjs` — round-based finders (reading-source / spec-auditor / dynamic) → serial weaponize+verify → findings. Feedback loop across rounds.

## Findings
- `000` — arc4random FFI link failure (medium, coverage-gap).
