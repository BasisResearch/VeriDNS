# Liveness / adequacy (and driver concurrency) — plan

Written 2026-07-12 against HEAD `516094c` (whole TCP plan complete). The verified core today
proves **soundness**: *if* the resolver delivers an answer, that answer refines the RFC model
(`ioResumeLoop_sound`, `serveDatagram_verdict_sound`, `serveTcpDatagram_total`). It does NOT
prove **liveness / adequacy**: that against a cooperative network the resolver *does* deliver,
delivers the model's answer, and never spuriously SERVFAILs or diverges. Today that direction is
only *demonstrated* — by the `#eval` traces in `Test/Loop.lean` and the differential rigs
(`test/difftest.sh`, `tcp_*_difftest.sh`) — never proven ∀-universally.

**Adequacy is the converse of the total-simulation refinement.** Total-simulation (gap class 1)
proved the impl *simulates the model* for all runs (the soundness/refinement direction). Adequacy
proves the model verdict is *achieved by the impl* on cooperative networks. The two together give
an **iff** on the cooperative path: delivered answer ⟺ model `HasVerdictAt` verdict. They share
the per-round classifiers, so L4 is soundness-minus-the-adversary, not new machinery.

**Overall size: XL — a total-simulation-scale arc.** L4 (multi-round descent) dominates; L0–L3
are assembly of lemmas that already exist. L6 (concurrency) is engineering + a documented
invariant, NOT a theorem (Lean can't prove liveness of a `partial` IO server loop).

## Why now

- The single biggest "demonstrated, not proven" gap is *that it resolves at all*. Soundness is
  vacuously satisfiable by a resolver that SERVFAILs everything; only adequacy rules that out.
- The concurrency introduced in Stage S (a real second OS thread + shared-cache mutex) has an
  availability bug — the cache lock spans upstream network I/O, so one slow resolution
  head-of-line-blocks every client on both transports. That is a liveness regression that
  wants fixing before it is load-bearing, and it belongs in this plan (L6).

## Design decisions (PROPOSED — recommendations marked)

1. **Adequacy target — RECOMMEND: the dual of `HasVerdictAt`, same scope premises.** L4's
   conclusion is literally "the `HasVerdictAt` verdict `v` is realized as `Prog.run … = some ((.ok
   resp, cout), w')` with `αResp resp` = `v`." It inherits soundness's scope (`q.qclass = .in`,
   `q.qtype ≠ .star`, `qname ≤ 127` labels, clock bound). Do NOT invent a fresh answer relation —
   pairing with `ioResumeLoop_sound` on the same `v` is what yields the iff.
2. **Cooperative-network model — RECOMMEND: an honest oracle over a modelled zone tree
   (`Node ResourceRecord`), NOT a new type.** Reuse the existing `World`/`WorldModelsTcp` honest
   arm and the `Node ResourceRecord` zone model already used by `Test/Loop.lean` and
   `Proof/NameTree.lean`. The distinguishing premise vs soundness is *totality + honesty*: the
   oracle is DEFINED and returns the RFC-correct honest response (referral toward the child cut, or
   the final answer/NXDOMAIN) for every query reachable along the delegation of `T`. This makes the
   theorem "adequacy against a modelled zone `T`" — exactly what the `#eval` mocks exercise, now
   universal. Avoids the vacuity trap (an over-strong "network answers everything instantly"
   premise proves nothing interesting).
3. **Progress metric — RECOMMEND: remaining delegation depth (labels to the target cut).** The
   descent measure is the number of labels between the current SLIST cut and the queried name,
   bounded by `qname.length ≤ 127`. Each cooperative round strictly decreases it (referral pushes
   the cut one zone deeper) or terminates (answer/NXDOMAIN). This is the L1 metric and it feeds
   both "no fuel starvation" (L1) and the L4 induction.
4. **Termination scope — RECOMMEND: per-query, not the server loop.** `serverLoop`/`udpServeLoop`/
   `tcpServeLoop` are `partial` and intentionally non-terminating (they are servers). The liveness
   claim is per-*query* termination + progress; the driver loops are explicitly out of the
   termination scope (as `Proof/ServeSequence.lean` already notes for the fold corollary).
5. **Concurrency (L6) — RECOMMEND: fix the critical section, document the invariant, do NOT
   attempt a Lean liveness proof of the IO loop.** Narrow the lock to snapshot-in / merge-out
   (decision detail in L6); state the non-starvation invariant as a documented mutex-discipline
   property backed by a stress test, since `partial` IO-loop liveness is not kernel-provable.

## What exists today (leverage)

- **L0/L1 seeds — intra-round progress is largely DONE.** `Proof/Resolver.lean`: `fuelRank`
  (`:801`), `fuelRank_le_seven` (`:813`), `step_goto_fuelRank` (`:889`), `loop_ne_maxIterations`
  (`:969`), `resume_ne_maxIterations` (`:1004`), `resolve_ne_maxIterations` (`:993`). These prove
  the step machine cannot spin on `maxIterations` within fuel ≥ 7 — the hard part of "no fuel
  starvation." What's missing is composing them into a per-*network-round* descent bound.
- **L2 seed — cache-hit completeness exists.** `Proof/NameTreeComplete.lean`: the `LookupComplete`
  family (`lookupComplete_cacheRRs`, `_cacheUnlessTruncated`, `_boundLru`, `_sweep`, …) proves a
  sane cache returns the modelled answer. Package into a 0-round liveness corollary.
- **L3 — single-round adequacy, DONE.** `Proof/FreeIO.lean`: `run_ioResumeLoop_answer` /
  `run_resolveWithIO_networkAnswer` (positive), `run_ioResumeLoop_nxdomain` (NXDOMAIN), and
  `run_ioResumeLoop_referral_lift` (the referral descent step — a monotone forward reduction). All
  three axiom-clean. L4 chains the referral lift on the delegation-depth metric, closing branches
  with the answer/NXDOMAIN terminals; the pinned per-round hypotheses are what L4 discharges from the
  cooperative-network model.
- **Per-round classifiers** from `ioResumeLoop_sound` (`Proof/IoResumeSound.lean`) — reuse with the
  oracle arm INSTANTIATED honest instead of quantified over honest∨spoof∨lost. Strictly fewer
  cases than soundness.
- The `#eval` mocks (`Test/Loop.lean`: `treeAnswered`, `delegationChased`, `treeChased`,
  `probeSequenceMinimised`, …) are the informal oracle for what L4/L5 must prove universally — port
  each into a regression pin once the theorem lands.

## Stage L0 — per-query termination — **S** (DONE)
`ioResumeLoop_terminates` / `resolveWithIO_terminates` (`Proof/Adequacy.lean`, both axiom-clean):
for ANY world (no cooperative-network premise — the pure "the free-monad program is finite" fact),
`∃ K, Prog.run K (ioResumeLoop … depth fuel …) w = some _`. The resolver never diverges — every path
reaches a terminal (answer / NXDOMAIN / give-up SERVFAIL / deadline error) in finitely many `Prog`
steps. This rules out the vacuity where a spinning resolver satisfies soundness.

Proof: nested strong induction (`Nat.strongRecOn`) on the loop's own `(depth, fuel)` termination
measure — glueless recursion strictly decreases `depth`, every other recursion decreases `fuel` —
walking each branch of the ~170-line body with a set of "existence-preserving" step combinators
(`Terminates p w := ∃ K r, Prog.run K p w = some r`; `terminates_{pure,bind,now_bind,log_bind,
randomId_bind,forwardQuery_bind,tcpForward_bind,gluelessUpdatedSlist_bind}`) to a pure terminal or a
strictly-smaller recursive call (the IH). The combinators dispatch the network steps to the existing
`run_forwardQuery_bind_eq{,_none,_acceptNone,_decodeError}` / `run_tcpForward_bind_eq{,…}` reduction
lemmas; the `∀ w` shape of the IH discharges every threaded intermediate world without tracking it.
`resolveWithIO_terminates` lifts it through the entry-point `resolve` (pure done/err, or pause into
the loop). The `partial` server loops (`serverLoop`/`udpServeLoop`/`tcpServeLoop`) are intentionally
non-terminating and out of scope (decision 4) — this is per-*query* termination.

## Stage L1 — no fuel starvation (progress bound) — **S–M** (DONE 2026-07-14)
`resolve_within_bound`: define the delegation-depth metric (decision 3) and prove each accepted
cooperative round strictly decreases it, so a terminal is reached in ≤ `k · qname.length` rounds
(`k` = the ≤ 7 `fuelRank` span). Corollary: on the cooperative path a SERVFAIL is NEVER due to fuel
exhaustion — every give-up is a genuine model `gaveUp`, not an artifact. Reuses the `fuelRank`
lemmas; the new content is the cross-round measure.

**Status: DONE (`Proof/SpineAdequacy.lean` + `Proof/FreeIO.lean`, all axiom-clean).** The spine
chain's fuel premise `spine.length·128 + (labels − revealed) < fuel` was already the cross-round
descent bound (the radix-encoded lexicographic (cut, reveal) measure — each probe round consumes a
reveal unit, each referral retires a 128-radix cut digit); L1 packages it:
- `spineFuelBound spine := spine.length * 128 + 128` — the explicit spine-computable bound
  (`labels − revealed ≤ labels ≤ 127 < 128` under the in-scope label bound; conservative — actual
  round count ≤ `labels + spine.length + 1` — but it is the bound the induction threads).
- `resolveWithIO_within_bound` (the plan's `resolve_within_bound`) — the general-depth capstone
  with the reveal-floor fuel premise replaced by `spineFuelBound spine ≤ fuel`; the caller supplies
  no reveal-floor arithmetic (`h127` discharges it via `omega`).
- `resolveWithIO_spine_no_starvation` — the give-up-is-genuine corollary, STRONGER than planned:
  on the cooperative spine path EVERY completed run (any step budget) IS the pinned positive
  answer, so no completed cooperative run is the fuel-exhaustion terminal
  (`.error "resolveWithIO: max IO rounds"`) or any other give-up — a SERVFAIL can only witness
  non-cooperative network behavior, never fuel starvation. Enabled by NEW `FreeIO.run_agree`
  (`Prog.run` determinism across step budgets, via `run_mono` + injectivity), which turns the one
  adequacy witness into a statement about every completed run.

## Stage L2 — cache-hit liveness — **S** (assembly) (DONE — `resolveWithIO_cacheHit_adequate` + `_treeFaithful`, `Proof/Adequacy.lean`)
`resolveWithIO_hits_return`: a query whose modelled answer is in a sane cache
(`LookupComplete` + `TreeSane` + `CacheAgrees`, the same hypotheses `lookupComplete_boundLru`
already takes) returns `.ok` with that answer in ZERO network rounds. Direct corollary of the
existing `LookupComplete` family — this stage is packaging + a stated theorem.

## Stage L3 — single-round adequacy, full terminal set — **M** (DONE)
Generalize `run_ioResumeLoop_answer` and add its siblings:
`run_ioResumeLoop_referral` (honest referral → loop re-enters `sendQueries` one cut deeper,
metric decreased) and `run_ioResumeLoop_nxdomain` (honest untruncated NXDOMAIN → strict-denial
terminal). Loosen the fully-pinned hypotheses to "the oracle returns the honest response for THIS
query per the cooperative model" (decision 2). These are the per-round steps L4 composes.

**Status: DONE (`Proof/FreeIO.lean`, axiom-clean).** All three terminals proven —
`run_ioResumeLoop_answer` + `run_resolveWithIO_networkAnswer` (positive), `run_ioResumeLoop_nxdomain`
(NXDOMAIN), and `run_ioResumeLoop_referral_lift` (the referral descent step). The referral sibling is
stated as a **monotone forward reduction**, not a terminal: given `afterResume … = .continue st`
(supplied by `Refinement.afterResume_referral_continues`) it lifts any terminating continue-state run
`Prog.run K (loop st fuel' revealed') w'` to the full round `Prog.run (K+6) (loop state (fuel'+1)
revealed) w`, consuming 6 `Prog` steps and threading the world (`idCtr += 2`; oracle/ids/clock
unchanged). This is exactly the shape L4's delegation-depth induction chains — the IH delivers the
continue-state run, this lemma lifts it one round up. The pinned per-round hypotheses (`horacle`,
`haccept`, `hdecode`, `hsani`, `haccResp`, `htc`, `hunfollow`, `hprobe`) are what L4 discharges from
the cooperative-network model.

## Stage L4 — multi-round descent (the adequacy capstone) — **L** (dominates)
`ioResumeLoop_adequate`: for a `CooperativeNetwork T` (decision 2 — honest, total along `T`'s
delegation) and an in-scope query `q` with model verdict `v` (`HasVerdictAt … q v`),
`Prog.run n (ioResumeLoop sbelt state deadline …) w = some ((.ok resp, cout), w')` with
`αResp resp = v` and `CacheRefines (αCache cout) coutM`. Induction on the L1 delegation-depth
metric; each step is an L3 single-round terminal with the oracle arm pinned honest. Structurally
mirrors `ioResumeLoop_sound` (~4800 lines) MINUS the spoof/lost disjuncts — the T1a experience says
adversary-free arms are the cheap ones, but the descent induction and the honest-oracle totality
threading are new. **Pairs with `ioResumeLoop_sound` on the same `v` to give the iff.**

**Descent toolkit — DONE (`Proof/Adequacy.lean`, axiom-clean).** The composable core of the L4
induction, independent of the (yet-to-be-built) cooperative-oracle model:
- `Delivers sbelt state deadline depth fuel revealed w out` := `∃ K w', Prog.run K (ioResumeLoop …)
  w = some (out, w')` — the adequacy analogue of soundness's `Prog.run … = some …`. The L3 terminals
  (`run_ioResumeLoop_answer` / `_nxdomain`) are `Delivers` witnesses *definitionally* (their `∃ K w'`
  conclusion IS what `Delivers` unfolds to — no bridging lemma needed).
- `Delivers_referral_step`: a referral round lifts `Delivers` at the deeper continue-state
  `st @ fuel'` back up to `state @ fuel'+1`, given the L3 referral-round hypotheses and `hnext` — a
  proof that the resolver delivers the SAME `out` from `st` in every world matching the post-round
  world (same oracle/tcpOracle/ids/clock, `idCtr += 2`). Proof: obtain the post-round world + `+6`-step
  transfer from `run_ioResumeLoop_referral_lift`, instantiate `hnext`, transfer up. **`hnext`'s
  world-condition is exactly what a cooperative (world-independent honest) oracle satisfies** — it is
  the induction hypothesis at the deeper cut.
- `resolveWithIO_delivers`: lifts a loop `Delivers` to the `resolveWithIO` entry point (any `fuel`,
  any `out`) — the end-to-end completeness sibling of `run_resolveWithIO_networkAnswer`.

**Descent induction backbone — DONE (`Proof/Adequacy.lean`, axiom-clean).** The transitive closure
of `Delivers_referral_step` — the descent *induction* itself, the piece flagged above as "the descent
induction is new content":
- `DescentChain sbelt deadline depth out state fuel revealed w` — an inductive predicate: `state @
  fuel` reaches `out` through a finite sequence of honest referral rounds (each a `referral` node
  carrying the exact per-round hypotheses `Delivers_referral_step` consumes, plus a world-generic
  `hnext` continuing from the deeper continue-state) ending in a `terminal` leaf (any established
  `Delivers` witness — the L3 answer/NXDOMAIN terminals ARE such witnesses definitionally).
- `DescentChain.delivers` — collapses a chain to `Delivers` by structural induction, composing
  `Delivers_referral_step` at each node and reading off the terminal at the leaf.
- `resolveWithIO_adequate_of_chain` — the end-to-end bridge: an entry `resolve` pause + a `DescentChain`
  from that state ⟹ `resolveWithIO` delivers `out`.

**Descent CONSTRUCTION + concrete per-cut bricks — DONE (`Proof/{Adequacy,CooperativeNetwork}.lean`,
axiom-clean).** The converse of `DescentChain.delivers` (build an unbounded-depth chain) and the
concrete zone bricks that feed it:
- `DescentChain.of_descent` (Adequacy) — build a `DescentChain` by well-founded induction on a
  delegation-depth metric `μ`, given a descent invariant `Inv` and a per-cut *step oracle* (each
  `Inv`-state either delivers `out` or admits a strictly-`μ`-closer referral round whose node builder
  consumes the deeper-cut chain). `resolveWithIO_adequate_of_descent` composes it with
  `resolveWithIO_adequate_of_chain` into the end-to-end capstone *contract* a concrete zone plugs into.
- Concrete referral round: `mkHonestOracleAddr` / `CooperativeNetworkAddr` (address-keyed honest
  oracle — a hierarchical zone's servers answer per their own cut), `oracle_supplies_roundAddr`,
  `delegatingReferralRound_node` (a `DescentChain.referral` node from a `CooperativeNetworkAddr`).
- Metric: `delegation_metric_decrease` (μ strictly decreases at a followable referral),
  `delegationMatchCount_le` (μ bounded by label count), `bestWithAddress_isSome_of_glueMatch` (a glued
  child SLIST resolves an address).
- Next-round discharge from the continue-state (primary/branch-1 case of
  `afterResume_referral_continue_cases`): `referral_continue_bestWithAddress` (the child SLIST's
  `bestWithAddress` — the deeper round's `hbest`) and `referral_continue_matchCount` (its `matchCount`
  = the referral cut — the `hst` of `delegation_metric_decrease`).

**Remaining for L4 (now precisely):**
1. **Branch determinacy — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean).** The clean
   cooperative case does NOT take `afterResume`'s disjunct-1 (transient-keep): `currentCloser_false_referral`
   shows an untruncated referral whose just-absorbed NS is re-found by `walkNs` at ≥ the same cut depth
   drives `stepFindServers` into the cache RE-DERIVE branch (disjunct 2). Rather than force a single
   branch, `referral_continue_matchCount_ge` proves the *shared* consequence of ALL followable branches:
   for a cooperative referral (NS authority, delegation strictly below root `0 < delegationMatchCount`),
   the continue-state reports `matchCount ≥ delegationMatchCount` — disjunct 1 (`=`), disjunct 2
   (`currentCloser`-false guard forces `mc ≥ dmc`), and disjunct 3 (sbelt) is IMPOSSIBLE (its guard
   contradicts `0 < dmc`). `delegation_metric_decrease` is generalized (`hst` from `=` to `≥`, still
   `omega`), so the metric strictly decreases whichever branch the impl's TTL-dependent gate selects.
2. **Continue-state send-round facts — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean).**
   `referralReply_continue_sendFacts`: the deeper cut's `st.currentStep = .sendQueries` +
   `CanonicalName st.resources.sname` + `∃ sq, buildSubQuery st revealed = some sq` are all PASSTHROUGHS
   of the parent round — a `referralReply` continue-state preserves `sname` (canonicity carries) and
   `lastQuery` (`afterResume_referral_continue_cases`), and `buildSubQuery` succeeds for any state whose
   `lastQuery` carries a question. No new network reasoning: the round preserves exactly the state fields
   `buildSubQuery` and the sub-query codec depend on.
3. **Child-cut `hglueless` — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean).**
   `addressTargets_empty_of_allGlued`: a `fromNsWithGlueAll names glue mc` whose EVERY NS name has a
   matching (case-folded) glue address emits only addressed servers `⟨n, some ga, 0⟩` (never the glueless
   fallback `⟨n, none, 0⟩`), so `addressTargets = #[]` — the answer/NXDOMAIN terminal's `hglueless`
   (`addressTargets[0]? = none`) at a child cut. Works on ANY `fromNsWithGlueAll`, so it applies both to
   the branch-1 referral SLIST and to the branch-2 re-derived SLIST (`setUpAddresses nsNames (reGlue …)
   mc` IS `fromNsWithGlueAll nsNames (reGlue …) mc` definitionally). Companion to
   `bestWithAddress_isSome_of_glueMatch` (the child-cut `hbest`).
4. **`reGlue` recovers the referral's cached glue (child-cut `hbest`/`hall`) — DONE end-to-end
   (`reGlue_of_referral_glue`, axiom-clean). Only item-5 `Inv` now supplies its premises.** FINDING: a realistic cooperative referral is UNTRUNCATED, so
   `currentCloser_false_referral` pins its continue-state to the branch-2 cache RE-DERIVE SLIST
   `fromNsWithGlueAll nsNames (reGlue cache' now nsNames) mc` (NOT the branch-1 transient-keep SLIST —
   `referral_continue_bestWithAddress` covers only branch 1, so it is NOT usable for the realistic child cut).
   Given the branch-2 SLIST form, BOTH child-cut obligations reduce to one premise via the bricks above:
   `hbest` from `bestWithAddress_isSome_of_glueMatch` and `hglueless` from `addressTargets_empty_of_allGlued`,
   both needing `∀ n ∈ nsNames, ∃ ga ∈ reGlue cache' now nsNames matching n`. That chains
   `mem_reGlue_of_served` (reGlue has a served glue address) ← `lookupTopCred_serves_glue` (a live top-cred
   size-4 `A` entry is served) ← **`storeChecked_pushed_live_maxrank` — DONE, axiom-clean**: a freshly-
   written `storeChecked rr credAdditional now` entry (non-zero TTL `hnz`, fresh expiry `hfresh` from the TTL
   cap, no strictly-more-trustworthy incumbent `hnb` = `storeChecked`'s own `betterExists=false` guard) is
   `liveEntry` + `maxRankForKey` for its key. The guard `hnb` doubles as the top-rank witness (no incumbent
   is strictly more trustworthy ⟹ the additional-cred glue ties-or-wins the per-key rank). REMAINING to close
   (4): lift `storeChecked_pushed_live_maxrank` from a single `storeChecked` to the actual continue-state cache
   `boundLru (cacheUnlessTruncated (cacheUnlessTruncated cache …) resp addRaws credAdditional now) touches now`
   — i.e. (a) the glue `A` is pushed at some `cacheRRs` fold step and survives later steps at top-rank in the
   FINAL fold result — **DONE (axiom-clean, `lookupTopCred_cacheRRs_serves_glue`)**: `Array.foldl_induction`
   with an index-gated motive carrying two folded invariants — `NoBetterGlue` (no fresh same-key entry
   strictly more trustworthy than `credAdditional`, preserved by `noBetterGlue_storeChecked`) and, once past
   the glue raw, `ServesGlue` (some live `credAdditional` size-4 `A` for the key, established at the glue raw
   via `mem_storeChecked_pushed` under `noBetterGlue_betterExists_false`, preserved by
   `servesGlue_storeChecked_preserve` — a replacing multi-glue store re-pushes an equally good witness). At
   the fold end `NoBetterGlue` turns the served entry's liveness into `maxRankForKey`, and
   `lookupTopCred_serves_glue` retrieves it. The two `Inv`-supplied premises are `NoBetterGlue` on the entry
   cache (`hnb0`) and honest-zone expiry/size consistency for same-key raws (`hexp`). Wrapped through the
   `tc`-guard (`lookupTopCred_cacheUnlessTruncated_serves_glue`) and composed with (b)+`mem_reGlue_of_served`
   into **`reGlue_of_referral_glue`** — the branch-2 child-cut `hbest`/`hglueless` glue-match producer;
   (b) it survives `boundLru` —
   **DONE (axiom-clean, `lookupTopCred_boundLru_serves_glue`, commit bb5571c)**: `boundLru = touchKeys ∘
   boundLruKeys`, `touchEntry` only bumps `lastUsed` which NO read path reads (`liveEntry_touchEntry` +
   `maxRankForKey_touchKeys` ⟹ `lookupTopCred_touchKeys` invariance), and below capacity `boundLruKeys` is
   the identity (`boundLruKeys_noop`), so a served size-4 `A` survives the write under the descent `Inv`'s
   capacity bound; and (c) the `betterExists=true` alternative (a pre-existing higher-cred incumbent for the
   glue key is itself served — a disjunctive resolution, not a blocker). (a) is now DONE; only (c) remains,
   best discharged inside item 5's `Inv` where maxRank is clean (the honest cooperative zone caches nothing
   more trustworthy than the referral glue, so `NoBetterGlue` holds and the `betterExists` branch is unused —
   `reGlue_of_referral_glue` takes `NoBetterGlue` as its `hnb0` premise, so (c) collapses to "the `Inv`
   guarantees `NoBetterGlue`", not a separate disjunct).
5. **Assemble the capstone — NOW UNBLOCKED (4 has landed); the ONLY remaining L4 work.** Instantiate `Inv`/`μ`
   (`μ := snameLabels.size − matchCount`) over a `Node ResourceRecord` delegation hierarchy and discharge
   `of_descent`'s step oracle per cut, yielding `ioResumeLoop_adequate`. A depth-1 delegation
   (root → child → answer) is the tractable first instance; the general zone follows by the same step
   oracle. Every per-round *constructor* is now in place: **the delegating step's terminal leaf under the
   address-keyed oracle — `delegatingAnswerRound_delivers` / `delegatingNxdomainRound_delivers` — is DONE
   (`Proof/CooperativeNetwork.lean`, both axiom-clean).** They are the address-keyed siblings of
   `delegatingReferralRound_node` (discharge `honest{Answer,Nxdomain}Round_delivers`'s
   `horacle`/`hid`/`hqm` from `CooperativeNetworkAddr respond` + `hrespEq` via `oracle_supplies_roundAddr`),
   so a delegating descent can END in an answer/NXDOMAIN under the SAME oracle its referral rounds run in —
   the flat `flatAuthoritative_*` terminals need an incompatible `Format → Format` `CooperativeNetwork` and
   cannot cap a delegating descent. So the per-cut step oracle now reads: referral cut →
   `delegatingReferralRound_node` fed by (1)+(2)+(3)+(4); leaf cut → `delegatingAnswerRound_delivers`/
   `delegatingNxdomainRound_delivers`. Every per-cut brick — metric decrease (1), send facts (2),
   `hglueless` (3), both round constructors — is in place, AND the child-cut `hbest` cache-recovery lemma
   (4) is now DONE (`reGlue_of_referral_glue`). So the SOLE remaining L4 work is the zone-indexed `Inv`/`μ`
   that threads these bricks through `of_descent`: define `Inv state fuel revealed w` = "`state` is a
   valid descent cut of a well-formed `Node ResourceRecord` zone `T` under the address-keyed honest oracle
   (`CooperativeNetworkAddr respond w`), with `state`'s SLIST resolving the current cut's server, cache
   satisfying the capacity + `NoBetterGlue` (glue never out-trusted) preconditions of (4), and `μ` labels
   to the target"; then discharge `of_descent`'s step oracle: a non-leaf cut yields a
   `delegatingReferralRound_node` whose `hbest` is `reGlue_of_referral_glue` (child SLIST) and whose
   `hnext` re-establishes `Inv` at the deeper cut (send facts (2), metric decrease (1), `Inv`-preservation
   of the cache invariants across the round-boundary write); a leaf cut yields
   `delegatingAnswerRound_delivers`/`delegatingNxdomainRound_delivers`. A depth-1 zone
   (root → child → answer) is the tractable first instance.

   **Exact-value `hbest` bricks — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean, commit ca17db9).**
   The address-keyed leaf round (`delegatingAnswerRound_delivers`) needs `hbest` in *exact-value* form
   (`bestWithAddress = some (entry, ipAddr)`) — it must name the destination IP the oracle is keyed on,
   for which `bestWithAddress_isSome_of_glueMatch`'s `.isSome` was insufficient. Added: `foldl_pickBest_mem`
   / `bestWithAddress_mem` (a folded `some (e,a)` is a real server with `e.address = some a` — pickBest
   never invents an address), `mem_fromNsWithGlueAll_addr_glue` (an addressed server carries a glue IP),
   and `bestWithAddress_glueMatch_resolves` (the composition — the child SLIST resolves to `some (entry, ga)`
   with `ga` a supplied glue address). Plus `CooperativeNetworkAddr_of_oracle_eq` (the coop-network premise
   depends only on `w.oracle`, so it survives the descent's post-round world — the `hnext` step that
   re-establishes `hcoop` at each deeper cut). So the depth-1 chain can be built DIRECTLY (no `of_descent`):
   `delegatingReferralRound_node` whose `hnext` returns `DescentChain.terminal (delegatingAnswerRound_delivers …)`
   for the continue-state `st` in the post-round world `w'`, with `st`'s facts from
   `referralReply_continue_sendFacts` + `reGlue_of_referral_glue` + `bestWithAddress_glueMatch_resolves` +
   `addressTargets_empty_of_allGlued` + `CooperativeNetworkAddr_of_oracle_eq`. What remains is the concrete
   zone + responder (referral at the root IP, answer at the child IP, with child glue IPs distinct from root)
   and the `Inv`-preservation of the cache invariants across the round-boundary write.

   **Branch-2 SLIST glue-source correction — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean).** A
   discrepancy the capstone assembly hits: `reGlue_of_referral_glue` recovers glue from the round's
   `boundLru`'d *cache*, but the branch-2 (cache re-derive) continue-state SLIST
   (`afterResume_referral_continue_cases`, `Refinement.lean:9259`) reGlues over the cache **before** the
   `boundLru` — its glue is `reGlue (cacheUnlessTruncated c resp raws cred now) now nsNames`, NO `boundLru`
   wrapper. Since the child cut's `hbest`/`hglueless` read `st.resources.slist` (that branch-2 SLIST), they
   need the glue in the *pre-`boundLru`* reGlue. Added `reGlue_preBoundLru_of_referral_glue` (=
   `reGlue_of_referral_glue` minus the item-4b `boundLru`-survival step — no capacity bound / touch list
   needed) and `bestWithAddress_reGlue_resolves` (the branch-2 SLIST resolves to `some (entry, ga)` with
   `(gn, ga)` real glue — exact-value `hbest` — via `bestWithAddress_glueMatch_resolves` with the reflexive
   `foldNameCase` self-match). So the depth-1 chain's child-cut `hbest` is the branch-2-matching
   `bestWithAddress_reGlue_resolves ∘ reGlue_preBoundLru_of_referral_glue`, and `hglueless` is
   `addressTargets_empty_of_allGlued` over the same pre-`boundLru` reGlue (per-name `hall` from the same
   brick — trivial for a singleton `nsNames`).

   **Continue-state terminal-facts packaging — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean,
   `cooperativeReferral_continue_terminalFacts`).** The connective tissue between the depth-1 chain's
   referral node and its terminal leaf: given a cooperative referral round (`resp` + referral
   classification premises) whose branch-2 (cache re-derive) inversion applies
   (`afterResume_referral_continue_slist`'s `hwalk`/`hclose`/`hnb` over the named post-round intermediate
   cache `postCache`), a fully-glued NS set (`hall`/`hnsMem`/`hg`), and the parent's question + canonical
   `sname`, it produces the UNIQUE continue-state `st` bundled with ALL FIVE facts the delegating terminal
   round (`delegatingAnswerRound_delivers`/`delegatingNxdomainRound_delivers`) consumes: `hcont`
   (`.continue st`), `hsendq` (`st.currentStep = .sendQueries`), canonical `st.sname`, `hbuild`
   (`buildSubQuery` succeeds — `st` keeps the parent's question-carrying `lastQuery`), exact-value `hbest`
   (`st.slist.bestWithAddress = some (entry, ga)`, naming the child destination IP) and `hglueless`
   (`st.slist.addressTargets[0]? = none`). Composes `afterResume_referral_continue_slist` (SLIST inversion)
   with `branch2_childSlist_resolves` (SLIST → `hbest`/`hglueless`) and the `buildSubQuery`-succeeds
   derivation. So the depth-1 chain's `hnext` reduces to: run this lemma to get `st`'s facts, note
   `afterResume` determinism (its `st` = the node's `hcont` `st`), and cap with the terminal
   `delegatingAnswerRound_delivers`.

   **Exact-value continue-state facts (names the child destination) — DONE
   (`cooperativeReferral_continue_terminalFacts_exact`, axiom-clean).** Same premises as
   `cooperativeReferral_continue_terminalFacts`, but the `hbest` conjunct additionally EXPOSES the
   resolved glue pair `(gn, ga) ∈ reGlue postCache state.now nsNames` (the packaged variant hides `ga`
   behind an existential with no provenance handle). The depth-1 assembly needs this: its two-server
   responder answers the CHILD query at the SLIST-resolved IP `ga`, and a `respond := fun addr q =>
   if addr == ipv4ToAddr rootIp then referralReply … else treeRespond childT childNeg q` discharges the
   child arm only via `if_neg` under `(ipv4ToAddr ga == ipv4ToAddr rootIp) = false` — proved from the
   exposed `(gn, ga)` glue pair + a zone premise `hglueDistinct` (every child glue IP's addr ≠ root's
   addr, a `by decide`/`rfl` over concrete addresses at instantiation, so NO `ipv4ToAddr`-injectivity
   lemma is needed in the assembly). Reads the exact `hbest` off `bestWithAddress_reGlue_resolves`.

   **Precise depth-1 assembly recipe (the remaining `depth1Delegation_chain`, XL but now fully
   scoped).** Conclusion `∃ out, DescentChain sbelt (now+budget) depth out state (fuel'+1) revealed w`
   (existential `out` sidesteps writing the giant answer term). Structure:
   `delegatingReferralRound_node` (round 1, referral at `rootIp`) whose `hnext` returns a
   `DescentChain.terminal` from `delegatingAnswerRound_delivers` for `st` in `w'`. KEY PLUMBING FACTS
   worked out: (a) **`out` is `w'`-independent** because `hnext`'s conds pin `w'.ids = w.ids` and
   `w'.idCtr = w.idCtr + 2`, so the round-2 sub-query secrets `w'.ids w'.idCtr = w.ids (w.idCtr+2)` are
   FIXED in `w` — express `out` in `w`-terms and `rw` the conds inside `hnext`. (b) **`st` determinism**:
   the `st` from `_terminalFacts_exact` = the `hnext`-bound `st` by `afterResume` being a function
   (`Server.afterResume … = .continue st` injective). (c) **round-2 `hlk`/`hq` (the real content)**: the
   child answer is `treeRespond childT childNeg sent2`, so classification comes FREE from
   `treeRespond_answer_classified` — but needs `hq2 : sent2.question[0]? = some qu2` and `hlk2 :
   treeLookup childT qu2.qname qu2.qtype = .answer rrs`. Since `afterResume` PRESERVES `sname`
   (`referralReply_continue_struct`: `st.sname = state.sname = qname`) and `buildSubQuery st` (under
   `hprobe`) builds a sub-question with `qname = st.sname`, `qu2.qname` = the ORIGINAL query name — so
   `hlk2` is the FIXED fact `treeLookup childT qname qtype = .answer rrs`, statable OUTSIDE `hnext`.
   `qu2` characterization threads `buildSubQuery_withSecrets_*` (from the hsent work). This (c) is the
   dominant remaining plumbing. (d) `CooperativeNetworkAddr respond w'` from
   `CooperativeNetworkAddr_of_oracle_eq` + `ho`. Then `resolveWithIO_adequate_of_chain` lifts the chain
   to full `resolveWithIO` depth-1 adequacy.

   ~~So the SOLE remaining L4 work is (i) `depth1Delegation_chain` (the assembly above — pure composition
   of existing bricks + the (a)-(d) plumbing, no new cache reasoning) and (ii) discharging
   `_terminalFacts_exact`'s `hwalk`/`hclose`/`hnb`/`hg`/`hall` + `hglueDistinct` obligations by
   computation over a concrete depth-1 zone's post-referral cache (`walkNs`-trace via
   `walkNs_base`/`walkNs_step`; the NS-served-at-postCache fact, an NS analogue of the size-4-A glue
   bricks).~~

   **(i) `depth1Delegation_chain` — DONE (`Proof/CooperativeNetwork.lean`, axiom-clean).** The full
   two-round assembly, exactly per the recipe: `delegatingReferralRound_node` (round 1 at `rootIp`)
   whose world-generic tail caps with `DescentChain.terminal (delegatingAnswerRound_delivers …)` at
   the continue-state `st` in `w'`. Plumbing as scoped: (a) `out` obtained via an INNER existential
   (`obtain ⟨out, hterm⟩ : ∃ out, ∀ w' …, Delivers … w' out := ⟨_, fun … => delegatingAnswerRound_delivers …⟩`
   — the witness resolves by direct unification; a postponed `refine ⟨_, ?_⟩` hole does NOT work);
   (b) `st` determinism via `.continue` injectivity (`injection (hcont.symm.trans hcont')`);
   (c) round-2 `hq`/`htc`/`hsf` from THREE NEW helper lemmas — `buildSubQuery_withSecrets_question`
   (the sent question = session name case-randomized by the round's 0x20 seed, at the original
   qtype/qclass), `buildSubQuery_withSecrets_header` (`tc`/`rcode` are the client query's own),
   `probeRoundB_false_of_fullReveal` (one `labelCount ≤ revealed` premise discharges both rounds'
   `hprobe`; the deeper floor via `revealedAfterContinue` = `max` on a same-name referral) — so the
   child-zone lookup premise is statable OUTSIDE the tail at the FIXED name
   `randomizeCase (w.ids (w.idCtr+3)) sname`; (d) `CooperativeNetworkAddr_of_oracle_eq`.
   `cooperativeReferral_continue_terminalFacts_exact` now also exposes `st.resources.sname =
   state.resources.sname` and `st.lastQuery = state.lastQuery` (the round-2 plumbing reads them).
   The responder is abstract with two arm equations: `hroot` (root IP → the concrete `referralReply`)
   and `hchild` (EVERY reGlue-recovered glue address → `treeRespond childT childNeg`), which absorbs
   `hglueDistinct` into the concrete responder's `if_neg` at instantiation.

   **(ii) partial — the `hwalk`/`hall` ENGINE is DONE (`referralWrite_nsKey_facts`, axiom-clean).**
   New cache-write INVERSIONS `mem_store_inv`/`mem_storeChecked_inv`/`mem_cacheRRs_inv` (a post-write
   record is an incumbent or the push of a parsed raw) + `mem_lookupTopCred_inv` (a served record
   names its live backing entry) + `cacheRRs_singleton`. Composed: for a referral whose normalized
   authority is a SINGLE NS record at the cut = sname (type NS/class IN, non-zero capped TTL),
   NS-free additional section, and an entry cache with NO record at the cut's NS key (`hnone` —
   trivial for the cold `default` cache), the post-referral double write serves a non-empty NS
   lookup at the cut (⟹ `walkNs_base` fires — `hwalk` with `nsNames := the filterMap` and
   `mc := labels.size sname`), whose walked name set CONTAINS the referral's NS rdata (`hnsMem`) and
   NOTHING ELSE (`hall` collapses to the one glued name). Existence = `mem_storeChecked_pushed` +
   `mem_cacheRRs_preserve` across the additional write + a maxRank argument closed by the inversions;
   exactness = the inversions with `hnone` closing the entry-cache arm and the type mismatch the
   additional-write arm.

   **The concrete depth-1 instance — DONE (NEW file `Proof/Depth1Adequacy.lean`, axiom-clean
   `[propext, Classical.choice, Quot.sound]`).** `resolveWithIO_depth1_adequate`: against an
   address-keyed two-server cooperative network (root referring, child answering at the referral's
   own glue address), an entry `resolve` pause over a COLD cache delivers the child zone's answer in
   exactly two rounds — every premise per-instance-computable. The assembly deviated from the recipe
   in two places, both simplifications: (a) `hclose` is NOT a per-instance computation — it is the
   GENERIC `currentCloser_false_of_ge` (Refinement), since `walkNs` stops at the queried name itself
   whose label count (`delegationMatchCount_le`) bounds any delegation cut; (b) the two-server
   responder premises (`hroot`/`hchild`/`hegressGlue`) collapse to TWO addresses because of a new
   **`reGlue` exactness engine**: `mem_reGlue_inv` (a recovered pair names a served size-4 `A` whose
   packed rdata is the address) + `referralWrite_reGlue_exact` (over the cold-cache double write,
   EVERY recovered glue address IS the referral's own glue IP `glueIpOf (rrRdata grr)` — entry-cache
   arm killed by `hcold`, NS-push arm by the `A`-key type mismatch, glue-push rdata carried verbatim
   through the TTL aging). Other bricks per the recipe: `referralReply_roundtrips` (round-1 `hrt`
   from `hsent`'s `decode_ok_wire_facts` + canonical NS/glue sections + 16-bit count bounds),
   `hwalk` via `referralWrite_nsKey_facts` conjunct-1 firing `walkNs_base` at fuel `127 + 1 ≡ 128`
   (`mc` pinned to `snameLabels.size` by rewriting the label match with `hsn`), `hall` via
   `allGlued_of_singleton` (conjunct-3 exactness + the `hg` pair + `foldNameCase` refl), `hg` via
   `reGlue_preBoundLru_of_referral_glue` (`hnb0` = `NoBetterGlue` unconditional on the cold cache —
   the only prior write is the NS push, whose key differs in type), `hnb` from `hg` non-emptiness.
   `twoServerRespond` + `_root`/`_child` arm equations are the `if_pos`/`if_neg` bricks a literal
   instance plugs in (child-arm distinctness a `by decide` over concrete IPs). ⚠ Lean gotcha found:
   `injection` on `some grr = some rr'` hit a DETERMINISTIC whnf timeout in this context (even at
   1.6M heartbeats) — `rw [Option.some.injEq]` (or `cases`) closes instantly.

   **Answer pin — DONE (2026-07-13, decision-1 compliance).** The depth-1 conclusion originally
   left `out` fully existential (statement-level no stronger than L0 termination). Now PINNED
   end-to-end: `depth1Delegation_chain` concludes `∃ resp cout, DescentChain … (.ok resp, cout) …
   ∧ resp.answer = rrs.map rrBytes ∧ resp.question = q.question`, propagated through
   `resolveWithIO_depth1_adequate` — the delivered output IS a positive answer carrying the child
   zone's records byte-exact, with the client's question restored. Bricks: `finalizeAnswer_answer`
   / `finalizeAnswer_question` (the finalization wrapper passes the (chain-free) answer section
   through and restores `lastQuery`'s question), `treeRespond_answer_eq` (the child answer arm is
   `rrs.map rrBytes`, state-independent), `st.cnameChain` passthrough re-exported from
   `cooperativeReferral_continue_terminalFacts_exact`, and a new cold-entry premise
   `hchain0 : state.cnameChain = #[]`.

   **Probe-round descent machinery — DONE (2026-07-13, `Proof/{FreeIO,Adequacy,CooperativeNetwork}.lean`,
   all axiom-clean).** The structural gap between depth-1 and general depth: a MULTI-LABEL cooperative
   descent routes its referrals through QNAME-minimisation probe rounds (`seedRevealed = matchCount+1 <
   labelCount`, so `probeRoundB = true` on every non-leaf round), which the descent machinery could not
   express — `DescentChain.referral` hard-required `probeRoundB = false` (exactly why the depth-1
   instance uses a single-label name; `Test/AdequacyPins.lean` documents the same constraint).
   Now closed in three layers:
   - `run_ioResumeLoop_referral_lift` probe premise GENERALIZED to fall-through guard form
     (`hpdeny : probeRoundB && strictDenialB resp = false`, `hpconsume : probeRoundB &&
     !probePassableB resp = false`): one lift covers full-reveal AND probe-shaped referral rounds
     (a followable referral is `probePassableB` — `referralShapedB` — so it reaches `afterResume`
     on a probe round). `Delivers_referral_step`/`DescentChain.referral` generalized accordingly;
     `of_descent` untouched (node builders are opaque to it).
   - NEW `run_ioResumeLoop_probeConsume_lift` + `Delivers_probeConsume_step` + `DescentChain.probe`:
     the reveal step of the ladder — a probe outcome that is neither a strict denial nor passable
     (answer/CNAME/NODATA at the probe ancestor, e.g. an empty non-terminal inside a zone) is
     consumed at the `markQueried` state with `bumpRevealed`; +7 `Prog` steps, `idCtr += 2`. The
     general μ becomes lexicographic: referral rounds decrease the cut coordinate, probe-consume
     rounds the reveal coordinate (encode as `(labels − mc) * (labels+1) + (labels − revealed)` for
     the Nat-valued `of_descent`).
   - `referralReply_strictDenial_false` + `referralReply_probePassable`: for a `referralReply` both
     guards hold UNCONDITIONALLY (rcode is noError; referral-shaped given `hns`/`hsoa`), so
     `honestReferralNode` takes the guard pair and `flatDelegating_referralNode` /
     `delegatingReferralRound_node` DROP the probe premise entirely — a cooperative referral round
     assembles a `DescentChain.referral` node at ANY reveal floor. Terminal rounds (answer/NXDOMAIN)
     rightly keep `hprobe` (a probe-elicited answer is consumed, never delivered).

   **Probe-consume builders + probe-round sub-query — DONE (2026-07-14, commit 59e5ca5, all
   axiom-clean).** Items (a)+(b) of the general-depth remainder:
   - (a) `treeRespond_answer_probeConsumed` / `treeRespond_nodata_probeConsumed` (+
     `treeRespond_nodata_eq`): the zone's answer/NODATA arms at a probe ancestor are neither
     `strictDenialB` nor `probePassableB` (rcode `noError` kills the denial; non-empty answer
     resp. NS-free negative authority kills the referral shape; `noError`-classifiability kills
     the retry shape) — bundled with the probe node's `htc`/`hunfollow`, NO codec round-trip
     needed. `honestProbeConsumeNode` (the `DescentChain.probe` sibling of `honestReferralNode`,
     wire premises via `honestReply_accepted`) and `delegatingProbeConsumeRound_node` (the
     address-keyed wrapper via `oracle_supplies_roundAddr`).
   - (b) `buildSubQuery_withSecrets_question_probe` (on a probe round the sent question is
     `minimisedName sname revealed` case-randomized at qtype A — what the cooperative responder is
     keyed on) + `buildSubQuery_withSecrets_roundtrips_probe` (probe-round `hsent`; canonicity via
     `QnameMin.minimisedName_canonical`, new import).

   **Flat multi-label probe-ladder adequacy — DONE (2026-07-14, commits 8c2c355/1f1801d, all
   axiom-clean).** The first consumer of the probe machinery and the REVEAL-coordinate half of the
   general lexicographic descent: `flatProbeLadder_chain` + `resolveWithIO_flatMultiLabel_adequate`
   — against a flat cooperative authoritative zone whose probe ancestors are NODATA at type A
   (`hplk`, ∀-seed) and whose full name answers (`hflk`), a query of ANY label count (within the
   fuel bound) delivers the answer PINNED byte-exact, descending the RFC 9156 ladder through
   `DescentChain.probe` nodes (cache untouched; SLIST stays a `markQueried`-bumped singleton —
   `bestWithAddress_singleton`/`markQueried_singleton`/`addressTargets_singleton_none`). Strong
   induction on `labelCount − revealed` (`bumpRevealed_metric_lt`), with the world pinned to
   `(oracle, ids, clock, idCtr)` so the delivered output is fixed OUTSIDE the world-generic descent
   tails (the depth-1 plumbing fact (a), iterated per level: the ∃ out sits between the metric
   quantifier and the ∀ w). Removes the flat capstones' single-label full-reveal restriction. NEW
   `treeRespond_nodata_roundtrips` (nodata-arm `hrt`). Pinned executable:
   `Test/AdequacyPins.lean` `flatMultiLabelDelivered` (3-label ladder on `Prog.run`, `idCtr = 6`
   pins exactly two probe rounds + one answer round; randomized probe names exercise the tree's
   case-insensitive `labelEqCI` lookup, matching the ∀-seed premises).

   **(c) Round-boundary cache invariant — the brick pack is DONE (2026-07-14, commit d7c1f15,
   all axiom-clean).** `DescentCacheInv c bound` := every cached record is (if NS-typed) at an
   owner strictly shorter than `bound` WIRE BYTES (an ancestor cut — byte size, not label count,
   is the right measure: `nameEqCI_size` proves case-insensitively equal names have equal byte
   size since `foldNameCase` is a per-byte map, so a shorter ancestor owner can never collide
   with a deeper cut's NS key) and never more trustworthy than `credAdditional` (a cooperative
   referral has `aa = 0`, so BOTH its section writes land at `credAuthority false =
   credAdditional`). Bricks: `DescentCacheInv.nsKey_none` (re-derives
   `referralWrite_nsKey_facts`' `hnone` at every cut of ≥ `bound` bytes),
   `DescentCacheInv.noBetterGlue` (re-derives `reGlue_preBoundLru_of_referral_glue`'s `hnb0`),
   `DescentCacheInv.write` (preservation across the round's double `cacheUnlessTruncated` +
   `boundLru` — NEW inversions `mem_touchKeys_inv`/`mem_boundLru_inv`/
   `mem_cacheUnlessTruncated_inv` pin every post-write record to an incumbent or a push at the
   write's own credibility below the new bound), `DescentCacheInv.of_empty`/`mono` (cold entry,
   descent weakening).

   **(d) The general-depth `Inv`/`μ` assembly — DONE (2026-07-14, NEW file
   `Proof/SpineAdequacy.lean`, all axiom-clean `[propext, Classical.choice, Quot.sound]`).**
   `spineDelegation_chain` + end-to-end `resolveWithIO_spine_adequate`: against an address-keyed
   cooperative network described by a linear single-NS delegation spine (`List SpineHop` +
   `SpineOk` — per hop: the server's zone `T` NODATA-consumes probes strictly above the child cut,
   `hopRespond` refers at/below it, referral sections normalized to singleton NS + singleton glue
   `A`), an entry `resolve` pause over a cold cache delivers the leaf zone's answer at ANY
   delegation depth, descending the full interleaved (cut, reveal) ladder — the answer PINNED
   byte-exact with the client's question restored. Resolution of the open designs:
   - **General responder**: per-hop address table, not a recursive zone walk. Each hop's server
     address is spine-computable (`glueIpOf (rrRdata grr)`) because `reGlue` value-exactness pins
     every recovered glue address to the referral's own glue IP; dispatch inside a hop
     (`hopRespond`) is by question WIRE BYTE SIZE vs the child cut apex (byte size is invariant
     under 0x20 randomization — `randomizeCase_size` — and strictly monotone along the
     minimised-ancestor ladder — `minimisedName_size_lt`), so no `labelCount`-of-randomized-name
     lemma is needed.
   - **Induction shape**: the ladder's pinned-world strong induction (NOT `of_descent`), on
     `μ = spine.length·128 + (labels − revealed)` (labels ≤ 127 keeps the reveal coordinate
     inside the radix), with `∃ resp cout` before the `∀ w` descent tails; case split =
     leaf-terminal (`treeAnswerRound_delivers_pinned`) / probe-consume (shared
     `treeProbeRound_node`, both leaf and hop zones) / referral (`hop.cutLen ≤ revealed`,
     probe/full agnostic).
   - **Warm-cache engines** (the depth-1 cold-cache facts, re-derived per hop):
     `DescentGlueInv c used` (every `A/IN` record's owner CI-matches a used spine glue owner;
     `aNone` re-derives the glue key's emptiness at each unused hop given pairwise-CI-distinct
     spine glue hosts — the `g_fresh_owner` premise; `write` preserves across the round boundary)
     feeding `referralWrite_reGlue_exact_warm`; and `referralWrite_walkNs_facts` — the general
     `hwalk` engine: `walkNs` ASCENDS from the full name to the hop's ancestor cut
     (`walkNs_minimised_ascend` over `parentDomainWire_minimisedName`), intermediate emptiness
     from `DescentCacheInv.write_pre` + `nsKey_none` + the strict ancestor-size ladder, stop
     fact from `referralWrite_nsKey_facts` applied at the apex.
   - **SLIST invariant**: `SlistShape` (all servers = the hop's NS host at its one glue address,
     nonempty, `matchCount` pinned) — established at hop entry from the branch-2 re-derive SLIST
     (`SlistShape.of_fromNsWithGlueAll` under walked-set + reGlue exactness), preserved by the
     probe rounds' `markQueried`, supplying exact-value `hbest`/`hglueless`/`delegationCloserB`
     per round.
   Scope kept (documented refinements, not blockers): single NS + single glue per cut (the
   multi-NS SLIST shape is a `SlistShape` generalization), pairwise-CI-distinct glue hostnames
   along the spine. ~~Cold entry cache at the capstone~~ — CLOSED 2026-07-14:
   `resolveWithIO_spine_adequate_warm` (axiom-clean) is the premise-general capstone over an
   arbitrary entry cache satisfying `DescentCacheInv` (entry-cut byte bound) + `DescentGlueInv`
   at an arbitrary initial used-glue-owner set `used₀` (the spine's glue owners fresh w.r.t.
   `used₀` via `SpineOk`'s `g_fresh_owner`); the cold capstone is its `used₀ := #[]` /
   `of_empty` corollary. ⚠ Lean gotchas hit: `subst h` with
   `h : a = b` eliminates the RHS variable (flipping the determinism equation matters);
   `decide` cannot close goals with free variables (split the `&&` and rewrite the closed
   conjunct first).

   **Regression pin — DONE (`Test/AdequacyPins.lean` `spineDelivered`).** The executable mirror of
   `resolveWithIO_spine_adequate`: a 3-label query against a one-hop spine (`hopRespond` at the
   `com.` cut, `treeRespond` ladder zone at the glue address) descends probe-round referral →
   probe-consume → full-reveal answer on the real `Prog.run`, byte-exact answer + restored
   question, exactly three rounds (`idCtr = 6`) — the interleaved (cut, reveal) node sequence
   neither the depth-1 pin (full-reveal referral) nor the flat pin (probes only) exercises.

   **Remaining after (d): L1 only — now DONE 2026-07-14 (see stage L1 status).** With L1 landed,
   the PROOF ARC (L0–L5) is COMPLETE; L6 (concurrency) landed earlier (engineering at `7e6ec13`,
   merge-consistency theorem 2026-07-14) — **the WHOLE PLAN is DONE**.
   Optional refinements: multi-NS cuts (a `SlistShape` generalization); the warm-entry capstone
   is DONE 2026-07-14 (`resolveWithIO_spine_adequate_warm`, see item (d) scope note).

## Stage L5 — serving adequacy (end-to-end) — **M** (DONE 2026-07-13)
`serveDatagram_adequate` / `serveTcpDatagram_adequate`: a well-formed in-scope query datagram to a
`CooperativeNetwork` yields a reply datagram carrying the model verdict — the completeness sibling
of `serveDatagram_verdict_sound`. Lifts L4 through the decode → resolve → `replyForResolution` →
(truncate | frame) → send tail (shared with the soundness capstone). This is the theorem the
`#eval` mocks + difftest currently stand in for; port those into regression pins here.

**Status: DONE (NEW `Proof/ServeAdequacy.lean`, all axiom-clean).**
- `storeNegativeIfCacheable_runs` / `replyForResolution_runs` — the serve tail is TOTAL (every
  arm at most one `log` + a pure cache write; forward `Prog.run` witnesses).
- `serveDatagram_delivers_of_resolve` / `serveTcpDatagram_delivers_of_resolve` — the per-transport
  serve-tail lift: ingress gates passed (permitted / decoded / `qr=0` / no `queryProblem`) + the
  embedded `resolveWithIO` sub-run delivering (ANY outcome) ⟹ the serve run completes. Forward
  composition (`run_now_bind` → `run_bind` on the sub-run → `run_bind` on the reply build →
  `run_pure'`) over the `serve{,Tcp}Datagram_served` program-level reductions; `sendTo`/`tcpSend`
  are effect-free under `Prog`, so the (truncated | framed) send costs no steps.
- `serveDatagram_depth1_adequate` — END-TO-END: a client datagram passing the gates, against the
  depth-1 two-server cooperative network (premises of `resolveWithIO_depth1_adequate` verbatim at
  the serve clock `w.clock` and the default fuel/depth/budget 40/6/5), is SERVED — with the
  embedded resolution exposed and pinned to `.ok resp`, `resp.answer = rrs.map rrBytes`,
  `resp.question = q.question`. The reply CONTENT at the client boundary is deliberately not
  re-stated: `Prog.run` is deterministic, so the exposed sub-run IS the one
  `serveDatagram_verdict_sound` names, and that capstone already pins the client bytes to
  `deliveredResponse query resp` — pairing the two on the same run gives the cooperative-path iff.
- **Regression pins — DONE (`Test/AdequacyPins.lean`).** Executable mirrors of the adequacy
  theorems using the proof layer's own cooperative-network objects (`mkHonestOracleAddr` /
  `twoServerRespond` / `referralReply` / `treeRespond`) as the responders: `depth1AnswerDelivered`
  (two-server descent on `Prog.run`, byte-exact answer + restored question in exactly two rounds,
  round count pinned via `idCtr = 4`), `depth1NxdomainDelivered`, `flatAnswerDelivered` (depth-0,
  one round), `serveDepth1Delivered` (the L5 serve scenario on `MockM`, where the client reply
  datagram is observable). Single-label qname (`com.`) keeps the pins inside the theorems'
  full-reveal (`hrev`) scope.

## Stage L6 — driver concurrency: fix + documented invariant — **M** (DONE)

**Status: DONE in two halves.** (1) The ENGINEERING (commit `7e6ec13`, 2026-07-12): snapshot-in /
merge-out critical section in `Main.lean` (the lock is never held across
`serveDatagram`/`serveTcpDatagram`'s upstream resolution), the new `DnsCache.absorb`
credibility-safe merge (`Impl/Cache.lean`), TCP `RateBucket` (was an unthrottled ingress), the
documented invariants (`docs/architecture.md` "Driver Concurrency"), and the non-starvation
stress rig (`test/concurrency_stress.sh`, A1/A2 cross-transport + B concurrent-burst, all pass).
(2) The THEOREM half promised by decision 5 (2026-07-14, NEW `Proof/Absorb.lean`, axiom-clean):
`absorb_serve_invariants` — `DnsCache.absorb` preserves the FULL cache invariant pack
`serveDatagram_verdict_sound` consumes on its entry cache and re-establishes on its exit cache,
so the shared cache's well-formedness is INDUCTIVE across serve rounds on both transports.
Structure: membership inversions `mem_absorb_records`/`mem_absorb_negatives` (the merge invents
no entry ⟹ every per-entry invariant transfers from the two inputs), plus the replay filter's
dedup (the same filter as `store`/`storeNegative`) deleting any same-key-different-expiry /
same-NS-key-same-rdata incumbent before each push — so the RELATIONAL invariants
(`OneExpiryPerKey`, `CacheNsDistinct`) and the capacity bound need only `base`'s invariants
(`oneExpiry_absorb_merge`/`nsDistinct_absorb_merge`/`absorb_size_le` take NO hypothesis on
`new`): even a corrupted merge input cannot break them. The non-starvation half stays a
documented invariant + stress test per decision 5 (a `partial` IO loop's liveness is not
kernel-provable).

Original problem statement (fixed by the above): the Stage-S concurrency (`Main.lean`) is
data-race SAFE (one global `Std.Mutex DnsCache`, acquired alone, never nested, no re-entrancy —
the verified core runs on a private snapshot) but had an AVAILABILITY bug and a gap:

- **The cache lock spans upstream network I/O.** `udpServeLoop` (`Main.lean:119-123`) and
  `tcpServeLoop` (`:145-149`) hold `cacheMx.atomically` across the whole
  `serveDatagram`/`serveTcpDatagram`, which calls `resolveWithIO` — every upstream round-trip and
  timeout runs inside the critical section. Effect: (1) zero real concurrency (the two threads
  fully serialise); (2) global head-of-line blocking — one slow delegation chain (up to the query
  deadline) stalls every client on both transports. A DoS surface, arguably worse than the old
  UDP-only single-thread.
- **TCP serving bypasses the rate limiter.** Only `udpServeLoop` calls `rb.bump` (`Main.lean:116`);
  `tcpServeLoop` has no `RateBucket`. TCP is an unthrottled ingress.

**Fix — narrow the critical section to snapshot-in / merge-out:**
1. Under the lock: read the cache snapshot; release.
2. Lock-free: run `serveDatagram`/`serveTcpDatagram` on the snapshot (resolution + upstream I/O +
   client reply happen with NO lock held).
3. Under the lock: MERGE the round's new records back into the CURRENT cache — a
   credibility-respecting merge (`cacheUnlessTruncated` + `boundLru`, the model's own monotone
   write), NOT a blind `set` that would clobber a concurrent writer's insertions. Last-writer-merge
   on an advisory, credibility-gated cache is acceptable (caches may lose a race and re-fetch).
4. Add `RateBucket` to `tcpServeLoop` (a per-transport bucket, or a shared `Std.Mutex RateBucket`).

**Verification posture (decision 5):** liveness of a `partial` IO server loop is not
kernel-provable. Deliverables are (a) the impl change above; (b) a DOCUMENTED invariant in
`docs/architecture.md` — "no cache lock is held across network I/O; a serve on one transport cannot
starve a client on the other"; (c) a stress/differential test in `test/` (concurrent UDP + TCP
floods, assert no transport is starved and the cache stays credibility-consistent). The merge step
IS amenable to a small purity lemma (merge = the model write) reusing the existing
`cacheUnlessTruncated` refinement, so the cache-consistency half can be a theorem even though the
non-starvation half is a test.

## Relationship to existing work

| Existing | This plan |
|---|---|
| `ioResumeLoop_sound` (soundness / refinement) | L4 is its converse; pairs to an iff on the cooperative path |
| total-simulation T0–T5 (impl simulates model, all runs) | L4 reuses its per-round classifiers, oracle arm pinned honest |
| `run_ioResumeLoop_answer` (single honest round) | L3 generalizes it + adds referral/NXDOMAIN siblings |
| `LookupComplete` family | L2 packages it into a 0-round liveness corollary |
| `fuelRank` / `*_ne_maxIterations` | L0/L1 compose them into a per-round descent bound |
| `Test/Loop.lean` `#eval` mocks, difftest rigs | L5 replaces them with a universal theorem; mocks become pins |

## Risk register

| Risk | Mitigation |
|---|---|
| L4 induction cost balloons like `ioResumeLoop_sound` | It is soundness MINUS the adversary — no spoof/lost disjuncts; crib the honest arms only |
| Cooperative-network premise too strong ⟹ vacuous theorem | Model it as honest responses along a concrete `Node ResourceRecord` zone `T` (decision 2), the same object the mocks use — not "answers everything instantly" |
| Adequacy and soundness drift to different answer relations (no iff) | L4's conclusion is stated against the SAME `HasVerdictAt v` soundness consumes (decision 1) |
| L6 non-starvation isn't Lean-provable ⟹ silent regression | Downgrade to documented invariant + stress test; keep the cache-merge purity as a real lemma |
| Snapshot/merge introduces a cache lost-update | Merge via `cacheUnlessTruncated`+`boundLru` (credibility-monotone), never blind `set`; last-writer-merge is acceptable on an advisory cache |
| Scheduling: L4 edits near `ioResumeLoop_sound` | L4 is a NEW theorem in a new file (`Proof/Adequacy.lean`), imports the classifiers read-only — no edit to the soundness proof |
