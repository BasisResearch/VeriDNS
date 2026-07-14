# Total simulation (assurance gap C, the last open gap-class) — plan

> **✅ ALL STAGES COMPLETE 2026-07-11** (T0 recon, T1 error verdicts, T2 client-boundary
> discharge, T3 serve-sequence corollary, T4a honest-CNAME upgrade + T4b audit, T5
> RFC 3597 carrier + qtype lift). See the per-stage sections for what landed; the
> give-up follow-ups and T4b residuals remain recorded below as future items.

Make the per-datagram capstone **total**: for EVERY terminating `serveDatagram` execution on
a permitted, decodable, well-formed client datagram, a model justification — closing the
unconstrained escape hatches in today's statement. Gap classes (2)(3)(4) of
`docs/assurance-roadmap.md` are closed; this is the remaining gap (1) work. The roadmap's C
section (written 2026-06-27) predates the July arc — its C3 "recursive frontier" induction
LANDED as `ioResumeLoop_sound` (2026-07-04, in `lake build` since `6f68ddd`) and is already
wired to the client boundary as `serveDatagram_verdict_sound`
(`Proof/ResolveWithIOSound.lean:3237`). This plan supersedes that section's TODO list.

Triaged against HEAD `ae5bd7c` (post item-5 read-LRU).

## Locked decisions (user, 2026-07-11 — lens: most realistic model, unbound parity)

1. **SERVFAILs: TWO constrained rules — `Resolves.gaveUp` + `Resolves.loopDetected`.**
   `gaveUp` for budget exhaustion (fuel / deadline / glueless depth — unbound's
   target-fetch-policy/MAX_TARGET_COUNT/timeout family); `loopDetected` for the RFC 1034
   §3.6.2 CNAME guards (chase cap 8, revisit detection — unbound's MAX_RESTART_COUNT = 11
   family), separately citable in the coverage layer. BOTH pinned to `rcode = servFail`,
   empty answer, NO cache write (`cf = c`) — so neither can justify an answer delivery or a
   cache mutation: the ~14 `Resolves` inductions gain two TRIVIAL cases and no existing
   `.ok`-outcome guarantee changes force (the weakening-audit that motivated the
   statement-level-disjunct alternative; rejected in favour of the more faithful model —
   real resolvers demonstrably give up). NOTE: unbound additionally caches SERVFAILs
   briefly (RFC 2308 §7.1 ≤5 min); our impl does not, so the rules write nothing — flagged
   as a possible future impl+model item, not smuggled into the rules.
2. **RFC 3597 unknown-type carrier: YES.** `RRType.unknown (code)` + opaque `RData`. The
   impl is already opaque over type codes (unbound parity); only `αType`'s 16-type table
   drops that traffic from the verified claim. Enumeration ripple confined to the
   abstraction layer (T5).
3. **`qclass = IN` scope KEPT.** Real recursion is IN-only; unbound's CH support is local
   builtins, not upstream recursion. The per-class `CacheNegWf` lift remains available.
4. **`qtype ≠ ANY` scope KEPT.** RFC 8482 direction (minimal answers, `deny-any`); the
   model's existing `QType.star` support keeps a later lift feasible.
5. **`rd`**: T0 confirms-and-documents (upstream rd=0 mirrors the impl's sub-queries; the
   client RD echo is separately proven at the delivered header).

## What "total" means here — and what already holds

`serveDatagram_verdict_sound` today: permitted + decoded + `queryProblem = none` client
query, entry cache invariants, `WorldModels` env-consistency ⟹ the resolution sub-run
exists and **either** `rr = .error msg` (UNCONSTRAINED — no model content) **or** a full
verdict chain: `HasVerdictAt` (derived, no oracle premise — the whole `Resolves` derivation
is CONSTRUCTED by the induction), rcode/answer agreement of the delivered response with the
verdict (scrub-exact), `CacheRefines` on the output cache, `WorldModels` at the final world,
all ten cache invariants RE-ESTABLISHED at `cacheOut` (self-sustaining across datagrams),
and the ≤512 bytes round-trip. The adversary is fully modelled (option-3 transport: loss,
spoofing; accepted-spoof deliveries justified by `trustedReply`/`trustedCname`, poisoning
excluded by the proven bailiwick write bounds).

The FOUR ways today's statement falls short of total, in decreasing severity:

1. **The `.error` disjunct is a free pass.** A SERVFAIL delivery carries no model
   justification at all. Every impl error outcome must be classified: model-justified
   (empty-SLIST ⟹ `Resolves.exhausted`), resource-exhaustion (fuel/deadline — needs a
   model rule or an explicit liveness-not-safety scoping), or proven UNREACHABLE under the
   loop invariants.
2. **Client-boundary hypotheses that should be theorems.** `hqm`/`hcanon`/`hqvalid`/`hqlen`
   (question-name abstraction + canonicity + label validity) are assumptions, yet
   `decode_ok_wire_facts` already proves `QuestionFromLabels` for every decoded question —
   they are dischargeable. After discharge, the only per-query hypotheses left are the
   genuine scope restrictions (see 4).
3. **Honest arms justified by the weak `trusted*` rules.** The cname family's honest arms
   use `trustedCname` (not `answerCname`) because `WorldModels`' honest-cname conjunct is
   rdata-only; the followed-referral honest sub-case assumes rdata canonicity (`n`) that an
   honest server + codec round-trip actually guarantee. Totality already holds THROUGH the
   trusted rules — this track upgrades the model image's *strength* on honest paths, so
   `trusted*` is reachable only under genuine spoofing.
4. **Scope restrictions**: `qclass = IN`, `qtype ≠ *`, qtype ∈ the 16 modelled types,
   `qm.rd = false`, qname ≤ 127 labels. Each needs an explicit keep-or-lift decision.

## Hypothesis classification (verified against the current statements)

| Class | Hypotheses | Disposition |
|---|---|---|
| Environment (legitimate, keep) | `WorldModels`, `net.WF`, `hclock` (no 2^32 wrap), `GluelessProv sbelt` | The unprovable network assumption + belt well-formedness; document as the TCB-adjacent premise set |
| Self-re-establishing (keep, close the loop) | 10 cache invariants at entry | Re-exported at `cacheOut` by the theorem itself; `DnsCache.empty` satisfies all — the serve-sequence corollary (T3) makes this visible |
| Dischargeable (make theorems) | `hqu`/`hqm`/`hcanon`/`ht`/`hqc`/`hqvalid`/`hqlen` | From `decode_ok_wire_facts` + `queryProblem` (qdcount=1); `ht` succeeds iff qtype modelled — folds into scope |
| Scope (decide) | `hqstar`, `hqin`, unmodelled qtypes, `hrd` | See Decisions |

## Stages (each lands green)

### T0 — error-outcome recon + unreachability triage — **S**
Enumerate every `.error` producer and classify. Current inventory (11 sites):
resource-exhaustion {`max IO rounds` (fuel), `query deadline exceeded`, `resolver: max
iterations` (pure fuel), glueless `depth = 0`}, structural {`no servers with addresses in
SLIST`, `cname chain too long` (chase bound 8), `cname loop detected` (RFC 1034 §3.6.2
guard)}, suspected-unreachable {`no response to analyze`, `cannot build sub-query`,
`unhandled response type`, `4b: no NS records in authority`}. For each: model rule /
liveness-scope / unreachability lemma. Output: the T1 checklist with per-error dispositions.
The suspected-unreachable four each get a `run_inversion`-style contradiction lemma or a
documented reachability witness (which would force a model rule).

#### T0 OUTPUT (2026-07-11) — per-error dispositions

Recon done against `a73f472`. The reply-path risk item is confirmed benign:
`replyForResolution`'s error arm is `pure (finalizeForClient (buildErrorResponse query
.serverFailure), cache')` — the returned cache IS `cache'` and `serveDatagram`'s output is
`cache'.boundLru (serveTouches …) nowT`, so a 3-line `replyForResolution_run_err_inv`
sibling + the existing `boundLru` preservation lemmas give the error-arm invariant
re-export. Dispositions (12 rows; the `no servers` message has TWO provenances):

| # | error | site | disposition |
|---|---|---|---|
| 1 | `resolver: max iterations` | `Impl/Resolver.lean:601` | `gaveUp` (T1b). (Since give-up follow-up 2, 2026-07-11: PROVEN UNREACHABLE at fuel ≥ 7 — `resume_ne_maxIterations`/`resolve_ne_maxIterations` in `Proof/Resolver.lean` via the `fuelRank` step-count bound; the `gaveUp` classification stays as the assembly's catch-all but this inhabitant is dead code.) |
| 2 | `resolveWithIO: max IO rounds` | `Impl/Server.lean:736` | `gaveUp` (T1b) |
| 3 | `resolveWithIO: query deadline exceeded` | `Impl/Server.lean:740` | `gaveUp` (T1b) |
| 4 | `resolveWithIO: no servers with addresses in SLIST`, sub-case `addressTargets ≠ []` ∧ `depth = 0` | `Impl/Server.lean:798` catch-all | `gaveUp` (T1b) — glueless-depth budget (unbound MAX_TARGET_COUNT family). Since give-up follow-up 3 (2026-07-11) this arm carries its own message, `resolveWithIO: glueless depth exhausted`, so the assembly cites `gaveUp` exactly |
| 5 | same message, sub-case `addressTargets = []` | same site | `exhausted` (T1a) — genuinely out of servers; the loop induction distinguishes the two branches even though the message can't |
| 6 | `cname chain too long` | `Impl/Resolver.lean:351` (`stepCheckLocal` `.abort`) | `loopDetected` (T1c), RFC 1034 §3.6.2 chase cap 8 |
| 7 | `cname loop detected` | `Impl/Resolver.lean:441` | `loopDetected` (T1c), RFC 1034 §3.6.2 revisit guard |
| 8 | `4b: no NS records in authority` | `Impl/Resolver.lean:487` | **REACHABLE — witness found** (was suspected-unreachable): an accepted reply with `rcode = REFUSED` (any rcode ∉ {noError, nameError, servFail}), empty answer, nonempty non-referral authority (e.g. SOA-only) passes `classifiableB` (authority nonempty), fails `answersQueryB` (empty answer), fails the referral shape AND the noError-nodata arm ⟹ `.error "4b"`. `dropIfBizarre` does NOT filter it (classifiable ⟹ not bizarre). Joins **`gaveUp`** (T1b): the resolver stops on an unusable upstream reply. Flagged (not smuggled in): a future impl improvement is retry-next-server à la unbound's lame-server handling — that would move this row to the `badResponse` retry rule. |
| 9 | `no response to analyze` | `Impl/Resolver.lean:428` | UNREACHABLE — needs the small machine invariant `currentStep = .analyzeResponse → lastResponse.isSome` (analyzeResponse is only entered from `stepSendQueries` on `some`, `resume` sets `some`, nothing clears it en route); contradiction lemma in T1a's loop cases |
| 10 | `unhandled response type` | `Impl/Resolver.lean:505` | UNREACHABLE — **already proven**: `step_analyzeResponse_coverage` (`Proof/Resolver.lean:426`, needs only `lastResponse = some`) |
| 11 | `resolveWithIO: cannot build sub-query` | `Impl/Server.lean:804` | UNREACHABLE under the driver invariant (`state.lastQuery = some q` with `q.question[0]? = some qu`, already threaded through IoResumeSound); `buildSubQuery` is `none` only when both are missing |
| 12 | parser/decode errors (`domain name: …`, Parsec) | `Impl/DomainName.lean`, `Impl/Parsec.lean` | NOT resolution outcomes: upstream-response decode failures are `Option`-collapsed to a lost datagram (`Impl/Server.lean:504`), client decode failures are gated before `resolveWithIO` (`hdec`) |

Verdict-shape audit for the error family: `afterResume`'s error arm returns
`state.resources.cache` — the PRE-round cache (a mid-resume cname write is discarded) — so
`cf = c` is literally satisfied at the round boundary; rows 1–8 all deliver
`buildErrorResponse … .serverFailure` with empty answer, matching the pinned
`gaveUp`/`loopDetected`/`exhausted` outputs.

### T1 — error-outcome model justification — **L** — ✅ COMPLETE 2026-07-11

Landed (d9bb039..HEAD): `Resolves.gaveUp`/`loopDetected` + classifiers; new
`Proof/IoResumeErrorSound.lean` (`ioResumeLoop_error_sound`, 1308 lines vs the .ok proof's
~4800 — the NO-verdict-threading + NO-WorldModels-threading design made the sibling cheap);
`resolveWithIO_error_sound` + `ioResumeLoop_error_sections`/`resolveWithIO_error_sections`
(the CacheRecCanon/CacheNegSoaCanon halves); `replyForResolution_run_err_inv`;
`serveDatagram_verdict_sound`'s error disjunct now carries: HasVerdictAt at the entry cache
with `v.rcode = servFail ∧ v.answer = []` (classified by message — loopDetected for the two
§3.6.2 guards, exhausted for the empty belt, gaveUp otherwise), WorldModels at w₂, and ALL
TEN invariants at both `cache'` and `cacheOut` — the serve-loop invariant closes for BOTH
outcomes. All axiom-clean `[propext, Classical.choice, Quot.sound]`.
The main new proof content. Three sub-tracks, independently committable:
- **T1a `exhausted`**: empty-SLIST/belt SERVFAIL ⟹ `Resolves.exhausted` verdict
  (`exhausted_model_realizable` exists since C2; the impl-side connection through the loop
  is the missing half). Extends `ioResumeLoop_sound` with an `.error`-outcome conclusion
  disjunct (or a sibling theorem `ioResumeLoop_error_sound` — prefer sibling: the `.ok`
  statement's 15-conjunct conclusion shouldn't grow a disjunction that every consumer must
  case on).
- **T1b resource exhaustion** (DECIDED): `Resolves.gaveUp` — fuel/deadline/depth
  SERVFAILs, citable to RFC 1035 §7.2's bounded-work mandate. Constructor pinned:
  `rcode = servFail`, empty answer, `cf = c`. One constructor + one `_hasVerdict`
  classifier + the trivial case in each `Resolves` induction.
- **T1c loop guards** (DECIDED): `Resolves.loopDetected` — `cname chain too long` /
  `cname loop detected`, citable to RFC 1034 §3.6.2 (chase cap + revisit guard). Same
  output pins as `gaveUp`; separate rule purely for the RFC citation surface.
  Then re-assemble: `serveDatagram_verdict_sound`'s first disjunct gains the verdict
  content — every `.error msg` comes with `HasVerdictAt … v` where `v.rcode = servFail`
  (plus the invariant re-export, which `replyForResolution`'s SERVFAIL arm preserves — the
  error arm returns `cache'` through `finalizeForClient (buildErrorResponse …)`, so the
  reply-path packs need an error-arm variant — check `replyForResolution_run_ok_inv`'s
  error sibling in T0).

### T2 — client-boundary discharge — **M** — ✅ COMPLETE 2026-07-11

`serveDatagram_total` (end of `Proof/ResolveWithIOSound.lean`, axiom-clean): wraps
`serveDatagram_verdict_sound` with `hqm`/`hcanon`/`hqvalid`/`hqlen` discharged from
`decode_ok_wire_facts`'s `QuestionFromLabels` (+ new `labelsToWireFormatGo_size_ge`:
≤255-octet wire name ⟹ ≤127 labels), and `hqq`/`hrd`/`hqstar`/`hqin` discharged BY
CONSTRUCTION (the model query is ours: `⟨decoded labels, .rr t, .in, false⟩`). Remaining
premises are exactly: the serve gates, the TWO scope restrictions (`ht`, `hqc` at IN), the
environment set, and the self-sustaining entry invariants.
Prove `hqm`/`hcanon`/`hqvalid`/`hqlen`/`hqu` from `hdec` + `hqp` (via
`decode_ok_wire_facts`, `canonicalName_of_questionFromLabels`, `wireFormat_roundtrip`).
Restate the capstone as `serveDatagram_total` taking only: permission, decode success,
`queryProblem = none`, qtype-abstractable (`αType qu.qtype = some t` — scope), the
environment premises, and the entry invariants. The old statement stays (the new one wraps
it); consumers unchanged.

### T3 — the serve-sequence corollary — **S–M** — ✅ COMPLETE 2026-07-11
New `Proof/ServeSequence.lean` (in `lake build`, 289 jobs, axiom-clean): `serveSeq` folds
`Server.afterRecv` (rate limiter included) over an explicit `(queryBytes, clientAddr)`
list — under `Prog`, `recvFrom` is effect-free, so the list IS the receive sequence.
`serveSeq_sound` threads `ServePack` (the ten invariants, `CacheNegWf` at the concrete IN
code — `αClass_inj` pins every in-scope query's class to it), `WorldModels`, and the clock
(`run_world_frame`) through the three step shapes: rate-dropped (`bump = none` — pure),
gate-failing (`serveDatagram_unserved`: under the free monad ANY failed ingress gate
reduces `serveDatagram` to `pure cache`), and served (`serveDatagram_total`). Conclusion:
pack at the final cache, `WorldModels` at the final world, and a `JustifiedTrace` — every
admitted gate-passing step carries `ServeJustification` (the `serveDatagram_total`
conclusion as a named Prop) at its arrival cache. `serveSeq_total` is the cold-start
instantiation (`DnsCache.empty`/`RateBucket.empty`, `ServePack_empty` vacuous): entry
premises are ONLY the environment set + the per-datagram `InScope` condition (required
only of gate-passing datagrams — out-of-scope resolutions carry no invariant guarantee).
`serverLoop` is `partial` and adds only the periodic sweep; the corollary quantifies over
the sequence, not the loop (documented; no impl change). Follow-up (not blocking): a
concrete served-datagram trace mock (lifting `run_resolveWithIO_networkAnswer` through
`serveDatagram_served` + the reply path) to pin `JustifiedTrace` realizability end-to-end.

### T4 — honest-arm strengthening — **M–L** — T4a ✅ COMPLETE 2026-07-11; T4b audit DONE (two designed residuals recorded)
- **T4a ✅ (275ae84)**: `WorldModels`' honest conjunct #8 strengthened IN PLACE from the
  rdata-only per-CNAME correspondence to the EXACT answer-section equality
  `αSection resp.answer = ref.answer` (mirroring the pre-existing authority/additional
  exactness; arity unchanged, so all positional destructures were stable — and the old
  conjunct had NO consumers). New `cname_classifier_bridge_at` (NetworkSim): the
  cout-exporting honest CNAME classifier through `Resolves.answerCname` with constructed
  transport; the exact-answer conjunct makes the rule's prepended record the impl's own
  chased CNAME and `absorb_resp_congr` retargets the impl-side `WriteRefines` to the
  rule's `ref.answerOwned` absorb slot. All three driver CNAME arms split honest|spoofed;
  `trustedCname` survives ONLY in spoof arms. No WorldModels instances exist to fix (it is
  the assumed environment premise; realizability mocks work at the `Resolves` layer).
- **T4b — the audit result.** The NS-rdata canonicity conjunct the plan asked for already
  exists in the honest disjunct (added during the glueless/cprov arc) and IS consumed by
  the honest referral arms (`hnstail` chains: `extractNsNames_canonical`,
  `glueAddresses_subperm_transient`). Grep audit of the remaining trusted-rule uses:
  - **CNAME family**: honest arms cite `answerCname`; `trustedCname` spoof-only. ✅
  - **Referral family**: honest arms cite `Resolves.referForget`
    (`serverReferForget_hasVerdictAt`) — EXCEPT two honest sub-cases (the walkNs-kept
    SLIST-rebuild arms) that use `trustedReferral` with honest transport
    (`origin = addr`): `serverReferForget` needs
    `ref.descendsBelow (serverBailiwick srv q.qname q.qclass)` and absorbs at the
    SERVER bailiwick, while the trusted rule absorbs at the frontier — upgrading these
    needs either a `serverBailiwick` conjunct in `WorldModels` or a `refer`-rule variant
    absorbing at the cut; a model-design decision, RECORDED AS FOLLOW-UP, not smuggled in.
  - **Answer family (deliberate, documented)**: honest arms route through
    `Resolves.trustedReply` with honest transport (`serverAnswer_hasVerdictAt` and the
    direct sites) because `Resolves.answer` has NO flexible output-cache slot — its cout
    is the full-message absorb, a write the impl's terminal delivery never performs.
    Follow-up options: give `answer` the `cf0`/`cf` `WriteRefines` slots `answerCname`
    already has (model surgery through ~14 inductions), or make the impl cache delivered
    answers (the glueless-arc follow-up) and keep the rule. Until then the attribution is
    trusted-shaped but the TRANSPORT is honest — the verdict content is identical.
  - **Probe terminals (by design)**: `ancestorDenied` and the qname-minimisation
    `trustedReferralProbe` are trusted-SHAPED rules (probe-keyed RFC 8020/9156 terminals
    with no honest sibling); their honest arms construct honest transport.

### T5 — RFC 3597 unknown-type carrier + docs — **M** — ✅ COMPLETE 2026-07-11
Landed (4b39960): `RRType.unknown (code : BitVec 16)` in `Spec/RRType.lean` (new
`include_rfc [3597][63:83]` block verifying §2–§3 at compile time; `rfc/rfc-3597.txt`
added) + `RData.generic (t : RRType) (data : ByteArray)` in `Spec/NetworkModel.lean` —
the carrier holds the `RRType` (not the raw code) so `αRData_rtype` survives for the
named-but-rdata-uninterpreted types (MX, TXT, …), which now also abstract (previously
dropped by `αSection`). `αType` TOTAL (`αType_total`); `αRData` total over type codes
(the five interpreted formats still parse structurally — RFC 3597 §3 forbids generic
treatment of interpreted well-known types); model wire-size layer
(`rdataNames`/`rdataFixed`/`emitRData`) extended per §4 (opaque bytes, never
compression targets). `serveDatagram_total` DROPPED the `ht` premise — `t` is produced
existentially — and the qtype scope shrank to the single deliberate ANY keep, now the
explicit wire-level `hqany : qu.qtype.toNat ≠ 255` (threaded through the five
`resolveWithIO_*_sound` theorems whose proofs derived `≠ 255` FROM `αType` partiality;
`ServeSequence.InScope`'s qtype conjunct became the same exclusion). Sweep notes:
`rrtype_eq_of_beq` is now UNCONDITIONAL (`unknown` carries a lawful-BEq `BitVec 16`;
the NetworkSim/late-Refinement enumeration duplicates now delegate); the three
`rtype ⟹ constructor` inversions that `.generic` falsifies at the model level go
through new `αRData_ns_inv`/`αRData_a_inv`/`αRR_rdata` image inversions;
`ofCode_toCode`/`αType_toCode` gained `isNamed` guards (`ofCode` deliberately stays
the literal RFC 1035 table). 289 jobs green, capstones axiom-clean, impl untouched
(it was already opaque over type codes — unbound parity confirmed by T0 recon §8).
The kept scopes (`qclass = IN`, no ANY) are documented in the capstone docstring.

**🎉 With T5, every stage of this plan is COMPLETE (T4b's two designed residuals are
recorded above as model-design follow-ups). Assurance gap class (1)'s C track is
closed; the remaining open item in that class, D2 (hhit completeness), CLOSED
2026-07-11 — `resolveWithIO_cacheHit_simulates` derives the served-set equality from
the cache invariants instead of assuming it (see the roadmap's D2 entry). Gap class
(1) now has no open items.**

Estimate: **3–5 sessions** (T1 is the L-sized core; T2/T3 are assembly; T4 is bounded model
surgery with known recipes).

## Give-up follow-ups (flagged 2026-07-11 — out of this plan's scope, candidates for later items)

The T0/T1 classification justified every impl SERVFAIL through `gaveUp`/`loopDetected`/
`exhausted`, which is SOUND but tags four spots where the impl (or the classification's
granularity) could be made more faithful to real resolvers:

1. ✅ **DONE 2026-07-11** — **`4b: no NS records in authority` was REACHABLE and the impl
   behaviour it justified was sub-unbound.** Witness (T0 row 8): an accepted upstream reply
   with `rcode = REFUSED` (any rcode ∉ {noError, nameError, servFail}), empty answer, and a
   nonempty non-referral authority (e.g. SOA-only) passed `classifiableB`, failed
   `answersQueryB`, the referral shape, and the noError-nodata arm, and landed on
   `.error "4b: no NS records in authority"` — SERVFAILing the WHOLE query on a single
   lame/refusing upstream reply. FIXED: the analyzer arm is now the lame-reply retry
   (`.goto .sendQueries`, response dropped, nothing cached — like the bizarre arm; the lame
   server is only try-count-demoted via `markQueried`, not removed, matching the least-tried
   rotation; RFC 1034 §5.3.3 4(d) "other bizarre contents"). Spec: `guard_serverFailure`
   gained the "unusable rcode" disjunct so `StepSpec` covers the retry; the model
   `badResponse` rule gained the `LameReply` middle disjunct (harmless width — `timeout`
   already justifies any discard via transport loss — kept for fixed-transport totality
   faithfulness). Proof: `stepAnalyzeResponse_goto_referral` became the disjunctive
   `stepAnalyzeResponse_goto_cases`; new `stepAnalyzeResponse_lame`/`afterResume_lame`
   (Refinement); the driver's three continue sites case on referral|lame (probe site:
   lame is not probe-passable, contradiction; full-round sites: retry via the IH with the
   unchanged belt — no hop rule needed, `markQueried` is model-invisible). The
   `"4b"` error message no longer exists; the error-side assembly is untouched (it never
   matched that string — it fell into the `gaveUp` catch-all, which now has one fewer
   inhabitant).
2. ✅ **DONE 2026-07-11** — **`resolver: max iterations` is now proven unreachable** (was
   gaveUp-justified). The step-count bound landed in `Proof/Resolver.lean`: `fuelRank`
   measures the goto pipeline position on `(currentStep, lastResponse)` — max 7 from ANY
   state, no reachability invariant — and strictly decreases across every goto
   (`step_goto_fuelRank`; the key structural fact is that every goto out of
   `analyzeResponse` clears `lastResponse`, so the re-entered pipeline pauses at
   `sendQueries`). `loop_ne_maxIterations` + corollaries `resolve_ne_maxIterations`
   (fuel ≥ 3) / `resume_ne_maxIterations` (fuel ≥ 7, unconditional over the resumed
   state) cover the driver's three fuel-64 call sites (`afterResume`, glueless
   sub-resolution, `resolveWithIO` entry). Axiom-clean `[propext, Quot.sound]`. The
   error assembly is untouched — the `gaveUp` catch-all stays sound, its max-iterations
   inhabitant is simply dead code (like follow-up 1's vanished `"4b"` message, but by
   theorem rather than by deletion).
3. ✅ **DONE 2026-07-11** — **The `no servers with addresses in SLIST` message conflated two
   provenances.** The T0 table split it (structural belt exhaustion → `exhausted`; glueless
   depth-0 → `gaveUp`), but the ASSEMBLY classified by message string, so both sub-cases
   cited `exhausted`. Fixed by splitting the impl error message: the depth-0 arm now returns
   `"resolveWithIO: glueless depth exhausted"` (→ the assembly's `gaveUp` catch-all, exact)
   while the empty-target arm keeps the old message (→ `exhausted`, now exact). The glueless
   match was NESTED (option outer, depth inner) so the no-servers terminal stays reducible
   with `depth` abstract (`run_ioResumeLoop_noserver` unchanged); ripple confined to
   reordering the option/depth case split in the six loop-proof sites plus one extra trivial
   `pure` arm in the three `split`-based proofs (SentMinimised, NameTree, NameTreeComplete).
   No assembly change was needed — the new message lands in the existing `gaveUp` catch-all.
4. **SERVFAIL caching (RFC 2308 §7.1, ≤5 min).** unbound caches give-ups briefly; our impl
   writes nothing on the error path (which is exactly why `cf = c` is provable). Lifting
   this needs a coordinated impl+model change (a negative-ish SERVFAIL cache entry class) —
   already flagged in locked decision 1, repeated here as the give-up family's fourth item.

## Risk register

| Risk | Mitigation |
|---|---|
| The `.error` arm of `replyForResolution`/reply packs lacks run-inversion lemmas (only `_ok_inv` exists) | T0 checks; the error arm is 3 lines of impl — a small `_err_inv` sibling if missing |
| An "unreachable" error is actually reachable (e.g. `4b: no NS records` on a malformed-but-classifiable response) | T0 demands a witness or a proof, never an assumption; a witness ⟹ that error joins T1c with a model rule |
| `gaveUp`/`loopDetected` weaken the model (an adversary could "justify" anything as give-up) | Both constructors carry `v.rcode = servFail`, empty answer, NO cache write (`cf = c`) — they can justify only an empty SERVFAIL delivery with unchanged model cache; the delivered-shape half stays pinned by the verdict-half theorems. Residual (accepted): a bare SERVFAIL verdict is less structurally informative than under `exhausted`-only |
| T4a's full-RR honest-cname conjunct breaks `WorldModels` instances in NetworkSim mocks/realizability | The conjunct is strengthened where servers are HONEST by construction in those instances — expect mechanical; budget the sweep in T4's M–L size |
| 15-conjunct conclusion churn if `.error` verdicts are folded into `ioResumeLoop_sound` itself | Sibling-theorem shape (T1a) — the existing statement and its ~6 consumers untouched |
| Scope-lift ripple (decision 2) through the 16-way `αType` case proofs (`typeBits`-style enumerations, `eq_of_αType_beq`, RData abstraction) | Confined to Refinement's abstraction layer; the unknown-carrier is opaque rdata, so no per-type semantics — but priced M and gated on the decision |
