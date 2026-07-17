# W4 hypothesis audit — liveness/adequacy corpus

Slice: `Proof/CooperativeNetwork.lean`, `Proof/SpineAdequacy.lean`, `Proof/Adequacy.lean`,
`Proof/Depth1Adequacy.lean`, `Proof/ServeAdequacy.lean`, `Proof/NameTreeComplete.lean`,
`Proof/NameTree.lean`, `Proof/RRsetComplete.lean`.

Method: read-only textual/structural analysis of every theorem in the slice; caller-discharge
checked repo-wide with grep; two `lean_minimal_hypotheses` probes
(`honestAnswerRound_delivers`, `FreeIO.run_ioResumeLoop_answer`) to confirm the top unused
suspect. No `.lean` edits, no build.

Classes: **U** = unused (removable), **UR** = unrealistic / scopes the theorem away from the
running system, **OS** = over-scoped conclusion (name/role promises more than delivered),
**LB** = load-bearing and fair. Severity 1 (cosmetic) – 5 (capstone-invalidating).

## Headline findings

1. **`hglueless` is dead plumbing through the whole answer/NXDOMAIN delivery chain (U, sev 3).**
   The base lemmas `FreeIO.run_ioResumeLoop_answer` (FreeIO.lean:275) and
   `FreeIO.run_ioResumeLoop_nxdomain` (FreeIO.lean:403) take
   `hglueless : state.resources.slist.addressTargets[0]? = none` but their proof bodies
   (explicit `rw`/`refine` scripts, no hypothesis-consuming automation) never reference it —
   the loop only reads `addressTargets` under `bestWithAddress = none`, and these lemmas assume
   `hbest = some`. `lean_minimal_hypotheses` reports "load-bearing" only because *call sites*
   pass it positionally (all breaks are application-arity errors, none are proof failures).
   The premise is then re-demanded, unused, by ~12 signatures in this slice:
   `honestAnswerRound_delivers`, `honestNxdomainRound_delivers`,
   `flatAuthoritative_{answer,nxdomain}Round_delivers`,
   `resolveWithIO_flatAuthoritative_{answer,nxdomain}_adequate`,
   `delegating{Answer,Nxdomain}Round_delivers`, `treeAnswerRound_delivers_pinned`, and
   `spineDelegation_chain` manufactures it via `SlistShape.addressTargets_none` just to feed it.
   Deleting it bottom-up is a mechanical cascade and strengthens every delivery theorem for free
   (delivery no longer pretends to require a fully-glued slist below the chosen server).
   Consistency check: the referral/probe nodes (`honestReferralNode`, `honestProbeConsumeNode`,
   `DescentChain.referral/.probe`) already do *not* take it.

2. **The single-NS shape is the one real generalisation gap (UR, sev 4)** — confirmed and
   characterised in the dedicated section below. Adequacy holds on a strictly narrower
   delegation shape than `ioResumeLoop_sound` covers.

3. **Cold-cache premises linger below the spine capstone (UR, sev 3).** The warm refinement
   (`resolveWithIO_spine_adequate_warm`, DescentCacheInv/DescentGlueInv@used₀) landed only at
   the spine base. Still cold-gated: `referralWrite_reGlue_exact` (Depth1Adequacy.lean:64,
   `hcold : c.records = #[]`, warm twin `referralWrite_reGlue_exact_warm` exists but depth1
   doesn't use it), `resolveWithIO_depth1_adequate` (:188), `serveDatagram_depth1_adequate`
   (ServeAdequacy.lean:126), and — notably — the spine *corollaries*
   `resolveWithIO_within_bound` and `resolveWithIO_spine_no_starvation` are stated over
   `resolveWithIO_spine_adequate` (cold), not `_warm`, so the fuel bound and the no-starvation
   guarantee are only stated for a cold start even though the machinery for warm exists.

4. **The serve-boundary adequacy conclusions don't pin the client payload (OS, sev 3).**
   `serveDatagram_delivers_of_resolve`, `serveTcpDatagram_delivers_of_resolve` and the serve
   conjunct of `serveDatagram_depth1_adequate` conclude only
   `∃ n cacheOut w', Prog.run n (serveDatagram …) = some (cacheOut, w')` — termination with
   *some* cache and world. The answer-content pin (`resp.answer = rrs.map rrBytes`) lives on the
   `resolveWithIO` conjunct, i.e. at the resolver boundary, before `replyForResolution`'s scrub/
   truncate/encode. "Delivers" in the names promises the client got the answer; the statement
   does not say what bytes were sent to the client. The dual of
   `serveDatagram_verdict_sound` should pin the encoded reply (or at least `replyForResolution`'s
   output format) on the cooperative path.

5. **`NetworkConsistent`/`NetworkConsistentTcp` are never discharged (UR, sev 3).**
   `ioResumeLoop_complete` / `resolveWithIO_complete` (NameTreeComplete.lean:3230/3483) and the
   model-shim `ioResumeLoop_sound` / `resolveWithIO_sound` (NameTree.lean:1822/2010) take these
   oracle premises, and grep finds zero instantiation anywhere outside `NameTree*.lean` — unlike
   the FreeIO arc, whose transport hypotheses are discharged concretely by `mkHonestOracle*`.
   A `NetworkConsistent T Prog Unit` instance for `w.oracle = mkHonestOracle (treeRespond T neg)`
   looks provable from `treeRespond_*` lemmas and would connect the completeness capstone to the
   same cooperative worlds the adequacy corpus uses. Feed to W2.

6. **`RRsetComplete` is fresh-key-only and orphaned (UR+OS, sev 3).**
   `storeStep_foldl_survivor` and `cacheRRsNorm_complete` both require
   `hfree : ∀ e ∈ cache.records, ¬ SameKey e.rr rr` — the key must be absent from the cache.
   The running system's common case (refreshing an already-cached RRset) is exactly the excluded
   one, and it is the case where the `Blocked` gate can drop members. `cacheRRsNorm_complete`
   has zero consumers repo-wide and no `rfc_proves` citation; the file name promises RRset
   completeness of caching in general.

7. **`hqsf` is derivable from `hrcq` in five spine signatures (U, sev 1).**
   `spineDelegation_chain`, `resolveWithIO_spine_adequate_warm`, `_adequate`, `_within_bound`,
   `_no_starvation` all take both `hrcq : q.header.rcode = .noError` and
   `hqsf : (q.header.rcode == .serverFailure) = false`; the latter is `by rw [hrcq]; decide`.
   One line each to drop.

## Per-theorem table

Grouped where a family shares the same hypothesis profile. Only non-trivial verdicts are
expanded; families marked LB were checked and every explicit premise is consumed directly.

### Proof/Adequacy.lean

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `resolveWithIO_cacheHit_adequate` | `hqu`, `hhit` | LB | both passed to `run_resolveWithIO_answerHit`; conclusion is ∀ world ∀ fuel — network-free, exemplary | none | – |
| `resolveWithIO_cacheHit_treeFaithful` | `hsane hagree hlc hone hneg hhit` | LB | invariant pack consumed by `localAnswer_complete` | none; note 0 refs (leaf capstone, cache-hit dual — keep) | – |
| `terminates_*` helpers, `ioResumeLoop_terminates`, `resolveWithIO_terminates` | (none) | LB | unconditional termination, zero premises | none | – |
| `Delivers_referral_step`, `Delivers_probeConsume_step`, `DescentChain` ctors, `.delivers` | full FreeIO-lift packs | LB | 1:1 images of `run_ioResumeLoop_{referral,probeConsume}_lift` premises | none | – |
| `resolveWithIO_delivers`, `resolveWithIO_adequate_of_chain` | `hpause` | LB | rewrites the `resolveWithIO` match arm | none | – |
| `DescentChain.of_descent` | `Inv`, `μ`, `hstep` | LB | generic well-founded driver | none | – |
| `resolveWithIO_adequate_of_descent` | (whole theorem) | U | 0 refs repo-wide; the spine proof uses `of_chain` directly | delete or keep as documented API; if kept, mark intent | 1 |

### Proof/Depth1Adequacy.lean

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `referralReply_roundtrips` | `hsent hnsz hgsz hcanNs hcanGlue` | LB | all fed to `decode_encode` | none | – |
| `mem_reGlue_inv` | `h` | LB | inversion lemma | none | – |
| `referralWrite_reGlue_exact` | `hcold : c.records = #[]` | UR | cold-cache; warm twin `referralWrite_reGlue_exact_warm` (SpineAdequacy.lean:98) already replaces it with `hAnone`; depth1 still calls the cold one | switch depth1 to the `_warm` form + `DescentGlueInv.aNone` | 3 |
| `referralWrite_reGlue_exact` | `hauthN = #[nsRaw]`, `haddN = #[glueRaw]` | UR | singleton `normalizeSection` = exactly one NS RR and one glue A per referral (single-NS shape, see gap section) | multi-record inverse (per-element, not all-equal-one) | 4 |
| `allGlued_of_singleton` | `hexact : ∀ n ∈ nsNames, n = nsName` | UR | the all-NS-names-collapse premise; only true for single-NS cuts | replace with per-name glue witness | 4 |
| `twoServerRespond*` | – | LB | test-oracle constructors | none | – |
| `resolveWithIO_depth1_adequate` | `hcold` | UR | as above; warm depth1 corollary absent | derive from spine warm machinery | 3 |
| `resolveWithIO_depth1_adequate` | `hauthN/haddN` singletons, `hnsName`, `hgKey` | UR | single NS + single glue shape | see gap section | 4 |
| `resolveWithIO_depth1_adequate` | `hclq`, `hbaiq`, `hroot`, `hchild` (∀ q′) | LB | only instantiated at `sent`, but `sent` depends on `w.ids` secrets, so the ∀-form is the honest way to state it | none | – |
| `resolveWithIO_depth1_adequate` | `hlk` at seed `w.ids (w.idCtr + 3)` | LB (fragile) | pins the 0x20 seed to the exact id-counter offset of round 2; spine uses `∀ seed` (`hflk`) instead | prefer the ∀-seed form for robustness | 1 |
| `resolveWithIO_depth1_adequate` | `sent` + `hsentEq` | U (cosmetic) | `sent` is a definitional alias only ever rewritten by `hsentEq` | inline | 1 |
| `resolveWithIO_depth1_adequate` | remaining ~35 premises (`hpause hsendq hdl hbest hegress hbuild hrev hcanon hsn hlq hqu hqtc hqsf hchain0 hnsz hgsz hcan* hopt* h*cap hns hsoa hpns hnsType hnsClass hnz* hfresh* hpg hgType hgClass hgSize hsz hwfRR`) | LB | each consumed by a named lemma in the proof body | none | – |

### Proof/ServeAdequacy.lean

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `storeNegativeIfCacheable_runs`, `replyForResolution_runs` | (none) | LB | unconditional termination | none | – |
| `serveDatagram_delivers_of_resolve`, `serveTcpDatagram_delivers_of_resolve` | `hperm hdec hqr hqp hres` | LB | rewrite `serveDatagram_served` + run the reply | none | – |
| same two | (conclusion) | OS | "delivers" but concludes only `∃ n cacheOut w', run … = some (cacheOut, w')` — no reply payload pinned | add the `replyForResolution` output (post-scrub bytes) to the conclusion | 3 |
| `serveDatagram_depth1_adequate` | `hcold` | UR | cold-start only; running server is warm | warm variant via spine machinery | 3 |
| `serveDatagram_depth1_adequate` | `hdl : ¬ (w.clock ≥ w.clock + 5)` | LB (note) | UInt32 no-overflow obligation for the hardcoded budget 5; holds except within 5 ticks of wraparound | could be internalized as `w.clock < 2^32 - 5` or discharged | 1 |
| `serveDatagram_depth1_adequate` | singleton `hauthN/haddN`, seed-pinned `hlk` | UR/LB | inherited from depth1 | as depth1 | 4 |
| `serveDatagram_depth1_adequate` | (conclusion) | OS | client-boundary payload not pinned (see headline 4); also no TCP twin | pin reply; add `serveTcpDatagram_depth1_adequate` | 3 |

### Proof/CooperativeNetwork.lean

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `honestDatagram`/`acceptExchanged_honestDatagram`/`honestReply_accepted` | – | LB | | none | – |
| `honestAnswerRound_delivers`, `honestNxdomainRound_delivers` | `hglueless` | **U** | bottoms out unused in `run_ioResumeLoop_answer`/`_nxdomain` (proof bodies verified line-by-line; tool break-analysis shows only call-site arity errors) | delete bottom-up from FreeIO through the chain | 3 |
| same two | rest of pack (`hsendq hdl hbest hegress hbuild hprobe horacle hrt hid hqm hsanEq htc hunfollow hcname hsf hcls hans/hnerr`) | LB | each drives one guard in the loop unfolding | none | – |
| `honestReferralNode`, `honestProbeConsumeNode` | full packs | LB | mirror `DescentChain.referral/.probe`; correctly do *not* take `hglueless` | none | – |
| `mkHonestOracle`, `CooperativeNetwork`, `oracle_supplies_round` | `hcoop hsent hidP hqP hne` | LB | note: `CooperativeNetwork` = whole-oracle equality ⇒ no timeouts/spoofs at *any* address, every address honestly framed. Only the contacted addresses matter to the proofs; a per-address (or per-exchange) honesty premise would strengthen every consumer and open "partial cooperation" adequacy (one timeout then honest retry is currently outside every adequacy theorem) | consider `HonestAt w addr respond` refactor | 2 |
| `treeRespond` lemma family (`_header_id … _nodata_probeConsumed`, :299–611) | per-lemma | LB | direct case analysis on `treeRespond` | none | – |
| `flatAuthoritative_{answer,nxdomain}Round_delivers` | `hglueless` | **U** | as above | delete | 3 |
| `resolveWithIO_flatAuthoritative_{answer,nxdomain}_adequate` | `hglueless` | **U** | as above | delete | 3 |
| same two | (status) | note | 0 refs repo-wide; they are the *only* NXDOMAIN adequacy capstones (depth 0). Keep; they are the seed for the missing general-depth NXDOMAIN dual | keep, extend | – |
| `canonicalRR_optRRBytes` … `buildSubQuery_withSecrets_*`, `probeRoundB_false_of_fullReveal` | per-lemma | LB | | none | – |
| `WfTreeRR`, `capTtlRR_rrBytes`, `treeRespond_*_roundtrips` | per-lemma | LB | | none | – |
| `InZone`, `WfTree`, `findChild_mem`, `nodeAt_inTree`, `nodeAtName_inTree`, `lookupAt_answer_mem`, `treeLookup_answer_node`, `treeLookup_answer_wfTree` | (whole cluster) | U | `treeLookup_answer_wfTree` has 0 refs; the cluster's only purpose was to derive per-answer `WfTreeRR` from a whole-tree `WfTree`, superseded by the pointwise `hwfRR` premises | delete cluster or wire `WfTree` in as the *nicer* premise (one `WfTree T` instead of `hwfRR` at every capstone) | 2 |
| `referralReply` lemma family (:1357–1514) | per-lemma | LB | | none | – |
| `flatDelegating_referralNode` | full pack | LB | no `hglueless` (correct) | none | – |
| `delegating{Answer,Nxdomain}Round_delivers` | `hglueless` | **U** | pass-through to honest rounds | delete | 3 |
| `delegatingProbeConsumeRound_node` | pack | LB | | none | – |
| `pickBest_*`, `bestWithAddress_*` (:1822–1913) | per-lemma | LB | `bestWithAddress_mem` is the multi-NS-ready primitive | none | – |
| `mem_fromNsWithGlueAll_addr_glue` … `addressTargets_empty_of_allGlued` | per-lemma | LB | | none | – |
| `storeChecked_pushed_live_maxrank`, `mem_{store,storeChecked,cacheRRs,lookupTopCred}_inv`, `cacheRRs_singleton` | per-lemma | LB | | none | – |
| `referralWrite_nsKey_facts` | `hauthN = #[nsRaw]` | UR | singleton authority — single NS per cut | multi-record variant | 4 |
| `referralWrite_nsKey_facts` | `hnone` (no NS key pre-cached at sname) | LB | warm-compatible: discharged by `DescentCacheInv.nsKey_none` | none | – |
| LRU/touch lemmas (`liveEntry_touchEntry` … `lookupTopCred_boundLru_serves_glue`) | per-lemma incl. `hcap ≤ capacity` | LB | capacity premise real (eviction) | none | – |
| `NoBetterGlue`/`ServesGlue` lemmas, `lookupTopCred_cacheRRs_serves_glue`, `…cacheUnlessTruncated_serves_glue`, `lookupTopCred_nameEqCI` | per-lemma | LB | | none | – |
| `reGlue_of_referral_glue`, `reGlue_preBoundLru_of_referral_glue` | `hnb0 : NoBetterGlue` + `hexp` | LB | warm-compatible via `DescentCacheInv.noBetterGlue` | none | – |
| `bestWithAddress_reGlue_resolves`, `branch2_childSlist_resolves` | `hall` (every NS glued) | UR (mild) | full-glue requirement: a cut with one glued NS + one glueless NS is excluded (glueless branch never exercised by adequacy) | see missing-duals: glueless adequacy | 3 |
| `cooperativeReferral_continue_terminalFacts` (non-`_exact`) | (whole theorem) | U | 0 refs; superseded by `_exact` (used at :3013) | delete | 1 |
| `cooperativeReferral_continue_terminalFacts_exact`, `depth1Delegation_chain` | `hchild`/`hegressGlue` ∀ (gn,ga) ∈ reGlue | LB | **multi-glue-ready** quantification — the single-NS collapse happens in the *callers* | reuse as-is for generalisation | – |
| `depth1Delegation_chain` | `hrev : labelCount ≤ revealed` | LB (scope) | depth1 skips the qname-min probe ladder (full reveal at entry); spine handles probes | none | – |
| `referral_continue_*`, `delegationMatchCount_*`, `markQueried_*`, `suffixMatchCount_le`, `delegation_metric_decrease`, `bumpRevealed_*`, `probeRoundB_true_of_lt` | per-lemma | LB | | none | – |
| `bestWithAddress_singleton`, `addressTargets_singleton_none`, `markQueried_singleton` | literal `servers = #[⟨n, some a, k⟩]` | UR | pre-`SlistShape` literal-singleton form | subsume under (generalised) `SlistShape` | 2 |
| `flatProbeLadder_chain` | `hsl : servers = #[⟨nsName, some ipAddr, k⟩]` | UR | literal single-server slist through the whole ladder | restate over `SlistShape` (then over its multi-NS generalisation) | 3 |
| `flatProbeLadder_chain` | `hplk` (all intermediate probes `.nodata`) | UR (mild) | probe ladder only covered when every ENT answers NODATA; a parent answering NXDOMAIN on an intermediate label (non-8020 server) is outside adequacy while soundness covers it (strictDenial arm) | probe-denial adequacy variant | 2 |
| `resolveWithIO_flatMultiLabel_adequate` | `hsl` singleton, `hplk` | UR | same | same | 3 |
| `foldNameCase_size`, `nameEqCI_size`, `DescentCacheInv` family, `mem_{touchKeys,boundLru,cacheUnlessTruncated}_inv`, `DescentCacheInv.write` | per-lemma | LB | the warm-entry toolkit | none | – |

### Proof/SpineAdequacy.lean

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `nameEqCI_{symm,trans}`, `DescentGlueInv` family | per-lemma | LB | warm glue toolkit | none | – |
| `referralWrite_reGlue_exact_warm` | `hAnone` | LB | the warm replacement for `hcold` — good pattern | none | – |
| `referralWrite_reGlue_exact_warm` | `hauthN/haddN` singletons; conclusion "every reGlue address = this one grr" | UR | all-glue-collapses-to-one; blocks multi-NS | per-element inverse: `(gn,ga) ∈ reGlue → ∃ glue record owned by gn with ga = glueIpOf(rdata)` | 4 |
| `SlistShape` (def) | `∀ e ∈ servers, e.name = nsName ∧ e.address = some ip` | UR | **the** single-NS shape: one name, one address, fully glued | generalise (see gap section) | 4 |
| `SlistShape.{bestWithAddress,addressTargets_none,markQueried,of_fromNsWithGlueAll}` | `hnames : ∀ n ∈ nsNames, n = nsName`, `hval : ∀ (gn,ga) ∈ G, ga = ip` | UR | the collapse premises | generalise | 4 |
| `delegationCloserB_of_matchCount`, `minimisedName_*`, `lookupTopCred_isEmpty_of_keyless`, `DescentCacheInv.write_pre`, `walkNs_minimised_ascend` | per-lemma | LB | | none | – |
| `referralWrite_walkNs_facts` | `hauthN = #[nsRaw]`; conclusion `∀ n ∈ nsNames, n = nsrr.rdata` | UR | walkNs result forced to a single target name | multi-NS: conclusion `nsNames = owners of the cut's NS RRset` | 4 |
| `hopRespond_{refer,tree}`, `DescentCacheInv.noBetterGlue_after_auth_write` | per-lemma | LB | | none | – |
| `HopOk` (structure) | `authN = #[nsRaw]`, `addN = #[glueRaw]` | UR | one NS RR + one glue A per hop | array-valued fields | 4 |
| `HopOk` | `plk` (probes `.nodata` for all prevCut < r < cutLen) | UR (mild) | parent zones must answer minimisation probes NODATA (RFC 8020-conformant); NXDOMAIN-on-ENT parents excluded from adequacy though soundness handles them | denial-tolerant probe round | 2 |
| `HopOk` | `g_fresh_owner` (glue owner ∉ used) | LB | drives `DescentGlueInv.aNone`; genuinely needed to keep walkNs from resolving stale glue | none | – |
| `LeafOk`, `SpineOk`, `spineOk_{cons,nil}_iff` | – | LB | | none | – |
| `treeProbeRound_node` | pack incl. `hrcq` (no `hqsf`) | LB | consistent minimal form | none | – |
| `treeAnswerRound_delivers_pinned` | `hglueless` | **U** | fed to `delegatingAnswerRound_delivers` → unused chain | delete | 3 |
| `treeAnswerRound_delivers_pinned` | `hqsf` (no `hrcq`) | LB | | none | – |
| `spineDelegation_chain` | `hqsf` | U (derivable) | implied by `hrcq` (`rw [hrcq]; decide`) | derive internally | 1 |
| `spineDelegation_chain` | `SlistShape` invariant, `DescentCacheInv`, `DescentGlueInv` | UR / LB / LB | shape gap; cache invariants are the warm-entry achievement | generalise shape only | 4 |
| `spineDelegation_chain` | `h127` | LB | feeds `referralWrite_walkNs_facts` (walkNs fuel 128); wire names satisfy it | none | – |
| `resolveWithIO_spine_adequate_warm` | `hqsf` | U (derivable) | as above | derive | 1 |
| `resolveWithIO_spine_adequate_warm` | `hcinv`/`hginv` @ used₀ | LB | the warm-entry premises (replaced `hcold`, cold now a corollary — confirmed) | none | – |
| `resolveWithIO_spine_adequate` | `hcold` | LB (by design) | cold corollary of `_warm`; fine | none | – |
| `resolveWithIO_within_bound`, `resolveWithIO_spine_no_starvation` | `hcold` | UR | stated over the **cold** capstone though `_warm` exists; the fuel-bound and no-starvation guarantees are silently cold-only | restate over `_warm` (mechanical) | 2 |
| `resolveWithIO_spine_no_starvation` | (conclusion) | LB | strongest liveness statement in repo: *any* terminating run yields the pinned answer (via `run_agree` determinism) | none | – |

### Proof/NameTree.lean (soundness shim)

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `treeLookup_*_sound`, `treeLookup_obligation_*`, case-folding lemmas, `wireFormatToLabels_*`, `decode*_valid`, `WfRR` lemmas | per-lemma | LB | | none | – |
| `CacheAgrees` + preservation family (`cacheAgrees_*`), `lookup_agrees`, `normRaws` lemmas, `localAnswer_sound`, `step*_sound`, `resolve*_sound`, `lookupNegative_deserved` | invariant packs | LB | packs preserved by every cache op; hold at `DnsCache.empty` | none | – |
| `NetworkConsistent`, `NetworkConsistentTcp` (defs, consumed by `ioResumeLoop_sound`, `resolveWithIO_sound`, and the `_complete` twins) | (as premises) | UR | never discharged: zero uses outside `NameTree*.lean`; no `NetworkConsistent T Prog Unit` instance exists, so the model-shim sound/complete capstones are conditional on an assumption no world in the repo satisfies (contrast: FreeIO transport discharged concretely) | prove `NetworkConsistent` for `mkHonestOracle (treeRespond T neg)` worlds; register as W2 obligation | 3 |
| `afterResume_sound`, `gluelessRecheck_sound`, `probeAbsent_of_strictDenial`, etc. | per-lemma | LB | | none | – |

### Proof/NameTreeComplete.lean (completeness)

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| congruence/`treeResolve` family, `Reaches` lemmas, `TreeSane` | per-lemma | LB | | none | – |
| `LookupComplete`/`OneExpiryPerKey`/`NegativesFaithful` + full preservation suite, `Sat`/`KeyAt`/`LowFloor` fold machinery | per-lemma | LB | the c8 max-cred architecture; premises all consumed | none | – |
| `localAnswer_complete` | `hsane hagree hlc hone hneg` | LB | | none | – |
| `StateOK` (structure), `stepCheckLocal/stepAnalyzeResponse/step/resolveLoop/resume/resolve_complete` | packs | LB | | none | – |
| `ioResumeLoop_complete`, `resolveWithIO_complete` | `hnet`, `hnetTcp` | UR | same undischarged-oracle issue as the sound shim (see above); this is the `rfc_proves [2181]` completeness capstone, so its RFC citation currently rests on an unwitnessed premise | same fix connects it | 3 |

### Proof/RRsetComplete.lean

| theorem | hypothesis | class | evidence | action | sev |
|---|---|---|---|---|---|
| `storeStep_foldl_survivor` | `hu : UniformTtls L` | LB | realistic: established by `normRaws_uniform` | none | – |
| `storeStep_foldl_survivor` | `hfree : ∀ e ∈ c.records, ¬ SameKey e.rr trr` | UR | fresh-key-only; RRset refresh (the warm common case, and the case where `Blocked` can drop members — bugs.md #4) is excluded | needs the coordinated model+impl TTL-normalisation from the #4 analysis, or a `Blocked`-aware survivor statement | 3 |
| `storeStep_foldl_survivor` | `httl ≠ 0` | LB | ttl-0 RRs are deliberately not stored | none | – |
| `cacheRRsNorm_complete` | `hfree`, `hnz` | UR | inherits fresh-key scoping | same | 3 |
| `cacheRRsNorm_complete` | (status) | OS | 0 consumers, no rfc citation; file/theorem name promises cache-write RRset completeness generally, delivers first-write only | wire into a capstone (e.g. answer-write conjunct of the delivery theorems) or rename | 3 |

## The multi-NS `SlistShape` gap, precisely

**Status (plan-2 Topology row; finding 035): the 035 coverage gap is CLOSED**
(`VeriDNS/Proof/Failover.lean`, axiom-clean). The set-valued `SlistShape'` (a cut with a *set*
`nsSet : Array (ByteArray × BitVec 32)` of NS-name/glue-address pairs; every slist entry realises
one of them) generalises `SlistShape`, which is kept as its singleton instance
(`SlistShape.toShape'` / `SlistShape'.toSingleton` round trip — so the single-NS spine/depth1
capstones compile unchanged). The **failover adequacy theorem** `run_ioResumeLoop_failoverAnswer`
proves that a multi-homed cut whose first-picked server times out and whose *distinct second*
server then answers delivers the answer (content pin `resp'.answer = resp2.answer`); the impl
mechanism is the resolver's own least-tried-first `bestWithAddress` rotation with `markQueried`
(`run_ioResumeLoop_timeout'` ∘ `run_ioResumeLoop_answer`). The set shape of a genuinely multi-NS
cut is built by `SlistShape'.of_fromNsWithGlueAll` with **no** name/address collapse (only a
full-glue premise). The set-valued collapse-point primitives are all present:
`SlistShape'.{bestWithAddress,markQueried,addressTargets_none}` and `reGlue_owned` (collapse point
(c), the per-element glue inverse). The only residue is a re-statement: the spine/depth1 capstones
still *state* `SlistShape`; migrating their binder to `SlistShape'` would delete the `topology`
scope gate outright but is not required for 035 and is left as follow-up. The gate now carries an
updated `open_scope` note in `RFC/ScopeLedger.lean` recording the closure.

Original characterisation (retained for the collapse-point map):

Adequacy originally covered only referral cuts of the shape **one NS RR, one glue A RR, all slist
entries sharing that one name and address**. Soundness (`IoResumeSound.ioResumeLoop_sound`)
has no such restriction.

Where the single-NS shape enters (four coupled points):

1. **Section singletons** — `hauthN : normalizeSection (bailiwickRaws (referralCutRaw nsAuth) nsAuth) = #[nsRaw]`
   and `haddN : … glue … = #[glueRaw]` in `referralWrite_reGlue_exact(_warm)`,
   `referralWrite_nsKey_facts`, `referralWrite_walkNs_facts`, `HopOk.authN/addN`, and both
   depth1 capstones. One NS record and one glue record survive the cut.
2. **walkNs collapse** — `referralWrite_walkNs_facts` concludes
   `∀ n ∈ nsNames, n = nsrr.rdata`: after the referral write, the cache walk finds exactly one
   NS target name.
3. **reGlue collapse** — `referralWrite_reGlue_exact(_warm)` concludes every `(gn, ga) ∈ reGlue`
   has `ga = glueIpOf grr.rdata`: all servable glue is one address.
4. **`SlistShape` itself** (SpineAdequacy.lean:158) — `∀ e ∈ s.servers, e.name = nsName ∧
   e.address = some ip`, fed by `SlistShape.of_fromNsWithGlueAll` whose `hnames`/`hval`
   premises are exactly collapses (2) and (3).

Theorems gated on the shape: `SlistShape.*` (4), `referralWrite_walkNs_facts`,
`referralWrite_reGlue_exact(_warm)`, `allGlued_of_singleton`, `HopOk`/`SpineOk` and everything
downstream — `spineDelegation_chain`, `resolveWithIO_spine_adequate_warm`, `_adequate`,
`_within_bound`, `_no_starvation`; plus the depth1 family
(`resolveWithIO_depth1_adequate`, `serveDatagram_depth1_adequate`) and the flat ladder
(`flatProbeLadder_chain`, `resolveWithIO_flatMultiLabel_adequate`, via literal
`servers = #[⟨nsName, some ipAddr, k⟩]`).

What a generalisation needs (in dependency order):

- `SlistShape'` : `s.servers` nonempty ∧ `∀ e ∈ s.servers, ∃ (n, ip) ∈ nsSet, e.name = n ∧
  e.address = some ip` ∧ `matchCount = mc`, for a finite `nsSet : Array (ByteArray × BitVec 32)`.
  `bestWithAddress` then yields *some member* of `nsSet` — the existing
  `bestWithAddress_mem` (CooperativeNetwork.lean:1906) is already the right primitive;
  `SlistShape.bestWithAddress` just needs the ∃-over-set conclusion.
- Per-element write inverses: replace the two "exact" collapse lemmas with
  `(gn, ga) ∈ reGlue post … → ∃ g ∈ glue-section, owner(g) ~CI gn ∧ ga = glueIpOf (rdata g)`,
  and `walkNs = some (nsNames, cutLen)` with `nsNames ⊆ {rdata of the cut's NS RRs}`
  (both provable by the same `mem_cacheRRs_inv` decomposition already used, minus the
  `Array.mem_singleton` collapse).
- `HopOk` fields become RRset-valued: `nsRaws : Array`, `glueRaws : Array`, with
  `resp_eq`, `plk`, `next_egress`, `g_fresh_owner` quantified over **every** glue address of
  the hop (the pattern already exists: `depth1Delegation_chain`'s `hchild`/`hegressGlue` are
  quantified over all reGlue pairs — the collapse there is introduced only by its callers).
- `DescentGlueInv` used-set pushed with *all* hop glue owners (`used.push` → `used ++ owners`).
- `SpineOk`'s recursion carries the *set* of next-hop ips; since `bestWithAddress` picks
  nondeterministically (by rank), `HopOk` for the next hop must hold at whichever member is
  picked — i.e. quantify hop obligations over the set (all hops of one cut serve the same
  `hopRespond`, which is also the realistic zone picture).
- Full glue is still assumed (every NS in the cut has a glue A). Partially-glued cuts route
  through the `bestWithAddress = none`/`addressTargets` glueless branch, which no adequacy
  theorem exercises — that is a separate missing dual (below), not part of the SlistShape
  refactor.

## Missing adequacy duals (W3 input)

Soundness/totality capstones repo-wide vs. their adequacy converse on the cooperative path.
("Paired" = a content-pinned delivery theorem exists for the same terminal.)

| soundness capstone | location | adequacy dual | status |
|---|---|---|---|
| `ioResumeLoop_sound` (network flagship) | IoResumeSound.lean:3468 | `resolveWithIO_spine_adequate(_warm)` | **paired, narrower**: answer terminal only, single-NS spine, glued referrals only |
| `resolveWithIO_verdict_sound` | ResolveWithIOSound.lean:1008 | spine + depth1 + flat capstones | paired for the positive-answer verdict; other verdicts unpaired (below) |
| `resolveWithIO_answerHit_sound` / `_full_sound` | ResolveWithIOSound.lean:712/843 | `resolveWithIO_cacheHit_adequate` + `_treeFaithful` | **paired** |
| `resolveWithIO_negHit_sound` / `resolveWithIO_negative_full_sound` | ResolveWithIOSound.lean:666/775 | — | **missing**: no negative-cache-hit adequacy (`localAnswer = .negative` terminal; `resolveWithIO_cacheHit_adequate` covers `.answerHit` only) |
| NXDOMAIN network terminal (inside verdict/loop soundness) | — | `resolveWithIO_flatAuthoritative_nxdomain_adequate` | **partial**: depth 0 flat only; **missing at any delegation depth** (spine leaf is pinned to `.answer` via `hflk`) |
| NODATA network terminal | — | — | **missing** as a *terminal* (nodata appears only as internal probe rounds); no capstone delivers a NOERROR/empty answer |
| CNAME-chase terminals (trustedCname arms of loop soundness) | IoResumeSound | — | **missing**: every adequacy capstone requires `cnameChain = #[]` and `cnameToChase resp = none` |
| glueless-delegation arm (depth recursion) of `ioResumeLoop_sound` | IoResumeSound | — | **missing**: no adequacy theorem enters `bestWithAddress = none`; only unconditional `ioResumeLoop_terminates` touches that branch |
| TC→TCP fallback arm (stage U) | IoResumeSound (tcp branch) | — | **missing**: all adequacy paths assume `tc == 1 = false`; no "truncated UDP ⇒ whole answer via tcpOracle delivered" dual |
| `serveDatagram_verdict_sound` | ResolveWithIOSound.lean:3553 | `serveDatagram_depth1_adequate` | **paired, narrower**: depth 1, cold cache, single NS, and client payload not pinned (OS finding 4) |
| `serveDatagram_total` | ResolveWithIOSound.lean:3826 | `serveDatagram_delivers_of_resolve` | paired-in-spirit (both totality); content dual is the depth1 theorem |
| `serveTcpDatagram_verdict_sound` | ServeTcp.lean:34 | `serveTcpDatagram_delivers_of_resolve` | **partial/missing**: termination only; no `serveTcpDatagram_depth1_adequate` (no content pin at the TCP client boundary) |
| `serveTcpDatagram_total` | ServeTcp.lean:272 | `serveTcpDatagram_delivers_of_resolve` | paired (totality) |
| `resolveThenReply_sound`, `replyForResolution_answer_sound` | ServeSound.lean:108/83 | `replyForResolution_runs` | **partial**: runs-to-completion only; the scrub-preserves-the-cooperative-answer direction (reply still *contains* the answer after `scrubAnswer`) has no adequacy statement |
| `serveSeq_sound` / `serveSeq_total` | ServeSequence.lean:215/333 | — | **missing (mild)**: no per-datagram content adequacy across a served sequence (single-datagram duals would lift) |
| `resolveWithIO_error_sound`, `ioResumeLoop_error_sound` | ResolveWithIOSound.lean:3449, IoResumeErrorSound.lean:706 | `resolveWithIO_spine_no_starvation` | intentionally unpaired (adequacy of failure not wanted); no-starvation already excludes error outputs on the spine path |
| `resolveWithIO_complete` / `ioResumeLoop_complete` (model shim) | NameTreeComplete.lean:3483/3230 | n/a (completeness) | conditional on undischarged `NetworkConsistent` — see finding 5 |
| `resolves_delivered_grounded_and_authentic` | DeliveredAuthentic.lean:9 | n/a (model-level authenticity) | – |
| `ioResumeLoop_sent_minimised` | SentMinimised.lean | n/a (sent-side property) | – |

Priority order suggested for W3, by (severity of gap × reuse of existing machinery):
1. NXDOMAIN at general depth (reuse spine: add a `.nameError` leaf alternative to `hflk` in
   `LeafOk` — `treeRespond_nxdomain_*` round lemmas already exist).
2. Negative cache-hit (mirror of `run_resolveWithIO_answerHit`; the `.negative` localAnswer arm
   and `lookupNegative_verdict` already exist).
3. TCP serve content dual (`serveTcpDatagram_depth1_adequate`, sed-copy of the UDP one per the
   ServeTcp recipe) + pin the client payload in both serve conclusions.
4. Multi-NS `SlistShape` generalisation (section above).
5. NODATA terminal; then CNAME-chase; then glueless arm; then TC→TCP.

## Counts

| class | count | notes |
|---|---|---|
| Unused (U) | 20 | `hglueless` ×12 signatures (1 root cause), `hqsf` derivable ×5, dead decls: `cooperativeReferral_continue_terminalFacts`, `resolveWithIO_adequate_of_descent`, WfTree cluster (counted 1), `sent`/`hsentEq` inlining (cosmetic, counted under depth1) |
| Unrealistic / scoping (UR) | 14 | single-NS shape (7 entry points, counted per theorem-family), `hcold` ×3 (depth1, serve, spine corollaries), `NetworkConsistent` undischarged ×2 capstone families, `hfree` fresh-key ×2, probe-NODATA-only ×2, whole-oracle cooperativity ×1 (note-level) |
| Over-scoped conclusion (OS) | 4 | serve "delivers" without payload pin ×2, `serveDatagram_depth1_adequate` client boundary, `cacheRRsNorm_complete` |
| Load-bearing and fair (LB) | ~180 hypothesis groups across ~140 theorems | including the exemplary zero-premise termination theorems and the warm-entry invariant pack |

Known-context confirmations: liveness L0–L6 complete as recorded; `resolveWithIO_spine_adequate_warm`
does replace `hcold` with `DescentCacheInv`/`DescentGlueInv @ used₀` and cold is a genuine
corollary (verified at SpineAdequacy.lean:1700–1704); multi-NS `SlistShape` is the only
*structural* generalisation gap, but the fuel-bound/no-starvation corollaries being cold-only
and the serve-boundary payload pin are two smaller re-statement gaps found on top of it.
