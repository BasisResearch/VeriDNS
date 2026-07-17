# W4 hypothesis audit — slice: `VeriDNS/Proof/IoResumeSound.lean` + `VeriDNS/Proof/IoResumeErrorSound.lean`

Date: 2026-07-15. Method: read-only textual/structural analysis. Every named hypothesis binder in
the slice was mechanically checked for occurrence in its proof body (word-boundary-aware,
prime/subscript-safe); the capstone's anonymous ∀-chain was checked against its `intro` names over
the full ~7,600-line proof body. Capstone-adjacent premises were traced through their callers
(`ResolveWithIOSound.lean` → `ServeSequence.lean` / `ServeTcp.lean`) to determine whether each is
*discharged by the caller* or *assumed and never discharged anywhere in the repo*.

Classes: **U** = unused, **UU** = uncertain-unused (consumed only by `omega`/`simp_all`/context
tactics or redundant-in-principle), **UR** = unrealistic, **OS** = over-scoped conclusion,
**LB** = load-bearing and fair, **DS** = documented scope limit (known/recorded, not a new finding).

## Headline counts

- Theorems/lemmas audited: 138 in `IoResumeSound.lean`, 20 in `IoResumeErrorSound.lean` (158 total).
- **Unused: 0** confirmed. (One uncertain-unused pair, `uint32_add_ttl_toNat`, resolved as
  omega-consumed = load-bearing.) Every other named hypothesis in the slice is referenced by its
  proof body. The two capstones' intro'd premises are all used (counts 13–160 each).
- **Unrealistic / assumed-oracle: 4 findings** (2 top-severity), **Over-scoped conclusion: 3
  findings**, **Documented scope limits re-confirmed: 5**, everything else **load-bearing and fair**.

---

## 1. Capstone: `ioResumeLoop_sound` (IoResumeSound.lean:3468)

Callers: `resolveWithIO_paused_sound` (ResolveWithIOSound.lean:181), internal glueless recursion in
`ioResumeLoop_error_sound` (IoResumeErrorSound.lean:908). Premise supply traced up through
`resolveWithIO_verdict_sound` → `serveDatagram_verdict_sound` / `serveDatagram_total` →
`serveSeq_sound`/`serveSeq_total` (ServeSequence.lean) and `ServeTcp.lean`.

| Hypothesis | Class | Evidence / who supplies it | Suggested action | Sev |
|---|---|---|---|---|
| `hnetWF : net.WF` | LB (boundary) | Used 13×. Assumed at every level up to `serveSeq_total`; never discharged for a concrete net. Part of the "∃ well-formed model network the world refines" TCB boundary, together with `WorldModels`. | Record as W2 boundary obligation (exhibit one concrete WF net per difftest scenario so the premise is demonstrably satisfiable). | 3 |
| `hGlSbelt : GluelessProv sbelt` | **UR (assumed, dischargeable, never discharged)** | Used 2×. Assumed at `serveSeq_sound`, `serveSeq_total`, `ServeTcp` capstones. Production sbelt is `DnsSList.mkSbelt rootServers` (VeriDNS/Main.lean:136); **no `GluelessProv (mkSbelt …)` lemma exists anywhere** (`grep GluelessProv` hits only the 5 proof files). Root-hint names are fixed literals, so this is provable (likely by `decide`/`native`-free computation) but the end-to-end chain currently has a hole a caller must fill on faith. | Add `GluelessProv_mkSbelt` (or a concrete `GluelessProv (mkSbelt rootServers)` pin) and thread it from Main-side docs. Cheap, closes a real gap. | 4 |
| `hSM : StateModels …` | LB | Constructed by `paused_StateModels_noPeel` (ResolveWithIOSound.lean:276) from decode facts + `MatchMaxEquiv.refl`. | none | 1 |
| `hwmTcp : WorldModelsTcp …` | **UR (honest-only oracle, assumed, never discharged)** | Used 49×. `WorldModelsTcp` (NetworkSim.lean:151) has **no spoof/adversarial disjunct** — every accepted TCP reply is required to come from an honest model server (`serverAt`+`ServerAnswers`+`linkReach`). The UDP `WorldModels` has the `SpoofReply` arm; TCP does not. Documented as tcp-plan decision 5 ("spoof-FREE honest-or-lost", off-path rationale, docs/tcp-plan.md:74–76), so DS at the plan level — but an **on-path/MITM attacker on the TCP leg is outside every capstone**, and this exclusion is invisible in the theorem statement or nearby comments. Never constructed for any world. | W2: either add an adversarial TCP arm (attacker constrained by connection 4-tuple, i.e. much weaker than UDP spoof) or surface the on-path exclusion as an explicit named assumption in docs/architecture.md and the capstone docstring. | 4 |
| `hCacheWf, hNsCanon, hCnCanon, hwfrr, hNegWf, hNsDistinct, hOE, hCap` (cache pack) | LB | All used 46–60×. Established for the empty cache (`ServePack_empty`, ServeSequence.lean:33) and re-delivered by the conclusion, so the serve loop threads them inductively. Genuine invariants. | none | 1 |
| `hmiss : c.hit now q = []`, `hnmiss : c.negHit now q = false` | LB | Used 71× each. Not "cache assumed empty": they say the *model* cache misses on *this* query, which is exactly the case split — hit paths are covered by `resolveWithIO_negHit_sound`/`resolveWithIO_answerHit_sound`. Discharged by `paused_cacheMiss` (ResolveWithIOSound.lean:321). | none | 1 |
| `hfreshInv : ∀ b ∈ seen, b.length < depthFloor`, `hMC : slist.matchCount = depthFloor` | LB | Frontier/freshness driver invariants; instantiated trivially at entry (`seen = []`, `depthFloor = matchCount`). | none | 1 |
| `hGlProv`, `hGlBelt` (GluelessProv of slist/sbelt in state) | LB | Discharged by `paused_GluelessProv` (ResolveWithIOSound.lean:371) + `walkNs_names_canonical` from `CacheNsCanon`; preserved by the `GluelessProv_*` frame lemmas (L2244–2264). | none | 1 |
| `hqm : ∀ qu, lastQuery ⇒ αQType/αClass agree` | LB | From decode facts at the caller. | none | 1 |
| `hrd : q.rd = false` | LB (definitional, not restrictive) | `q` is the *model* query; nothing links `q.rd` to the client's wire RD bit (only qname/qtype/qclass are pinned by `hqm`/`hsnameCanon`). Top-level `ServeJustification` *constructs* `qm` with `rd := false` (ServeSequence.lean:110), so a client sending RD=1 is still covered — the model verdict is always the iterative one. Worth one comment line so a reader doesn't misread it as "RD=1 clients unsupported". | Add a comment at the capstone; no proof change. | 1 |
| `hqstar : q.qtype ≠ QType.star` | **DS** | QTYPE=ANY(255) excluded; pairs with `hqany : qu.qtype.toNat ≠ 255` upstream and the per-datagram `InScope` gate (ServeSequence.lean:53). Recorded RFC 3597/T5 scope keep. | Keep on the recorded follow-up list; no new finding. | 2 |
| `hqin : q.qclass = RRClass.in` | **DS** | Class-IN-only scope; visible at every layer up to `InScope` (`αClass qu.qclass = some RRClass.in`). Recorded scope keep ("per-class CacheNegWf lift" follow-up). | ditto | 2 |
| `hclock : state.now.toNat + 604800 < 2^32` | LB (realistic) | 7-day headroom before the 2106 UInt32 wraparound; true for any real clock this century. Assumed at top (`serveSeq_total`) — fine. | none | 1 |
| `hsnameCanon`, `hqlen ≤ 127`, `hqvalid` (label sizes) | LB | Derived from `Message.decode` wire facts + `αName_labelsToWireFormat` in `serveDatagram_total`. | none | 1 |
| `hCCM : CnameChainModels state q nseen` | LB | Discharged by `paused_CnameChainModels_noPeel` / `initVisited_models`. | none | 1 |
| `hAW : AnswerWriteWf state.cnameChain state.now` | LB | Discharged by `paused_chain_answerWriteWf` (ResolveWithIOSound.lean:99). | none | 1 |
| `hstep : currentStep = sendQueries` | LB | From `resolve_paused_inv`. | none | 1 |
| `hrun : Prog.run n … = some ((.ok resp, cout), w')` | LB | The subject of the theorem. Note `fuel'`, `depth`, `revealed`, `deadline`, `n` are all universally quantified with **no lower bounds** — no impossible-fuel scoping here (good; matches the fuelRank work). | none | 1 |

### Over-scoped-conclusion notes on the capstone (feed W3)

| Aspect | Class | Evidence | Suggested action | Sev |
|---|---|---|---|---|
| servFail verdicts are model-free | **OS** | Conclusion delivers `HasVerdictAt … v` with `(αResp resp).rcode = v.rcode`; but the model's `Resolves.gaveUp` rule (used via `gaveUp_hasVerdictAt`, WorldNetwork.lean:427) is **unconditional** — any query has a servFail verdict in any cache/net. So on the servFail path the "verdict" conjunct is content-free; the real content there is only cache-invariant + WorldModels preservation. Known: "give-up 4" is the last open give-up item in the total-sim notes, but it is not visible at the theorem statement. | W2/W3: guard `gaveUp` (e.g. require exhausted slist or deadline in the model), or annotate the capstone that servFail carries no verdict content. | 4 |
| glueless hops anchored to a fabricated cache | **OS** | `gluelessNs_anchor_witness` (L2328) has **zero hypotheses**: for ANY `nsQ`/`qn` it manufactures `cprov = {pos := [root NS nsQ]}` satisfying the model's glueless connector. I.e. the `HasVerdictAt` justification for glueless descent does not certify the NS name came from the resolver's actual cache — the model rule's cprov slot is vacuously satisfiable. This is the recorded fork-(b) cprov-slot decision, but the weakening it induces on the capstone's conclusion is not documented at the capstone. | W2: strengthen the model glueless rule to tie `cprov` to the abstracted resolver cache (the impl-side facts to justify it already flow through `hGlProv`). | 4 |
| conclusion omits `WorldModelsTcp w'` | UU/minor | Conclusion re-delivers `WorldModels … w'` but not `WorldModelsTcp … w'`; callers recover it via `WorldModelsTcp_tcpOracle` + oracle-frame equalities. Harmless asymmetry. | Optionally add the conjunct for symmetry. | 1 |

---

## 2. Capstone: `ioResumeLoop_error_sound` (IoResumeErrorSound.lean:706)

| Hypothesis | Class | Evidence | Suggested action | Sev |
|---|---|---|---|---|
| `hnetWF`, `hGlSbelt`, `hwm : WorldModels`, `hwmTcp` | LB (here) | All genuinely consumed: the error loop's glueless sub-resolution arm invokes the full `ioResumeLoop_sound` (line 908) and so needs the whole pack. Same discharge status as §1. | as §1 | — |
| `htm : αTime state.now = now` | LB | Time-abstraction pin; supplied `rfl`-like by callers. | none | 1 |
| `hp : CachePackNC state.resources.cache state.now` | **DS** (class-IN hardcode) | `CachePackNC` (L12) bundles `CacheNegWf c (1 : BitVec 16)` — class IN hardcoded as the literal `1` (see `CachePackNC.of_parts` L21). Matches the recorded "per-class CacheNegWf lift" follow-up. | Lift to per-class when the class-IN scope is lifted. | 2 |
| `hCap`, `hclock`, `hGlProv`, `hGlBelt` | LB | As in §1. | none | 1 |
| `hsnA : ∃ qn, αName sname = some qn`, `hqmA : … isSome` | LB | Weakened (isSome-only) forms of §1's `hqm`; needed for `αQuery_buildSubQuery_exists`. | none | 1 |
| **Conclusion** `CachePackNC cout ∧ size ≤ capacity` | **OS (name over-promises)** | The name says *error soundness*, the statement delivers only *cache-invariant preservation on the error path*. The semantic claim for errors (servFail justified) lives in the CALLER (`resolveWithIO_error_sound`, ResolveWithIOSound.lean:3449) and is discharged there by the **unconditional** `gaveUp/loopDetected/exhausted_hasVerdictAt` constructors keyed on the error *string* (`by_cases hm1 : msg = "cname chain too long" …`). So the entire error family's RFC content reduces to the unguarded give-up rule (see §1 OS row 1). | Rename or strengthen; primary fix is guarding the model's `gaveUp`. | 3 |

---

## 3. `tcpSpoofReply_of_honest` (IoResumeSound.lean:3440)

| Hypothesis | Class | Evidence | Suggested action | Sev |
|---|---|---|---|---|
| `hwmTcp` | UR (inherits §1 TCP-honesty) | This lemma is the honest→spoof-arm coercion: it *realizes* the UDP-shaped `SpoofReply` disjunct from an honest TCP reply, i.e. it exists precisely because the TCP oracle is honest-only. | as §1 hwmTcp | 4 (same finding) |
| `hO/hdec/hsan/hacc/hαq` | LB | Acceptance-pipeline conditions; mirror the impl's actual checks. | none | 1 |
| `htc0 : (resp.header.tc == 1) = false` | LB | TCP replies are used only when untruncated; enforced at the call sites (`htc0` from the loop's guard). | none | 1 |
| `hreachR : linkReach net ns ra ra = true` | LB | Self-reachability; discharged internally at all 4 call sites via `WorldNetwork.reach_self`. Could be dropped by inlining `reach_self`, but it keeps the lemma net-generic. | optional cleanup | 1 |
| `hnetWF` | LB | Feeds `referral_bailiwick_desc`. | none | 1 |

---

## 4. Oracle-shape findings surfaced while tracing (definitions consumed by this slice)

These are not hypotheses *of* theorems in the slice, but every theorem in the slice quantifies over
them; W2 should own them.

| Item | Class | Evidence | Suggested action | Sev |
|---|---|---|---|---|
| `WorldModels`/`WorldModelsTcp` never constructed | LB (boundary) / UR (unwitnessed) | `grep -rn WorldModels` over `VeriDNS/`: only 6 proof files, always hypothesis/conclusion-threading (`WorldModels_oracle`, `WorldModelsTcp_tcpOracle` are frame transports, not constructions). No `⊢ WorldModels … concreteWorld` exists, not even for a one-server toy net — so satisfiability of the whole capstone stack is never machine-checked. (The total-sim T-track closed the *shape* obligations; a witness world would close satisfiability.) | W2: one small witness instance (`WorldModels net₀ … (worldOf net₀)`) as a sanity pin; doubles as a vacuity guard. | 4 |
| `SpoofReply` structural conjuncts constrain the attacker | LB-with-caveat | SpoofReply (NetworkSim.lean:64) requires spoofed replies to have parseable/abstractable RRs and, in the referral sub-case, canonical NS rdata + `delegationMatchCount` agreement + bailiwick. These are fine *iff* they are implied by decode/sanitize/accept for every acceptable byte-string (the T-track direction); the known residue is the spoofed-referral n-canonicity boundary (recorded 2026-06-29 note). Any conjunct NOT implied by acceptance narrows the adversary unrealistically. | W2: per-conjunct derivability check of the SpoofReply referral block from decode facts; the ones that fail become model obligations (this is the recorded trailing-bytes item). | 3 |

---

## 5. Bulk classification — remaining theorems in the slice

Mechanical scan verdict: **all named hypotheses referenced in their proof bodies** (158 theorems,
1 zero-ref pair resolved as omega-consumed). Families, with class:

| Family (representatives, lines) | Hypotheses | Class | Notes |
|---|---|---|---|
| TTL/absorb frame lemmas: `groupMinTtl_le_seed` L12, `normRaws_*` L16/27, `*_absorb` L58–140, `cout_exports_bound` L686, `storeNegative_records_package` L729 | cache invariants + parse-validity of absorbed raws | LB | validity premises are supplied by WorldModels conjuncts at the call sites |
| `uint32_add_ttl_toNat` L214 | `hb : t ≤ 604800`, `hc : now+604800 < 2^32` | LB (UU-scan false positive) | zero textual refs but both consumed by the two `by omega` closings; not removable |
| α-bridge micro-lemmas: `αSecF_*` L229–241, `implNsCutF_*` L250–256, `findSome?_ns_align` L296, `referralCutRaw_αName` L364, `αSection_*` L1089/1818 | parse/canonicity of section bytes | LB | |
| CNAME freshness/chase: `CnameChainModels_congr` L434, `visited_target_fresh` L444, `cname_target_fresh` L460, `covers_cname_false_of_chase` L472, `localAnswer_chase_peel` L1114, `cname_link_facts` L1654, `afterResume_cname_*` L1833–2102, `afterResume_cname_continue_inv` L2462 | chain-models pack + canonicity + `t ≠ RRType.cname` guards | LB | `htne : t ≠ cname` is a case-split guard, not a scope limit (the cname case has its own arm) |
| Negative-cache: `CacheNegWf_*` L610–729, `storeNegative_negWriteRefines_prepend` L799, `storeProbeNegative_*` L858/908, `lookupNxdomain_none_negHitNx_false` L926, `lookupNegative_none_negHit_false` L979, `lookupNegative_negHit_negResponse` L3041 | `CacheNegWf`, canonicity pairs, `hrc : rc = nameError ∨ noError` | LB | rcode disjunction mirrors RFC 2308 cacheable rcodes |
| Redundant canonicity pairs: `lookupNegative_negHit_negResponse` L3041, `lookupAnswerable_hit_bridge` L3092, `hit_nil_of_lookupAnswerable_empty` L587, `cname_link_facts` L1654 | both `hα : αName sname = some qn` AND `hcan : sname = labelsToWireFormatGo qn` | UU (redundant-in-principle) | with 0<size validity, `hα` follows from `hcan` via `αName_labelsToWireFormat` (Refinement.lean:799); where only `size ≤ 63` is carried, `hα` additionally supplies label-positivity, so dropping it needs the stronger validity form. Harmless; dedup only if touching anyway. Sev 1 |
| QNAME-min plumbing: `buildSubQuery_inv` L1470, `subQuestion_*` L1486/1494, `probeRoundB_facts` L1535, `αQuery_buildSubQuery_probe` L1609, `αQuery_buildSubQuery_exists` (err L675) | probe/full round guards | LB | |
| SLIST/GluelessProv frames: L2163–2328 (`GluelessProv_*`, `addressTargets_*`, `extractNsNames_canonical`, `walkNs_names_canonical`) | subset/canonicity | LB | `GluelessProv_fromNsWithGlueAll_of_canonical` + `walkNs_names_canonical` are what make hGlProv self-sustaining; only the SBELT seed lacks a witness (§1) |
| Loop structural invariants: `step_nowOk` L1901, `loop_done_now` L1925, `resume_done_now` L1951, `ioResumeLoop_ok_lastQuery` L2679, `resolve_mkAddressQuery_paused_inv` L2823, `loop_checkAnswer_miss_struct` L2390, `localAnswer_miss_ident_or_fresh` L2348 | step-shape equalities | LB | |
| AnswerWriteWf algebra: L3263–3411 (`answerWriteWf_*`, `localAnswer_chain_*`, `respWriteWf_of_answerWriteWf`) | wf pack + provenance | LB | |
| glueless recheck: `gluelessRecheck_cases` L2983, `extractAAddress_model_a` L2913, `foldl_ipMinOpt_some` L2955, `addressOf_isSome_of_mem_a` L2966 | membership/extraction | LB | |
| ErrorSound helpers: `CachePackNC.of_parts` L21 (class-IN hardcode → §2), `cred*_tier` L28–48 (no hyps), `cachePackNC_write/touchKeys/boundLru` L59–103, `answerWriteWf_ownerRaws/bailiwickRaws` L125/130, `cnameToChase_target_abs` L137, `localAnswer_miss_sname_abs` L160, `step_carry` L207, `dropIfBizarre_*` L440/452, `resolveLoop_paused_carry` L462, `afterResume_error_cache` L514, `afterResume_continue_carry` L526, `sectionWriteWf_of_wire` L589, `respPackFacts_of_wire` L616 | frames + wire-validity | LB | `hcred` 4-way tier disjunction in `cachePackNC_write` is exhaustive over the impl's three cred producers (`cred*_tier`) — fair |

---

## 6. Feed-forward summary

**To W2 (assumed premises → model obligations):**
1. `WorldModelsTcp` honest-only arm (sev 4) — on-path TCP attacker outside all capstones; documented
   only in docs/tcp-plan.md decision 5, invisible at the theorems.
2. No `WorldModels`/`WorldModelsTcp` witness world anywhere (sev 4) — satisfiability unpinned.
3. `GluelessProv (mkSbelt rootServers)` missing lemma (sev 4, cheap).
4. `net.WF` boundary premise (sev 3) — pair with the witness world.
5. SpoofReply referral-block derivability audit (sev 3) — recorded trailing-bytes boundary.

**To W3 (over-scoped conclusions → adequacy duals / strengthenings):**
1. Unconditional model `gaveUp` makes every servFail arm (ok-capstone servFail case, entire
   `ioResumeLoop_error_sound` family via its caller) verdict-content-free (sev 4).
2. `gluelessNs_anchor_witness` fabricated-cprov connector — glueless verdicts not anchored to the
   real cache (sev 4, recorded fork-(b)).
3. `ioResumeLoop_error_sound` name/statement mismatch (sev 3).

**Deletions:** none — zero removable hypotheses found in the slice.

**Documented scope limits re-confirmed (no action beyond the existing follow-up list):**
`q.qclass = .in` / `qu.qtype.toNat ≠ 255` / `q.qtype ≠ QType.star` gates (RFC 3597 T5 scope keeps),
`CachePackNC`'s hardcoded class-IN `CacheNegWf`, TCP spoof-free arm (plan-documented).
