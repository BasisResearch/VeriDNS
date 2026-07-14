# Assurance roadmap: drive the residual bug surface down to kernel + FFI

**North star.** A bug can only exist where a theorem doesn't pin the implementation to an
RFC-faithful model. The meta-lesson: *a theorem guarantees exactly its statement* — bugs hide in
(i) hypotheses assumed away, (ii) branches not proven, (iii) the model being weaker than the RFC,
(iv) the TCB. Close (i)–(iii); shrink (iv) to the irreducible kernel + FFI.

Audit done 2026-06-27: **no `sorry`, no custom `axiom`** anywhere in `Spec/`, `Proof/`, `Impl/`.
Residual `native_decide` ×3 in `Proof/Primitives.lean` (trusts the compiler — TCB). FFI `opaque`s in
`Impl/UdpSocket.lean` (irreducible TCB). Everything else is the four gap-classes below.

**2026-07-10 addendum — QNAME minimisation (deferred item 6) landed end-to-end** (RFC 9156 strict
mode + RFC 8020 subtree denial; `docs/qname-minimisation-plan.md`). New assurance surface: the
egress side of the loop is now itself pinned — `ioResumeLoop_sent_minimised`
(`Proof/SentMinimised.lean`) proves over the free-monad program tree that in every world the loop's
only egress is the minimised `buildSubQuery` question (CI-ancestor of the session name, exactly
`revealed` labels at QTYPE=A on probe rounds), i.e. a "sends more than it should" bug is a compile
error, the same posture the referral guard gave the accept side. Known-and-documented residuals:
RFC 8020 §3.2 read side (descendant negative lookup) not implemented — siblings under a denied
ancestor re-probe (liveness, not soundness); probe rounds have lower 0x20 entropy (fewer letters)
with id/port entropy unchanged.

---

## Inventory of open gaps (the "not yet proven / assumed away" list)

### GAP 1 — unproven branches (oracle premises in the forward simulation)

> **STATUS 2026-07-11 — the C track (total simulation) is CLOSED.** The description below
> is the 2026-06-27 snapshot. What landed since: the C3 induction as `ioResumeLoop_sound`
> (2026-07-04, in `lake build`), the client boundary as `serveDatagram_verdict_sound`, and
> the totality closure per `docs/total-simulation-plan.md` — T0 error recon, T1
> (`Resolves.gaveUp`/`loopDetected` + `ioResumeLoop_error_sound`: every `.error` outcome
> verdict-justified), T2 (`serveDatagram_total`: client-boundary hypotheses discharged),
> T3 (`serveSeq_total`: cold-start serve-sequence corollary), T4a (honest CNAME arms cite
> `answerCname`; T4b residuals recorded as follow-ups in the plan), T5 (RFC 3597
> unknown-type carrier: `αType` total, qtype scope lifted — remaining scope keeps are
> deliberate: no ANY, class IN). The last open item, **D2 (hhit completeness)**, CLOSED
> 2026-07-11: `resolveWithIO_cacheHit_simulates` no longer takes the served-set equality
> `hhit` as a hypothesis — it derives it via `hhit_of_invariants` from the impl-level cache
> well-formedness invariants (`hwf`/`hcanon`/`hused`/`hwfrr`) and the query-name canonicity
> facts, all discharged elsewhere by `store`/`sweep` preservation and the client boundary.
> **This gap class has no open items**; recorded follow-ups (T4b residuals, give-up items
> 1–4, 7-level credibility ranking) live in `docs/total-simulation-plan.md` and below.

The 2026-06-27 snapshot: `resolveWithIO_simulates` (`Proof/Refinement.lean`) is **not total**. Impl-connected branches:
`negHit` (×2), `cacheHit` (cache paths), `answer` (network, via `NetworkSim.networkAnswer_simulates`
+ FreeIO `run_resolveWithIO_networkAnswer`). **NOT impl-connected** (supplied as the `HasVerdict`
oracle disjunct): `refer`, `answerCname`, `cacheCname`, `timeout`, `skipMissing`, `referNoGlue`,
`rejectSpoof`, `exhausted`. The `*_hasVerdict` lemmas exist for all of them but only state the model
side; the impl loop is not yet shown to *reach* them. **This is the class that hid the referral
cache-poisoning bug.**

### GAP 2 — assumed-away hypotheses
- ~~`resolveWithIO_cacheHit_simulates`: `hhit` (served-set equality) assumed.~~ **DISCHARGED
  (2026-06-27)** — `hhit_of_invariants` *proves* the exact `hhit` statement
  (`αSection ((lookupAnswerable).map rrBytes) = Cache.hit`) from the cache well-formedness invariants,
  via `lookupAnswerable_αRR_eq_hit` (the full set+list equality, kernel-clean) + `αSection_map_rrBytes_wf`
  (codec round-trip). No longer an oracle premise; the cache-hit read path refines unconditionally.
- `resolveWithIO_negHit_nodata_simulates`: `negHitNx = false`, `rc = noError` assumed.
- `NameTree.step_sound` / `CacheAgrees`: `ResponseConsistent T resp` assumed (cache stays truthful
  *only if the response is truthful*). NOTE: the **security** anti-poison
  (`cacheWrite_pos_in_bailiwick`, now generic over any section) does **not** assume this — it holds
  for *arbitrary adversarial* `resp`. So the dangerous direction is already adversarial-proven; the
  `ResponseConsistent` hypothesis only weakens the *cooperative* agreement property.
- `WorldNetwork.answer_model_realizable` / `NetworkSim.networkAnswer_simulates`: well-formedness
  (`howner`, `hmatch`, `hfit`) assumed.

### GAP 3 — model weaker than the RFC
- ~~**In-bailiwick-glue rule** not enforced~~ **CLOSED (2026-06-27)**: BOTH sides now filter. Impl
  (`Resolver.lean` SLIST glue via `bailiwickRaws (referralCutRaw …)`, D1-impl) AND model
  (`glueAddresses` now requires `isAncestor (referralCut ref) r.owner` on every glue owner, D1-model).
  Locked by the adversarial regression theorem `out_of_bailiwick_glue_rejected` (a referral naming an
  out-of-bailiwick `evil.com` NS with matching glue → its address is dropped). The cache absorb was
  already bailiwick-filtered (`absorbBailiwick`). So the glue-poisoning vector is now closed on *both*
  the write path (cache) and the SLIST-seed path (model + impl).
- ~~**Credibility granularity**: model `Cred` 4-tier vs impl `Trustworthiness.toCode` 7-level.~~
  **CLOSED (2026-06-27)** — `cred_ranking_faithful_for_resolver`: the 4-tier collapse is *lossless for
  the resolver*. The resolver only ever **assigns** credibilities via
  `credAnswer`/`credAuthority`/`credAdditional` (`cred_used_*`), yielding exactly the 4-element set
  `{authoritativeSection, authoritySection, sectionNonauthoritative, additionalAuthoritative}`; the 3
  finer levels (`primaryZone`/`zoneTransfer`/`gluePrimary`) are authoritative-server-only and never
  produced. On that 4-set `αCred` is an order-reversing bijection onto `Cred.rank` (`αCred_order_used`),
  so for *any* credibilities the resolver can assign the model's coarse rank order coincides with the
  impl's full `toCode` order. The model is not weaker than the RFC for the resolver's behaviour. So
  **GAP 3 is fully closed**: §5.4.1 floor ✓, in-bailiwick-glue ✓ (both sides), `hhit` ✓ (discharged
  theorem), credibility ranking ✓.

### GAP 4 — the TCB  (status: substantially shrunk 2026-06-27)
- `Impl/UdpSocket.lean` FFI `opaque`s (sockets, clock, RNG) — **irreducible** (the real I/O boundary).
- ~~`native_decide` ×3~~ **ELIMINATED**: the `example` → `decide` (kernel-checked); the two
  `∀ BitVec 16` bit-identities → `bv_decide`. This removes `Lean.ofReduceBool`/`trustCompiler`
  (whole-compiler trust) from the codebase entirely.
- Wire codec round-trip: **already proven** — `Proof.Message.decode_encode_of_decode`
  (`decode buf = .ok m → decode (encode m) = .ok m`: encode faithfully represents any decodable
  message). Its only non-standard axioms are `bv_decide`'s SAT-certificate axioms
  (`*._native.bv_decide.ax_*`) in the byte/bit layer — narrower than `native_decide` and already
  pervasive in the codec proofs.
- **Key fact:** the *semantic core* — `resolveWithIO_simulates`, `cacheWrite_pos_in_bailiwick`,
  `referralCacheWrite_pos_in_bailiwick`, `answer_model_realizable`, the negHit/cacheHit branches —
  is **fully kernel-clean** (`[propext, Classical.choice, Quot.sound]` only; no `bv_decide`, no
  compiler trust). So `bv_decide`'s SAT trust lives *only* in the low-level codec, and the
  resolution-correctness results don't depend on it. Residual TCB = FFI + (codec's bv_decide SAT
  certificate) + (model ≈ RFC, human judgment).

---

## Chunked plan (each chunk compiles, stays axiom-clean)

- **B1 (GAP 2, security — DONE):** adversarial cache anti-poison. `cacheWrite_pos_in_bailiwick`
  generalised over any section + `referralCacheWrite_pos_in_bailiwick` (the referral double-write):
  for *arbitrary adversarial `resp`*, every record entering the cache (answer or referral
  authority/additional) is pre-existing or in-bailiwick. Axiom-clean. Closes the cache-poisoning
  class for all write paths.
- **E1 (GAP 4 — DONE):** `native_decide` eliminated (→ `decide`/`bv_decide`); codec round-trip
  `decode_encode_of_decode` already proven; semantic core confirmed kernel-clean.
> **C-track CLOSED 2026-07-11** — C1/C2/C2.5/C3 all landed (C3 = `ioResumeLoop_sound`,
> 2026-07-04); the totality closure on top (error verdicts, client-boundary discharge,
> serve-sequence corollary, honest-arm upgrades, RFC 3597 qtype lift) is
> `docs/total-simulation-plan.md` T0–T5, all complete. The C entries below are the
> historical working notes.

- **C1 (GAP 1):** define `WorldModels net ns resolverAddr w` — the environment-consistency relation
  (the World oracle's replies are what the model network would send). This is the *legitimate*
  assumption (you can't prove the network; you assume it behaves per the model).
- **C2 (GAP 1) — terminal shapes DONE (4/4):** per-branch model-realizability (`WorldNetwork.lean`).
  ALL FOUR purely-terminal (non-recursive) response shapes done: `answer_model_realizable`,
  `nxdomain_model_realizable`, `nodata_model_realizable` (+ child-name lemmas `nameEq_child_false`,
  `isAncestor_child`, and zone helpers `wildcardSynth_empty/_ent`, `isEmptyNonTerminal_empty/_ent`,
  `noDataAuthority_ent`, etc.), and **`exhausted_model_realizable`** (empty-SLIST → SERVFAIL, RFC 1034
  §5.3.3; parametric over any `net`/`ns` since `Resolves.exhausted` is a base case). TODO: the
  RECURSIVE constructors — `refer` (the bug's branch), `answerCname`/`cacheCname`, and the recursive-
  premise terminals `timeout`/`skipMissing`/`rejectSpoof`/`referNoGlue` (each carries an `ih`/`hrec`) —
  need the loop induction, i.e. C3. (Impl-side connection for `exhausted`'s empty-SLIST SERVFAIL path
  also pending — distinct from the `run_ioResumeLoop_fuel_zero` `Except.error` fuel cap.)
- **C2.5 (GAP 1) — single-hop totality DONE:** `NetworkSim.networkAnswer_simulates` +
  **`networkNxdomain_simulates`** join the FreeIO `Prog.run` (impl side) with the model-realizability
  (model side) — for a single-server answer/NXDOMAIN the verdict is *derived* (no `HasVerdict` oracle
  premise), only the env-consistency (well-formedness/fit) of that one reply is assumed.
- **C3 (GAP 1) — the recursive frontier (remaining):** inductive composition over `ioResumeLoop` for
  the *multi-hop* paths (referral chains, CNAME chains) → `resolveWithIO_total`. Needs the model's
  recursive `refer`/`answerCname`/`cacheCname` derivations threaded through the loop induction (the
  FreeIO `run_ioResumeLoop_{retryThenAnswer,bizarre_recurses}` are the impl-side recursion). This is
  the culminating theorem; single-hop is done, multi-hop recursion is the open work.
  - **C3-prep DONE:** the recursive step lemmas (`*_hasVerdict`, taking raw `Resolves`) all exist, and
    now their **HasVerdict-threading wrappers** too — `refer_hasVerdict_hv`, `timeout_hasVerdict_hv`,
    `skipMissing_hasVerdict_hv`, `rejectSpoof_hasVerdict_hv` (the output-preserving recursive branches).
    These bridge "IH yields a `HasVerdict` (trace existentially closed)" to "step lemma needs a named
    `Resolves`", so the induction composes uniformly with no oracle premise per step. Axiom-clean.
    Remaining for C3: the induction itself (well-founded over `ioResumeLoop` fuel) discharging each
    branch's model premises (`hfind`/`hans`/`htrans`/`hwire`/…) from the impl's received datagram —
    i.e. the C1 `WorldModels` environment-consistency relation + the per-branch premise discharge. The
    CNAME branches (verdict-transforming) and `referNoGlue` (double sub-resolution) thread directly in
    the induction rather than via a uniform wrapper.
  - **DECISION (2026-06-27): Option 3 — full transport incl. adversary** (user-chosen). `WorldModels`
    models the whole network including loss, partition, and off-path spoofing — the most faithful
    formulation, fitting the security focus (the referral bug was a poisoning attack). The induction
    must discharge spoof→`rejectSpoof` and loss→`timeout` branches. **C1 COMPLETE (2026-06-27):**
    (a) `αQuery` (Format → model `Query`) + `αQuery_fields`; (b) `byteAddrToModel` (oracle 6-byte key →
    model `String` addr) + `byteAddrToModel_ipv4ToAddr` (consistency with `IPv4.toDotted`); (c) the
    **`WorldModels` Prop** (`Proof/NetworkSim.lean`, Option-3 shape: for every accepted oracle reply,
    `∃ origin reply, Transit (linkReach …) origin ra reply (some reply) ∧ accepts … ∧ RespAgree … ∧
    (honest `serverAt`+`ServerAnswers`+`OnWire` ∨ off-path `origin ≠ byteAddrToModel ab`)`). All
    typecheck, build green. **REMAINING = C3 only:** the well-founded `ioResumeLoop` induction that
    instantiates `WorldModels` per hop, classifies the reply (answer/refer/cname/retry) as the impl's
    `analyzeResponse` does, and applies the matching `*_hasVerdict_hv` wrapper / terminal realizability
    to the IH → `resolveWithIO_total`. This is the multi-week culminating theorem; all its inputs (step
    wrappers, single-hop totality, terminal realizabilities 4/4, and now C1) are in place.
  - **C3 concrete decomposition (the remaining work, in dependency order).** The `ioResumeLoop` is
    `termination_by (depth, fuel)` with branches: fuel-0/deadline → `.error`; no-server-with-address →
    glueless sub-resolve+recurse `(depth', fuel')` *or* `.error`; `some (entry, ipAddr)` → send, then
    `upstreamResp`: none → recurse `(depth, fuel')` [timeout]; `acceptResponse = none` → recurse
    [rejectSpoof]; `unfollowableDelegation` → recurse [bailiwick-drop]; else `afterResume`:
    `.finished result` → done; `.continue` → recurse [refer/cname]. The proof breaks into:
    (i) **wire construction** — `honest_wire_premises` **DONE** (`Proof/NetworkSim.lean`): from server
    response + reachability, build `Transit.deliver` + `accepts` (via `accepts_reply`) + `OnWire.fromServer`
    for `replyDatagram (queryDatagram …) honest`; shared by all honest branches;
    (ii) **per-branch classifiers** mapping the impl's `afterResume`/`acceptResponse`/`forwardQuery`
    outcome to the matching model constructor premises — **answer (honest, non-referral) →
    `answer_classifier` DONE**; **referral (the bug's branch) → `referral_classifier` DONE** (composes
    `honest_wire_premises` + `refer_hasVerdict_hv`); the retry branches are *already* classifiers — the
    `*_hasVerdict_hv` wrappers: `upstreamResp=none` → `timeout_hasVerdict_hv`, `acceptResponse=none` →
    `rejectSpoof_hasVerdict_hv`, no-server → `skipMissing_hasVerdict_hv`, empty-SLIST → `exhausted_*`.
    **cname → `cname_classifier` DONE** (+ `answerCname_hasVerdict_hv`, the verdict-transforming thread:
    `v.answer = cn :: vsub.answer`). So **part (ii) is COMPLETE — every branch classifier proven**:
    answer, referral (bug's branch), cname, timeout, rejectSpoof, skipMissing/glueless, exhausted, all
    axiom-clean. (iii) the **`(depth, fuel)` well-founded induction** threading the IH (a `HasVerdict`
    for the recursive `ioResumeLoop` call) through the classified branch → `resolveWithIO_total`.
    **C3 progress (2026-06-27): parts (i) + (ii) COMPLETE — wire construction + ALL per-branch
    classifiers committed axiom-clean.** Realizability-discharge started: `answer_records_match` proves
    the answer realizability's assumed `howner`/`hmatch` from the model structure (`recordsAt` filters by
    owner). **ONLY part (iii), the fuel induction assembly, remains** — and it is the genuine remaining
    unit: a well-founded induction over the *executable* `ioResumeLoop` (interpreted via FreeIO
    `Prog.run`) that, at each step, connects the impl operation (`forwardQuery`/`acceptResponse`/
    `afterResume`) to `WorldModels`, dispatches to the proven branch classifier, and threads the
    recursive call's `HasVerdict` as IH. This generalizes the concrete path-lemmas
    (`run_ioResumeLoop_{answer,nxdomain,retryThenAnswer,bizarre_recurses}`) into one recursion. It is a
    sustained multi-day/week proof — NOT a single committable lemma — and is the sole barrier between the
    proven classifier set and the top-level `resolveWithIO_total` that eliminates the network oracle
    premise. Every input it consumes is now proven.
  - **C3 induction machinery STARTED (2026-06-27): per-branch FreeIO `Prog.run` reductions.** Beyond the
    model-side classifiers, the induction needs impl-side reduction lemmas (one loop iteration `Prog.run`-
    reduces to the recursive call) per branch. Existing: `run_ioResumeLoop_{answer,nxdomain}` (terminals),
    `run_ioResumeLoop_bizarre_recurses` (servfail/unclassifiable retry). **NEW (this turn):
    `run_ioResumeLoop_{timeout,rejectSpoof,unfollowable}`** — the **entire retry/drop family** is now
    reduced at the `Prog.run` level: oracle-drop (`horacle = none`) → `timeout`; accepted-but-fails-
    `acceptResponse` → `rejectSpoof`; unfollowable/out-of-bailiwick delegation → drop+retry. Each
    `Prog.run (m+k) (loop (fuel'+1)) = Prog.run m (loop fuel' (markQueried state))`, the matching
    `Resolves` retry step. Plus `Prog`-stepping helpers `run_forwardQuery_bind_eq_none` /
    `run_round_bind_eq_none`. All axiom-clean. **FreeIO reduction layer now: terminals (answer/nxdomain)
    ✓, bizarre ✓, timeout ✓, rejectSpoof ✓, unfollowable ✓, AND the state-changing
    `run_ioResumeLoop_continue` ✓** (`afterResume .continue` → refer/cname — generic over the absorbed
    state `st`, covering both refer (bailiwick-filtered cache + glue SLIST) and cname (chased target); the
    model side supplies the concrete `st`). **So EVERY send-path branch is now reduced.** TODO: only the
    **glueless** branch (`bestWithAddress = none` + address-target ⟹ recursive NS-address sub-resolution →
    `referNoGlue`) — its monadic SLIST-mutation step is now done (`run_gluelessUpdatedSlist_resolved`:
    `extractAAddress = some addr` ⟹ `gluelessUpdatedSlist` reduces to `slist.addAddress nsName addr`),
    remaining = composing it with the `bestWithAddress = none` stepping + the nested sub-resolution +
    recurse. The deadline/`.error` terminals are **vacuous for the `.ok` premise** (`Except.ok ≠ .error`),
    so not needed as lemmas. Then the **fuel induction** composes {reductions × classifiers × WorldModels}
    by well-founded recursion on `(depth, fuel)`. Reduction layer: 5 reductions + 3 helpers committed this
    session (timeout/rejectSpoof/unfollowable/continue + gluelessUpdatedSlist step), all axiom-clean,
    built bottom-up.
  - **C3 FreeIO REDUCTION LAYER COMPLETE (2026-06-27): EVERY impl branch has a `Prog.run` reduction.**
    Now also **`run_ioResumeLoop_glueless_done`** ✓ (the glueless/`referNoGlue` branch: `bestWithAddress
    = none` + glueless NS target resolving in one shot ⟹ recurse at `depth'` with `addAddress`), composed
    from `Prog.bind_assoc` + `run_gluelessUpdatedSlist_resolved{,_bind}` + nested-match reduction (`heq`
    discharged by `htargets`). **So the impl-side half of the fuel induction is DONE.** REMAINING for
    `resolveWithIO_total`: ONLY the `(depth, fuel)` well-founded induction composing the committed
    {reductions × classifiers × WorldModels} — every input is now proven and committed.
  - **CRITICAL-PATH BLOCKER PINNED (2026-06-27, from tracing the induction's actual per-branch
    obligations end-to-end).** The remaining `resolveWithIO_total` work is NOT uniformly "compose the
    reductions"; it decomposes into two very different-sized pieces:
    (A) *the control-flow skeleton* — strong induction on `fuel` (with `depth` in the lex measure),
        casing the run hypothesis `Prog.run K (loop) w = some (.ok resp, w')` on each runtime decision
        (`clock<deadline`, `bestWithAddress`, oracle result, `acceptResponse`, `unfollowableDelegationB`,
        `afterResume`), each error terminal excluded by `.ok ≠ .error`. The `'`-suffixed `∀ m` reduction
        form (cf. `run_ioResumeLoop_bizarre_recurses'`) is what the `K = m + k` fuel-threading needs, so
        the reductions still lacking a `∀ m` variant (timeout/rejectSpoof/unfollowable/continue/glueless)
        each need one. Mechanical, ~1–2 days.
    (B) **the actual bulk — the abstraction/mutation COMMUTATION lemmas** that discharge the classifiers'
        cache/slist premises and prove the model state is *preserved* across each recursive hop. The
        `refer` step needs `αCache (afterResume-absorbed cache) = c.absorb now (absorbBailiwick …)
        (referralCut ref)` and `αSlist (glue-updated slist) = sortByRtt (glueEntries rttOf ref)`; the
        glueless step needs the `addAddress` analogue; the cname step the `c.absorb … serverBailiwick`
        analogue. **These "α commutes with the impl mutation, landing exactly on the model's update"
        lemmas are the hard, still-unwritten core** — they are where the bailiwick-safe referral fix is
        actually re-proven to match the model, and they dwarf the skeleton. This (B) is the multi-week
        residue; (A) without (B) cannot discharge a single recursive classifier premise. The keystone
        `StateModels` invariant (cache=αCache, sname/stype/sclass→q, now=αTime, WorldModels w, slist↔
        addressed servers, cache-miss at head) exists only on paper; writing it is gated on (B)'s shape.
  - **(B) RE-ROUTED — the exact `αCache (mutation) = c.absorb …` equality is FALSE (2026-06-27, from
    reading `storeChecked`/`store` vs `Cache.insert`).** The model `Cache.insert` is **pure prepend**
    (`⟨r,now,cred⟩ :: pos` if `cacheable`) — append-only; the §5.4.1 max-credibility gate is applied at
    **read** time (the per-key-max filter in `hit`/`served`). The impl `storeChecked` instead gates at
    **write** time: it SKIPS the write when a fresher strictly-higher-cred same-key record exists
    (`betterExists`), and `store` itself FILTERS OUT same-key records before adding (replace semantics).
    So impl and model caches **diverge in raw content** and coincide **only on the served (`hit`) set**
    (the read-time max in the model discards exactly what the impl declined to write). CONSEQUENCE: the
    per-hop bridge must be stated at the **served level**, not raw `αCache` equality:
    `ServedEquiv c₁ c₂ := ∀ t q, c₁.hit t q = c₂.hit t q ∧ c₁.negHit … = … ∧ c₁.negHitNx … = … ∧
    c₁.cnameAt … = c₂.cnameAt …` (the four predicates through which `Resolves` ever consults a cache).
    The NEW keystone (B) needs is a **`Resolves`/`HasVerdict` congruence under `ServedEquiv`** (the cache
    argument is replaceable by any served-equivalent cache — provable because the cache enters `Resolves`
    only via those four read predicates, and `absorb`/`absorbNeg` preserve `ServedEquiv` since they
    append the same records). Then the per-hop obligation becomes
    `ServedEquiv (αCache (storeChecked-fold of bailiwickRaws)) ((αCache c).absorb now bw (αResp ref))`
    — provable via the ALREADY-DONE per-key-max hhit machinery (`lookupAnswerable_αRR_eq_hit`,
    `maxCredForKey_of_served_maximal`), since both sides compute the same per-key-max served set. This
    connects (B) to proven work and makes it tractable: `StateModels` carries `ServedEquiv` (served sets
    agree), the soundness induction threads `ServedEquiv` through each hop via the congruence, and the
    classifiers' exact-`c.absorb` cache argument is reached by congruence-rewriting, not raw equality.
    The congruence over the ~14 `Resolves` constructors is the remaining large-but-tractable unit.
  - **(B) REFINED AGAIN — even `served`-equality is NOT `absorb`-stable; the stable invariant is
    per-key-max-RANK among ALL matching (2026-06-27, with counterexample).** Worked the `absorb`-
    stability obligation to the bottom. `Cache.served = matching.filter (usable ∧ per-key-max-rank)`
    where the per-key max is taken over **all** `matching` (incl. non-usable) and `usable` is filtered
    *after* — so a non-usable top-rank record SUPPRESSES usable lower-rank ones (served = ∅ at that key).
    COUNTEREXAMPLE that kills `served`-equality as the threaded relation: `c` = key k with usable `r`@
    cred `authority`(2); `c'` = same `r`@`authoritative`(3). Both serve `{r}` (sole ⟹ max) so `served`
    AND `hit` agree. `absorb` r2 (same k, cred 2): in `c`, r2 ties max ⟹ served `{r,r2}`; in `c'`, r2 <
    max ⟹ served `{r}`. **Diverge.** So neither `hit`- nor `served`-equality survives `absorb`. The
    genuinely `absorb`-stable invariant must pin, per key, the **max RANK among all matching records
    (usable or not)** — strictly stronger than `served`-equality. WHY the actual threaded pair is still
    fine: the impl (`storeChecked` keeps the true max via `betterExists`/replace) and the model (prepend
    + read-time max) BOTH maintain the genuine per-key max, so for THEM the max-rank agrees by
    construction — but a *general* `ServedEquiv` congruence cannot assume it, so the congruence's
    hypothesis must be the max-rank-level relation, and the per-hop bridge must re-establish max-rank
    agreement (not just served agreement) from the parallel construction. This is the precise core of
    the multi-week (B): define `MatchMaxEquiv c c' := ∀ now q, perKeyMaxRank(matching c now q) =
    perKeyMaxRank(matching c' now q) ∧ neg-preds agree`, prove it `absorb`/`absorbNeg`-stable, prove it
    implies `served`/`hit`/`negHit`/`cnameAt` agreement (so it discharges every cache-dependent
    `Resolves` output), and prove the parallel impl-vs-model construction establishes it per hop via the
    DONE per-key-max hhit machinery. The naive `served`-level plan (two turns of refinement) was the
    wrong relation; THIS is the right one. Saved weeks of attacking an `absorb`-unstable invariant.
  - **(B) READ-SIDE COMMITTED — first real code of the cache-substitution congruence (2026-06-27,
    axiom-clean, build green 270 jobs).** Wrote the correct relation and proved it determines every cache
    read predicate:
    • `Cache.topServed` (NetworkSemantics.lean) — per-key rank-maximal matching records = `served`
      *without* the `usable` filter; the `absorb`-stable level.
    • `Cache.served_eq_topServed_filter` — `served = topServed.filter usable` (gate factorisation; one
      `List.filter_filter`).
    • `Cache.hit_eq_of_topServed_eq` — equal `topServed` ⟹ equal `hit`.
    • `MatchMaxEquiv` (NetworkSim.lean) — the congruence relation: equal `topServed` + equal
      `negHit`/`negHitNx`/`cnameAt` (the four channels the cache reaches `Resolves` through), with
      `refl`/`symm`/`trans`.
    • `MatchMaxEquiv.served` / `MatchMaxEquiv.hit` — the relation discharges the positive-cache reads.
    So the READ-side half of "Resolves is a congruence in its cache argument" is proven. REMAINING (B):
    (1) **`MatchMaxEquiv` `absorb`/`absorbNeg`-stability** — the hard per-key-argmax theorem (records
    strictly below a key's max never re-enter it since `absorb` only raises the max; the max-rank records
    agree by hypothesis). Confirmed TRUE by case analysis (new-max vs tie vs below), now needs the Lean
    proof over the `matching`-filter/argmax structure. (2) the `Resolves`/`HasVerdict` congruence
    induction (~14 ctors) consuming `MatchMaxEquiv` + stability. (3) per-hop establishment of
    `MatchMaxEquiv (αCache storeChecked-fold) ((αCache c).absorb …)` from the hhit per-key-max machinery.
  - **(B) `absorb`-STRUCTURAL BACKBONE COMMITTED (2026-06-27, axiom-clean, build green 270 jobs).**
    `foldl_insert_pos` (a `foldl` of `Cache.insert` prepends a cache-INDEPENDENT list `N` to `pos`),
    `absorb_pos_append` (`∃ N, ∀ c, (c.absorb …).pos = N ++ c.pos` — composes the three section folds),
    `matching_absorb_append` (`∃ M, ∀ c, (c.absorb …).matching now' q = M ++ c.matching now' q` — filter
    distributes over the prepend). So `absorb`-stability of `topServed`-equality is now reduced to ONE
    purely list-combinatorial lemma: **`topOf (M ++ L)` depends on `L` only through `topOf L`** (where
    `topOf L := L.filter (fun e => L.all (¬sameKey ∨ rank e2 ≤ rank e))` and `topServed = topOf ∘
    matching`). Its proof needs the max-achieved sublemma `e2 ∈ L → ∃ em ∈ topOf L, sameKey em e2 ∧
    rank e2 ≤ rank em` (every record is dominated by an in-`topOf` record of its key), then membership
    bookkeeping (`filter_append`; the M-part's domination condition factors through `topOf L`, the
    L-part is `(topOf L).filter (M-domination)`). ~80–150 lines; the single remaining lemma for (B)(1).
  - **(B) COMBINATORIAL HEART COMMITTED (2026-06-27, axiom-clean, build green 270 jobs).** The hard
    mathematical core of the `topOf` congruence is now proven (NetworkSim.lean): `rrtype_eq_of_beq`/
    `rrclass_eq_of_beq` (beq→eq on the non-`LawfulBEq` enums, exhaustive case split + `decide`),
    `cacheRR_sameKey_refl`/`cacheRR_sameKey_trans` (`sameKey` is a key-equivalence), `topOf` +
    `topServed_eq_topOf` (the `topServed = topOf ∘ matching` bridge), `list_has_max_rank` (a non-empty
    `CacheRR` list has a rank-maximal element), and **`exists_dom_in_topOf`** — the max-achieved lemma:
    every record of `L` is dominated at its key by a record in `topOf L`. This is the structural crux
    that makes a key's max rank (hence a future `absorb`'s outcome) a function of `topOf L` alone.
    REMAINING for (B)(1): only the membership-bookkeeping assembly `topOf L = topOf L' → topOf (M ++ L)
    = topOf (M ++ L')` (now a direct consequence of `exists_dom_in_topOf` + `filter_append`), then
    `MatchMaxEquiv`-`absorb`/`absorbNeg`-stability (the `absorbNeg` side is trivial — `absorb` never
    touches `pos`'s max structure for the neg predicates, and `absorbNeg` never touches `pos`). Then
    (B)(2) the `Resolves` congruence induction and (B)(3) per-hop establishment remain.
  - **(B)(1) `topServed` `absorb`-STABILITY PROVEN (2026-06-27, axiom-clean, build green 270 jobs).** The
    `topOf` congruence and its payoff are committed (NetworkSim.lean): `all_eq_topOf_all` (dominating all
    of `L` at a key = dominating all of `topOf L`, from `exists_dom_in_topOf`), `topOf_append_key` +
    **`topOf_append_congr`** (`topOf (M ++ L)` depends on `L` only through `topOf L` — THE congruence),
    and **`topServed_absorb_congr`** (equal `topServed` ⟹ equal `topServed` after `absorb`, composing
    `matching_absorb_append` with the congruence). This is the **positive-cache component of
    `MatchMaxEquiv` `absorb`-stability** — exactly the keystone two earlier turns proved was unavailable
    at the `hit`/`served` level. REMAINING for full `MatchMaxEquiv` stability: (i) `absorb_neg`
    (`absorb` leaves `neg` untouched ⟹ `negHit`/`negHitNx` trivially stable), (ii) `cnameAt`-stability
    under `absorb` (head? of the prepended `pos` — small), (iii) `absorbNeg`-stability (prepends `neg`,
    leaves `pos`, so `topServed` is untouched and `negHit`/`negHitNx` are same-prepend-stable). All
    routine given the structural backbone. Then (B)(2) `Resolves` congruence induction, (B)(3) per-hop
    establishment, then `resolveWithIO_total`. The single hardest piece of the whole capstone — the
    `topOf` congruence — is now DONE.
  - **(B)(1) COMPLETE — full `MatchMaxEquiv` `absorb`/`absorbNeg`-stability PROVEN (2026-06-27, axiom-
    clean, build green 270 jobs).** The remaining read-predicate stability is committed (NetworkSim.lean):
    `negHit_absorb`/`negHitNx_absorb` (via the model's existing `absorb_neg` — `absorb` never touches
    `neg`), `cnameAt_absorb_congr` (`head?` of the `absorb`-prepended `pos`, `filter_append` + nil/cons
    case), `absorbNeg_neg_append` (`absorbNeg` prepends a cache-independent prefix to `neg`),
    `topServed_absorbNeg`/`cnameAt_absorbNeg` (via the model's existing `absorbNeg_pos` — `absorbNeg`
    never touches `pos`), and the assemblies **`MatchMaxEquiv.absorb`** and **`MatchMaxEquiv.absorbNeg`**.
    So `MatchMaxEquiv` is preserved by *every* cache mutation a `Resolves` derivation threads — exactly
    the hypothesis the cache-substitution congruence's recursive cases need. **This was the "multi-week
    core" of (B); it is done.** REMAINING for gap (1): (B)(2) the `Resolves`/`HasVerdict` congruence
    induction (~14 ctors — now a clean induction: each cache read discharged by `MatchMaxEquiv.hit`/
    `.served`/the neg/cname components, each recursive `absorb`/`absorbNeg` step by `MatchMaxEquiv.absorb`/
    `.absorbNeg`), (B)(3) per-hop establishment `MatchMaxEquiv (αCache storeChecked-fold) ((αCache c).
    absorb …)` from the hhit per-key-max machinery, then (A) the `(depth,fuel)` skeleton → `resolveWithIO_total`.
  - **(B)(2) COMPLETE — `Resolves`/`HasVerdict` cache-substitution congruence PROVEN (2026-06-27, axiom-
    clean, build green 270 jobs).** `resolves_cache_congr` (NetworkSim.lean): the full 15-case induction
    over `Resolves` — a `MatchMaxEquiv`-equivalent cache yields the same derivation outcome (same
    trace/path/end-time/**response**) with a `MatchMaxEquiv`-equivalent output cache (the latter needed
    for `referNoGlue`'s second sub-resolution). Each cache read is discharged by a `MatchMaxEquiv`
    component (`hit`/`negHit`/`negHitNx`/`cnameAt`, plus `negTrace_congr`/`negResponse_congr` for the
    `negHit` case's trace/response), each recursive `absorb`/`absorbNeg` step by `MatchMaxEquiv.absorb`/
    `.absorbNeg`. Lifted to **`hasVerdict_cache_congr`** (the form the totality induction consumes: a
    `MatchMaxEquiv`-equivalent cache preserves the verdict). **So (B)(1)+(B)(2) — the entire cache-
    substitution congruence subsystem, repeatedly flagged as the multi-week core of gap (1) — is DONE
    and committed.** REMAINING for gap (1): (B)(3) per-hop establishment `MatchMaxEquiv (αCache
    storeChecked-fold) ((αCache c).absorb …)` (bridge the impl's actual cache mutation to the model's at
    the `topServed` level, via the proven hhit per-key-max machinery), then (A) the `(depth,fuel)`
    well-founded skeleton casing the run + composing the FreeIO reductions × classifiers ×
    `hasVerdict_cache_congr` × `WorldModels` → `resolveWithIO_total`.
  - **(B)(3) GROUNDWORK COMMITTED + crux pinned (2026-06-27, axiom-clean, build green 270 jobs).** The
    per-hop establishment `MatchMaxEquiv (αCache (impl storeChecked-fold)) ((αCache c).absorb …)` is
    proven *record by record*, pairing each impl `storeChecked` write with a model `insert`. Committed the
    model-side templates: `matching_insert_append` (`insert` prepends a cache-independent prefix to
    `matching`) and `topServed_insert_congr` (`topServed`-equality is `insert`-stable) — NetworkSim.lean.
    **The remaining (B)(3) CRUX is the impl side:** `topServed (αCache (DnsCache.storeChecked c rr cred
    now)) = topServed ((αCache c).insert (αTime now) (αCred cred) (αRR rr))` (and the `neg`/`cnameAt`
    components), i.e. the impl `storeChecked` (filter-out same-key-dup + `betterExists` skip, then push)
    abstracts to the model append-only `insert` at the per-key-max (`topServed`) level. This is the
    **write-path analogue of the proven read-path `lookupAnswerable_αRR_eq_hit`** — a fresh multi-lemma
    effort of comparable size, reusing the same per-key-max / `αCacheRR` / `αCred`-order machinery. NOTE:
    (B)(3) is needed ONLY for the cache-*changing* recursive branches (refer/answerCname/referNoGlue); the
    retry family (timeout/rejectSpoof/badResponse/unfollowable/skipMissing) and `cacheCname` recurse on an
    unchanged cache where the bridge is `MatchMaxEquiv.refl`. Then (A) the `(depth,fuel)` skeleton remains.
  - **(B)(3) ORDERING FINDING — `topServed`-as-LIST-equality cannot bridge impl-store vs model-absorb; the
    relation (and `RespAgree`) must be PERMUTATION-based on answers (2026-06-27).** Confirmed structurally:
    `αCache c .pos = c.records.toList.filterMap αCacheRR` preserves the impl's `Array` order, and
    `DnsCache.store` **pushes** the new entry at the END (`Array.toList_push` ⟹ `αCache (store c rr) .pos
    = (filtered c.records).filterMap αCacheRR ++ [αCacheRR entry]`), whereas the model `Cache.insert`
    **prepends** (`⟨…⟩ :: pos`). So `αCache (impl storeChecked-fold)` (new records last) and
    `(αCache c).absorb …` (new records first) are reverse-ordered — their `topServed` LISTS differ even
    when equal as sets. WHY the read-path `lookupAnswerable_αRR_eq_hit` was immune: it compares one cache's
    impl-lookup to *its own* `αCache`-hit, both in `c.records` order — no prepend involved. CONSEQUENCE:
    `MatchMaxEquiv` (currently `topServed` LIST equality) is too strong for the impl-vs-model write pair;
    it must be **permutation** (`List.Perm`) on `topServed`, and correspondingly `RespAgree` must compare
    `answer` up to permutation. This is *also a legitimate gap-(iii) relaxation*: **DNS RRset order is
    RFC-unspecified, so requiring exact answer-list order is a model requirement STRONGER than the RFC.**
    Fixing `RespAgree`/`MatchMaxEquiv` to multiset/`Perm` answers both unblocks (B)(3) and removes that
    over-strength. The congruence proofs (B)(2) and stability (B)(1) carry over to `Perm` with `List.Perm`
    lemmas in place of `Eq` (topOf is a filter — `Perm`-congruent — and `absorb` prepends a shared prefix,
    so `Perm` is preserved). This is the redirection (B)(3) needs before the impl-side `storeChecked ↔
    insert` correspondence; the structural `αCache_store_pos` decomposition (push-order) is its anchor.
  - **`Perm`-FOUNDATIONS COMMITTED (2026-06-27, axiom-clean, build green 270 jobs).** The keystones that
    port the committed list-equality forms of (B)(1)/(B)(2) to permutation: `perm_all` (`List.all` is
    `Perm`-invariant — it quantifies over membership only), **`topOf_perm`** (`topOf` is `Perm`-congruent:
    `L ~ L' ⟹ topOf L ~ topOf L'`, since the per-key-max predicate is membership-only and `filter`
    commutes with `Perm`), and **`topOf_append_perm`** (`topOf L ~ topOf L' ⟹ topOf (M++L) ~ topOf (M++L')`
    — the `Perm` analogue of `topOf_append_congr`). With these, the next steps are mechanical ports:
    redefine `MatchMaxEquiv` with `(topServed …).Perm` (instead of `=`); re-derive `topServed_absorb_congr`
    /`MatchMaxEquiv.absorb`/`.absorbNeg` via `topOf_append_perm` (`absorb`/`absorbNeg` prepend a shared
    prefix); redefine `RespAgree` answer-comparison as `List.Perm`; re-thread the (B)(2) congruence
    (`resolves_cache_congr`'s `cacheHit`/`negHit` cases now yield `Perm` answers — `RespAgree`-`Perm`
    absorbs the `hit`-permutation). Then the impl-side `storeChecked ↔ insert` `topServed`-`Perm`
    correspondence (the (B)(3) crux, write-path analogue of `lookupAnswerable_αRR_eq_hit`), then (A).
  - **`RespAgree` → `Perm` DONE (2026-06-27, axiom-clean, build green 270 jobs).** `RespAgree a b` now
    compares `a.answer.Perm b.answer` (was `a.answer = b.answer`); `resolveWithIO_simulates` stays
    kernel-clean. The refactor touched only **7 sites** (added `RespAgree.of_eq` for the exact-match
    construction sites — the negHit branches and the four `WorldNetwork` terminal realizabilities — and
    swapped the `answerCname` reconstruction's `congrArg (cn :: ·)` for `List.Perm.cons`). This both
    unblocks the (B)(3) order-divergence AND is a **gap-(iii) over-strength removal**: the verdict relation
    no longer demands exact RRset order, which the RFC leaves unspecified. NEXT: redefine `MatchMaxEquiv`
    topServed-component to `Perm` (`refl`/`symm`/`trans`/`.hit`/`.served` → `Perm`; `topServed_absorb_congr`
    /`MatchMaxEquiv.absorb`/`.absorbNeg` re-derived via `topOf_append_perm`), then restate
    `resolves_cache_congr` to produce a `RespAgree`-equivalent final (only the `cacheHit` case yields a
    genuine `Perm`; all others `RespAgree.refl`) and lift through `hasVerdict_cache_congr` by
    `RespAgree.trans`. Then the impl-side `storeChecked ↔ insert` `topServed`-`Perm` correspondence, then (A).
  - **(B)(3) HAS TWO OBSTACLES, not one (2026-06-27) — `Perm`-ifying `MatchMaxEquiv` was REVERTED to keep
    (B)(2) green.** Working the `Perm` congruence surfaced that order-divergence is not the only issue:
    **OBSTACLE A (order-sensitive projections):** `Perm`-ifying `MatchMaxEquiv` breaks `referNoGlue` — its
    `hnsaddr : addressOf nsResp = some nsAddr` uses `addressOf` (first A-record), order-sensitive; a
    permuted `nsResp'` yields a different `nsAddr'`, and the second sub-resolution's IH is fixed to the
    original `[nsAddr]`, so it can't be re-applied. `cnameAt`/`cnameRR` (first cname) are order-sensitive
    too. **OBSTACLE B (dedup divergence):** impl `DnsCache.store` FILTERS same-key duplicates
    (`Cache.lean:51-53`: removes `same-key && (diff-expiry ∨ same-rdata)`) before pushing; the model
    `Cache.absorb`/`insert` APPEND with NO dedup — so the model `pos`/`served`/`hit` can carry duplicate
    RRs the impl removed. `[a]` is NOT `Perm` `[a,a]` (permutation preserves multiplicity), so **even
    `Perm` cannot bridge a dedup mismatch** — the relation would need to be up-to-dedup (set-level).
    CONSEQUENCE: the faithful fix is a pair of gap-(iii) model refinements making the model match the
    impl's cleaner behavior — (a) make `addressOf`/`cnameAt`/`cnameRR` order-INVARIANT (canonical pick,
    not "first"), and (b) make the model `served`/`hit` (or `absorb`) dedup so it never produces a
    duplicate answer RR (a real correctness nicety — DNS answers shouldn't repeat an RR). With both,
    `MatchMaxEquiv` can be set/`Perm`-based and the impl-`store` ↔ model-`absorb` bridge holds. KEPT:
    `RespAgree`-`Perm` (valid gap-(iii) relaxation), `RespAgree.refl`/`.trans`, and the Perm keystones
    (`perm_all`/`topOf_perm`/`topOf_append_perm`) for when the refinements land. This is the genuine
    remaining shape of (B)(3): two small model refinements, then the bridge, then (A).
  - **FINDING (2026-06-27, second model gap, security-relevant, from the unfollowable reduction): the
    model lacks an image for the `unfollowableDelegation` drop.** The impl (`run_ioResumeLoop_unfollowable`)
    drops a *received, accepted* response that is an out-of-bailiwick or not-closer delegation
    (`unfollowableDelegationB = true` — the bailiwick enforcement the referral-poisoning fix added) and
    retries the next server. NO model constructor covers it: `refer`/`referNoGlue` *require*
    `inBailiwick ∧ descendsBelow`, so an unfollowable referral cannot use them; `badResponse` only matches
    `rcode = servFail`; `timeout`/`rejectSpoof` are for lost/spoofed. So the C3 induction's unfollowable
    branch has no model target — a model gap exactly like `badResponse`, and pointedly the *security*
    branch. **Fix:** generalise `badResponse`'s `hbad` condition from `rcode = servFail` to a "response is
    not usable" predicate covering SERVFAIL **and** unfollowable-delegation **and** unclassifiable — LOW
    ripple, since the 14 `Resolves` inductions don't inspect `hbad` (their `| badResponse … hbad …`
    patterns are unaffected by `hbad`'s type), so only the constructor + the `badResponse_hasVerdict`
    classifier's hypothesis change. So the totality work has now surfaced that the "received-but-useless
    response → retry" family has *three* sub-cases (servfail ✓, unfollowable, unclassifiable) and only
    one was modeled — another gap-(iii) the induction forces into view. **DONE (2026-06-27, model gap
    CLOSED):** added the `Resolves.unfollowableReferral` constructor (received referral, `isReferral`,
    `descendsBelow = false` ⟹ not followable, recurse on `rest`); fixed all 14 `Resolves` inductions
    (mirroring `badResponse`/`rejectSpoof`) + reconstruction in `resolves_rd_irrelevant`; added the
    `unfollowableReferral_hasVerdict_hv` C3 classifier. Full build green (270 jobs), axiom-clean. So the
    *security-relevant* bailiwick-drop branch now has a model image and a classifier — the model is
    complete for it. (The `unclassifiable` retry sub-case beyond servfail+unfollowable remains a possible
    further refinement.) **SECOND gap-(iii) surfaced AND closed by the totality work this session.**
  - **FINDING (2026-06-27, state-abstraction design constraint, from reading `markQueried`/`bestWithAddress`):
    impl and model have DIFFERENT SLIST semantics.** The model's retry constructors recurse on `rest`
    (queried server *removed*); the impl's `markQueried` *increments `transmissionCount`* (deprioritizes,
    keeps the server) and `bestWithAddress` picks the lowest-count addressed server — so the impl **can
    re-query** a server (the sole addressed server is retried until fuel runs out), while the model
    exhausts after one pass. CONSEQUENCE for C3: the state-abstraction `αSlist` must map the impl state to
    the **query SEQUENCE** it will actually produce (simulate `bestWithAddress`+`markQueried` over the
    fuel), NOT the remaining-server *set* — the naive set abstraction is wrong and leaves the re-query
    path with no model image. So `αSlist (markQueried s name)` = the *tail* of the produced sequence,
    matching the model's `addr :: rest` → `rest`. This is a real design constraint surfaced by the
    totality work (the impl's retry-by-deprioritization vs the model's retry-by-removal); it shapes how
    the fuel induction's state relation must be defined. (Not a safety bug — re-querying is harmless and
    the cache write-path is bailiwick-bounded regardless — but a modeling subtlety the induction needs.)
    **RESOLUTION (makes C3 more tractable):** the model slist is a `List String` that **admits duplicates**,
    so a re-query is modeled by the same address appearing twice (`[A, A, B]`); and the slist need NOT be
    defined upfront by an `αSlist` function — it is **existentially constructed during the induction**:
    each retry/answer step's derivation puts the *current* `byteAddrToModel ab` at the head and takes the
    tail from the IH on the `markQueried` state (`HasVerdict … (addr :: restᵢₕ) …`). So the SLIST
    abstraction collapses from "define a tricky sequence function" to "build it inductively", and the
    re-query path is discharged by duplicate addresses. The cache / query / `cnameChain`→nseen mappings
    are the remaining state-relation pieces; for the retry-only sub-paths they're invariant (only the
    slist advances), so a **retry-then-terminal sub-induction** is the natural first slice of C3.
  - **FINDING (2026-06-27, BLOCKER for C3, from reading the recursion lemma): the model lacks a
    constructor for the impl's "bizarre-retry" branch.** The impl (`afterResume_bizarre` /
    `dropIfBizarre`, exercised by `run_ioResumeLoop_bizarre_recurses`) drops a *received* response that
    passed `acceptResponse` (id/question match) but is SERVFAIL or unclassifiable, and retries the next
    server. NO model `Resolves` constructor covers this: `timeout` needs `Transit … none` (lost, not
    received); `rejectSpoof` needs `accepts = false` (this passed); `answer`/`refer` need a
    `ServerAnswers` derivation (a SERVFAIL is none). So the `(depth, fuel)` induction has a branch it
    *cannot* discharge — C3 is blocked not only by proof effort but by a genuine **model gap**. **Fix
    (a real gap-(iii) closure, prerequisite for C3) — **DONE 2026-06-27, model gap CLOSED:** added the
    `Resolves.badResponse` constructor (`Transit … (some reply)` ∧ `accepts = true` ∧
    `reply.msg.rcode = servFail`, recurse on `rest`); fixed all 13 `Resolves` inductions (each gets a
    `badResponse` case mirroring `rejectSpoof`) and all downstream files; added `badResponse_hasVerdict`
    + `badResponse_hasVerdict_hv` (the C3 classifier, output-preserving). Full build green (270 jobs),
    axiom-clean. **The model now has an image for EVERY impl branch**, and the C3 induction has a
    classifier for the bizarre-retry path that previously had none. (A finer `unclassifiable`-retry
    variant beyond SERVFAIL is a possible further refinement; SERVFAIL is the principal bizarre case.)
    A genuine gap-(iii) model-incompleteness — surfaced *and closed* by the totality work, the
    meta-lesson in action.
  - **FINDING (2026-06-27, from the totality work): `finalizeAnswer` does not filter the answer section
    to qname-owned records.** The impl returns whatever answer RRs the upstream server sent (after
    `acceptResponse`'s id/question check), so `networkAnswer_simulates`'s `howner` (every answer RR owned
    by qname) is a genuine *precondition*, not automatic. This is the kind of unproven branch the
    meta-lesson targets. **It is NOT a cache-poisoning hole** — the cache *write* is bailiwick-bounded for
    every section by the proven `cacheWrite_pos_in_bailiwick` (gap 2), and cache *reads* key by name
    (`liveEntry`'s `nameEqCI`), so an unowned answer RR cannot be served for another name. The residual
    is only that the *returned-to-client* answer is not validated qname-owned — a possible hardening
    (filter `finalizeAnswer`'s answer to `nameEqCI · qname`), which would make `howner` a theorem and is
    a candidate D-class strengthening. Surfaced precisely because building the totality forces every
    branch's premises to be discharged.
    Known frictions to handle in (ii): the on-wire `truncateToCap`/`aa` normalization between
    `WorldModels`'s `OnWire ref reply` and `answer_hasVerdict`'s `RespAgree v {reply.msg with aa:=false}`;
    and the spoofed disjunct (`origin ≠ queried`) routing to `rejectSpoof`/bailiwick rather than `answer`.
    Each (i)/(ii) sub-lemma is independently committable; (iii) is the single large induction that
    consumes them. This is the genuinely multi-week unit — qualitatively unlike gaps 2–4's independent
    lemmas — but now fully scoped with every dependency proven.
  - **C1 REFINED + two C3 findings (2026-06-27, from attempting branch (ii)).** The first `WorldModels`
    baked a single `OnWire`/`reply` into the honest case — but `answer_hasVerdict` consumes the
    *truncated* wire form (`OnWire … (truncateToCap … qm ref).1 reply`) while `refer` consumes the
    *untruncated* `ref` — one fixed `reply` cannot serve both. **Fixed:** `WorldModels`'s honest case now
    gives the server's `ref` + reachability (`serverAt`+`ServerAnswers`+`RespAgree`+`linkReach`), and
    each branch classifier constructs its own wire form (`replyDatagram` with branch-appropriate
    truncation, `Transit.deliver`, `accepts` via `accepts_reply`). **Finding 1:** the answer classifier
    needs `ServerAnswers` *as its `answer` case* to derive `reply.msg.isReferral = false` — so (ii) must
    `cases` the `ServerAnswers` derivation and match it to the impl's `analyzeResponse` classification.
    **Finding 2 (security-relevant):** the **accepted-spoof** case (off-path reply that passes
    `acceptResponse`'s id/question gate) genuinely *cannot* be justified by `answer`/`refer` — those
    require the reply content to be a real server's `ServerAnswers`, which spoofed content is not. So
    totality for that case rests entirely on the **bailiwick anti-poison theorems already proven**
    (`cacheWrite_pos_in_bailiwick` etc.): the spoof is accepted but can only poison in-bailiwick names,
    which the cache-write refinement bounds. This is the precise point where gap (1) (totality) and gap
    (2) (anti-poison) meet — and why closing gap (2) first was the right order.
  - **C1 `WorldModels` — the design decision (the hinge).** This is the *only* remaining oracle premise
    and the one piece that is a modelling choice, not a derivable lemma: it states "the network the
    World oracle simulates behaves as the model `net`/`ns` says". You cannot prove the network — you
    *assume* it behaves per the model; the art is making the assumption (a) weak enough to be realizable
    by a real recursive resolver's environment and (b) strong enough to discharge every branch premise.
    Shape (from the FreeIO oracle `w.oracle : ByteArray → String → Option (Exchanged ByteArray)` and the
    `run_resolveWithIO_networkAnswer` pipeline `oracle → acceptExchanged → decode → sanitizeTtlsCap →
    acceptResponse → resp`): for every query-bytes `qb` and address `addr`, if
    `w.oracle qb addr = some d` and the pipeline yields `resp`, then the model's server at `addr`
    (`serverAt net addr`) produces a `ServerAnswers`/`Transit`/`OnWire` derivation observably agreeing
    with `αResp resp` — i.e. each *oracle exchange* is a single-hop model reply (which the per-branch
    `*_hasVerdict` lemmas already consume). Candidate formulations differ on: whether to quantify over
    all `(qb, addr)` or only reachable ones; whether to bake in the anti-spoof `accepts` gate; and
    whether to phrase the model side as `ServerReplies` (server-local) or full `Transit` (with
    `linkReach`). RECOMMEND the `Transit`-level, reachable-only form — it mirrors the single-hop lemmas
    exactly so the induction step is `WorldModels`-instantiation + the matching `*_hasVerdict_hv`
    wrapper. Once fixed, C3 is: `induction` on the `ioResumeLoop` fuel; the send/recv branch invokes
    `WorldModels` to get the single-hop reply + its model derivation, classifies it
    (answer/refer/cname/retry) exactly as the impl's `analyzeResponse` does, and applies the
    corresponding threading wrapper to the IH. NOTE: this is a genuinely large (multi-week) proof — it
    is the whole recursive resolver loop verified against the inductive model — and is qualitatively
    unlike gaps 2–4, which closed as independent incremental lemmas.
- **D1 (GAP 3) — DONE:** in-bailiwick-glue rule in model + impl (SLIST from filtered glue). Impl
  filters via `bailiwickRaws (referralCutRaw …)` (D1-impl); model `glueAddresses` now requires
  `isAncestor (referralCut ref) r.owner` (D1-model). Locked by `out_of_bailiwick_glue_rejected`. Both
  `by decide` worked examples (`glue_ignores_non_ns_address`, `faster_glue_tried_first`) still hold
  (their glue is in-bailiwick); the `refer` constructor is unaffected (uses glue as data).
- **D2 (GAP 3) — keystone DONE:** credibility-granularity gap closed *on the resolver's used cred
  set* via **`αCred_order_used`** (αCred is order-reversing on `{authoritativeSection, authoritySection,
  sectionNonauthoritative, additionalAuthoritative}` = images of `credAnswer/credAuthority/credAdditional`,
  recorded by `cred_used_*`). With `αCred_usable` this gives `maxCredForKey ↔ Cache.served` on the
  built cache. Done for `hhit`: the CODEC round-trip half **`αSection_map_rrBytes_wf`**; the
  produced-value correspondence **`αRR_setTtl`** + **`αRR_aged`** (impl TTL-aged record ↦ model
  TTL-aged served record, under fresh + `insertedAt ≤ now`). With `fresh_corr`/`αCacheRR_fresh`,
  `nameEqCI_iff`, `αClass`, `αRR_fields` already present, *all the local per-record correspondences
  for `hhit` now exist* — including the predicate correspondence **`answerableEntry_matching`**
  (impl `answerableEntry` ↔ model `matching ∩ usable`). Remaining for `hhit`: ONLY the `filterMap`
  *assembly* (`List.filterMap_filterMap` pushing both sides over `c.records`, composing
  `answerableEntry_matching` + `αRR_aged` + `mem_αCache_pos`) + the `maxCred`↔`maxrank` reconciliation
  (`served_is_per_key_maximal` + `αCred_order_used`, under a per-key-uniform-cred invariant). Plus
  model-side in-bailiwick-glue rule. REVERSE bridges now also done (`mapEq_of_bytesEqCI`,
  `foldEq_of_labelEq`, `mapfold_of_nameEq`). **FINDING:** the reverse *name* correspondence
  (`nameEqCI` from `nameEq` of abstractions) is **false in general** — `αName` ignores bytes after the
  null terminator while `nameEqCI`/`foldNameCase` fold all bytes, so names differing only in trailing
  garbage are `nameEq` but not `nameEqCI`. It holds only for **canonical** wire names (no trailing),
  which the `WfRR` cache invariant provides. So `hhit`'s reverse (= completeness) direction needs a
  canonical-name hypothesis + a fold/encode-commutation lemma (`foldNameCase (labelsToWireFormat ls) =
  labelsToWireFormat (ls.map foldNameCase)`) on top of the existing round-trip
  (`wireFormatToLabelsGo_prepend`). The SOUNDNESS direction (`lookupAnswerable ⊆ hit`, the
  security-relevant one) needs none of this — and is now **DONE**: `lookupAnswerable_subset_hit`
  (every record the resolver serves from cache abstracts to a member of `Cache.hit`; the impl never
  serves a record the model wouldn't), under abstraction-success + a per-key-uniform-rank invariant.
  Axiom-clean. The COMPLETENESS half (`hit ⊆ lookupAnswerable`, needed for exact `RespAgree`) is what
  still needs the canonical-name reverse correspondence. **Fold/encode commutation now DONE**:
  `foldNameCase_labelsToWireFormat` (+ `foldNameCase_append`, `foldCaseByte_le63`,
  `size_toUInt8_le63`, `foldNameCase_push`, `foldNameCase_labelsToWireFormatGo`) — case-folding a
  canonical wire name = encoding its case-folded labels. Next in the completeness chain: canonicity
  (`wireFormatToLabels` round-trip ⟹ `a = labelsToWireFormat (wireFormatToLabels a)`), then the
  reverse name correspondence under canonicity, then `maxrank`/`filterMap` completeness assembly.
  **Reverse name correspondence DONE**: `nameEqCI_of_αName_canonical` (under canonicity +
  validity, the `WfRR` invariant) — assembles the commutation + `mapfold_of_nameEq`.
  **Reverse PREDICATE correspondence DONE**: `matching_answerableEntry` (the COMPLETENESS-side
  converse of `answerableEntry_matching`) — a model entry satisfying `Cache.matching` ∩ `usable`,
  whose impl source abstracts to it, *is* an impl `answerableEntry`, under the canonical-name `WfRR`
  invariant. Needed two new image-restricted `beq→eq` lemmas — `eq_of_αType_beq` /
  `eq_of_αClass_beq` — since `RRType` (62 ctors) / `RRClass` are `deriving BEq` but NOT `LawfulBEq`,
  so generic `eq_of_beq` is unavailable; proven by exhaustive case split over the 16×16 (resp. 4×4)
  *image* grid, off-diagonal cells closed by `decide` on the concrete `==`.
  **Same-RRset-key bridge now DONE**: `αRR_sameKey` (impl `sameRRKey` ⟹ model `CacheRR.sameKey` on
  abstractions; forward, no canonicity) + `rrtype_beq_self`/`rrclass_beq_self` (reflexivity of `==` on
  the non-`LawfulBEq` enums). This is the grouping bridge the `maxCredForKey ↔ served`-maximality
  reconciliation needs. All axiom-clean (`[propext, Classical.choice, Quot.sound]`).
  **Both membership inclusions now DONE — the cache-served SET equality is proven.**
  `maxCredForKey_of_served_maximal` (keystone — model per-key `Cred.rank`-maximality ⟹ impl
  `e.toCode ≤ e2.toCode` gate via `αCred_order_used` + `αRR_sameKey` + `answerableEntry_matching`,
  under per-key-uniform-cred invariant `hused`) and `hit_subset_lookupAnswerable` (the COMPLETENESS
  inclusion `Cache.hit ⊆ lookupAnswerable`, membership converse of the done soundness
  `lookupAnswerable_subset_hit`). Together: the impl serves **exactly** the model's `Cache.hit` set —
  neither more (anti-mis-answer) nor less (completeness). Both axiom-clean. The ONLY residue for the
  full `hhit` *list* equality is now **DONE**: `lookupAnswerable_αRR_eq_hit` proves
  `(lookupAnswerable …).toList.filterMap αRR = Cache.hit` outright (axiom-clean) — the impl serves
  exactly the model's `Cache.hit` as a list (set, order, TTL-aging), fusing both sides to a common
  `c.records.toList.filterMap` (the inner `matching` kept folded via `generalize`) and closing the
  per-element option equality with `cond_eq` + `αRR_aged`. So the cacheHit branch is an
  *unconditional* refinement; the only step left is to thread it (with `αSection_map_rrBytes_wf`) to
  delete the `hhit` argument of `resolveWithIO_cacheHit_simulates` literally. **THREADED 2026-07-11 —
  D2 CLOSED**: `resolveWithIO_cacheHit_simulates` now takes the invariant pack
  (`hwf`/`hcanon`/`hused`/`hwfrr` + query canonicity `hqc`/`hcanN`/`hvN`, and the `q.qtype = .rr t`
  no-ANY pin) instead of `hhit`/`hne`, deriving both via `hhit_of_invariants` +
  `lookupAnswerable_αRR_eq_hit`; `resolveWithIO_simulates`' cache-hit disjunct carries the same
  impl-level facts in place of the model-level served-set equality. (`lookupAnswerable_mem_entry`/
  `lookupAnswerable_αRR_isSome` moved from `IoResumeSound` down to `Refinement` to support the
  discharge, the latter now over the unbundled record-abstraction clause.) Axiom-clean. The 7-level
  credibility ranking (model 4-tier `Cred.rank` mirroring the full §5.4.1 ladder) remains recorded as
  a model-faithfulness follow-up — under the `hused` invariant it does not affect the proven equality.
- **E1 (GAP 4):** replace `native_decide` with `decide`; full codec round-trip
  (`decode (encode m) = m`).

Order rationale: B1 locks the security property adversarially; C* removes the structural
(branch-coverage) class that hid the bug; D* makes the model match the RFC; E* shrinks the TCB.
