# LRU cache (deferred item 5) — implementation plan

Replace the cache's eviction policy — positives: drop the oldest-written entry's whole
expiry class (`evictClasses`); negatives: front-extract FIFO (`boundFifo`) — with **full
read-LRU at per-key granularity**: every lookup counts as a use, and the eviction victim is
the least-recently-used RRset key-group (positives) / entry (negatives). Anchor is unbound's
`lruhash` (rrset + msg caches are read-LRU); no RFC mandates an eviction policy, so this is
a quality/real-impl-parity item, not an RFC-compliance one (`prefer-rfc-real-impl`), and the
coverage layer gains nothing — deliberately no `check_rfc_doc` inflation.

Triaged against HEAD `b204b0f` (post item-6/Q4).

## Locked decisions (user, 2026-07-10)

1. **Full read-LRU** — reads bump recency, not just writes (unbound parity). Realized as the
   round-batched observational equivalent (see Design); NOT as in-band mutation of the cache
   on every pure-machine read (that variant is priced XL — state-literal churn through every
   run-inversion lemma and both capstones — and is observationally indistinguishable, so it
   buys nothing; veto here if in-band mutation is wanted for its own sake).
2. **Per-entry granularity with key-grouping** — the positive eviction unit is the
   `(name, type, class)` key-group (an RRset with its cohort), NOT today's expiry class.
   Strictly better RRset atomicity than the status quo (today a whole cross-key expiry
   cohort dies together; under key-grouping only the stale RRset dies), and it dodges the
   bugs.md #4 interplay: sub-key (single-RR) eviction is the thing that would touch the
   lossy-store/OneExpiryPerKey stack; whole-key eviction preserves OneExpiryPerKey trivially
   (a per-key property is unaffected by removing all of a key).
3. **Recency clock = `now` stamps** (`UInt32`, the loop's cache clock; same currency as
   `expiry`). No monotone counter field on `DnsCache` (avoids a second piece of threaded
   state); same-second ties broken by array order (stable — later-written wins, matching the
   current push-to-end discipline).
4. **Scope**: both stores. Positives at the two `boundExpiryClasses` sites; negatives
   replace `boundFifo`'s front-extract with an LRU victim. Model untouched (unbounded cache,
   recency-free) — `αCache` stays blind to recency.

---

## Recon facts the design rests on (verified 2026-07-10)

1. **The eviction interface is policy-invisible.** Everything the proof layer consumes about
   positive eviction is four lemma shapes: `evictClasses_filter_form`
   (`∃ p, result = a.filter (p ·.expiry)`), `mem_of_mem_evictClasses`,
   `size_evictClasses_le`, `evictClasses_noop`/`boundExpiryClasses_noop` (identity below
   capacity). The refinement path proper runs under the capacity-headroom hypothesis where
   the bound is a NO-OP (`Refinement.lean:2914` — over-capacity positive eviction is
   explicitly out of refinement scope; the general case rides the filter-form through
   `CacheRecCanon`/`CacheWf`-style invariants and the IoResumeSound c2f eviction slot).
   Changing the *victim chooser* keeps all four shapes; changing the filter's *key* (expiry →
   RRset key, decision 2) re-shapes `filter_form`'s predicate domain — the one real
   proof-surface change (stage L3).
2. **Eviction happens ONLY at boundaries.** Positives: exactly two sites —
   `Server.lean:529` (`boundStateCache`, applied on every `afterResume` continue/finish) and
   `Server.lean:826` (server-side bound after resolution). Negatives: inside
   `DnsCache.storeNegative` (all negative writes route through it, including Q3b's
   `storeProbeNegative`). No eviction mid-round.
3. **A round's read set is a deterministic function of its inputs.** Every pure-machine
   cache read (`stepCheckLocal`'s negative + answerable lookups, `stepFindServers`' SLIST
   NS/address reads, `gluelessRecheck`'s two subCache lookups, the server-side reply path)
   is keyed by values computable from `(state, resp)` at the round boundary — nothing reads
   the cache at a key the boundary can't reconstruct.
4. **Adding a `CacheEntry` field is nearly free**: exactly ONE anonymous constructor literal
   in the repo (`Impl/Cache.lean:50`); `αCacheRR` reads named fields (`rr`, `expiry`,
   `credibility`) and ignores anything new by construction; all cache invariants
   (`CacheWf`, `CacheNegWf`, `CacheNsCanon`, `CacheCnameCanon`, `LookupComplete`,
   `OneExpiryPerKey`, `CacheRecCanon`, …) read only non-recency fields.
5. **Negatives are pre-paid.** `NegWriteRefines` (Q3b) states the negative clauses as
   implications (impl-hit ⟹ model-hit): any shrink — hence ANY eviction policy — is already
   sound. `boundFifo`'s consumers are `mem_of_mem_boundFifo` + `size_boundFifo_lt` only.

---

## Design (locked): batched touches at the eviction boundary

**The core argument.** Since eviction only occurs at boundaries (recon 2), applying a
round's accumulated touches immediately before each bound gives **bit-identical eviction
decisions** to touching on every individual read: no eviction can observe the difference,
and nothing else reads recency. So full read-LRU is implemented as
*compute-the-read-set-at-the-boundary* (recon 3) — zero changes to the pure resolver's
signatures or state, zero state-literal churn, and the entire proof cost lands in the ONE
slot per site that already absorbs a cache transformation (`boundStateCache`, the
`.done-carries-state` / c2f-eviction precedent).

**New impl surface.**
- `CacheEntry.lastUsed : UInt32 := 0` (and `NegativeEntry.lastUsed`); stamped `now` at
  store time (`store`/`storeChecked`/`storeNegative`).
- `RRKey := (foldNameCase name, type, class)`; `DnsCache.touchKeys (keys : Array RRKey)
  (now : UInt32)` — map over `records`/`negatives` bumping `lastUsed` on key match;
  value-preserving by construction.
- `roundTouches state resp : Array RRKey` — the deterministic mirror of the round's read
  set: the `(sname, qtype, qclass)` demand key (positive + negative reads), the SLIST
  NS/address keys `stepFindServers` consults, and (on the glueless path) `gluelessRecheck`'s
  two keys. Touches are at DEMAND-key granularity (what was asked of the cache), not
  per-scanned-entry — LRU over queries, which is what unbound's lruhash keys on too.
- `evictLruKeys` — replaces `evictClasses`: while over capacity, drop the whole key-group
  whose recency (max `lastUsed` over the group) is minimal; ties by array order.
  Same fuel/termination shape as `evictClasses` (victim group is nonempty ⟹ strict shrink).
- `boundLru (touches) := touchKeys touches ∘ bound` replacing `boundExpiryClasses` at both
  sites; negatives: `storeNegative`'s `boundFifo` → drop-min-`lastUsed` entry when at
  capacity (keep the same filter+push same-key refresh).

**Anti-drift pins.** `roundTouches` duplicates knowledge of where the machine reads — the
one real risk of the batched design. Each read site gets a coverage lemma
(`touches_cover_localAnswer`, `touches_cover_findServers`, `touches_cover_recheck`): the key
that lookup consults is a member of `roundTouches state resp`. A future read site added
without a pin shows up in review; a changed key breaks the lemma.

**Proof story.**
- `touchKeys` invariance family: `αCache_touchKeys : αCache (c.touchKeys ks now) = αCache c`
  plus `Invariant_touchKeys` for each cache invariant — all one-liners through a generic
  `touchKeys` field-preservation lemma (entries change only in `lastUsed`).
- `evictLruKeys` re-proves the four interface lemmas with the filter over `RRKey`:
  `∃ p, result = a.filter (p (rrKey ·))`, `mem`, `size ≤ capacity`, `noop` below capacity.
  `OneExpiryPerKey`/`LookupComplete`/`CacheRecCanon` consumers re-thread on the key-filter
  form (the c2f eviction slot in IoResumeSound and the `boundExpiryClasses` literals in
  ResolveWithIOSound `:1374–1590` are the two concentrations).
- Below-capacity refinement path: `boundLru_noop`-analogue does NOT hold verbatim (touches
  bump `lastUsed` even below capacity) — the noop consumers upgrade from `= c` to
  `αCache`-equality via `αCache_touchKeys` (this is the main mechanical delta vs today; the
  drivers hold α-level facts at these points, so it is a substitution, not a redesign).
- Capstone statements untouched (acceptance criterion, same as qmin).

---

## Stages (each lands green)

### L0 — recon pins + literal sweep — **S**
Enumerate every pure-machine cache-read site (grep `lookup*`/`findNegative`/
`retrieveNegative`/`answers`/SLIST readers) and every consumer of
`boundExpiryClasses`/`evictClasses_filter_form`/`boundFifo` (expect: Proof/Cache.lean
interface, DeliveredWire `cacheRecCanon_boundExpiryClasses`, Refinement noop lemma,
IoResumeSound c2f slot, ResolveWithIOSound `:1374–1590`, NameTree/ServeSound touchpoints).
Count `DnsCache`/`NegativeEntry` literal sites. Output: the L3 checklist.

### L1 — pure additions, committed unused (item-4 stage-A shape) — **S**
`lastUsed` fields + stamped stores; `RRKey`/`rrKey`; `touchKeys` + invariance family;
`evictLruKeys` + four interface lemmas; negative LRU victim + its two lemmas. Zero call
sites change.

### L2 — `roundTouches` + anti-drift coverage lemmas — **M**
The deterministic read-set mirror + per-site `touches_cover_*` pins. Committed unused.

### L3 — the swap — **L, 1–2 sessions**
`boundStateCache`/`Server.lean:826` → `boundLru` with `roundTouches`; `storeNegative` victim
swap. Re-thread: run-lemma literals gain the touch wrapper (mechanical, boundStateCache
precedent), c2f eviction slot re-shaped to the key-filter form, noop consumers upgraded to
`αCache_touchKeys` equalities. Capstones re-elaborate; statements untouched.

### L4 — server-boundary reads — **S**
The reply path's own cache reads (negative-SOA authority assembly, direct cache answers)
join the touch set at `:826`; `serverLoop` already threads the cache across requests, so
cross-query recency needs nothing new.

### L5 — mocks + rig + docs — **S–M**
- `lruHotSurvivesEviction`: fill past capacity with distinct keys, interleave CLIENT READS
  (not writes) of one hot key, overflow — hot key still served from cache, cold victim gone.
  **The FIFO mutant is red** (under FIFO the hot key's age is its write time, so it dies).
- `lruReadIsAUse`: the read-LRU pin proper — two keys written in order A,B; read A; overflow
  by one; B (not A) is the victim. Distinguishes read-LRU from write-recency.
- `lruRRsetAtomic`: a 2-RR RRset under eviction pressure — both members evicted or both
  kept, never split.
- `lruNegativeRecency`: negative-cache twin.
- Rig: full corpus difftest re-run (eviction policy is client-invisible at corpus scale —
  expect 12/12 unchanged); optional stress run with a tiny `capacity` build to observe
  eviction live. Docs: architecture.md cache section, this plan's landed notes, memory.

Estimate: **3–5 sessions**. (The L3 slot re-shaping is the only L-sized item; everything
else is additive.)

---

## ✅ LANDED COMPLETE (2026-07-10, one session)

L0 (`bfdd72d`), L1a/b/c (`01b5ac8`/`588e23b`/`dc17c41`), L2 (`09b3cb5`), L3-pre family +
key-filter α-engine (`98293dc`), L3a negative swap (`22a1e63`), L3b+L4 serveDatagram `:826`
swap (`9dac1df`), L3c `boundStateCache`/`afterResume` swap + full rethread (`c1968ea`),
L5 mocks/rig/docs (`9e1c0f6`). Build green 287 + exe 576; `ioResumeLoop_sound` and
`serveDatagram_verdict_sound` axiom-clean; 5 `#guard` mocks green (`lruReadIsAUse`,
`lruHotSurvivesEviction` end-to-end, `lruRRsetAtomic`, `lruNegativeRecency`,
`lruNegativeEvictsCold`); difftest rig 12/12 vs live unbound. Notes: L4 folded into L3b
(`serveTouches`; `:826` went straight to final `boundLru` form); `lookupComplete_boundLru`
requires `TreeSane` + `CacheAgrees` (key filter has no same-expiry witness tie — verified
false without them); `recheckTouches` wired into the glueless slot 2026-07-11 (both
`gluelessRecheck` outcomes apply a bare `touchKeys` to `subCache` — not a boundary, no
evict — glueless-arm rethreads were pure `_touchKeys` transports); L3c grew a `resume_done_now` frame family (terminal state's `now` =
entry `now`) to identify the touch clock in the inversion lemmas.

## L0 findings (landed 2026-07-10) — the L3 checklist

**Recon corrections.**
- Recon fact 4 ("exactly ONE anonymous `CacheEntry` literal") is WRONG: besides
  `Impl/Cache.lean:50`, Proof/NetworkSim.lean has ~25 four-field `⟨rr, now + rr.ttl…, false,
  cred⟩` store-image literals (lines 2553–3778) and Proof/Refinement.lean 4 more
  (`:453/:1853/:1903/:1922`, plus `pushOf :924`). All are store-image facts with the same
  `now` in scope — each gains a 5th component `now`. Mechanical, but the L1 diff is wider
  than "one literal".
- Design line "`boundLru (touches) := touchKeys touches ∘ bound`" has the composition
  BACKWARDS relative to the core argument: touches must be applied BEFORE the eviction
  decision. Implemented as touch-then-evict.
- `storeNegative` does not receive `now` (only `expiry`), so the negative `lastUsed` stamp
  requires a signature change: new trailing `(now : UInt32)` param. Callers: 2 impl sites
  (`Server.lean:353` storeProbeNegative, `:754` storeNegativeIfCacheable — both have `now`
  in scope) + the `NegativeCacheSpec.cacheNegative` instance (`Impl/Cache.lean:302`,
  instance-only — `cacheNegative` has NO other call site in the repo). 28 direct
  `.storeNegative` applications across Proof/ (IoResumeSound 14, ResolveWithIOSound 6,
  NameTree 3, Cache 2, NameTreeComplete 2, DeliveredWire 1) gain the argument.
- No `CacheEntry`/`NegativeEntry`/`DnsCache` literals in test/ or VeriDNS/Test/.

**Positive-eviction consumer inventory** (all must survive the `evictClasses → evictLruKeys`
re-shape; the filter-form domain changes `UInt32`-expiry → `RRKey`):
- Interface (Impl/Cache.lean): `evictClasses_filter_form :183`, `mem_of_mem_evictClasses
  :203`, `size_evictClasses_le :209`; Proof/Cache.lean: `boundExpiryClasses_bounded :203`,
  `evictClasses_noop :210`, `boundExpiryClasses_noop :222`.
- Preservation family (each gets a `_boundLru` analogue = `_touchKeys` ∘ `_evictLruKeys`):
  `CacheWf_boundExpiryClasses` (NetworkSim:2966), `CacheNsCanon_/CacheCnameCanon_/
  CacheNsDistinct_boundExpiryClasses` (Refinement:4677/4687/4696),
  `CacheNegWf_boundExpiryClasses` (IoResumeSound:744), `wfrrAll_boundExpiryClasses`
  (IoResumeSound:765), `cacheRecCanon_boundExpiryClasses` (DeliveredWire:655),
  `LookupComplete` (NameTreeComplete:268), `NegativesFaithful :318` (rfl today — touches
  keep it rfl-ish), `OneExpiryPerKey` (NameTreeComplete:800), `CacheAgrees` (NameTree:971).
- α-level engine (Refinement:2914–3030): `αCache_boundExpiryClasses_noop :2923` (byte-`=`
  via `boundExpiryClasses_noop` — upgrade consumers to `αCache_touchKeys`-equality),
  `_pos_subset :2932`, `_pos_filter :2971` (the factor-through-`αCacheRR` engine — the ONE
  real re-shape: expiry-predicate → key-predicate; key factors through `αCacheRR` via
  owner/type/class canonicity, cf. `CacheRecCanon`), `αCache_boundExpiryClasses_eq :3006`.
- c2f slot (IoResumeSound:164–202): `αCache_boundExpiryClasses_eq_of_CacheWf :167`,
  `αCache_boundStateCache_refines :184`, `cacheRefines_boundStateCache_absorb :198`; noop
  consumers at `:5621/:6284` (`αCache_boundExpiryClasses_noop` under `hCap`) upgrade to
  `αCache_touchKeys`-composed equality. Invariant-pack sites: `:788` pack, `:5610–5631`,
  `:6273–6294`, `:8270–8310`, and the referral blocks `:5862–5984/:6515–6638/:7063–7186/
  :7633–7755` (all `_boundExpiryClasses` lemma applications — rename+re-shape mechanically).
- ResolveWithIOSound `:1374–1618` (serveDatagram run-lemma literal `pure
  cache''.boundExpiryClasses` + invariant pack), `:2539–2580`, `:3059–3125`,
  `:3306–3321`; `CacheNegSoaCanon/Owner` at `:3071/:3138`.
- FreeIO run-lemma literals: `:297/:366/:412/:1218–1276/:1329/:1370` (statement literals of
  `boundStateCache`/`.boundExpiryClasses` images — gain the touch wrapper in L3).
- Refinement driver arms: `:6786/:6916/:6944/:7624/:7722/:7885/:7918–7980/:8048/
  :8670–8776` (boundStateCache inversion/case lemmas — wrapper-transparent, re-elaborate).

**Negative-eviction consumers**: `mem_of_mem_boundFifo` (Impl/Cache.lean:251),
`size_boundFifo_lt :260`; uses at Proof/Cache.lean:234, IoResumeSound:824/:894,
NameTree:952/:958, NameTreeComplete:3136, ResolveWithIOSound:2686/:3125. All shrink-shaped
(recon 5 confirmed: `NegWriteRefines` clauses are impl-hit ⟹ model-hit implications).

**Pure-machine read sites → `roundTouches` obligations** (all keyed from `(state, resp)` +
the boundary cache; the localAnswer chase keys are cache-DEPENDENT, so the mirror re-runs
the chase on the boundary cache — same fuel 8, same visited-guard):
1. `localAnswer` (Impl/Resolver.lean:302–326), per chase hop `sname_i`: negative read
   `(sname_i, qtype, qclass)` (`retrieveNegative`; `lookupNxdomain` half ignores qtype —
   demand key still `(sname_i, ·, qclass)` at qtype granularity, documented), answerable
   read `(sname_i, qtype, qclass)`, CNAME probe `(sname_i, 5, qclass)`, negative-SOA
   authority assembly on the hit arm (same key as the negative read).
2. `stepFindServers` (`:353–412`): `walkNs` NS reads `(name_i, NS, IN)` for `name_i` =
   sname, parent(sname), … (fuel 128, stops at first non-empty); glue reads
   `(nsName, A, IN)` per returned NS name.
3. `gluelessRecheck` (Impl/Server.lean:565–584): `(sname, qtype, qclass)` negative +
   answerable on the SUB-RUN's output cache (which becomes the main cache) — its touch
   joins the post-recheck bound.
4. Server reply path (L4, at `:826`): the first-round `stepCheckLocal` reads (cache-hit
   answers on the immediate-`.done` path never cross `boundStateCache`) + negative-SOA
   assembly — covered by touching the client demand key + re-running the chase mirror at
   the `:826` boundary.

## Risk register

| Risk | Mitigation |
|---|---|
| `roundTouches` drifts from the real read sites (silent recency loss) | per-site `touches_cover_*` lemmas land WITH the mirror (L2); review checklist item |
| Key-filter form breaks c2f-slot consumers in ways expiry-filter didn't | L0 enumerates them first; the form is still `∃ p, filter` — only the predicate's domain changes |
| Below-capacity noop identity (`boundExpiryClasses_noop`) is load-bearing as a BYTE equality somewhere | L0 sweep flags exact-`=` consumers; upgrade path is `αCache_touchKeys` + `MatchMaxEquiv` (warm-cache-dedup precedent) |
| `lastUsed` stamps regress `OneExpiryPerKey`-style uniqueness assumptions | recency is a fresh field no invariant reads; the invariance family is proven in L1 before any call site changes |
| Touch at `now` granularity too coarse (same-second storms) | ties fall back to array order = today's behaviour; acceptable, documented |
| Per-key eviction evicts a key mid-resolution that the SLIST still needs | same exposure as today's class eviction (eviction may drop live data); the loop's cache-first re-check and SBELT fallback already tolerate it |
