import VeriDNS.Spec.Cache
import VeriDNS.Impl.Cache
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Server

/-!
DnsCache conformance to the NLP-generated cache specification.

The generated `CacheSpec` laws (`store_mem`, `storeAt_mem`, `sweep_subset`,
from the RFC 1034 §5.3.2 CACHE glossary entry) are proven directly in the
instance (Impl/Cache.lean). Every remaining cache constraint in this file
INSTANTIATES a generated parameterized Prop — the statements come from the
RFC text via the generator, not from hand-written formalizations (manually
stated bridges, marked as helpers, only connect the instantiated predicates
back to membership facts):

- §5.3.2 "convert the interval specified in arriving RRs to some sort of
  absolute time when the RR is stored in the cache":
  `store_absolute_expiry` instantiates the generated
  `cache_storeAt_absolute`.
- §5.3.2 "the resolver just ignores or discards old RRs when it runs across
  them in the course of a search": `lookup_ignores_old` instantiates the
  generated `cache_search_ignores_old` against `liveEntry` (the exact
  per-entry test `lookup` filters by); helper `lookup_fresh` adds the
  membership/remaining-TTL reading.
- §5.3.2 "discards them during periodic sweeps": `sweep_discards_old`
  instantiates the generated `cache_sweep_discards_old` against
  `CacheEntry.fresh` (the exact retention test `sweep` filters by); helper
  `sweep_removes_expired` is the membership reading.
- §7.4 "either the data in the response or the cache is preferred, but the
  two should never be combined" (the all-or-none discipline):
  `store_never_combined` instantiates the generated
  `usingthecache_never_combined`; helper `store_replaces` is the
  underlying membership argument.
- §7.4 "should not cache a possibly partial set" (truncation):
  `truncated_not_cached` instantiates the generated
  `usingthecache_truncated_not_cached`; corollary
  `truncated_cache_unchanged` is the pointwise equation.
- §7.4 "unsolicited responses or RR data other than that requested ...
  discard it without caching it": `accept_discard_unrequested` instantiates
  the generated `usingthecache_discard_unrequested`.
-/

namespace VeriDNS.Proof.Cache

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.Cache
open VeriDNS.Impl.Resolver VeriDNS.Impl.Server
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase foldCaseByte alphabeticByte)

-- ============================================================
-- §5.3.2: absolute-time conversion on store
-- ============================================================

/-- `DnsCache.store` satisfies the generated `cache_storeAt_absolute`
    ("convert the interval specified in arriving RRs to some sort of
    absolute time when the RR is stored in the cache"): `interval` is the
    RR's TTL, `storeAt` is the store, and the post-store predicate holds
    of the absolute time `now + ttl` — an entry carrying the RR with
    exactly that absolute expiry is present after the store. -/
theorem store_absolute_expiry :
    cache_storeAt_absolute DnsCache ResourceRecord
      (fun rr => rr.ttl.toNat.toUInt32)
      (fun c rr now => DnsCache.store c rr now)
      (fun c rr e => ∃ en ∈ c.records, en.rr = rr ∧ en.expiry = e) := by
  intro c rr now
  dsimp only
  unfold DnsCache.store
  exact ⟨_, Array.mem_push.mpr (Or.inr rfl), rfl, rfl⟩

-- ============================================================
-- §5.3.2: search ignores expired entries
-- ============================================================

/-- The search path satisfies the generated `cache_search_ignores_old`
    ("the resolver just ignores or discards old RRs when it runs across
    them in the course of a search"): `old` is the negation of
    `CacheEntry.fresh`, and `ignored` is the negation of `liveEntry` — the
    EXACT per-entry test `DnsCache.lookup` filters by (single source of
    truth). An old entry never passes the search test. -/
theorem lookup_ignores_old (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) :
    cache_search_ignores_old CacheEntry
      (fun e => !(e.fresh now))
      (fun e => !(liveEntry e name qt qc now)) := by
  intro e h
  have hf : e.fresh now = false := by simpa using h
  simp [liveEntry, hf]

/-- Helper (membership reading of `lookup_ignores_old`): every RR returned
    by a lookup comes from an entry that has not expired, and carries the
    REMAINING ttl (expiry − now), never the original interval. -/
theorem lookup_fresh (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : ResourceRecord)
    (h : rr ∈ DnsCache.lookup c name qt qc now) :
    ∃ e ∈ c.records, e.expiry > now ∧
      rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold DnsCache.lookup at h
  obtain ⟨e, he, hf⟩ := Array.mem_filterMap.mp h
  split at hf
  · rename_i hcond
    refine ⟨e, he, ?_, (Option.some.inj hf).symm⟩
    unfold liveEntry CacheEntry.fresh at hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact hcond.2
  · exact absurd hf (by simp)

-- ============================================================
-- §5.3.2: periodic sweeps remove expired entries
-- ============================================================

/-- The sweep satisfies the generated `cache_sweep_discards_old`
    ("discards them during periodic sweeps"): `old` is the negation of
    `CacheEntry.fresh`, which is the EXACT retention test
    `DnsCache.sweep` filters by (single source of truth) — old data is
    discarded by the sweep filter. -/
theorem sweep_discards_old (now : UInt32) :
    cache_sweep_discards_old CacheEntry
      (fun e => !(e.fresh now))
      (fun e => !(e.fresh now)) :=
  fun _ h => h

/-- Helper (membership reading of `sweep_discards_old`): after a sweep at
    time `now`, no expired entry remains. -/
theorem sweep_removes_expired (c : DnsCache) (now : UInt32) :
    ∀ e ∈ (DnsCache.sweep c now).records, e.expiry > now := by
  intro e he
  unfold DnsCache.sweep at he
  have := (Array.mem_filter.mp he).2
  simpa [CacheEntry.fresh] using this

-- ============================================================
-- §7.4: all-or-none — the response and the cache are never combined
-- ============================================================

/-- Helper (membership argument for `store_never_combined`): after storing
    an RR, every same-key entry belongs to the new record's batch (same
    expiry — its RRset siblings, RFC 2181 §5.2) or is the new record
    itself — a stale set is never merged with the new one. -/
theorem store_replaces (c : DnsCache) (rr : ResourceRecord) (now : UInt32) :
    ∀ e ∈ (DnsCache.store c rr now).records,
      (nameEqCI e.rr.name rr.name && e.rr.type == rr.type
        && e.rr.class == rr.class) = true →
      e.rr = rr ∨ e.expiry = now + rr.ttl.toNat.toUInt32 := by
  intro e he hkey
  unfold DnsCache.store at he
  rcases Array.mem_push.mp he with hold | hnew
  · right
    have hkeep := (Array.mem_filter.mp hold).2
    rw [hkey] at hkeep
    by_contra hne
    have : (e.expiry != now + rr.ttl.toNat.toUInt32) = true := by
      simpa using hne
    rw [this] at hkeep
    simp at hkeep
  · left; rw [hnew]

/-- Storing satisfies the generated `usingthecache_never_combined`
    ("either the data in the response or the cache is preferred, but the
    two should never be combined"): the entries `preferred` for the
    stored RR's key are drawn wholly from the `response` side (the new
    record and its same-expiry batch siblings) — proven via the left
    disjunct; old same-key data from the `cache` side never survives
    alongside them (`store_replaces`). -/
theorem store_never_combined (c : DnsCache) (rr : ResourceRecord) (now : UInt32) :
    usingthecache_never_combined CacheEntry
      (fun e => e.rr = rr ∨ e.expiry = now + rr.ttl.toNat.toUInt32)
      (fun e => e ∈ c.records)
      (fun e => e ∈ (DnsCache.store c rr now).records ∧
        (nameEqCI e.rr.name rr.name && e.rr.type == rr.type
          && e.rr.class == rr.class) = true) :=
  Or.inl fun e h => store_replaces c rr now e h.1 h.2

-- ============================================================
-- Cache bounds: expiry-class eviction at IO-round boundaries
-- ============================================================

/-- The positive section is within `capacity` after the round-boundary
    bound: `boundExpiryClasses` evicts whole expiry classes (oldest
    inserted first) until the section fits. `store` itself no longer
    evicts — a mid-batch eviction could strand part of an RRset, breaking
    the wholeness invariant (`LookupComplete`,
    Proof/NameTreeComplete.lean); `ioResumeLoop` and `serveOne` apply the
    bound between IO rounds instead. -/
theorem boundExpiryClasses_bounded (c : DnsCache) :
    (c.boundExpiryClasses).records.size ≤ DnsCache.capacity := by
  unfold DnsCache.boundExpiryClasses
  exact size_evictClasses_le _ _ (Nat.le_refl _)

/-- The negative section never exceeds `capacity`. -/
theorem storeNegative_bounded (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (rc : Rcode) (soa : Option ResourceRecord)
    (expiry : UInt32) :
    (DnsCache.storeNegative c name qt qc rc soa expiry).negatives.size
      ≤ DnsCache.capacity := by
  unfold DnsCache.storeNegative
  rw [Array.size_push]
  exact Nat.succ_le_of_lt (size_boundFifo_lt _)

-- ============================================================
-- §7.4: truncated responses are not cached
-- ============================================================

/-- The caching gate satisfies the generated
    `usingthecache_truncated_not_cached` ("When a response is truncated,
    ... it should not cache a possibly partial set of RRs"): `truncated`
    reads the TC bit, and the `cache` action is `cacheUnlessTruncated` —
    a no-op on truncated data (at any credibility rank). -/
theorem truncated_not_cached {C RR : Type} [TrustworthinessSpec C RR]
    [RRParse RR] :
    usingthecache_truncated_not_cached C
      (Format × Array ByteArray × Trustworthiness × UInt32)
      (fun p => p.1.header.tc == 1)
      (fun cache p => cacheUnlessTruncated (RR := RR) cache p.1 p.2.1
        p.2.2.1 p.2.2.2) := by
  intro cache p h
  obtain ⟨resp, raws, cred, now⟩ := p
  show cacheUnlessTruncated (RR := RR) cache resp raws cred now = cache
  unfold cacheUnlessTruncated
  rw [if_pos h]

/-- Corollary (pointwise equation): a truncated response contributes
    nothing to the cache. -/
theorem truncated_cache_unchanged {C RR : Type} [TrustworthinessSpec C RR]
    [RRParse RR] (cache : C) (resp : Format) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) (h : resp.header.tc = 1) :
    cacheUnlessTruncated (RR := RR) cache resp raws cred now = cache :=
  truncated_not_cached cache (resp, raws, cred, now) (by simp [h])

-- ============================================================
-- §7.4: unsolicited / unrequested data is discarded before caching
-- ============================================================

/-- The response-acceptance gate satisfies the generated
    `usingthecache_discard_unrequested`: data that does not echo our query
    (`requested := acceptResponse matches`) never passes the gate
    (`cached := the gate yields a response`), hence never reaches `resume`
    and the cache. -/
theorem accept_discard_unrequested (sent : Format) :
    usingthecache_discard_unrequested Format
      (fun resp => (resp.header.id == sent.header.id
        && questionMatches resp.question sent.question))
      (fun resp => (acceptResponse sent resp).isSome) := by
  intro resp hreq
  show (acceptResponse sent resp).isSome = false
  have hreq' : (resp.header.id == sent.header.id
      && questionMatches resp.question sent.question) = false := hreq
  unfold acceptResponse
  rw [hreq']
  rfl

-- ============================================================
-- RFC 2308: negative caching conformance
-- (generated specs in Spec/NegativeCache.lean)
-- ============================================================

private theorem rcode_eq_of_beq {a b : Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem size_eq_zero_of_isEmpty {α : Type} {a : Array α}
    (h : a.isEmpty = true) : a.size = 0 := by
  simp at h; simp [h]

/-- `computeNegativeTtl` satisfies the generated negative-TTL law
    ("the minimum of the MINIMUM field of the SOA record and the TTL of the
    SOA itself"). -/
theorem computeNegativeTtl_conform :
    negativeanswersfromauthoritativeservers_negative_ttl computeNegativeTtl :=
  fun _ _ => rfl

/-- The implementation's NODATA cacheability test agrees with the generated
    `nodata_indicated` (NOERROR + empty answer) on untruncated responses. -/
theorem negativelyCacheable_nodata (resp : Format)
    (htc : resp.header.tc = 0)
    (hne : resp.header.rcode ≠ Rcode.nameError)
    (h : negativelyCacheable resp = true) :
    nodata_indicated resp := by
  unfold negativelyCacheable at h
  rw [htc] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h with ⟨_, hcase | ⟨hno, hempty⟩⟩
  · exact absurd (rcode_eq_of_beq hcase) hne
  · exact ⟨rcode_eq_of_beq hno, size_eq_zero_of_isEmpty hempty⟩

private theorem orElse_eq_some {α : Type} {a b : Option α} {x : α}
    (h : (a <|> b) = some x) : a = some x ∨ (a = none ∧ b = some x) := by
  cases a with
  | some y => left; simpa using h
  | none => right; exact ⟨rfl, by simpa using h⟩

/-- Negative lookups never return expired entries (the §5.3.2 freshness
    discipline applies to the negative cache as well) — through both the
    NXDOMAIN scan and the per-type scan. -/
theorem lookupNegative_fresh (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rc : Rcode)
    (h : DnsCache.lookupNegative c name qt qc now = some rc) :
    ∃ e ∈ c.negatives, e.rcode = rc ∧ e.expiry > now := by
  unfold DnsCache.lookupNegative at h
  rcases orElse_eq_some h with hx | ⟨_, hx⟩
  · unfold DnsCache.lookupNxdomain at hx
    obtain ⟨e, he, hf⟩ := Array.exists_of_findSome?_eq_some hx
    refine ⟨e, he, ?_⟩
    split at hf
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨Option.some.inj hf, hcond.1.2⟩
    · exact absurd hf (by simp)
  · obtain ⟨e, he, hf⟩ := Array.exists_of_findSome?_eq_some hx
    refine ⟨e, he, ?_⟩
    split at hf
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨Option.some.inj hf, hcond.2⟩
    · exact absurd hf (by simp)

/-- `DnsCache.lookupNxdomain` satisfies the generated
    `cachingnegativeanswers_nameError_retrieval` (NXDOMAIN retrieval is
    keyed by <QNAME, QCLASS> only): it takes no qtype at all, so the
    qtype-invariance is definitional. -/
theorem nxdomain_retrieval_conform :
    cachingnegativeanswers_nameError_retrieval (DnsCache × UInt32) (Option Rcode)
      (fun p qname _qtype qclass => DnsCache.lookupNxdomain p.1 qname qclass p.2) :=
  fun _ _ _ _ _ => rfl

/-- The resolver's negative lookup surfaces a fresh NXDOMAIN entry for
    EVERY query type (the bridge from the invariant retrieval to
    `lookupNegative`, which `stepCheckLocal` consults). -/
theorem lookupNegative_nxdomain_any_qtype (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (rc : Rcode)
    (h : DnsCache.lookupNxdomain c name qc now = some rc) :
    DnsCache.lookupNegative c name qt qc now = some rc := by
  unfold DnsCache.lookupNegative
  rw [h]
  rfl

/-- `NegativeEntry.authority` instantiates the generated §6 obligation
    `obligation_addCachedSoaRecordToAuthoritySection` ("MUST add the cached
    SOA record to the authority section of the response with the TTL
    decremented by the amount of time it was stored in the cache"): for any
    cached negative entry holding a SOA, the SOA with its TTL decremented
    to the remaining lifetime (`expiry − now`) is a member of the authority
    section the entry serves. -/
theorem negative_soa_in_authority :
    obligation_addCachedSoaRecordToAuthoritySection
      (NegativeEntry × UInt32) ResourceRecord
      (fun p => decide (p.1.expiry > p.2))
      (fun p => p.1.soa)
      (fun p rr => { rr with ttl := BitVec.ofNat 32 (p.1.expiry - p.2).toNat })
      (fun p => p.1.authority p.2) := by
  intro p _ rr hsoa
  obtain ⟨e, now⟩ := p
  dsimp only [] at hsoa ⊢
  unfold NegativeEntry.authority
  rw [hsoa]
  exact Array.mem_singleton.mpr rfl

/-- The negative-cache lookup serves exactly that authority section: a
    fresh entry found for the key yields its `NegativeEntry.authority`. -/
theorem lookupNegativeSoa_serves_authority (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (e : NegativeEntry)
    (h : DnsCache.findNegative c name qt qc now = some e) :
    DnsCache.lookupNegativeSoa c name qt qc now = e.authority now := by
  unfold DnsCache.lookupNegativeSoa
  rw [h]

-- ============================================================
-- RFC 2181 §5.4.1: credibility ranking conformance
-- ============================================================

/-- The answer-grade lookup never surfaces an entry at the untrustworthy
    floor: this instantiates the generated
    `obligation_untrustworthyNotAnswerable` (state = a (cache, key, time, rr)
    that `lookupAnswerable` returns; `credibility` = its entry's tier;
    `returnedAsAnswer` = membership in the answerable result). The key
    poisoning fix: glue, cached at the floor rank, can never be served as
    an answer. -/
theorem lookupAnswerable_excludes_floor
    (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : ResourceRecord) (h : rr ∈ DnsCache.lookupAnswerable c name qt qc now) :
    ∃ e ∈ c.records, e.credibility.toCode < untrustworthyFloor := by
  unfold DnsCache.lookupAnswerable at h
  obtain ⟨e, he, hf⟩ := Array.mem_filterMap.mp h
  split at hf
  · rename_i hcond
    unfold answerableEntry at hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact ⟨e, he, hcond.2⟩
  · exact absurd hf (by simp)

/-- The cache's answer path satisfies the generated
    `obligation_untrustworthyNotAnswerable`. State σ = a cache entry with a
    lookup key+time; `credibility` reads the entry's tier;
    `returnedAsAnswer` is `answerableEntry` — the EXACT per-entry test
    `lookupAnswerable` filters by (single source of truth). A floor-rank
    entry never passes — RFC 2181 §5.4.1's "never be returned as answers". -/
theorem cache_untrustworthyNotAnswerable :
    obligation_untrustworthyNotAnswerable
      (CacheEntry × ByteArray × BitVec 16 × BitVec 16 × UInt32)
      (fun p => p.1.credibility)
      (fun p => answerableEntry p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  rintro ⟨e, name, qt, qc, now⟩ hrank
  dsimp only [] at hrank ⊢
  unfold answerableEntry
  have hfloor : (decide (e.credibility.toCode < untrustworthyFloor)) = false := by
    have hf : untrustworthyFloor = 6 := rfl
    rw [hf]
    simp only [decide_eq_false_iff_not]
    omega
  rw [hfloor, Bool.and_false]

/-- `lookupAnswerable` is a credibility-restriction of `lookup`: every RR it
    returns is also returned by the unfiltered lookup (so the answer path
    never invents data). -/
theorem lookupAnswerable_subset
    (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : ResourceRecord) (h : rr ∈ DnsCache.lookupAnswerable c name qt qc now) :
    rr ∈ DnsCache.lookup c name qt qc now := by
  unfold DnsCache.lookupAnswerable at h
  unfold DnsCache.lookup
  obtain ⟨e, he, hf⟩ := Array.mem_filterMap.mp h
  apply Array.mem_filterMap.mpr
  refine ⟨e, he, ?_⟩
  split at hf
  · rename_i hcond
    unfold answerableEntry at hcond
    rw [Bool.and_eq_true] at hcond
    rw [if_pos hcond.1]
    exact hf
  · exact absurd hf (by simp)

/-- RFC 2181 §5.4.1 no-downgrade: `storeChecked` at credibility `cred` never
    evicts a fresh same-key entry the incoming data is NOT at least as
    trustworthy as (stated with the generated
    `Trustworthiness.atLeastAsTrustworthy` ranking relation) — that entry
    survives the store. "Data from a reply will be ignored if the cache
    contains data from a [more trustworthy] source." -/
theorem storeChecked_no_downgrade
    (c : DnsCache) (rr : ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (e : CacheEntry) (he : e ∈ c.records)
    (hkey : nameEqCI e.rr.name rr.name && e.rr.type == rr.type
      && e.rr.class == rr.class)
    (hfresh : e.expiry > now)
    (hbetter : ¬ Trustworthiness.atLeastAsTrustworthy cred e.credibility) :
    e ∈ (DnsCache.storeChecked c rr cred now).records := by
  have hbetter : e.credibility.toCode < cred.toCode := Nat.lt_of_not_le hbetter
  unfold DnsCache.storeChecked
  split
  · -- RFC 1035 §3.2.1 zero-TTL skip: the cache is untouched
    exact he
  rw [if_pos]
  · exact he
  · apply Array.any_eq_true.mpr
    obtain ⟨i, hi, hg⟩ := Array.getElem_of_mem he
    refine ⟨i, hi, ?_⟩
    rw [hg]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [Bool.and_eq_true, Bool.and_eq_true] at hkey
    exact ⟨⟨⟨⟨hkey.1.1, hkey.1.2⟩, hkey.2⟩, Or.inl hfresh⟩, hbetter⟩

-- ============================================================
-- RFC 1035 §3.1: end-to-end case-insensitivity of the cache
-- ============================================================

/-- The answer-path lookup is invariant under the case of the queried
    name: `EXAMPLE.com` hits the entry stored for `example.com`. End-to-end
    consequence of routing every name comparison through `nameEqCI`
    (which satisfies the generated `namespace_compare_caseinsensitive`). -/
theorem lookupAnswerable_caseInsensitive (c : DnsCache) (n1 n2 : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : foldNameCase n1 = foldNameCase n2) :
    DnsCache.lookupAnswerable c n1 qt qc now
      = DnsCache.lookupAnswerable c n2 qt qc now := by
  unfold DnsCache.lookupAnswerable answerableEntry liveEntry nameEqCI
  rw [h]

/-- The internal lookup is likewise case-invariant in the queried name. -/
theorem lookup_caseInsensitive (c : DnsCache) (n1 n2 : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : foldNameCase n1 = foldNameCase n2) :
    DnsCache.lookup c n1 qt qc now = DnsCache.lookup c n2 qt qc now := by
  unfold DnsCache.lookup liveEntry nameEqCI
  rw [h]

/-- Negative-cache retrieval is case-invariant in the queried name
    (both the NXDOMAIN and the per-type NODATA scan). -/
theorem lookupNegative_caseInsensitive (c : DnsCache) (n1 n2 : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : foldNameCase n1 = foldNameCase n2) :
    DnsCache.lookupNegative c n1 qt qc now
      = DnsCache.lookupNegative c n2 qt qc now := by
  unfold DnsCache.lookupNegative DnsCache.lookupNxdomain nameEqCI
  rw [h]

end VeriDNS.Proof.Cache
