import VeriDNS.Spec.Cache
import VeriDNS.Impl.Cache
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Server
import VeriDNS.RFC.Check

namespace VeriDNS.Proof.Cache

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.Cache
open VeriDNS.Impl.Resolver VeriDNS.Impl.Server
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase foldCaseByte alphabeticByte)

theorem store_absolute_expiry :
    cache_storeAt_absolute DnsCache ResourceRecord
      (fun rr => rr.ttl.toNat.toUInt32)
      (fun c rr now => DnsCache.store c rr now)
      (fun c rr e => ∃ en ∈ c.records, en.rr = rr ∧ en.expiry = e) := by
  intro c rr now
  dsimp only
  unfold DnsCache.store
  exact ⟨_, Array.mem_push.mpr (Or.inr rfl), rfl, rfl⟩

theorem lookup_ignores_old (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) :
    cache_search_ignores_old CacheEntry
      (fun e => !(e.fresh now))
      (fun e => !(liveEntry e name qt qc now)) := by
  intro e h
  have hf : e.fresh now = false := by simpa using h
  simp [liveEntry, hf]

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

/-- **Membership characterization of the (plain) cache lookup.** A record is served by `DnsCache.lookup` iff
    some cache entry is `liveEntry` for the query key (name/type/class match + fresh) and the served record is
    that entry's RR with its TTL adjusted to the remaining lifetime. The full-`liveEntry` companion of
    `lookup_fresh` (which exposes only freshness) — the handle the SLIST connector's cache-glue correspondence
    (step 4c) uses to pin which records `stepFindServers`' `CacheSpec.lookup` (= `DnsCache.lookup`) returns
    for an NS host's `A` records. -/
theorem mem_lookup (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : ResourceRecord) :
    rr ∈ DnsCache.lookup c name qt qc now ↔ ∃ e ∈ c.records, liveEntry e name qt qc now = true
      ∧ rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold DnsCache.lookup
  rw [Array.mem_filterMap]
  constructor
  · rintro ⟨e, he, hf⟩
    split at hf
    · rename_i hcond; exact ⟨e, he, hcond, (Option.some.inj hf).symm⟩
    · exact absurd hf (by simp)
  · rintro ⟨e, he, hlive, hrr⟩
    exact ⟨e, he, by rw [if_pos hlive, hrr]⟩

/-- **`liveEntry` decomposition for the lookup key.** A cache entry is live for `(name, qtype, qclass)` iff its
    owner case-insensitively matches `name`, its type and class equal `qtype`/`qclass`, and it is fresh. The
    next cache-glue building block (step 4c): instantiating `qtype = A`, `qclass = IN`, `name = nsName` picks
    out exactly the in-bailiwick glue `A` records `stepFindServers` reads for an NS host. -/
theorem liveEntry_iff (e : CacheEntry) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32) :
    liveEntry e name qt qc now = true ↔
      nameEqCI e.rr.name name = true ∧ e.rr.type = qt ∧ e.rr.class = qc ∧ e.fresh now = true := by
  unfold liveEntry
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- **`storeChecked` completeness (the write-path's positive direction).** A nonzero-TTL record with no
    higher-credibility incumbent for its key is actually stored: the cache afterwards contains an entry whose
    RR is `rr`, expiring at `now + ttl`, at credibility `cred`. The companion of the provenance lemma
    `mem_storeChecked_records` (which bounds what gets stored); together they pin `storeChecked`'s output. Under
    the driver's cache-MISS invariant `betterExists` is vacuously false (no incumbent), so the referral glue is
    genuinely cached — the write half of the SLIST connector's cache-glue correspondence (step 4c). -/
theorem mem_storeChecked_pushed (c : DnsCache) (rr : ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (hnz : (rr.ttl == 0) = false)
    (hnb : (c.records.any fun e =>
        nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
          && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
          && e.credibility.toCode < cred.toCode) = false) :
    ∃ e ∈ (c.storeChecked rr cred now).records,
      e.rr = rr ∧ e.expiry = now + rr.ttl.toNat.toUInt32 ∧ e.credibility = cred := by
  unfold DnsCache.storeChecked
  simp only [hnz, hnb, Bool.false_eq_true, if_false]
  unfold DnsCache.store
  exact ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩, Array.mem_push.mpr (Or.inr rfl), rfl, rfl, rfl⟩

/-- **A live, top-ranked cache entry makes `lookupTopCred` non-empty.** `lookupTopCred` is a `filterMap` keeping
    exactly the entries that pass `liveEntry` (name/type/class match + fresh) and `maxRankForKey` (top credibility
    for their key); any such member witnesses a non-empty result. The retrieval half of the referral cache-write
    read-back (`mem_storeChecked_pushed` supplies the member, this turns it into `lookupTopCred ≠ ∅`), i.e. the
    `hcut_ne_impl`/`walkNs_base` precondition of the refer-`.continue` SLIST keystone. -/
theorem lookupTopCred_ne_of_mem (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32)
    (e : CacheEntry) (he : e ∈ c.records)
    (hlive : liveEntry e name qtype qclass now = true)
    (hrank : c.maxRankForKey e now = true) :
    (c.lookupTopCred name qtype qclass now).isEmpty = false := by
  rw [Array.isEmpty_eq_false_iff_exists_mem]
  refine ⟨{ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }, ?_⟩
  rw [DnsCache.lookupTopCred, Array.mem_filterMap]
  exact ⟨e, he, by rw [hlive, hrank]; rfl⟩

/-- **`store` preserves non-conflicting entries.** An incumbent entry survives a `store` of `rr` unless it
    shares the `(name, type, class)` key AND either has a different expiry or the same rdata — i.e. distinct
    RRsets and same-expiry-distinct-rdata siblings (the multi-glue case: several `A` records for one NS host)
    all coexist. The preservation step the cache-glue fold (`cacheRRs`) needs so that every in-bailiwick glue
    `A` record stored earlier in the fold is still present at the end (step 4c). -/
theorem mem_store_preserve (c : DnsCache) (rr : ResourceRecord) (now : UInt32) (cred : Trustworthiness)
    (e : CacheEntry) (he : e ∈ c.records)
    (hkeep : (nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata)) = false) :
    e ∈ (c.store rr now cred).records := by
  unfold DnsCache.store
  refine Array.mem_push.mpr (Or.inl ?_)
  rw [Array.mem_filter]
  exact ⟨he, by rw [hkeep]; rfl⟩

/-- **`storeChecked` preserves non-conflicting entries.** `storeChecked` either no-ops (zero TTL or a
    higher-cred incumbent) or delegates to `store`; in all cases a non-conflicting incumbent survives. The
    inductive step of the `cacheRRs` fold completeness — every glue `A` record stored at one iteration is
    still present after all later iterations (step 4c). -/
theorem mem_storeChecked_preserve (c : DnsCache) (rr : ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (e : CacheEntry) (he : e ∈ c.records)
    (hkeep : (nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata)) = false) :
    e ∈ (c.storeChecked rr cred now).records := by
  simp only [DnsCache.storeChecked]
  split
  · exact he
  · split
    · exact he
    · exact mem_store_preserve c rr now cred e he hkeep

/-- **`cacheRRs` fold preservation.** An entry already in the cache survives the whole `cacheRRs` fold,
    provided it does not conflict (same key + different-expiry-or-same-rdata) with any record parsed from the
    raws. By `Array.foldl_induction` over the glue raws, threading `mem_storeChecked_preserve` at each step.
    The fold half of the SLIST connector's cache-glue write path (step 4c): combined with the per-record push
    (`mem_storeChecked_pushed`), it shows every in-bailiwick glue `A` record survives `cacheRRs` to be served
    by `stepFindServers`' lookup. -/
theorem mem_cacheRRs_preserve (c : DnsCache) (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32)
    (e : CacheEntry) (he : e ∈ c.records)
    (hnc : ∀ b ∈ raws, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := ResourceRecord) b = some rr →
        (nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
          && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata)) = false) :
    e ∈ (Resolver.cacheRRs (C := DnsCache) (RR := ResourceRecord) c raws cred now).records := by
  unfold Resolver.cacheRRs
  refine Array.foldl_induction (motive := fun _ (acc : DnsCache) => e ∈ acc.records) he ?_
  intro i acc ih
  cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := ResourceRecord) raws[i] with
  | none => simp only [hp]; exact ih
  | some rr =>
    simp only [hp]
    exact mem_storeChecked_preserve acc rr cred now e ih (hnc raws[i] (Array.getElem_mem i.isLt) rr hp)

theorem sweep_discards_old (now : UInt32) :
    cache_sweep_discards_old CacheEntry
      (fun e => !(e.fresh now))
      (fun e => !(e.fresh now)) :=
  fun _ h => h

theorem sweep_removes_expired (c : DnsCache) (now : UInt32) :
    ∀ e ∈ (DnsCache.sweep c now).records, e.expiry > now := by
  intro e he
  unfold DnsCache.sweep at he
  have := (Array.mem_filter.mp he).2
  simpa [CacheEntry.fresh] using this

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

theorem store_never_combined (c : DnsCache) (rr : ResourceRecord) (now : UInt32) :
    usingthecache_never_combined CacheEntry
      (fun e => e.rr = rr ∨ e.expiry = now + rr.ttl.toNat.toUInt32)
      (fun e => e ∈ c.records)
      (fun e => e ∈ (DnsCache.store c rr now).records ∧
        (nameEqCI e.rr.name rr.name && e.rr.type == rr.type
          && e.rr.class == rr.class) = true) :=
  Or.inl fun e h => store_replaces c rr now e h.1 h.2

theorem boundExpiryClasses_bounded (c : DnsCache) :
    (c.boundExpiryClasses).records.size ≤ DnsCache.capacity := by
  unfold DnsCache.boundExpiryClasses
  exact size_evictClasses_le _ _ (Nat.le_refl _)

/-- **`evictClasses` is the identity below capacity.** The very first guard returns the array unchanged when
    `size ≤ capacity`, so no expiry-class is dropped — for any fuel. -/
theorem evictClasses_noop (a : Array CacheEntry) (n : Nat) (h : a.size ≤ DnsCache.capacity) :
    evictClasses a n = a := by
  cases n with
  | zero => rfl
  | succ m => unfold evictClasses; rw [if_pos h]

/-- **`boundExpiryClasses` is the identity below capacity.** A cache that fits its capacity is not evicted, so
    the `boundStateCache` wrap applied on a referral `.continue` leaves the (small, just-absorbed) cache
    untouched — `state''.cache` is then exactly the model-mirrored `absorb` writes, with no eviction to
    reconcile. (The over-capacity case — a genuine eviction that can drop a fresh max-cred entry the unbounded
    model keeps — needs a capacity invariant on the absorbed cache or a one-directional cache refinement; this
    no-op lemma discharges the reconciliation whenever that invariant holds.) -/
theorem boundExpiryClasses_noop (c : DnsCache) (h : c.records.size ≤ DnsCache.capacity) :
    c.boundExpiryClasses = c := by
  unfold DnsCache.boundExpiryClasses
  rw [evictClasses_noop _ _ h]

theorem storeNegative_bounded (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (rc : Rcode) (soa : Option ResourceRecord)
    (expiry : UInt32) :
    (DnsCache.storeNegative c name qt qc rc soa expiry).negatives.size
      ≤ DnsCache.capacity := by
  unfold DnsCache.storeNegative
  rw [Array.size_push]
  exact Nat.succ_le_of_lt (size_boundFifo_lt _)

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

theorem truncated_cache_unchanged {C RR : Type} [TrustworthinessSpec C RR]
    [RRParse RR] (cache : C) (resp : Format) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) (h : resp.header.tc = 1) :
    cacheUnlessTruncated (RR := RR) cache resp raws cred now = cache :=
  truncated_not_cached cache (resp, raws, cred, now) (by simp [h])

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

private theorem rcode_eq_of_beq {a b : Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem size_eq_zero_of_isEmpty {α : Type} {a : Array α}
    (h : a.isEmpty = true) : a.size = 0 := by
  simp at h; simp [h]

theorem computeNegativeTtl_conform :
    negativeanswersfromauthoritativeservers_negative_ttl computeNegativeTtl :=
  fun _ _ => rfl

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

theorem nxdomain_retrieval_conform :
    cachingnegativeanswers_nameError_retrieval (DnsCache × UInt32) (Option Rcode)
      (fun p qname _qtype qclass => DnsCache.lookupNxdomain p.1 qname qclass p.2) :=
  fun _ _ _ _ _ => rfl

theorem lookupNegative_nxdomain_any_qtype (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (rc : Rcode)
    (h : DnsCache.lookupNxdomain c name qc now = some rc) :
    DnsCache.lookupNegative c name qt qc now = some rc := by
  unfold DnsCache.lookupNegative
  rw [h]
  rfl

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

theorem lookupNegativeSoa_serves_authority (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (e : NegativeEntry)
    (h : DnsCache.findNegative c name qt qc now = some e) :
    DnsCache.lookupNegativeSoa c name qt qc now = e.authority now := by
  unfold DnsCache.lookupNegativeSoa
  rw [h]

theorem lookupAnswerable_excludes_floor
    (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : ResourceRecord) (h : rr ∈ DnsCache.lookupAnswerable c name qt qc now) :
    ∃ e ∈ c.records, e.credibility.toCode < untrustworthyFloor := by
  unfold DnsCache.lookupAnswerable at h
  obtain ⟨e, he, hf⟩ := Array.mem_filterMap.mp h
  split at hf
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hans, _⟩ := hcond
    unfold answerableEntry at hans
    rw [Bool.and_eq_true, decide_eq_true_eq] at hans
    exact ⟨e, he, hans.2⟩
  · exact absurd hf (by simp)

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
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hans, _⟩ := hcond
    unfold answerableEntry at hans
    rw [Bool.and_eq_true] at hans
    rw [if_pos hans.1]
    exact hf
  · exact absurd hf (by simp)

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
  ·
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

theorem lookupAnswerable_caseInsensitive (c : DnsCache) (n1 n2 : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : foldNameCase n1 = foldNameCase n2) :
    DnsCache.lookupAnswerable c n1 qt qc now
      = DnsCache.lookupAnswerable c n2 qt qc now := by
  unfold DnsCache.lookupAnswerable DnsCache.maxCredForKey answerableEntry liveEntry nameEqCI
  rw [h]

theorem lookup_caseInsensitive (c : DnsCache) (n1 n2 : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : foldNameCase n1 = foldNameCase n2) :
    DnsCache.lookup c n1 qt qc now = DnsCache.lookup c n2 qt qc now := by
  unfold DnsCache.lookup liveEntry nameEqCI
  rw [h]

theorem lookupNegative_caseInsensitive (c : DnsCache) (n1 n2 : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : foldNameCase n1 = foldNameCase n2) :
    DnsCache.lookupNegative c n1 qt qc now
      = DnsCache.lookupNegative c n2 qt qc now := by
  unfold DnsCache.lookupNegative DnsCache.lookupNxdomain nameEqCI
  rw [h]

end VeriDNS.Proof.Cache

rfc_proves VeriDNS.Proof.Cache.truncated_cache_unchanged [1035][2585:2587]
rfc_proves VeriDNS.Proof.Cache.accept_discard_unrequested [1035][2601:2605]
rfc_proves VeriDNS.Proof.Cache.store_never_combined [1035][2607:2611]

rfc_proves VeriDNS.Proof.Cache.store_never_combined [2181][313:342]
