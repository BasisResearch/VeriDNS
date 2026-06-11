import VeriDNS.Spec.Resolver
import VeriDNS.Spec.ResourceRecord
import VeriDNS.Spec.Credibility
import VeriDNS.Spec.NegativeCache
import VeriDNS.Impl.ResourceRecord

namespace VeriDNS.Impl.Cache

open VeriDNS.Spec
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase)

/-- The max (least-trustworthy) credibility rank: `Trustworthiness`'s last
    tier (additional information / authority of a non-authoritative answer).
    RFC 2181 §5.4.1: data at this rank must never be returned as an answer
    — the `obligation_untrustworthyNotAnswerable` floor. -/
def untrustworthyFloor : Nat :=
  Trustworthiness.toCode .additionalAuthoritative

-- RFC 1035 §6.1.3: absolute expiry; RFC 2181 §5.4.1: credibility tier
-- (the generated `Trustworthiness` enum; rank 0 = most trustworthy,
-- `untrustworthyFloor` = least, not answerable).
structure CacheEntry where
  rr : ResourceRecord
  expiry : UInt32
  authoritative : Bool
  credibility : Trustworthiness := .additionalAuthoritative
  deriving Inhabited

/-- Per-entry freshness (RFC 1034 §5.3.2): an entry whose absolute expiry
    has passed is "old". Single source of truth for the freshness
    discipline — `lookup` (via `liveEntry`) and `sweep` filter through it,
    and its negation instantiates `old` in the generated
    `cache_search_ignores_old` / `cache_sweep_discards_old`
    (Proof/Cache.lean). -/
def CacheEntry.fresh (e : CacheEntry) (now : UInt32) : Bool :=
  e.expiry > now

/-- RFC 2308: a cached negative answer for (name, qtype, qclass). `soa` is
    the SOA record that carried the negative TTL (§6: it MUST be added to
    the authority section when the entry answers a query, TTL decremented);
    stored with its TTL equal to the (capped) negative TTL so the remaining
    lifetime `expiry − now` IS the decremented TTL. -/
structure NegativeEntry where
  name : ByteArray
  qtype : BitVec 16
  qclass : BitVec 16
  rcode : Rcode
  expiry : UInt32
  soa : Option ResourceRecord := none
  deriving Inhabited

structure DnsCache where
  records : Array CacheEntry
  negatives : Array NegativeEntry := #[]
  deriving Inhabited

def DnsCache.empty : DnsCache := { records := #[] }

/-- Maximum entries per cache section (positive records / negative entries).
    A full cache evicts its oldest-inserted entry (FIFO) on store, bounding
    memory regardless of query mix. -/
def DnsCache.capacity : Nat := 4096

/-- Drop the oldest-inserted entries until there is room for one more. -/
private def boundFifo {α : Type} (a : Array α) : Array α :=
  if a.size ≥ DnsCache.capacity then a.extract (a.size + 1 - DnsCache.capacity) a.size
  else a

/-- Store an RR with absolute expiry = now + ttl.

    RFC 1035 §7.4 all-or-none applies at RRset granularity: a multi-record
    set (e.g. 4 A records) arrives as one batch sharing `expiry`
    (RFC 2181 §5.2: RRs of an RRset have equal TTLs). Storing a member
    replaces same-key entries from OTHER batches (different expiry — a
    stale set is never merged with the new one) and any identical
    re-stored record, but keeps same-batch siblings, so the whole set
    survives.

    `store` itself never evicts: a capacity eviction in the middle of a
    batch could orphan the members already stored, breaking RRset
    wholeness (`LookupComplete`, Proof/NameTreeComplete.lean). The bound
    is enforced between IO rounds by `boundExpiryClasses`. -/
def DnsCache.store (c : DnsCache) (rr : ResourceRecord) (now : UInt32)
    (cred : Trustworthiness := .additionalAuthoritative) : DnsCache :=
  let expiry := now + rr.ttl.toNat.toUInt32
  let entry : CacheEntry := ⟨rr, expiry, false, cred⟩
  let records := c.records.filter fun e =>
    !(nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
      && (e.expiry != expiry || e.rr.rdata == rr.rdata))
  { c with records := records.push entry }

/-- Credibility-checked store (RFC 2181 §5.4.1): a same-key entry of
    STRICTLY BETTER credibility (lower rank) that is still fresh is retained
    in preference to the incoming RR — "data from a reply will be ignored if
    the cache contains data from [a more trustworthy source]" — so the store
    is a no-op. Otherwise it tags the RR with `cred` and stores it (§7.4
    all-or-none and FIFO bounds via `store`). The resolver caches response
    sections through this (each section at its §5.4.1 rank), so forged glue
    can neither be served as an answer (`lookupAnswerable`) nor evict
    legitimately authoritative data. -/
def DnsCache.storeChecked (c : DnsCache) (rr : ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) : DnsCache :=
  -- RFC 1035 §3.2.1: a zero TTL means the RR "can only be used for the
  -- transaction in progress, and should not be cached". (This also keeps
  -- every stored entry strictly fresh at store time, which the RRset
  -- wholeness invariant relies on.)
  if rr.ttl == 0 then c
  else
    -- A same-key entry of strictly better credibility blocks the store
    -- when it is fresh OR of the incoming batch's own expiry (the second
    -- disjunct refuses to overwrite better-credibility data of the same
    -- vintage; without it a least-trustworthy store could replace an
    -- answerable batch member and split its RRset).
    let expiry := now + rr.ttl.toNat.toUInt32
    let betterExists := c.records.any fun e =>
      nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry > now || e.expiry == expiry)
        && e.credibility.toCode < cred.toCode
    if betterExists then c else DnsCache.store c rr now cred

/-- RFC 2308: store a negative answer, replacing existing same-key entries;
    evicts FIFO at capacity. An NXDOMAIN store replaces ALL entries for
    <QNAME, QCLASS> (§5: the name does not exist for any type); a NODATA
    store replaces only its own <QNAME, QTYPE, QCLASS>. -/
def DnsCache.storeNegative (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (rcode : Rcode) (soa : Option ResourceRecord) (expiry : UInt32) : DnsCache :=
  let negatives := c.negatives.filter fun e =>
    !(nameEqCI e.name name && e.qclass == qclass
      && (rcode == Rcode.nameError || e.qtype == qtype))
  { c with negatives := (boundFifo negatives).push ⟨name, qtype, qclass, rcode, expiry, soa⟩ }

/-- RFC 2308 §5: NXDOMAIN entries are keyed by <QNAME, QCLASS> only — no
    qtype parameter at all, which makes the generated qtype-invariance
    (`cachingnegativeanswers_nxdomain_retrieval`) definitional. -/
def DnsCache.lookupNxdomain (c : DnsCache) (name : ByteArray) (qclass : BitVec 16)
    (now : UInt32) : Option Rcode :=
  c.negatives.findSome? fun e =>
    if nameEqCI e.name name && e.qclass == qclass && e.expiry > now
        && e.rcode == Rcode.nameError then
      some e.rcode
    else none

/-- RFC 2308: cached negative rcode for the key, if not expired. An
    NXDOMAIN entry answers every qtype (§5 <QNAME, QCLASS> keying); NODATA
    entries are per-type. -/
def DnsCache.lookupNegative (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Option Rcode :=
  (c.lookupNxdomain name qclass now) <|>
    c.negatives.findSome? fun e =>
      if nameEqCI e.name name && e.qtype == qtype && e.qclass == qclass && e.expiry > now then
        some e.rcode
      else none

/-- The per-entry search test (RFC 1034 §5.3.2): key match AND fresh.
    Single source of truth — `lookup` filters by it, and its negation
    instantiates `ignored` in the generated `cache_search_ignores_old`
    (an old entry never passes; Proof/Cache.lean `lookup_ignores_old`). -/
def liveEntry (e : CacheEntry) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Bool :=
  nameEqCI e.rr.name name && e.rr.type == qtype && e.rr.class == qclass
    && e.fresh now

/-- Lookup RRs by name+type+class, excluding expired entries. Returned RRs
    carry the REMAINING TTL (expiry − now): a cached RR passed on to a client
    must not restart its lifetime (RFC 1035 §6.1.3 absolute-expiry
    discipline read back as an interval).

    This (unfiltered) lookup is for INTERNAL use — finding NS records for
    server selection (§5.3.3 step 2). RFC 2181 §5.4.1 permits even
    least-trustworthy data "to be returned as additional information" /
    used internally; only ANSWERS to the client are gated (see
    `lookupAnswerable`). -/
def DnsCache.lookup (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32)
    : Array ResourceRecord :=
  c.records.filterMap fun e =>
    if liveEntry e name qtype qclass now then
      some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
    else
      none

/-- The per-entry answerability test (RFC 2181 §5.4.1): key match, fresh,
    and strictly more trustworthy than the floor. Single source of truth —
    used by `lookupAnswerable` and instantiating `returnedAsAnswer` in the
    generated `obligation_untrustworthyNotAnswerable`. -/
def answerableEntry (e : CacheEntry) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Bool :=
  liveEntry e name qtype qclass now
    && e.credibility.toCode < untrustworthyFloor

/-- Lookup for the CLIENT ANSWER path (RFC 1034 §5.3.3 step 1): like
    `lookup`, but EXCLUDES entries at the untrustworthy floor. RFC 2181
    §5.4.1: least-trustworthy data (additional information, authority of a
    non-authoritative answer) "should not be cached in such a way that they
    would ever be returned as answers". This instantiates the generated
    `obligation_untrustworthyNotAnswerable` (proven in Proof/Cache.lean). -/
def DnsCache.lookupAnswerable (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Array ResourceRecord :=
  c.records.filterMap fun e =>
    if answerableEntry e name qtype qclass now then
      some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
    else
      none

/-- RFC 2308 §6 authority section for a cached negative answer: the stored
    SOA "with the TTL decremented by the amount of time it was stored in
    the cache". The SOA was stored carrying the negative TTL, so the
    decremented TTL is exactly the entry's remaining lifetime
    `expiry − now`. Instantiates the transform and target of the generated
    `obligation_addCachedSoaRecordToAuthoritySection` (Proof/Cache.lean). -/
def NegativeEntry.authority (e : NegativeEntry) (now : UInt32) : Array ResourceRecord :=
  match e.soa with
  | some rr => #[{ rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }]
  | none => #[]

/-- The fresh negative entry answering ⟨name, qtype, qclass⟩ — NXDOMAIN
    (qtype-invariant, §5 <QNAME, QCLASS> keying) first, then per-type
    NODATA, mirroring `lookupNegative`'s keying. -/
def DnsCache.findNegative (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Option NegativeEntry :=
  (c.negatives.find? fun e =>
    nameEqCI e.name name && e.qclass == qclass && e.expiry > now
      && e.rcode == Rcode.nameError)
  <|> c.negatives.find? fun e =>
    nameEqCI e.name name && e.qtype == qtype && e.qclass == qclass && e.expiry > now

/-- RFC 2308 §6: the authority RRs to attach when a cached negative entry
    answers ⟨name, qtype, qclass⟩ — the stored SOA, TTL decremented. -/
def DnsCache.lookupNegativeSoa (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Array ResourceRecord :=
  match c.findNegative name qtype qclass now with
  | some e => e.authority now
  | none => #[]

/-- Remove expired entries (positive and negative). The positive
    section's retention test is exactly `CacheEntry.fresh` — the
    generated `cache_sweep_discards_old` is instantiated against it
    (Proof/Cache.lean `sweep_discards_old`). -/
def DnsCache.sweep (c : DnsCache) (now : UInt32) : DnsCache :=
  { records := c.records.filter fun e => e.fresh now
    negatives := c.negatives.filter fun e => e.expiry > now }

/-- Evict whole expiry classes — oldest-inserted entry's class first —
    until the positive section is within capacity. An RRset batch shares
    one expiry (one store time + RFC 2181 §5.2 uniform TTLs), so
    class-granular eviction never splits a cached set; per-entry FIFO
    could strand half an RRset, breaking the wholeness invariant
    (`LookupComplete`, Proof/NameTreeComplete.lean). Runs at IO-round
    boundaries (`ioResumeLoop`, `serveOne`), never mid-batch. -/
def evictClasses (a : Array CacheEntry) : Nat → Array CacheEntry
  | 0 => a
  | fuel + 1 =>
    if a.size ≤ DnsCache.capacity then a
    else
      match a[0]? with
      | some e0 => evictClasses (a.filter fun e => e.expiry != e0.expiry) fuel
      | none => a

def DnsCache.boundExpiryClasses (c : DnsCache) : DnsCache :=
  { c with records := evictClasses c.records c.records.size }

/-- Every eviction pass is a filter by a predicate on the entry's EXPIRY
    alone — the formal core of "no RRset is ever split": same-expiry
    entries are kept or dropped together. -/
theorem evictClasses_filter_form (a : Array CacheEntry) (fuel : Nat) :
    ∃ p : UInt32 → Bool, evictClasses a fuel = a.filter (fun e => p e.expiry) := by
  induction fuel generalizing a with
  | zero =>
    exact ⟨fun _ => true, by
      unfold evictClasses
      exact (Array.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩
  | succ fuel ih =>
    unfold evictClasses
    split
    · exact ⟨fun _ => true,
        (Array.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩
    · split
      · next e0 _ =>
        obtain ⟨p, hp⟩ := ih (a.filter fun e => e.expiry != e0.expiry)
        refine ⟨fun x => p x && (x != e0.expiry), ?_⟩
        rw [hp, Array.filter_filter]
      · exact ⟨fun _ => true,
          (Array.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩

theorem mem_of_mem_evictClasses {a : Array CacheEntry} {fuel : Nat}
    {e : CacheEntry} (h : e ∈ evictClasses a fuel) : e ∈ a := by
  obtain ⟨p, hp⟩ := evictClasses_filter_form a fuel
  rw [hp] at h
  exact (Array.mem_filter.mp h).1

/-- Eviction reaches the capacity bound: each pass drops at least the
    oldest entry, so `a.size` passes suffice. -/
theorem size_evictClasses_le (a : Array CacheEntry) (fuel : Nat)
    (hfuel : a.size ≤ fuel) :
    (evictClasses a fuel).size ≤ DnsCache.capacity := by
  induction fuel generalizing a with
  | zero =>
    unfold evictClasses
    unfold DnsCache.capacity
    omega
  | succ fuel ih =>
    unfold evictClasses
    split
    · assumption
    · next hbig =>
      split
      · next e0 he0 =>
        refine ih _ ?_
        have he0mem : a[0]? = some e0 := he0
        have hsz : 0 < a.size := by
          by_contra hz
          rw [Array.getElem?_eq_none (by omega)] at he0mem
          cases he0mem
        have hkeep : (a.filter fun e => e.expiry != e0.expiry).size < a.size := by
          have hmem : e0 ∈ a := by
            have := Array.getElem?_eq_some_iff.mp he0mem
            obtain ⟨h0, heq⟩ := this
            exact heq ▸ a.getElem_mem h0
          by_contra hge
          have hle : (a.filter fun e => e.expiry != e0.expiry).size ≤ a.size :=
            Array.size_filter_le
          have heq : (a.filter fun e => e.expiry != e0.expiry).size = a.size := by
            omega
          have := (Array.filter_size_eq_size.mp heq) e0 hmem
          simp at this
        omega
      · next he0 =>
        have hempty : a.size ≤ 0 := by
          by_contra hpos
          rw [Array.getElem?_eq_none_iff] at he0
          omega
        unfold DnsCache.capacity
        omega

theorem mem_of_mem_boundFifo {α : Type} {a : Array α} {x : α}
    (h : x ∈ boundFifo a) : x ∈ a := by
  unfold boundFifo at h
  split at h
  · rw [Array.mem_extract_iff_getElem] at h
    obtain ⟨k, hk, hx⟩ := h
    exact hx ▸ a.getElem_mem _
  · exact h

theorem size_boundFifo_lt {α : Type} (a : Array α) :
    (boundFifo a).size < DnsCache.capacity := by
  unfold boundFifo
  split <;> rename_i h
  · rw [Array.size_extract]
    unfold DnsCache.capacity at *
    omega
  · unfold DnsCache.capacity at *
    omega

private theorem store_mem_aux (c : DnsCache) (rr : ResourceRecord) (now : UInt32) :
    rr ∈ (DnsCache.store c rr now).records.map (·.rr) := by
  unfold DnsCache.store
  exact Array.mem_map.mpr ⟨_, Array.mem_push.mpr (Or.inr rfl), rfl⟩

instance : CacheSpec DnsCache ResourceRecord where
  store c rr := DnsCache.store c rr 0
  storeAt := DnsCache.store
  sweep := DnsCache.sweep
  entries c := c.records.map (·.rr)
  lookup := DnsCache.lookup
  store_mem c rr := store_mem_aux c rr 0
  storeAt_mem := store_mem_aux
  sweep_subset c t y hy := by
    unfold DnsCache.sweep at hy
    obtain ⟨e, he, hrr⟩ := Array.mem_map.mp hy
    exact Array.mem_map.mpr ⟨e, (Array.mem_filter.mp he).1, hrr⟩

instance : TrustworthinessSpec DnsCache ResourceRecord where
  acceptRrset := DnsCache.storeChecked
  answers := DnsCache.lookupAnswerable

/-- Attach a SOA record to the matching fresh negative entry (the one just
    stored with the same key and expiry). Implements the generated
    `NegativeAuthoritySpec.storeSoaRecord` ("... the amount of time it was
    stored in the cache"). -/
def DnsCache.setNegativeSoa (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (soa : ResourceRecord) (expiry : UInt32) : DnsCache :=
  { c with negatives := c.negatives.map fun e =>
      if nameEqCI e.name name && e.qtype == qtype && e.qclass == qclass
          && e.expiry == expiry then
        { e with soa := some soa }
      else e }

instance : NegativeCacheSpec DnsCache where
  cacheNegative c name qtype qclass rc expiry :=
    DnsCache.storeNegative c name qtype qclass rc none expiry
  retrieveNegative := DnsCache.lookupNegative

instance : NegativeAuthoritySpec DnsCache ResourceRecord where
  storeSoaRecord := DnsCache.setNegativeSoa
  authoritySection := DnsCache.lookupNegativeSoa

instance instRRParseResourceRecord : RRParse ResourceRecord where
  parseRaw bytes := match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) => some rr | .error _ => none
  rrType rr := rr.type
  rrRdata rr := rr.rdata
  rrBytes rr := DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr)
  rrName rr := rr.name

end VeriDNS.Impl.Cache
