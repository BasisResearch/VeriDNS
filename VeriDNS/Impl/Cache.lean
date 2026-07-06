import VeriDNS.Spec.Resolver
import VeriDNS.Spec.ResourceRecord
import VeriDNS.Spec.Credibility
import VeriDNS.Spec.NegativeCache
import VeriDNS.Impl.ResourceRecord

namespace VeriDNS.Impl.Cache

open VeriDNS.Spec
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase)

def untrustworthyFloor : Nat :=
  Trustworthiness.toCode .additionalAuthoritative

structure CacheEntry where
  rr : ResourceRecord
  expiry : UInt32
  authoritative : Bool
  credibility : Trustworthiness := .additionalAuthoritative
  deriving Inhabited

def CacheEntry.fresh (e : CacheEntry) (now : UInt32) : Bool :=
  e.expiry > now

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

def DnsCache.capacity : Nat := 4096

private def boundFifo {α : Type} (a : Array α) : Array α :=
  if a.size ≥ DnsCache.capacity then a.extract (a.size + 1 - DnsCache.capacity) a.size
  else a

def DnsCache.store (c : DnsCache) (rr : ResourceRecord) (now : UInt32)
    (cred : Trustworthiness := .additionalAuthoritative) : DnsCache :=
  let expiry := now + rr.ttl.toNat.toUInt32
  let entry : CacheEntry := ⟨rr, expiry, false, cred⟩
  let records := c.records.filter fun e =>
    !(nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
      && (e.expiry != expiry || e.rr.rdata == rr.rdata))
  { c with records := records.push entry }

def DnsCache.storeChecked (c : DnsCache) (rr : ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) : DnsCache :=

  if rr.ttl == 0 then c
  else

    let expiry := now + rr.ttl.toNat.toUInt32
    let betterExists := c.records.any fun e =>
      nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry > now || e.expiry == expiry)
        && e.credibility.toCode < cred.toCode
    if betterExists then c else DnsCache.store c rr now cred

def DnsCache.storeNegative (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (rcode : Rcode) (soa : Option ResourceRecord) (expiry : UInt32) : DnsCache :=
  let negatives := c.negatives.filter fun e =>
    !(nameEqCI e.name name && e.qclass == qclass
      && (rcode == Rcode.nameError || e.qtype == qtype))
  { c with negatives := (boundFifo negatives).push ⟨name, qtype, qclass, rcode, expiry, soa⟩ }

def DnsCache.lookupNxdomain (c : DnsCache) (name : ByteArray) (qclass : BitVec 16)
    (now : UInt32) : Option Rcode :=
  c.negatives.findSome? fun e =>
    if nameEqCI e.name name && e.qclass == qclass && e.expiry > now
        && e.rcode == Rcode.nameError then
      some e.rcode
    else none

def DnsCache.lookupNegative (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Option Rcode :=
  (c.lookupNxdomain name qclass now) <|>
    c.negatives.findSome? fun e =>
      if nameEqCI e.name name && e.qtype == qtype && e.qclass == qclass && e.expiry > now then
        some e.rcode
      else none

def liveEntry (e : CacheEntry) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Bool :=
  nameEqCI e.rr.name name && e.rr.type == qtype && e.rr.class == qclass
    && e.fresh now

def DnsCache.lookup (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32)
    : Array ResourceRecord :=
  c.records.filterMap fun e =>
    if liveEntry e name qtype qclass now then
      some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
    else
      none

def answerableEntry (e : CacheEntry) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Bool :=
  liveEntry e name qtype qclass now
    && e.credibility.toCode < untrustworthyFloor

def sameRRKey (a b : CacheEntry) : Bool :=
  nameEqCI a.rr.name b.rr.name && a.rr.type == b.rr.type && a.rr.class == b.rr.class

def DnsCache.maxCredForKey (c : DnsCache) (e : CacheEntry) (name : ByteArray)
    (qtype qclass : BitVec 16) (now : UInt32) : Bool :=
  c.records.all fun e2 =>
    !(answerableEntry e2 name qtype qclass now && sameRRKey e2 e)
      || e.credibility.toCode ≤ e2.credibility.toCode

def DnsCache.lookupAnswerable (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Array ResourceRecord :=
  c.records.filterMap fun e =>
    if answerableEntry e name qtype qclass now && c.maxCredForKey e name qtype qclass now then
      some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
    else
      none

/-- **Per-key max-credibility gate WITHOUT the answer floor** — the SLIST-building analogue of `maxCredForKey`.
    Building the SLIST is not *answering*, so even non-answerable (low-credibility, e.g. additional-section glue)
    records may be used to reach servers (RFC 1034 §5.3.3); only the per-key max-credibility ranking applies
    (RFC 2181 §5.4.1). Mirrors the model's `Cache.topServed` gate (max rank over the live matching records, no
    `usable` filter), in contrast to `maxCredForKey`/`lookupAnswerable` which add the answer floor (`= served`). -/
def DnsCache.maxRankForKey (c : DnsCache) (e : CacheEntry) (now : UInt32) : Bool :=
  c.records.all fun e2 =>
    !(e2.fresh now && sameRRKey e2 e) || e.credibility.toCode ≤ e2.credibility.toCode

/-- **Credibility-aware SLIST lookup** — live matching records at per-key MAX credibility (no answer floor).
    The impl counterpart of `Cache.topServed`: a real resolver builds its SLIST preferring the most-credible
    address per nameserver, yet still uses low-credibility glue to reach servers. Used by `stepFindServers`
    (replacing the raw `lookup`, which ignored credibility entirely — the under-faithful behavior). -/
def DnsCache.lookupTopCred (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Array ResourceRecord :=
  c.records.filterMap fun e =>
    if liveEntry e name qtype qclass now && c.maxRankForKey e now then
      some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
    else
      none

def NegativeEntry.authority (e : NegativeEntry) (now : UInt32) : Array ResourceRecord :=
  match e.soa with
  | some rr => #[{ rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }]
  | none => #[]

def DnsCache.findNegative (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Option NegativeEntry :=
  (c.negatives.find? fun e =>
    nameEqCI e.name name && e.qclass == qclass && e.expiry > now
      && e.rcode == Rcode.nameError)
  <|> c.negatives.find? fun e =>
    nameEqCI e.name name && e.qtype == qtype && e.qclass == qclass && e.expiry > now

def DnsCache.lookupNegativeSoa (c : DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Array ResourceRecord :=
  match c.findNegative name qtype qclass now with
  | some e => e.authority now
  | none => #[]

def DnsCache.sweep (c : DnsCache) (now : UInt32) : DnsCache :=
  { records := c.records.filter fun e => e.fresh now
    negatives := c.negatives.filter fun e => e.expiry > now }

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
  lookupTopCred := DnsCache.lookupTopCred
  store_mem c rr := store_mem_aux c rr 0
  storeAt_mem := store_mem_aux
  sweep_subset c t y hy := by
    unfold DnsCache.sweep at hy
    obtain ⟨e, he, hrr⟩ := Array.mem_map.mp hy
    exact Array.mem_map.mpr ⟨e, (Array.mem_filter.mp he).1, hrr⟩

instance : TrustworthinessSpec DnsCache ResourceRecord where
  acceptRrset := DnsCache.storeChecked
  answers := DnsCache.lookupAnswerable

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

/-! ### RRset TTL normalization (RFC 2181 §5.2)

    The wire may carry an RRset whose members have differing TTLs. Storing them one-at-a-time
    through `store` would evict same-key members with a differing expiry (`Removes`), collapsing a
    legal non-uniform-TTL RRset to a single record. RFC 2181 §5.2 permits treating such an RRset as
    if every TTL equalled the **minimum** over the set. `normalizeRRsetTtls` rewrites each member's
    `ttl` to that per-key minimum *before* the write, so every same-key member shares one expiry and
    `store` keeps them all. The min (not the incoming TTL) never over-caches and never revives an
    expired member. -/

def rrSameKeyB (a b : ResourceRecord) : Bool :=
  nameEqCI a.name b.name && a.type == b.type && a.class == b.class

def minTtlB (x y : BitVec 32) : BitVec 32 := if y.toNat < x.toNat then y else x

/-- The minimum `ttl` over every member of `rrs` sharing `rr`'s `(name,type,class)` key (seeded with
    `rr.ttl`, so when `rr ∈ rrs` this is exactly the per-key minimum). -/
def groupMinTtl (rrs : List ResourceRecord) (rr : ResourceRecord) : BitVec 32 :=
  rrs.foldl (fun acc e => if rrSameKeyB e rr then minTtlB acc e.ttl else acc) rr.ttl

/-- Rewrite every member's `ttl` to the per-key minimum over the section — the RFC 2181 §5.2
    normalization. Preserves the member *set* (only `ttl` changes). -/
def normalizeRRsetTtls (rrs : List ResourceRecord) : List ResourceRecord :=
  rrs.map (fun rr => { rr with ttl := groupMinTtl rrs rr })

/-- The parsed records of a raw section (the unparseable dropped, as `cacheRRs` does). Uses the same
    concrete decode as the `RRParse ResourceRecord` instance (so it is defeq to
    `filterMap RRParse.parseRaw`), stated pre-instance to break the `normalizeSection` cycle. -/
def rrsOf (raws : Array ByteArray) : List ResourceRecord :=
  raws.toList.filterMap (fun b => match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
    | .ok (rr, _) => some rr | .error _ => none)

/-- The wire image of the TTL-normalized section: parse every raw, drop the unparseable, normalize
    per-key TTLs, and re-serialize. Feeding this to the unchanged `cacheRRs` gives a write whose
    same-key members all share one expiry — the RFC 2181 §5.2 fix, expressed as a pure pre-pass on
    the raw section so the store layer (and `OneExpiryPerKey`) is untouched. -/
def normRaws (raws : Array ByteArray) : Array ByteArray :=
  ((normalizeRRsetTtls (rrsOf raws)).map
    (fun rr => DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr))).toArray

instance instRRParseResourceRecord : RRParse ResourceRecord where
  parseRaw bytes := match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) => some rr | .error _ => none
  rrType rr := rr.type
  rrRdata rr := rr.rdata
  rrBytes rr := DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr)
  rrName rr := rr.name
  normalizeSection := normRaws

end VeriDNS.Impl.Cache
