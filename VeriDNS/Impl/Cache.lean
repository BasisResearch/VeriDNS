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

/-- Store an RR with absolute expiry = now + ttl; evicts FIFO at capacity.

    RFC 1035 §7.4 all-or-none applies at RRset granularity: a multi-record
    set (e.g. 4 A records) arrives as one batch sharing `expiry`
    (RFC 2181 §5.2: RRs of an RRset have equal TTLs). Storing a member
    replaces same-key entries from OTHER batches (different expiry — a
    stale set is never merged with the new one) and any identical
    re-stored record, but keeps same-batch siblings, so the whole set
    survives. -/
def DnsCache.store (c : DnsCache) (rr : ResourceRecord) (now : UInt32)
    (cred : Trustworthiness := .additionalAuthoritative) : DnsCache :=
  let expiry := now + rr.ttl.toNat.toUInt32
  let entry : CacheEntry := ⟨rr, expiry, false, cred⟩
  let records := c.records.filter fun e =>
    !(nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
      && (e.expiry != expiry || e.rr.rdata == rr.rdata))
  { c with records := (boundFifo records).push entry }

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
  let betterExists := c.records.any fun e =>
    nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
      && e.expiry > now && e.credibility.toCode < cred.toCode
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
    if nameEqCI e.rr.name name && e.rr.type == qtype && e.rr.class == qclass && e.expiry > now then
      some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
    else
      none

/-- The per-entry answerability test (RFC 2181 §5.4.1): key match, fresh,
    and strictly more trustworthy than the floor. Single source of truth —
    used by `lookupAnswerable` and instantiating `returnedAsAnswer` in the
    generated `obligation_untrustworthyNotAnswerable`. -/
def answerableEntry (e : CacheEntry) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) : Bool :=
  nameEqCI e.rr.name name && e.rr.type == qtype && e.rr.class == qclass
    && e.expiry > now && e.credibility.toCode < untrustworthyFloor

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

/-- Remove expired entries (positive and negative). -/
def DnsCache.sweep (c : DnsCache) (now : UInt32) : DnsCache :=
  { records := c.records.filter fun e => e.expiry > now
    negatives := c.negatives.filter fun e => e.expiry > now }

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
  store_mem c rr := store_mem_aux c rr 0
  storeAt_mem := store_mem_aux
  sweep_subset c t y hy := by
    unfold DnsCache.sweep at hy
    obtain ⟨e, he, hrr⟩ := Array.mem_map.mp hy
    exact Array.mem_map.mpr ⟨e, (Array.mem_filter.mp he).1, hrr⟩

instance : CacheLookup DnsCache ResourceRecord where
  lookup := DnsCache.lookup
  storeRanked := DnsCache.storeChecked
  lookupAnswerable := DnsCache.lookupAnswerable

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

instance : RRParse ResourceRecord where
  parseRaw bytes := match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) => some rr | .error _ => none
  rrType rr := rr.type
  rrRdata rr := rr.rdata
  rrBytes rr := DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr)
  rrName rr := rr.name

end VeriDNS.Impl.Cache
