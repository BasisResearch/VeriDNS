import VeriDNS.Proof.MessageValid
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Server

/-!
# W0 — the ingress parser as the single trust root

There are two record decoders:

* `Impl.Message.decodeRRCanonical` — the only ingress path (per record inside
  `Impl.Message.decode`).  It decompresses every embedded name, re-serialises
  the record into a canonical pointer-free blob, and checks rdlength for the
  name-bearing types (NS/CNAME/PTR/SOA/MX/SRV).
* `Impl.ResourceRecord.decode` — the lenient internal decoder that runs
  afterwards (cache `parseRaw`, resolver, server) on blobs the ingress parser
  already produced.

This module makes the informal fact "the internal decoder only ever sees
ingress outputs" a theorem-shaped interface:

* `CanonicalRaw b` pins the exact byte shape the internal decoder is safe on:
  `b` is an `rrWire` image — an expanded (pointer-free) owner name of valid
  labels (each 1..63 bytes, total wire form ≤ 255), a 10-byte fixed part whose
  rdlength field is exactly `rdata.size`, and a type-canonical rdata
  (`Proof.Message.CanonicalRdata`: expanded names for NS/CNAME/PTR/SOA/MX/SRV,
  size < 65536 always).  `Proof.Message.run_decodeRRCanonical_shape` proves
  every `decodeRRCanonical` output has this shape, so `CanonicalRaw` is
  equivalently "is an ingress-parser output".

* `CanonicalRecord rr` is the record-level image: the decoded form of a
  canonical blob.  `encode` maps `CanonicalRecord` records to `CanonicalRaw`
  blobs and `ResourceRecord.decode` is a total inverse
  (`decode_ok_of_canonicalRaw`, `parseRaw_of_canonicalRaw`).

* `CacheRawsCanonical` is the store-side invariant: every record in the cache
  (positive entries and negative-entry SOAs) is `CanonicalRecord`, so every
  blob the resolver re-derives from the cache via `rrBytes` is `CanonicalRaw`.
  It is established at ingest (`cacheRRs`/`cacheUnlessTruncated` on decoded
  message sections) and preserved by every cache writer, including the
  LRU/eviction paths.

Wrapper corollary (`decoders_agree_of_canonicalRaw`): on its actual domain the
ingress decoder is the identity on blobs, and the internal decoder followed by
re-encoding is that same identity — either decoder is expressible as a wrapper
of the other on `CanonicalRaw`.  We record the corollary; deleting one decoder
is left as a follow-up.
-/

namespace VeriDNS.Proof.CanonicalRaw

open VeriDNS.Impl
open VeriDNS.Spec

private theorem ba_append_assoc (a b c : ByteArray) : a ++ b ++ c = a ++ (b ++ c) := by
  ext1; simp [ByteArray.data_append, Array.append_assoc]

private theorem ba_empty_append (a : ByteArray) : ByteArray.empty ++ a = a := by
  ext1; simp

private theorem ba_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  ext1; simp

/-- The exact byte shape the internal (lenient) decoder is safe on: an encode
image of a canonical record.  This is definitionally
`Proof.Message.CanonicalRR`, the shape proven of every `decodeRRCanonical`
output by `Proof.Message.run_decodeRRCanonical_shape`. -/
abbrev CanonicalRaw (b : ByteArray) : Prop := Proof.Message.CanonicalRR b

/-- Every ingress-parser output is a canonical raw (re-export of
`run_decodeRRCanonical_shape` under the W0 name). -/
theorem decodeRRCanonical_canonicalRaw {buf : ByteArray} {pos : Nat}
    {out : ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.Message.decodeRRCanonical buf pos = .ok (out, pos')) :
    CanonicalRaw out :=
  Proof.Message.run_decodeRRCanonical_shape h

/-- Record-level canonicality: the decoded form of a canonical blob.  The
owner name is an expanded wire form of valid labels (≤ 255 bytes), the rdata
is type-canonical, and the rdlength field agrees with the rdata content. -/
def CanonicalRecord (rr : VeriDNS.Spec.ResourceRecord) : Prop :=
  (∃ ls : Array ByteArray, Proof.DomainName.ValidLabels ls ∧
      (Impl.DomainName.labelsToWireFormat ls).size ≤ 255 ∧
      Impl.DomainName.labelsToWireFormat ls = rr.name) ∧
  Proof.Message.CanonicalRdata rr.type rr.rdata ∧
  rr.rdlength = BitVec.ofNat 16 rr.rdata.size

theorem canonicalRecord_rdlength_toNat {rr : VeriDNS.Spec.ResourceRecord}
    (h : CanonicalRecord rr) : rr.rdlength.toNat = rr.rdata.size := by
  rw [h.2.2, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Proof.Message.canonicalRdata_size_lt h.2.1)

/-- A ttl rewrite (cache expiry adjustment, RRset ttl normalisation, negative
ttl computation) preserves record canonicality. -/
theorem canonicalRecord_withTtl {rr : VeriDNS.Spec.ResourceRecord}
    (h : CanonicalRecord rr) (x : BitVec 32) :
    CanonicalRecord { rr with ttl := x } :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- `ResourceRecord.encode` unfolds to the `rrWire` byte decomposition. -/
theorem encode_eq_wire (rr : VeriDNS.Spec.ResourceRecord) :
    DnsSerializer.runBytes (Impl.ResourceRecord.encode rr)
      = rr.name ++ (Proof.Message.rrFixed rr.type rr.class rr.ttl rr.rdlength ++ rr.rdata) :=
  Proof.Message.rrWire_encoder rr.name rr.type rr.class rr.ttl rr.rdlength rr.rdata

theorem encode_eq_rrWire {rr : VeriDNS.Spec.ResourceRecord} {ls : Array ByteArray}
    (hname : Impl.DomainName.labelsToWireFormat ls = rr.name)
    (hrl : rr.rdlength = BitVec.ofNat 16 rr.rdata.size) :
    DnsSerializer.runBytes (Impl.ResourceRecord.encode rr)
      = Proof.Message.rrWire ls rr.type rr.class rr.ttl rr.rdata := by
  rw [encode_eq_wire, Proof.Message.rrWire, hname, hrl]

/-- Encoding a canonical record yields a canonical raw: the store-to-wire
direction.  Every blob the resolver re-derives from a canonical record via
`RRParse.rrBytes` is in the internal decoder's safe domain. -/
theorem canonicalRaw_encode {rr : VeriDNS.Spec.ResourceRecord}
    (h : CanonicalRecord rr) :
    CanonicalRaw (DnsSerializer.runBytes (Impl.ResourceRecord.encode rr)) := by
  obtain ⟨⟨ls, hv, hle, hname⟩, hrd, hrl⟩ := h
  exact ⟨ls, rr.type, rr.class, rr.ttl, rr.rdata, hv, hle, hrd,
    encode_eq_rrWire hname hrl⟩

/-- TOTALITY + ROUND-TRIP: on a canonical raw the internal decoder succeeds,
consumes the whole blob, returns a canonical record, and re-encoding that
record restores the blob exactly — `ResourceRecord.decode` is the inverse of
`ResourceRecord.encode` on `CanonicalRaw`. -/
theorem decode_ok_of_canonicalRaw {b : ByteArray} (h : CanonicalRaw b) :
    ∃ rr : VeriDNS.Spec.ResourceRecord,
      DnsParser.run Impl.ResourceRecord.decode b = .ok (rr, b.size)
      ∧ CanonicalRecord rr
      ∧ DnsSerializer.runBytes (Impl.ResourceRecord.encode rr) = b := by
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl⟩ := h
  have hrun := Proof.Message.run_resourceRecordDecode_rrWire ls hv hle t c ttl rdata
    (Proof.Message.canonicalRdata_size_lt hrd) ByteArray.empty ByteArray.empty
  rw [ba_append_empty, ba_empty_append] at hrun
  simp only [ByteArray.size_empty, Nat.zero_add] at hrun
  refine ⟨_, hrun, ⟨⟨ls, hv, hle, rfl⟩, hrd, rfl⟩, ?_⟩
  exact encode_eq_rrWire rfl rfl

/-- Determinism corollary: whatever record the internal decoder returns on a
canonical raw, re-encoding it restores the blob and the parse consumed the
whole blob. -/
theorem decode_inverse_of_canonicalRaw {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} {pos' : Nat} (hb : CanonicalRaw b)
    (h : DnsParser.run Impl.ResourceRecord.decode b = .ok (rr, pos')) :
    DnsSerializer.runBytes (Impl.ResourceRecord.encode rr) = b
      ∧ pos' = b.size ∧ CanonicalRecord rr := by
  obtain ⟨rr0, hrun, hcan, henc⟩ := decode_ok_of_canonicalRaw hb
  rw [hrun] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
  subst h1; subst h2
  exact ⟨henc, rfl, hcan⟩

/-- `RRParse.parseRaw` (the cache/resolver entry point of the internal
decoder) is total on canonical raws, and `RRParse.rrBytes` is its inverse. -/
theorem parseRaw_of_canonicalRaw {b : ByteArray} (h : CanonicalRaw b) :
    ∃ rr : VeriDNS.Spec.ResourceRecord,
      RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
      ∧ RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr = b
      ∧ CanonicalRecord rr := by
  obtain ⟨rr, hrun, hcan, henc⟩ := decode_ok_of_canonicalRaw h
  refine ⟨rr, ?_, henc, hcan⟩
  show (match DnsParser.run Impl.ResourceRecord.decode b with
    | .ok (rr, _) => some rr | .error _ => none) = some rr
  rw [hrun]

/-- Whatever record `parseRaw` returns on a canonical raw is canonical and
re-encodes to the blob. -/
theorem parseRaw_inverse_of_canonicalRaw {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} (hb : CanonicalRaw b)
    (h : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr = b
      ∧ CanonicalRecord rr := by
  obtain ⟨rr0, hp, henc, hcan⟩ := parseRaw_of_canonicalRaw hb
  rw [hp] at h
  obtain rfl := Option.some.inj h
  exact ⟨henc, hcan⟩

/-- On its actual domain the ingress decoder is the identity on blobs
(specialisation of `rrWire_frame` to the unframed blob). -/
theorem decodeRRCanonical_id_of_canonicalRaw {b : ByteArray} (h : CanonicalRaw b) :
    DnsParser.run Impl.Message.decodeRRCanonical b = .ok (b, b.size) := by
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl⟩ := h
  have hrun := Proof.Message.rrWire_frame ls hv hle t c ttl rdata hrd
    ByteArray.empty ByteArray.empty
  rw [ba_append_empty, ba_empty_append] at hrun
  simpa only [ByteArray.size_empty, Nat.zero_add] using hrun

/-- WRAPPER COROLLARY: on canonical blobs the two decoders determine each
other — the ingress decoder equals the internal decoder followed by
re-encoding.  On its actual domain the lenient decoder is provably equivalent
to the validating one; either can be expressed as a wrapper of the other
(deletion of one is a recorded follow-up, not done here). -/
theorem decoders_agree_of_canonicalRaw {b : ByteArray} (h : CanonicalRaw b) :
    DnsParser.run Impl.Message.decodeRRCanonical b
      = (DnsParser.run Impl.ResourceRecord.decode b).map
          (fun x => (DnsSerializer.runBytes (Impl.ResourceRecord.encode x.1), x.2)) := by
  obtain ⟨rr, hrun, _, henc⟩ := decode_ok_of_canonicalRaw h
  rw [decodeRRCanonical_id_of_canonicalRaw h, hrun]
  simp only [Except.map, henc]

/-! ## Message sections are canonical raws

Every record blob in a decoded message is an ingress-parser output, hence
`CanonicalRaw` (re-exports of the `MessageValid` section theorems). -/

theorem message_answer_canonicalRaw {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) : ∀ b ∈ f.answer, CanonicalRaw b :=
  Proof.Message.decode_answer_canonicalRR h

theorem message_authority_canonicalRaw {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) : ∀ b ∈ f.authority, CanonicalRaw b :=
  Proof.Message.decode_authority_canonicalRR h

theorem message_additional_canonicalRaw {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) : ∀ b ∈ f.additional, CanonicalRaw b :=
  Proof.Message.decode_additional_canonicalRR h

/-! ## The re-encoding pipeline preserves canonicality -/

theorem rrsOf_canonicalRecord {raws : Array ByteArray}
    (h : ∀ b ∈ raws, CanonicalRaw b) :
    ∀ rr ∈ Impl.Cache.rrsOf raws, CanonicalRecord rr := by
  intro rr hrr
  unfold Impl.Cache.rrsOf at hrr
  obtain ⟨b, hb, hp⟩ := List.mem_filterMap.mp hrr
  obtain ⟨rr0, hrun, hcan, -⟩ := decode_ok_of_canonicalRaw (h b (Array.mem_def.mpr hb))
  rw [hrun] at hp
  exact Option.some.inj hp ▸ hcan

theorem normalizeRRsetTtls_canonicalRecord {rrs : List VeriDNS.Spec.ResourceRecord}
    (h : ∀ rr ∈ rrs, CanonicalRecord rr) :
    ∀ rr ∈ Impl.Cache.normalizeRRsetTtls rrs, CanonicalRecord rr := by
  intro rr hrr
  unfold Impl.Cache.normalizeRRsetTtls at hrr
  obtain ⟨rr0, hrr0, rfl⟩ := List.mem_map.mp hrr
  exact canonicalRecord_withTtl (h rr0 hrr0) _

/-- `normalizeSection` (the TTL-normalising re-encoder that feeds the cache)
maps canonical raws to canonical raws. -/
theorem normRaws_canonicalRaw {raws : Array ByteArray}
    (h : ∀ b ∈ raws, CanonicalRaw b) :
    ∀ b ∈ Impl.Cache.normRaws raws, CanonicalRaw b := by
  intro b hb
  unfold Impl.Cache.normRaws at hb
  rw [List.mem_toArray] at hb
  obtain ⟨rr, hrr, rfl⟩ := List.mem_map.mp hb
  exact canonicalRaw_encode
    (normalizeRRsetTtls_canonicalRecord (rrsOf_canonicalRecord h) rr hrr)

/-! ## The store-side invariant `CacheRawsCanonical`

Every record in the cache — positive entries and the SOA records carried by
negative entries — is `CanonicalRecord`, so every blob the resolver re-derives
from the cache via `RRParse.rrBytes` is `CanonicalRaw` and therefore inside
the internal decoder's proven-safe domain. -/

open VeriDNS.Impl.Cache

def CacheRawsCanonical (c : DnsCache) : Prop :=
  (∀ e ∈ c.records, CanonicalRecord e.rr) ∧
  (∀ n ∈ c.negatives, ∀ rr : VeriDNS.Spec.ResourceRecord,
      n.soa = some rr → CanonicalRecord rr)

theorem cacheRawsCanonical_empty : CacheRawsCanonical DnsCache.empty := by
  constructor
  · intro e he; simp [DnsCache.empty] at he
  · intro n hn; simp [DnsCache.empty] at hn

/-! ### Preservation by every cache writer -/

theorem cacheRawsCanonical_store {c : DnsCache} (hc : CacheRawsCanonical c)
    {rr : VeriDNS.Spec.ResourceRecord} (hrr : CanonicalRecord rr)
    (now : UInt32) (cred : Trustworthiness) :
    CacheRawsCanonical (c.store rr now cred) := by
  refine ⟨?_, hc.2⟩
  intro e he
  simp only [DnsCache.store] at he
  rcases Array.mem_push.mp he with he | rfl
  · exact hc.1 e (Array.mem_filter.mp he).1
  · exact hrr

theorem cacheRawsCanonical_storeChecked {c : DnsCache} (hc : CacheRawsCanonical c)
    {rr : VeriDNS.Spec.ResourceRecord} (hrr : CanonicalRecord rr)
    (cred : Trustworthiness) (now : UInt32) :
    CacheRawsCanonical (c.storeChecked rr cred now) := by
  simp only [DnsCache.storeChecked]
  split
  · exact hc
  · split
    · exact hc
    · exact cacheRawsCanonical_store hc hrr now cred

theorem cacheRawsCanonical_storeNegative {c : DnsCache} (hc : CacheRawsCanonical c)
    {name : ByteArray} {qtype qclass : BitVec 16} {rcode : Rcode}
    {soa : Option VeriDNS.Spec.ResourceRecord}
    (hsoa : ∀ rr, soa = some rr → CanonicalRecord rr) (expiry now : UInt32) :
    CacheRawsCanonical (c.storeNegative name qtype qclass rcode soa expiry now) := by
  refine ⟨hc.1, ?_⟩
  intro n hn
  simp only [DnsCache.storeNegative] at hn
  rcases Array.mem_push.mp hn with hn | rfl
  · exact hc.2 n (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hn)).1
  · exact hsoa

theorem cacheRawsCanonical_setNegativeSoa {c : DnsCache} (hc : CacheRawsCanonical c)
    {name : ByteArray} {qtype qclass : BitVec 16}
    {soa : VeriDNS.Spec.ResourceRecord} (hsoa : CanonicalRecord soa)
    (expiry : UInt32) :
    CacheRawsCanonical (c.setNegativeSoa name qtype qclass soa expiry) := by
  refine ⟨hc.1, ?_⟩
  intro n hn rr hrr
  simp only [DnsCache.setNegativeSoa] at hn
  obtain ⟨n0, hn0, rfl⟩ := Array.mem_map.mp hn
  split at hrr
  · exact Option.some.inj hrr ▸ hsoa
  · exact hc.2 n0 hn0 rr hrr

theorem cacheRawsCanonical_sweep {c : DnsCache} (hc : CacheRawsCanonical c)
    (now : UInt32) : CacheRawsCanonical (c.sweep now) := by
  refine ⟨?_, ?_⟩
  · intro e he
    exact hc.1 e (Array.mem_filter.mp he).1
  · intro n hn
    exact hc.2 n (Array.mem_filter.mp hn).1

theorem cacheRawsCanonical_boundExpiryClasses {c : DnsCache}
    (hc : CacheRawsCanonical c) : CacheRawsCanonical c.boundExpiryClasses := by
  refine ⟨?_, hc.2⟩
  intro e he
  exact hc.1 e (mem_of_mem_evictClasses he)

theorem cacheRawsCanonical_touchKeys {c : DnsCache} (hc : CacheRawsCanonical c)
    (ks : Array RRKey) (now : UInt32) :
    CacheRawsCanonical (c.touchKeys ks now) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [touchKeys_records] at he
    obtain ⟨e0, he0, rfl⟩ := Array.mem_map.mp he
    rw [touchEntry_rr]
    exact hc.1 e0 he0
  · intro n hn rr hrr
    rw [touchKeys_negatives] at hn
    obtain ⟨n0, hn0, rfl⟩ := Array.mem_map.mp hn
    rw [touchNegEntry_soa] at hrr
    exact hc.2 n0 hn0 rr hrr

theorem cacheRawsCanonical_boundLruKeys {c : DnsCache}
    (hc : CacheRawsCanonical c) : CacheRawsCanonical c.boundLruKeys := by
  refine ⟨?_, hc.2⟩
  intro e he
  exact hc.1 e (mem_of_mem_evictLruKeys he)

/-- The read-LRU eviction path (touch + whole-key eviction) preserves the
invariant. -/
theorem cacheRawsCanonical_boundLru {c : DnsCache} (hc : CacheRawsCanonical c)
    (touches : Array RRKey) (now : UInt32) :
    CacheRawsCanonical (c.boundLru touches now) :=
  cacheRawsCanonical_boundLruKeys (cacheRawsCanonical_touchKeys hc touches now)

private theorem list_foldl_preserves {α β : Type} (P : β → Prop) (Q : α → Prop)
    (f : β → α → β) (hf : ∀ c a, P c → Q a → P (f c a)) :
    ∀ (l : List α) (c : β), P c → (∀ a ∈ l, Q a) → P (l.foldl f c)
  | [], _, hc, _ => hc
  | a :: l, c, hc, hl =>
    list_foldl_preserves P Q f hf l (f c a)
      (hf c a hc (hl a (List.mem_cons_self ..)))
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem cacheRawsCanonical_absorb {base new : DnsCache}
    (hb : CacheRawsCanonical base) (hn : CacheRawsCanonical new) :
    CacheRawsCanonical (base.absorb new) := by
  unfold DnsCache.absorb
  refine cacheRawsCanonical_boundExpiryClasses ?_
  have hrecs : CacheRawsCanonical (new.records.foldl (fun c e =>
      { c with records := (c.records.filter fun e2 =>
          !(Impl.DomainName.nameEqCI e2.rr.name e.rr.name && e2.rr.type == e.rr.type
            && e2.rr.class == e.rr.class
            && (e2.expiry != e.expiry || rdataEqCI e.rr.type e2.rr.rdata e.rr.rdata))).push e }) base) := by
    rw [← Array.foldl_toList]
    refine list_foldl_preserves CacheRawsCanonical (fun e => CanonicalRecord e.rr) _
      ?_ _ _ hb (fun e he => hn.1 e (Array.mem_def.mpr he))
    intro c e hc he
    refine ⟨?_, hc.2⟩
    intro e2 he2
    rcases Array.mem_push.mp he2 with he2 | rfl
    · exact hc.1 e2 (Array.mem_filter.mp he2).1
    · exact he
  rw [← Array.foldl_toList]
  refine list_foldl_preserves CacheRawsCanonical
    (fun n => ∀ rr, n.soa = some rr → CanonicalRecord rr) _ ?_ _ _ hrecs
    (fun n hnn => hn.2 n (Array.mem_def.mpr hnn))
  intro c n hc hns
  refine ⟨hc.1, ?_⟩
  intro n2 hn2
  rcases Array.mem_push.mp hn2 with hn2 | rfl
  · exact hc.2 n2 (Array.mem_filter.mp hn2).1
  · exact hns

/-! ### Established at ingest

`cacheRRs` (instantiated at the executable cache) only stores `parseRaw`
outputs of the raws it is given; when those raws are canonical — as every
section of a decoded message is — the invariant is preserved. -/

theorem cacheRawsCanonical_cacheRRs {cache : DnsCache} (hc : CacheRawsCanonical cache)
    {raws : Array ByteArray} (hraws : ∀ b ∈ raws, CanonicalRaw b)
    (cred : Trustworthiness) (now : UInt32) :
    CacheRawsCanonical
      (Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  unfold Resolver.cacheRRs
  rw [← Array.foldl_toList]
  refine list_foldl_preserves CacheRawsCanonical CanonicalRaw _ ?_ _ _ hc
    (fun b hb => hraws b (Array.mem_def.mpr hb))
  intro c b hcc hb
  cases hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => exact hcc
  | some rr =>
    have hcanrr := (parseRaw_inverse_of_canonicalRaw hb hp).2
    show CacheRawsCanonical (c.storeChecked rr cred now)
    exact cacheRawsCanonical_storeChecked hcc hcanrr cred now

/-- At the executable instance, `normalizeSection` is `normRaws`. -/
theorem normalizeSection_eq_normRaws (raws : Array ByteArray) :
    RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws
      = Impl.Cache.normRaws raws := rfl

/-- The response-caching entry point preserves the invariant whenever the
section raws are canonical (which `message_*_canonicalRaw` supplies for every
freshly decoded message). -/
theorem cacheRawsCanonical_cacheUnlessTruncated {cache : DnsCache}
    (hc : CacheRawsCanonical cache) {resp : VeriDNS.Spec.Format}
    {raws : Array ByteArray} (hraws : ∀ b ∈ raws, CanonicalRaw b)
    (cred : Trustworthiness) (now : UInt32) :
    CacheRawsCanonical
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        cache resp raws cred now) := by
  unfold Resolver.cacheUnlessTruncated
  split
  · exact hc
  · rw [normalizeSection_eq_normRaws]
    exact cacheRawsCanonical_cacheRRs hc (normRaws_canonicalRaw hraws) cred now

/-! ### Cache reads deliver canonical records

Everything the cache hands back to the resolver (positive lookups at any
credibility gate, and negative-entry SOA authority) is a canonical record, so
its `rrBytes` re-encoding — the only way a cache read becomes a raw again — is
`CanonicalRaw` (via `canonicalRaw_encode`). -/

theorem lookup_canonicalRecord {c : DnsCache} (hc : CacheRawsCanonical c)
    (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ rr ∈ c.lookup name qtype qclass now, CanonicalRecord rr := by
  intro rr hrr
  unfold DnsCache.lookup at hrr
  obtain ⟨e, he, heq⟩ := Array.mem_filterMap.mp hrr
  split at heq
  · exact Option.some.inj heq ▸ canonicalRecord_withTtl (hc.1 e he) _
  · cases heq

theorem lookupAnswerable_canonicalRecord {c : DnsCache} (hc : CacheRawsCanonical c)
    (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ rr ∈ c.lookupAnswerable name qtype qclass now, CanonicalRecord rr := by
  intro rr hrr
  unfold DnsCache.lookupAnswerable at hrr
  obtain ⟨e, he, heq⟩ := Array.mem_filterMap.mp hrr
  split at heq
  · exact Option.some.inj heq ▸ canonicalRecord_withTtl (hc.1 e he) _
  · cases heq

theorem lookupTopCred_canonicalRecord {c : DnsCache} (hc : CacheRawsCanonical c)
    (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ rr ∈ c.lookupTopCred name qtype qclass now, CanonicalRecord rr := by
  intro rr hrr
  unfold DnsCache.lookupTopCred at hrr
  obtain ⟨e, he, heq⟩ := Array.mem_filterMap.mp hrr
  split at heq
  · exact Option.some.inj heq ▸ canonicalRecord_withTtl (hc.1 e he) _
  · cases heq

private theorem option_orElse_eq_some {α : Type} {x y : Option α} {n : α}
    (h : (x <|> y) = some n) : x = some n ∨ y = some n := by
  cases x with
  | some a => simp_all
  | none => simp_all

private theorem findNegative_mem {c : DnsCache} {name : ByteArray}
    {qtype qclass : BitVec 16} {now : UInt32} {n : NegativeEntry}
    (h : c.findNegative name qtype qclass now = some n) : n ∈ c.negatives := by
  unfold DnsCache.findNegative at h
  rcases option_orElse_eq_some h with hf | hf <;>
    exact Array.mem_of_find?_eq_some hf

theorem lookupNegativeSoa_canonicalRecord {c : DnsCache} (hc : CacheRawsCanonical c)
    (name : ByteArray) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ rr ∈ c.lookupNegativeSoa name qtype qclass now, CanonicalRecord rr := by
  intro rr hrr
  unfold DnsCache.lookupNegativeSoa at hrr
  split at hrr
  · rename_i n hfind
    have hn : n ∈ c.negatives := findNegative_mem hfind
    unfold NegativeEntry.authority at hrr
    split at hrr
    · rename_i soa hsoa
      rw [Array.mem_singleton] at hrr
      exact hrr ▸ canonicalRecord_withTtl (hc.2 n hn soa hsoa) _
    · simp at hrr
  · simp at hrr

/-! ## Server-side raw pipelines

The remaining places where blobs are (re-)made before reaching the internal
decoder: the TTL-capping sanitiser and the negative-cache SOA extraction. -/

theorem extractSoaNegative_canonicalRecord {qname : ByteArray}
    {authority : Array ByteArray} (hauth : ∀ b ∈ authority, CanonicalRaw b)
    {negTtl : BitVec 32} {soaRR : VeriDNS.Spec.ResourceRecord}
    (h : Impl.Server.extractSoaNegative qname authority = some (negTtl, soaRR)) :
    CanonicalRecord soaRR := by
  unfold Impl.Server.extractSoaNegative at h
  obtain ⟨b, hb, hf⟩ := Array.exists_of_findSome?_eq_some h
  generalize hrr : DnsParser.run Impl.ResourceRecord.decode b = r at hf
  rcases r with e | ⟨rr0, n⟩
  · simp at hf
  · simp only [] at hf
    have hcan := (decode_inverse_of_canonicalRaw (hauth b hb) hrr).2.2
    split at hf
    · generalize hsoa : DnsParser.run Impl.RData.decodeSoa rr0.rdata = rs at hf
      rcases rs with e2 | ⟨soa, n2⟩
      · simp at hf
      · simp only [] at hf
        obtain ⟨-, h2⟩ := Prod.mk.inj (Option.some.inj hf)
        exact h2 ▸ canonicalRecord_withTtl hcan _
    · simp at hf

/-- The negative-cache write built from an extracted (canonical-authority)
SOA preserves the invariant: this is the pure core of the server's
`storeNegativeIfCacheable`. -/
theorem cacheRawsCanonical_storeNegative_soa {base : DnsCache}
    (hb : CacheRawsCanonical base) {qname : ByteArray}
    {authority : Array ByteArray} (hauth : ∀ b ∈ authority, CanonicalRaw b)
    {negTtl : BitVec 32} {soaRR : VeriDNS.Spec.ResourceRecord}
    (hext : Impl.Server.extractSoaNegative qname authority = some (negTtl, soaRR))
    (name : ByteArray) (qtype qclass : BitVec 16) (rcode : Rcode)
    (t : BitVec 32) (expiry now : UInt32) :
    CacheRawsCanonical (base.storeNegative name qtype qclass rcode
      (some { soaRR with ttl := t }) expiry now) := by
  refine cacheRawsCanonical_storeNegative hb ?_ expiry now
  intro rr hsome
  obtain rfl := Option.some.inj hsome
  exact canonicalRecord_withTtl
    (extractSoaNegative_canonicalRecord hauth hext) t

/-- The probe-denial negative store (whole writer) preserves the invariant. -/
theorem cacheRawsCanonical_storeProbeNegative {cache : DnsCache}
    (hc : CacheRawsCanonical cache) {sub resp : VeriDNS.Spec.Format}
    (hauth : ∀ b ∈ resp.authority, CanonicalRaw b) (now : UInt32) :
    CacheRawsCanonical (Impl.Server.storeProbeNegative cache sub resp now) := by
  unfold Impl.Server.storeProbeNegative
  split
  · split
    · rename_i hext
      exact cacheRawsCanonical_storeNegative_soa hc hauth hext _ _ _ _ _ _ _
    · exact hc
  · exact hc

/-- The TTL-capping sanitiser preserves blob canonicality: it either keeps a
blob or re-encodes its parse with a rewritten TTL. -/
theorem capTtlRR_canonicalRaw {b : ByteArray} (h : CanonicalRaw b) :
    CanonicalRaw (Impl.Server.capTtlRR b) := by
  unfold Impl.Server.capTtlRR
  cases hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => exact h
  | some rr =>
    have hcan := (parseRaw_inverse_of_canonicalRaw h hp).2
    show CanonicalRaw (if rr.ttl >>> 31 == 1 then
        DnsSerializer.runBytes (Impl.ResourceRecord.encode { rr with ttl := 0 })
      else if 604800 < rr.ttl.toNat then
        DnsSerializer.runBytes
          (Impl.ResourceRecord.encode { rr with ttl := BitVec.ofNat 32 604800 })
      else b)
    split
    · exact canonicalRaw_encode (canonicalRecord_withTtl hcan 0)
    · split
      · exact canonicalRaw_encode (canonicalRecord_withTtl hcan _)
      · exact h

theorem capTtls_answer_canonicalRaw {resp : VeriDNS.Spec.Format}
    (h : ∀ b ∈ resp.answer, CanonicalRaw b) :
    ∀ b ∈ (Impl.Server.capTtls resp).answer, CanonicalRaw b := by
  intro b hb
  obtain ⟨b0, hb0, rfl⟩ := Array.mem_map.mp hb
  exact capTtlRR_canonicalRaw (h b0 hb0)

theorem capTtls_authority_canonicalRaw {resp : VeriDNS.Spec.Format}
    (h : ∀ b ∈ resp.authority, CanonicalRaw b) :
    ∀ b ∈ (Impl.Server.capTtls resp).authority, CanonicalRaw b := by
  intro b hb
  obtain ⟨b0, hb0, rfl⟩ := Array.mem_map.mp hb
  exact capTtlRR_canonicalRaw (h b0 hb0)

theorem capTtls_additional_canonicalRaw {resp : VeriDNS.Spec.Format}
    (h : ∀ b ∈ resp.additional, CanonicalRaw b) :
    ∀ b ∈ (Impl.Server.capTtls resp).additional, CanonicalRaw b := by
  intro b hb
  obtain ⟨b0, hb0, rfl⟩ := Array.mem_map.mp hb
  exact capTtlRR_canonicalRaw (h b0 hb0)

/-- The full response sanitiser (`stripOpt` then TTL cap), applied to a
freshly decoded upstream message, yields sections of canonical raws — so the
whole post-ingress pipeline stays inside the internal decoder's proven-safe
domain. -/
theorem sanitizeTtlsCap_canonicalRaw {resp resp' : VeriDNS.Spec.Format}
    (hans : ∀ b ∈ resp.answer, CanonicalRaw b)
    (hauth : ∀ b ∈ resp.authority, CanonicalRaw b)
    (hadd : ∀ b ∈ resp.additional, CanonicalRaw b)
    (h : Impl.Server.sanitizeTtlsCap resp = some resp') :
    (∀ b ∈ resp'.answer, CanonicalRaw b) ∧
    (∀ b ∈ resp'.authority, CanonicalRaw b) ∧
    (∀ b ∈ resp'.additional, CanonicalRaw b) := by
  obtain rfl := (Option.some.inj h).symm
  refine ⟨capTtls_answer_canonicalRaw hans,
    capTtls_authority_canonicalRaw hauth,
    capTtls_additional_canonicalRaw ?_⟩
  intro b hb
  exact hadd b (Array.mem_filter.mp hb).1

/-! ## Owner-rewriting pipelines: the answer scrub

`scrubAnswerB` does not merely filter: `setOwnerB` splices a reachable name
onto the record's tail bytes.  Canonicality survives because reachable names
are themselves canonical names (the seed is the client qname, the closure
steps are CNAME rdata of canonical records). -/

/-- A canonical (expanded, pointer-free, ≤ 255 byte) wire-format name. -/
def CanonicalName (nm : ByteArray) : Prop :=
  ∃ ls : Array ByteArray, Proof.DomainName.ValidLabels ls ∧
    (Impl.DomainName.labelsToWireFormat ls).size ≤ 255 ∧
    Impl.DomainName.labelsToWireFormat ls = nm

theorem canonicalRecord_name {rr : VeriDNS.Spec.ResourceRecord}
    (h : CanonicalRecord rr) : CanonicalName rr.name := h.1

/-- A decoded question's qname is a canonical name (bridge from the
`MessageValid` question-shape predicate). -/
theorem questionFromLabels_canonicalName {q : VeriDNS.Spec.Question}
    (h : Proof.Message.QuestionFromLabels q) : CanonicalName q.qname := h

/-- The rdata of a canonical NS/CNAME/PTR record is a canonical name. -/
theorem canonicalRecord_rdata_name {rr : VeriDNS.Spec.ResourceRecord}
    (hcan : CanonicalRecord rr)
    (ht : rr.type = 2 ∨ rr.type = 5 ∨ rr.type = 12) : CanonicalName rr.rdata := by
  obtain ⟨name, type_, cls, ttl, rdl, rdata⟩ := rr
  have hrd := hcan.2.1
  simp only at hrd ht ⊢
  cases hrd with
  | nameType ht' hv hle => exact ⟨_, hv, hle, rfl⟩
  | soa hm hr hlem hler htail =>
    rcases ht with ht | ht | ht <;> simp at ht
  | prefixedName ht' hv hle =>
    rcases ht' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases ht with ht | ht | ht <;> simp at ht
  | other h2 h5 h12 h6 h15 h33 hsz =>
    rcases ht with ht | ht | ht
    · exact absurd ht h2
    · exact absurd ht h5
    · exact absurd ht h12

theorem reachTarget?_canonicalName {reach : Array ByteArray} {bytes tgt : ByteArray}
    (hb : CanonicalRaw bytes)
    (h : Impl.Resolver.reachTarget? (RR := VeriDNS.Spec.ResourceRecord) reach bytes
      = some tgt) :
    CanonicalName tgt := by
  unfold Impl.Resolver.reachTarget? at h
  generalize hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = p at h
  rcases p with _ | rr
  · simp at h
  · simp only [] at h
    split at h
    · rename_i hcond
      have hcan := (parseRaw_inverse_of_canonicalRaw hb hp).2
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      have ht5 : rr.type = 5 := hcond.1
      exact canonicalRecord_rdata_name hcan (Or.inr (Or.inl ht5))
    · cases h

theorem reachStepB_canonicalName {answer reach : Array ByteArray}
    (hans : ∀ b ∈ answer, CanonicalRaw b) (hreach : ∀ m ∈ reach, CanonicalName m) :
    ∀ m ∈ Impl.Resolver.reachStepB (RR := VeriDNS.Spec.ResourceRecord) answer reach,
      CanonicalName m := by
  intro m hm
  unfold Impl.Resolver.reachStepB at hm
  rcases Array.mem_append.mp hm with hm | hm
  · exact hreach m hm
  · obtain ⟨b, hb, hf⟩ := Array.mem_filterMap.mp hm
    exact reachTarget?_canonicalName (hans b hb) hf

theorem reachIterB_canonicalName {answer : Array ByteArray}
    (hans : ∀ b ∈ answer, CanonicalRaw b) :
    ∀ (k : Nat) (reach : Array ByteArray), (∀ m ∈ reach, CanonicalName m) →
      ∀ m ∈ Impl.Resolver.reachIterB (RR := VeriDNS.Spec.ResourceRecord) answer k reach,
        CanonicalName m := by
  intro k
  induction k with
  | zero => intro reach hreach; exact hreach
  | succ k ih =>
    intro reach hreach
    exact ih _ (reachStepB_canonicalName hans hreach)

theorem reachableNamesB_canonicalName {qname : ByteArray} (hq : CanonicalName qname)
    {answer : Array ByteArray} (hans : ∀ b ∈ answer, CanonicalRaw b) :
    ∀ m ∈ Impl.Resolver.reachableNamesB (RR := VeriDNS.Spec.ResourceRecord) qname answer,
      CanonicalName m := by
  intro m hm
  rw [Impl.Resolver.reachableNamesB_eq_iter] at hm
  refine reachIterB_canonicalName hans _ _ ?_ m hm
  intro m' hm'
  rw [Array.mem_singleton] at hm'
  exact hm' ▸ hq

private theorem ba_extract_append (a b : ByteArray) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  ext1
  simp only [ByteArray.data_extract, ByteArray.data_append]
  rw [← Array.toList_inj, Array.toList_extract, Array.toList_append,
      List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  simp only [ByteArray.size, Array.size_eq_length_toList]
  rw [List.drop_left, List.take_length]

/-- The owner-splice of the answer scrub preserves blob canonicality: the new
owner is a canonical name and the tail (fixed part + rdata) is untouched. -/
theorem setOwnerB_canonicalRaw {bytes : ByteArray} (hb : CanonicalRaw bytes)
    {rr : VeriDNS.Spec.ResourceRecord}
    (hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr)
    {m : ByteArray} (hm : CanonicalName m) :
    CanonicalRaw (Impl.Resolver.setOwnerB (RR := VeriDNS.Spec.ResourceRecord) rr bytes m) := by
  obtain ⟨henc, hcan⟩ := parseRaw_inverse_of_canonicalRaw hb hp
  obtain ⟨lsm, hvm, hlem, hwfm⟩ := hm
  have hbytes : bytes
      = rr.name ++ (Proof.Message.rrFixed rr.type rr.class rr.ttl rr.rdlength ++ rr.rdata) := by
    rw [← henc]
    exact encode_eq_wire rr
  show CanonicalRaw (m ++ bytes.extract rr.name.size bytes.size)
  rw [hbytes, ByteArray.size_append, ba_extract_append]
  exact ⟨lsm, rr.type, rr.class, rr.ttl, rr.rdata, hvm, hlem, hcan.2.1, by
    rw [Proof.Message.rrWire, hwfm, ← hcan.2.2]⟩

/-- The delivered-answer scrub preserves blob canonicality: everything the
server hands back to the client (and everything a CNAME chain carries) stays
inside the internal decoder's proven-safe domain. -/
theorem scrubAnswerB_canonicalRaw {qname : ByteArray} (hq : CanonicalName qname)
    {answer : Array ByteArray} (hans : ∀ b ∈ answer, CanonicalRaw b) :
    ∀ b ∈ Impl.Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord) qname answer,
      CanonicalRaw b := by
  intro b hb
  unfold Impl.Resolver.scrubAnswerB at hb
  obtain ⟨b0, hb0, hf⟩ := Array.mem_filterMap.mp hb
  generalize hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b0 = p at hf
  rcases p with _ | rr
  · simp at hf
  · simp only [] at hf
    generalize hfind : Array.find? (fun m => Impl.DomainName.nameEqCI
        (RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr) m)
        (Impl.Resolver.reachableNamesB (RR := VeriDNS.Spec.ResourceRecord) qname answer)
        = fo at hf
    rcases fo with _ | m
    · simp at hf
    · simp only [Option.map_some] at hf
      obtain rfl := Option.some.inj hf
      exact setOwnerB_canonicalRaw (hans b0 hb0) hp
        (reachableNamesB_canonicalName hq hans m (Array.mem_of_find?_eq_some hfind))

/-! ## Filter-shaped pipelines (memberships restrict) -/

theorem ownerRaws_canonicalRaw {sname : ByteArray} {raws : Array ByteArray}
    (h : ∀ b ∈ raws, CanonicalRaw b) :
    ∀ b ∈ Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname raws,
      CanonicalRaw b := by
  intro b hb
  exact h b (Array.mem_def.mpr
    (Impl.Resolver.ownerRaws_subset sname raws (Array.mem_def.mp hb)))

theorem bailiwickRaws_canonicalRaw {bw : ByteArray} {raws : Array ByteArray}
    (h : ∀ b ∈ raws, CanonicalRaw b) :
    ∀ b ∈ Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws,
      CanonicalRaw b := by
  intro b hb
  exact h b (Array.mem_def.mpr
    (Impl.Resolver.bailiwickRaws_subset bw raws (Array.mem_def.mp hb)))

theorem cnameRaws_canonicalRaw {sname : ByteArray} {raws : Array ByteArray}
    (h : ∀ b ∈ raws, CanonicalRaw b) :
    ∀ b ∈ Impl.Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) sname raws,
      CanonicalRaw b := by
  intro b hb
  exact h b (Array.mem_def.mpr
    (Impl.Resolver.cnameRaws_subset sname raws (Array.mem_def.mp hb)))

theorem scrubAuthorityB_canonicalRaw {qname : ByteArray} {authority : Array ByteArray}
    (h : ∀ b ∈ authority, CanonicalRaw b) :
    ∀ b ∈ Impl.Server.scrubAuthorityB qname authority, CanonicalRaw b := by
  intro b hb
  exact h b (Array.mem_filter.mp hb).1

/-- CNAME chains only ever accumulate answer-section members, so a chain of
canonical raws stays canonical. -/
theorem prependCnameLink_canonicalRaw {chain : Array ByteArray}
    (hchain : ∀ b ∈ chain, CanonicalRaw b) {resp : VeriDNS.Spec.Format}
    (hans : ∀ b ∈ resp.answer, CanonicalRaw b) :
    ∀ b ∈ Impl.Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) chain resp,
      CanonicalRaw b := by
  intro b hb
  unfold Impl.Resolver.prependCnameLink at hb
  split at hb
  · split at hb
    · rename_i hcn
      rcases Array.mem_push.mp hb with hb | rfl
      · exact hchain b hb
      · unfold Impl.Resolver.extractCnameRR at hcn
        exact hans _ (Array.mem_of_find?_eq_some hcn)
    · exact hchain b hb
  · exact hchain b hb

end VeriDNS.Proof.CanonicalRaw
