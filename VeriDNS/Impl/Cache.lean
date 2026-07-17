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
  lastUsed : UInt32 := 0
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
  lastUsed : UInt32 := 0
  deriving Inhabited

structure DnsCache where
  records : Array CacheEntry
  negatives : Array NegativeEntry := #[]
  deriving Inhabited

def DnsCache.empty : DnsCache := { records := #[] }

def DnsCache.capacity : Nat := 4096

def minRecBy {α : Type} (rec : α → UInt32) : List α → Option α
  | [] => none
  | e :: es =>
    match minRecBy rec es with
    | none => some e
    | some b => if rec e ≤ rec b then some e else some b

def negSameKey (a b : NegativeEntry) : Bool :=
  nameEqCI a.name b.name && a.qtype == b.qtype && a.qclass == b.qclass

def dropLruNegatives (a : Array NegativeEntry) : Nat → Array NegativeEntry
  | 0 => a
  | fuel + 1 =>
    if a.size < DnsCache.capacity then a
    else
      match minRecBy (·.lastUsed) a.toList with
      | some e0 => dropLruNegatives (a.filter fun e => !negSameKey e e0) fuel
      | none => a

def boundLruNegatives (a : Array NegativeEntry) : Array NegativeEntry :=
  dropLruNegatives a a.size

/-- RFC 4343 §3 / RFC 3597 §7: RR comparisons are case-insensitive only in the
domain-name fields of the well-known name-bearing types; RRs of unknown type
compare as opaque bytes and must not be rewritten. The name layout of the
well-known types the impl handles: NS(2)/CNAME(5)/PTR(12) rdata is exactly one
name; MX(15) is a 16-bit preference followed by the exchange name; SOA(6) is
mname + rname followed by 20 bytes of fixed 32-bit fields. -/
def rdataCaseFold (t : BitVec 16) (rd : ByteArray) : ByteArray :=
  if t == 2 || t == 5 || t == 12 then foldNameCase rd
  else if t == 15 then
    rd.extract 0 2 ++ foldNameCase (rd.extract 2 rd.size)
  else if t == 6 then
    foldNameCase (rd.extract 0 (rd.size - 20)) ++ rd.extract (rd.size - 20) rd.size
  else rd

/-- Case-insensitive rdata identity (equality modulo 0x20 case in embedded
domain names) — the RRset-member dedup identity at the cache write boundary.
Finding 053: 0x20-cased rdata names must not defeat dedup. -/
def rdataEqCI (t : BitVec 16) (a b : ByteArray) : Bool :=
  rdataCaseFold t a == rdataCaseFold t b

def DnsCache.store (c : DnsCache) (rr : ResourceRecord) (now : UInt32)
    (cred : Trustworthiness := .additionalAuthoritative) : DnsCache :=
  let expiry := now + rr.ttl.toNat.toUInt32
  let entry : CacheEntry := ⟨rr, expiry, false, cred, now⟩
  let records := c.records.filter fun e =>
    !(nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
      && (e.expiry != expiry || rdataEqCI rr.type e.rr.rdata rr.rdata))
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
    (rcode : Rcode) (soa : Option ResourceRecord) (expiry : UInt32) (now : UInt32) : DnsCache :=
  let negatives := c.negatives.filter fun e =>
    !(nameEqCI e.name name && e.qclass == qclass
      && (rcode == Rcode.nameError || e.qtype == qtype))
  { c with negatives :=
      (boundLruNegatives negatives).push ⟨name, qtype, qclass, rcode, expiry, soa, now⟩ }

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

def DnsCache.maxRankForKey (c : DnsCache) (e : CacheEntry) (now : UInt32) : Bool :=
  c.records.all fun e2 =>
    !(e2.fresh now && sameRRKey e2 e) || e.credibility.toCode ≤ e2.credibility.toCode

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



def DnsCache.absorb (base new : DnsCache) : DnsCache :=
  let withRecs : DnsCache :=
    new.records.foldl (fun c e =>
      { c with records := (c.records.filter fun e2 =>
          !(nameEqCI e2.rr.name e.rr.name && e2.rr.type == e.rr.type && e2.rr.class == e.rr.class
            && (e2.expiry != e.expiry || rdataEqCI e.rr.type e2.rr.rdata e.rr.rdata))).push e }) base
  let withNegs : DnsCache :=
    new.negatives.foldl (fun c n =>
      { c with negatives := (c.negatives.filter fun n2 =>
          !(nameEqCI n2.name n.name && n2.qclass == n.qclass
            && (n.rcode == Rcode.nameError || n2.qtype == n.qtype))).push n }) withRecs
  withNegs.boundExpiryClasses

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



abbrev RRKey : Type := ByteArray × BitVec 16 × BitVec 16

def demandKey (name : ByteArray) (qtype qclass : BitVec 16) : RRKey :=
  (foldNameCase name, qtype, qclass)

def rrKey (e : CacheEntry) : RRKey := demandKey e.rr.name e.rr.type e.rr.class

def keyEqB (k k' : RRKey) : Bool :=
  k.1 == k'.1 && k.2.1 == k'.2.1 && k.2.2 == k'.2.2

theorem byteArray_beq_refl (b : ByteArray) : (b == b) = true := by
  show ByteArray.beq b b = true
  unfold ByteArray.beq
  simp

theorem keyEqB_refl (k : RRKey) : keyEqB k k = true := by
  unfold keyEqB
  simp [byteArray_beq_refl]

theorem nameEqCI_refl (b : ByteArray) : nameEqCI b b = true := byteArray_beq_refl _

theorem rdataEqCI_refl (t : BitVec 16) (a : ByteArray) : rdataEqCI t a a = true :=
  byteArray_beq_refl _

theorem rdataEqCI_of_eq (t : BitVec 16) {a b : ByteArray} (h : a = b) :
    rdataEqCI t a b = true := h ▸ rdataEqCI_refl t a

def touchEntry (ks : Array RRKey) (now : UInt32) (e : CacheEntry) : CacheEntry :=
  if ks.any (fun k => keyEqB k (rrKey e)) then { e with lastUsed := now } else e

def negConsulted (k : RRKey) (e : NegativeEntry) : Bool :=
  k.1 == foldNameCase e.name && k.2.2 == e.qclass
    && (e.rcode == Rcode.nameError || k.2.1 == e.qtype)

def touchNegEntry (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) : NegativeEntry :=
  if ks.any (fun k => negConsulted k e) then { e with lastUsed := now } else e

def DnsCache.touchKeys (c : DnsCache) (ks : Array RRKey) (now : UInt32) : DnsCache :=
  { records := c.records.map (touchEntry ks now)
    negatives := c.negatives.map (touchNegEntry ks now) }

theorem touchEntry_rr (ks : Array RRKey) (now : UInt32) (e : CacheEntry) :
    (touchEntry ks now e).rr = e.rr := by
  unfold touchEntry; split <;> rfl

theorem touchEntry_expiry (ks : Array RRKey) (now : UInt32) (e : CacheEntry) :
    (touchEntry ks now e).expiry = e.expiry := by
  unfold touchEntry; split <;> rfl

theorem touchEntry_authoritative (ks : Array RRKey) (now : UInt32) (e : CacheEntry) :
    (touchEntry ks now e).authoritative = e.authoritative := by
  unfold touchEntry; split <;> rfl

theorem touchEntry_credibility (ks : Array RRKey) (now : UInt32) (e : CacheEntry) :
    (touchEntry ks now e).credibility = e.credibility := by
  unfold touchEntry; split <;> rfl

theorem touchNegEntry_name (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    (touchNegEntry ks now e).name = e.name := by
  unfold touchNegEntry; split <;> rfl

theorem touchNegEntry_qtype (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    (touchNegEntry ks now e).qtype = e.qtype := by
  unfold touchNegEntry; split <;> rfl

theorem touchNegEntry_qclass (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    (touchNegEntry ks now e).qclass = e.qclass := by
  unfold touchNegEntry; split <;> rfl

theorem touchNegEntry_rcode (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    (touchNegEntry ks now e).rcode = e.rcode := by
  unfold touchNegEntry; split <;> rfl

theorem touchNegEntry_expiry (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    (touchNegEntry ks now e).expiry = e.expiry := by
  unfold touchNegEntry; split <;> rfl

theorem touchNegEntry_soa (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    (touchNegEntry ks now e).soa = e.soa := by
  unfold touchNegEntry; split <;> rfl

theorem touchEntry_cases (ks : Array RRKey) (now : UInt32) (e : CacheEntry) :
    touchEntry ks now e = e ∨ touchEntry ks now e = { e with lastUsed := now } := by
  unfold touchEntry
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem touchNegEntry_cases (ks : Array RRKey) (now : UInt32) (e : NegativeEntry) :
    touchNegEntry ks now e = e ∨ touchNegEntry ks now e = { e with lastUsed := now } := by
  unfold touchNegEntry
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem touchKeys_records (c : DnsCache) (ks : Array RRKey) (now : UInt32) :
    (c.touchKeys ks now).records = c.records.map (touchEntry ks now) := rfl

theorem touchKeys_negatives (c : DnsCache) (ks : Array RRKey) (now : UInt32) :
    (c.touchKeys ks now).negatives = c.negatives.map (touchNegEntry ks now) := rfl

theorem minRecBy_mem {α : Type} (rec : α → UInt32) :
    ∀ {l : List α} {e : α}, minRecBy rec l = some e → e ∈ l
  | [], _, h => by cases h
  | x :: xs, e, h => by
    unfold minRecBy at h
    revert h
    cases hm : minRecBy rec xs with
    | none => intro h; exact (Option.some.inj h) ▸ List.mem_cons_self ..
    | some b =>
      intro h
      change (if rec x ≤ rec b then some x else some b) = some e at h
      by_cases hle : rec x ≤ rec b
      · rw [if_pos hle] at h
        exact (Option.some.inj h) ▸ List.mem_cons_self ..
      · rw [if_neg hle] at h
        obtain rfl := Option.some.inj h
        exact List.mem_cons_of_mem _ (minRecBy_mem rec hm)

theorem minRecBy_eq_none {α : Type} (rec : α → UInt32) :
    ∀ {l : List α}, minRecBy rec l = none → l = []
  | [], _ => rfl
  | x :: xs, h => by
    exfalso
    unfold minRecBy at h
    revert h
    cases hm : minRecBy rec xs with
    | none => intro h; cases h
    | some b =>
      intro h
      change (if rec x ≤ rec b then some x else some b) = none at h
      by_cases hle : rec x ≤ rec b
      · rw [if_pos hle] at h; cases h
      · rw [if_neg hle] at h; cases h

def groupLastUsed (a : Array CacheEntry) (e : CacheEntry) : UInt32 :=
  a.foldl
    (fun acc e2 =>
      if keyEqB (rrKey e2) (rrKey e) && acc ≤ e2.lastUsed then e2.lastUsed else acc)
    e.lastUsed

def lruVictim (a : Array CacheEntry) : Option CacheEntry :=
  minRecBy (groupLastUsed a) a.toList

def evictLruKeys (a : Array CacheEntry) : Nat → Array CacheEntry
  | 0 => a
  | fuel + 1 =>
    if a.size ≤ DnsCache.capacity then a
    else
      match lruVictim a with
      | some e0 => evictLruKeys (a.filter fun e => !keyEqB (rrKey e) (rrKey e0)) fuel
      | none => a

def DnsCache.boundLruKeys (c : DnsCache) : DnsCache :=
  { c with records := evictLruKeys c.records c.records.size }

def DnsCache.boundLru (c : DnsCache) (touches : Array RRKey) (now : UInt32) : DnsCache :=
  (c.touchKeys touches now).boundLruKeys

theorem evictLruKeys_filter_form (a : Array CacheEntry) (fuel : Nat) :
    ∃ p : RRKey → Bool, evictLruKeys a fuel = a.filter (fun e => p (rrKey e)) := by
  induction fuel generalizing a with
  | zero =>
    exact ⟨fun _ => true, by
      unfold evictLruKeys
      exact (Array.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩
  | succ fuel ih =>
    unfold evictLruKeys
    split
    · exact ⟨fun _ => true,
        (Array.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩
    · split
      · next e0 _ =>
        obtain ⟨p, hp⟩ := ih (a.filter fun e => !keyEqB (rrKey e) (rrKey e0))
        refine ⟨fun k => p k && !keyEqB k (rrKey e0), ?_⟩
        rw [hp, Array.filter_filter]
      · exact ⟨fun _ => true,
          (Array.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩

theorem mem_of_mem_evictLruKeys {a : Array CacheEntry} {fuel : Nat}
    {e : CacheEntry} (h : e ∈ evictLruKeys a fuel) : e ∈ a := by
  obtain ⟨p, hp⟩ := evictLruKeys_filter_form a fuel
  rw [hp] at h
  exact (Array.mem_filter.mp h).1

theorem size_evictLruKeys_le (a : Array CacheEntry) (fuel : Nat)
    (hfuel : a.size ≤ fuel) :
    (evictLruKeys a fuel).size ≤ DnsCache.capacity := by
  induction fuel generalizing a with
  | zero =>
    unfold evictLruKeys
    unfold DnsCache.capacity
    omega
  | succ fuel ih =>
    unfold evictLruKeys
    split
    · assumption
    · next hbig =>
      split
      · next e0 he0 =>
        refine ih _ ?_
        have hmem : e0 ∈ a := by
          have := minRecBy_mem (groupLastUsed a) he0
          exact Array.mem_def.mpr this
        have hkeep : (a.filter fun e => !keyEqB (rrKey e) (rrKey e0)).size < a.size := by
          by_contra hge
          have hle : (a.filter fun e => !keyEqB (rrKey e) (rrKey e0)).size ≤ a.size :=
            Array.size_filter_le
          have heq : (a.filter fun e => !keyEqB (rrKey e) (rrKey e0)).size = a.size := by
            omega
          have := (Array.filter_size_eq_size.mp heq) e0 hmem
          simp [keyEqB_refl] at this
        omega
      · next he0 =>
        have hnil : a.toList = [] := minRecBy_eq_none _ he0
        have : a.size = 0 := by
          simpa using congrArg List.length hnil
        unfold DnsCache.capacity
        omega

theorem negSameKey_refl (e : NegativeEntry) : negSameKey e e = true := by
  unfold negSameKey
  simp [nameEqCI_refl]

theorem mem_of_mem_dropLruNegatives :
    ∀ {fuel : Nat} {a : Array NegativeEntry} {x : NegativeEntry},
      x ∈ dropLruNegatives a fuel → x ∈ a
  | 0, _, _, h => h
  | fuel + 1, a, x, h => by
    unfold dropLruNegatives at h
    split at h
    · exact h
    · split at h
      · exact (Array.mem_filter.mp (mem_of_mem_dropLruNegatives h)).1
      · exact h

theorem mem_of_mem_boundLruNegatives {a : Array NegativeEntry} {x : NegativeEntry}
    (h : x ∈ boundLruNegatives a) : x ∈ a :=
  mem_of_mem_dropLruNegatives h

theorem size_dropLruNegatives_lt (a : Array NegativeEntry) (fuel : Nat)
    (hfuel : a.size ≤ fuel) :
    (dropLruNegatives a fuel).size < DnsCache.capacity := by
  induction fuel generalizing a with
  | zero =>
    unfold dropLruNegatives
    unfold DnsCache.capacity
    omega
  | succ fuel ih =>
    unfold dropLruNegatives
    split
    · assumption
    · next hbig =>
      split
      · next e0 he0 =>
        refine ih _ ?_
        have hmem : e0 ∈ a := Array.mem_def.mpr (minRecBy_mem _ he0)
        have hkeep : (a.filter fun e => !negSameKey e e0).size < a.size := by
          by_contra hge
          have hle : (a.filter fun e => !negSameKey e e0).size ≤ a.size :=
            Array.size_filter_le
          have heq : (a.filter fun e => !negSameKey e e0).size = a.size := by
            omega
          have := (Array.filter_size_eq_size.mp heq) e0 hmem
          simp [negSameKey_refl] at this
        omega
      · next he0 =>
        have hnil : a.toList = [] := minRecBy_eq_none _ he0
        have : a.size = 0 := by
          simpa using congrArg List.length hnil
        unfold DnsCache.capacity
        omega

theorem size_boundLruNegatives_lt (a : Array NegativeEntry) :
    (boundLruNegatives a).size < DnsCache.capacity :=
  size_dropLruNegatives_lt a a.size (Nat.le_refl _)

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
    DnsCache.storeNegative c name qtype qclass rc none expiry 0
  retrieveNegative := DnsCache.lookupNegative

instance : NegativeAuthoritySpec DnsCache ResourceRecord where
  storeSoaRecord := DnsCache.setNegativeSoa
  authoritySection := DnsCache.lookupNegativeSoa



def rrSameKeyB (a b : ResourceRecord) : Bool :=
  nameEqCI a.name b.name && a.type == b.type && a.class == b.class

def minTtlB (x y : BitVec 32) : BitVec 32 := if y.toNat < x.toNat then y else x

def groupMinTtl (rrs : List ResourceRecord) (rr : ResourceRecord) : BitVec 32 :=
  rrs.foldl (fun acc e => if rrSameKeyB e rr then minTtlB acc e.ttl else acc) rr.ttl

def normalizeRRsetTtls (rrs : List ResourceRecord) : List ResourceRecord :=
  rrs.map (fun rr => { rr with ttl := groupMinTtl rrs rr })

def rrsOf (raws : Array ByteArray) : List ResourceRecord :=
  raws.toList.filterMap (fun b => match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
    | .ok (rr, _) => some rr | .error _ => none)

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
