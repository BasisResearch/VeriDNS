import VeriDNS.Proof.NameTree
import VeriDNS.RFC.Check

namespace VeriDNS.Proof.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.NameTree
open VeriDNS.Impl.Cache
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase)

private theorem byteArray_beq_iff {a b : ByteArray} : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    apply ByteArray.ext
    show a.data = b.data
    have : ByteArray.beq a b = true := h
    unfold ByteArray.beq at this
    simpa using this
  · intro h
    subst h
    show ByteArray.beq a a = true
    unfold ByteArray.beq
    simp

theorem nameEqCI_iff {a b : ByteArray} :
    nameEqCI a b = true ↔ foldNameCase a = foldNameCase b := by
  unfold nameEqCI
  exact byteArray_beq_iff

theorem nameEqCI_refl (a : ByteArray) : nameEqCI a a = true :=
  nameEqCI_iff.mpr rfl

theorem nameEqCI_symm {a b : ByteArray} (h : nameEqCI a b = true) :
    nameEqCI b a = true :=
  nameEqCI_iff.mpr (nameEqCI_iff.mp h).symm

theorem nameEqCI_trans {a b c : ByteArray} (h₁ : nameEqCI a b = true)
    (h₂ : nameEqCI b c = true) : nameEqCI a c = true :=
  nameEqCI_iff.mpr ((nameEqCI_iff.mp h₁).trans (nameEqCI_iff.mp h₂))

theorem nodeAtName_congr {T : Node ResourceRecord} {a b : ByteArray}
    (h : nameEqCI a b = true) :
    nodeAtName T a = nodeAtName T b :=
  nodeAtName_congrCI T h

theorem treeLookup_congr {T : Node ResourceRecord} {a b : ByteArray}
    (h : nameEqCI a b = true) (qtype : BitVec 16) :
    treeLookup T a qtype = treeLookup T b qtype := by
  unfold treeLookup
  rw [nodeAtName_congr h]

theorem treeResolve_outcome_chain {T : Node ResourceRecord}
    (qtype : BitVec 16) :
    ∀ (fuel : Nat) (q : ByteArray) (ch₁ ch₂ : Array ResourceRecord)
      {c₁ : Array ResourceRecord} {o₁ : Outcome ResourceRecord},
    treeResolve T qtype fuel q ch₁ = some (c₁, o₁) →
    ∃ c₂, treeResolve T qtype fuel q ch₂ = some (c₂, o₁)
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, q, ch₁, ch₂, c₁, o₁, h => by
    unfold treeResolve at h ⊢
    cases hlook : treeLookup T q qtype with
    | redirect rr canonical =>
      rw [hlook] at h
      exact treeResolve_outcome_chain qtype fuel canonical _ _ h
    | answer rrs => rw [hlook] at h; cases h; exact ⟨ch₂, rfl⟩
    | nodata => rw [hlook] at h; cases h; exact ⟨ch₂, rfl⟩
    | nameError => rw [hlook] at h; cases h; exact ⟨ch₂, rfl⟩

theorem treeResolve_stable {T : Node ResourceRecord} (qtype : BitVec 16) :
    ∀ (fuel : Nat) (q : ByteArray) (ch : Array ResourceRecord)
      {r : Array ResourceRecord × Outcome ResourceRecord},
    treeResolve T qtype fuel q ch = some r →
    treeResolve T qtype (fuel + 1) q ch = some r
  | 0, _, _, _, h => by cases h
  | fuel + 1, q, ch, r, h => by
    show treeResolve T qtype (fuel + 1 + 1) q ch = some r
    unfold treeResolve at h ⊢
    cases hlook : treeLookup T q qtype with
    | redirect rr canonical =>
      rw [hlook] at h
      exact treeResolve_stable qtype fuel _ _ h
    | answer rrs => rw [hlook] at h; exact h
    | nodata => rw [hlook] at h; exact h
    | nameError => rw [hlook] at h; exact h

theorem treeResolve_mono {T : Node ResourceRecord} {qtype : BitVec 16}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {q : ByteArray}
    {ch : Array ResourceRecord}
    {r : Array ResourceRecord × Outcome ResourceRecord}
    (h : treeResolve T qtype fuel q ch = some r) :
    treeResolve T qtype fuel' q ch = some r := by
  induction fuel' with
  | zero =>
    have : fuel = 0 := Nat.le_zero.mp hle
    subst this
    exact h
  | succ n ih =>
    rcases Nat.lt_or_ge fuel (n + 1) with hlt | hge
    · exact treeResolve_stable qtype n q ch (ih (Nat.le_of_lt_succ hlt))
    · have : fuel = n + 1 := Nat.le_antisymm hle hge
      subst this
      exact h

theorem treeResolve_unique {T : Node ResourceRecord} {qtype : BitVec 16}
    {f₁ f₂ : Nat} {q : ByteArray} {ch₁ ch₂ : Array ResourceRecord}
    {c₁ c₂ : Array ResourceRecord} {o₁ o₂ : Outcome ResourceRecord}
    (h₁ : treeResolve T qtype f₁ q ch₁ = some (c₁, o₁))
    (h₂ : treeResolve T qtype f₂ q ch₂ = some (c₂, o₂)) : o₁ = o₂ := by
  obtain ⟨c₂', h₁'⟩ := treeResolve_outcome_chain qtype f₁ q ch₁ ch₂ h₁
  have h1m := treeResolve_mono (Nat.le_max_left f₁ f₂) h₁'
  have h2m := treeResolve_mono (Nat.le_max_right f₁ f₂) h₂
  rw [h1m] at h2m
  cases h2m
  rfl

theorem treeResolve_congr {T : Node ResourceRecord} {qtype : BitVec 16}
    {fuel : Nat} {a b : ByteArray} (h : nameEqCI a b = true)
    {ch : Array ResourceRecord}
    {r : Array ResourceRecord × Outcome ResourceRecord}
    (hr : treeResolve T qtype fuel a ch = some r) :
    treeResolve T qtype fuel b ch = some r := by
  cases fuel with
  | zero => cases hr
  | succ fuel =>
    unfold treeResolve at hr ⊢
    rw [← treeLookup_congr h qtype]
    exact hr

theorem reaches_congr_left {T : Node ResourceRecord} {qtype : BitVec 16}
    {q q' s : ByteArray} (h : nameEqCI q' q = true)
    (hr : Reaches T qtype q s) : Reaches T qtype q' s := by
  induction hr with
  | refl hci => exact .refl (nameEqCI_trans h hci)
  | step _ hlook hci ih => exact .step ih hlook hci

theorem reaches_congr_right {T : Node ResourceRecord} {qtype : BitVec 16}
    {q s t : ByteArray} (hr : Reaches T qtype q s)
    (h : nameEqCI s t = true) : Reaches T qtype q t := by
  cases hr with
  | refl hci => exact .refl (nameEqCI_trans hci h)
  | step hr' hlook hci => exact .step hr' hlook (nameEqCI_trans hci h)

theorem reaches_trans {T : Node ResourceRecord} {qtype : BitVec 16}
    {q s t : ByteArray} (h₁ : Reaches T qtype q s)
    (h₂ : Reaches T qtype s t) : Reaches T qtype q t := by
  induction h₂ with
  | refl hci => exact reaches_congr_right h₁ hci
  | step _ hlook hci ih => exact .step ih hlook hci

theorem reaches_resolve_back {T : Node ResourceRecord} {qtype : BitVec 16}
    {q s : ByteArray} (hr : Reaches T qtype q s) :
    ∀ {fuel : Nat} {ch c : Array ResourceRecord} {o : Outcome ResourceRecord},
    treeResolve T qtype fuel s ch = some (c, o) →
    ∃ fuel' c', treeResolve T qtype fuel' q #[] = some (c', o) := by
  induction hr with
  | refl hci =>
    intro fuel ch c o h
    obtain ⟨c₂, h₂⟩ := treeResolve_outcome_chain qtype fuel _ ch #[] h
    exact ⟨fuel, c₂, treeResolve_congr (nameEqCI_symm hci) h₂⟩
  | @step s' t' rr canonical hreach hlook hci ih =>
    intro fuel ch c o h

    have h1 : treeResolve T qtype fuel canonical ch = some (c, o) :=
      treeResolve_congr (nameEqCI_symm hci) h

    obtain ⟨c₂, h2⟩ := treeResolve_outcome_chain qtype fuel canonical ch
      ((#[] : Array ResourceRecord).push rr) h1

    refine ih (fuel := fuel + 1) (ch := #[]) (c := c₂) (o := o) ?_
    unfold treeResolve
    rw [hlook]
    exact h2

theorem reaches_terminal_pins {T : Node ResourceRecord} {qtype : BitVec 16}
    {q s : ByteArray} (hr : Reaches T qtype q s)
    {o : Outcome ResourceRecord} (hlook : treeLookup T s qtype = o)
    (hterm : ∀ rr c, o ≠ .redirect rr c) :
    ∀ {fuel : Nat} {c' : Array ResourceRecord} {o' : Outcome ResourceRecord},
    treeResolve T qtype fuel q #[] = some (c', o') → o' = o := by
  intro fuel c' o' h
  have hone : treeResolve T qtype (0 + 1) s #[] = some (#[], o) := by
    cases o with
    | redirect rr c => exact absurd rfl (hterm rr c)
    | answer rrs => unfold treeResolve; rw [hlook]
    | nodata => unfold treeResolve; rw [hlook]
    | nameError => unfold treeResolve; rw [hlook]
  obtain ⟨fuel'', c'', h''⟩ := reaches_resolve_back hr hone
  exact treeResolve_unique h h''

structure TreeSane (T : Node ResourceRecord) : Prop where
  cnameExclusive : CnameExclusive T
  cnameUnique : ∀ name n, nodeAtName T name = some n →
    ∀ rr ∈ n.resourceSet.toList, ∀ rr' ∈ n.resourceSet.toList,
      rr.type = cnameType → rr'.type = cnameType → rr.rdata = rr'.rdata
  named : ∀ name n, nodeAtName T name = some n →
    ∀ rr ∈ n.resourceSet.toList, nameEqCI rr.name name = true
  classUniform : ∀ name n, nodeAtName T name = some n →
    ∀ rr ∈ n.resourceSet.toList, ∀ rr' ∈ n.resourceSet.toList,
      rr.class = rr'.class

private theorem bv16_beq_iff {a b : BitVec 16} : (a == b) = true ↔ a = b :=
  ⟨eq_of_beq, fun h => h ▸ beq_self_eq_true a⟩

private theorem bv32_beq_iff {a b : BitVec 32} : (a == b) = true ↔ a = b :=
  ⟨eq_of_beq, fun h => h ▸ beq_self_eq_true a⟩

private theorem uint32_beq_iff {a b : UInt32} : (a == b) = true ↔ a = b :=
  ⟨eq_of_beq, fun h => h ▸ beq_self_eq_true a⟩

theorem sameData_iff {a b : ResourceRecord} :
    sameData a b = true ↔
      nameEqCI a.name b.name = true ∧ a.type = b.type ∧
      a.class = b.class ∧ rdataEqCI b.type a.rdata b.rdata = true := by
  unfold sameData
  simp only [Bool.and_eq_true, bv16_beq_iff, and_assoc]

theorem rdataEqCI_symm {t : BitVec 16} {a b : ByteArray}
    (h : rdataEqCI t a b = true) : rdataEqCI t b a = true := by
  unfold rdataEqCI at h ⊢
  rw [byteArray_beq_iff] at h ⊢
  exact h.symm

theorem rdataEqCI_trans {t : BitVec 16} {a b c : ByteArray}
    (h₁ : rdataEqCI t a b = true) (h₂ : rdataEqCI t b c = true) :
    rdataEqCI t a c = true := by
  unfold rdataEqCI at h₁ h₂ ⊢
  rw [byteArray_beq_iff] at h₁ h₂ ⊢
  exact h₁.trans h₂

/-- For CNAME rdata (exactly one name), the CI rdata identity is exactly
case-insensitive name equality. -/
theorem rdataEqCI_cname (a b : ByteArray) :
    rdataEqCI (5 : BitVec 16) a b = nameEqCI a b := rfl

def SameKey (a b : ResourceRecord) : Prop :=
  nameEqCI a.name b.name = true ∧ a.type = b.type ∧ a.class = b.class

theorem sameKey_refl (a : ResourceRecord) : SameKey a a :=
  ⟨nameEqCI_refl _, rfl, rfl⟩

theorem sameKey_symm {a b : ResourceRecord} (h : SameKey a b) : SameKey b a :=
  ⟨nameEqCI_symm h.1, h.2.1.symm, h.2.2.symm⟩

theorem sameKey_trans {a b c : ResourceRecord} (h₁ : SameKey a b)
    (h₂ : SameKey b c) : SameKey a c :=
  ⟨nameEqCI_trans h₁.1 h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem sameKey_of_sameData {a b : ResourceRecord} (h : sameData a b = true) :
    SameKey a b :=
  let ⟨hn, ht, hc, _⟩ := sameData_iff.mp h
  ⟨hn, ht, hc⟩

theorem sameData_set_ttl {a b : ResourceRecord} (ttl : BitVec 32)
    (h : sameData a b = true) : sameData { a with ttl := ttl } b = true := by
  rw [sameData_iff] at h ⊢
  exact h

def LookupComplete (T : Node ResourceRecord) (c : DnsCache) : Prop :=
  ∀ e ∈ c.records, e.credibility.toCode < untrustworthyFloor →
    ∀ n, nodeAtName T e.rr.name = some n →
      ∀ trr ∈ n.resourceSet.toList, trr.type = e.rr.type →
        ∃ e' ∈ c.records, sameData e'.rr trr = true ∧
          e'.expiry = e.expiry ∧
          e'.credibility.toCode < untrustworthyFloor ∧

          (∀ e₂ ∈ c.records, SameKey e₂.rr e'.rr → e₂.expiry = e'.expiry →
            e'.credibility.toCode ≤ e₂.credibility.toCode)

def NegativesFaithful (T : Node ResourceRecord) (c : DnsCache) : Prop :=
  ∀ ne ∈ c.negatives,
    (ne.rcode = Rcode.nameError → nodeAtName T ne.name = none) ∧
    (ne.rcode = Rcode.noError → treeLookup T ne.name ne.qtype = .nodata) ∧
    (ne.rcode = Rcode.nameError ∨ ne.rcode = Rcode.noError)

theorem lookupComplete_empty (T : Node ResourceRecord) :
    LookupComplete T DnsCache.empty := by
  intro e he
  simp [DnsCache.empty] at he

theorem negativesFaithful_empty (T : Node ResourceRecord) :
    NegativesFaithful T DnsCache.empty := by
  intro ne hne
  simp [DnsCache.empty] at hne

theorem lookupComplete_bound {T : Node ResourceRecord} {c : DnsCache}
    (h : LookupComplete T c) : LookupComplete T c.boundExpiryClasses := by
  unfold DnsCache.boundExpiryClasses
  obtain ⟨p, hp⟩ := evictClasses_filter_form c.records c.records.size
  rw [hp]
  intro e he hcred n hn trr htrr hty
  obtain ⟨hmem, hkeep⟩ := Array.mem_filter.mp he
  obtain ⟨e', he', hdata, hexp, hcred', hmax⟩ := h e hmem hcred n hn trr htrr hty
  refine ⟨e', Array.mem_filter.mpr ⟨he', by rw [hexp]; exact hkeep⟩, hdata, hexp, hcred',
    fun e₂ he₂ hk₂ hexp₂ => hmax e₂ (Array.mem_filter.mp he₂).1 hk₂ hexp₂⟩

theorem lookupComplete_sweep {T : Node ResourceRecord} {c : DnsCache}
    (h : LookupComplete T c) (now : UInt32) :
    LookupComplete T (c.sweep now) := by
  intro e he hcred n hn trr htrr hty
  obtain ⟨hmem, hkeep⟩ := Array.mem_filter.mp he
  obtain ⟨e', he', hdata, hexp, hcred', hmax⟩ := h e hmem hcred n hn trr htrr hty
  refine ⟨e', Array.mem_filter.mpr ⟨he', ?_⟩, hdata, hexp, hcred',
    fun e₂ he₂ hk₂ hexp₂ => hmax e₂ (Array.mem_filter.mp he₂).1 hk₂ hexp₂⟩
  unfold CacheEntry.fresh at hkeep ⊢
  rw [hexp]
  exact hkeep

theorem lookupComplete_touchKeys {T : Node ResourceRecord} {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (h : LookupComplete T c) : LookupComplete T (c.touchKeys ks tnow) := by
  intro e he hcred n hn trr htrr hty
  rw [touchKeys_records] at he
  obtain ⟨e₀, he₀, hmap⟩ := Array.mem_map.mp he
  subst hmap
  rw [touchEntry_credibility] at hcred
  rw [touchEntry_rr] at hn hty
  obtain ⟨e', he', hdata, hexp, hcred', hmax⟩ := h e₀ he₀ hcred n hn trr htrr hty
  refine ⟨touchEntry ks tnow e', ?_, ?_, ?_, ?_, ?_⟩
  · rw [touchKeys_records]
    exact Array.mem_map.mpr ⟨e', he', rfl⟩
  · rw [touchEntry_rr]; exact hdata
  · rw [touchEntry_expiry, touchEntry_expiry]; exact hexp
  · rw [touchEntry_credibility]; exact hcred'
  · intro e₂ he₂ hk₂ hexp₂
    rw [touchKeys_records] at he₂
    obtain ⟨e₂', he₂', hmap₂⟩ := Array.mem_map.mp he₂
    subst hmap₂
    rw [touchEntry_rr, touchEntry_rr] at hk₂
    rw [touchEntry_expiry, touchEntry_expiry] at hexp₂
    rw [touchEntry_credibility, touchEntry_credibility]
    exact hmax e₂' he₂' hk₂ hexp₂

theorem lookupComplete_boundLruKeys {T : Node ResourceRecord} {c : DnsCache}
    (hsane : TreeSane T) (hagreeC : CacheAgrees T c)
    (h : LookupComplete T c) : LookupComplete T c.boundLruKeys := by
  unfold DnsCache.boundLruKeys
  obtain ⟨p, hp⟩ := evictLruKeys_filter_form c.records c.records.size
  rw [hp]
  intro e he hcred n hn trr htrr hty
  obtain ⟨hmem, hkeep⟩ := Array.mem_filter.mp he
  obtain ⟨e', he', hdata, hexp, hcred', hmax⟩ := h e hmem hcred n hn trr htrr hty
  have hkey : rrKey e' = rrKey e := by
    obtain ⟨hdn, hdt, hdc, _⟩ := sameData_iff.mp hdata
    have hnamed : nameEqCI trr.name e.rr.name = true :=
      hsane.named e.rr.name n hn trr htrr
    obtain ⟨n₀, hn₀, rr', hrr', hd'⟩ := (hagreeC.positives e hmem).1
    have hn₀n : n₀ = n := Option.some.inj (hn₀.symm.trans hn)
    subst hn₀n
    have hclassTrr : trr.class = rr'.class :=
      hsane.classUniform e.rr.name n₀ hn trr htrr rr' hrr'
    have hclassE : rr'.class = e.rr.class := (sameData_iff.mp hd').2.2.1
    unfold rrKey demandKey
    rw [nameEqCI_iff.mp (nameEqCI_trans hdn hnamed), hdt, hty, hdc, hclassTrr, hclassE]
  refine ⟨e', Array.mem_filter.mpr ⟨he', by rw [hkey]; exact hkeep⟩, hdata, hexp, hcred',
    fun e₂ he₂ hk₂ hexp₂ => hmax e₂ (Array.mem_filter.mp he₂).1 hk₂ hexp₂⟩

theorem lookupComplete_boundLru {T : Node ResourceRecord} {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hsane : TreeSane T) (hagreeC : CacheAgrees T c)
    (h : LookupComplete T c) : LookupComplete T (c.boundLru ks tnow) :=
  lookupComplete_boundLruKeys hsane (cacheAgrees_touchKeys ks tnow hagreeC)
    (lookupComplete_touchKeys ks tnow h)

theorem lookupComplete_storeNegative {T : Node ResourceRecord} {c : DnsCache}
    (h : LookupComplete T c) (name : ByteArray) (qt qc : BitVec 16)
    (rc : Rcode) (soa : Option ResourceRecord) (expiry now : UInt32) :
    LookupComplete T (c.storeNegative name qt qc rc soa expiry now) := h

theorem lookupComplete_setNegativeSoa {T : Node ResourceRecord} {c : DnsCache}
    (h : LookupComplete T c) (name : ByteArray) (qt qc : BitVec 16)
    (soa : ResourceRecord) (expiry : UInt32) :
    LookupComplete T (c.setNegativeSoa name qt qc soa expiry) := h

theorem negativesFaithful_store {T : Node ResourceRecord} {c : DnsCache}
    (h : NegativesFaithful T c) (rr : ResourceRecord) (now : UInt32)
    (cred : Trustworthiness) :
    NegativesFaithful T (c.store rr now cred) := h

theorem negativesFaithful_storeChecked {T : Node ResourceRecord} {c : DnsCache}
    (h : NegativesFaithful T c) (rr : ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) :
    NegativesFaithful T (c.storeChecked rr cred now) := by
  unfold DnsCache.storeChecked
  split
  · exact h
  · dsimp only []
    split
    · exact h
    · exact negativesFaithful_store h rr now cred

theorem negativesFaithful_bound {T : Node ResourceRecord} {c : DnsCache}
    (h : NegativesFaithful T c) : NegativesFaithful T c.boundExpiryClasses := h

theorem negativesFaithful_touchKeys {T : Node ResourceRecord} {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (h : NegativesFaithful T c) : NegativesFaithful T (c.touchKeys ks tnow) := by
  intro ne hne
  rw [touchKeys_negatives] at hne
  obtain ⟨ne₀, hne₀, hmap⟩ := Array.mem_map.mp hne
  subst hmap
  rw [touchNegEntry_rcode, touchNegEntry_name, touchNegEntry_qtype]
  exact h ne₀ hne₀

theorem negativesFaithful_boundLruKeys {T : Node ResourceRecord} {c : DnsCache}
    (h : NegativesFaithful T c) : NegativesFaithful T c.boundLruKeys := h

theorem negativesFaithful_boundLru {T : Node ResourceRecord} {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (h : NegativesFaithful T c) : NegativesFaithful T (c.boundLru ks tnow) :=
  negativesFaithful_boundLruKeys (negativesFaithful_touchKeys ks tnow h)

theorem negativesFaithful_sweep {T : Node ResourceRecord} {c : DnsCache}
    (h : NegativesFaithful T c) (now : UInt32) :
    NegativesFaithful T (c.sweep now) := by
  intro ne hne
  exact h ne (Array.mem_filter.mp hne).1

section StoreCharacterization

def Removes (rr : ResourceRecord) (now : UInt32) (e : CacheEntry) : Prop :=
  SameKey e.rr rr ∧
    (e.expiry ≠ now + rr.ttl.toNat.toUInt32
      ∨ rdataEqCI rr.type e.rr.rdata rr.rdata = true)

private theorem removes_iff {rr : ResourceRecord} {now : UInt32}
    {e : CacheEntry} :
    (nameEqCI e.rr.name rr.name && e.rr.type == rr.type
      && e.rr.class == rr.class
      && (e.expiry != now + rr.ttl.toNat.toUInt32
          || rdataEqCI rr.type e.rr.rdata rr.rdata)) = true
    ↔ Removes rr now e := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, bv16_beq_iff]
  exact ⟨fun ⟨⟨⟨hn, ht⟩, hc⟩, hd⟩ => ⟨⟨hn, ht, hc⟩, hd⟩,
    fun ⟨⟨hn, ht, hc⟩, hd⟩ => ⟨⟨⟨hn, ht⟩, hc⟩, hd⟩⟩

private theorem keeps_iff {rr : ResourceRecord} {now : UInt32}
    {e : CacheEntry} :
    (!(nameEqCI e.rr.name rr.name && e.rr.type == rr.type
      && e.rr.class == rr.class
      && (e.expiry != now + rr.ttl.toNat.toUInt32
          || rdataEqCI rr.type e.rr.rdata rr.rdata))) = true
    ↔ ¬ Removes rr now e := by
  rw [Bool.not_eq_true']
  rw [← removes_iff]
  cases (nameEqCI e.rr.name rr.name && e.rr.type == rr.type
      && e.rr.class == rr.class
      && (e.expiry != now + rr.ttl.toNat.toUInt32
          || rdataEqCI rr.type e.rr.rdata rr.rdata)) <;> simp

theorem mem_store_iff {c : DnsCache} {rr : ResourceRecord} {now : UInt32}
    {cred : Trustworthiness} {e : CacheEntry} :
    e ∈ (c.store rr now cred).records ↔
      (e ∈ c.records ∧ ¬ Removes rr now e) ∨
      e = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  unfold DnsCache.store
  constructor
  · intro he
    rcases Array.mem_push.mp he with hf | hp
    · obtain ⟨hm, hcond⟩ := Array.mem_filter.mp hf
      exact Or.inl ⟨hm, keeps_iff.mp hcond⟩
    · exact Or.inr hp
  · intro h
    rcases h with ⟨hm, hnot⟩ | heq
    · exact Array.mem_push.mpr
        (Or.inl (Array.mem_filter.mpr ⟨hm, keeps_iff.mpr hnot⟩))
    · exact Array.mem_push.mpr (Or.inr heq)

def Blocked (c : DnsCache) (rr : ResourceRecord) (cred : Trustworthiness)
    (now : UInt32) : Prop :=
  ∃ e ∈ c.records, SameKey e.rr rr ∧
    (e.expiry > now ∨ e.expiry = now + rr.ttl.toNat.toUInt32) ∧
    e.credibility.toCode < cred.toCode

private theorem blockedTest_iff {rr : ResourceRecord} {now : UInt32}
    {cred : Trustworthiness} {e : CacheEntry} :
    (nameEqCI e.rr.name rr.name && e.rr.type == rr.type
      && e.rr.class == rr.class
      && (decide (e.expiry > now)
          || e.expiry == now + rr.ttl.toNat.toUInt32)
      && decide (e.credibility.toCode < cred.toCode)) = true
    ↔ SameKey e.rr rr ∧
      (e.expiry > now ∨ e.expiry = now + rr.ttl.toNat.toUInt32) ∧
      e.credibility.toCode < cred.toCode := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    bv16_beq_iff, uint32_beq_iff]
  exact ⟨fun ⟨⟨⟨⟨hn, ht⟩, hc⟩, hf⟩, hb⟩ => ⟨⟨hn, ht, hc⟩, hf, hb⟩,
    fun ⟨⟨hn, ht, hc⟩, hf, hb⟩ => ⟨⟨⟨⟨hn, ht⟩, hc⟩, hf⟩, hb⟩⟩

theorem storeChecked_cases (c : DnsCache) (rr : ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) :
    (rr.ttl = 0 ∧ c.storeChecked rr cred now = c) ∨
    (rr.ttl ≠ 0 ∧ Blocked c rr cred now ∧ c.storeChecked rr cred now = c) ∨
    (rr.ttl ≠ 0 ∧ ¬ Blocked c rr cred now ∧
      c.storeChecked rr cred now = c.store rr now cred) := by
  unfold DnsCache.storeChecked
  by_cases h0 : (rr.ttl == 0) = true
  · exact Or.inl ⟨bv32_beq_iff.mp h0, by rw [if_pos h0]⟩
  · have httl : rr.ttl ≠ 0 := fun h => h0 (bv32_beq_iff.mpr h)
    rw [if_neg h0]
    dsimp only []
    by_cases hb : (c.records.any fun e =>
        nameEqCI e.rr.name rr.name && e.rr.type == rr.type
          && e.rr.class == rr.class
          && (decide (e.expiry > now)
              || e.expiry == now + rr.ttl.toNat.toUInt32)
          && decide (e.credibility.toCode < cred.toCode)) = true
    · refine Or.inr (Or.inl ⟨httl, ?_, by rw [if_pos hb]⟩)
      obtain ⟨e, hmem, hcond⟩ := Array.any_eq_true'.mp hb
      exact ⟨e, hmem, blockedTest_iff.mp hcond⟩
    · refine Or.inr (Or.inr ⟨httl, ?_, by rw [if_neg hb]⟩)
      intro ⟨e, hmem, hcond⟩
      exact hb (Array.any_eq_true'.mpr ⟨e, hmem, blockedTest_iff.mpr hcond⟩)

theorem blocked_congr {c : DnsCache} {r r' : ResourceRecord}
    {cred : Trustworthiness} {now : UInt32} (hk : SameKey r' r)
    (ht : r'.ttl = r.ttl) :
    Blocked c r' cred now ↔ Blocked c r cred now := by
  unfold Blocked
  constructor
  · rintro ⟨e, hm, hkey, hf, hb⟩
    exact ⟨e, hm, sameKey_trans hkey hk, by rw [← ht]; exact hf, hb⟩
  · rintro ⟨e, hm, hkey, hf, hb⟩
    exact ⟨e, hm, sameKey_trans hkey (sameKey_symm hk), by rw [ht]; exact hf, hb⟩

end StoreCharacterization

section CacheFold

open VeriDNS.Impl.Resolver (cacheRRs cacheUnlessTruncated bailiwickRaws
  bailiwickRaws_subset bailiwickRaws_owner_inBailiwick isAncestorB
  ownerRaws ownerRaws_subset ownerRaws_owner_eq
  cnameRaws cnameRaws_subset cnameRaws_owner_eq cnameRaws_pred)

variable {cred : Trustworthiness} {now : UInt32}

def storeStep (cred : Trustworthiness) (now : UInt32)
    (c : DnsCache) (b : ByteArray) : DnsCache :=
  match RRParse.parseRaw (RR := ResourceRecord) b with
  | some rr => c.storeChecked rr cred now
  | none => c

theorem storeStep_some {c : DnsCache} {b : ByteArray} {r : ResourceRecord}
    (hp : RRParse.parseRaw (RR := ResourceRecord) b = some r) :
    storeStep cred now c b = c.storeChecked r cred now := by
  unfold storeStep
  rw [hp]

theorem cacheRRs_eq (c : DnsCache) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) :
    cacheRRs (C := DnsCache) (RR := ResourceRecord) c raws cred now
      = raws.toList.foldl (storeStep cred now) c := by
  unfold cacheRRs storeStep
  rw [← Array.foldl_toList]
  congr 1
  funext c' b
  cases RRParse.parseRaw (RR := ResourceRecord) b <;> rfl

def UniformTtls (L : List ByteArray) : Prop :=
  ∀ b₁ ∈ L, ∀ b₂ ∈ L, ∀ r₁ r₂,
    RRParse.parseRaw (RR := ResourceRecord) b₁ = some r₁ →
    RRParse.parseRaw (RR := ResourceRecord) b₂ = some r₂ →
    SameKey r₁ r₂ → r₁.ttl = r₂.ttl

theorem uniformTtls_of (raws : Array ByteArray) (h : TtlUniform raws) :
    UniformTtls raws.toList := by
  intro b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ hk
  exact h b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ hk.1 hk.2.1 hk.2.2

private theorem uniformTtls_tail {b : ByteArray} {L : List ByteArray}
    (h : UniformTtls (b :: L)) : UniformTtls L :=
  fun b₁ hb₁ b₂ hb₂ => h b₁ (List.mem_cons_of_mem b hb₁)
    b₂ (List.mem_cons_of_mem b hb₂)

theorem blocked_storeStep {c : DnsCache} {b : ByteArray}
    {rr : ResourceRecord}
    (hcoh : ∀ r, RRParse.parseRaw (RR := ResourceRecord) b = some r →
      SameKey r rr → r.ttl = rr.ttl) :
    Blocked (storeStep cred now c b) rr cred now ↔ Blocked c rr cred now := by
  unfold storeStep
  cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
  | none => exact Iff.rfl
  | some r =>
    dsimp only []
    rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
        ⟨httl, hnb, heq⟩
    · rw [heq]
    · rw [heq]
    · rw [heq]
      constructor
      · rintro ⟨e, hm, hkey, hf, hb'⟩
        rcases mem_store_iff.mp hm with ⟨hold, _⟩ | hnew
        · exact ⟨e, hold, hkey, hf, hb'⟩
        ·
          exfalso
          rw [hnew] at hb'
          exact Nat.lt_irrefl _ hb'
      · rintro ⟨e, hm, hkey, hf, hb'⟩
        by_cases hrem : Removes r now e
        ·
          exfalso
          apply hnb
          refine ⟨e, hm, hrem.1, ?_, hb'⟩
          rcases hf with hfr | hfe
          · exact Or.inl hfr
          · right
            have hkr : SameKey r rr :=
              sameKey_trans (sameKey_symm hrem.1) hkey
            rw [hfe, hcoh r hp hkr]
        · exact ⟨e, mem_store_iff.mpr (Or.inl ⟨hm, hrem⟩), hkey, hf, hb'⟩

theorem blocked_foldl {rr : ResourceRecord} :
    ∀ (L : List ByteArray) (c : DnsCache),
    (∀ b ∈ L, ∀ r, RRParse.parseRaw (RR := ResourceRecord) b = some r →
      SameKey r rr → r.ttl = rr.ttl) →
    (Blocked (L.foldl (storeStep cred now) c) rr cred now ↔
      Blocked c rr cred now)
  | [], _, _ => Iff.rfl
  | b :: L, c, hcoh => by
    rw [List.foldl_cons]
    exact (blocked_foldl L _ (fun b' hb' => hcoh b' (List.mem_cons_of_mem b hb'))).trans
      (blocked_storeStep (hcoh b List.mem_cons_self))

theorem mem_foldl_store :
    ∀ (L : List ByteArray) (c : DnsCache), UniformTtls L →
    ∀ {e : CacheEntry}, e ∈ (L.foldl (storeStep cred now) c).records →
    e ∈ c.records ∨
      ∃ b ∈ L, ∃ r, RRParse.parseRaw (RR := ResourceRecord) b = some r ∧
        e = ⟨r, now + r.ttl.toNat.toUInt32, false, cred, now⟩ ∧ r.ttl ≠ 0 ∧
        ¬ Blocked c r cred now
  | [], _, _, _, he => Or.inl he
  | b :: L, c, hu, e, he => by
    rw [List.foldl_cons] at he
    rcases mem_foldl_store L _ (uniformTtls_tail hu) he with hstep | hwit
    ·
      unfold storeStep at hstep
      revert hstep
      cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
      | none => exact fun hstep => Or.inl hstep
      | some r =>
        intro hstep
        dsimp only [] at hstep
        rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
            ⟨httl, hnb, heq⟩
        · rw [heq] at hstep; exact Or.inl hstep
        · rw [heq] at hstep; exact Or.inl hstep
        · rw [heq] at hstep
          rcases mem_store_iff.mp hstep with ⟨hold, _⟩ | hnew
          · exact Or.inl hold
          · exact Or.inr ⟨b, List.mem_cons_self, r, hp, hnew, httl, hnb⟩
    ·
      obtain ⟨b', hb', r', hp', heq', httl', hnb'⟩ := hwit
      refine Or.inr ⟨b', List.mem_cons_of_mem b hb', r', hp', heq', httl', ?_⟩
      intro hblocked
      apply hnb'
      rw [blocked_storeStep (fun r₀ hp₀ hk₀ =>
        hu b List.mem_cons_self b' (List.mem_cons_of_mem b hb') r₀ r' hp₀ hp' hk₀)]
      exact hblocked

def Sat (trr : ResourceRecord) (E : UInt32) (κ : Nat) (c : DnsCache) : Prop :=
  ∃ e' ∈ c.records, sameData e'.rr trr = true ∧ e'.expiry = E ∧
    e'.credibility.toCode ≤ κ

theorem sat_foldl {trr : ResourceRecord} {E : UInt32} {κ : Nat} :
    ∀ (L : List ByteArray) (c : DnsCache), UniformTtls L →
    (∀ b ∈ L, ∀ r, RRParse.parseRaw (RR := ResourceRecord) b = some r →
      SameKey r trr →
      r.ttl = 0 ∨ Blocked c r cred now ∨ now + r.ttl.toNat.toUInt32 = E) →
    Sat trr E κ c → Sat trr E κ (L.foldl (storeStep cred now) c)
  | [], _, _, _, h => h
  | b :: L, c, hu, hkey, h => by
    rw [List.foldl_cons]

    have hstep : Sat trr E κ (storeStep cred now c b) := by
      unfold storeStep
      cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
      | none => exact h
      | some r =>
        dsimp only []
        rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
            ⟨httl, hnb, heq⟩
        · rw [heq]; exact h
        · rw [heq]; exact h
        · rw [heq]
          obtain ⟨e', hm', hdata', hexp', hcred'⟩ := h
          by_cases hrem : Removes r now e'
          ·
            have hkr : SameKey r trr :=
              sameKey_trans (sameKey_symm hrem.1) (sameKey_of_sameData hdata')
            have hE : now + r.ttl.toNat.toUInt32 = E := by
              rcases hkey b List.mem_cons_self r hp hkr with h0 | hbl | hE
              · exact absurd h0 httl
              · exact absurd hbl hnb
              · exact hE

            have hrd : rdataEqCI r.type e'.rr.rdata r.rdata = true := by
              rcases hrem.2 with hne | hrd
              · exact absurd (hexp'.trans hE.symm) hne
              · exact hrd

            have hcb : cred.toCode ≤ e'.credibility.toCode := by
              by_contra hlt
              exact hnb ⟨e', hm', hrem.1, Or.inr (hexp'.trans hE.symm),
                Nat.lt_of_not_le hlt⟩
            refine ⟨⟨r, now + r.ttl.toNat.toUInt32, false, cred, now⟩,
              mem_store_iff.mpr (Or.inr rfl), ?_, hE, Nat.le_trans hcb hcred'⟩

            obtain ⟨hn', ht', hc', hd'⟩ := sameData_iff.mp hdata'
            have hk' : SameKey r e'.rr := sameKey_symm hrem.1
            exact sameData_iff.mpr ⟨nameEqCI_trans hk'.1 hn',
              hk'.2.1.trans ht', hk'.2.2.trans hc',
              rdataEqCI_trans (rdataEqCI_symm (hkr.2.1 ▸ hrd)) hd'⟩
          · exact ⟨e', mem_store_iff.mpr (Or.inl ⟨hm', hrem⟩), hdata',
              hexp', hcred'⟩
    refine sat_foldl L _ (uniformTtls_tail hu) ?_ hstep
    intro b' hb' r' hp' hk'
    rcases hkey b' (List.mem_cons_of_mem b hb') r' hp' hk' with h0 | hbl | hE
    · exact Or.inl h0
    · refine Or.inr (Or.inl ?_)
      have hcoh : ∀ b₀ ∈ [b], ∀ r₀,
          RRParse.parseRaw (RR := ResourceRecord) b₀ = some r₀ →
          SameKey r₀ r' → r₀.ttl = r'.ttl := by
        intro b₀ hb₀ r₀ hp₀ hk₀
        have hbeq : b₀ = b := by simpa using hb₀
        subst hbeq
        exact hu b₀ List.mem_cons_self b' (List.mem_cons_of_mem b₀ hb')
          r₀ r' hp₀ hp' hk₀
      exact (blocked_foldl [b] c hcoh).mpr hbl
    · exact Or.inr (Or.inr hE)

def KeyAt (K : ResourceRecord) (E : UInt32) (c : DnsCache) : Prop :=
  ∀ e ∈ c.records, SameKey e.rr K → e.expiry = E

private theorem keyAt_store {c : DnsCache} {r K : ResourceRecord}
    {E : UInt32} (hK : SameKey r K)
    (hE : now + r.ttl.toNat.toUInt32 = E) :
    KeyAt K E (c.store r now cred) := by
  intro e he hk
  rcases mem_store_iff.mp he with ⟨_, hnrem⟩ | hnew
  · by_contra hne
    apply hnrem
    refine ⟨sameKey_trans hk (sameKey_symm hK), Or.inl ?_⟩
    rw [hE]
    exact hne
  · rw [hnew, ← hE]

private theorem keyAt_foldl {K : ResourceRecord} {E : UInt32} :
    ∀ (L : List ByteArray) (c : DnsCache), UniformTtls L →
    (∀ b ∈ L, ∀ r, RRParse.parseRaw (RR := ResourceRecord) b = some r →
      SameKey r K →
      r.ttl = 0 ∨ Blocked c r cred now ∨ now + r.ttl.toNat.toUInt32 = E) →
    KeyAt K E c → KeyAt K E (L.foldl (storeStep cred now) c)
  | [], _, _, _, h => h
  | b :: L, c, hu, hkey, h => by
    rw [List.foldl_cons]
    have hstep : KeyAt K E (storeStep cred now c b) := by
      unfold storeStep
      cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
      | none => exact h
      | some r =>
        dsimp only []
        rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
            ⟨httl, hnb, heq⟩
        · rw [heq]; exact h
        · rw [heq]; exact h
        · rw [heq]
          intro e he hk
          rcases mem_store_iff.mp he with ⟨hold, _⟩ | hnew
          · exact h e hold hk
          ·
            have hkr : SameKey r K := by
              rw [hnew] at hk
              exact hk
            rcases hkey b List.mem_cons_self r hp hkr with h0 | hbl | hE
            · exact absurd h0 httl
            · exact absurd hbl hnb
            · rw [hnew, ← hE]
    refine keyAt_foldl L _ (uniformTtls_tail hu) ?_ hstep
    intro b' hb' r' hp' hk'
    rcases hkey b' (List.mem_cons_of_mem b hb') r' hp' hk' with h0 | hbl | hE
    · exact Or.inl h0
    · refine Or.inr (Or.inl ?_)
      have hcoh : ∀ b₀ ∈ [b], ∀ r₀,
          RRParse.parseRaw (RR := ResourceRecord) b₀ = some r₀ →
          SameKey r₀ r' → r₀.ttl = r'.ttl := by
        intro b₀ hb₀ r₀ hp₀ hk₀
        have hbeq : b₀ = b := by simpa using hb₀
        subst hbeq
        exact hu b₀ List.mem_cons_self b' (List.mem_cons_of_mem b₀ hb')
          r₀ r' hp₀ hp' hk₀
      exact (blocked_foldl [b] c hcoh).mpr hbl
    · exact Or.inr (Or.inr hE)

theorem final_keyAt {K : ResourceRecord} {E : UInt32} :
    ∀ (L : List ByteArray) (c : DnsCache), UniformTtls L →
    (∃ b ∈ L, ∃ r, RRParse.parseRaw (RR := ResourceRecord) b = some r ∧
      SameKey r K ∧ r.ttl ≠ 0 ∧ ¬ Blocked c r cred now ∧
      now + r.ttl.toNat.toUInt32 = E) →
    ∀ e ∈ (L.foldl (storeStep cred now) c).records, SameKey e.rr K →
      e.expiry = E
  | [], _, _, hex => by
    obtain ⟨b, hb, _⟩ := hex
    exact absurd hb (List.not_mem_nil)
  | b :: L, c, hu, hex => by
    rw [List.foldl_cons]
    obtain ⟨b', hb', r', hp', hk', httl', hnb', hE'⟩ := hex
    rcases List.mem_cons.mp hb' with rfl | htail
    ·
      have hstep : KeyAt K E (storeStep cred now c b') := by
        unfold storeStep
        rw [hp']
        dsimp only []
        rcases storeChecked_cases c r' cred now with ⟨h0, _⟩ | ⟨_, hbl, _⟩ |
            ⟨_, _, heq⟩
        · exact absurd h0 httl'
        · exact absurd hbl hnb'
        · rw [heq]
          exact keyAt_store hk' hE'
      exact keyAt_foldl L _ (uniformTtls_tail hu)
        (fun b₀ hb₀ r₀ hp₀ hk₀ => Or.inr (Or.inr (by
          rw [← hE']
          have := hu b₀ (List.mem_cons_of_mem b' hb₀) b' List.mem_cons_self
            r₀ r' hp₀ hp' (sameKey_trans hk₀ (sameKey_symm hk'))
          rw [this]))) hstep
    ·
      refine final_keyAt L _ (uniformTtls_tail hu)
        ⟨b', htail, r', hp', hk', httl', ?_, hE'⟩
      intro hblocked
      apply hnb'
      have hcoh : ∀ b₀ ∈ [b], ∀ r₀,
          RRParse.parseRaw (RR := ResourceRecord) b₀ = some r₀ →
          SameKey r₀ r' → r₀.ttl = r'.ttl := by
        intro b₀ hb₀ r₀ hp₀ hk₀
        have hbeq : b₀ = b := by simpa using hb₀
        subst hbeq
        exact hu b₀ List.mem_cons_self b' (List.mem_cons_of_mem b₀ htail)
          r₀ r' hp₀ hp' hk₀
      exact (blocked_foldl [b] c hcoh).mp hblocked

def OneExpiryPerKey (c : DnsCache) : Prop :=
  ∀ e₁ ∈ c.records, ∀ e₂ ∈ c.records, SameKey e₁.rr e₂.rr → e₁.expiry = e₂.expiry

theorem oneExpiry_empty : OneExpiryPerKey DnsCache.empty := by
  intro e₁ he₁; simp [DnsCache.empty] at he₁

theorem oneExpiry_store {c : DnsCache} {rr : ResourceRecord} {now : UInt32}
    {cred : Trustworthiness} (h : OneExpiryPerKey c) :
    OneExpiryPerKey (c.store rr now cred) := by

  have key : ∀ e ∈ (c.store rr now cred).records, SameKey e.rr rr →
      e.expiry = now + rr.ttl.toNat.toUInt32 := by
    intro e he hke
    rcases mem_store_iff.mp he with ⟨_, hnrem⟩ | hnew
    · by_contra hne; exact hnrem ⟨hke, Or.inl hne⟩
    · rw [hnew]
  intro e₁ he₁ e₂ he₂ hk
  by_cases hr : SameKey e₁.rr rr
  · have h2 : SameKey e₂.rr rr := sameKey_trans (sameKey_symm hk) hr
    rw [key e₁ he₁ hr, key e₂ he₂ h2]
  ·
    rcases mem_store_iff.mp he₁ with ⟨hold₁, _⟩ | hnew₁
    · rcases mem_store_iff.mp he₂ with ⟨hold₂, _⟩ | hnew₂
      · exact h e₁ hold₁ e₂ hold₂ hk
      · exact absurd (by rw [hnew₂] at hk; exact hk) hr
    · rw [hnew₁] at hr; exact absurd (sameKey_refl _) hr

theorem oneExpiry_storeStep {c : DnsCache} {b : ByteArray}
    (cred : Trustworthiness) (now : UInt32) (h : OneExpiryPerKey c) :
    OneExpiryPerKey (storeStep cred now c b) := by
  unfold storeStep
  cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
  | none => exact h
  | some r =>
    dsimp only []
    rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
        ⟨_, _, heq⟩
    · rw [heq]; exact h
    · rw [heq]; exact h
    · rw [heq]; exact oneExpiry_store h

theorem oneExpiry_foldl (cred : Trustworthiness) (now : UInt32) :
    ∀ (L : List ByteArray) (c : DnsCache), OneExpiryPerKey c →
      OneExpiryPerKey (L.foldl (storeStep cred now) c)
  | [], _, h => h
  | b :: L, c, h => by
    rw [List.foldl_cons]
    exact oneExpiry_foldl cred now L _ (oneExpiry_storeStep cred now h)

theorem oneExpiry_cacheRRs (c : DnsCache) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) (h : OneExpiryPerKey c) :
    OneExpiryPerKey (cacheRRs (C := DnsCache) (RR := ResourceRecord) c raws cred now) := by
  rw [cacheRRs_eq]; exact oneExpiry_foldl cred now raws.toList c h

theorem oneExpiry_bound {c : DnsCache} (h : OneExpiryPerKey c) :
    OneExpiryPerKey c.boundExpiryClasses := by
  unfold DnsCache.boundExpiryClasses
  obtain ⟨p, hp⟩ := evictClasses_filter_form c.records c.records.size
  rw [hp]
  intro e₁ he₁ e₂ he₂ hk
  exact h e₁ (Array.mem_filter.mp he₁).1 e₂ (Array.mem_filter.mp he₂).1 hk

theorem oneExpiry_sweep {c : DnsCache} (h : OneExpiryPerKey c) (now : UInt32) :
    OneExpiryPerKey (c.sweep now) := by
  intro e₁ he₁ e₂ he₂ hk
  exact h e₁ (Array.mem_filter.mp he₁).1 e₂ (Array.mem_filter.mp he₂).1 hk

theorem oneExpiry_touchKeys {c : DnsCache} (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : OneExpiryPerKey c) :
    OneExpiryPerKey (c.touchKeys ks tnow) := by
  intro e₁ he₁ e₂ he₂ hk
  rw [touchKeys_records] at he₁ he₂
  obtain ⟨a₁, ha₁, hm₁⟩ := Array.mem_map.mp he₁
  obtain ⟨a₂, ha₂, hm₂⟩ := Array.mem_map.mp he₂
  subst hm₁; subst hm₂
  rw [touchEntry_rr, touchEntry_rr] at hk
  rw [touchEntry_expiry, touchEntry_expiry]
  exact h a₁ ha₁ a₂ ha₂ hk

theorem oneExpiry_boundLruKeys {c : DnsCache} (h : OneExpiryPerKey c) :
    OneExpiryPerKey c.boundLruKeys := by
  unfold DnsCache.boundLruKeys
  obtain ⟨p, hp⟩ := evictLruKeys_filter_form c.records c.records.size
  rw [hp]
  intro e₁ he₁ e₂ he₂ hk
  exact h e₁ (Array.mem_filter.mp he₁).1 e₂ (Array.mem_filter.mp he₂).1 hk

theorem oneExpiry_boundLru {c : DnsCache} (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : OneExpiryPerKey c) :
    OneExpiryPerKey (c.boundLru ks tnow) :=
  oneExpiry_boundLruKeys (oneExpiry_touchKeys ks tnow h)

def LowFloor (trr : ResourceRecord) (E : UInt32) (cred : Trustworthiness)
    (c : DnsCache) : Prop :=
  ∀ e ∈ c.records, SameKey e.rr trr → e.expiry = E →
    cred.toCode ≤ e.credibility.toCode

theorem lowFloor_store {c : DnsCache} {rr : ResourceRecord} {now : UInt32}
    {cred : Trustworthiness} {trr : ResourceRecord} {E : UInt32}
    (h : LowFloor trr E cred c) : LowFloor trr E cred (c.store rr now cred) := by
  intro e he hk hexp
  rcases mem_store_iff.mp he with ⟨hold, _⟩ | hnew
  · exact h e hold hk hexp
  · rw [hnew]; exact Nat.le_refl _

theorem lowFloor_storeStep {c : DnsCache} {b : ByteArray}
    {cred : Trustworthiness} {now : UInt32} {trr : ResourceRecord} {E : UInt32}
    (h : LowFloor trr E cred c) : LowFloor trr E cred (storeStep cred now c b) := by
  unfold storeStep
  cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
  | none => exact h
  | some r =>
    dsimp only []
    rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
        ⟨_, _, heq⟩
    · rw [heq]; exact h
    · rw [heq]; exact h
    · rw [heq]; exact lowFloor_store h

theorem lowFloor_foldl {cred : Trustworthiness} {now : UInt32}
    {trr : ResourceRecord} {E : UInt32} :
    ∀ (L : List ByteArray) (c : DnsCache), LowFloor trr E cred c →
      LowFloor trr E cred (L.foldl (storeStep cred now) c)
  | [], _, h => h
  | b :: L, c, h => by
    rw [List.foldl_cons]
    exact lowFloor_foldl L _ (lowFloor_storeStep h)

theorem mem_foldl_keep {cred : Trustworthiness} {now : UInt32} {e₀ : CacheEntry} :
    ∀ (L : List ByteArray) (c : DnsCache), UniformTtls L → e₀ ∈ c.records →
    (∀ b ∈ L, ∀ r, RRParse.parseRaw (RR := ResourceRecord) b = some r →
      SameKey r e₀.rr → r.ttl ≠ 0 → Blocked c r cred now) →
    e₀ ∈ (L.foldl (storeStep cred now) c).records
  | [], _, _, h0, _ => h0
  | b :: L, c, hu, h0, hbl => by
    rw [List.foldl_cons]
    have hkeep : e₀ ∈ (storeStep cred now c b).records := by
      unfold storeStep
      cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
      | none => exact h0
      | some r =>
        dsimp only []
        rcases storeChecked_cases c r cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
            ⟨httlr, hnbr, heq⟩
        · rw [heq]; exact h0
        · rw [heq]; exact h0
        · rw [heq]
          have hnsk : ¬ SameKey r e₀.rr := fun hsk =>
            hnbr (hbl b List.mem_cons_self r hp hsk httlr)
          exact mem_store_iff.mpr (Or.inl ⟨h0, fun hrem => hnsk (sameKey_symm hrem.1)⟩)
    refine mem_foldl_keep L _ (uniformTtls_tail hu) hkeep ?_
    intro b' hb' r' hp' hsk' httl'
    have hcoh : ∀ r₀, RRParse.parseRaw (RR := ResourceRecord) b = some r₀ →
        SameKey r₀ r' → r₀.ttl = r'.ttl := fun r₀ hp₀ hk₀ =>
      hu b List.mem_cons_self b' (List.mem_cons_of_mem b hb') r₀ r' hp₀ hp' hk₀
    exact (blocked_storeStep hcoh).mpr (hbl b' (List.mem_cons_of_mem b hb') r' hp' hsk' httl')

private theorem sameKey_tree_record {T : Node ResourceRecord}
    (hsane : TreeSane T) {y : ResourceRecord} {n : Node ResourceRecord}
    (hn : nodeAtName T y.name = some n) (hin : RRInTree T y)
    {trr : ResourceRecord} (htrr : trr ∈ n.resourceSet.toList)
    (hty : trr.type = y.type) : SameKey trr y := by
  obtain ⟨n', hn', trr₀, htrr₀, hdata₀⟩ := hin
  rw [hn] at hn'
  cases hn'
  obtain ⟨hn₀, _, hc₀, _⟩ := sameData_iff.mp hdata₀
  refine ⟨hsane.named y.name n hn trr htrr, hty, ?_⟩
  calc trr.class = trr₀.class := hsane.classUniform y.name n hn trr htrr trr₀ htrr₀
    _ = y.class := hc₀.symm ▸ rfl

private theorem floor_pos : 0 < untrustworthyFloor := by decide

theorem lookupComplete_cacheRRs {T : Node ResourceRecord} {c : DnsCache}
    (hsane : TreeSane T) (hagreeC : CacheAgrees T c) (h : LookupComplete T c)
    {raws : Array ByteArray} (hagree : SectionAgrees T raws)
    (hwhole : SectionWhole T raws) (huni : TtlUniform raws)
    (cred : Trustworthiness) (now : UInt32) :
    LookupComplete T
      (cacheRRs (C := DnsCache) (RR := ResourceRecord) c raws cred now) := by
  rw [cacheRRs_eq]
  have hu := uniformTtls_of raws huni
  intro e he hcred n hn trr htrr hty
  have hnamed : nameEqCI trr.name e.rr.name = true := hsane.named e.rr.name n hn trr htrr
  have hn_trr : nodeAtName T trr.name = some n := by rw [nodeAtName_congr hnamed]; exact hn

  have touched : ∀ (bw : ByteArray) (rw : ResourceRecord),
      bw ∈ raws.toList → RRParse.parseRaw (RR := ResourceRecord) bw = some rw →
      SameKey rw trr → ¬ Blocked c rw cred now → rw.ttl ≠ 0 →
      cred.toCode < untrustworthyFloor →
      ∃ e' ∈ (raws.toList.foldl (storeStep cred now) c).records,
        sameData e'.rr trr = true ∧ e'.expiry = now + rw.ttl.toNat.toUInt32 ∧
        e'.credibility.toCode < untrustworthyFloor ∧
        (∀ e₂ ∈ (raws.toList.foldl (storeStep cred now) c).records,
          SameKey e₂.rr e'.rr → e₂.expiry = e'.expiry →
          e'.credibility.toCode ≤ e₂.credibility.toCode) := by
    intro bw rw hbw hpw hkw hnbw httlw hcfloor
    have hnrw : nodeAtName T rw.name = some n := by rw [nodeAtName_congr hkw.1]; exact hn_trr
    obtain ⟨b', hb', r', hp', hd'⟩ := hwhole bw hbw rw hpw n hnrw trr htrr hkw.2.1.symm
    have hkr'rw : SameKey r' rw := sameKey_trans (sameKey_of_sameData hd') (sameKey_symm hkw)
    have httl' : r'.ttl = rw.ttl :=
      huni b' hb' bw hbw r' rw hp' hpw hkr'rw.1 hkr'rw.2.1 hkr'rw.2.2
    have hnb' : ¬ Blocked c r' cred now := fun hbl =>
      hnbw ((blocked_congr hkr'rw httl').mp hbl)
    have hlowbase : LowFloor trr (now + rw.ttl.toNat.toUInt32) cred c := by
      intro e₂ he₂ hk₂ hexp₂
      by_contra hlt
      exact hnbw ⟨e₂, he₂, sameKey_trans hk₂ (sameKey_symm hkw), Or.inr hexp₂,
        Nat.lt_of_not_le hlt⟩
    have hlowfinal := lowFloor_foldl (cred := cred) (now := now) (trr := trr)
      (E := now + rw.ttl.toNat.toUInt32) raws.toList c hlowbase
    obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hb'
    have hmemL₁ : ∀ {b₁ : ByteArray}, b₁ ∈ L₁ → b₁ ∈ raws.toList := by
      intro b₁ hb₁; rw [hsplit]; exact List.mem_append_left _ hb₁
    have hmemL₂ : ∀ {b₁ : ByteArray}, b₁ ∈ L₂ → b₁ ∈ raws.toList := by
      intro b₁ hb₁; rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hb₁)
    have hfold_eq : raws.toList.foldl (storeStep cred now) c =
        L₂.foldl (storeStep cred now)
          (storeStep cred now (L₁.foldl (storeStep cred now) c) b') := by
      rw [hsplit, List.foldl_append, List.foldl_cons]
    have hnb'' : ¬ Blocked (L₁.foldl (storeStep cred now) c) r' cred now := by
      intro hbl
      apply hnb'
      refine (blocked_foldl L₁ c ?_).mp hbl
      intro b₀ hb₀ r₀ hp₀ hk₀
      exact hu b₀ (hmemL₁ hb₀) b' hb' r₀ r' hp₀ hp' hk₀
    have hsat : Sat trr (now + rw.ttl.toNat.toUInt32) cred.toCode
        (storeStep cred now (L₁.foldl (storeStep cred now) c) b') := by
      rw [storeStep_some hp']
      rcases storeChecked_cases (L₁.foldl (storeStep cred now) c) r' cred now
        with ⟨h0, _⟩ | ⟨_, hbl, _⟩ | ⟨_, _, heq⟩
      · exact absurd (httl'.symm.trans h0) httlw
      · exact absurd hbl hnb''
      · rw [heq]
        exact ⟨⟨r', now + r'.ttl.toNat.toUInt32, false, cred, now⟩,
          mem_store_iff.mpr (Or.inr rfl), hd', by rw [httl'], Nat.le_refl _⟩
    have huL₂ : UniformTtls L₂ := fun b₁ hb₁ b₂ hb₂ =>
      hu b₁ (hmemL₂ hb₁) b₂ (hmemL₂ hb₂)
    have hkeyh : ∀ b₁ ∈ L₂, ∀ r₁,
        RRParse.parseRaw (RR := ResourceRecord) b₁ = some r₁ → SameKey r₁ trr →
        r₁.ttl = 0 ∨
          Blocked (storeStep cred now (L₁.foldl (storeStep cred now) c) b') r₁ cred now ∨
          now + r₁.ttl.toNat.toUInt32 = now + rw.ttl.toNat.toUInt32 := by
      intro b₁ hb₁ r₁ hp₁ hk₁
      refine Or.inr (Or.inr ?_)
      have : r₁.ttl = rw.ttl :=
        hu b₁ (hmemL₂ hb₁) bw hbw r₁ rw hp₁ hpw (sameKey_trans hk₁ (sameKey_symm hkw))
      rw [this]
    obtain ⟨e', he', hd_e', hexp_e', hcred_e'⟩ :=
      sat_foldl (cred := cred) (now := now) L₂ _ huL₂ hkeyh hsat
    refine ⟨e', by rw [hfold_eq]; exact he', hd_e', hexp_e',
      Nat.lt_of_le_of_lt hcred_e' hcfloor, ?_⟩
    intro e₂ he₂ hk₂ hexp₂
    exact Nat.le_trans hcred_e'
      (hlowfinal e₂ he₂ (sameKey_trans hk₂ (sameKey_of_sameData hd_e')) (hexp₂.trans hexp_e'))
  rcases mem_foldl_store raws.toList c hu he with hold |
      ⟨b, hb, r, hparse, heq, httl, hnb⟩
  ·
    obtain ⟨e₀', he₀', hdata₀, hexp₀, hcred₀, hmax₀⟩ := h e hold hcred n hn trr htrr hty
    have hkey_trr : SameKey trr e.rr :=
      sameKey_tree_record hsane hn (hagreeC.positives e hold).1 htrr hty
    by_cases hex : ∃ b ∈ raws.toList, ∃ r,
        RRParse.parseRaw (RR := ResourceRecord) b = some r ∧
        SameKey r e.rr ∧ r.ttl ≠ 0 ∧ ¬ Blocked c r cred now
    ·
      obtain ⟨b, hb, r, hparse, hkr, httl, hnb⟩ := hex
      have hEe : e.expiry = now + r.ttl.toNat.toUInt32 :=
        final_keyAt raws.toList c hu
          ⟨b, hb, r, hparse, hkr, httl, hnb, rfl⟩ e he (sameKey_refl _)
      have hcfloor : cred.toCode < untrustworthyFloor := by
        have hcredle : cred.toCode ≤ e.credibility.toCode := by
          by_contra hlt
          exact hnb ⟨e, hold, sameKey_symm hkr, Or.inr hEe, Nat.lt_of_not_le hlt⟩
        exact Nat.lt_of_le_of_lt hcredle hcred
      obtain ⟨e', he', hd', hexp', hcfl', hmax'⟩ :=
        touched b r hb hparse (sameKey_trans hkr (sameKey_symm hkey_trr)) hnb httl hcfloor
      exact ⟨e', he', hd', by rw [hexp']; exact hEe.symm, hcfl', hmax'⟩
    ·
      have hbl_all : ∀ b' ∈ raws.toList, ∀ r',
          RRParse.parseRaw (RR := ResourceRecord) b' = some r' →
          SameKey r' e₀'.rr → r'.ttl ≠ 0 → Blocked c r' cred now := by
        intro b' hb' r' hp' hk' h0
        by_contra hnbl
        exact hex ⟨b', hb', r', hp',
          sameKey_trans (sameKey_trans hk' (sameKey_of_sameData hdata₀)) hkey_trr, h0, hnbl⟩
      have hfin : e₀' ∈ (raws.toList.foldl (storeStep cred now) c).records :=
        mem_foldl_keep raws.toList c hu he₀' hbl_all
      refine ⟨e₀', hfin, hdata₀, hexp₀, hcred₀, ?_⟩
      intro e₂ he₂ hk₂ hexp₂
      have he₂c : e₂ ∈ c.records := by
        rcases mem_foldl_store raws.toList c hu he₂ with ho |
            ⟨b₂, hb₂, r₂, hp₂, heq₂, httl₂, hnb₂⟩
        · exact ho
        · exfalso
          apply hex
          have hsk : SameKey r₂ e.rr := by
            have hrr : e₂.rr = r₂ := by rw [heq₂]
            rw [← hrr]
            exact sameKey_trans (sameKey_trans hk₂ (sameKey_of_sameData hdata₀)) hkey_trr
          exact ⟨b₂, hb₂, r₂, hp₂, hsk, httl₂, hnb₂⟩
      exact hmax₀ e₂ he₂c hk₂ hexp₂
  ·
    subst heq
    have hinr : RRInTree T r :=
      rrInTree_of_rrAgrees (hagree b (by simpa using hb)) hparse
    have hkey_trr : SameKey trr r := sameKey_tree_record hsane hn hinr htrr hty
    exact touched b r hb hparse (sameKey_symm hkey_trr) hnb httl hcred

private theorem bv1_eq_zero {b : BitVec 1} (h : ¬ b = 1) : b = 0 := by
  have hlt := b.isLt
  apply BitVec.eq_of_toNat_eq
  have h1 : ¬ b.toNat = 1 := fun he => h (BitVec.eq_of_toNat_eq (by simpa using he))
  have h0 : (0 : BitVec 1).toNat = 0 := rfl
  omega



theorem minTtlB_toNat (x y : BitVec 32) : (minTtlB x y).toNat = min x.toNat y.toNat := by
  unfold minTtlB
  by_cases h : y.toNat < x.toNat
  · simp only [h, if_true]; omega
  · simp only [h, if_false]; omega

theorem minTtlB_cases (x y : BitVec 32) : minTtlB x y = x ∨ minTtlB x y = y := by
  unfold minTtlB
  by_cases h : y.toNat < x.toNat
  · exact Or.inr (by simp [h])
  · exact Or.inl (by simp [h])

theorem foldl_minTtl_props (L : List ResourceRecord) (p : ResourceRecord → Bool) (s : BitVec 32) :
    ((L.foldl (fun acc e => if p e then minTtlB acc e.ttl else acc) s).toNat ≤ s.toNat)
    ∧ (∀ e ∈ L, p e → (L.foldl (fun acc e => if p e then minTtlB acc e.ttl else acc) s).toNat
        ≤ e.ttl.toNat)
    ∧ ((L.foldl (fun acc e => if p e then minTtlB acc e.ttl else acc) s) = s
        ∨ ∃ e ∈ L, p e = true
            ∧ (L.foldl (fun acc e => if p e then minTtlB acc e.ttl else acc) s) = e.ttl) := by
  induction L generalizing s with
  | nil => exact ⟨Nat.le_refl _, by simp, Or.inl rfl⟩
  | cons a L ih =>
    simp only [List.foldl_cons]
    obtain ⟨ihle, ihall, ihatt⟩ := ih (if p a = true then minTtlB s a.ttl else s)
    have hs'le : (if p a = true then minTtlB s a.ttl else s).toNat ≤ s.toNat := by
      by_cases hp : p a = true
      · rw [if_pos hp, minTtlB_toNat]; exact Nat.min_le_left _ _
      · exact Nat.le_of_eq (by rw [if_neg hp])
    refine ⟨Nat.le_trans ihle hs'le, ?_, ?_⟩
    · intro e he hpe
      rcases List.mem_cons.mp he with rfl | heL
      · have hthis : (if p e = true then minTtlB s e.ttl else s).toNat ≤ e.ttl.toNat := by
          rw [if_pos hpe, minTtlB_toNat]; exact Nat.min_le_right _ _
        exact Nat.le_trans ihle hthis
      · exact ihall e heL hpe
    · rcases ihatt with heq | ⟨e, heL, hpe, heq⟩
      · by_cases hp : p a = true
        · simp only [if_pos hp] at heq ⊢
          rcases minTtlB_cases s a.ttl with hm | hm
          · exact Or.inl (heq.trans hm)
          · exact Or.inr ⟨a, List.mem_cons_self, hp, heq.trans hm⟩
        · simp only [if_neg hp] at heq ⊢
          exact Or.inl heq
      · exact Or.inr ⟨e, List.mem_cons_of_mem a heL, hpe, heq⟩

theorem rrSameKeyB_iff {a b : ResourceRecord} : rrSameKeyB a b = true ↔ SameKey a b := by
  unfold rrSameKeyB SameKey
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨hn, ht⟩, hc⟩ => ⟨hn, ht, hc⟩, fun ⟨hn, ht, hc⟩ => ⟨⟨hn, ht⟩, hc⟩⟩

theorem rrSameKeyB_refl (a : ResourceRecord) : rrSameKeyB a a = true :=
  rrSameKeyB_iff.mpr (sameKey_refl a)

theorem rrSameKeyB_symm {a b : ResourceRecord} (h : rrSameKeyB a b = true) :
    rrSameKeyB b a = true :=
  rrSameKeyB_iff.mpr (sameKey_symm (rrSameKeyB_iff.mp h))

theorem rrSameKeyB_trans {a b c : ResourceRecord} (h₁ : rrSameKeyB a b = true)
    (h₂ : rrSameKeyB b c = true) : rrSameKeyB a c = true :=
  rrSameKeyB_iff.mpr (sameKey_trans (rrSameKeyB_iff.mp h₁) (rrSameKeyB_iff.mp h₂))

theorem groupMinTtl_congr {rrs : List ResourceRecord} {a b : ResourceRecord}
    (ha : a ∈ rrs) (hb : b ∈ rrs) (hk : rrSameKeyB a b = true) :
    groupMinTtl rrs a = groupMinTtl rrs b := by
  obtain ⟨_, hia, hiiia⟩ := foldl_minTtl_props rrs (fun e => rrSameKeyB e a) a.ttl
  obtain ⟨_, hib, hiiib⟩ := foldl_minTtl_props rrs (fun e => rrSameKeyB e b) b.ttl
  have hle_ab : (groupMinTtl rrs a).toNat ≤ (groupMinTtl rrs b).toNat := by
    rcases hiiib with hseed | ⟨e, heL, hpe, heq⟩
    · rw [show groupMinTtl rrs b = b.ttl from hseed]
      exact hia b hb (rrSameKeyB_symm hk)
    · rw [show groupMinTtl rrs b = e.ttl from heq]
      exact hia e heL (rrSameKeyB_trans hpe (rrSameKeyB_symm hk))
  have hle_ba : (groupMinTtl rrs b).toNat ≤ (groupMinTtl rrs a).toNat := by
    rcases hiiia with hseed | ⟨e, heL, hpe, heq⟩
    · rw [show groupMinTtl rrs a = a.ttl from hseed]
      exact hib a ha hk
    · rw [show groupMinTtl rrs a = e.ttl from heq]
      exact hib e heL (rrSameKeyB_trans hpe hk)
  exact BitVec.toNat_inj.mp (Nat.le_antisymm hle_ab hle_ba)

theorem normRaws_uniform (raws : Array ByteArray) :
    UniformTtls (normRaws raws).toList := by
  intro b₁ hb₁ b₂ hb₂ r₁' r₂' hp₁ hp₂ hk
  obtain ⟨r₁, hr₁, hb₁eq⟩ := mem_normRaws hb₁
  obtain ⟨r₂, hr₂, hb₂eq⟩ := mem_normRaws hb₂
  have hrt₁ := parseRaw_normMember hr₁
  have hrt₂ := parseRaw_normMember hr₂
  rw [hb₁eq] at hp₁
  rw [hb₂eq] at hp₂
  have hr1' : r₁' = _ := Option.some.inj (hp₁.symm.trans hrt₁)
  have hr2' : r₂' = _ := Option.some.inj (hp₂.symm.trans hrt₂)
  subst hr1' hr2'
  exact groupMinTtl_congr hr₁ hr₂ (rrSameKeyB_iff.mpr hk)

theorem normRaws_TtlUniform (raws : Array ByteArray) : TtlUniform (normRaws raws) := by
  intro b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ hn ht hc
  exact normRaws_uniform raws b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ ⟨hn, ht, hc⟩

theorem sectionWhole_normRaws {T : Node ResourceRecord} {raws : Array ByteArray}
    (h : SectionWhole T raws) : SectionWhole T (normRaws raws) := by
  intro bn hbn rr' hp' n hn trr htrr hty
  obtain ⟨r, hr, rfl⟩ := parseRaw_mem_normRaws hbn hp'
  obtain ⟨b, hb, hpb⟩ := List.mem_filterMap.mp hr
  have hpb' : RRParse.parseRaw (RR := ResourceRecord) b = some r := hpb
  obtain ⟨b'', hb'', rr'', hp'', hdata⟩ := h b hb r hpb' n hn trr htrr hty
  refine ⟨RRParse.rrBytes (RR := ResourceRecord) { rr'' with ttl := groupMinTtl (rrsOf raws) rr'' },
    mem_normRaws_of (List.mem_filterMap.mpr ⟨b'', hb'', hp''⟩),
    { rr'' with ttl := groupMinTtl (rrsOf raws) rr'' },
    parseRaw_normMember (List.mem_filterMap.mpr ⟨b'', hb'', hp''⟩), ?_⟩
  exact sameData_set_ttl _ hdata

theorem lookupComplete_cacheUnlessTruncated {T : Node ResourceRecord}
    {c : DnsCache} (hsane : TreeSane T) (hagreeC : CacheAgrees T c)
    (h : LookupComplete T c) (resp : Format) {raws : Array ByteArray}
    (hagree : SectionAgrees T raws)
    (hwhole : resp.header.tc = 0 → SectionWhole T raws)
    (huni : resp.header.tc = 0 → TtlUniform raws)
    (cred : Trustworthiness) (now : UInt32) :
    LookupComplete T
      (cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
        c resp raws cred now) := by
  unfold cacheUnlessTruncated
  split
  · exact h
  · next htc =>
    have h0 : resp.header.tc = 0 :=
      bv1_eq_zero (fun he => htc (by rw [he]; simp))
    exact lookupComplete_cacheRRs hsane hagreeC h (sectionAgrees_normRaws hagree)
      (sectionWhole_normRaws (hwhole h0)) (normRaws_TtlUniform raws) cred now

theorem ttlUniform_bailiwick (qname : ByteArray) {answer : Array ByteArray}
    (hu : TtlUniform answer) :
    TtlUniform (bailiwickRaws (RR := ResourceRecord) qname answer) := by
  intro b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ hname htype hcls
  exact hu b₁ (bailiwickRaws_subset _ _ hb₁) b₂
    (bailiwickRaws_subset _ _ hb₂) r₁ r₂ hp₁ hp₂ hname htype hcls

theorem isAncestorB_congr (bw o1 o2 : ByteArray) (h : nameEqCI o1 o2 = true) :
    isAncestorB bw o1 = isAncestorB bw o2 := by
  have hfold : foldNameCase o1 = foldNameCase o2 := nameEqCI_iff.mp h
  unfold isAncestorB
  cases hbw : VeriDNS.Impl.DomainName.wireFormatToLabels bw with
  | error _ => simp [hbw]
  | ok bwL =>
    cases h1 : VeriDNS.Impl.DomainName.wireFormatToLabels o1 with
    | error e1 =>
      obtain ⟨e1', he1'⟩ := wireFormatToLabels_fold_error o1 e1 h1
      cases h2 : VeriDNS.Impl.DomainName.wireFormatToLabels o2 with
      | error _ => simp [hbw, h1, h2]
      | ok L2 =>
        have e2' := wireFormatToLabels_fold_ok o2 L2 h2
        rw [← hfold, he1'] at e2'; exact absurd e2' (by simp)
    | ok L1 =>
      cases h2 : VeriDNS.Impl.DomainName.wireFormatToLabels o2 with
      | error e2 =>
        obtain ⟨e2', he2'⟩ := wireFormatToLabels_fold_error o2 e2 h2
        have e1' := wireFormatToLabels_fold_ok o1 L1 h1
        rw [hfold, he2'] at e1'; exact absurd e1' (by simp)
      | ok L2 =>
        have hLL : L1.map foldNameCase = L2.map foldNameCase := by
          have e1' := wireFormatToLabels_fold_ok o1 L1 h1
          have e2' := wireFormatToLabels_fold_ok o2 L2 h2
          rw [hfold, e2'] at e1'; injection e1' with e1'; exact e1'.symm
        have hLLt : L1.toList.map foldNameCase = L2.toList.map foldNameCase := by
          have := congrArg Array.toList hLL; simpa using this
        simp only [hbw, h1, h2, hLLt]

theorem sectionWhole_bailiwick {T : Node ResourceRecord} (hsane : TreeSane T)
    (bw : ByteArray) {answer : Array ByteArray}
    (hw : SectionWhole T answer) :
    SectionWhole T (bailiwickRaws (RR := ResourceRecord) bw answer) := by
  intro b hb rr hpr n hn trr htrr htyp
  obtain ⟨b', hb'mem, rr', hpr', hsame⟩ :=
    hw b (bailiwickRaws_subset _ _ hb) rr hpr n hn trr htrr htyp

  have hkept : isAncestorB bw (RRParse.rrName rr) = true :=
    bailiwickRaws_owner_inBailiwick _ _ hb hpr

  have htn : nameEqCI trr.name rr.name = true := hsane.named rr.name n hn trr htrr
  have hrr' : nameEqCI rr'.name trr.name = true := by
    unfold sameData at hsame
    simp only [Bool.and_eq_true] at hsame
    exact hsame.1.1.1
  have hcong : nameEqCI rr'.name rr.name = true := nameEqCI_trans hrr' htn
  refine ⟨b', ?_, rr', hpr', hsame⟩
  have hbf' : b' ∈ bailiwickRaws (RR := ResourceRecord) bw answer := by
    unfold bailiwickRaws
    apply Array.mem_filter.mpr
    refine ⟨Array.mem_def.mpr hb'mem, ?_⟩
    simp only [hpr']
    show isAncestorB bw rr'.name = true
    rw [isAncestorB_congr bw rr'.name rr.name hcong]; exact hkept
  exact Array.mem_def.mp hbf'

theorem ttlUniform_owner (sname : ByteArray) {answer : Array ByteArray}
    (hu : TtlUniform answer) :
    TtlUniform (ownerRaws (RR := ResourceRecord) sname answer) := by
  intro b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ hname htype hcls
  exact hu b₁ (ownerRaws_subset _ _ hb₁) b₂
    (ownerRaws_subset _ _ hb₂) r₁ r₂ hp₁ hp₂ hname htype hcls

theorem sectionWhole_owner {T : Node ResourceRecord} (hsane : TreeSane T)
    (sname : ByteArray) {answer : Array ByteArray}
    (hw : SectionWhole T answer) :
    SectionWhole T (ownerRaws (RR := ResourceRecord) sname answer) := by
  intro b hb rr hpr n hn trr htrr htyp
  obtain ⟨b', hb'mem, rr', hpr', hsame⟩ :=
    hw b (ownerRaws_subset _ _ hb) rr hpr n hn trr htrr htyp
  have hkept : nameEqCI (RRParse.rrName rr) sname = true :=
    ownerRaws_owner_eq _ _ hb hpr
  have htn : nameEqCI trr.name rr.name = true := hsane.named rr.name n hn trr htrr
  have hrr' : nameEqCI rr'.name trr.name = true := by
    unfold sameData at hsame
    simp only [Bool.and_eq_true] at hsame
    exact hsame.1.1.1
  have hcong : nameEqCI rr'.name rr.name = true := nameEqCI_trans hrr' htn
  refine ⟨b', ?_, rr', hpr', hsame⟩
  have hbf' : b' ∈ ownerRaws (RR := ResourceRecord) sname answer := by
    unfold VeriDNS.Impl.Resolver.ownerRaws
    apply Array.mem_filter.mpr
    refine ⟨Array.mem_def.mpr hb'mem, ?_⟩
    simp only [hpr']
    show nameEqCI rr'.name sname = true
    exact nameEqCI_trans hcong hkept
  exact Array.mem_def.mp hbf'


theorem ttlUniform_cnameOwner (sname : ByteArray) {answer : Array ByteArray}
    (hu : TtlUniform answer) :
    TtlUniform (cnameRaws (RR := ResourceRecord) sname answer) := by
  intro b₁ hb₁ b₂ hb₂ r₁ r₂ hp₁ hp₂ hname htype hcls
  exact hu b₁ (cnameRaws_subset _ _ hb₁) b₂
    (cnameRaws_subset _ _ hb₂) r₁ r₂ hp₁ hp₂ hname htype hcls

theorem sectionWhole_cnameOwner {T : Node ResourceRecord} (hsane : TreeSane T)
    (sname : ByteArray) {answer : Array ByteArray}
    (hw : SectionWhole T answer) :
    SectionWhole T (cnameRaws (RR := ResourceRecord) sname answer) := by
  intro b hb rr hpr n hn trr htrr htyp
  obtain ⟨b', hb'mem, rr', hpr', hsame⟩ :=
    hw b (cnameRaws_subset _ _ hb) rr hpr n hn trr htrr htyp
  have hkeptP := cnameRaws_pred (RR := ResourceRecord) _ _ hb hpr
  simp only [Bool.and_eq_true] at hkeptP
  have hkept : nameEqCI (RRParse.rrName rr) sname = true := hkeptP.2
  have hty5 : rr.type = (5 : BitVec 16) := eq_of_beq hkeptP.1
  have htn : nameEqCI trr.name rr.name = true := hsane.named rr.name n hn trr htrr
  unfold sameData at hsame
  simp only [Bool.and_eq_true] at hsame
  have hrr' : nameEqCI rr'.name trr.name = true := hsame.1.1.1
  have hcong : nameEqCI rr'.name rr.name = true := nameEqCI_trans hrr' htn
  have hty' : rr'.type = (5 : BitVec 16) := by
    have h1 : rr'.type = trr.type := eq_of_beq hsame.1.1.2
    rw [h1, htyp, hty5]
  refine ⟨b', ?_, rr', hpr', ?_⟩
  · have hbf' : b' ∈ cnameRaws (RR := ResourceRecord) sname answer := by
      unfold VeriDNS.Impl.Resolver.cnameRaws
      apply Array.mem_filter.mpr
      refine ⟨Array.mem_def.mpr hb'mem, ?_⟩
      simp only [hpr']
      show (rr'.type == (5 : BitVec 16) && nameEqCI rr'.name sname) = true
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hty', nameEqCI_trans hcong hkept⟩
    exact Array.mem_def.mp hbf'
  · unfold sameData
    simp only [Bool.and_eq_true]
    exact hsame

theorem oneExpiry_cacheUnlessTruncated {c : DnsCache} (h : OneExpiryPerKey c)
    (resp : Format) (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32) :
    OneExpiryPerKey
      (cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
        c resp raws cred now) := by
  unfold cacheUnlessTruncated
  split
  · exact h
  · exact oneExpiry_cacheRRs c (normRaws raws) cred now h

end CacheFold

section ServingEdge

private theorem answerableEntry_iff {e : CacheEntry} {name : ByteArray}
    {qtype qclass : BitVec 16} {now : UInt32} :
    answerableEntry e name qtype qclass now = true ↔
      nameEqCI e.rr.name name = true ∧ e.rr.type = qtype ∧
      e.rr.class = qclass ∧ e.expiry > now ∧
      e.credibility.toCode < untrustworthyFloor := by
  unfold answerableEntry liveEntry CacheEntry.fresh
  simp only [Bool.and_eq_true, decide_eq_true_eq, bv16_beq_iff]
  exact ⟨fun ⟨⟨⟨⟨hn, ht⟩, hc⟩, hf⟩, hb⟩ => ⟨hn, ht, hc, hf, hb⟩,
    fun ⟨hn, ht, hc, hf, hb⟩ => ⟨⟨⟨⟨hn, ht⟩, hc⟩, hf⟩, hb⟩⟩

private theorem sameRRKey_sameKey {a b : CacheEntry} (h : sameRRKey a b = true) :
    SameKey a.rr b.rr := by
  unfold sameRRKey at h
  simp only [Bool.and_eq_true, bv16_beq_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem mem_lookupAnswerable {c : DnsCache} {name : ByteArray}
    {qtype qclass : BitVec 16} {now : UInt32} {rr : ResourceRecord} :
    rr ∈ c.lookupAnswerable name qtype qclass now ↔
      ∃ e ∈ c.records, answerableEntry e name qtype qclass now = true ∧
        c.maxCredForKey e name qtype qclass now = true ∧
        rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold DnsCache.lookupAnswerable
  rw [Array.mem_filterMap]
  constructor
  · rintro ⟨e, hm, hf⟩
    split at hf
    · next hcond =>
      rw [Bool.and_eq_true] at hcond
      exact ⟨e, hm, hcond.1, hcond.2, (Option.some.inj hf).symm⟩
    · cases hf
  · rintro ⟨e, hm, ha, hmx, rfl⟩
    exact ⟨e, hm, by rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨ha, hmx⟩)]⟩

private theorem entry_node {T : Node ResourceRecord} {c : DnsCache}
    (hagree : CacheAgrees T c) {e : CacheEntry} (hm : e ∈ c.records)
    {name : ByteArray} (hci : nameEqCI e.rr.name name = true)
    {n : Node ResourceRecord} (hn : nodeAtName T name = some n) :
    nodeAtName T e.rr.name = some n ∧
    ∃ trr₀ ∈ n.resourceSet.toList, sameData trr₀ e.rr = true := by
  have hnn : nodeAtName T e.rr.name = some n := by
    rw [nodeAtName_congr hci]
    exact hn
  obtain ⟨n', hn', trr₀, htrr₀, hdata₀⟩ := (hagree.positives e hm).1
  rw [hnn] at hn'
  cases hn'
  exact ⟨hnn, trr₀, htrr₀, hdata₀⟩

theorem lookupAnswerable_whole {T : Node ResourceRecord} {c : DnsCache}
    (hsane : TreeSane T) (hagree : CacheAgrees T c)
    (hlc : LookupComplete T c) (hone : OneExpiryPerKey c)
    {name : ByteArray} {qtype qclass : BitVec 16}
    {now : UInt32} {rr₀ : ResourceRecord}
    (hmem : rr₀ ∈ c.lookupAnswerable name qtype qclass now)
    {n : Node ResourceRecord} (hn : nodeAtName T name = some n)
    {trr : ResourceRecord} (htrr : trr ∈ n.resourceSet.toList)
    (hty : trr.type = qtype) :
    ∃ rr' ∈ c.lookupAnswerable name qtype qclass now,
      sameData rr' trr = true := by
  obtain ⟨e, hm, ha, _, _⟩ := mem_lookupAnswerable.mp hmem
  obtain ⟨hci, htyE, hclE, hfr, hcr⟩ := answerableEntry_iff.mp ha
  obtain ⟨hnn, trr₀, htrr₀, hdata₀⟩ := entry_node hagree hm hci hn
  obtain ⟨e', he', hdata', hexp', hcred', hmax'⟩ :=
    hlc e hm hcr n hnn trr htrr (hty.trans htyE.symm)
  obtain ⟨hn', ht', hc', _⟩ := sameData_iff.mp hdata'

  have ha' : answerableEntry e' name qtype qclass now = true := by
    rw [answerableEntry_iff]
    refine ⟨?_, ?_, ?_, ?_, hcred'⟩
    · exact nameEqCI_trans hn' (hsane.named name n hn trr htrr)
    · rw [ht', hty]
    · calc e'.rr.class = trr.class := hc'
        _ = trr₀.class := hsane.classUniform name n hn trr htrr trr₀ htrr₀
        _ = e.rr.class := (sameData_iff.mp hdata₀).2.2.1
        _ = qclass := hclE
    · rw [hexp']; exact hfr

  have hmx' : c.maxCredForKey e' name qtype qclass now = true := by
    unfold DnsCache.maxCredForKey
    refine Array.all_eq_true.mpr (fun i hi => ?_)
    have he2 : c.records[i] ∈ c.records := Array.getElem_mem hi
    by_cases hcond : (answerableEntry c.records[i] name qtype qclass now
        && sameRRKey c.records[i] e') = true
    · rw [Bool.and_eq_true] at hcond
      have hsk : SameKey c.records[i].rr e'.rr := sameRRKey_sameKey hcond.2
      have hsame : c.records[i].expiry = e'.expiry := hone c.records[i] he2 e' he' hsk
      rw [Bool.or_eq_true]; right
      rw [decide_eq_true_eq]
      exact hmax' c.records[i] he2 hsk hsame
    · simp only [Bool.not_eq_true] at hcond
      rw [Bool.or_eq_true]; left; rw [hcond]; rfl
  exact ⟨{ e'.rr with ttl := BitVec.ofNat 32 (e'.expiry - now).toNat },
    mem_lookupAnswerable.mpr ⟨e', he', ha', hmx', rfl⟩, sameData_set_ttl _ hdata'⟩

theorem lookupNegative_verdict {T : Node ResourceRecord} {c : DnsCache}
    (hneg : NegativesFaithful T c) {name : ByteArray}
    {qtype qclass : BitVec 16} {now : UInt32} {rc : Rcode}
    (h : DnsCache.lookupNegative c name qtype qclass now = some rc) :
    (rc = Rcode.nameError ∧ treeLookup T name qtype = .nameError) ∨
    (rc = Rcode.noError ∧ treeLookup T name qtype = .nodata) := by
  unfold DnsCache.lookupNegative DnsCache.lookupNxdomain at h
  rcases hor : c.negatives.findSome? (fun e =>
      if nameEqCI e.name name && e.qclass == qclass && e.expiry > now
          && e.rcode == Rcode.nameError then some e.rcode else none)
      with _ | rc0
  ·
    rw [hor] at h
    simp at h
    obtain ⟨e, hmem, hcond⟩ := Array.exists_of_findSome?_eq_some h
    split at hcond
    · next hkeyB =>
      cases hcond
      try simp only [Bool.and_eq_true] at hkeyB
      have hci : nameEqCI e.name name = true := hkeyB.1.1.1
      have hqt : e.qtype = qtype := by
        have h2 := hkeyB.1.1.2
        first | exact h2 | exact eq_of_beq h2
      obtain ⟨hnx, hnod, hrcs⟩ := hneg e hmem
      rcases hrcs with hrc | hrc
      · refine Or.inl ⟨hrc, ?_⟩
        rw [treeLookup_nameError_iff, ← nodeAtName_congr hci]
        exact hnx hrc
      · refine Or.inr ⟨hrc, ?_⟩
        rw [← treeLookup_congr hci qtype, ← hqt]
        exact hnod hrc
    · cases hcond
  ·
    rw [hor] at h
    simp at h
    cases h
    obtain ⟨e, hmem, hcond⟩ := Array.exists_of_findSome?_eq_some hor
    split at hcond
    · next hkeyB =>
      cases hcond
      try simp only [Bool.and_eq_true] at hkeyB
      have hci : nameEqCI e.name name = true := hkeyB.1.1.1
      have hrcE : e.rcode = Rcode.nameError := by
        have h2 := hkeyB.2
        first
        | exact h2
        | (revert h2; cases e.rcode <;> intro h2 <;>
            first | rfl | exact absurd h2 (by decide))
      refine Or.inl ⟨hrcE, ?_⟩
      rw [treeLookup_nameError_iff, ← nodeAtName_congr hci]
      exact (hneg e hmem).1 hrcE
    · cases hcond

end ServingEdge

section LocalChase

open VeriDNS.Impl.Resolver

private theorem rrType_eq (rr : ResourceRecord) :
    RRParse.rrType (RR := ResourceRecord) rr = rr.type := rfl

private theorem rrRdata_eq (rr : ResourceRecord) :
    RRParse.rrRdata (RR := ResourceRecord) rr = rr.rdata := rfl

private theorem entry_node' {T : Node ResourceRecord} {c : DnsCache}
    (hagree : CacheAgrees T c) {e : CacheEntry} (hm : e ∈ c.records)
    {name : ByteArray} (hci : nameEqCI e.rr.name name = true) :
    ∃ n, nodeAtName T name = some n ∧
      ∃ trr₀ ∈ n.resourceSet.toList, sameData trr₀ e.rr = true := by
  obtain ⟨n', hn', trr₀, htrr₀, hdata₀⟩ := (hagree.positives e hm).1
  exact ⟨n', by rw [← nodeAtName_congr hci]; exact hn', trr₀, htrr₀, hdata₀⟩

private theorem treeLookup_redirect_of_cname {T : Node ResourceRecord}
    (hsane : TreeSane T) {sname : ByteArray} {n : Node ResourceRecord}
    (hn : nodeAtName T sname = some n) {crr : ResourceRecord}
    (htrr : crr ∈ n.resourceSet.toList) (hty : crr.type = cnameType)
    {qtype : BitVec 16} (hq : qtype ≠ cnameType) :
    ∃ rrStar, treeLookup T sname qtype = .redirect rrStar crr.rdata := by
  have hall := hsane.cnameExclusive sname n hn
    ⟨crr, htrr, by rw [rrType_eq, hty]; exact bv16_beq_iff.mpr rfl⟩

  have hempty : ¬ (n.resourceSet.filter
      (fun rr => RRParse.rrType rr == qtype)).size > 0 := by
    intro hpos
    obtain ⟨x, hx⟩ := Array.exists_mem_of_size_pos hpos
    obtain ⟨hxm, hxt⟩ := Array.mem_filter.mp hx
    have h5 := hall x (by simpa using hxm)
    rw [rrType_eq] at hxt h5
    exact hq ((bv16_beq_iff.mp hxt).symm.trans (bv16_beq_iff.mp h5))

  have hfsome : (n.resourceSet.find?
      (fun rr => RRParse.rrType rr == cnameType)).isSome = true := by
    rw [Array.find?_isSome]
    exact ⟨crr, by simpa using htrr,
      by rw [rrType_eq, hty]; exact bv16_beq_iff.mpr rfl⟩
  obtain ⟨rrStar, hrrStar⟩ := Option.isSome_iff_exists.mp hfsome
  have hmemStar : rrStar ∈ n.resourceSet := Array.mem_of_find?_eq_some hrrStar
  have htyStar : rrStar.type = cnameType := by
    have := Array.find?_some (p := fun r =>
      RRParse.rrType r == cnameType) hrrStar
    rw [rrType_eq] at this
    exact bv16_beq_iff.mp this
  have hrd : rrStar.rdata = crr.rdata :=
    hsane.cnameUnique sname n hn rrStar (by simpa using hmemStar) crr htrr
      htyStar hty
  refine ⟨rrStar, ?_⟩
  unfold treeLookup
  rw [hn]
  dsimp only []
  unfold lookupAt
  dsimp only []
  rw [if_neg hempty, hrrStar]
  dsimp only []
  rw [if_neg (fun h => hq (bv16_beq_iff.mp h)), rrRdata_eq, hrd]

theorem localAnswer_complete {T : Node ResourceRecord} {c : DnsCache}
    (hsane : TreeSane T) (hagree : CacheAgrees T c) (hlc : LookupComplete T c)
    (hone : OneExpiryPerKey c)
    (hneg : NegativesFaithful T c) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray),
    (match localAnswer (C := DnsCache) (RR := ResourceRecord)
        c qtype qclass now fuel sname chain visited with
     | .negative rc _ chain' =>
         (∃ s', Reaches T qtype sname s' ∧
           ((rc = Rcode.nameError ∧ treeLookup T s' qtype = .nameError) ∨
            (rc = Rcode.noError ∧ treeLookup T s' qtype = .nodata))) ∧
         (∀ b ∈ chain'.toList, b ∈ chain.toList ∨
           (qtype ≠ cnameType ∧
            ∃ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
              rr.type = cnameType))
     | .answerHit s' chain' rrs =>
         Reaches T qtype sname s' ∧
         (∃ matching, treeLookup T s' qtype = .answer matching ∧
           ∀ trr ∈ matching.toList, ∃ rr' ∈ rrs, sameData rr' trr = true) ∧
         (∀ rr' ∈ rrs, RRInTree T rr' ∧ WfRR rr') ∧
         (∀ b ∈ chain'.toList, b ∈ chain.toList ∨
           (qtype ≠ cnameType ∧
            ∃ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
              rr.type = cnameType))
     | .miss s' chain' =>
         Reaches T qtype sname s' ∧
         (∀ b ∈ chain'.toList, b ∈ chain.toList ∨
           (qtype ≠ cnameType ∧
            ∃ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
              rr.type = cnameType))
     | .abort => True)
  | 0, sname, chain, visited => by
    unfold localAnswer
    trivial
  | fuel + 1, sname, chain, visited => by
    unfold localAnswer
    cases hret : NegativeCacheSpec.retrieveNegative (C := DnsCache)
        c sname qtype qclass now with
    | some rc =>

      exact ⟨⟨sname, .refl (nameEqCI_refl _), lookupNegative_verdict hneg hret⟩,
        fun b hb => Or.inl hb⟩
    | none =>
      dsimp only []
      by_cases hempty : (TrustworthinessSpec.answers (C := DnsCache)
          c sname qtype qclass now : Array ResourceRecord).isEmpty = true
      · rw [if_pos hempty]
        by_cases hq5 : (qtype == (5 : BitVec 16)) = true
        · rw [if_pos hq5]
          exact ⟨.refl (nameEqCI_refl _), fun b hb => Or.inl hb⟩
        · rw [if_neg hq5]
          cases hcrr : (TrustworthinessSpec.answers (C := DnsCache)
              c sname (5 : BitVec 16) qclass now : Array ResourceRecord)[0]? with
          | none =>
            exact ⟨.refl (nameEqCI_refl _), fun b hb => Or.inl hb⟩
          | some crr =>
            dsimp only []
            by_cases hrev : (visited.any (fun v => nameEqCI v (RRParse.rrRdata (RR := ResourceRecord) crr))) = true
            · rw [if_pos hrev]
              exact ⟨.refl (nameEqCI_refl _), fun b hb => Or.inl hb⟩
            rw [if_neg hrev]
            have hmemc : crr ∈ (TrustworthinessSpec.answers (C := DnsCache)
                c sname (5 : BitVec 16) qclass now : Array ResourceRecord) :=
              Array.mem_of_getElem? hcrr
            obtain ⟨ec, hmc, hac, _, hceq⟩ := mem_lookupAnswerable.mp hmemc
            obtain ⟨hciC, htyC, _, _, _⟩ := answerableEntry_iff.mp hac
            obtain ⟨ns, hns, trrC, htrrC, hdataC⟩ := entry_node' hagree hmc hciC
            have htyTrr : trrC.type = cnameType :=
              ((sameData_iff.mp hdataC).2.1).trans htyC
            have hqne : qtype ≠ cnameType := fun h =>
              hq5 (bv16_beq_iff.mpr h)
            obtain ⟨rrStar, hlook⟩ :=
              treeLookup_redirect_of_cname hsane hns htrrC htyTrr hqne
            have hrdc : nameEqCI trrC.rdata
                (RRParse.rrRdata (RR := ResourceRecord) crr) = true := by
              rw [rrRdata_eq, hceq]
              have h4 := (sameData_iff.mp hdataC).2.2.2
              rw [htyC, rdataEqCI_cname] at h4
              exact h4
            have hstep : Reaches T qtype sname
                (RRParse.rrRdata (RR := ResourceRecord) crr) :=
              .step (.refl (nameEqCI_refl sname)) hlook hrdc

            have hwfc : WfRR crr := by
              rw [hceq]
              exact wfRR_set_ttl (hagree.positives ec hmc).2 _
            have hparsec : RRParse.parseRaw (RR := ResourceRecord)
                (RRParse.rrBytes (RR := ResourceRecord) crr) = some crr :=
              parseRaw_rrBytes_of_wf hwfc
            have htypec : crr.type = cnameType := by
              rw [hceq]
              exact htyC

            have ih := localAnswer_complete hsane hagree hlc hone hneg qtype qclass
              now fuel (RRParse.rrRdata (RR := ResourceRecord) crr)
              (chain.push (RRParse.rrBytes (RR := ResourceRecord) crr))
              (visited.push (RRParse.rrRdata (RR := ResourceRecord) crr))
            have hchainpush : ∀ b ∈ (chain.push
                (RRParse.rrBytes (RR := ResourceRecord) crr)).toList,
                b ∈ chain.toList ∨
                (qtype ≠ cnameType ∧
                 ∃ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
                   rr.type = cnameType) := by
              intro b hb
              rcases Array.mem_push.mp (Array.mem_def.mpr hb) with hl | rfl
              · exact Or.inl (Array.mem_def.mp hl)
              · exact Or.inr ⟨hqne, crr, hparsec, htypec⟩
            rcases hres : localAnswer (C := DnsCache) (RR := ResourceRecord)
                c qtype qclass now fuel
                (RRParse.rrRdata (RR := ResourceRecord) crr)
                (chain.push (RRParse.rrBytes (RR := ResourceRecord) crr))
                (visited.push (RRParse.rrRdata (RR := ResourceRecord) crr)) with
              ⟨rc, soaAuth⟩ | ⟨s', chain', rrs⟩ | ⟨s', chain'⟩ | _
            · dsimp only []
              rw [hres] at ih
              obtain ⟨⟨s', hreach, hverd⟩, hchain⟩ := ih
              refine ⟨⟨s', reaches_trans hstep hreach, hverd⟩, ?_⟩
              intro b hb
              rcases hchain b hb with hl | hc
              · exact hchainpush b hl
              · exact Or.inr hc
            · dsimp only []
              rw [hres] at ih
              obtain ⟨hreach, hmatch, hwfs, hchain⟩ := ih
              refine ⟨reaches_trans hstep hreach, hmatch, hwfs, ?_⟩
              intro b hb
              rcases hchain b hb with hl | hc
              · exact hchainpush b hl
              · exact Or.inr hc
            · dsimp only []
              rw [hres] at ih
              obtain ⟨hreach, hchain⟩ := ih
              refine ⟨reaches_trans hstep hreach, ?_⟩
              intro b hb
              rcases hchain b hb with hl | hc
              · exact hchainpush b hl
              · exact Or.inr hc
            · dsimp only []
      ·
        rw [if_neg hempty]
        have hpos : 0 < (TrustworthinessSpec.answers (C := DnsCache)
            c sname qtype qclass now : Array ResourceRecord).size := by
          rcases Nat.eq_zero_or_pos (TrustworthinessSpec.answers (C := DnsCache)
              c sname qtype qclass now : Array ResourceRecord).size with h0 | h
          · exact absurd (by
              rw [Array.isEmpty_iff]
              exact Array.eq_empty_of_size_eq_zero h0) hempty
          · exact h
        obtain ⟨rr₀, hmem₀⟩ := Array.exists_mem_of_size_pos hpos
        obtain ⟨e₀, hm₀, ha₀, _, h₀eq⟩ := mem_lookupAnswerable.mp hmem₀
        obtain ⟨hci₀, hty₀, _, _, _⟩ := answerableEntry_iff.mp ha₀
        obtain ⟨n, hn, trr₀, htrr₀, hdata₀⟩ := entry_node' hagree hm₀ hci₀
        have htyT₀ : trr₀.type = qtype :=
          ((sameData_iff.mp hdata₀).2.1).trans hty₀
        have htrr₀f : trr₀ ∈ n.resourceSet.filter
            (fun rr => RRParse.rrType rr == qtype) := by
          refine Array.mem_filter.mpr ⟨by simpa using htrr₀, ?_⟩
          rw [rrType_eq, htyT₀]
          exact bv16_beq_iff.mpr rfl
        have hposf : (n.resourceSet.filter
            (fun rr => RRParse.rrType rr == qtype)).size > 0 :=
          Array.size_pos_iff.mpr
            (fun he => Array.not_mem_empty trr₀ (he ▸ htrr₀f))
        refine ⟨.refl (nameEqCI_refl _),
          ⟨n.resourceSet.filter (fun rr => RRParse.rrType rr == qtype),
            ?_, ?_⟩,
          fun rr' h => lookupAnswerable_agrees hagree _ _ _ _ rr' h,
          fun b hb => Or.inl hb⟩
        · unfold treeLookup
          rw [hn]
          dsimp only []
          unfold lookupAt
          dsimp only []
          rw [if_pos hposf]
        · intro trr htrrm
          have h2 : trr ∈ n.resourceSet ∧ RRParse.rrType trr = qtype := by
            simpa using htrrm
          exact lookupAnswerable_whole hsane hagree hlc hone hmem₀ hn
            (by simpa using h2.1) h2.2

end LocalChase

section StepCompleteness

open VeriDNS.Impl.Resolver

variable {S NS : Type} [SlistSpec S NS] [SlistFromNameSpec S NS] [Inhabited S]

structure StateOK (T : Node ResourceRecord) (q₀ : Format) (qu₀ : Question)
    (s : State S DnsCache NS ResourceRecord) : Prop where
  agrees : StateAgrees T s
  complete : LookupComplete T s.resources.cache
  oneExp : OneExpiryPerKey s.resources.cache
  negs : NegativesFaithful T s.resources.cache
  query : s.lastQuery = some q₀
  question : q₀.question[0]? = some qu₀
  reach : Reaches T qu₀.qtype qu₀.qname s.resources.sname
  chainFree : ∀ b ∈ s.cnameChain.toList, ∀ rr,
    RRParse.parseRaw (RR := ResourceRecord) b = some rr →
    ¬ rr.type = qu₀.qtype
  respNone : s.currentStep = .checkAnswer ∨ s.currentStep = .findServers →
    s.lastResponse = none
  respMatch : ∀ r, s.lastResponse = some r →
    VeriDNS.Impl.Server.probePassableB r = false →
    ∃ qu, r.question[0]? = some qu ∧
      nameEqCI qu.qname s.resources.sname = true ∧
      qu.qtype = qu₀.qtype ∧ qu.qclass = qu₀.qclass

private theorem storeChecked_negatives (c : DnsCache) (rr : ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) :
    (c.storeChecked rr cred now).negatives = c.negatives := by
  rcases storeChecked_cases c rr cred now with ⟨_, heq⟩ | ⟨_, _, heq⟩ |
      ⟨_, _, heq⟩
  · rw [heq]
  · rw [heq]
  · rw [heq]
    rfl

private theorem cacheRRs_negatives (c : DnsCache) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) :
    (cacheRRs (C := DnsCache) (RR := ResourceRecord)
      c raws cred now).negatives = c.negatives := by
  rw [cacheRRs_eq]
  induction raws.toList generalizing c with
  | nil => rfl
  | cons b L ih =>
    rw [List.foldl_cons, ih]
    unfold storeStep
    cases RRParse.parseRaw (RR := ResourceRecord) b with
    | none => rfl
    | some r => exact storeChecked_negatives c r cred now

theorem negativesFaithful_cacheUnlessTruncated {T : Node ResourceRecord}
    {c : DnsCache} (h : NegativesFaithful T c) (resp : Format)
    (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32) :
    NegativesFaithful T
      (cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
        c resp raws cred now) := by
  unfold cacheUnlessTruncated
  split
  · exact h
  · intro ne hne
    rw [cacheRRs_negatives] at hne
    exact h ne hne

private theorem finalizeAnswer_rcode
    (s : State S DnsCache NS ResourceRecord) (r : Format) :
    (finalizeAnswer s r).header.rcode = r.header.rcode := by
  unfold finalizeAnswer prependChain
  cases s.lastQuery <;> dsimp only [] <;> split <;> rfl

private theorem finalizeAnswer_tc
    (s : State S DnsCache NS ResourceRecord) (r : Format) :
    (finalizeAnswer s r).header.tc = r.header.tc := by
  unfold finalizeAnswer prependChain
  cases s.lastQuery <;> dsimp only [] <;> split <;> rfl

private theorem finalizeAnswer_answer_mem
    {s : State S DnsCache NS ResourceRecord} {r : Format} {b : ByteArray}
    (hb : b ∈ r.answer.toList) : b ∈ (finalizeAnswer s r).answer.toList := by
  unfold finalizeAnswer prependChain
  cases s.lastQuery <;> dsimp only [] <;> split <;>
    first
      | exact hb
      | exact Array.mem_def.mp (Array.mem_append.mpr
          (Or.inr (Array.mem_def.mpr hb)))

private theorem finalizeAnswer_answer_sub
    {s : State S DnsCache NS ResourceRecord} {r : Format} :
    ∀ b ∈ (finalizeAnswer s r).answer.toList,
      b ∈ s.cnameChain.toList ∨ b ∈ r.answer.toList := by
  unfold finalizeAnswer prependChain
  cases s.lastQuery <;> dsimp only [] <;> split <;>
    first
      | exact fun b hb => Or.inr hb
      | (intro b hb
         rcases Array.mem_append.mp (Array.mem_def.mpr hb) with hl | hr
         · exact Or.inl (Array.mem_def.mp hl)
         · exact Or.inr (Array.mem_def.mp hr))

private theorem hasType_iff_hasRRTypeIn {rrs : Array ByteArray}
    {code : BitVec 16} :
    hasRRTypeIn (RR := ResourceRecord) rrs code = true ↔ HasType rrs code := by
  unfold hasRRTypeIn HasType
  rw [Array.any_eq_true']
  constructor
  · rintro ⟨b, hb, hcond⟩
    revert hcond
    cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
    | none => intro hcond; cases hcond
    | some rr =>
      intro hcond
      exact ⟨b, by simpa using hb, rr, hp, bv16_beq_iff.mp hcond⟩
  · rintro ⟨b, hb, rr, hp, hty⟩
    refine ⟨b, by simpa using hb, ?_⟩
    rw [hp]
    exact bv16_beq_iff.mpr hty

private theorem extractCname_some {sname : ByteArray} {rrs : Array ByteArray}
    {canonical : ByteArray}
    (h : extractCname (RR := ResourceRecord) sname rrs = some canonical) :
    ∃ b ∈ rrs.toList, ∃ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
      rr.type = cnameType ∧ rr.rdata = canonical := by
  unfold extractCname at h
  obtain ⟨b, hb, hcond⟩ := Array.exists_of_findSome?_eq_some h
  revert hcond
  cases hp : RRParse.parseRaw (RR := ResourceRecord) b with
  | none => intro hcond; cases hcond
  | some rr =>
    intro hcond
    dsimp only [] at hcond
    split at hcond
    · next hty =>
      cases hcond
      exact ⟨b, by simpa using hb, rr, hp,
        bv16_beq_iff.mp (Bool.and_eq_true _ _ |>.mp hty).1, rfl⟩
    · cases hcond

private theorem extractCname_none {sname : ByteArray} {rrs : Array ByteArray}
    (h : extractCname (RR := ResourceRecord) sname rrs = none) :
    ¬ HasOwnedCname sname rrs := by
  rintro ⟨b, hb, rr, hp, hty, hown⟩
  unfold extractCname at h
  have hnone := Array.findSome?_eq_none_iff.mp h b (by simpa using hb)
  rw [hp] at hnone
  dsimp only [] at hnone
  rw [if_pos (show (RRParse.rrType (RR := ResourceRecord) rr == (5 : BitVec 16)
      && VeriDNS.Impl.DomainName.nameEqCI (RRParse.rrName (RR := ResourceRecord) rr) sname) = true
    from Bool.and_eq_true _ _ |>.mpr ⟨bv16_beq_iff.mpr hty, hown⟩)] at hnone
  cases hnone

private theorem answersFromTree_of_terminal {T : Node ResourceRecord}
    {qu₀ : Question} {r : Format} {s' : ByteArray}
    (hreach : Reaches T qu₀.qtype qu₀.qname s')
    {o : Outcome ResourceRecord} (hlook : treeLookup T s' qu₀.qtype = o)
    (hterm : ∀ rr c, o ≠ .redirect rr c)
    (hagrees : SectionAgrees T r.answer)
    (hclause : match o with
      | .nameError => r.header.rcode = Rcode.nameError
      | .answer rrsT => r.header.rcode = Rcode.noError ∧
          ∀ rr ∈ rrsT.toList, ∃ b ∈ r.answer.toList, ∃ rr',
            RRParse.parseRaw (RR := ResourceRecord) b = some rr' ∧
            sameData rr' rr = true
      | .nodata => r.header.rcode = Rcode.noError ∧
          ¬ ∃ b ∈ r.answer.toList, ∃ rr,
            RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
            (rr.type == qu₀.qtype) = true
      | .redirect _ _ => True) :
    ∀ fuel, AnswersFromTree T qu₀.qname qu₀.qtype fuel r := by
  intro fuel
  refine ⟨hagrees, ?_⟩
  cases htr : treeResolve T qu₀.qtype fuel qu₀.qname #[] with
  | none => exact True.intro
  | some res =>
    obtain ⟨c', o'⟩ := res
    have ho := reaches_terminal_pins hreach hlook hterm htr
    subst ho
    cases o' with
    | answer rrsT => exact hclause
    | nodata => exact hclause
    | nameError => exact hclause
    | redirect rr canonical => exact True.intro

private theorem answersFromTree_of_answer {T : Node ResourceRecord}
    {qu₀ : Question} {r : Format} {s' : ByteArray}
    (hreach : Reaches T qu₀.qtype qu₀.qname s')
    {k : Nat} {chT : Array ResourceRecord} {rrsT : Array ResourceRecord}
    (hres : treeResolve T qu₀.qtype k s' #[] = some (chT, .answer rrsT))
    (hagrees : SectionAgrees T r.answer)
    (hrc : r.header.rcode = Rcode.noError)
    (hdeliver : ∀ rr ∈ rrsT.toList, ∃ b ∈ r.answer.toList, ∃ rr',
      RRParse.parseRaw (RR := ResourceRecord) b = some rr' ∧
      sameData rr' rr = true) :
    ∀ fuel, AnswersFromTree T qu₀.qname qu₀.qtype fuel r := by
  intro fuel
  refine ⟨hagrees, ?_⟩
  obtain ⟨f', c', hback⟩ := reaches_resolve_back hreach hres
  cases htr : treeResolve T qu₀.qtype fuel qu₀.qname #[] with
  | none => exact True.intro
  | some res =>
    obtain ⟨c'', o''⟩ := res
    have ho := treeResolve_unique htr hback
    subst ho
    exact ⟨hrc, hdeliver⟩

private theorem negativeResponse_rcode (q : Format) (rc : Rcode)
    (soaAuth : Array ResourceRecord) :
    (negativeResponse (RR := ResourceRecord) q rc soaAuth).header.rcode = rc :=
  rfl

private theorem negativeResponse_answer (q : Format) (rc : Rcode)
    (soaAuth : Array ResourceRecord) :
    (negativeResponse (RR := ResourceRecord) q rc soaAuth).answer = #[] := rfl

private theorem cacheResponse_rcode (q : Format) (rrs : Array ResourceRecord) :
    (cacheResponse (RR := ResourceRecord) q rrs).header.rcode =
      Rcode.noError := rfl

private theorem answersQueryB_eq {resp : Format} {qu : Question}
    (hq : resp.question[0]? = some qu) :
    answersQueryB (RR := ResourceRecord) resp
      = hasRRTypeIn (RR := ResourceRecord) resp.answer qu.qtype := by
  unfold answersQueryB
  rw [hq]

/-- An entitled answer is in particular a type-matching answer: from
    `entitledAnswerB = true` extract the plain `hasRRTypeIn` fact the
    completeness proof needs (the 2026-07-15 off-owner tightening replaced the
    `answersQueryB` acceptance guard with `entitledAnswerB`). -/
private theorem hasRRTypeIn_of_entitled {resp : Format} {qu : Question}
    (hq : resp.question[0]? = some qu)
    (h : entitledAnswerB (RR := ResourceRecord) resp = true) :
    hasRRTypeIn (RR := ResourceRecord) resp.answer qu.qtype = true := by
  rw [← answersQueryB_eq hq]
  exact answersQueryB_of_entitled (RR := ResourceRecord) resp h

private theorem not_type_of_hasRRTypeIn_false {rrs : Array ByteArray}
    {code : BitVec 16}
    (h : ¬ hasRRTypeIn (RR := ResourceRecord) rrs code = true) :
    ∀ b ∈ rrs.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr →
      ¬ rr.type = code := by
  intro b hb rr hp hty
  exact h (hasType_iff_hasRRTypeIn.mpr ⟨b, hb, rr, hp, hty⟩)

private theorem hasRRTypeIn_empty {rrs : Array ByteArray} {code : BitVec 16}
    (h : rrs.isEmpty = true) :
    ¬ hasRRTypeIn (RR := ResourceRecord) rrs code = true := by
  intro hcon
  obtain ⟨b, hb, _, _, _⟩ := hasType_iff_hasRRTypeIn.mp hcon
  rw [Array.isEmpty_iff] at h
  subst h
  simp at hb

private theorem lookupAnswerable_parse_back {T : Node ResourceRecord}
    {c : DnsCache} (hagree : CacheAgrees T c) {name : ByteArray}
    {qtype qclass : BitVec 16} {now : UInt32} {rr : ResourceRecord}
    (hmem : rr ∈ c.lookupAnswerable name qtype qclass now) :
    RRParse.parseRaw (RR := ResourceRecord)
      (RRParse.rrBytes (RR := ResourceRecord) rr) = some rr :=
  parseRaw_rrBytes_of_wf (lookupAnswerable_agrees hagree name qtype qclass
    now rr hmem).2

private theorem stepCheckLocal_answer_cache {s : State S DnsCache NS ResourceRecord}
    {r : Format} {rst : State S DnsCache NS ResourceRecord}
    (h : stepCheckLocal s = .answer r rst) :
    rst.resources.cache = s.resources.cache := by
  unfold stepCheckLocal at h
  repeat' first
  | (cases h; try rfl)
  | split at h

private theorem step_answer_cacheOK {T : Node ResourceRecord} {q₀ : Format} {qu₀ : Question}
    {s : State S DnsCache NS ResourceRecord}
    {r : Format} {rst : State S DnsCache NS ResourceRecord}
    (hsane : TreeSane T) (hs : StateOK T q₀ qu₀ s)
    (hresp : ∀ r', s.lastResponse = some r' → ResponseConsistent T r')
    (h : step s = .answer r rst) :
    CacheAgrees T rst.resources.cache ∧ LookupComplete T rst.resources.cache ∧
    OneExpiryPerKey rst.resources.cache ∧ NegativesFaithful T rst.resources.cache := by
  have base : CacheAgrees T s.resources.cache ∧ LookupComplete T s.resources.cache ∧
      OneExpiryPerKey s.resources.cache ∧ NegativesFaithful T s.resources.cache :=
    ⟨hs.agrees.cache, hs.complete, hs.oneExp, hs.negs⟩
  unfold step at h
  split at h
  · rw [show rst.resources.cache = s.resources.cache from stepCheckLocal_answer_cache h]
    exact base
  · unfold stepFindServers at h
    dsimp only [] at h
    split at h <;> (try split at h) <;> (try split at h) <;> cases h
  · unfold stepSendQueries at h
    split at h <;> cases h
  · unfold stepAnalyzeResponse at h
    split at h
    · cases h
    · next resp heq =>
      have hcons := hresp resp heq
      split at h
      ·
        simp only [] at h
        split at h
        · cases h; exact base
        · split at h <;> cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · split at h
              · cases h; exact base
              · cases h
          · split at h
            ·
              simp only [] at h
              cases h
              refine ⟨?_, ?_, ?_, ?_⟩
              · exact cacheAgrees_cacheUnlessTruncated hs.agrees.cache resp
                  (fun b hb => hcons.answer b (ownerRaws_subset _ _ hb)) _ s.now
              · exact lookupComplete_cacheUnlessTruncated hsane hs.agrees.cache
                  hs.complete resp
                  (fun b hb => hcons.answer b (ownerRaws_subset _ _ hb))
                  (fun h0 => sectionWhole_owner hsane _ (hcons.answerWhole h0))
                  (fun h0 => ttlUniform_owner _ (hcons.answerTtlUniform h0)) _ s.now
              · exact oneExpiry_cacheUnlessTruncated hs.oneExp _ _ _ _
              · exact negativesFaithful_cacheUnlessTruncated hs.negs resp _ _ s.now
            · split at h
              · cases h; exact base
              · split at h
                · cases h; exact base
                · split at h
                  · cases h; exact base
                  · cases h

theorem stepCheckLocal_complete {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : Question} {s : State S DnsCache NS ResourceRecord}
    (hsane : TreeSane T) (hs : StateOK T q₀ qu₀ s)
    (hcur : s.currentStep = .checkAnswer) :
    (∀ r rst, stepCheckLocal s = .answer r rst →
      ∀ fuel, AnswersFromTree T qu₀.qname qu₀.qtype fuel r) ∧
    (∀ st s', stepCheckLocal s = .goto st s' →
      StateOK T q₀ qu₀ { s' with currentStep := st }) := by
  have hresp0 : s.lastResponse = none := hs.respNone (Or.inl hcur)
  have hla := localAnswer_complete hsane hs.agrees.cache hs.complete hs.oneExp hs.negs
    qu₀.qtype qu₀.qclass s.now 8 s.resources.sname s.cnameChain
    (cnameChaseVisited (RR := ResourceRecord) qu₀.qname s.cnameChain)
  have hsound := stepCheckLocal_sound (S := S) (NS := NS) (s := s) hs.agrees
  constructor
  · intro r rst hr
    have hagrees := (hsound.1 r rst hr).1
    unfold stepCheckLocal at hr
    rw [hs.query] at hr
    dsimp only [] at hr
    rw [hs.question] at hr
    dsimp only [] at hr
    split at hr
    ·
      next rc soaAuth chain' heqL =>
      cases hr
      rw [heqL] at hla
      obtain ⟨⟨s', hreach', hverd⟩, hchainprov⟩ := hla
      rcases hverd with ⟨hrc, hlook⟩ | ⟨hrc, hlook⟩
      · exact answersFromTree_of_terminal
          (reaches_trans hs.reach hreach') hlook
          (fun _ _ h => by cases h) hagrees
          (by rw [finalizeAnswer_rcode, negativeResponse_rcode, hrc])
      · refine answersFromTree_of_terminal
          (reaches_trans hs.reach hreach') hlook
          (fun _ _ h => by cases h) hagrees
          ⟨by rw [finalizeAnswer_rcode, negativeResponse_rcode, hrc], ?_⟩
        rintro ⟨b, hb, rr, hp, hty⟩
        rcases finalizeAnswer_answer_sub b hb with hchainb | hrb
        · rcases hchainprov b hchainb with hold | ⟨hqne, rr', hp', hty'⟩
          · exact hs.chainFree b hold rr hp (bv16_beq_iff.mp hty)
          · rw [hp] at hp'
            cases hp'
            exact hqne ((bv16_beq_iff.mp hty) ▸ hty')
        · rw [negativeResponse_answer] at hrb
          simp at hrb
    ·
      next sname' chain' rrs heqL =>
      cases hr
      rw [heqL] at hla
      obtain ⟨hreach', ⟨matching, hlook, hdeliver⟩, hwfs, _⟩ := hla
      refine answersFromTree_of_terminal
        (reaches_trans hs.reach hreach') hlook
        (fun _ _ h => by cases h) hagrees
        ⟨by rw [finalizeAnswer_rcode, cacheResponse_rcode], ?_⟩
      intro trr htrr
      obtain ⟨rr', hrr', hdata'⟩ := hdeliver trr htrr
      refine ⟨RRParse.rrBytes (RR := ResourceRecord) rr',
        finalizeAnswer_answer_mem ?_, rr',
        parseRaw_rrBytes_of_wf (hwfs rr' hrr').2, hdata'⟩
      show RRParse.rrBytes (RR := ResourceRecord) rr'
        ∈ (rrs.map (RRParse.rrBytes (RR := ResourceRecord))).toList
      exact Array.mem_def.mp (Array.mem_map.mpr ⟨rr', hrr', rfl⟩)
    ·
      next sname' chain' heqL =>
      split at hr <;> cases hr
    · cases hr
  · intro st s' hgo
    have hag := (hsound.2 st s' hgo).1
    unfold stepCheckLocal at hgo
    rw [hs.query] at hgo
    dsimp only [] at hgo
    rw [hs.question] at hgo
    dsimp only [] at hgo
    split at hgo
    · cases hgo
    · cases hgo
    · next sname' chain' heqL =>
      rw [heqL] at hla
      obtain ⟨hreach', hchain'⟩ := hla
      split at hgo
      ·
        cases hgo
        exact ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs,
          hs.query, hs.question, hs.reach, hs.chainFree,
          fun _ => hresp0, fun r hr => by rw [hresp0] at hr; cases hr⟩
      ·
        cases hgo
        refine ⟨⟨hag.cache, hag.chain⟩, hs.complete, hs.oneExp, hs.negs,
          rfl, hs.question,
          reaches_trans hs.reach hreach', ?_,
          fun _ => hresp0, fun r hr => by rw [hresp0] at hr; cases hr⟩
        intro b hb rr hp hty
        rcases hchain' b hb with hold | ⟨hqne, rr', hp', hty'⟩
        · exact hs.chainFree b hold rr hp hty
        · rw [hp] at hp'
          cases hp'
          exact hqne (hty ▸ hty')
    · cases hgo

private theorem rcode_beq_eq {a b : Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem rcode_beq_self (a : Rcode) : (a == a) = true := by
  cases a <;> decide

private theorem size_pos_of_not_isEmpty {α : Type} {as : Array α}
    (h : ¬ as.isEmpty = true) : 0 < as.size := by
  rcases Nat.eq_zero_or_pos as.size with h0 | hp
  · exact absurd (by
      rw [Array.isEmpty_iff]
      exact Array.eq_empty_of_size_eq_zero h0) h
  · exact hp

private theorem and5_false_of_tail {p a b c d : Bool}
    (h : (a && b && c && d) = false) : (p && a && b && c && d) = false := by
  revert p a b c d; decide

private theorem probePassable_false_of_chase {resp : Format} {c : ByteArray}
    (h : cnameToChase (RR := ResourceRecord) resp = some c) :
    VeriDNS.Impl.Server.probePassableB resp = false := by
  unfold VeriDNS.Impl.Server.probePassableB VeriDNS.Impl.Server.referralShapedB
    VeriDNS.Impl.Server.retryShapedB
  rw [h]
  rfl

private theorem probePassable_false_of_guards {resp : Format}
    (h4d : ¬ ((resp.header.rcode == Rcode.serverFailure
        || !classifiableB resp) = true))
    (hNS : ¬ ((hasRRTypeIn (RR := ResourceRecord) resp.authority 2
        && resp.header.aa == 0
        && (resp.header.rcode == Rcode.noError)
        && !hasRRTypeIn (RR := ResourceRecord) resp.authority 6) = true)) :
    VeriDNS.Impl.Server.probePassableB resp = false := by
  rw [Bool.not_eq_true] at h4d hNS
  unfold VeriDNS.Impl.Server.probePassableB VeriDNS.Impl.Server.referralShapedB
    VeriDNS.Impl.Server.retryShapedB
  rw [Bool.or_eq_false_iff]
  exact ⟨and5_false_of_tail hNS, by rw [h4d, Bool.and_false]⟩

private theorem probePassable_false_of_not4b {resp : Format}
    (h4d : ¬ ((resp.header.rcode == Rcode.serverFailure
        || !classifiableB resp) = true))
    (h4b : ¬ ((!answersQueryB (RR := ResourceRecord) resp
        && !(resp.header.rcode == Rcode.nameError)
        && resp.answer.isEmpty
        && !resp.authority.isEmpty) = true)) :
    VeriDNS.Impl.Server.probePassableB resp = false := by
  rw [Bool.not_eq_true] at h4d h4b
  unfold VeriDNS.Impl.Server.probePassableB VeriDNS.Impl.Server.referralShapedB
    VeriDNS.Impl.Server.retryShapedB
  rw [Bool.or_eq_false_iff]
  refine ⟨?_, by rw [h4d, Bool.and_false]⟩
  by_contra hc
  rw [Bool.not_eq_false] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hansF⟩, hemp⟩, hane⟩, _⟩, _⟩, hnoerr⟩, _⟩ := hc
  have hne : (resp.header.rcode == Rcode.nameError) = false := by
    rw [rcode_beq_eq hnoerr]; decide
  rw [hansF, hemp, hane, hne] at h4b
  simp at h4b

-- 019: the chase-arm write (`cnameRaws`, an extra type conjunct in the filter
-- closure) pushed the big `split at hgo/hr` elaboration just over the default
-- heartbeat budget; bump it for this theorem only.
set_option maxHeartbeats 1000000 in
theorem stepAnalyzeResponse_complete {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : Question} {s : State S DnsCache NS ResourceRecord}
    (hsane : TreeSane T) (hs : StateOK T q₀ qu₀ s)
    (hresp : ∀ r, s.lastResponse = some r → ResponseConsistent T r) :
    (∀ r rst, stepAnalyzeResponse s = .answer r rst → r.header.tc = 0 →
      ∀ fuel, AnswersFromTree T qu₀.qname qu₀.qtype fuel r) ∧
    (∀ st s', stepAnalyzeResponse s = .goto st s' →
      StateOK T q₀ qu₀ { s' with currentStep := st }) := by
  have hsound := stepAnalyzeResponse_sound (S := S) (NS := NS) (s := s)
    hs.agrees hresp
  constructor
  · intro r rst hr htc
    have hagrees := (hsound.1 r rst hr).1
    unfold stepAnalyzeResponse at hr
    split at hr
    · cases hr
    · next resp heq =>
      have hcons := hresp resp heq
      have hrm := hs.respMatch resp heq
      split at hr
      · simp only [] at hr
        split at hr
        · next hTC =>
          cases hr
          rw [finalizeAnswer_tc] at htc
          rw [htc] at hTC
          simp at hTC
        · split at hr <;> cases hr
      · next hchaseEq =>
        split at hr
        · cases hr
        · next h4d =>
          split at hr
          · next h4b =>
            split at hr
            · cases hr
            · next hNS =>
              split at hr
              ·
                next h410 =>
                cases hr
                obtain ⟨qu_r, hqur, hqci, hqty, hqcl⟩ :=
                  hrm (probePassable_false_of_guards h4d hNS)
                have hqmem : qu_r ∈ resp.question.toList := by
                  have := Array.mem_of_getElem? hqur
                  simpa using this
                rw [finalizeAnswer_tc] at htc
                simp only [Bool.and_eq_true] at h410
                have hrc0 : resp.header.rcode = Rcode.noError :=
                  rcode_beq_eq h410.1.1
                have hnotref : ¬ (HasType resp.authority (2 : BitVec 16)
                    ∧ resp.header.aa = 0 ∧ ¬ HasType resp.authority (6 : BitVec 16)) := by
                  rintro ⟨hNS2, haa2, hnSOA⟩
                  have e1 : hasRRTypeIn (RR := ResourceRecord) resp.authority 2 = true :=
                    hasType_iff_hasRRTypeIn.mpr hNS2
                  have e6 : hasRRTypeIn (RR := ResourceRecord) resp.authority 6 = false :=
                    Bool.eq_false_iff.mpr (fun h => hnSOA (hasType_iff_hasRRTypeIn.mp h))
                  rw [e1, e6, haa2, hrc0] at hNS
                  exact absurd hNS (by decide)
                have hverd := hcons.nodataDeserved qu_r hqmem htc hrc0
                  h410.1.2 hnotref
                rw [hqty, treeLookup_congr hqci] at hverd
                refine answersFromTree_of_terminal hs.reach hverd
                  (fun _ _ h => by cases h) hagrees
                  ⟨by rw [finalizeAnswer_rcode]; exact hrc0, ?_⟩
                rintro ⟨b, hb, rr, hp, htyB⟩
                rcases finalizeAnswer_answer_sub b hb with hch | hresp'
                · exact hs.chainFree b hch rr hp (bv16_beq_iff.mp htyB)
                · rw [Array.isEmpty_iff] at h410
                  rw [h410.1.2] at hresp'
                  simp at hresp'
              · cases hr
          · next h4b =>
            obtain ⟨qu_r, hqur, hqci, hqty, hqcl⟩ :=
              hrm (probePassable_false_of_not4b h4d h4b)
            have hqmem : qu_r ∈ resp.question.toList := by
              have := Array.mem_of_getElem? hqur
              simpa using this
            split at hr
            ·

              next hansT =>
              simp only [] at hr
              cases hr
              rw [finalizeAnswer_tc] at htc
              have hsz : 0 < resp.answer.size := by
                refine size_pos_of_not_isEmpty ?_
                intro hcontra
                exact absurd (hasRRTypeIn_of_entitled hqur hansT)
                  (hasRRTypeIn_empty hcontra)
              by_cases hne : resp.header.rcode = Rcode.nameError
              ·
                have hmiss := hcons.nameErrorDeserved hne qu_r hqmem
                have hverd : treeLookup T s.resources.sname qu₀.qtype
                    = .nameError := by
                  rw [← treeLookup_congr hqci, ← hqty]
                  exact (treeLookup_nameError_iff ..).mpr hmiss
                exact answersFromTree_of_terminal hs.reach hverd
                  (fun _ _ h => by cases h) hagrees
                  (by rw [finalizeAnswer_rcode]; exact hne)
              ·
                have hrc0 : resp.header.rcode = Rcode.noError := by
                  rcases hcons.rcodeFaithful hsz with h | h
                  · exact h
                  · exact absurd h hne
                have hht : HasType resp.answer qu_r.qtype :=
                  hasType_iff_hasRRTypeIn.mp (hasRRTypeIn_of_entitled hqur hansT)
                obtain ⟨k, chT, rrsT, hres, hdel⟩ :=
                  hcons.answersFaithful qu_r hqmem htc hrc0 hht
                rw [hqty] at hres
                have hres' := treeResolve_congr hqci hres
                refine answersFromTree_of_answer hs.reach hres' hagrees
                  (by rw [finalizeAnswer_rcode]; exact hrc0) ?_
                intro trr htrr
                obtain ⟨b, hb, rr', hp', hdata'⟩ := hdel trr htrr
                exact ⟨b, finalizeAnswer_answer_mem hb, rr', hp', hdata'⟩
            · next hansOuter =>
              -- entitled = false.  The `.answer` arms are now only: NXDOMAIN,
              -- SOA-nodata (vacuous in ¬B), and truncation.  A NON-EMPTY FOREIGN
              -- answer no longer lands here — it retries (goto), handled in the
              -- goto branch.
              split at hr
              ·
                next h4a =>
                -- NXDOMAIN: the nameError verdict is deserved.  The guard is now
                -- `rcode == nameError && answer.isEmpty` (a genuine, answer-free
                -- NXDOMAIN); extract the rcode conjunct.
                cases hr
                rw [finalizeAnswer_tc] at htc
                have hne : resp.header.rcode = Rcode.nameError :=
                  rcode_beq_eq (Bool.and_eq_true _ _ |>.mp h4a).1
                have hmiss := hcons.nameErrorDeserved hne qu_r hqmem
                have hverd : treeLookup T s.resources.sname qu₀.qtype
                    = .nameError := by
                  rw [← treeLookup_congr hqci, ← hqty]
                  exact (treeLookup_nameError_iff ..).mpr hmiss
                exact answersFromTree_of_terminal hs.reach hverd
                  (fun _ _ h => by cases h) hagrees
                  (by rw [finalizeAnswer_rcode]; exact hne)
              · next h4a =>
                split at hr
                ·
                  next h420 =>
                  -- E (outer): noError && empty && SOA-in-authority.  In ¬B the
                  -- authority is empty, but the SOA gate needs a record there —
                  -- so this branch is vacuous.
                  exfalso
                  cases hr
                  simp only [Bool.and_eq_true] at h420
                  have hrc0 : resp.header.rcode = Rcode.noError :=
                    rcode_beq_eq h420.1.1
                  have hempty : resp.answer.isEmpty = true := h420.1.2
                  have hansF : answersQueryB (RR := ResourceRecord) resp
                      = false := by
                    rw [answersQueryB_eq hqur]
                    cases hcase : hasRRTypeIn (RR := ResourceRecord)
                        resp.answer qu_r.qtype
                    · rfl
                    · exact absurd hcase (hasRRTypeIn_empty hempty)
                  have hneB : (resp.header.rcode == Rcode.nameError)
                      = false := by
                    cases hcase : resp.header.rcode == Rcode.nameError
                    · rfl
                    · rw [rcode_beq_eq hcase] at hrc0
                      cases hrc0
                  have hauthEmpty : resp.authority.isEmpty = true := by
                    cases hcase : resp.authority.isEmpty
                    · exact absurd (by rw [hansF, hneB, hempty, hcase]; rfl) h4b
                    · rfl
                  -- SOA gate holds (h420.2) but authority is empty: contradiction.
                  have hsoa := h420.2
                  unfold VeriDNS.Impl.Resolver.hasSoaAuthorityFor at hsoa
                  rw [Array.isEmpty_iff] at hauthEmpty
                  rw [hauthEmpty] at hsoa
                  simp at hsoa
                · split at hr
                  ·
                    next hTC =>
                    cases hr
                    rw [finalizeAnswer_tc] at htc
                    rw [htc] at hTC
                    simp at hTC
                  · cases hr
  · intro st s' hgo
    have hag := (hsound.2 st s' hgo).1
    unfold stepAnalyzeResponse at hgo
    split at hgo
    · cases hgo
    · next resp heq =>
      have hcons := hresp resp heq
      have hrm := hs.respMatch resp heq
      split at hgo
      ·
        next canonicalName hchaseEq =>
        simp only [] at hgo
        split at hgo
        · cases hgo
        split at hgo
        · cases hgo
        cases hgo
        obtain ⟨qu_r, hqur, hqci, hqty, hqcl⟩ :=
          hrm (probePassable_false_of_chase hchaseEq)
        have hqmem : qu_r ∈ resp.question.toList := by
          have := Array.mem_of_getElem? hqur
          simpa using this

        have hansF : answersQueryB (RR := ResourceRecord) resp = false := by
          cases hcase : answersQueryB (RR := ResourceRecord) resp
          · rfl
          · unfold cnameToChase at hchaseEq
            rw [if_pos hcase] at hchaseEq
            cases hchaseEq
        have hansT : ¬ (answersQueryB (RR := ResourceRecord) resp = true) := by
          rw [hansF]
          simp
        have hext : extractCname (RR := ResourceRecord) qu_r.qname resp.answer
            = some canonicalName := by
          unfold cnameToChase at hchaseEq
          rw [if_neg hansT] at hchaseEq
          simp only [hqur] at hchaseEq
          exact hchaseEq
        obtain ⟨b, hb, rrC, hpC, htyC, hrdC⟩ := extractCname_some hext
        have hnqt : ¬ HasType resp.answer qu_r.qtype := by
          intro hht
          rw [answersQueryB_eq hqur, hasType_iff_hasRRTypeIn.mpr hht]
            at hansF
          cases hansF
        have hpath := hcons.redirectsOnPath qu_r hqmem hnqt b hb rrC hpC htyC
        rw [hqty] at hpath
        have hreachC : Reaches T qu₀.qtype s.resources.sname canonicalName := by
          rw [← hrdC]
          exact reaches_congr_left (nameEqCI_symm hqci) hpath
        refine ⟨⟨hag.cache, hag.chain⟩, ?_, ?_, ?_, hs.query, hs.question,
          reaches_trans hs.reach hreachC, ?_, fun _ => rfl,
          fun r hrr => by cases hrr⟩
        · exact lookupComplete_cacheUnlessTruncated hsane hs.agrees.cache
            hs.complete resp
            (fun b hb => hcons.answer b (cnameRaws_subset _ _ hb))
            (fun h0 => sectionWhole_cnameOwner hsane _ (hcons.answerWhole h0))
            (fun h0 => ttlUniform_cnameOwner _ (hcons.answerTtlUniform h0)) _ s.now
        · exact oneExpiry_cacheUnlessTruncated hs.oneExp _ _ _ _
        · exact negativesFaithful_cacheUnlessTruncated hs.negs resp _ _ s.now
        ·
          intro b' hb' rr hp hty
          have hF : ¬ hasRRTypeIn (RR := ResourceRecord)
              resp.answer qu_r.qtype = true := by
            rw [← answersQueryB_eq hqur, hansF]
            simp
          cases hext : extractCnameRR (RR := ResourceRecord) qu_r.qname resp.answer with
          | none =>
            simp only [prependCnameLink, hqur, hext] at hb'
            exact hs.chainFree b' hb' rr hp hty
          | some cnBytes =>
            simp only [prependCnameLink, hqur, hext, Array.toList_push, List.mem_append,
              List.mem_singleton] at hb'
            rcases hb' with hl | hr'
            · exact hs.chainFree b' hl rr hp hty
            · subst b'
              exact not_type_of_hasRRTypeIn_false hF cnBytes
                (Array.mem_def.mp (Array.mem_of_find?_eq_some hext)) rr hp (by rw [hty, hqty])
      · next hchaseEq =>
        split at hgo
        ·
          cases hgo
          exact ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs,
            hs.query, hs.question, hs.reach, hs.chainFree, fun _ => rfl,
            fun r hrr => by cases hrr⟩
        · split at hgo
          · split at hgo
            ·
              cases hgo
              refine ⟨⟨hag.cache, hag.chain⟩, ?_, ?_, ?_, hs.query, hs.question,
                hs.reach, hs.chainFree, fun _ => rfl,
                fun r hrr => by cases hrr⟩
              · exact lookupComplete_cacheUnlessTruncated hsane
                  (cacheAgrees_cacheUnlessTruncated hs.agrees.cache resp
                    (fun b hb => hcons.authority b (bailiwickRaws_subset _ _ hb)) _ s.now)
                  (lookupComplete_cacheUnlessTruncated hsane hs.agrees.cache
                    hs.complete resp
                    (fun b hb => hcons.authority b (bailiwickRaws_subset _ _ hb))
                    (fun h0 => sectionWhole_bailiwick hsane _ (hcons.authorityWhole h0))
                    (fun h0 => ttlUniform_bailiwick _ (hcons.authorityTtlUniform h0)) _ s.now)
                  resp
                  (fun b hb => hcons.additional b (bailiwickRaws_subset _ _ hb))
                  (fun h0 => sectionWhole_bailiwick hsane _ (hcons.additionalWhole h0))
                  (fun h0 => ttlUniform_bailiwick _ (hcons.additionalTtlUniform h0)) _ s.now
              · exact oneExpiry_cacheUnlessTruncated
                  (oneExpiry_cacheUnlessTruncated hs.oneExp _ _ _ _) _ _ _ _
              · exact negativesFaithful_cacheUnlessTruncated
                  (negativesFaithful_cacheUnlessTruncated hs.negs resp _ _ s.now)
                  resp _ _ s.now
            · split at hgo
              · cases hgo
              ·
                cases hgo
                exact ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs,
                  hs.query, hs.question, hs.reach, hs.chainFree, fun _ => rfl,
                  fun r hrr => by cases hrr⟩
          · split at hgo
            ·
              simp only [] at hgo; cases hgo
            · split at hgo
              · cases hgo
              · split at hgo
                · cases hgo
                · split at hgo
                  · cases hgo
                  · -- else (outer): bizarre / foreign response ⇒ retry.  RFC 1034
                    -- §4.3.2.d + off-owner: cache/chain unchanged, StateOK preserved.
                    cases hgo
                    exact ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp,
                      hs.negs, hs.query, hs.question, hs.reach, hs.chainFree,
                      fun _ => rfl, fun r hrr => by cases hrr⟩

theorem step_complete {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : Question} {s : State S DnsCache NS ResourceRecord}
    (hsane : TreeSane T) (hs : StateOK T q₀ qu₀ s)
    (hresp : ∀ r, s.lastResponse = some r → ResponseConsistent T r) :
    (∀ r rst, step s = .answer r rst → r.header.tc = 0 →
      ∀ fuel, AnswersFromTree T qu₀.qname qu₀.qtype fuel r) ∧
    (∀ st s', step s = .goto st s' →
      StateOK T q₀ qu₀ { s' with currentStep := st } ∧
      (∀ r, s'.lastResponse = some r → ResponseConsistent T r)) ∧
    (∀ s', step s = .needsIO s' → StateOK T q₀ qu₀ s' ∧
      s'.currentStep = .sendQueries ∧ s'.lastResponse = none) := by
  cases hcur : s.currentStep with
  | checkAnswer =>
    obtain ⟨ha, hg⟩ := stepCheckLocal_complete hsane hs hcur
    refine ⟨?_, ?_, ?_⟩
    · intro r rst h htc
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      exact ha r rst h
    · intro st s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      refine ⟨hg st s' h, ?_⟩
      have hpres := (stepCheckLocal_sound (S := S) (NS := NS) (s := s)
        hs.agrees).2 st s' h
      intro r hr
      rw [hpres.2, hs.respNone (Or.inl hcur)] at hr
      cases hr
    · intro s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepCheckLocal at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> first | cases h | (split at h <;> cases h)
  | findServers =>
    have hrespN : s.lastResponse = none := hs.respNone (Or.inr hcur)
    refine ⟨?_, ?_, ?_⟩
    · intro r rst h htc
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> (try split at h) <;> cases h
      · split at h <;> cases h
    · intro st s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> (try split at h) <;> cases h <;>
          exact ⟨⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs,
            hs.query, hs.question, hs.reach, hs.chainFree,
            fun _ => hrespN,
            fun r hr => by
              have hr' : s.lastResponse = some r := hr
              rw [hrespN] at hr'
              cases hr'⟩,
            fun r hr => by
              have hr' : s.lastResponse = some r := hr
              rw [hrespN] at hr'
              cases hr'⟩
      · split at h <;> cases h <;>
          exact ⟨⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs,
            hs.query, hs.question, hs.reach, hs.chainFree,
            fun _ => hrespN,
            fun r hr => by
              have hr' : s.lastResponse = some r := hr
              rw [hrespN] at hr'
              cases hr'⟩,
            fun r hr => by
              have hr' : s.lastResponse = some r := hr
              rw [hrespN] at hr'
              cases hr'⟩
    · intro s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> (try split at h) <;> cases h
      · split at h <;> cases h
  | sendQueries =>
    refine ⟨?_, ?_, ?_⟩
    · intro r rst h htc
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepSendQueries at h
      split at h <;> cases h
    · intro st s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepSendQueries at h
      split at h
      · cases h
        refine ⟨⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs,
          hs.query, hs.question, hs.reach, hs.chainFree, ?_,
          hs.respMatch⟩, hresp⟩
        rintro (h | h) <;> cases h
      · cases h
    · intro s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepSendQueries at h
      split at h
      · cases h
      · next hnone =>
        cases h
        exact ⟨hs, hcur, hnone⟩
  | analyzeResponse =>
    obtain ⟨ha, hg⟩ := stepAnalyzeResponse_complete hsane hs hresp
    refine ⟨?_, ?_, ?_⟩
    · intro r rst h htc
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      exact ha r rst h htc
    · intro st s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      refine ⟨hg st s' h, ?_⟩
      have hnone := (stepAnalyzeResponse_sound (S := S) (NS := NS) (s := s)
        hs.agrees hresp).2 st s' h
      intro r hr
      have hr' : s'.lastResponse = some r := hr
      rw [hnone.2] at hr'
      cases hr'
    · intro s' h
      unfold step at h
      rw [hcur] at h
      dsimp only [] at h
      unfold stepAnalyzeResponse at h
      split at h
      · cases h
      · split at h
        · simp only [] at h; split at h <;> (try split at h) <;> cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · split at h <;> cases h
            · split at h
              ·
                simp only [] at h; cases h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · split at h <;> (try split at h) <;> cases h

theorem resolveLoop_complete {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : Question} (hsane : TreeSane T) :
    ∀ (fuel : Nat) (s : State S DnsCache NS ResourceRecord),
    StateOK T q₀ qu₀ s →
    (∀ r, s.lastResponse = some r → ResponseConsistent T r) →
    (match resolve.loop (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) s fuel with
     | .ok (.done resp stF) =>
         (resp.header.tc = 0 →
           ∀ k, AnswersFromTree T qu₀.qname qu₀.qtype k resp) ∧
         CacheAgrees T stF.resources.cache ∧
         LookupComplete T stF.resources.cache ∧
         OneExpiryPerKey stF.resources.cache ∧
         NegativesFaithful T stF.resources.cache
     | .ok (.paused s') => StateOK T q₀ qu₀ s' ∧
         s'.currentStep = .sendQueries ∧ s'.lastResponse = none
     | .error _ => True)
  | 0, _, _, _ => trivial
  | fuel + 1, s, hs, hresp => by
    unfold resolve.loop
    obtain ⟨ha, hg, hio⟩ := step_complete hsane hs hresp
    split
    · next resp stF heq =>
      split at heq
      · next r rst hstep =>
        cases heq
        obtain ⟨hcA, hcL, hcO, hcN⟩ := step_answer_cacheOK hsane hs hresp hstep
        exact ⟨ha _ _ hstep, hcA, hcL, hcO, hcN⟩
      · next st s' hstep =>
        obtain ⟨hs', hresp'⟩ := hg st s' hstep
        have ih := resolveLoop_complete hsane fuel
          { s' with currentStep := st } hs' hresp'
        rw [heq] at ih
        exact ih
      · next s' hstep => exact absurd heq (by simp)
      · next msg hstep => cases heq
    · next s' heq =>
      split at heq
      · next r rst hstep => exact absurd heq (by simp)
      · next st s'' hstep =>
        obtain ⟨hs'', hresp''⟩ := hg st s'' hstep
        have ih := resolveLoop_complete hsane fuel
          { s'' with currentStep := st } hs'' hresp''
        rw [heq] at ih
        exact ih
      · next s'' hstep =>
        cases heq
        exact hio s' hstep
      · next msg hstep => cases heq
    · trivial

theorem resume_complete {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : Question} {s : State S DnsCache NS ResourceRecord}
    (hsane : TreeSane T) (hs : StateOK T q₀ qu₀ s)
    (hcur : s.currentStep = .sendQueries)
    {resp : Format} (hcons : ResponseConsistent T resp)
    (hmatch : VeriDNS.Impl.Server.probePassableB resp = false →
      ∃ qu, resp.question[0]? = some qu ∧
      nameEqCI qu.qname s.resources.sname = true ∧
      qu.qtype = qu₀.qtype ∧ qu.qclass = qu₀.qclass)
    (fuel : Nat) :
    (match resume (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) s resp fuel with
     | .ok (.done r stF) =>
         (r.header.tc = 0 →
           ∀ k, AnswersFromTree T qu₀.qname qu₀.qtype k r) ∧
         CacheAgrees T stF.resources.cache ∧
         LookupComplete T stF.resources.cache ∧
         OneExpiryPerKey stF.resources.cache ∧
         NegativesFaithful T stF.resources.cache
     | .ok (.paused s') => StateOK T q₀ qu₀ s' ∧
         s'.currentStep = .sendQueries ∧ s'.lastResponse = none
     | .error _ => True) := by
  unfold resume
  refine resolveLoop_complete hsane fuel _
    ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs, hs.query,
      hs.question, hs.reach, hs.chainFree, ?_, ?_⟩
    (fun r hr => by cases hr; exact hcons)
  · intro hor
    rcases hor with h | h <;>
      (have h' : s.currentStep = _ := h
       rw [hcur] at h'
       cases h')
  · intro r hr
    have hr' : some resp = some r := hr
    cases hr'
    exact hmatch

theorem resolve_complete {T : Node ResourceRecord} (hsane : TreeSane T)
    (query : Format) {qu₀ : Question} (hq : query.question[0]? = some qu₀)
    (sbelt : S) (fuel : Nat) (now : UInt32) {initCache : DnsCache}
    (hc : CacheAgrees T initCache) (hlc : LookupComplete T initCache)
    (hone : OneExpiryPerKey initCache)
    (hneg : NegativesFaithful T initCache) :
    (match resolve (S := S) (C := DnsCache) (NS := NS) (RR := ResourceRecord)
        query sbelt fuel now initCache with
     | .ok (.done resp stF) =>
         (resp.header.tc = 0 →
           ∀ k, AnswersFromTree T qu₀.qname qu₀.qtype k resp) ∧
         CacheAgrees T stF.resources.cache ∧
         LookupComplete T stF.resources.cache ∧
         OneExpiryPerKey stF.resources.cache ∧
         NegativesFaithful T stF.resources.cache
     | .ok (.paused s') => StateOK T query qu₀ s' ∧
         s'.currentStep = .sendQueries ∧ s'.lastResponse = none
     | .error _ => True) := by
  unfold resolve
  refine resolveLoop_complete hsane fuel _
    ⟨⟨hc, ?_⟩, hlc, hone, hneg, rfl, hq, ?_, ?_, fun _ => rfl, ?_⟩ ?_
  · intro b hb
    simp [initFromQuery] at hb
  · show Reaches T qu₀.qtype qu₀.qname
      (initFromQuery (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) query sbelt now initCache).resources.sname
    unfold initFromQuery
    dsimp only []
    rw [hq]
    exact .refl (nameEqCI_refl _)
  · intro b hb rr hp
    simp [initFromQuery] at hb
  · intro r hr
    cases hr
  · intro r hr
    cases hr

end StepCompleteness

section ShimCompleteness

open VeriDNS.Impl.Server VeriDNS.Impl.Resolver VeriDNS.Impl.SList
open VeriDNS.Impl.Cache (DnsCache)

private theorem satisfiesM_true' {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (x : m α) : SatisfiesM (fun _ => True) x :=
  ⟨(fun a => ⟨a, trivial⟩) <$> x, by simp [Functor.map_map]⟩

variable {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
  [UdpSocket M Sock ByteArray]

def ShimComplete (T : Node ResourceRecord) (qu₀ : Question)
    (rc : Except String Format × DnsCache) : Prop :=
  (∀ f, rc.1 = .ok f → f.header.tc = 0 →
    ∀ k, AnswersFromTree T qu₀.qname qu₀.qtype k f) ∧
  CacheAgrees T rc.2 ∧ LookupComplete T rc.2 ∧ OneExpiryPerKey rc.2 ∧
    NegativesFaithful T rc.2

private theorem stateOK_slist {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : VeriDNS.Spec.Question}
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    (hs : StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀ state)
    (sl : DnsSList) :
    StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀
      { state with resources := { state.resources with slist := sl } } :=
  ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs, hs.query,
    hs.question, hs.reach, hs.chainFree, hs.respNone, hs.respMatch⟩

private theorem stateOK_slistNoEdns {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : VeriDNS.Spec.Question}
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    (hs : StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀ state)
    (sl : DnsSList) :
    StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀
      { state with
        resources := { state.resources with slist := sl },
        noEdns := true } :=
  ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs, hs.query,
    hs.question, hs.reach, hs.chainFree, hs.respNone, hs.respMatch⟩

private theorem stateOK_glueless {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : VeriDNS.Spec.Question}
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    (hs : StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀ state)
    (hnone : state.lastResponse = none)
    (sl : DnsSList) {c : DnsCache} (hc : c = state.resources.cache) :
    StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀
      { state with resources :=
        { state.resources with slist := sl, cache := c } } := by
  subst hc
  exact ⟨⟨hs.agrees.cache, hs.agrees.chain⟩, hs.complete, hs.oneExp, hs.negs, hs.query,
    hs.question, hs.reach, hs.chainFree, fun _ => hnone,
    fun r hr => by
      have hr' : state.lastResponse = some r := hr
      rw [hnone] at hr'
      cases hr'⟩

private theorem stateOK_gluelessCache {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : VeriDNS.Spec.Question}
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    (hs : StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀ state)
    (hnone : state.lastResponse = none)
    (sl : DnsSList) {c : DnsCache} (hca : CacheAgrees T c)
    (hlc : LookupComplete T c) (hone : OneExpiryPerKey c)
    (hneg : NegativesFaithful T c) :
    StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀
      { state with resources :=
        { state.resources with slist := sl, cache := c } } :=
  ⟨⟨hca, hs.agrees.chain⟩, hlc, hone, hneg, hs.query, hs.question, hs.reach,
    hs.chainFree, fun _ => hnone,
    fun r hr => by
      have hr' : state.lastResponse = some r := hr
      rw [hnone] at hr'
      cases hr'⟩

private theorem gluelessRecheck_complete {T : Node ResourceRecord} {q₀ : Format}
    {qu₀ : Question} {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    {subCache : DnsCache} (hsane : TreeSane T)
    (hs : StateOK (S := DnsSList) (NS := SlistEntry) T q₀ qu₀ state)
    (hca : CacheAgrees T subCache) (hlc : LookupComplete T subCache)
    (hone : OneExpiryPerKey subCache) (hneg : NegativesFaithful T subCache) :
    ∀ hit, gluelessRecheck state subCache = some hit →
      ∀ k, AnswersFromTree T qu₀.qname qu₀.qtype k hit := by
  intro hit hr
  have hagrees : SectionAgrees T hit.answer :=
    gluelessRecheck_sound hs.agrees.chain hca hit hr
  unfold gluelessRecheck at hr
  rw [hs.query] at hr
  dsimp only [] at hr
  rw [hs.question] at hr
  dsimp only [] at hr
  have hla := localAnswer_complete hsane hca hlc hone hneg
    qu₀.qtype qu₀.qclass state.now 1 state.resources.sname state.cnameChain
    (cnameChaseVisited (RR := ResourceRecord) qu₀.qname state.cnameChain)
  split at hr
  · next rc hret =>
    cases hr
    have heqL : localAnswer (C := DnsCache) (RR := ResourceRecord)
        subCache qu₀.qtype qu₀.qclass state.now 1 state.resources.sname
        state.cnameChain
        (cnameChaseVisited (RR := ResourceRecord) qu₀.qname state.cnameChain)
        = .negative rc (NegativeAuthoritySpec.authoritySection
            (RR := ResourceRecord) subCache state.resources.sname
            qu₀.qtype qu₀.qclass state.now) state.cnameChain := by
      unfold localAnswer
      rw [hret]
    rw [heqL] at hla
    obtain ⟨⟨s', hreach', hverd⟩, hchainprov⟩ := hla
    rcases hverd with ⟨hrc, hlook⟩ | ⟨hrc, hlook⟩
    · exact answersFromTree_of_terminal
        (reaches_trans hs.reach hreach') hlook
        (fun _ _ h => by cases h) hagrees
        (by rw [finalizeAnswer_rcode, negativeResponse_rcode, hrc])
    · refine answersFromTree_of_terminal
        (reaches_trans hs.reach hreach') hlook
        (fun _ _ h => by cases h) hagrees
        ⟨by rw [finalizeAnswer_rcode, negativeResponse_rcode, hrc], ?_⟩
      rintro ⟨b, hb, rr, hp, hty⟩
      rcases finalizeAnswer_answer_sub b hb with hchainb | hrb
      · rcases hchainprov b hchainb with hold | ⟨hqne, rr', hp', hty'⟩
        · exact hs.chainFree b hold rr hp (bv16_beq_iff.mp hty)
        · rw [hp] at hp'
          cases hp'
          exact hqne ((bv16_beq_iff.mp hty) ▸ hty')
      · rw [negativeResponse_answer] at hrb
        simp at hrb
  · next hret =>
    split at hr
    · cases hr
    · next hne =>
      cases hr
      have heqL : localAnswer (C := DnsCache) (RR := ResourceRecord)
          subCache qu₀.qtype qu₀.qclass state.now 1 state.resources.sname
          state.cnameChain
          (cnameChaseVisited (RR := ResourceRecord) qu₀.qname state.cnameChain)
          = .answerHit state.resources.sname state.cnameChain
            (TrustworthinessSpec.answers (C := DnsCache) subCache
              state.resources.sname qu₀.qtype qu₀.qclass state.now) := by
        unfold localAnswer
        rw [hret]
        dsimp only []
        rw [if_neg hne]
      rw [heqL] at hla
      obtain ⟨hreach', ⟨matching, hlook, hdeliver⟩, hwfs, _⟩ := hla
      refine answersFromTree_of_terminal
        (reaches_trans hs.reach hreach') hlook
        (fun _ _ h => by cases h) hagrees
        ⟨by rw [finalizeAnswer_rcode, cacheResponse_rcode], ?_⟩
      intro trr htrr
      obtain ⟨rr', hrr', hdata'⟩ := hdeliver trr htrr
      refine ⟨RRParse.rrBytes (RR := ResourceRecord) rr',
        finalizeAnswer_answer_mem ?_, rr',
        parseRaw_rrBytes_of_wf (hwfs rr' hrr').2, hdata'⟩
      show RRParse.rrBytes (RR := ResourceRecord) rr'
        ∈ ((TrustworthinessSpec.answers (C := DnsCache) subCache
            state.resources.sname qu₀.qtype qu₀.qclass
            state.now).map (RRParse.rrBytes (RR := ResourceRecord))).toList
      exact Array.mem_def.mp (Array.mem_map.mpr ⟨rr', hrr', rfl⟩)

private theorem acceptResponse_facts {sent resp₀ resp : Format}
    (h : acceptResponse sent resp₀ = some resp) :
    resp₀ = resp ∧ questionMatches resp.question sent.question = true := by
  unfold acceptResponse at h
  split at h
  · next hcond =>
    cases h
    simp only [Bool.and_eq_true] at hcond
    exact ⟨rfl, hcond.1.1.2⟩
  · cases h

private theorem questionMatches_facts {a b : Array VeriDNS.Spec.Question}
    (h : questionMatches a b = true) :
    ∃ qa qb, a[0]? = some qa ∧ b[0]? = some qb ∧
      nameEqCI qa.qname qb.qname = true ∧ qa.qtype = qb.qtype ∧
      qa.qclass = qb.qclass := by
  unfold questionMatches at h
  split at h
  · next qa qb ha hb =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨qa, qb, ha, hb, nameEqCI_of_beq h.1.1, bv16_beq_iff.mp h.1.2,
      bv16_beq_iff.mp h.2⟩
  · cases h

private theorem buildSubQuery_question
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    {q₀ : Format} {qu₀ : VeriDNS.Spec.Question}
    (hq : state.lastQuery = some q₀)
    (hqu : q₀.question[0]? = some qu₀) {sub : Format} {revealed : Nat}
    (hfull : probeRoundB state.resources.sname revealed = false)
    (hsub : buildSubQuery state revealed = some sub) :
    sub.question[0]? = some
      { qname := state.resources.sname, qtype := qu₀.qtype,
        qclass := qu₀.qclass } := by
  unfold buildSubQuery at hsub
  rw [hq] at hsub
  dsimp only [] at hsub
  rw [hqu] at hsub
  dsimp only [] at hsub
  cases hsub
  show #[subQuestion state.resources.sname revealed qu₀][0]? = _
  unfold subQuestion
  rw [hfull]
  rfl

private theorem buildSubQuery_question_probe
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    {q₀ : Format} {qu₀ : VeriDNS.Spec.Question}
    (hq : state.lastQuery = some q₀)
    (hqu : q₀.question[0]? = some qu₀) {sub : Format} {revealed : Nat}
    (hprobe : probeRoundB state.resources.sname revealed = true)
    (hsub : buildSubQuery state revealed = some sub) :
    sub.question[0]? = some
      { qname := VeriDNS.Impl.DomainName.minimisedName state.resources.sname revealed,
        qtype := BitVec.ofNat 16 1, qclass := qu₀.qclass } := by
  unfold buildSubQuery at hsub
  rw [hq] at hsub
  dsimp only [] at hsub
  rw [hqu] at hsub
  dsimp only [] at hsub
  cases hsub
  show #[subQuestion state.resources.sname revealed qu₀][0]? = _
  unfold subQuestion
  rw [hprobe]
  rfl

private theorem nodeAt_prefix_none :
    ∀ (l₁ l₂ : List ByteArray) (root : Node ResourceRecord),
      nodeAt root l₁ = none → nodeAt root (l₁ ++ l₂) = none
  | [], _, _, h => by simp [nodeAt] at h
  | l :: rest, l₂, root, h => by
    rw [List.cons_append]
    unfold nodeAt at h ⊢
    cases hf : findChild root l with
    | none => rfl
    | some ch =>
      rw [hf] at h
      exact nodeAt_prefix_none rest l₂ ch h

private theorem validLabels_extract' (ls : Array ByteArray)
    (hv : VeriDNS.Proof.DomainName.ValidLabels ls) (i j : Nat) :
    VeriDNS.Proof.DomainName.ValidLabels (ls.extract i j) := by
  intro k hk
  simp only [Array.getElem_extract]
  have hsz : (ls.extract i j).size = min j ls.size - i := Array.size_extract
  exact hv (i + k) (by omega)

private theorem extract_suffix_toList' (ls : Array ByteArray) (i : Nat) :
    (ls.extract i ls.size).toList = ls.toList.drop i := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  exact List.take_of_length_le (by simp)

private theorem nodeAtName_none_of_minimisedName_none {T : Node ResourceRecord}
    {m : ByteArray} {keep : Nat}
    (hn : nodeAtName T (VeriDNS.Impl.DomainName.minimisedName m keep) = none) :
    nodeAtName T m = none := by
  unfold VeriDNS.Impl.DomainName.minimisedName at hn
  cases hw : VeriDNS.Impl.DomainName.wireFormatToLabels m with
  | error e =>
    rw [hw] at hn
    exact hn
  | ok ls =>
    rw [hw] at hn
    dsimp only [] at hn
    by_cases hk : keep < ls.size
    · rw [if_pos hk] at hn
      have hv : VeriDNS.Proof.DomainName.ValidLabels ls := fun i hi =>
        VeriDNS.Proof.DomainName.wireFormatToLabels_valid hw ls[i]
          (Array.mem_def.mp (ls.getElem_mem hi))
      have hvx := validLabels_extract' ls hv (ls.size - keep) ls.size
      unfold nodeAtName at hn ⊢
      rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip _ hvx] at hn
      dsimp only [] at hn
      rw [hw]
      dsimp only []
      have hsplit : ls.toList.reverse
          = (ls.extract (ls.size - keep) ls.size).toList.reverse
            ++ (ls.toList.take (ls.size - keep)).reverse := by
        rw [extract_suffix_toList', ← List.reverse_append, List.take_append_drop]
      rw [hsplit]
      exact nodeAt_prefix_none _ _ _ hn
    · rw [if_neg hk] at hn
      exact hn

private theorem lookupComplete_storeProbeNegative {T : Node ResourceRecord}
    {c : DnsCache} (h : LookupComplete T c) {sub resp : Format} {now : UInt32} :
    LookupComplete T (storeProbeNegative c sub resp now) := by
  unfold storeProbeNegative
  split
  · split
    · exact h
    · exact h
  · exact h

private theorem oneExpiry_storeProbeNegative {c : DnsCache}
    (h : OneExpiryPerKey c) {sub resp : Format} {now : UInt32} :
    OneExpiryPerKey (storeProbeNegative c sub resp now) := by
  unfold storeProbeNegative
  split
  · split
    · exact h
    · exact h
  · exact h

private theorem negativesFaithful_storeProbeNegative {T : Node ResourceRecord}
    {c : DnsCache} (h : NegativesFaithful T c) {sub resp : Format} {now : UInt32}
    (habsent : ∀ qu, sub.question[0]? = some qu → nodeAtName T qu.qname = none)
    (hrc : resp.header.rcode = Rcode.nameError) :
    NegativesFaithful T (storeProbeNegative c sub resp now) := by
  unfold storeProbeNegative
  split
  · next qu hq =>
    split
    · intro ne hne
      simp only [DnsCache.storeNegative] at hne
      rcases Array.mem_push.mp hne with hmem | heq
      · exact h ne (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hmem)).1
      · subst heq
        exact ⟨fun _ => habsent qu hq,
          fun hno => absurd (hrc.symm.trans hno) (by intro hcon; cases hcon),
          Or.inl hrc⟩
    · exact h
  · exact h

private theorem afterResume_complete (T : Node ResourceRecord) (hsane : TreeSane T)
    {q₀ : Format} {qu₀ : VeriDNS.Spec.Question}
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    (entryName : ByteArray) (hs : StateOK T q₀ qu₀ state)
    (hcur : state.currentStep = .sendQueries) {resp : Format}
    (hcons : ResponseConsistent T resp)
    (hmatch : VeriDNS.Impl.Server.probePassableB resp = false →
      ∃ qu, resp.question[0]? = some qu ∧
      nameEqCI qu.qname state.resources.sname = true ∧
      qu.qtype = qu₀.qtype ∧ qu.qclass = qu₀.qclass) :
    (match afterResume state entryName resp with
     | .finished result cout =>
         (∀ f, result = .ok f → f.header.tc = 0 →
           ∀ k, AnswersFromTree T qu₀.qname qu₀.qtype k f) ∧
         CacheAgrees T cout ∧ LookupComplete T cout ∧
         OneExpiryPerKey cout ∧ NegativesFaithful T cout
     | .continue st => StateOK T q₀ qu₀ st ∧
         st.currentStep = .sendQueries ∧ st.lastResponse = none) := by
  have hr := resume_complete (S := DnsSList) (NS := SlistEntry) (T := T) hsane
    (s := dropIfBizarre state entryName resp)
    (by unfold dropIfBizarre; split <;> exact stateOK_slist hs _)
    (by unfold dropIfBizarre; split <;> exact hcur) hcons
    (by unfold dropIfBizarre; split <;> exact hmatch) 64
  unfold afterResume
  split at hr <;> rename_i h <;> rw [h]
  · exact ⟨(fun f hf => by cases hf; exact hr.1),
      cacheAgrees_boundLru _ _ hr.2.1,
      lookupComplete_boundLru _ _ hsane hr.2.1 hr.2.2.1,
      oneExpiry_boundLru _ _ hr.2.2.2.1, negativesFaithful_boundLru _ _ hr.2.2.2.2⟩
  · obtain ⟨hok', hcur', hnone'⟩ := hr
    exact ⟨⟨⟨cacheAgrees_boundLru _ _ hok'.agrees.cache, hok'.agrees.chain⟩,
        lookupComplete_boundLru _ _ hsane hok'.agrees.cache hok'.complete,
        oneExpiry_boundLru _ _ hok'.oneExp,
        negativesFaithful_boundLru _ _ hok'.negs,
        hok'.query, hok'.question, hok'.reach, hok'.chainFree,
        hok'.respNone, hok'.respMatch⟩, hcur', hnone'⟩
  · exact ⟨(fun f hf => nomatch hf), hs.agrees.cache, hs.complete,
      hs.oneExp, hs.negs⟩

theorem ioResumeLoop_complete (T : Node ResourceRecord) (hsane : TreeSane T)
    (hnet : NetworkConsistent T M Sock) (hnetTcp : NetworkConsistentTcp T M Sock) (sbelt : DnsSList)
    (q₀ : Format) (qu₀ : VeriDNS.Spec.Question) :
    ∀ (depth fuel : Nat)
      (state : State DnsSList DnsCache SlistEntry ResourceRecord)
      (deadline : UInt32) (revealed : Nat),
    StateOK T q₀ qu₀ state →
    state.currentStep = .sendQueries →
    state.lastResponse = none →
    SatisfiesM (ShimComplete T qu₀)
      (ioResumeLoop (M := M) (Sock := Sock) sbelt state deadline depth fuel revealed)
  | depth, 0, state, deadline, revealed, hs, hcur, hnone => by
    rw [ioResumeLoop.eq_def]
    exact SatisfiesM.pure (p := ShimComplete T qu₀)
      ⟨(fun _ h => nomatch h), hs.agrees.cache, hs.complete, hs.oneExp, hs.negs⟩
  | depth, fuel' + 1, state, deadline, revealed, hs, hcur, hnone => by
    rw [ioResumeLoop.eq_def]
    dsimp only []
    refine SatisfiesM.bind (satisfiesM_true' _) ?_
    intro t _
    split
    ·
      exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.agrees.cache, hs.complete, hs.oneExp, hs.negs⟩
    · refine SatisfiesM.bind (satisfiesM_true' _) ?_
      intro _ _
      split
      ·
        split
        ·
          next nsName _ =>
          split
          ·

            next depth' =>
            refine SatisfiesM.bind (satisfiesM_true' _) ?_
            intro _ _
            have hrc := resolve_complete (S := DnsSList) (NS := SlistEntry)
              (T := T) hsane (mkAddressQuery nsName) rfl sbelt 64 state.now
              hs.agrees.cache hs.complete hs.oneExp hs.negs
            split <;> rename_i h <;> rw [h] at hrc
            ·
              refine SatisfiesM.bind (satisfiesM_true' _) ?_
              intro _ _
              exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀ depth' fuel' _ _ _
                (stateOK_slist hs _) hcur hnone
            ·
              refine SatisfiesM.bind (satisfiesM_true' _) ?_
              intro _ _
              exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀ depth' fuel' _ _ _
                (stateOK_slist hs _) hcur hnone
            ·

              refine SatisfiesM.bind
                (ioResumeLoop_complete T hsane hnet hnetTcp sbelt (mkAddressQuery nsName)
                  _ depth' fuel' _ deadline _ hrc.1 hrc.2.1 hrc.2.2) ?_
              intro y hy
              refine SatisfiesM.bind (satisfiesM_true' _) ?_
              intro _ _
              split
              ·
                split
                ·
                  split
                  · next hit hre =>
                    exact SatisfiesM.pure
                      ⟨fun f hf _ => by
                          cases hf
                          exact gluelessRecheck_complete hsane hs hy.2.1 hy.2.2.1
                            hy.2.2.2.1 hy.2.2.2.2 hit hre,
                        cacheAgrees_touchKeys _ _ hy.2.1,
                        lookupComplete_touchKeys _ _ hy.2.2.1,
                        oneExpiry_touchKeys _ _ hy.2.2.2.1,
                        negativesFaithful_touchKeys _ _ hy.2.2.2.2⟩
                  · exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀ depth' fuel' _ _ _
                      (stateOK_gluelessCache hs hnone _
                        (cacheAgrees_touchKeys _ _ hy.2.1)
                        (lookupComplete_touchKeys _ _ hy.2.2.1)
                        (oneExpiry_touchKeys _ _ hy.2.2.2.1)
                        (negativesFaithful_touchKeys _ _ hy.2.2.2.2)) hcur hnone
                ·
                  exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀ depth' fuel' _ _ _
                    (stateOK_slist hs _) hcur hnone
              ·
                exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀ depth' fuel' _ _ _
                  (stateOK_slist hs _) hcur hnone
          ·
            exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.agrees.cache, hs.complete, hs.oneExp, hs.negs⟩
        ·
          exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.agrees.cache, hs.complete, hs.oneExp, hs.negs⟩
      ·
        next entry ipAddr _ =>
        split
        ·
          next subQuery₀ hbsq =>
          refine SatisfiesM.bind (satisfiesM_true' _) ?_
          intro _ _
          refine SatisfiesM.bind (satisfiesM_true' _) ?_
          intro rid _
          refine SatisfiesM.bind (satisfiesM_true' _) ?_
          intro cid _
          split
          ·
            refine SatisfiesM.bind (satisfiesM_true' _) ?_
            intro _ _
            rw [pure_bind]
            exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
              depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
          refine SatisfiesM.bind (hnet _ _) ?_
          intro upstreamResp hup
          split
          ·
            next resp₀ =>
            split
            ·
              next resp hacc =>
              have hconsU : ResponseConsistent T resp :=
                hup resp₀ resp rfl hacc
              refine SatisfiesM.bind (satisfiesM_true' _) ?_
              intro _ _
              refine SatisfiesM.bind
                (p := fun ro => ∀ r', ro = some r' →
                  ResponseConsistent T r'
                    ∧ ∃ src, acceptResponse (withSecrets subQuery₀ rid cid) src = some r')
                ?tcguard ?_
              case tcguard =>
                split
                · refine SatisfiesM.bind (satisfiesM_true' _) ?_
                  intro _ _
                  refine SatisfiesM.bind (hnetTcp _ _) ?_
                  intro tcpRo htcp
                  cases tcpRo with
                  | none => exact SatisfiesM.pure (m := M) (fun r' h => nomatch h)
                  | some tcpResp =>
                    dsimp only []
                    split
                    · exact SatisfiesM.pure (m := M) (fun r' h => nomatch h)
                    · next tcpRespA hacctcp =>
                      refine SatisfiesM.pure (m := M) ?_
                      intro r' hr'
                      split at hr'
                      · exact absurd hr' (by simp)
                      · cases hr'
                        exact ⟨htcp tcpResp tcpRespA rfl hacctcp, tcpResp, hacctcp⟩
                · exact SatisfiesM.pure (m := M)
                    (fun r' hr' => by cases hr'; exact ⟨hconsU, resp₀, hacc⟩)
              intro ro hro
              cases ro with
              | none =>
                dsimp only []
                refine SatisfiesM.bind (satisfiesM_true' _) ?_
                intro _ _
                exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                  depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
              | some resp =>
                obtain ⟨hcons, srcResp, hacc⟩ := hro resp rfl
                obtain ⟨_, hqm⟩ := acceptResponse_facts hacc
                obtain ⟨qa, qb, hqa, hqb, hci, hty, hcl⟩ :=
                  questionMatches_facts hqm
                dsimp only []
                split
                ·
                  refine SatisfiesM.bind (satisfiesM_true' _) ?_
                  intro _ _
                  exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                    depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
                ·
                  split
                  · -- 055 (RFC 6891 §6.2.2): FORMERR to an OPT-bearing sub-query — the
                    -- loop retries without EDNS (noEdns flag); plain recursion.
                    refine SatisfiesM.bind (satisfiesM_true' _) ?_
                    intro _ _
                    exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                      depth fuel' _ _ _ (stateOK_slistNoEdns hs _) hcur hnone
                  ·
                    split
                    · -- 051/064: the probe-NXDOMAIN arm now recurses (full-qname
                      -- fallback, RFC 9156 §2.3) instead of delivering.
                      refine SatisfiesM.bind (satisfiesM_true' _) ?_
                      intro _ _
                      exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                        depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
                    ·
                      split
                      ·
                        refine SatisfiesM.bind (satisfiesM_true' _) ?_
                        intro _ _
                        exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                          depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
                      ·
                        next hpg =>
                        have hmatch : probePassableB resp = false →
                            ∃ qu, resp.question[0]? = some qu ∧
                              nameEqCI qu.qname state.resources.sname = true ∧
                              qu.qtype = qu₀.qtype ∧ qu.qclass = qu₀.qclass := by
                          intro hpass
                          cases hpr : probeRoundB state.resources.sname revealed
                          · have hq0 := buildSubQuery_question hs.query hs.question hpr hbsq
                            have hsentq : (withSecrets subQuery₀ rid cid).question[0]?
                                = some { qname := VeriDNS.Impl.DomainName.randomizeCase cid
                                           state.resources.sname,
                                         qtype := qu₀.qtype, qclass := qu₀.qclass } := by
                              show ((withRandomId subQuery₀ rid).question.map _)[0]? = _
                              rw [show (withRandomId subQuery₀ rid).question
                                  = subQuery₀.question from rfl, Array.getElem?_map, hq0]
                              rfl
                            rw [hsentq] at hqb
                            cases hqb
                            exact ⟨qa, hqa,
                              nameEqCI_trans hci
                                (randomizeCase_nameEqCI cid state.resources.sname),
                              hty, hcl⟩
                          · exfalso
                            refine hpg ?_
                            show (probeRoundB state.resources.sname revealed
                                && !probePassableB resp) = true
                            rw [hpr, hpass]
                            rfl
                        have ha := afterResume_complete T hsane (entryName := entry.name)
                          (state := { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } })
                          (stateOK_slist hs _) hcur hcons hmatch
                        split <;> rename_i h <;> rw [h] at ha
                        ·
                          exact SatisfiesM.pure ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
                        ·
                          exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                            depth fuel' _ _ _ ha.1 ha.2.1 ha.2.2
            ·
              refine SatisfiesM.bind (satisfiesM_true' _) ?_
              intro _ _
              exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
                depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
          ·
            exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt q₀ qu₀
              depth fuel' _ _ _ (stateOK_slist hs _) hcur hnone
        ·
          exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.agrees.cache, hs.complete, hs.oneExp, hs.negs⟩
  termination_by depth fuel => (depth, fuel)
  decreasing_by all_goals
    (first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega))

theorem resolveWithIO_complete (T : Node ResourceRecord) (hsane : TreeSane T)
    (hnet : NetworkConsistent T M Sock) (hnetTcp : NetworkConsistentTcp T M Sock) (query : Format)
    {qu₀ : VeriDNS.Spec.Question} (hq : query.question[0]? = some qu₀)
    (sbelt : DnsSList) {cache : DnsCache} (hc : CacheAgrees T cache)
    (hlc : LookupComplete T cache) (hone : OneExpiryPerKey cache)
    (hneg : NegativesFaithful T cache)
    (now : UInt32) (fuel depth : Nat) (budget : UInt32) :
    SatisfiesM (ShimComplete T qu₀)
      (resolveWithIO (M := M) (Sock := Sock) query sbelt cache now
        fuel depth budget) := by
  unfold resolveWithIO
  have h := resolve_complete (S := DnsSList) (NS := SlistEntry) (T := T)
    hsane query hq sbelt 64 now hc hlc hone hneg
  split
  · next resp stF hdone =>
    rw [hdone] at h
    exact SatisfiesM.pure
      ⟨(fun f hf => by cases hf; exact h.1), hc, hlc, hone, hneg⟩
  · next st hpause =>
    rw [hpause] at h
    obtain ⟨hok, hcur, hnone⟩ := h
    exact ioResumeLoop_complete T hsane hnet hnetTcp sbelt query qu₀ depth fuel st
      (now + budget) (seedRevealed st) hok hcur hnone
  · exact SatisfiesM.pure ⟨(fun _ hf => nomatch hf), hc, hlc, hone, hneg⟩

end ShimCompleteness

end VeriDNS.Proof.NameTree

rfc_proves VeriDNS.Proof.NameTree.resolveWithIO_complete [2181][195:202]
