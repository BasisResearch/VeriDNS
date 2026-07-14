import VeriDNS.Impl.Cache
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Server
import VeriDNS.RFC.Check
import VeriDNS.Proof.DomainName
import VeriDNS.Proof.NameTreeComplete
import VeriDNS.Proof.Cache
import VeriDNS.Spec.NetworkSemantics

namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (Trustworthiness RRType RRClass)
open VeriDNS.Impl
open VeriDNS.Impl.DomainName (nameEqCI)

def αType (t : BitVec 16) : Option RRType :=
  match t.toNat with
  | 1 => some .a   | 2 => some .ns   | 3 => some .md    | 4 => some .mf
  | 5 => some .cname | 6 => some .soa | 7 => some .mb   | 8 => some .mg
  | 9 => some .mr  | 10 => some .null | 11 => some .wks | 12 => some .ptr
  | 13 => some .hinfo | 14 => some .minfo | 15 => some .mx | 16 => some .txt
  | _ => some (.unknown t)

theorem αType_total (t : BitVec 16) : ∃ rt, αType t = some rt := by
  unfold αType; split <;> exact ⟨_, rfl⟩

def αClass (c : BitVec 16) : Option RRClass :=
  match c.toNat with
  | 1 => some .in | 2 => some .cs | 3 => some .ch | 4 => some .hs | _ => none

def αQType (qt : BitVec 16) : Option VeriDNS.Spec.Net.QType :=
  if qt.toNat = 255 then some .star else (αType qt).map .rr

def αName (w : ByteArray) : Option VeriDNS.Spec.Net.Name :=
  match DomainName.wireFormatToLabels w with
  | .ok labels => some labels.toList
  | .error _ => none

theorem αName_valid {w : ByteArray} {na : VeriDNS.Spec.Net.Name} (h : αName w = some na) :
    ∀ x ∈ na, 0 < x.size ∧ x.size ≤ 63 := by
  unfold αName at h
  split at h
  · next labels hlab =>
    have hna : labels.toList = na := Option.some.inj h
    intro x hx
    exact VeriDNS.Proof.DomainName.wireFormatToLabels_valid hlab x (hna ▸ hx)
  · exact absurd h (by simp)



theorem foldByte_eq (x : UInt8) :
    VeriDNS.Spec.Net.foldByte x = DomainName.foldCaseByte x := by
  unfold VeriDNS.Spec.Net.foldByte DomainName.foldCaseByte
  simp only [Nat.ble_eq, Bool.cond_eq_ite, decide_eq_true_eq, Bool.and_eq_true,
    UInt8.le_iff_toNat_le, show UInt8.toNat 65 = 65 from rfl, show UInt8.toNat 90 = 90 from rfl]

theorem foldNameCase_append (a b : ByteArray) :
    DomainName.foldNameCase (a ++ b)
      = DomainName.foldNameCase a ++ DomainName.foldNameCase b := by
  apply ByteArray.ext
  simp [DomainName.foldNameCase, ByteArray.data_append, Array.map_append]

theorem foldCaseByte_le63 (b : UInt8) (h : b ≤ 63) : DomainName.foldCaseByte b = b := by
  unfold DomainName.foldCaseByte
  have hcond : (65 ≤ b && b ≤ 90) = false := by
    rcases Nat.lt_or_ge b.toNat 65 with hlt | hge
    · simp only [Bool.and_eq_false_iff]; left
      simp only [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, Nat.not_le]; exact hlt
    · exfalso; rw [UInt8.le_iff_toNat_le] at h
      simp only [show UInt8.toNat 63 = 63 from rfl] at h; omega
  simp [hcond]

theorem size_toUInt8_le63 (x : ByteArray) (h : x.size ≤ 63) : x.size.toUInt8 ≤ 63 := by
  have hsz : x.size.toUInt8.toNat = x.size := by
    have : x.size.toUInt8.toNat = x.size % 256 := rfl
    omega
  rw [UInt8.le_iff_toNat_le, hsz, show UInt8.toNat 63 = 63 from rfl]; exact h

theorem foldNameCase_push (b : UInt8) (h : b ≤ 63) :
    DomainName.foldNameCase (ByteArray.empty.push b) = ByteArray.empty.push b := by
  apply ByteArray.ext
  simp [DomainName.foldNameCase, foldCaseByte_le63 b h]

theorem foldNameCase_labelsToWireFormatGo (l : List ByteArray) (hv : ∀ x ∈ l, x.size ≤ 63) :
    DomainName.foldNameCase (DomainName.labelsToWireFormatGo l)
      = DomainName.labelsToWireFormatGo (l.map DomainName.foldNameCase) := by
  induction l with
  | nil =>
    show DomainName.foldNameCase ⟨#[0]⟩ = ⟨#[0]⟩
    apply ByteArray.ext
    show (#[(0:UInt8)]).map DomainName.foldCaseByte = #[0]
    rw [Array.map_singleton, show DomainName.foldCaseByte 0 = 0 from by decide]
  | cons x rest ih =>
    simp only [List.map_cons, DomainName.labelsToWireFormatGo]
    rw [foldNameCase_append, foldNameCase_append,
        ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))]
    have hxsz : (DomainName.foldNameCase x).size = x.size := Array.size_map
    rw [foldNameCase_push x.size.toUInt8 (size_toUInt8_le63 x (hv x List.mem_cons_self)), hxsz]

theorem foldNameCase_labelsToWireFormat (ls : Array ByteArray) (hv : ∀ x ∈ ls, x.size ≤ 63) :
    DomainName.foldNameCase (DomainName.labelsToWireFormat ls)
      = DomainName.labelsToWireFormat (ls.map DomainName.foldNameCase) := by
  unfold DomainName.labelsToWireFormat
  rw [foldNameCase_labelsToWireFormatGo ls.toList (fun x hx => hv x (Array.mem_def.mpr hx)),
    Array.toList_map]

theorem bytesEqCI_of_mapEq (as bs : List UInt8)
    (h : as.map DomainName.foldCaseByte = bs.map DomainName.foldCaseByte) :
    VeriDNS.Spec.Net.bytesEqCI as bs = true := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons b bs => simp at h
  | cons a as ih => cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      unfold VeriDNS.Spec.Net.bytesEqCI
      rw [foldByte_eq, foldByte_eq, h.1]
      simp only [beq_self_eq_true, Bool.true_and]
      exact ih bs h.2

theorem labelEq_of_foldEq (x y : ByteArray)
    (h : DomainName.foldNameCase x = DomainName.foldNameCase y) :
    VeriDNS.Spec.Net.labelEq x y = true := by
  unfold VeriDNS.Spec.Net.labelEq
  apply bytesEqCI_of_mapEq
  have hd : x.data.map DomainName.foldCaseByte = y.data.map DomainName.foldCaseByte := by
    unfold DomainName.foldNameCase at h; injection h
  rw [← Array.toList_map, ← Array.toList_map, hd]

theorem nameEq_of_mapfold (xs ys : List ByteArray)
    (h : xs.map DomainName.foldNameCase = ys.map DomainName.foldNameCase) :
    VeriDNS.Spec.Net.nameEq xs ys = true := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih => cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      unfold VeriDNS.Spec.Net.nameEq
      rw [labelEq_of_foldEq x y h.1]
      simp only [Bool.true_and]
      exact ih ys h.2

theorem mapEq_of_bytesEqCI (as bs : List UInt8)
    (h : VeriDNS.Spec.Net.bytesEqCI as bs = true) :
    as.map DomainName.foldCaseByte = bs.map DomainName.foldCaseByte := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons b bs => simp [VeriDNS.Spec.Net.bytesEqCI] at h
  | cons a as ih => cases bs with
    | nil => simp [VeriDNS.Spec.Net.bytesEqCI] at h
    | cons b bs =>
      unfold VeriDNS.Spec.Net.bytesEqCI at h
      simp only [Bool.and_eq_true] at h
      rw [foldByte_eq, foldByte_eq] at h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨eq_of_beq h.1, ih bs h.2⟩

theorem foldEq_of_labelEq (x y : ByteArray) (h : VeriDNS.Spec.Net.labelEq x y = true) :
    DomainName.foldNameCase x = DomainName.foldNameCase y := by
  unfold VeriDNS.Spec.Net.labelEq at h
  have hm := mapEq_of_bytesEqCI x.data.toList y.data.toList h
  have harr : x.data.map DomainName.foldCaseByte = y.data.map DomainName.foldCaseByte := by
    apply Array.toList_inj.mp
    rw [Array.toList_map, Array.toList_map]; exact hm
  unfold DomainName.foldNameCase
  rw [harr]

theorem mapfold_of_nameEq (xs ys : List ByteArray)
    (h : VeriDNS.Spec.Net.nameEq xs ys = true) :
    xs.map DomainName.foldNameCase = ys.map DomainName.foldNameCase := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp [VeriDNS.Spec.Net.nameEq] at h
  | cons x xs ih => cases ys with
    | nil => simp [VeriDNS.Spec.Net.nameEq] at h
    | cons y ys =>
      unfold VeriDNS.Spec.Net.nameEq at h
      simp only [Bool.and_eq_true] at h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨foldEq_of_labelEq x y h.1, ih ys h.2⟩

theorem nameEqCI_of_αName_canonical {a b : ByteArray} {na nb : VeriDNS.Spec.Net.Name}
    (h : VeriDNS.Spec.Net.nameEq na nb = true)
    (hca : a = DomainName.labelsToWireFormatGo na) (hcb : b = DomainName.labelsToWireFormatGo nb)
    (hva : ∀ x ∈ na, x.size ≤ 63) (hvb : ∀ x ∈ nb, x.size ≤ 63) :
    VeriDNS.Impl.DomainName.nameEqCI a b = true := by
  rw [VeriDNS.Proof.NameTree.nameEqCI_iff, hca, hcb,
      foldNameCase_labelsToWireFormatGo na hva, foldNameCase_labelsToWireFormatGo nb hvb,
      mapfold_of_nameEq na nb h]

theorem αName_of_nameEqCI {a b : ByteArray} {nb : VeriDNS.Spec.Net.Name}
    (h : nameEqCI a b = true) (hb : αName b = some nb) :
    ∃ na, αName a = some na ∧ VeriDNS.Spec.Net.nameEq na nb = true := by
  have hfold : DomainName.foldNameCase a = DomainName.foldNameCase b :=
    VeriDNS.Proof.NameTree.nameEqCI_iff.mp h
  unfold αName at hb ⊢
  cases hbl : DomainName.wireFormatToLabels b with
  | error e => rw [hbl] at hb; exact absurd hb (by simp)
  | ok bL =>
    rw [hbl] at hb; injection hb with hb; subst hb
    have hfb := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok b bL hbl
    cases hal : DomainName.wireFormatToLabels a with
    | error ea =>
      obtain ⟨ea', hea'⟩ := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_error a ea hal
      rw [hfold, hfb] at hea'
      exact absurd hea' (by simp)
    | ok aL =>
      refine ⟨aL.toList, rfl, ?_⟩
      have hfa := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok a aL hal
      rw [hfold, hfb] at hfa
      injection hfa with hfa
      apply nameEq_of_mapfold
      have := congrArg Array.toList hfa
      simpa using this.symm

theorem nameEqCI_eq_nameEq {a b : ByteArray} {na nb : VeriDNS.Spec.Net.Name}
    (hca : a = DomainName.labelsToWireFormatGo na) (hva : ∀ x ∈ na, x.size ≤ 63) (hαa : αName a = some na)
    (hcb : b = DomainName.labelsToWireFormatGo nb) (hvb : ∀ x ∈ nb, x.size ≤ 63) (hαb : αName b = some nb) :
    VeriDNS.Impl.DomainName.nameEqCI a b = VeriDNS.Spec.Net.nameEq na nb := by
  by_cases hne : VeriDNS.Spec.Net.nameEq na nb = true
  · rw [hne]; exact nameEqCI_of_αName_canonical hne hca hcb hva hvb
  · rw [Bool.not_eq_true] at hne
    rw [hne]
    cases hci : VeriDNS.Impl.DomainName.nameEqCI a b with
    | false => rfl
    | true =>
      obtain ⟨na', hαa', hnt⟩ := αName_of_nameEqCI hci hαb
      obtain rfl : na' = na := Option.some.inj (hαa'.symm.trans hαa)
      rw [hne] at hnt; exact absurd hnt (by simp)

theorem nameEqCI_size_ne {a b : ByteArray} (h : a.size ≠ b.size) :
    VeriDNS.Impl.DomainName.nameEqCI a b = false := by
  rw [← Bool.not_eq_true, VeriDNS.Proof.NameTree.nameEqCI_iff]
  intro heq
  exact h (by rw [← VeriDNS.Proof.NameTree.foldNameCase_size a,
    ← VeriDNS.Proof.NameTree.foldNameCase_size b, heq])

theorem nameEqCI_false_of_isAncestorB_ne {bw owner n : ByteArray}
    (h : Resolver.isAncestorB bw owner ≠ Resolver.isAncestorB bw n) :
    VeriDNS.Impl.DomainName.nameEqCI owner n = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  exact h (VeriDNS.Proof.NameTree.isAncestorB_congr bw owner n hc)

theorem glue_findSome_none_of_out_of_bailiwick (cut n : ByteArray)
    (glue : Array (ByteArray × BitVec 32))
    (hn : Resolver.isAncestorB cut n = false)
    (hglue : ∀ gp ∈ glue, Resolver.isAncestorB cut gp.1 = true) :
    glue.findSome? (fun (gn, ga) =>
      if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none) = none := by
  rw [Array.findSome?_eq_none_iff]
  intro gp hgp
  have hne : VeriDNS.Impl.DomainName.nameEqCI gp.1 n = false :=
    nameEqCI_false_of_isAncestorB_ne (by rw [hglue gp hgp, hn]; simp)
  simp [hne]

theorem isAncestorB_isAncestor (bw owner : ByteArray) (bwN ownerN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (hown : αName owner = some ownerN)
    (h : Resolver.isAncestorB bw owner = true) :
    VeriDNS.Spec.Net.isAncestor bwN ownerN = true := by
  unfold αName at hbw hown
  cases hbwl : DomainName.wireFormatToLabels bw with
  | error e => rw [hbwl] at hbw; exact absurd hbw (by simp)
  | ok bwL =>
  cases hownl : DomainName.wireFormatToLabels owner with
  | error e => rw [hownl] at hown; exact absurd hown (by simp)
  | ok ownerL =>
    rw [hbwl] at hbw; rw [hownl] at hown
    injection hbw with hbw; injection hown with hown
    subst hbw; subst hown
    unfold Resolver.isAncestorB at h
    rw [hbwl, hownl] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, hbeq⟩ := h
    unfold VeriDNS.Spec.Net.isAncestor
    rw [Nat.ble_eq.mpr (by simpa using hlen)]
    simp only [cond_true]
    apply nameEq_of_mapfold
    rw [List.map_drop]
    simpa using hbeq

theorem isAncestor_isAncestorB (bw owner : ByteArray) (bwN ownerN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (hown : αName owner = some ownerN)
    (h : VeriDNS.Spec.Net.isAncestor bwN ownerN = true) :
    Resolver.isAncestorB bw owner = true := by
  unfold αName at hbw hown
  cases hbwl : DomainName.wireFormatToLabels bw with
  | error e => rw [hbwl] at hbw; exact absurd hbw (by simp)
  | ok bwL =>
  cases hownl : DomainName.wireFormatToLabels owner with
  | error e => rw [hownl] at hown; exact absurd hown (by simp)
  | ok ownerL =>
    rw [hbwl] at hbw; rw [hownl] at hown
    injection hbw with hbw; injection hown with hown
    subst hbw; subst hown
    unfold VeriDNS.Spec.Net.isAncestor at h
    unfold Resolver.isAncestorB
    rw [hbwl, hownl]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases hlen : Nat.ble bwL.toList.length ownerL.toList.length = true
    · rw [hlen, cond_true] at h
      refine ⟨by simpa using hlen, ?_⟩
      have := mapfold_of_nameEq _ _ h
      rw [List.map_drop] at this
      simpa using this
    · rw [Bool.eq_false_iff.mpr hlen, cond_false] at h; exact absurd h (by simp)

theorem array_foldl_toList {β : Type} (f : β → ByteArray → β) (init : β) (a : Array ByteArray) :
    a.foldl f init = a.toList.foldl f init := by
  rw [← List.foldl_toArray, Array.toArray_toList]

theorem mem_store_records {c : Cache.DnsCache} {rr : VeriDNS.Spec.ResourceRecord} {now : UInt32}
    {cred : Trustworthiness} {e : Cache.CacheEntry}
    (h : e ∈ (c.store rr now cred).records) : e ∈ c.records ∨ e.rr = rr := by
  unfold Cache.DnsCache.store at h
  simp only [Array.mem_push] at h
  rcases h with h | h
  · exact Or.inl (Array.mem_filter.mp h).1
  · subst h; exact Or.inr rfl

theorem storeChecked_cases (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) :
    c.storeChecked rr cred now = c ∨ c.storeChecked rr cred now = c.store rr now cred := by
  simp only [Cache.DnsCache.storeChecked]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem mem_storeChecked_records {c : Cache.DnsCache} {rr : VeriDNS.Spec.ResourceRecord}
    {cred : Trustworthiness} {now : UInt32} {e : Cache.CacheEntry}
    (h : e ∈ (c.storeChecked rr cred now).records) : e ∈ c.records ∨ e.rr = rr := by
  rcases storeChecked_cases c rr cred now with heq | heq
  · rw [heq] at h; exact Or.inl h
  · rw [heq] at h; exact mem_store_records h

theorem cacheRRs_append (c : Cache.DnsCache) (raws₁ raws₂ : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) :
    Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c (raws₁ ++ raws₂) cred now
      = Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws₁ cred now)
          raws₂ cred now := by
  unfold Resolver.cacheRRs
  rw [Array.foldl_append]

theorem cacheRRs_singleton (X : Cache.DnsCache) (b : ByteArray) (cred : Trustworthiness) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) X #[b] cred now
      = X.storeChecked rr cred now := by
  unfold Resolver.cacheRRs
  simp [hp]
  rfl

theorem mem_cacheRRs_live_of_split (c : Cache.DnsCache) (pre post : Array ByteArray) (nsRaw : ByteArray)
    (nsRR : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsRR)
    (hnz : (nsRR.ttl == 0) = false)
    (hbetter : ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c pre cred now).records.any
      fun e => DomainName.nameEqCI e.rr.name nsRR.name && e.rr.type == nsRR.type && e.rr.class == nsRR.class
        && (e.expiry > now || e.expiry == now + nsRR.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false)
    (hfresh : Cache.CacheEntry.fresh ⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred, now⟩ now = true)
    (hpost : ∀ b ∈ post, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (DomainName.nameEqCI nsRR.name rr.name && nsRR.type == rr.type && nsRR.class == rr.class
        && (now + nsRR.ttl.toNat.toUInt32 != now + rr.ttl.toNat.toUInt32 || nsRR.rdata == rr.rdata)) = false) :
    ∃ e ∈ (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (pre ++ #[nsRaw] ++ post) cred now).records,
      Cache.liveEntry e nsRR.name nsRR.type nsRR.class now = true := by
  refine ⟨⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred, now⟩, ?_, ?_⟩
  · rw [Array.append_assoc, cacheRRs_append c pre (#[nsRaw] ++ post),
       cacheRRs_append (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
         c pre cred now) #[nsRaw] post]
    refine VeriDNS.Proof.Cache.mem_cacheRRs_preserve _ post cred now
      ⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred, now⟩ ?_ ?_
    · rw [cacheRRs_singleton _ nsRaw cred now nsRR hp, Cache.DnsCache.storeChecked]
      simp only [hnz, Bool.false_eq_true, if_false, hbetter]
      exact Array.mem_push.mpr (Or.inr rfl)
    · intro b hb rr hpr; exact hpost b hb rr hpr
  · simp only [Cache.liveEntry, VeriDNS.Proof.NameTree.nameEqCI_refl, beq_self_eq_true, hfresh,
      Bool.and_self]

theorem mem_cacheRRs_records (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32)
    (c : Cache.DnsCache) {e : Cache.CacheEntry}
    (h : e ∈ (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now).records) :
    e ∈ c.records ∨ ∃ b ∈ raws.toList,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some e.rr := by
  unfold Resolver.cacheRRs at h
  refine Array.foldl_induction
    (motive := fun _ (acc : Cache.DnsCache) => e ∈ acc.records →
      e ∈ c.records ∨ ∃ b ∈ raws.toList,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some e.rr)
    (fun he => Or.inl he) ?_ h
  intro i acc ih hacc
  cases hpi : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raws[i] with
  | none => simp only [hpi] at hacc; exact ih hacc
  | some rr =>
    simp only [hpi] at hacc
    rcases mem_storeChecked_records (rr := rr) hacc with h' | h'
    · exact ih h'
    · exact Or.inr ⟨raws[i], Array.mem_def.mp (Array.getElem_mem i.isLt), by rw [hpi, h']⟩

theorem cacheRRs_bailiwick_owner (c : Cache.DnsCache) (cut : ByteArray) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) {e : Cache.CacheEntry}
    (h : e ∈ (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut raws) cred now).records) :
    e ∈ c.records ∨ Resolver.isAncestorB cut e.rr.name = true := by
  rcases mem_cacheRRs_records (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut raws)
      cred now c h with h' | ⟨b, hb, hpr⟩
  · exact Or.inl h'
  · exact Or.inr (Resolver.bailiwickRaws_owner_inBailiwick cut raws hb hpr)

theorem isAncestorB_self {a : ByteArray} {labels : Array ByteArray}
    (h : DomainName.wireFormatToLabels a = .ok labels) : Resolver.isAncestorB a a = true := by
  unfold Resolver.isAncestorB
  rw [h]
  simp only [Nat.le_refl, decide_true, Nat.sub_self, List.drop_zero, Bool.and_self, decide_eq_true_eq]

theorem parentDomainWire_some {wire parent : ByteArray}
    (h : DomainName.parentDomainWire wire = some parent) :
    ∃ labels, DomainName.wireFormatToLabels wire = .ok labels ∧ labels.size ≠ 0
      ∧ DomainName.labelsToWireFormat (labels.extract 1) = parent := by
  unfold DomainName.parentDomainWire at h
  split at h
  · exact absurd h (by simp)
  · next labels heq =>
    split at h
    · exact absurd h (by simp)
    · next hne => exact ⟨labels, heq, by simpa using hne, by simpa using h⟩

theorem validLabels_extract {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    VeriDNS.Proof.DomainName.ValidLabels (labels.extract 1) := by
  intro i hi
  have hbound : 1 + i < labels.size := by
    have := hi; rw [Array.size_extract] at this; omega
  rw [Array.getElem_extract]
  exact hv (1 + i) hbound

theorem parentDomainWire_labelsToWireFormat {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) (hne : labels.size ≠ 0) :
    DomainName.parentDomainWire (DomainName.labelsToWireFormat labels)
      = some (DomainName.labelsToWireFormat (labels.extract 1)) := by
  unfold DomainName.parentDomainWire
  rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip labels hv]
  simp only [beq_iff_eq, hne, if_false, reduceIte]

theorem validLabels_extract_start {labels : Array ByteArray} {s : Nat}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    VeriDNS.Proof.DomainName.ValidLabels (labels.extract s) := by
  intro i hi
  have hbound : s + i < labels.size := by
    have := hi; rw [Array.size_extract] at this; omega
  rw [Array.getElem_extract]
  exact hv (s + i) hbound

theorem extract_extract_one {labels : Array ByteArray} {d : Nat} :
    (labels.extract d).extract 1 = labels.extract (d + 1) := by
  rw [Array.extract_extract]
  congr 1
  simp only [Array.size_extract]
  omega

theorem parentDomainWire_αName {a b : ByteArray} {labels : Array ByteArray}
    (hwl : DomainName.wireFormatToLabels a = .ok labels)
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels)
    (h : DomainName.parentDomainWire a = some b) :
    labels.toList ≠ [] ∧ αName a = some labels.toList ∧ αName b = some labels.toList.tail := by
  have hαa : αName a = some labels.toList := by unfold αName; rw [hwl]
  obtain ⟨labels', hwl', hne, hpar⟩ := parentDomainWire_some h
  have hll : labels = labels' := Except.ok.inj (hwl.symm.trans hwl')
  rw [← hll] at hpar hne
  refine ⟨?_, hαa, ?_⟩
  · intro hc
    rw [Array.toList_eq_nil_iff] at hc
    rw [hc] at hne
    exact hne rfl
  · have hαb : αName b = some (labels.extract 1).toList := by
      rw [← hpar]; unfold αName
      rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip (labels.extract 1) (validLabels_extract hv)]
    rw [hαb]
    congr 1
    rw [Array.toList_extract]
    simp [List.drop_one]
    apply List.take_of_length_le
    simp [List.length_tail]

theorem array_extract_one_toList {α : Type} (a : Array α) : (a.extract 1).toList = a.toList.tail := by
  rw [Array.toList_extract]
  simp [List.drop_one]
  apply List.take_of_length_le
  simp [List.length_tail]

theorem parentDomainWire_chain_αName :
    ∀ (L : List ByteArray) (start : ByteArray) (lab : Array ByteArray),
      DomainName.wireFormatToLabels start = .ok lab →
      VeriDNS.Proof.DomainName.ValidLabels lab →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start L →
      List.Chain (fun (a b : VeriDNS.Spec.Net.Name) => a ≠ [] ∧ a.tail = b)
        lab.toList (L.map (fun w => (αName w).getD [])) := by
  intro L
  induction L with
  | nil => intro start lab _ _ _; exact List.Chain.nil
  | cons b rest ih =>
    intro start lab hwl hv hchain
    obtain ⟨hlink, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨lab', hwl', hne', hpar⟩ := parentDomainWire_some hlink
    have hll : lab = lab' := Except.ok.inj (hwl.symm.trans hwl')
    have hwlb : DomainName.wireFormatToLabels b = .ok (lab.extract 1) := by
      rw [← hpar, hll]
      exact VeriDNS.Proof.DomainName.wireFormat_roundtrip (lab'.extract 1) (validLabels_extract (hll ▸ hv))
    have hαb' : αName b = some (lab.extract 1).toList := by unfold αName; rw [hwlb]
    have hne : lab.toList ≠ [] := by
      intro hc; rw [Array.toList_eq_nil_iff] at hc
      rw [← hll] at hne'; rw [hc] at hne'; exact hne' rfl
    rw [List.map_cons]
    refine List.Chain.cons ⟨hne, ?_⟩ ?_
    · show lab.toList.tail = (αName b).getD []
      rw [hαb']
      exact (array_extract_one_toList lab).symm
    · show List.Chain _ ((αName b).getD []) _
      rw [show (αName b).getD [] = (lab.extract 1).toList from by simp [hαb']]
      exact ih b (lab.extract 1) hwlb (validLabels_extract hv) hchain'

theorem chain_canonical :
    ∀ (L : List ByteArray) (start : ByteArray) (lab : Array ByteArray),
      DomainName.wireFormatToLabels start = .ok lab → VeriDNS.Proof.DomainName.ValidLabels lab →
      start = DomainName.labelsToWireFormatGo lab.toList →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start L →
      ∀ m ∈ start :: L, ∃ na, αName m = some na ∧ m = DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63) := by
  intro L
  induction L with
  | nil =>
    intro start lab hwl hv hcanon _ m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    refine ⟨lab.toList, by unfold αName; rw [hwl], hcanon, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Array.getElem_toList]
    exact (hv i (by rwa [Array.length_toList] at hi)).2
  | cons b rest ih =>
    intro start lab hwl hv hcanon hchain m hm
    obtain ⟨hlink, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨lab', hwl', hne, hpar⟩ := parentDomainWire_some hlink
    have hll : lab = lab' := Except.ok.inj (hwl.symm.trans hwl')
    have hwlb : DomainName.wireFormatToLabels b = .ok (lab.extract 1) := by
      rw [← hpar, hll]
      exact VeriDNS.Proof.DomainName.wireFormat_roundtrip (lab'.extract 1) (validLabels_extract (hll ▸ hv))
    have hbcanon : b = DomainName.labelsToWireFormatGo (lab.extract 1).toList := by
      rw [← hpar, hll]; rfl
    rcases List.mem_cons.mp hm with rfl | hm'
    · refine ⟨lab.toList, by unfold αName; rw [hwl], hcanon, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [Array.getElem_toList]
      exact (hv i (by rwa [Array.length_toList] at hi)).2
    · exact ih b (lab.extract 1) hwlb (validLabels_extract hv) hbcanon hchain' m hm'

theorem parentDomainWire_chain_length :
    ∀ (L : List ByteArray) (start : ByteArray) (lab : Array ByteArray),
      DomainName.wireFormatToLabels start = .ok lab → VeriDNS.Proof.DomainName.ValidLabels lab →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start L →
      L.length ≤ lab.size := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _; simp
  | cons b rest ih =>
    intro start lab hwl hv hchain
    obtain ⟨hlink, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨lab', hwl', hne, hpar⟩ := parentDomainWire_some hlink
    have hll : lab = lab' := Except.ok.inj (hwl.symm.trans hwl')
    have hwlb : DomainName.wireFormatToLabels b = .ok (lab.extract 1) := by
      rw [← hpar, hll]
      exact VeriDNS.Proof.DomainName.wireFormat_roundtrip (lab'.extract 1) (validLabels_extract (hll ▸ hv))
    have hib := ih b (lab.extract 1) hwlb (validLabels_extract hv) hchain'
    have hsz : (lab.extract 1).size = lab.size - 1 := by rw [Array.size_extract]; omega
    have hne' : lab.size ≠ 0 := by rw [hll]; exact hne
    rw [hsz] at hib
    simp only [List.length_cons]
    omega

theorem parentChain_aux {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    ∀ (n s : Nat), s + n ≤ labels.size →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b)
        (DomainName.labelsToWireFormat (labels.extract s))
        ((List.range' (s + 1) n).map (fun i => DomainName.labelsToWireFormat (labels.extract i))) := by
  intro n
  induction n with
  | zero => intro s _; exact List.Chain.nil
  | succ n ih =>
    intro s hs
    have hne : (labels.extract s).size ≠ 0 := by
      simp only [Array.size_extract, Nat.min_self]; omega
    have hstep : DomainName.parentDomainWire (DomainName.labelsToWireFormat (labels.extract s))
        = some (DomainName.labelsToWireFormat (labels.extract (s + 1))) := by
      rw [parentDomainWire_labelsToWireFormat (validLabels_extract_start hv) hne, extract_extract_one]
    rw [List.range'_succ, List.map_cons]
    exact List.Chain.cons hstep (ih (s + 1) (by omega))

theorem parentChain_from_root {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) (d : Nat) (hdle : d ≤ labels.size) :
    List.Chain (fun a b => DomainName.parentDomainWire a = some b)
      (DomainName.labelsToWireFormat labels)
      ((List.range' 1 d).map (fun i => DomainName.labelsToWireFormat (labels.extract i))) := by
  have h := parentChain_aux hv d 0 (by omega)
  simpa using h

theorem parentChain_inter_zone {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) (d : Nat) (hd : 0 < d) (hdle : d ≤ labels.size) :
    List.Chain (fun a b => DomainName.parentDomainWire a = some b)
      (DomainName.labelsToWireFormat labels)
      ((List.range' 1 (d - 1)).map (fun i => DomainName.labelsToWireFormat (labels.extract i))
        ++ [DomainName.labelsToWireFormat (labels.extract d)]) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h := parentChain_from_root hv (k + 1) hdle
  rw [List.range'_concat, List.map_append, List.map_cons, List.map_nil] at h
  have e2 : 1 + 1 * k = k + 1 := by omega
  rw [e2] at h
  simpa using h



theorem store_negatives (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : VeriDNS.Spec.Trustworthiness) : (Cache.DnsCache.store c rr now cred).negatives = c.negatives :=
  rfl

theorem storeChecked_negatives (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    (c.storeChecked rr cred now).negatives = c.negatives := by
  rcases storeChecked_cases c rr cred now with h | h
  · rw [h]
  · rw [h, store_negatives]

theorem cacheRRs_negatives (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (c : Cache.DnsCache) :
    (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now).negatives
      = c.negatives := by
  unfold Resolver.cacheRRs
  refine Array.foldl_induction (motive := fun _ (acc : Cache.DnsCache) => acc.negatives = c.negatives)
    rfl ?_
  intro i acc hacc
  split
  · next rr' hrr' =>
    rw [show VeriDNS.Spec.TrustworthinessSpec.acceptRrset acc rr' cred now = acc.storeChecked rr' cred now
        from rfl, storeChecked_negatives]
    exact hacc
  · exact hacc

theorem store_fresh_records (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : VeriDNS.Spec.Trustworthiness)
    (h : ∀ e ∈ c.records, (VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class) = false) :
    (Cache.DnsCache.store c rr now cred).records
      = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  have hf : Array.filter (fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != (now + rr.ttl.toNat.toUInt32) || e.rr.rdata == rr.rdata))) c.records = c.records := by
    apply Array.filter_eq_self.mpr
    intro e he
    rw [h e he]; simp
  show (Array.filter _ c.records).push _ = _
  rw [hf]

theorem storeChecked_fresh_push (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (httl : (rr.ttl == 0) = false)
    (h : ∀ e ∈ c.records, (VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class) = false) :
    (c.storeChecked rr cred now).records = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  have hbetter : (c.records.any fun e =>
      VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false := by
    by_contra hc
    rw [Bool.not_eq_false, Array.any_eq_true] at hc
    obtain ⟨i, hi, hpe⟩ := hc
    rw [h c.records[i] (Array.getElem_mem hi)] at hpe
    simp at hpe
  simp only [Cache.DnsCache.storeChecked, httl, hbetter, Bool.false_eq_true, if_false]
  exact store_fresh_records c rr now cred h

theorem storeChecked_push_of (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (httl : (rr.ttl == 0) = false)
    (hbetter : (c.records.any fun e =>
        VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type
          && e.rr.class == rr.class
          && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
          && e.credibility.toCode < cred.toCode) = false)
    (hstore : (Cache.DnsCache.store c rr now cred).records
        = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩) :
    (c.storeChecked rr cred now).records
      = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  unfold Cache.DnsCache.storeChecked
  simp only [httl, hbetter, Bool.false_eq_true, if_false]
  exact hstore

theorem store_push_records (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : VeriDNS.Spec.Trustworthiness)
    (h : ∀ e ∈ c.records, (VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != (now + rr.ttl.toNat.toUInt32) || e.rr.rdata == rr.rdata)) = false) :
    (Cache.DnsCache.store c rr now cred).records
      = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  have hf : Array.filter (fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != (now + rr.ttl.toNat.toUInt32) || e.rr.rdata == rr.rdata))) c.records = c.records := by
    apply Array.filter_eq_self.mpr
    intro e he
    simp only [h e he, Bool.not_false]
  show (Array.filter _ c.records).push _ = _
  rw [hf]

theorem cacheRRs_records_append (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (c : Cache.DnsCache)
    (h : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b ∈ raws.toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        ∃ pre, (VeriDNS.Spec.TrustworthinessSpec.acceptRrset acc rr cred now).records
          = acc.records ++ pre) :
    ∃ extra, (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now).records = c.records ++ extra := by
  unfold Resolver.cacheRRs
  refine Array.foldl_induction
    (motive := fun _ (acc : Cache.DnsCache) => ∃ pre, acc.records = c.records ++ pre)
    ⟨#[], by simp⟩ ?_
  intro i acc ⟨pre, hpre⟩
  split
  · next rr hrr =>
    obtain ⟨pre0, hp0⟩ := h acc raws[i] rr (by simp) hrr
    exact ⟨pre ++ pre0, hp0.trans (by rw [hpre, Array.append_assoc])⟩
  · next => exact ⟨pre, hpre⟩

def pushOf (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (b : ByteArray) : List Cache.CacheEntry :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | some rr => if rr.ttl == 0 then [] else [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩]
  | none => []

theorem pushOf_none {b : ByteArray} (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = none) :
    pushOf cred now b = [] := by unfold pushOf; rw [h]

theorem pushOf_zero {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord} (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (h0 : (rr.ttl == 0) = true) : pushOf cred now b = [] := by
  unfold pushOf; rw [h]; simp only [h0, if_true]

theorem pushOf_pos {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord} (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (h0 : (rr.ttl == 0) = false) :
    pushOf cred now b = [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩] := by
  unfold pushOf; rw [h]; simp only [h0, Bool.false_eq_true, if_false]

theorem foldl_storeChecked_concrete (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (l : List ByteArray) (c : Cache.DnsCache)
    (h : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b ∈ l →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (rr.ttl == 0) = false →
        (acc.storeChecked rr cred now).records
          = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩) :
    (l.foldl (fun acc b => match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
        | some rr => acc.storeChecked rr cred now | none => acc) c).records.toList
      = c.records.toList ++ l.flatMap (pushOf cred now) := by
  induction l generalizing c with
  | nil => simp
  | cons b t ih =>
    have ht : ∀ (acc : Cache.DnsCache) (b' : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b' ∈ t →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
        (rr.ttl == 0) = false →
        (acc.storeChecked rr cred now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :=
      fun acc b' rr hb' => h acc b' rr (List.mem_cons_of_mem _ hb')
    simp only [List.foldl_cons, List.flatMap_cons]
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [pushOf_none cred now hpr, List.nil_append]; exact ih c ht
    | some rr =>
      by_cases htt : (rr.ttl == 0) = true
      · rw [pushOf_zero cred now hpr htt, List.nil_append]
        have hsc : (c.storeChecked rr cred now).records.toList = c.records.toList := by
          unfold Cache.DnsCache.storeChecked; simp only [htt, if_true]
        simp only [hpr]
        rw [ih (c.storeChecked rr cred now) ht, hsc]
      · have htf : (rr.ttl == 0) = false := by simpa using htt
        rw [pushOf_pos cred now hpr htf]
        simp only [hpr]
        rw [ih (c.storeChecked rr cred now) ht, h c b rr (by simp) hpr htf, Array.toList_push,
          List.append_assoc]

theorem αName_labelsToWireFormat (labels : Array ByteArray)
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    αName (DomainName.labelsToWireFormat labels) = some labels.toList := by
  unfold αName
  rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip labels hv]

theorem αType_toCode (rt : RRType) (hn : rt.isNamed = true) :
    αType (BitVec.ofNat 16 rt.toCode) = some rt := by
  cases rt <;> first
    | rfl
    | exact absurd hn (by simp [VeriDNS.Spec.RRType.isNamed])

theorem αClass_toCode (rc : RRClass) : αClass (BitVec.ofNat 16 rc.toCode) = some rc := by
  cases rc <;> rfl

theorem αType_some_toCode {t : BitVec 16} {rt : RRType} (h : αType t = some rt) :
    t.toNat = rt.toCode := by
  unfold αType at h
  split at h <;> simp_all <;> subst h <;> rfl

theorem αType_injective {u v : BitVec 16} {rt : RRType}
    (hu : αType u = some rt) (hv : αType v = some rt) : u = v :=
  BitVec.eq_of_toNat_eq ((αType_some_toCode hu).trans (αType_some_toCode hv).symm)

theorem αClass_inj {u v : BitVec 16} {c : RRClass}
    (hu : αClass u = some c) (hv : αClass v = some c) : u = v := by
  apply BitVec.eq_of_toNat_eq
  cases c <;>
    (unfold αClass at hu hv
     split at hu <;> simp_all <;> split at hv <;> simp_all)

theorem rrtype_eq_of_beq : ∀ {x y : RRType}, (x == y) = true → x = y := by
  intro x y h
  cases x <;> cases y <;>
    first
    | rfl
    | exact Bool.noConfusion h
    | exact congrArg RRType.unknown (eq_of_beq h)

theorem rrtype_beq_self (x : RRType) : (x == x) = true := by
  cases x <;> first
    | rfl
    | (rename_i c; show (c == c) = true; exact beq_self_eq_true c)

theorem eq_of_αType_beq {u v : BitVec 16} {x y : RRType}
    (_hx : αType u = some x) (_hy : αType v = some y) (h : (x == y) = true) : x = y :=
  rrtype_eq_of_beq h

theorem eq_of_αClass_beq {u v : BitVec 16} {x y : RRClass}
    (hx : αClass u = some x) (hy : αClass v = some y) (h : (x == y) = true) : x = y := by
  unfold αClass at hx hy
  split at hx <;> split at hy <;> simp_all <;> (subst hx; subst hy; exact absurd h (by decide))

def αCred : Trustworthiness → VeriDNS.Spec.Net.Cred
  | .primaryZone => .authoritative
  | .zoneTransfer => .authoritative
  | .authoritativeSection => .authoritative
  | .authoritySection => .authority
  | .additionalAuthoritative => .additional
  | _ => .glue

theorem αCred_usable (t : Trustworthiness) :
    (αCred t).usable = decide (t.toCode < VeriDNS.Impl.Cache.untrustworthyFloor) := by
  cases t <;> rfl

theorem αCred_order_used (t1 t2 : Trustworthiness)
    (h1 : t1 = .authoritativeSection ∨ t1 = .authoritySection ∨
          t1 = .sectionNonauthoritative ∨ t1 = .additionalAuthoritative)
    (h2 : t2 = .authoritativeSection ∨ t2 = .authoritySection ∨
          t2 = .sectionNonauthoritative ∨ t2 = .additionalAuthoritative) :
    (t1.toCode ≤ t2.toCode)
      ↔ (VeriDNS.Spec.Net.Cred.rank (αCred t2) ≤ VeriDNS.Spec.Net.Cred.rank (αCred t1)) := by
  rcases h1 with rfl|rfl|rfl|rfl <;> rcases h2 with rfl|rfl|rfl|rfl <;>
    simp [αCred, VeriDNS.Spec.Net.Cred.rank, VeriDNS.Spec.Trustworthiness.toCode]

theorem cred_used_credAnswer (aa : Bool) :
    Resolver.credAnswer aa = .authoritativeSection ∨ Resolver.credAnswer aa = .authoritySection ∨
    Resolver.credAnswer aa = .sectionNonauthoritative ∨
    Resolver.credAnswer aa = .additionalAuthoritative := by
  cases aa
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl

theorem cred_used_credAuthority (aa : Bool) :
    Resolver.credAuthority aa = .authoritativeSection ∨
    Resolver.credAuthority aa = .authoritySection ∨
    Resolver.credAuthority aa = .sectionNonauthoritative ∨
    Resolver.credAuthority aa = .additionalAuthoritative := by
  cases aa
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)

theorem cred_used_credAdditional :
    Resolver.credAdditional = .authoritativeSection ∨
    Resolver.credAdditional = .authoritySection ∨
    Resolver.credAdditional = .sectionNonauthoritative ∨
    Resolver.credAdditional = .additionalAuthoritative :=
  Or.inr (Or.inr (Or.inr rfl))

theorem cred_ranking_faithful_for_resolver
    (aa1 aa2 : Bool) (c1 c2 : Trustworthiness)
    (h1 : c1 = Resolver.credAnswer aa1 ∨ c1 = Resolver.credAuthority aa1 ∨ c1 = Resolver.credAdditional)
    (h2 : c2 = Resolver.credAnswer aa2 ∨ c2 = Resolver.credAuthority aa2 ∨ c2 = Resolver.credAdditional) :
    (c1.toCode ≤ c2.toCode)
      ↔ (VeriDNS.Spec.Net.Cred.rank (αCred c2) ≤ VeriDNS.Spec.Net.Cred.rank (αCred c1)) := by
  apply αCred_order_used
  · rcases h1 with rfl | rfl | rfl
    · exact cred_used_credAnswer aa1
    · exact cred_used_credAuthority aa1
    · exact cred_used_credAdditional
  · rcases h2 with rfl | rfl | rfl
    · exact cred_used_credAnswer aa2
    · exact cred_used_credAuthority aa2
    · exact cred_used_credAdditional

theorem αCred_credAnswer (aa : Bool) :
    αCred (Resolver.credAnswer aa)
      = (if aa then VeriDNS.Spec.Net.Cred.authoritative else VeriDNS.Spec.Net.Cred.glue) := by
  cases aa <;> rfl

theorem αCred_credAuthority (aa : Bool) :
    αCred (Resolver.credAuthority aa)
      = (if aa then VeriDNS.Spec.Net.Cred.authority else VeriDNS.Spec.Net.Cred.additional) := by
  cases aa <;> rfl

theorem αCred_credAdditional :
    αCred Resolver.credAdditional = VeriDNS.Spec.Net.Cred.additional := rfl

def αRCode : VeriDNS.Spec.Rcode → VeriDNS.Spec.Net.RCode
  | .noError => .noError
  | .nameError => .nameError
  | _ => .servFail

def αIPv4 (rdata : ByteArray) : Option VeriDNS.Spec.Net.IPv4 :=
  if rdata.size = 4 then
    some ⟨rdata.data[0]!, rdata.data[1]!, rdata.data[2]!, rdata.data[3]!⟩
  else none

def αSoa (rdata : ByteArray) : Option VeriDNS.Spec.Net.RData :=
  match DnsParser.run VeriDNS.Impl.RData.decodeSoa rdata with
  | .ok (soa, _) =>
    match αName soa.mname, αName soa.rname with
    | some mn, some rn =>
      some (.soa mn rn soa.serial.toNat soa.refresh.toNat soa.retry.toNat
        soa.expire.toNat soa.minimum.toNat)
    | _, _ => none
  | .error _ => none

theorem αSoa_inv {rdata : ByteArray} {rd : VeriDNS.Spec.Net.RData}
    (h : αSoa rdata = some rd) :
    ∃ soa rest mn rn, DnsParser.run VeriDNS.Impl.RData.decodeSoa rdata = .ok (soa, rest)
      ∧ αName soa.mname = some mn ∧ αName soa.rname = some rn
      ∧ rd = .soa mn rn soa.serial.toNat soa.refresh.toNat soa.retry.toNat
          soa.expire.toNat soa.minimum.toNat := by
  unfold αSoa at h
  cases hrun : DnsParser.run VeriDNS.Impl.RData.decodeSoa rdata with
  | error e => rw [hrun] at h; exact absurd h (by simp)
  | ok p =>
    obtain ⟨soa, rest⟩ := p
    rw [hrun] at h
    cases hmn : αName soa.mname with
    | none => simp only [hmn] at h; exact absurd h (by simp)
    | some mn =>
      cases hrn : αName soa.rname with
      | none => simp only [hmn, hrn] at h; exact absurd h (by simp)
      | some rn =>
        simp only [hmn, hrn] at h
        exact ⟨soa, rest, mn, rn, rfl, hmn, hrn, (Option.some.inj h).symm⟩

theorem αSoa_rtype {rdata : ByteArray} {rd : VeriDNS.Spec.Net.RData}
    (h : αSoa rdata = some rd) : rd.rtype = RRType.soa := by
  obtain ⟨soa, rest, mn, rn, -, -, -, rfl⟩ := αSoa_inv h
  rfl

def αRData (type : BitVec 16) (rdata : ByteArray) : Option VeriDNS.Spec.Net.RData :=
  match type.toNat with
  | 1 => (αIPv4 rdata).map .a
  | 2 => (αName rdata).map .ns
  | 5 => (αName rdata).map .cname
  | 6 => αSoa rdata
  | 12 => (αName rdata).map .ptr
  | _ => (αType type).map (fun t => .generic t rdata)

theorem αRData_six (rdata : ByteArray) : αRData (6 : BitVec 16) rdata = αSoa rdata := rfl

def αRR (rr : VeriDNS.Spec.ResourceRecord) : Option VeriDNS.Spec.Net.RR :=
  match αName rr.name, αRData rr.type rr.rdata, αClass rr.class with
  | some owner, some rdata, some cls =>
    some { owner := owner, ttl := rr.ttl.toNat, rdata := rdata, cls := cls }
  | _, _, _ => none

theorem αRData_rtype (type : BitVec 16) (rdata : ByteArray) (rd : VeriDNS.Spec.Net.RData)
    (h : αRData type rdata = some rd) : αType type = some rd.rtype := by
  unfold αRData at h
  split at h <;> rename_i heq <;>
    first
    | (rw [Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h
       unfold αType; rw [heq]; rfl)
    | (unfold αType; simp only [heq]; rw [αSoa_rtype h])
    | (rw [Option.map_eq_some_iff] at h; obtain ⟨t, hαt, rfl⟩ := h; exact hαt)

theorem αRR_rtype (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : αRR rr = some r) : αType rr.type = some r.rdata.rtype := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    rw [← Option.some.inj h]
    exact αRData_rtype rr.type rr.rdata rdata hrd
  · exact absurd h (by simp)

theorem αRR_fields (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : αRR rr = some r) :
    αName rr.name = some r.owner ∧ r.ttl = rr.ttl.toNat ∧ αClass rr.class = some r.cls := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    obtain rfl := Option.some.inj h
    exact ⟨hn, rfl, hcl⟩
  · exact absurd h (by simp)

theorem αRR_rdata (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : αRR rr = some r) : αRData rr.type rr.rdata = some r.rdata := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    obtain rfl := Option.some.inj h
    exact hrd
  · exact absurd h (by simp)

theorem αRData_ns_inv {rdata : ByteArray} {rd : VeriDNS.Spec.Net.RData}
    (h : αRData (BitVec.ofNat 16 2) rdata = some rd) :
    ∃ host, αName rdata = some host ∧ rd = VeriDNS.Spec.Net.RData.ns host := by
  have h2 : (αName rdata).map VeriDNS.Spec.Net.RData.ns = some rd := h
  rw [Option.map_eq_some_iff] at h2
  obtain ⟨host, hh, hrd⟩ := h2
  exact ⟨host, hh, hrd.symm⟩

theorem αRData_a_inv {rdata : ByteArray} {rd : VeriDNS.Spec.Net.RData}
    (h : αRData (BitVec.ofNat 16 1) rdata = some rd) :
    ∃ ip, αIPv4 rdata = some ip ∧ rd = VeriDNS.Spec.Net.RData.a ip := by
  have h1 : (αIPv4 rdata).map VeriDNS.Spec.Net.RData.a = some rd := h
  rw [Option.map_eq_some_iff] at h1
  obtain ⟨ip, hh, hrd⟩ := h1
  exact ⟨ip, hh, hrd.symm⟩

theorem bailiwickRaws_owner_model (bw : ByteArray) (raws : Array ByteArray) {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR} {bwN : VeriDNS.Spec.Net.Name}
    (hb : b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws).toList)
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hαr : αRR rr = some r) (hbwN : αName bw = some bwN) :
    VeriDNS.Spec.Net.isAncestor bwN r.owner = true := by
  have him : Resolver.isAncestorB bw (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr)
      = true := Resolver.bailiwickRaws_owner_inBailiwick bw raws hb hpr
  have hname : αName rr.name = some r.owner := (αRR_fields rr r hαr).1
  have hrn : VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr = rr.name := rfl
  rw [hrn] at him
  exact isAncestorB_isAncestor bw rr.name bwN r.owner hbwN hname him

theorem mem_bailiwickRaws (bw : ByteArray) (raws : Array ByteArray) {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord}
    (hb : b ∈ raws.toList) (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hbail : Resolver.isAncestorB bw (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr)
        = true) :
    b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws).toList := by
  have hb' : b ∈ raws := Array.mem_def.mpr hb
  have hmem : b ∈ Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws := by
    unfold Resolver.bailiwickRaws
    rw [Array.mem_filter]
    exact ⟨hb', by simp only [hpr]; exact hbail⟩
  exact Array.mem_def.mp hmem

def αSection (rrs : Array ByteArray) : List VeriDNS.Spec.Net.RR :=
  rrs.toList.filterMap fun b =>
    match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | some rr => αRR rr
    | none => none

theorem mem_αSection_bailiwickRaws {bw : ByteArray} {section_ : Array ByteArray}
    {r : VeriDNS.Spec.Net.RR} {bwN : VeriDNS.Spec.Net.Name} (hbwN : αName bw = some bwN)
    (hr : r ∈ αSection (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw section_)) :
    r ∈ αSection section_ ∧ VeriDNS.Spec.Net.isAncestor bwN r.owner = true := by
  unfold αSection at hr ⊢
  rw [List.mem_filterMap] at hr ⊢
  obtain ⟨b, hb, hg⟩ := hr
  have hbsec : b ∈ section_.toList :=
    Resolver.bailiwickRaws_subset (RR := VeriDNS.Spec.ResourceRecord) bw section_ hb
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hg; simp at hg
  | some rr =>
    rw [hpr] at hg
    exact ⟨⟨b, hbsec, by rw [hpr]; exact hg⟩, bailiwickRaws_owner_model bw section_ hb hpr hg hbwN⟩

theorem isAncestorB_eq (bw owner : ByteArray) (bwN ownerN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (hown : αName owner = some ownerN) :
    Resolver.isAncestorB bw owner = VeriDNS.Spec.Net.isAncestor bwN ownerN := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h; exact isAncestorB_isAncestor bw owner bwN ownerN hbw hown h
  · intro h; exact isAncestor_isAncestorB bw owner bwN ownerN hbw hown h

theorem filter_filterMap_comm {α β : Type} (l : List α) (p : α → Bool)
    (g : α → Option β) (q : β → Bool)
    (h : ∀ a b, g a = some b → p a = q b) :
    (l.filter p).filterMap g = (l.filterMap g).filter q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hg : g a with
    | none =>
      cases hp : p a with
      | true => simp [hp, hg, ih]
      | false => simp [hp, hg, ih]
    | some b =>
      have hpq := h a b hg
      cases hp : p a with
      | true =>
        have hq : q b = true := by rw [← hpq]; exact hp
        simp [hp, hg, hq, ih]
      | false =>
        have hq : q b = false := by rw [hp] at hpq; exact hpq.symm
        simp [hp, hg, hq, ih]

theorem αSection_bailiwickRaws_eq (bw : ByteArray) (bwN : VeriDNS.Spec.Net.Name)
    (section_ : Array ByteArray) (hbw : αName bw = some bwN) :
    αSection (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw section_)
      = (αSection section_).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner) := by
  unfold αSection Resolver.bailiwickRaws
  rw [Array.toList_filter]
  apply filter_filterMap_comm
  intro b r hg
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hg; simp at hg
  | some rr =>
    rw [hpr] at hg
    obtain ⟨hn, _, _⟩ := αRR_fields rr r hg
    show Resolver.isAncestorB bw (VeriDNS.Spec.RRParse.rrName rr)
      = VeriDNS.Spec.Net.isAncestor bwN r.owner
    exact isAncestorB_eq bw rr.name bwN r.owner hbw hn

def αResp (f : VeriDNS.Spec.Format) : VeriDNS.Spec.Net.Response :=
  { aa := f.header.aa == 1
    rcode := αRCode f.header.rcode
    answer := αSection f.answer
    authority := αSection f.authority
    additional := αSection f.additional
    ra := f.header.ra == 1
    tc := f.header.tc == 1 }

theorem αResp_components (f : VeriDNS.Spec.Format) :
    (αResp f).rcode = αRCode f.header.rcode
      ∧ (αResp f).answer = αSection f.answer
      ∧ (αResp f).authority = αSection f.authority
      ∧ (αResp f).additional = αSection f.additional
      ∧ (αResp f).aa = (f.header.aa == 1)
      ∧ (αResp f).tc = (f.header.tc == 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def αQuery (f : VeriDNS.Spec.Format) : Option VeriDNS.Spec.Net.Query :=
  match f.question[0]? with
  | none => none
  | some qu =>
    match αName qu.qname, αQType qu.qtype, αClass qu.qclass with
    | some n, some qt, some qc =>
      some { qname := n, qtype := qt, qclass := qc, rd := f.header.rd == 1 }
    | _, _, _ => none

theorem αQuery_fields {f : VeriDNS.Spec.Format} {q : VeriDNS.Spec.Net.Query}
    (h : αQuery f = some q) :
    ∃ qu, f.question[0]? = some qu ∧ αName qu.qname = some q.qname
      ∧ αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by
  unfold αQuery at h
  split at h
  · exact absurd h (by simp)
  · rename_i qu hqu
    split at h
    · rename_i n qt qc hn hqt hqc
      injection h with h; subst h
      exact ⟨qu, hqu, hn, hqt, hqc⟩
    · exact absurd h (by simp)

theorem αQuery_buildSubQuery
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {q : VeriDNS.Spec.Net.Query} {sub : VeriDNS.Spec.Format} {revealed : Nat}
    (hbuild : Resolver.buildSubQuery state revealed = some sub)
    (hfull : Resolver.probeRoundB state.resources.sname revealed = false)
    (hsname : αName state.resources.sname = some q.qname)
    (hqt : ∀ qu : VeriDNS.Spec.Question,
        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
        αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass)
    (hrd : q.rd = false) :
    αQuery sub = some q := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i q₀ hlq
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu hqu
      injection hbuild with hb
      subst hb
      obtain ⟨hqt', hqc'⟩ := hqt qu ⟨q₀, hlq, hqu⟩
      have hsq : Resolver.subQuestion state.resources.sname revealed qu
          = { qname := state.resources.sname, qtype := qu.qtype, qclass := qu.qclass } := by
        unfold Resolver.subQuestion
        rw [hfull]
        rfl
      unfold αQuery
      rw [show (#[Resolver.subQuestion state.resources.sname revealed qu]
          : Array VeriDNS.Spec.Question)[0]? = some
          (Resolver.subQuestion state.resources.sname revealed qu) from rfl, hsq]
      dsimp only
      rw [hsname, hqt', hqc']
      dsimp only
      cases q; simp_all

def byteAddrToModel (ab : ByteArray) : String :=
  s!"{ab.get! 0 |>.toNat}.{ab.get! 1 |>.toNat}.{ab.get! 2 |>.toNat}.{ab.get! 3 |>.toNat}"

theorem byteAddrToModel_ipv4ToAddr (ip : BitVec 32) (port : UInt16) :
    byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr ip port)
      = (VeriDNS.Spec.Net.IPv4.toDotted
          ⟨(ip >>> 24).toNat.toUInt8, ((ip >>> 16) &&& 0xFF).toNat.toUInt8,
           ((ip >>> 8) &&& 0xFF).toNat.toUInt8, (ip &&& 0xFF).toNat.toUInt8⟩) :=
  rfl

theorem toNat_toUInt8_toBitVec (x : BitVec 32) : (x.toNat.toUInt8).toBitVec = x.setWidth 8 :=
  UInt8.toBitVec_ofBitVec (BitVec.ofNat 8 x.toNat)

theorem getLsbD_0xFF_32 (i : Nat) : (0xFF : BitVec 32).getLsbD i = decide (i < 8) := by
  rw [show (0xFF : BitVec 32) = BitVec.ofNat 32 (2^8 - 1) from rfl,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp [h, (by omega : i < 32)]
  · simp only [decide_eq_false (show ¬ i < 8 from by omega), Bool.and_false]

theorem ipv4_unpack (b0 b1 b2 b3 : UInt8) (packed : BitVec 32)
    (hp : packed = BitVec.setWidth 32 b0.toBitVec <<< 24 ||| BitVec.setWidth 32 b1.toBitVec <<< 16 |||
        BitVec.setWidth 32 b2.toBitVec <<< 8 ||| BitVec.setWidth 32 b3.toBitVec) :
    (BitVec.setWidth 8 (packed >>> 24) = b0.toBitVec)
      ∧ (BitVec.setWidth 8 ((packed >>> 16) &&& 0xFF) = b1.toBitVec)
      ∧ (BitVec.setWidth 8 ((packed >>> 8) &&& 0xFF) = b2.toBitVec)
      ∧ (BitVec.setWidth 8 (packed &&& 0xFF) = b3.toBitVec) := by
  subst hp
  have z1 : ∀ k, 8 ≤ k → b1.toBitVec.getLsbD k = false := fun k h => BitVec.getLsbD_of_ge _ _ h
  have z2 : ∀ k, 8 ≤ k → b2.toBitVec.getLsbD k = false := fun k h => BitVec.getLsbD_of_ge _ _ h
  have z3 : ∀ k, 8 ≤ k → b3.toBitVec.getLsbD k = false := fun k h => BitVec.getLsbD_of_ge _ _ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    rw [show 24 + i - 24 = i from by omega, z1 (24+i-16) (by omega), z2 (24+i-8) (by omega), z3 (24+i) (by omega)]
    simp [hi, decide_eq_false (show ¬ 24+i < 24 from by omega), decide_eq_false (show ¬ 24+i < 16 from by omega),
      decide_eq_false (show ¬ 24+i < 8 from by omega), (show 24+i < 32 from by omega), (show i < 32 from by omega)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_and, getLsbD_0xFF_32]
    rw [show 16 + i - 16 = i from by omega, z2 (16+i-8) (by omega), z3 (16+i) (by omega)]
    simp [hi, decide_eq_false (show ¬ 16+i < 16 from by omega), (show 16+i < 24 from by omega),
      (show 16+i < 32 from by omega), (show i < 32 from by omega), (show i < 8 from hi)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_and, getLsbD_0xFF_32]
    rw [show 8 + i - 8 = i from by omega, z3 (8+i) (by omega)]
    simp [hi, decide_eq_false (show ¬ 8+i < 8 from by omega), (show 8+i < 16 from by omega),
      (show 8+i < 24 from by omega), (show 8+i < 32 from by omega), (show i < 32 from by omega), (show i < 8 from hi)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_and, getLsbD_0xFF_32]
    simp [hi, (show i < 8 from hi), (show i < 16 from by omega), (show i < 24 from by omega), (show i < 32 from by omega)]

theorem ipv4_pack_unpack (b0 b1 b2 b3 : UInt8) :
    ((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) >>> 24).toNat.toUInt8 = b0)
      ∧ (((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) >>> 16) &&& 0xFF).toNat.toUInt8 = b1)
      ∧ (((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) >>> 8) &&& 0xFF).toNat.toUInt8 = b2)
      ∧ ((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) &&& 0xFF).toNat.toUInt8 = b3) := by
  have h := ipv4_unpack b0 b1 b2 b3 _ rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.1
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.2.1
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.2.2.1
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.2.2.2

theorem matchCount_setUpAddresses (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    VeriDNS.Spec.SlistFromNameSpec.matchCount (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
      (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) names glue mc) = mc :=
  rfl

theorem searchFails_fromNsWithGlueAll (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc).servers.isEmpty = names.isEmpty := by
  unfold VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll
  rw [Bool.eq_iff_iff, Array.isEmpty_iff, Array.isEmpty_iff, Array.flatMap_eq_empty_iff]
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Array.exists_mem_of_ne_empty names hne
    have hgx := h x hx
    by_cases he : (glue.filterMap (fun gp =>
        if DomainName.foldNameCase gp.1 == DomainName.foldNameCase x then some gp.2 else none)).isEmpty = true
    · rw [if_pos he] at hgx; simp at hgx
    · rw [if_neg he, Array.map_eq_empty_iff] at hgx
      exact he (by rw [Array.isEmpty_iff]; exact hgx)
  · rintro rfl
    intro x hx
    exact absurd hx (by simp)

theorem searchFails_setUpAddresses (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    VeriDNS.Spec.SlistFromNameSpec.searchFails (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
      (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) names glue mc)
      = names.isEmpty :=
  searchFails_fromNsWithGlueAll names glue mc

theorem currentCloser_false_of_ge (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc walkMc : Nat)
    (hne : names.isEmpty = false) (hge : mc ≤ walkMc) :
    (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry) names glue mc)
      && decide (walkMc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := VeriDNS.Impl.SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList)
            (NS := VeriDNS.Spec.SlistEntry) names glue mc))) = false := by
  rw [searchFails_setUpAddresses, matchCount_setUpAddresses, hne]
  simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt]
  exact hge

theorem walkNs_base {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (name : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (fuel : Nat)
    (h : (VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now : Array RR).isEmpty = false) :
    Resolver.stepFindServers.walkNs (RR := RR) name cache nsType inClass now (fuel + 1)
      = some ((VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now).filterMap (fun (rr : RR) =>
          if VeriDNS.Spec.RRParse.rrType (RR := RR) rr == nsType
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr) else none),
        (match DomainName.wireFormatToLabels name with | .ok labels => labels.size | .error _ => 0)) := by
  unfold Resolver.stepFindServers.walkNs
  simp only [h, Bool.false_eq_true, if_false]
  rfl

theorem walkNs_step {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (name : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (fuel : Nat)
    (parent : ByteArray)
    (h : (VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now : Array RR).isEmpty = true)
    (hp : DomainName.parentDomainWire name = some parent) :
    Resolver.stepFindServers.walkNs (RR := RR) name cache nsType inClass now (fuel + 1)
      = Resolver.stepFindServers.walkNs (RR := RR) parent cache nsType inClass now fuel := by
  rw [Resolver.stepFindServers.walkNs]
  simp only [h, if_true, hp]

theorem walkNs_one_hop {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (name parent : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (fuel : Nat)
    (h1 : (VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now : Array RR).isEmpty = true)
    (hp : DomainName.parentDomainWire name = some parent)
    (h2 : (VeriDNS.Spec.CacheSpec.lookupTopCred cache parent nsType inClass now : Array RR).isEmpty = false) :
    Resolver.stepFindServers.walkNs (RR := RR) name cache nsType inClass now (fuel + 2)
      = some ((VeriDNS.Spec.CacheSpec.lookupTopCred cache parent nsType inClass now).filterMap (fun (rr : RR) =>
          if VeriDNS.Spec.RRParse.rrType (RR := RR) rr == nsType
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr) else none),
        (match DomainName.wireFormatToLabels parent with | .ok labels => labels.size | .error _ => 0)) := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl,
     walkNs_step name cache nsType inClass now (fuel + 1) parent h1 hp]
  exact walkNs_base parent cache nsType inClass now fuel h2

theorem walkNs_ascend {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (zone : ByteArray)
    (h2 : (VeriDNS.Spec.CacheSpec.lookupTopCred cache zone nsType inClass now : Array RR).isEmpty = false) :
    ∀ (inter : List ByteArray) (start : ByteArray) (fuel : Nat),
      inter.length + 2 ≤ fuel →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start (inter ++ [zone]) →
      (∀ m ∈ start :: inter,
        (VeriDNS.Spec.CacheSpec.lookupTopCred cache m nsType inClass now : Array RR).isEmpty = true) →
      Resolver.stepFindServers.walkNs (RR := RR) start cache nsType inClass now fuel
        = Resolver.stepFindServers.walkNs (RR := RR) zone cache nsType inClass now 1 := by
  intro inter
  induction inter with
  | nil =>
    intro start fuel hf hchain hempty
    obtain ⟨hps, _⟩ := List.chain_cons.mp hchain
    have hes := hempty start (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    rw [show f + 2 = (f + 1) + 1 from rfl,
       walkNs_step start cache nsType inClass now (f + 1) zone hes hps,
       walkNs_base zone cache nsType inClass now f h2,
       walkNs_base zone cache nsType inClass now 0 h2]
  | cons m rest ih =>
    intro start fuel hf hchain hempty
    obtain ⟨hps, hchain'⟩ := List.chain_cons.mp hchain
    have hes := hempty start (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [walkNs_step start cache nsType inClass now f m hes hps]
    exact ih m f (by simpa using hf) hchain' (fun x hx => hempty x (List.mem_cons_of_mem start hx))

theorem walkNs_some_inversion {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (cache : C) (nsType inClass : BitVec 16) (now : UInt32) :
    ∀ (fuel : Nat) (sname : ByteArray) (nsNames : Array ByteArray) (mc : Nat),
      Resolver.stepFindServers.walkNs (RR := RR) sname cache nsType inClass now fuel = some (nsNames, mc) →
      (VeriDNS.Spec.CacheSpec.lookupTopCred cache sname nsType inClass now : Array RR).isEmpty = false
      ∨ ∃ cut inter, List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut])
          ∧ (∀ m ∈ sname :: inter,
              (VeriDNS.Spec.CacheSpec.lookupTopCred cache m nsType inClass now : Array RR).isEmpty = true)
          ∧ (VeriDNS.Spec.CacheSpec.lookupTopCred cache cut nsType inClass now : Array RR).isEmpty = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname nsNames mc h
    rw [Resolver.stepFindServers.walkNs] at h
    exact absurd h (by simp)
  | succ f ih =>
    intro sname nsNames mc h
    by_cases he : (VeriDNS.Spec.CacheSpec.lookupTopCred cache sname nsType inClass now : Array RR).isEmpty = true
    · right
      cases hp : DomainName.parentDomainWire sname with
      | none =>
        rw [Resolver.stepFindServers.walkNs] at h
        simp only [he, if_true, hp] at h
        exact absurd h (by simp)
      | some parent =>
        rw [walkNs_step sname cache nsType inClass now f parent he hp] at h
        rcases ih parent nsNames mc h with hbase | ⟨cut, inter, hchain, hempty, hcut_ne⟩
        · exact ⟨parent, [], List.Chain.cons hp List.Chain.nil,
            fun m hm => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; exact he, hbase⟩
        · refine ⟨cut, parent :: inter, ?_, ?_, hcut_ne⟩
          · rw [List.cons_append]; exact List.Chain.cons hp hchain
          · intro m hm
            rcases List.mem_cons.mp hm with rfl | hm'
            · exact he
            · exact hempty m hm'
    · left; simpa using he

theorem lookup_nameEqCI_congr (c : Cache.DnsCache) (m n : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (h : nameEqCI m n = true) :
    c.lookup m qt qc now = c.lookup n qt qc now := by
  have hfold : DomainName.foldNameCase m = DomainName.foldNameCase n := by
    have h'' : ByteArray.beq (DomainName.foldNameCase m) (DomainName.foldNameCase n) = true := h
    unfold ByteArray.beq at h''
    exact ByteArray.ext (eq_of_beq h'')
  unfold Cache.DnsCache.lookup
  congr 1
  funext e
  have hle : Cache.liveEntry e m qt qc now = Cache.liveEntry e n qt qc now := by
    unfold Cache.liveEntry nameEqCI; rw [hfold]
  rw [hle]

theorem mem_lookup_of_live (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hlive : Cache.liveEntry e name qtype qclass now = true) :
    ({ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } : VeriDNS.Spec.ResourceRecord)
      ∈ c.lookup name qtype qclass now := by
  unfold Cache.DnsCache.lookup
  rw [Array.mem_filterMap]
  exact ⟨e, he, by simp only [hlive, if_true]⟩

theorem mem_records_of_mem_lookup (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (r : VeriDNS.Spec.ResourceRecord) (hr : r ∈ c.lookup name qtype qclass now) :
    ∃ e ∈ c.records, Cache.liveEntry e name qtype qclass now = true
      ∧ r = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold Cache.DnsCache.lookup at hr
  rw [Array.mem_filterMap] at hr
  obtain ⟨e, he, hmap⟩ := hr
  split at hmap
  · next hl => exact ⟨e, he, hl, (Option.some.inj hmap).symm⟩
  · simp at hmap

theorem mem_walkNs_nsNames_of_live (c : Cache.DnsCache) (name : ByteArray) (nsType inClass : BitVec 16)
    (now : UInt32) (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hlive : Cache.liveEntry e name nsType inClass now = true) :
    e.rr.rdata ∈ (c.lookup name nsType inClass now).filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == nsType
        then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) := by
  have htype : (e.rr.type == nsType) = true := by
    have h := hlive; simp only [Cache.liveEntry, Bool.and_eq_true] at h; exact h.1.1.2
  rw [Array.mem_filterMap]
  refine ⟨{ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat },
    mem_lookup_of_live c name nsType inClass now e he hlive, ?_⟩
  simp only [VeriDNS.Spec.RRParse.rrType, VeriDNS.Spec.RRParse.rrRdata, htype, if_true]

theorem nsName_mem_extractNsNames_of_rederived (c : Cache.DnsCache) (cut : ByteArray)
    (authority : Array ByteArray) (cred : Trustworthiness) (now : UInt32) (nm : ByteArray)
    (hmiss : ∀ e ∈ c.records,
      Cache.liveEntry e cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now = false)
    (hmem : nm ∈ ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut authority) cred now).lookup
        cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)) :
    nm ∈ Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) authority := by
  rw [Array.mem_filterMap] at hmem
  obtain ⟨r, hrlook, hrf⟩ := hmem
  obtain ⟨e, he, hlive, hre⟩ :=
    mem_records_of_mem_lookup _ cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now r hrlook
  rw [hre] at hrf
  simp only [VeriDNS.Spec.RRParse.rrType, VeriDNS.Spec.RRParse.rrRdata] at hrf
  split at hrf
  · next htype =>
    obtain rfl : e.rr.rdata = nm := Option.some.inj hrf
    rcases mem_cacheRRs_records _ cred now c he with hcmem | ⟨b, hb, hpb⟩
    · simp [hmiss e hcmem] at hlive
    · have hbauth : b ∈ authority.toList :=
        Resolver.bailiwickRaws_subset (RR := VeriDNS.Spec.ResourceRecord) cut authority hb
      unfold Resolver.extractNsNames
      rw [Array.mem_filterMap]
      refine ⟨b, Array.mem_def.mpr hbauth, ?_⟩
      simp only [hpb, VeriDNS.Spec.RRParse.rrType, VeriDNS.Spec.RRParse.rrRdata, htype, if_true]
  · exact absurd hrf (by simp)

theorem lookup_nonempty_of_mem (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hlive : Cache.liveEntry e name qtype qclass now = true) :
    (c.lookup name qtype qclass now).isEmpty = false := by
  have hmem := mem_lookup_of_live c name qtype qclass now e he hlive
  by_contra h
  rw [Bool.not_eq_false, Array.isEmpty_iff] at h
  rw [h] at hmem
  simp at hmem

theorem lookup_nonempty_after_cacheRRs (c : Cache.DnsCache) (pre post : Array ByteArray)
    (nsRaw : ByteArray) (nsRR : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsRR)
    (hnz : (nsRR.ttl == 0) = false)
    (hbetter : ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c pre cred now).records.any
      fun e => DomainName.nameEqCI e.rr.name nsRR.name && e.rr.type == nsRR.type && e.rr.class == nsRR.class
        && (e.expiry > now || e.expiry == now + nsRR.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false)
    (hfresh : Cache.CacheEntry.fresh ⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred, now⟩ now = true)
    (hpost : ∀ b ∈ post, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (DomainName.nameEqCI nsRR.name rr.name && nsRR.type == rr.type && nsRR.class == rr.class
        && (now + nsRR.ttl.toNat.toUInt32 != now + rr.ttl.toNat.toUInt32 || nsRR.rdata == rr.rdata)) = false) :
    ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (pre ++ #[nsRaw] ++ post) cred now).lookup nsRR.name nsRR.type nsRR.class now).isEmpty = false := by
  obtain ⟨e, hmem, hlive⟩ :=
    mem_cacheRRs_live_of_split c pre post nsRaw nsRR cred now hp hnz hbetter hfresh hpost
  exact lookup_nonempty_of_mem _ nsRR.name nsRR.type nsRR.class now e hmem hlive

theorem lookup_empty_of_no_mem (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (hno : ∀ e ∈ c.records, Cache.liveEntry e name qtype qclass now = false) :
    (c.lookup name qtype qclass now).isEmpty = true := by
  rw [Array.isEmpty_iff]
  unfold Cache.DnsCache.lookup
  rw [Array.filterMap_eq_empty_iff]
  intro e he
  simp only [hno e he, Bool.false_eq_true, if_false]

theorem lookup_empty_after_cacheRRs (c : Cache.DnsCache) (cut : ByteArray) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) (m : ByteArray) (qtype qclass : BitVec 16)
    (hc : ∀ e ∈ c.records, Cache.liveEntry e m qtype qclass now = false)
    (hbwlive : ∀ e, Resolver.isAncestorB cut e.rr.name = true → Cache.liveEntry e m qtype qclass now = false) :
    ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut raws) cred now).lookup
        m qtype qclass now).isEmpty = true := by
  apply lookup_empty_of_no_mem
  intro e he
  rcases cacheRRs_bailiwick_owner c cut raws cred now he with hcmem | hbw
  · exact hc e hcmem
  · exact hbwlive e hbw

theorem store_self_live (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : Trustworthiness)
    (hfresh : Cache.CacheEntry.fresh ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ now = true) :
    ∃ e ∈ (c.store rr now cred).records, Cache.liveEntry e rr.name rr.type rr.class now = true := by
  refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩, ?_, ?_⟩
  · unfold Cache.DnsCache.store
    exact Array.mem_push.mpr (Or.inr rfl)
  · simp only [Cache.liveEntry, VeriDNS.Proof.NameTree.nameEqCI_refl, beq_self_eq_true, hfresh,
      Bool.and_self]

theorem storeChecked_self_live (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : Trustworthiness)
    (hnz : (rr.ttl == 0) = false)
    (hbetter : (c.records.any fun e =>
      DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false)
    (hfresh : Cache.CacheEntry.fresh ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ now = true) :
    ∃ e ∈ (c.storeChecked rr cred now).records, Cache.liveEntry e rr.name rr.type rr.class now = true := by
  simp only [Cache.DnsCache.storeChecked, hnz, Bool.false_eq_true, if_false, hbetter]
  exact store_self_live c rr now cred hfresh

theorem extractGlue_addr_αIPv4 (rd : ByteArray) (a : VeriDNS.Spec.Net.IPv4) (ha : αIPv4 rd = some a) :
    byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr
      ((rd.data[0]!.toBitVec.setWidth 32 <<< 24) ||| (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
       (rd.data[2]!.toBitVec.setWidth 32 <<< 8) ||| rd.data[3]!.toBitVec.setWidth 32))
      = a.toDotted := by
  rw [byteAddrToModel_ipv4ToAddr]
  obtain ⟨h0, h1, h2, h3⟩ := ipv4_pack_unpack rd.data[0]! rd.data[1]! rd.data[2]! rd.data[3]!
  rw [h0, h1, h2, h3]
  unfold αIPv4 at ha
  split at ha
  · rw [← Option.some.inj ha]
  · exact absurd ha (by simp)

theorem a_extract_reconcile (rd : ByteArray) :
    (αIPv4 rd).map (fun ip => ip.toDotted)
      = if rd.size == 4 then some (byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr
          ((rd.data[0]!.toBitVec.setWidth 32 <<< 24) ||| (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
           (rd.data[2]!.toBitVec.setWidth 32 <<< 8) ||| rd.data[3]!.toBitVec.setWidth 32))) else none := by
  cases ha : αIPv4 rd with
  | some a =>
    have hsz : (rd.size == 4) = true := by
      by_contra hc
      unfold αIPv4 at ha
      rw [if_neg (fun h => hc (by simp [h]))] at ha
      exact absurd ha (by simp)
    rw [if_pos hsz, Option.map_some, extractGlue_addr_αIPv4 rd a ha]
  | none =>
    have hsz : (rd.size == 4) = false := by
      by_contra hc
      simp only [Bool.not_eq_false, beq_iff_eq] at hc
      unfold αIPv4 at ha
      rw [if_pos hc] at ha
      exact absurd ha (by simp)
    rw [if_neg (by simp [hsz]), Option.map_none]

def modelSlistOf (s : VeriDNS.Impl.SList.DnsSList) : List String :=
  s.servers.toList.filterMap (fun e =>
    e.address.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))

theorem modelSlistOf_fromNsWithGlue (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)
      = names.toList.filterMap (fun n =>
          (glue.findSome? (fun (gn, ga) =>
              if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none)).map
            (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.fromNsWithGlue
  rw [Array.toList_map, List.filterMap_map]
  rfl

theorem mem_modelSlistOf_fromNsWithGlue (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) (s : String) :
    s ∈ modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc) ↔
    ∃ n ∈ names.toList, ∃ a, glue.findSome? (fun (gn, ga) =>
        if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none) = some a
      ∧ s = byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a) := by
  rw [modelSlistOf_fromNsWithGlue, List.mem_filterMap]
  constructor
  · rintro ⟨n, hn, hmap⟩
    rw [Option.map_eq_some_iff] at hmap
    obtain ⟨a, ha, hs⟩ := hmap
    exact ⟨n, hn, a, ha, hs.symm⟩
  · rintro ⟨n, hn, a, ha, hs⟩
    exact ⟨n, hn, by rw [ha, Option.map_some, hs]⟩

theorem filterMap_filter_of_none {α β : Type} (p : α → Bool) (f : α → Option β) (l : List α)
    (h : ∀ x ∈ l, p x = false → f x = none) :
    l.filterMap f = (l.filter p).filterMap f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun x hx hpx => h x (List.mem_cons_of_mem a hx) hpx)
    cases hpa : p a with
    | true => rw [List.filter_cons_of_pos hpa, List.filterMap_cons, List.filterMap_cons, ih']
    | false =>
      rw [List.filter_cons_of_neg (by simp [hpa]), List.filterMap_cons,
          h a (List.mem_cons_self ..) hpa, ih']

theorem modelSlistOf_perm_of_names_perm {names names' : Array ByteArray}
    (glue : Array (ByteArray × BitVec 32)) (mc mc' : Nat)
    (h : names.toList.Perm names'.toList) :
    (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)).Perm
      (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names' glue mc')) := by
  rw [modelSlistOf_fromNsWithGlue, modelSlistOf_fromNsWithGlue]
  exact h.filterMap _

theorem modelSlistOf_filter_inBailiwick (cut : ByteArray) (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (hglue : ∀ gp ∈ glue, Resolver.isAncestorB cut gp.1 = true) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)
      = modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue
          (names.filter (fun n => Resolver.isAncestorB cut n)) glue mc) := by
  rw [modelSlistOf_fromNsWithGlue, modelSlistOf_fromNsWithGlue, Array.toList_filter]
  apply filterMap_filter_of_none
  intro n _ hp
  rw [glue_findSome_none_of_out_of_bailiwick cut n glue hp hglue, Option.map_none]

theorem modelSlistOf_markQueried (s : VeriDNS.Impl.SList.DnsSList) (nm : ByteArray) :
    modelSlistOf (s.markQueried nm) = modelSlistOf s := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.markQueried
  rw [Array.toList_map, List.filterMap_map]
  congr 1
  funext e
  dsimp only [Function.comp]
  split <;> rfl

theorem filterMap_partition_perm {α β : Type} (l : List α) (p : α → Bool) (f : α → Option β) :
    (l.filterMap f).Perm ((l.filter p).filterMap f ++ (l.filter (fun x => !p x)).filterMap f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons]
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hp]), List.filterMap_cons]
      cases f a with
      | none => exact ih
      | some b => exact ih.cons b
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos (by simp [hp]),
        List.filterMap_cons]
      cases f a with
      | none => exact ih
      | some b => exact (ih.cons b).trans List.perm_middle.symm

theorem modelSlistOf_removeServer_sublist (s : VeriDNS.Impl.SList.DnsSList) (name : ByteArray) :
    List.Sublist (modelSlistOf (s.removeServer name)) (modelSlistOf s) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.removeServer
  have hsub : List.Sublist (s.servers.filter (fun e => e.name != name)).toList s.servers.toList := by
    rw [Array.toList_filter]; exact List.filter_sublist
  exact hsub.filterMap _

theorem modelSlistOf_removeServer_perm (s : VeriDNS.Impl.SList.DnsSList) (name : ByteArray) :
    (modelSlistOf s).Perm
      ((s.servers.toList.filter (fun e => e.name == name)).filterMap
          (fun e => e.address.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))
        ++ modelSlistOf (s.removeServer name)) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.removeServer
  rw [Array.toList_filter]
  exact filterMap_partition_perm s.servers.toList (fun e => e.name == name) _

theorem pickBest_some {acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32)}
    {x e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32}
    (h : VeriDNS.Impl.SList.DnsSList.pickBest acc x = some (e, addr)) :
    (e = x ∧ x.address = some addr) ∨ acc = some (e, addr) := by
  unfold VeriDNS.Impl.SList.DnsSList.pickBest at h
  repeat' split at h
  all_goals simp_all [Option.some.injEq, Prod.mk.injEq]

theorem foldl_pickBest_some (l : List VeriDNS.Spec.SlistEntry)
    (acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32)) {e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32}
    (h : l.foldl VeriDNS.Impl.SList.DnsSList.pickBest acc = some (e, addr)) :
    acc = some (e, addr) ∨ (e ∈ l ∧ e.address = some addr) := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil] at h; exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · rcases pickBest_some h1 with ⟨rfl, ha⟩ | h2
      · exact Or.inr ⟨List.mem_cons_self, ha⟩
      · exact Or.inl h2
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩

theorem pickBest_eq_none {acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32)} {x : VeriDNS.Spec.SlistEntry}
    (h : VeriDNS.Impl.SList.DnsSList.pickBest acc x = none) : acc = none ∧ x.address = none := by
  unfold VeriDNS.Impl.SList.DnsSList.pickBest at h
  split at h
  · next heq => exact ⟨h, heq⟩
  · next addr heq =>
    repeat' split at h
    all_goals simp at h

theorem foldl_pickBest_eq_none (l : List VeriDNS.Spec.SlistEntry)
    (acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32))
    (h : l.foldl VeriDNS.Impl.SList.DnsSList.pickBest acc = none) :
    acc = none ∧ ∀ e ∈ l, e.address = none := by
  induction l generalizing acc with
  | nil => exact ⟨by simpa using h, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨hpb, hxs⟩ := ih _ h
    obtain ⟨hacc, hxaddr⟩ := pickBest_eq_none hpb
    refine ⟨hacc, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hxaddr
    · exact hxs e he'

theorem modelSlistOf_nil_of_bestWithAddress_none (s : VeriDNS.Impl.SList.DnsSList)
    (h : s.bestWithAddress = none) : modelSlistOf s = [] := by
  unfold VeriDNS.Impl.SList.DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  obtain ⟨-, haddr⟩ := foldl_pickBest_eq_none s.servers.toList none h
  unfold modelSlistOf
  rw [List.filterMap_eq_nil_iff]
  intro e he
  rw [haddr e he]; rfl

theorem bestWithAddress_mem_modelSlistOf (s : VeriDNS.Impl.SList.DnsSList)
    {e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32}
    (h : s.bestWithAddress = some (e, addr)) :
    byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr addr) ∈ modelSlistOf s := by
  unfold VeriDNS.Impl.SList.DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  rcases foldl_pickBest_some _ none h with h1 | ⟨hmem, haddr⟩
  · exact absurd h1 (by simp)
  · unfold modelSlistOf
    rw [List.mem_filterMap]
    exact ⟨e, hmem, by simp [haddr]⟩

theorem modelSlistOf_ne_nil_of_bestWithAddress_some (s : VeriDNS.Impl.SList.DnsSList)
    {e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32} (h : s.bestWithAddress = some (e, addr)) :
    modelSlistOf s ≠ [] :=
  List.ne_nil_of_mem (bestWithAddress_mem_modelSlistOf s h)

def αRRType (bytes : ByteArray) : Option RRType :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
  | some rr => αType (VeriDNS.Spec.RRParse.rrType rr)
  | none => none

theorem hasRRTypeIn_corr (rrs : Array ByteArray) (code : BitVec 16) (rt : RRType)
    (hc : αType code = some rt) :
    Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) rrs code = true
      ↔ ∃ b ∈ rrs, αRRType b = some rt := by
  unfold Resolver.hasRRTypeIn αRRType
  constructor
  · intro h
    obtain ⟨i, hi, hcond⟩ := Array.any_eq_true.mp h
    refine ⟨rrs[i], Array.getElem_mem hi, ?_⟩
    revert hcond
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rrs[i] with
    | none => intro hcond; exact absurd hcond (by simp)
    | some rr =>
      intro hcond
      have heq : VeriDNS.Spec.RRParse.rrType rr = code := by simpa using hcond
      simp only [heq, hc]
  · rintro ⟨b, hbmem, hcond⟩
    obtain ⟨i, hi, hib⟩ := Array.getElem_of_mem hbmem
    subst hib
    apply Array.any_eq_true.mpr
    refine ⟨i, hi, ?_⟩
    revert hcond
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rrs[i] with
    | none => intro hcond; exact absurd hcond (by simp)
    | some rr =>
      intro hcond
      have heq : VeriDNS.Spec.RRParse.rrType rr = code := αType_injective hcond hc
      simp [heq]

theorem answersQueryB_corr (resp : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qt : RRType)
    (hq : resp.question[0]? = some qu) (hqt : αType qu.qtype = some qt) :
    Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true
      ↔ ∃ b ∈ resp.answer, αRRType b = some qt := by
  unfold Resolver.answersQueryB
  rw [hq]
  exact hasRRTypeIn_corr resp.answer qu.qtype qt hqt

theorem delegationShapedB_authority_has_ns (resp : VeriDNS.Spec.Format)
    (h : Server.delegationShapedB resp = true) :
    ∃ b ∈ resp.authority, αRRType b = some RRType.ns := by
  unfold Server.delegationShapedB at h
  simp only [Bool.and_eq_true] at h
  exact (hasRRTypeIn_corr resp.authority 2 RRType.ns (by rfl)).mp h.1.1.1

open VeriDNS.Spec.Net (Time)

def αTime (t : UInt32) : Time := t.toNat

theorem fresh_corr (e : Cache.CacheEntry) (now : UInt32)
    (insertedAt ttl : Time) (h : e.expiry.toNat = insertedAt + ttl) :
    e.fresh now = Nat.blt (αTime now) (insertedAt + ttl) := by
  unfold Cache.CacheEntry.fresh αTime
  rw [← h, Bool.eq_iff_iff]
  simp [UInt32.lt_iff_toNat_lt, Nat.blt_eq]

theorem agedTtl_corr (e : Cache.CacheEntry) (now : UInt32)
    (insertedAt ttl : Nat) (hexp : e.expiry.toNat = insertedAt + ttl)
    (hfresh : e.fresh now = true) (hins : insertedAt ≤ now.toNat) :
    (e.expiry - now).toNat = ttl - (now.toNat - insertedAt) := by
  have hlt : now < e.expiry := by
    have hb := hfresh; unfold Cache.CacheEntry.fresh at hb; simpa using hb
  have hle : now ≤ e.expiry := UInt32.le_of_lt hlt
  rw [UInt32.toNat_sub_of_le e.expiry now hle, hexp]
  omega

def αCacheRR (e : Cache.CacheEntry) : Option VeriDNS.Spec.Net.CacheRR :=
  (αRR e.rr).map fun r =>
    { rr := r, insertedAt := e.expiry.toNat - e.rr.ttl.toNat, cred := αCred e.credibility }

theorem αCacheRR_rr {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR} (h : αCacheRR e = some ce) :
    αRR e.rr = some ce.rr := by
  unfold αCacheRR at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, hce⟩ := h
  rw [← hce]; exact hr

theorem αCacheRR_expiry {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR} (hα : αCacheRR e = some ce)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat) :
    ce.insertedAt + ce.rr.ttl = e.expiry.toNat := by
  have hrttl : ce.rr.ttl = e.rr.ttl.toNat := (αRR_fields e.rr ce.rr (αCacheRR_rr hα)).2.1
  unfold αCacheRR at hα
  rw [Option.map_eq_some_iff] at hα
  obtain ⟨r, hr, hceeq⟩ := hα
  have hins : ce.insertedAt = e.expiry.toNat - e.rr.ttl.toNat := by rw [← hceeq]
  rw [hins, hrttl, Nat.sub_add_cancel hle]

theorem αCacheRR_cred {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR} (h : αCacheRR e = some ce) :
    ce.cred = αCred e.credibility := by
  unfold αCacheRR at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, hce⟩ := h
  rw [← hce]

theorem αCacheRR_push (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (now : UInt32) (cred : VeriDNS.Spec.Trustworthiness)
    (hr : αRR rr = some r)
    (hno : (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩
      = some ⟨r, now.toNat, αCred cred⟩ := by
  unfold αCacheRR
  rw [hr, Option.map_some]
  congr 1
  rw [hno]
  simp

theorem cacheable_corr {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (h : αRR rr = some r) :
    VeriDNS.Spec.Net.cacheable r = !(rr.ttl == 0) := by
  have htt : r.ttl = rr.ttl.toNat := (αRR_fields rr r h).2.1
  have hz : (rr.ttl.toNat = 0) ↔ (rr.ttl = 0) := by
    constructor
    · intro hh; exact BitVec.toNat_inj.mp (by rw [hh]; rfl)
    · intro hh; rw [hh]; rfl
  unfold VeriDNS.Spec.Net.cacheable
  rw [htt]
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.blt_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, ← hz]
  omega

theorem flatMap_pushOf_filterMap (l : List ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    (l.flatMap (pushOf cred now)).filterMap αCacheRR
      = l.filterMap (fun b =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
          | some rr => if rr.ttl == 0 then none else αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩
          | none => none) := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih, List.filterMap_cons]
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [pushOf_none cred now hpr]; simp only [hpr, List.filterMap_nil, List.nil_append]
    | some rr =>
      by_cases htt : (rr.ttl == 0) = true
      · rw [pushOf_zero cred now hpr htt]
        simp only [hpr, htt, if_true, List.filterMap_nil, List.nil_append]
      · have htf : (rr.ttl == 0) = false := by simpa using htt
        rw [pushOf_pos cred now hpr htf]
        simp only [hpr, htf, Bool.false_eq_true, if_false]
        cases hac : αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ with
        | none => simp only [hac, List.filterMap_cons, List.filterMap_nil, List.nil_append]
        | some ce => simp only [hac, List.filterMap_cons, List.filterMap_nil, List.cons_append,
            List.nil_append]

theorem αCacheRR_fresh (e : Cache.CacheEntry) (r : VeriDNS.Spec.Net.CacheRR) (now : UInt32)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (h : αCacheRR e = some r) : e.fresh now = r.fresh now.toNat := by
  unfold αCacheRR at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r', hrr, rfl⟩ := h
  have hfields := αRR_fields e.rr r' hrr
  have hexp : e.expiry.toNat = (e.expiry.toNat - e.rr.ttl.toNat) + e.rr.ttl.toNat := by omega
  rw [fresh_corr e now (e.expiry.toNat - e.rr.ttl.toNat) e.rr.ttl.toNat hexp]
  simp only [αTime, VeriDNS.Spec.Net.CacheRR.fresh, hfields.2.1]

theorem αRR_setTtl (rr : VeriDNS.Spec.ResourceRecord) (X : BitVec 32) :
    αRR { rr with ttl := X }
      = (αRR rr).map (fun r => { r with ttl := X.toNat }) := by
  unfold αRR
  cases h : αName rr.name <;> cases h2 : αRData rr.type rr.rdata <;> cases h3 : αClass rr.class <;>
    simp [h, h2, h3]

theorem αRR_aged (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR) (now : UInt32)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat) (hfresh : e.fresh now = true)
    (hmono : e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (ha : αCacheRR e = some a) :
    αRR { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
      = some { a.rr with ttl := a.rr.ttl - (now.toNat - a.insertedAt) } := by
  unfold αCacheRR at ha
  rw [Option.map_eq_some_iff] at ha
  obtain ⟨r, hr, rfl⟩ := ha
  have hf := αRR_fields e.rr r hr
  have hins : e.expiry.toNat = (e.expiry.toNat - e.rr.ttl.toNat) + e.rr.ttl.toNat :=
    (Nat.sub_add_cancel hle).symm
  have haged := agedTtl_corr e now (e.expiry.toNat - e.rr.ttl.toNat) e.rr.ttl.toNat hins hfresh hmono
  have hb : (BitVec.ofNat 32 (e.expiry - now).toNat).toNat = (e.expiry - now).toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (UInt32.toNat_lt _)
  rw [αRR_setTtl, hr, Option.map_some, hb, haged, hf.2.1]

theorem answerableEntry_matching (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (hans : Cache.answerableEntry e name qt qc now = true)
    (ha : αCacheRR e = some a) :
    a.fresh (αTime now) = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true
      ∧ q.qtype.covers a.rr.rtype = true ∧ (a.rr.cls == q.qclass) = true
      ∧ a.cred.usable = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hcr : a.cred = αCred e.credibility := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; rfl
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.answerableEntry Cache.liveEntry at hans
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hans
  obtain ⟨⟨⟨⟨hnm, htype⟩, hcls⟩, hfr⟩, hcred⟩ := hans
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show αTime now = now.toNat from rfl, ← αCacheRR_fresh e a now hle ha]; exact hfr
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm hqn
    rw [hfields.1] at hna; injection hna with hna; subst hna; exact hne
  · have htypeq : e.rr.type = qt := eq_of_beq htype
    have hrtt0 : αType e.rr.type = some t := by rw [htypeq]; exact ht
    rw [hrt] at hrtt0
    have hrtt : a.rr.rdata.rtype = t := by injection hrtt0
    rw [hqq]
    show (VeriDNS.Spec.Net.QType.rr t).covers a.rr.rdata.rtype = true
    rw [hrtt]
    exact rrtype_beq_self t
  · have hclseq : e.rr.class = qc := eq_of_beq hcls
    have hcc : αClass e.rr.class = some q.qclass := by rw [hclseq]; exact hqc
    rw [hfields.2.2] at hcc; injection hcc with hcc
    rw [hcc]; cases q.qclass <;> rfl
  · rw [hcr, αCred_usable]; exact decide_eq_true hcred

theorem liveEntry_matching (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (hlive : Cache.liveEntry e name qt qc now = true)
    (ha : αCacheRR e = some a) :
    a.fresh (αTime now) = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true
      ∧ q.qtype.covers a.rr.rtype = true ∧ (a.rr.cls == q.qclass) = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.liveEntry at hlive
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlive
  obtain ⟨⟨⟨hnm, htype⟩, hcls⟩, hfr⟩ := hlive
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show αTime now = now.toNat from rfl, ← αCacheRR_fresh e a now hle ha]; exact hfr
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm hqn
    rw [hfields.1] at hna; injection hna with hna; subst hna; exact hne
  · have htypeq : e.rr.type = qt := eq_of_beq htype
    have hrtt0 : αType e.rr.type = some t := by rw [htypeq]; exact ht
    rw [hrt] at hrtt0
    have hrtt : a.rr.rdata.rtype = t := by injection hrtt0
    rw [hqq]
    show (VeriDNS.Spec.Net.QType.rr t).covers a.rr.rdata.rtype = true
    rw [hrtt]
    exact rrtype_beq_self t
  · have hclseq : e.rr.class = qc := eq_of_beq hcls
    have hcc : αClass e.rr.class = some q.qclass := by rw [hclseq]; exact hqc
    rw [hfields.2.2] at hcc; injection hcc with hcc
    rw [hcc]; cases q.qclass <;> rfl

theorem matching_answerableEntry (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (ha : αCacheRR e = some a)
    (hcanE : e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname)
    (hvE : ∀ x ∈ a.rr.owner, x.size ≤ 63) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hfr : a.fresh (αTime now) = true)
    (hnm : VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
    (hcov : q.qtype.covers a.rr.rtype = true)
    (hcls : (a.rr.cls == q.qclass) = true)
    (hu : a.cred.usable = true) :
    Cache.answerableEntry e name qt qc now = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hcr : a.cred = αCred e.credibility := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; rfl
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.answerableEntry Cache.liveEntry
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN
  · rw [hqq] at hcov
    have hbeq : (t == a.rr.rtype) = true := hcov
    have heqt : t = a.rr.rdata.rtype := eq_of_αType_beq ht hrt hbeq
    have hqte : qt = e.rr.type := αType_injective ht (by rw [hrt, heqt])
    rw [hqte]; exact beq_self_eq_true _
  · have heqc : a.rr.cls = q.qclass := eq_of_αClass_beq hfields.2.2 hqc hcls
    have hqce : qc = e.rr.class := αClass_inj hqc (by rw [hfields.2.2, heqc])
    rw [hqce]; exact beq_self_eq_true _
  · rw [αCacheRR_fresh e a now hle ha]
    rwa [show αTime now = now.toNat from rfl] at hfr
  · rw [hcr, αCred_usable] at hu; exact hu

theorem matching_liveEntry (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (ha : αCacheRR e = some a)
    (hcanE : e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname)
    (hvE : ∀ x ∈ a.rr.owner, x.size ≤ 63) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hfr : a.fresh (αTime now) = true)
    (hnm : VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
    (hcov : q.qtype.covers a.rr.rtype = true)
    (hcls : (a.rr.cls == q.qclass) = true) :
    Cache.liveEntry e name qt qc now = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.liveEntry
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN
  · rw [hqq] at hcov
    have hbeq : (t == a.rr.rtype) = true := hcov
    have heqt : t = a.rr.rdata.rtype := eq_of_αType_beq ht hrt hbeq
    have hqte : qt = e.rr.type := αType_injective ht (by rw [hrt, heqt])
    rw [hqte]; exact beq_self_eq_true _
  · have heqc : a.rr.cls = q.qclass := eq_of_αClass_beq hfields.2.2 hqc hcls
    have hqce : qc = e.rr.class := αClass_inj hqc (by rw [hfields.2.2, heqc])
    rw [hqce]; exact beq_self_eq_true _
  · rw [αCacheRR_fresh e a now hle ha]
    rwa [show αTime now = now.toNat from rfl] at hfr

theorem rrclass_beq_self (x : RRClass) : (x == x) = true := by cases x <;> rfl

theorem αRR_sameKey (e2 e : Cache.CacheEntry) (a2 a : VeriDNS.Spec.Net.CacheRR)
    (h2 : αCacheRR e2 = some a2) (ha : αCacheRR e = some a)
    (h : Cache.sameRRKey e2 e = true) :
    a2.sameKey a.rr = true := by
  have harr2 : αRR e2.rr = some a2.rr := by
    unfold αCacheRR at h2; rw [Option.map_eq_some_iff] at h2; obtain ⟨r, hr, rfl⟩ := h2; exact hr
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha; obtain ⟨r, hr, rfl⟩ := ha; exact hr
  unfold Cache.sameRRKey at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold VeriDNS.Spec.Net.CacheRR.sameKey
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm (αRR_fields e.rr a.rr harr).1
    rw [(αRR_fields e2.rr a2.rr harr2).1] at hna; injection hna with hna; subst hna; exact hne
  · have ht2 : e2.rr.type = e.rr.type := eq_of_beq htype
    have hx := αRR_rtype e2.rr a2.rr harr2
    rw [ht2, αRR_rtype e.rr a.rr harr] at hx
    injection hx with hx
    show (a2.rr.rdata.rtype == a.rr.rdata.rtype) = true
    rw [← hx]; exact rrtype_beq_self _
  · have hc2 : e2.rr.class = e.rr.class := eq_of_beq hcls
    have hx := (αRR_fields e2.rr a2.rr harr2).2.2
    rw [hc2, (αRR_fields e.rr a.rr harr).2.2] at hx
    injection hx with hx
    rw [← hx]; exact rrclass_beq_self _

theorem sameKey_sameRRKey (e2 e : Cache.CacheEntry) (a2 a : VeriDNS.Spec.Net.CacheRR)
    (h2 : αCacheRR e2 = some a2) (ha : αCacheRR e = some a)
    (hcan2 : e2.rr.name = DomainName.labelsToWireFormatGo a2.rr.owner)
    (hcanE : e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner)
    (hv2 : ∀ x ∈ a2.rr.owner, x.size ≤ 63) (hvE : ∀ x ∈ a.rr.owner, x.size ≤ 63)
    (h : a2.sameKey a.rr = true) :
    Cache.sameRRKey e2 e = true := by
  have harr2 : αRR e2.rr = some a2.rr := by
    unfold αCacheRR at h2; rw [Option.map_eq_some_iff] at h2; obtain ⟨r, hr, rfl⟩ := h2; exact hr
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha; obtain ⟨r, hr, rfl⟩ := ha; exact hr
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold Cache.sameRRKey
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcan2 hcanE hv2 hvE
  · have heqt : a2.rr.rdata.rtype = a.rr.rdata.rtype :=
      eq_of_αType_beq (αRR_rtype e2.rr a2.rr harr2) (αRR_rtype e.rr a.rr harr) htype
    have hte := αType_injective (αRR_rtype e2.rr a2.rr harr2)
      (by rw [αRR_rtype e.rr a.rr harr, ← heqt] : αType e.rr.type = some a2.rr.rdata.rtype)
    rw [hte]; exact beq_self_eq_true _
  · have heqc : a2.rr.cls = a.rr.cls :=
      eq_of_αClass_beq (αRR_fields e2.rr a2.rr harr2).2.2 (αRR_fields e.rr a.rr harr).2.2 hcls
    have hce := αClass_inj (αRR_fields e2.rr a2.rr harr2).2.2
      (by rw [(αRR_fields e.rr a.rr harr).2.2, ← heqc] : αClass e.rr.class = some a2.rr.cls)
    rw [hce]; exact beq_self_eq_true _



theorem αRR_set_ttl (rr : VeriDNS.Spec.ResourceRecord) (t : BitVec 32) :
    αRR { rr with ttl := t } = (αRR rr).map (fun mr => { mr with ttl := t.toNat }) := by
  unfold αRR
  cases hn : αName rr.name <;> cases hrd : αRData rr.type rr.rdata <;> cases hcl : αClass rr.class <;>
    simp [hn, hrd, hcl]

theorem rrSameKeyB_rrKeyEq (a b : VeriDNS.Spec.ResourceRecord) (ma mb : VeriDNS.Spec.Net.RR)
    (hma : αRR a = some ma) (hmb : αRR b = some mb)
    (h : Cache.rrSameKeyB a b = true) : VeriDNS.Spec.Net.rrKeyEq ma mb = true := by
  unfold Cache.rrSameKeyB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold VeriDNS.Spec.Net.rrKeyEq
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm (αRR_fields b mb hmb).1
    rw [(αRR_fields a ma hma).1] at hna; injection hna with hna; subst hna; exact hne
  · have ht2 : a.type = b.type := eq_of_beq htype
    have hx := αRR_rtype a ma hma
    rw [ht2, αRR_rtype b mb hmb] at hx
    injection hx with hx
    show (ma.rdata.rtype == mb.rdata.rtype) = true
    rw [← hx]; exact rrtype_beq_self _
  · have hc2 : a.class = b.class := eq_of_beq hcls
    have hx := (αRR_fields a ma hma).2.2
    rw [hc2, (αRR_fields b mb hmb).2.2] at hx
    injection hx with hx
    show (ma.cls == mb.cls) = true
    rw [← hx]; exact rrclass_beq_self _

theorem rrKeyEq_rrSameKeyB (a b : VeriDNS.Spec.ResourceRecord) (ma mb : VeriDNS.Spec.Net.RR)
    (hma : αRR a = some ma) (hmb : αRR b = some mb)
    (hcan_a : a.name = DomainName.labelsToWireFormatGo ma.owner)
    (hcan_b : b.name = DomainName.labelsToWireFormatGo mb.owner)
    (hv_a : ∀ x ∈ ma.owner, x.size ≤ 63) (hv_b : ∀ x ∈ mb.owner, x.size ≤ 63)
    (h : VeriDNS.Spec.Net.rrKeyEq ma mb = true) : Cache.rrSameKeyB a b = true := by
  unfold VeriDNS.Spec.Net.rrKeyEq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold Cache.rrSameKeyB
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcan_a hcan_b hv_a hv_b
  · have heqt : ma.rdata.rtype = mb.rdata.rtype :=
      eq_of_αType_beq (αRR_rtype a ma hma) (αRR_rtype b mb hmb) htype
    have hte := αType_injective (αRR_rtype a ma hma)
      (by rw [αRR_rtype b mb hmb, ← heqt] : αType b.type = some ma.rdata.rtype)
    rw [hte]; exact beq_self_eq_true _
  · have heqc : ma.cls = mb.cls :=
      eq_of_αClass_beq (αRR_fields a ma hma).2.2 (αRR_fields b mb hmb).2.2 hcls
    have hce := αClass_inj (αRR_fields a ma hma).2.2
      (by rw [(αRR_fields b mb hmb).2.2, ← heqc] : αClass b.class = some ma.cls)
    rw [hce]; exact beq_self_eq_true _

theorem rrSameKeyB_eq_rrKeyEq (a b : VeriDNS.Spec.ResourceRecord) (ma mb : VeriDNS.Spec.Net.RR)
    (hma : αRR a = some ma) (hmb : αRR b = some mb)
    (hcan_a : a.name = DomainName.labelsToWireFormatGo ma.owner)
    (hcan_b : b.name = DomainName.labelsToWireFormatGo mb.owner)
    (hv_a : ∀ x ∈ ma.owner, x.size ≤ 63) (hv_b : ∀ x ∈ mb.owner, x.size ≤ 63) :
    Cache.rrSameKeyB a b = VeriDNS.Spec.Net.rrKeyEq ma mb := by
  rw [Bool.eq_iff_iff]
  exact ⟨fun h => rrSameKeyB_rrKeyEq a b ma mb hma hmb h,
         fun h => rrKeyEq_rrSameKeyB a b ma mb hma hmb hcan_a hcan_b hv_a hv_b h⟩

theorem minTtlB_toNat_eq (x y : BitVec 32) : (Cache.minTtlB x y).toNat = min x.toNat y.toNat := by
  simp only [Cache.minTtlB]; split <;> omega

theorem filterMap_congr' {α β : Type} {L : List α} {f g : α → Option β}
    (h : ∀ a ∈ L, f a = g a) : L.filterMap f = L.filterMap g := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

def RRCanonMappable (e : VeriDNS.Spec.ResourceRecord) : Prop :=
  ∃ me, αRR e = some me ∧ e.name = DomainName.labelsToWireFormatGo me.owner
    ∧ ∀ x ∈ me.owner, x.size ≤ 63

theorem groupMin_fold_corr (r0 : VeriDNS.Spec.ResourceRecord) (mr : VeriDNS.Spec.Net.RR)
    (hr0 : αRR r0 = some mr) (hcan0 : r0.name = DomainName.labelsToWireFormatGo mr.owner)
    (hv0 : ∀ x ∈ mr.owner, x.size ≤ 63) :
    ∀ (L : List VeriDNS.Spec.ResourceRecord), (∀ e ∈ L, RRCanonMappable e) →
    ∀ (s : BitVec 32) (sm : Nat), s.toNat = sm →
    (L.foldl (fun acc e => if Cache.rrSameKeyB e r0 then Cache.minTtlB acc e.ttl else acc) s).toNat
      = (L.filterMap αRR).foldl
          (fun acc me => if VeriDNS.Spec.Net.rrKeyEq me mr then min acc me.ttl else acc) sm := by
  intro L
  induction L with
  | nil => intro _ s sm hs; simpa using hs
  | cons e L' ih =>
    intro hL s sm hs
    obtain ⟨me, hme, hcane, hve⟩ := hL e (List.mem_cons_self ..)
    rw [List.filterMap_cons, hme]
    simp only [List.foldl_cons]
    have hkey : Cache.rrSameKeyB e r0 = VeriDNS.Spec.Net.rrKeyEq me mr :=
      rrSameKeyB_eq_rrKeyEq e r0 me mr hme hr0 hcane hcan0 hve hv0
    have httl : e.ttl.toNat = me.ttl := ((αRR_fields e me hme).2.1).symm
    refine ih (fun x hx => hL x (List.mem_cons_of_mem e hx)) _ _ ?_
    rw [hkey]
    by_cases hk : VeriDNS.Spec.Net.rrKeyEq me mr = true
    · simp only [hk, if_true]; rw [minTtlB_toNat_eq, hs, httl]
    · simp only [hk, Bool.false_eq_true, if_false]; exact hs

theorem groupMin_corr (L : List VeriDNS.Spec.ResourceRecord) (hL : ∀ e ∈ L, RRCanonMappable e)
    (r0 : VeriDNS.Spec.ResourceRecord) (mr : VeriDNS.Spec.Net.RR) (hr0 : αRR r0 = some mr)
    (hcan0 : r0.name = DomainName.labelsToWireFormatGo mr.owner) (hv0 : ∀ x ∈ mr.owner, x.size ≤ 63) :
    (Cache.groupMinTtl L r0).toNat = VeriDNS.Spec.Net.rrGroupMin (L.filterMap αRR) mr := by
  unfold Cache.groupMinTtl VeriDNS.Spec.Net.rrGroupMin
  exact groupMin_fold_corr r0 mr hr0 hcan0 hv0 L hL r0.ttl mr.ttl ((αRR_fields r0 mr hr0).2.1).symm

theorem filterMap_optionMap_eq {α β : Type} (L : List α) (f : α → Option β)
    (g : α → β → β) (h : β → β) (hyp : ∀ a ∈ L, ∀ b, f a = some b → g a b = h b) :
    L.filterMap (fun a => (f a).map (g a)) = (L.filterMap f).map h := by
  induction L with
  | nil => rfl
  | cons a L' ih =>
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => simp only [hfa, Option.map_none]; rw [List.filterMap_cons, hfa]; exact ih (fun x hx b hb => hyp x (List.mem_cons_of_mem a hx) b hb)
    | some b =>
      simp only [hfa, Option.map_some]
      rw [List.filterMap_cons, hfa, List.map_cons, hyp a (List.mem_cons_self ..) b hfa]
      exact congrArg _ (ih (fun x hx b hb => hyp x (List.mem_cons_of_mem a hx) b hb))

theorem αSection_normRaws (R : Array ByteArray) (hwf : ∀ e ∈ Cache.rrsOf R, RRCanonMappable e) :
    αSection (Cache.normRaws R) = VeriDNS.Spec.Net.normalizeTTL (αSection R) := by
  have hαsec : αSection R = (Cache.rrsOf R).filterMap αRR := by
    unfold αSection Cache.rrsOf
    rw [List.filterMap_filterMap]
    congr 1
    funext b
    show (match (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
          | .ok (rr, _) => some rr | .error _ => none) with
        | some rr => αRR rr | none => none)
      = (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
          | .ok (rr, _) => some rr | .error _ => none).bind αRR
    cases DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
    | error e => rfl
    | ok v => obtain ⟨rr, pos⟩ := v; rfl
  have hround : ∀ r0 ∈ Cache.rrsOf R,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
          { r0 with ttl := Cache.groupMinTtl (Cache.rrsOf R) r0 })
        = some { r0 with ttl := Cache.groupMinTtl (Cache.rrsOf R) r0 } := by
    intro r0 hr0
    obtain ⟨b, _, hpb⟩ := List.mem_filterMap.mp hr0
    exact VeriDNS.Proof.NameTree.parseRaw_rrBytes_of_wf
      (VeriDNS.Proof.NameTree.wfRR_set_ttl (VeriDNS.Proof.NameTree.wfRR_of_parseRaw hpb) _)
  have hLHS : αSection (Cache.normRaws R)
      = (Cache.rrsOf R).filterMap (fun r0 => (αRR r0).map
          (fun mr => { mr with ttl := (Cache.groupMinTtl (Cache.rrsOf R) r0).toNat })) := by
    unfold αSection Cache.normRaws Cache.normalizeRRsetTtls
    rw [List.toList_toArray, List.map_map, List.filterMap_map]
    apply filterMap_congr'
    intro r0 hr0
    show (match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
          { r0 with ttl := Cache.groupMinTtl (Cache.rrsOf R) r0 }) with
        | some rr => αRR rr | none => none)
      = (αRR r0).map (fun mr => { mr with ttl := (Cache.groupMinTtl (Cache.rrsOf R) r0).toNat })
    rw [hround r0 hr0]; exact αRR_set_ttl r0 _
  rw [hLHS, hαsec]
  unfold VeriDNS.Spec.Net.normalizeTTL
  refine filterMap_optionMap_eq (Cache.rrsOf R) αRR _ _ ?_
  intro r0 hr0 mr hmr
  obtain ⟨me', hme', hc', hv'⟩ := hwf r0 hr0
  rw [hmr] at hme'; obtain rfl := Option.some.inj hme'
  have hgm := groupMin_corr (Cache.rrsOf R) hwf r0 mr hmr hc' hv'
  rw [hgm]

def αNegRR (e : Cache.NegativeEntry) : Option VeriDNS.Spec.Net.NegRR :=
  match αName e.name with
  | none => none
  | some n =>
    if e.rcode == VeriDNS.Spec.Rcode.nameError then
      some { qname := n, qtype := none, insertedAt := 0, ttl := e.expiry.toNat }
    else
      match αType e.qtype with
      | some t => some { qname := n, qtype := some (.rr t), insertedAt := 0, ttl := e.expiry.toNat }
      | none => none

def αCache (c : Cache.DnsCache) : VeriDNS.Spec.Net.Cache :=
  { pos := c.records.toList.filterMap αCacheRR
    neg := c.negatives.toList.filterMap αNegRR }

theorem αCache_boundExpiryClasses_noop (c : Cache.DnsCache)
    (h : c.records.size ≤ Cache.DnsCache.capacity) :
    αCache c.boundExpiryClasses = αCache c := by
  rw [VeriDNS.Proof.Cache.boundExpiryClasses_noop c h]

theorem αCache_boundExpiryClasses_pos_subset (c : Cache.DnsCache) {e : VeriDNS.Spec.Net.CacheRR}
    (he : e ∈ (αCache c.boundExpiryClasses).pos) : e ∈ (αCache c).pos := by
  simp only [αCache, List.mem_filterMap] at he ⊢
  obtain ⟨entry, hmem, hα⟩ := he
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at hmem
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at hmem
  exact ⟨entry, hmem.1, hα⟩

theorem filterMap_filter_comm {α β : Type} (l : List α) (r : α → Bool) (f : α → Option β) (q : β → Bool)
    (h : ∀ x ∈ l, ∀ y, f x = some y → r x = q y) :
    (l.filter r).filterMap f = (l.filterMap f).filter q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [List.filter_cons]
    cases hf : f a with
    | none =>
      by_cases hr : r a = true
      · rw [if_pos hr, List.filterMap_cons, hf, List.filterMap_cons, hf, ih']
      · rw [if_neg hr, List.filterMap_cons, hf, ih']
    | some b =>
      have hqb : q b = r a := (h a (List.mem_cons_self ..) b hf).symm
      by_cases hr : r a = true
      · rw [if_pos hr, List.filterMap_cons, hf, List.filterMap_cons, hf, List.filter_cons,
          if_pos (by rw [hqb]; exact hr), ih']
      · rw [if_neg hr, List.filterMap_cons, hf, List.filter_cons,
          if_neg (by rw [hqb]; exact hr), ih']

theorem αCache_boundExpiryClasses_pos_filter (c : Cache.DnsCache)
    (hwf : ∀ e ∈ c.records.toList, e.rr.ttl.toNat ≤ e.expiry.toNat) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      (αCache c.boundExpiryClasses).pos = (αCache c).pos.filter qf
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.insertedAt + ce₁.rr.ttl = ce₂.insertedAt + ce₂.rr.ttl → qf ce₁ = qf ce₂) := by
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  refine ⟨fun ce => p (UInt32.ofNat (ce.insertedAt + ce.rr.ttl)), ?_,
    fun ce₁ ce₂ hexp => by simp only [hexp]⟩
  show (c.boundExpiryClasses.records).toList.filterMap αCacheRR
      = ((c.records).toList.filterMap αCacheRR).filter _
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses
  rw [hp, Array.toList_filter]
  apply filterMap_filter_comm
  intro entry hentry ce hce
  have httl := hwf entry hentry
  unfold αCacheRR at hce
  rw [Option.map_eq_some_iff] at hce
  obtain ⟨r, hr, hceeq⟩ := hce
  have hrttl : r.ttl = entry.rr.ttl.toNat := by
    unfold αRR at hr
    split at hr
    · rw [← Option.some.inj hr]
    · simp at hr
  show p entry.expiry = p (UInt32.ofNat (ce.insertedAt + ce.rr.ttl))
  congr 1
  rw [← hceeq]
  show entry.expiry = UInt32.ofNat ((entry.expiry.toNat - entry.rr.ttl.toNat) + r.ttl)
  rw [hrttl, Nat.sub_add_cancel httl]
  simp

theorem αCache_boundExpiryClasses_eq (c : Cache.DnsCache)
    (hwf : ∀ e ∈ c.records.toList, e.rr.ttl.toNat ≤ e.expiry.toNat) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      αCache c.boundExpiryClasses
        = { pos := (αCache c).pos.filter qf, neg := (αCache c).neg }
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.insertedAt + ce₁.rr.ttl = ce₂.insertedAt + ce₂.rr.ttl → qf ce₁ = qf ce₂) := by
  obtain ⟨qf, hpos, hexp⟩ := αCache_boundExpiryClasses_pos_filter c hwf
  refine ⟨qf, ?_, hexp⟩
  have hneg : (αCache c.boundExpiryClasses).neg = (αCache c).neg := rfl
  cases hαbe : αCache c.boundExpiryClasses with
  | mk pos neg =>
    have hp : pos = (αCache c).pos.filter qf := by rw [← hpos, hαbe]
    have hn : neg = (αCache c).neg := by rw [← hneg, hαbe]
    rw [hp, hn]

theorem cacheRRs_αCache_pos (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (c : Cache.DnsCache)
    (h : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b ∈ raws.toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (rr.ttl == 0) = false →
        (acc.storeChecked rr cred now).records
          = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩) :
    (αCache (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now)).pos
      = (αCache c).pos ++ (raws.toList.flatMap (pushOf cred now)).filterMap αCacheRR := by
  have hrec : (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c raws cred now).records.toList
      = c.records.toList ++ raws.toList.flatMap (pushOf cred now) := by
    have he : Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now
        = raws.toList.foldl (fun (acc : Cache.DnsCache) b =>
            match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
            | some rr => acc.storeChecked rr cred now | none => acc) c := by
      unfold Resolver.cacheRRs
      rw [array_foldl_toList]
      congr 1
      funext acc b
      cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => rfl
      | some rr => rfl
    rw [he]
    exact foldl_storeChecked_concrete cred now raws.toList c h
  unfold αCache
  rw [hrec, List.filterMap_append]

theorem cacheUnlessTruncated_untruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (htc : (resp.header.tc == 1) = false) :
    Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache resp raws cred now
      = Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache (Cache.normRaws raws) cred now := by
  unfold Resolver.cacheUnlessTruncated
  rw [htc]; rfl

theorem cacheUnlessTruncated_negatives (c : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    (Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now).negatives = c.negatives := by
  unfold Resolver.cacheUnlessTruncated
  split
  · rfl
  · exact cacheRRs_negatives _ cred now c

theorem two_section_αCache_pos (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws1 raws2 : Array ByteArray) (cred1 cred2 : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (htc : (resp.header.tc == 1) = false)
    (h1 : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (Cache.normRaws raws1).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr cred1 now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred1, now⟩)
    (h2 : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (Cache.normRaws raws2).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr cred2 now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred2, now⟩) :
    (αCache (Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache resp raws1 cred1 now) resp raws2 cred2 now)).pos
      = (αCache cache).pos
        ++ ((Cache.normRaws raws1).toList.flatMap (pushOf cred1 now)).filterMap αCacheRR
        ++ ((Cache.normRaws raws2).toList.flatMap (pushOf cred2 now)).filterMap αCacheRR := by
  rw [cacheUnlessTruncated_untruncated _ _ _ _ _ htc, cacheUnlessTruncated_untruncated _ _ _ _ _ htc,
    cacheRRs_αCache_pos (Cache.normRaws raws2) cred2 now _ h2,
    cacheRRs_αCache_pos (Cache.normRaws raws1) cred1 now cache h1]

theorem mem_αCache_pos (c : Cache.DnsCache) (a : VeriDNS.Spec.Net.CacheRR)
    (h : a ∈ (αCache c).pos) : ∃ e ∈ c.records, αCacheRR e = some a := by
  unfold αCache at h
  simp only [List.mem_filterMap] at h
  obtain ⟨e, he, ha⟩ := h
  exact ⟨e, Array.mem_def.mpr he, ha⟩

theorem mem_αCache_neg (c : Cache.DnsCache) (a : VeriDNS.Spec.Net.NegRR)
    (h : a ∈ (αCache c).neg) : ∃ e ∈ c.negatives, αNegRR e = some a := by
  unfold αCache at h
  simp only [List.mem_filterMap] at h
  obtain ⟨e, he, ha⟩ := h
  exact ⟨e, Array.mem_def.mpr he, ha⟩

theorem αNegRR_fields {e : Cache.NegativeEntry} {a : VeriDNS.Spec.Net.NegRR}
    (h : αNegRR e = some a) : a.insertedAt = 0 ∧ a.ttl = e.expiry.toNat := by
  unfold αNegRR at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · split at h
      · injection h with h; subst h; exact ⟨rfl, rfl⟩
      · exact absurd h (by simp)

theorem αCache_negHit (c : Cache.DnsCache) (now : UInt32) (q : VeriDNS.Spec.Net.Query)
    (e : Cache.NegativeEntry) (a : VeriDNS.Spec.Net.NegRR)
    (he : e ∈ c.negatives) (hα : αNegRR e = some a) (hfresh : now < e.expiry)
    (hname : VeriDNS.Spec.Net.nameEq a.qname q.qname = true)
    (hqt : (match a.qtype with | none => true | some t => t == q.qtype) = true) :
    (αCache c).negHit (αTime now) q = true := by
  unfold VeriDNS.Spec.Net.Cache.negHit
  apply List.any_eq_true.mpr
  refine ⟨a, ?_, ?_⟩
  · unfold αCache
    simp only [List.mem_filterMap]
    exact ⟨e, Array.mem_def.mp he, hα⟩
  · simp only [Bool.and_eq_true]
    obtain ⟨h0, htt⟩ := αNegRR_fields hα
    refine ⟨⟨?_, hname⟩, hqt⟩
    unfold VeriDNS.Spec.Net.NegRR.fresh αTime
    rw [h0, htt, Nat.zero_add]
    exact Nat.blt_eq.mpr (UInt32.lt_iff_toNat_lt.mp hfresh)

theorem lookupNegative_negHit (cache : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rc : VeriDNS.Spec.Rcode) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hlk : cache.lookupNegative name qt qc now = some rc)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) :
    (αCache cache).negHit (αTime now) q = true := by
  have rcodeEq : ∀ a : VeriDNS.Spec.Rcode,
      (a == VeriDNS.Spec.Rcode.nameError) = true → a = VeriDNS.Spec.Rcode.nameError := by
    intro a h; cases a <;> first | rfl | exact absurd h (by decide)
  have go : ∀ e ∈ cache.negatives,
      VeriDNS.Impl.DomainName.nameEqCI e.name name = true → now < e.expiry →
      (e.rcode = VeriDNS.Spec.Rcode.nameError ∨ e.qtype = qt) →
      (αCache cache).negHit (αTime now) q = true := by
    intro e hemem hname hfresh hkind
    obtain ⟨na, hna, hnameq⟩ := αName_of_nameEqCI hname hqn
    by_cases hnx : e.rcode = VeriDNS.Spec.Rcode.nameError
    · refine αCache_negHit cache now q e ⟨na, none, 0, e.expiry.toNat⟩ hemem ?_ hfresh hnameq rfl
      unfold αNegRR; rw [hna]; rw [hnx]; rfl
    · have heqt : e.qtype = qt := hkind.resolve_left hnx
      have hrcf : (e.rcode == VeriDNS.Spec.Rcode.nameError) = false := by
        cases hc : e.rcode == VeriDNS.Spec.Rcode.nameError
        · rfl
        · exact absurd (rcodeEq _ hc) hnx
      refine αCache_negHit cache now q e
        ⟨na, some (VeriDNS.Spec.Net.QType.rr t), 0, e.expiry.toNat⟩ hemem ?_ hfresh hnameq ?_
      · unfold αNegRR; rw [hna]; simp [hrcf, heqt, ht]
      · simp only [hqq]; exact rrtype_beq_self t
  unfold Cache.DnsCache.lookupNegative at hlk
  cases hnxr : cache.lookupNxdomain name qc now with
  | some rc' =>
    unfold Cache.DnsCache.lookupNxdomain at hnxr
    obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some hnxr
    split at hef
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcond
      exact go e hemem hcond.1.1.1 hcond.1.2 (Or.inl (rcodeEq _ hcond.2))
    · exact absurd hef (by simp)
  | none =>
    rw [hnxr] at hlk
    obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some hlk
    split at hef
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcond
      exact go e hemem hcond.1.1.1 hcond.2 (Or.inr (eq_of_beq hcond.1.1.2))
    · exact absurd hef (by simp)

theorem αCache_negHitNx (c : Cache.DnsCache) (now : UInt32) (q : VeriDNS.Spec.Net.Query)
    (e : Cache.NegativeEntry) (a : VeriDNS.Spec.Net.NegRR)
    (he : e ∈ c.negatives) (hα : αNegRR e = some a) (hfresh : now < e.expiry)
    (hname : VeriDNS.Spec.Net.nameEq a.qname q.qname = true)
    (hnone : a.qtype.isNone = true) :
    (αCache c).negHitNx (αTime now) q = true := by
  unfold VeriDNS.Spec.Net.Cache.negHitNx
  apply List.any_eq_true.mpr
  refine ⟨a, ?_, ?_⟩
  · unfold αCache
    simp only [List.mem_filterMap]
    exact ⟨e, Array.mem_def.mp he, hα⟩
  · simp only [Bool.and_eq_true]
    obtain ⟨h0, htt⟩ := αNegRR_fields hα
    refine ⟨⟨?_, hname⟩, hnone⟩
    unfold VeriDNS.Spec.Net.NegRR.fresh αTime
    rw [h0, htt, Nat.zero_add]
    exact Nat.blt_eq.mpr (UInt32.lt_iff_toNat_lt.mp hfresh)

theorem lookupNxdomain_nameError (c : Cache.DnsCache) (name : ByteArray) (qc : BitVec 16)
    (now : UInt32) (rc : VeriDNS.Spec.Rcode)
    (h : c.lookupNxdomain name qc now = some rc) : rc = VeriDNS.Spec.Rcode.nameError := by
  have hrcodeEq : ∀ a : VeriDNS.Spec.Rcode,
      (a == VeriDNS.Spec.Rcode.nameError) = true → a = VeriDNS.Spec.Rcode.nameError :=
    fun a h => by cases a <;> first | rfl | exact absurd h (by decide)
  unfold Cache.DnsCache.lookupNxdomain at h
  obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some h
  split at hef
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    have hrc : e.rcode = rc := by injection hef
    rw [← hrc]; exact hrcodeEq _ hcond.2
  · exact absurd hef (by simp)

theorem lookupNxdomain_negHitNx (c : Cache.DnsCache) (name : ByteArray) (qc : BitVec 16)
    (now : UInt32) (rc : VeriDNS.Spec.Rcode) (q : VeriDNS.Spec.Net.Query)
    (h : c.lookupNxdomain name qc now = some rc) (hqn : αName name = some q.qname) :
    (αCache c).negHitNx (αTime now) q = true := by
  unfold Cache.DnsCache.lookupNxdomain at h
  obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some h
  split at hef
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcond
    obtain ⟨na, hna, hnameq⟩ := αName_of_nameEqCI hcond.1.1.1 hqn
    refine αCache_negHitNx c now q e ⟨na, none, 0, e.expiry.toNat⟩ hemem ?_ hcond.1.2 hnameq rfl
    unfold αNegRR; rw [hna]; rw [hcond.2]; rfl
  · exact absurd hef (by simp)

theorem localAnswer_negative (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray) (rc : VeriDNS.Spec.Rcode)
    (h : cache.lookupNegative sname qt qc now = some rc) :
    Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection
          (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now) chain := by
  simp only [Resolver.localAnswer]
  rw [show VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now
      = cache.lookupNegative sname qt qc now from rfl, h]

theorem localAnswer_answerHit (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hneg : cache.lookupNegative sname qt qc now = none)
    (hans : VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now = rrs)
    (hne : rrs.isEmpty = false) :
    Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited
      = .answerHit sname chain rrs := by
  simp only [Resolver.localAnswer]
  rw [show VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now
      = cache.lookupNegative sname qt qc now from rfl, hneg, hans]
  simp only [hne, Bool.false_eq_true, if_false]

theorem localAnswer_answerHit_inv (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname0 : ByteArray) (chain0 visited0 : Array ByteArray)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (h : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname0 chain0 visited0 = .answerHit sname chain rrs) :
    cache.lookupNegative sname qt qc now = none
      ∧ VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now = rrs
      ∧ rrs.isEmpty = false := by
  induction fuel generalizing sname0 chain0 visited0 with
  | zero => simp only [Resolver.localAnswer] at h; exact absurd h (by simp)
  | succ n ih =>
    simp only [Resolver.localAnswer] at h
    split at h
    · exact absurd h (by simp)
    · next hneg =>
      split at h
      · split at h
        · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · exact ih _ _ _ h
          · exact absurd h (by simp)
      · next hne =>
        injection h with hs hc hr
        subst sname0
        refine ⟨?_, hr, by rw [← hr]; simpa using hne⟩
        rw [show cache.lookupNegative sname qt qc now
          = VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now from rfl]
        exact hneg

theorem localAnswer_cname_step (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
    (crr : VeriDNS.Spec.ResourceRecord)
    (hneg : cache.lookupNegative sname qt qc now = none)
    (hempty : (VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true)
    (hnt5 : (qt == (5 : BitVec 16)) = false)
    (hcn : (VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname (5 : BitVec 16) qc now)[0]? = some crr)
    (hnrev : (visited.any (fun v =>
        VeriDNS.Impl.DomainName.nameEqCI v (VeriDNS.Spec.RRParse.rrRdata crr))) = false) :
    Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited
      = Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qt qc now fuel (VeriDNS.Spec.RRParse.rrRdata crr)
          (chain.push (VeriDNS.Spec.RRParse.rrBytes crr))
          (visited.push (VeriDNS.Spec.RRParse.rrRdata crr)) := by
  simp only [Resolver.localAnswer]
  rw [show VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now
      = cache.lookupNegative sname qt qc now from rfl, hneg]
  simp only [hempty, hnt5, hcn, hnrev, if_true, Bool.false_eq_true, if_false]

def RespAgree (a b : VeriDNS.Spec.Net.Response) : Prop :=
  a.rcode = b.rcode ∧ a.answer.Perm b.answer

theorem RespAgree.of_eq {a b : VeriDNS.Spec.Net.Response}
    (hrc : a.rcode = b.rcode) (han : a.answer = b.answer) : RespAgree a b :=
  ⟨hrc, han ▸ List.Perm.refl _⟩

theorem RespAgree.refl (a : VeriDNS.Spec.Net.Response) : RespAgree a a := ⟨rfl, List.Perm.refl _⟩

theorem RespAgree.trans {a b c : VeriDNS.Spec.Net.Response}
    (h1 : RespAgree a b) (h2 : RespAgree b c) : RespAgree a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

def HasVerdict (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : VeriDNS.Spec.Net.Time) (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name)
    (c : VeriDNS.Spec.Net.Cache) (slist : List String) (q : VeriDNS.Spec.Net.Query)
    (v : VeriDNS.Spec.Net.Response) : Prop :=
  ∃ tr sp tEnd cout resp,
    VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q
      tr sp tEnd cout resp
    ∧ RespAgree v resp

def HasVerdictAt (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : VeriDNS.Spec.Net.Time) (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name)
    (c : VeriDNS.Spec.Net.Cache) (slist : List String) (q : VeriDNS.Spec.Net.Query)
    (v : VeriDNS.Spec.Net.Response) (coutM : VeriDNS.Spec.Net.Cache) : Prop :=
  ∃ tr sp tEnd resp,
    VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q
      tr sp tEnd coutM resp
    ∧ RespAgree v resp

theorem HasVerdictAt.toHasVerdict
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState}
    {resolverAddr : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : VeriDNS.Spec.Net.Time} {nseen seen : List VeriDNS.Spec.Net.Name}
    {c : VeriDNS.Spec.Net.Cache} {slist : List String} {q : VeriDNS.Spec.Net.Query}
    {v : VeriDNS.Spec.Net.Response} {coutM : VeriDNS.Spec.Net.Cache}
    (h : HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v coutM) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v := by
  obtain ⟨tr, sp, tEnd, resp, hres, hag⟩ := h
  exact ⟨tr, sp, tEnd, coutM, resp, hres, hag⟩

theorem cacheWrite_pos_in_bailiwick (c : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (sect : Array ByteArray)
    (bw : ByteArray) (cred : Trustworthiness) (now : UInt32) (bwN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (a : VeriDNS.Spec.Net.CacheRR)
    (ha : a ∈ (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw sect)
        cred now)).pos) :
    a ∈ (αCache c).pos ∨ VeriDNS.Spec.Net.isAncestor bwN a.rr.owner = true := by
  obtain ⟨e, he, hae⟩ := mem_αCache_pos _ a ha
  have hαrr : αRR e.rr = some a.rr := by
    unfold αCacheRR at hae
    rw [Option.map_eq_some_iff] at hae
    obtain ⟨r, hr, rfl⟩ := hae
    exact hr
  have hown : αName e.rr.name = some a.rr.owner := (αRR_fields e.rr a.rr hαrr).1
  have hpos : e ∈ c.records → a ∈ (αCache c).pos := by
    intro hec
    unfold αCache
    simp only [List.mem_filterMap]
    exact ⟨e, Array.mem_def.mp hec, hae⟩
  unfold Resolver.cacheUnlessTruncated at he
  split at he
  · exact Or.inl (hpos he)
  · rcases mem_cacheRRs_records _ cred now c he with hec | ⟨b, hb, hpb⟩
    · exact Or.inl (hpos hec)
    · right
      obtain ⟨r, hr, hrreq⟩ := VeriDNS.Proof.NameTree.parseRaw_mem_normRaws hb hpb
      obtain ⟨b', hb', hpb'⟩ := List.mem_filterMap.mp hr
      have hpb'' : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some r := hpb'
      have hname : e.rr.name = r.name := by rw [hrreq]
      have hanc : Resolver.isAncestorB bw e.rr.name = true := by
        rw [hname]; exact Resolver.bailiwickRaws_owner_inBailiwick bw sect hb' hpb''
      exact isAncestorB_isAncestor bw e.rr.name bwN a.rr.owner hbw hown hanc

theorem referralCacheWrite_pos_in_bailiwick (c : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (cred1 cred2 : Trustworthiness) (now : UInt32) (cutN : VeriDNS.Spec.Net.Name)
    (hcut : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
        = some cutN)
    (a : VeriDNS.Spec.Net.CacheRR)
    (ha : a ∈ (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
          cred1 now)
        resp
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
        cred2 now)).pos) :
    a ∈ (αCache c).pos ∨ VeriDNS.Spec.Net.isAncestor cutN a.rr.owner = true := by
  rcases cacheWrite_pos_in_bailiwick _ resp resp.additional _ cred2 now cutN hcut a ha with hinner | hbail
  · rcases cacheWrite_pos_in_bailiwick c resp resp.authority _ cred1 now cutN hcut a hinner with
      horig | hbail2
    · exact Or.inl horig
    · exact Or.inr hbail2
  · exact Or.inr hbail

theorem lookupAnswerable_no_stale (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupAnswerable name qt qc now) : 0 < rr.ttl.toNat := by
  unfold Cache.DnsCache.lookupAnswerable at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, _, hsome⟩ := h
  split at hsome
  · rename_i hans

    have hfresh : e.fresh now = true := by
      rw [Bool.and_eq_true] at hans
      obtain ⟨hans, _⟩ := hans
      unfold Cache.answerableEntry Cache.liveEntry at hans
      simp only [Bool.and_eq_true] at hans
      obtain ⟨⟨⟨⟨_, _⟩, _⟩, hf⟩, _⟩ := hans
      exact hf
    have hlt : now < e.expiry := by
      have hb := hfresh; unfold Cache.CacheEntry.fresh at hb; simpa using hb
    have hpos : 0 < (e.expiry - now).toNat := by
      rw [UInt32.toNat_sub_of_le e.expiry now (UInt32.le_of_lt hlt)]
      have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    obtain rfl : rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
      injection hsome with h'; exact h'.symm
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
    exact hpos
  · exact absurd hsome (by simp)

theorem lookupAnswerable_grounded (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupAnswerable name qt qc now) :
    ∃ e ∈ c.records, rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold Cache.DnsCache.lookupAnswerable at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  refine ⟨e, he, ?_⟩
  split at hsome
  · injection hsome with h'; exact h'.symm
  · exact absurd hsome (by simp)

theorem lookupTopCred_grounded (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred name qt qc now) :
    ∃ e ∈ c.records, rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  refine ⟨e, he, ?_⟩
  split at hsome
  · injection hsome with h'; exact h'.symm
  · exact absurd hsome (by simp)

theorem mem_lookupTopCred_rrType (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord) (h : rr ∈ c.lookupTopCred name qt qc now) :
    (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == qt) = true := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, _, hsome⟩ := h
  split at hsome
  · rename_i hgate
    rw [Bool.and_eq_true] at hgate
    have hl := hgate.1
    unfold Cache.liveEntry at hl
    simp only [Bool.and_eq_true] at hl
    obtain ⟨⟨⟨_, htype⟩, _⟩, _⟩ := hl
    injection hsome with hsome
    rw [← hsome]
    exact htype
  · exact absurd hsome (by simp)

theorem mem_lookupTopCred_entry (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord) (h : rr ∈ c.lookupTopCred name qt qc now) :
    ∃ e ∈ c.records, VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
      = VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) e.rr
      ∧ VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
        = VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) e.rr := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  refine ⟨e, he, ?_, ?_⟩
  all_goals
    split at hsome
    · rw [Option.some.injEq] at hsome; subst hsome; rfl
    · exact absurd hsome (by simp)

theorem ns_extract_isSome (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now) :
    (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
      then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none).isSome = true := by
  rw [if_pos (mem_lookupTopCred_rrType c cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now rr h)]
  rfl

theorem lookupTopCred_no_stale (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred name qt qc now) : 0 < rr.ttl.toNat := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, _, hsome⟩ := h
  split at hsome
  · rename_i hgate
    have hfresh : e.fresh now = true := by
      rw [Bool.and_eq_true] at hgate
      obtain ⟨hlive, _⟩ := hgate
      unfold Cache.liveEntry at hlive
      simp only [Bool.and_eq_true] at hlive
      obtain ⟨⟨⟨_, _⟩, _⟩, hf⟩ := hlive
      exact hf
    have hlt : now < e.expiry := by
      have hb := hfresh; unfold Cache.CacheEntry.fresh at hb; simpa using hb
    have hpos : 0 < (e.expiry - now).toNat := by
      rw [UInt32.toNat_sub_of_le e.expiry now (UInt32.le_of_lt hlt)]
      have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    obtain rfl : rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
      injection hsome with h'; exact h'.symm
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
    exact hpos
  · exact absurd hsome (by simp)

theorem lookupTopCred_toList_filterMap {β : Type} (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (g : VeriDNS.Spec.ResourceRecord → Option β) :
    (c.lookupTopCred name qt qc now).toList.filterMap g
      = c.records.toList.filterMap (fun e =>
          if Cache.liveEntry e name qt qc now && c.maxRankForKey e now
          then g { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } else none) := by
  unfold Cache.DnsCache.lookupTopCred
  rw [Array.toList_filterMap, List.filterMap_filterMap]
  congr 1
  funext e
  cases hg : (Cache.liveEntry e name qt qc now && c.maxRankForKey e now) <;> simp [hg]

theorem αSection_map_rrBytes_wf (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hwf : ∀ rr ∈ rrs, VeriDNS.Proof.NameTree.WfRR rr) :
    αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
      = rrs.toList.filterMap αRR := by
  unfold αSection
  rw [Array.toList_map, List.filterMap_map]
  have key : ∀ l : List VeriDNS.Spec.ResourceRecord,
      (∀ rr ∈ l, VeriDNS.Proof.NameTree.WfRR rr) →
      l.filterMap ((fun b => match VeriDNS.Spec.RRParse.parseRaw
            (RR := VeriDNS.Spec.ResourceRecord) b with
          | some rr => αRR rr | none => none) ∘ VeriDNS.Spec.RRParse.rrBytes)
        = l.filterMap αRR := by
    intro l hl
    induction l with
    | nil => rfl
    | cons rr rest ih =>
      simp only [List.filterMap_cons, Function.comp_apply,
        VeriDNS.Proof.NameTree.parseRaw_rrBytes_of_wf (hl rr (List.mem_cons_self ..))]
      rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  exact key rrs.toList (fun rr hrr => hwf rr (Array.mem_def.mpr hrr))

theorem served_is_per_key_maximal (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (e e2 : Cache.CacheEntry)
    (hmax : c.maxCredForKey e name qt qc now = true)
    (h2 : e2 ∈ c.records) (hans2 : Cache.answerableEntry e2 name qt qc now = true)
    (hkey : Cache.sameRRKey e2 e = true) :
    e.credibility.toCode ≤ e2.credibility.toCode := by
  unfold Cache.DnsCache.maxCredForKey at hmax
  obtain ⟨i, hi, hgi⟩ := Array.getElem_of_mem h2
  have hbody := Array.all_eq_true.mp hmax i hi
  rw [hgi] at hbody
  simp only [hans2, hkey, Bool.and_true, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at hbody
  exact hbody



theorem filter_map_eq_filterMap {α β} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f = l.filterMap (fun a => bif p a then some (f a) else none) := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.filter_cons]; cases hx : p x <;> simp [hx, List.filterMap_cons, ih]

theorem filter_filterMap_eq {α β} (l : List α) (p : α → Bool) (g : α → Option β) :
    (l.filter p).filterMap g = l.filterMap (fun a => bif p a then g a else none) := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.filter_cons]; cases hx : p x <;> simp [hx, List.filterMap_cons, ih]

theorem filterMap_congr_mem {α β} (l : List α) (f g : α → Option β) (h : ∀ a ∈ l, f a = g a) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h x (by simp), ih (fun a ha => h a (by simp [ha]))]

theorem flatMap_congr_mem {α β} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih (fun a ha => h a (by simp [ha]))]

theorem lookupAnswerable_subset_hit (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hmaxrank : ∀ a ∈ (αCache c).matching (αTime now) q,
        ((αCache c).matching (αTime now) q).all
          (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true)
    (rr : VeriDNS.Spec.ResourceRecord) (hrr : rr ∈ c.lookupAnswerable name qt qc now) :
    ∃ rm, αRR rr = some rm ∧ rm ∈ (αCache c).hit (αTime now) q := by
  unfold Cache.DnsCache.lookupAnswerable at hrr
  rw [Array.mem_filterMap] at hrr
  obtain ⟨e, hemem, hsome⟩ := hrr
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hans, _hmax⟩ := hcond
    injection hsome with hsome
    obtain ⟨hane, hle, hmono⟩ := hwf e hemem
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
    have hfr : e.fresh now = true := by
      unfold Cache.answerableEntry Cache.liveEntry at hans
      simp only [Bool.and_eq_true] at hans
      exact hans.1.2
    obtain ⟨hf, hne, hcov, hcl, hus⟩ :=
      answerableEntry_matching e a name qt qc now q t hqn ht hqq hqc hle hans ha
    have hmatch : a ∈ (αCache c).matching (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.matching
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold αCache; simp only [List.mem_filterMap]
        exact ⟨e, Array.mem_def.mp hemem, ha⟩
      · simp only [Bool.and_eq_true]; exact ⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩
    have hserved : a ∈ (αCache c).served (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.served
      rw [List.mem_filter]
      refine ⟨hmatch, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hus, hmaxrank a hmatch⟩
    refine ⟨{ a.rr with ttl := a.rr.ttl - (now.toNat - a.insertedAt) }, ?_, ?_⟩
    · rw [← hsome]; exact αRR_aged e a now hle hfr hmono ha
    · unfold VeriDNS.Spec.Net.Cache.hit
      rw [List.mem_map]
      exact ⟨a, hserved, rfl⟩
  · exact absurd hsome (by simp)

theorem maxCredForKey_of_served_maximal (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hmax : ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true) :
    c.maxCredForKey e name qt qc now = true := by
  unfold Cache.DnsCache.maxCredForKey
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro e2 he2
  by_cases hcond : (Cache.answerableEntry e2 name qt qc now && Cache.sameRRKey e2 e) = true
  · rw [hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hans2, hsame2⟩ := hcond
    obtain ⟨hane2, hle2, _hmono2⟩ := hwf e2 he2
    obtain ⟨a2, ha2⟩ := Option.isSome_iff_exists.mp hane2
    obtain ⟨hf2, hne2, hcov2, hcl2, _hus2⟩ :=
      answerableEntry_matching e2 a2 name qt qc now q t hqn ht hqq hqc hle2 hans2 ha2
    have hmatch2 : a2 ∈ (αCache c).matching (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.matching
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold αCache; simp only [List.mem_filterMap]; exact ⟨e2, Array.mem_def.mp he2, ha2⟩
      · simp only [Bool.and_eq_true]; exact ⟨⟨⟨hf2, hne2⟩, hcov2⟩, hcl2⟩
    have hsk : a2.sameKey a.rr = true := αRR_sameKey e2 e a2 a ha2 ha hsame2
    have hmaxp := (List.all_eq_true.mp hmax) a2 hmatch2
    simp only [hsk, Bool.not_true, Bool.false_or] at hmaxp
    have hrank : a2.cred.rank ≤ a.cred.rank := Nat.le_of_ble_eq_true hmaxp
    have hce : αCred e.credibility = a.cred := by
      have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hce2 : αCred e2.credibility = a2.cred := by
      have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
    rw [hce, hce2] at hord
    exact hord.mpr hrank
  · rw [Bool.not_eq_true] at hcond
    rw [hcond]; rfl

theorem maxRankForKey_of_topServed_maximal (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hlive : Cache.liveEntry e name qt qc now = true)
    (hmax : ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true) :
    c.maxRankForKey e now = true := by
  unfold Cache.DnsCache.maxRankForKey
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro e2 he2
  by_cases hcond : (e2.fresh now && Cache.sameRRKey e2 e) = true
  · rw [hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hfresh2, hsame2⟩ := hcond
    obtain ⟨hane2, hle2, _hmono2⟩ := hwf e2 he2
    obtain ⟨a2, ha2⟩ := Option.isSome_iff_exists.mp hane2
    have hlive2 : Cache.liveEntry e2 name qt qc now = true := by
      have hsk := hsame2
      unfold Cache.sameRRKey at hsk
      simp only [Bool.and_eq_true] at hsk
      obtain ⟨⟨hnm2, htype2⟩, hcls2⟩ := hsk
      have hlv := hlive
      unfold Cache.liveEntry at hlv ⊢
      simp only [Bool.and_eq_true] at hlv ⊢
      obtain ⟨⟨⟨hnm, htype⟩, hcls⟩, _⟩ := hlv
      refine ⟨⟨⟨VeriDNS.Proof.NameTree.nameEqCI_trans hnm2 hnm, ?_⟩, ?_⟩, hfresh2⟩
      · rw [beq_iff_eq] at htype2 htype ⊢; rw [htype2, htype]
      · rw [beq_iff_eq] at hcls2 hcls ⊢; rw [hcls2, hcls]
    obtain ⟨hf2, hne2, hcov2, hcl2⟩ :=
      liveEntry_matching e2 a2 name qt qc now q t hqn ht hqq hqc hle2 hlive2 ha2
    have hmatch2 : a2 ∈ (αCache c).matching (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.matching
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold αCache; simp only [List.mem_filterMap]; exact ⟨e2, Array.mem_def.mp he2, ha2⟩
      · simp only [Bool.and_eq_true]; exact ⟨⟨⟨hf2, hne2⟩, hcov2⟩, hcl2⟩
    have hsk : a2.sameKey a.rr = true := αRR_sameKey e2 e a2 a ha2 ha hsame2
    have hmaxp := (List.all_eq_true.mp hmax) a2 hmatch2
    simp only [hsk, Bool.not_true, Bool.false_or] at hmaxp
    have hrank : a2.cred.rank ≤ a.cred.rank := Nat.le_of_ble_eq_true hmaxp
    have hce : αCred e.credibility = a.cred := by
      have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hce2 : αCred e2.credibility = a2.cred := by
      have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
    rw [hce, hce2] at hord
    exact hord.mpr hrank
  · rw [Bool.not_eq_true] at hcond
    rw [hcond]; rfl

theorem served_maximal_of_maxCredForKey (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hmaxc : c.maxCredForKey e name qt qc now = true) :
    ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true := by
  rw [List.all_eq_true]
  intro a2 ha2mem
  by_cases hsk : a2.sameKey a.rr = true
  · simp only [hsk, Bool.not_true, Bool.false_or]
    unfold VeriDNS.Spec.Net.Cache.matching at ha2mem
    rw [List.mem_filter] at ha2mem
    obtain ⟨hpos2, hpred2⟩ := ha2mem
    obtain ⟨e2, he2, ha2⟩ := mem_αCache_pos c a2 hpos2
    obtain ⟨hane2, hle2, _hmono2⟩ := hwf e2 he2
    by_cases hu2 : a2.cred.usable = true
    · obtain ⟨hcanE2, hvE2⟩ := hcanon e2 he2 a2 ha2
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred2
      obtain ⟨⟨⟨hf2, hne2⟩, hcov2⟩, hcl2⟩ := hpred2
      have hans2 : Cache.answerableEntry e2 name qt qc now = true :=
        matching_answerableEntry e2 a2 name qt qc now q t ht hqq hqc hle2 ha2 hcanE2 hcanN hvE2 hvN
          hf2 hne2 hcov2 hcl2 hu2
      have hsame2 : Cache.sameRRKey e2 e = true := by
        obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
        exact sameKey_sameRRKey e2 e a2 a ha2 ha hcanE2 hcanE hvE2 hvE hsk
      have hmcp := Array.all_eq_true_iff_forall_mem.mp hmaxc e2 he2
      rw [hans2, hsame2, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hmcp
      have hce : αCred e.credibility = a.cred := by
        have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h; rfl
      have hce2 : αCred e2.credibility = a2.cred := by
        have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h; rfl
      have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
      rw [hce, hce2] at hord
      exact Nat.ble_eq.mpr (hord.mp hmcp)
    · have hadd : a2.cred = VeriDNS.Spec.Net.Cred.additional := by
        cases hc : a2.cred with
        | additional => rfl
        | glue => simp [hc, VeriDNS.Spec.Net.Cred.usable] at hu2
        | authority => simp [hc, VeriDNS.Spec.Net.Cred.usable] at hu2
        | authoritative => simp [hc, VeriDNS.Spec.Net.Cred.usable] at hu2
      rw [hadd]; exact Nat.ble_eq.mpr (Nat.zero_le _)
  · rw [Bool.not_eq_true] at hsk
    simp only [hsk, Bool.not_false, Bool.true_or]

theorem topServed_maximal_of_maxRankForKey (c : Cache.DnsCache)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hmaxr : c.maxRankForKey e now = true) :
    ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true := by
  rw [List.all_eq_true]
  intro a2 ha2mem
  by_cases hsk : a2.sameKey a.rr = true
  · simp only [hsk, Bool.not_true, Bool.false_or]
    unfold VeriDNS.Spec.Net.Cache.matching at ha2mem
    rw [List.mem_filter] at ha2mem
    obtain ⟨hpos2, hpred2⟩ := ha2mem
    obtain ⟨e2, he2, ha2⟩ := mem_αCache_pos c a2 hpos2
    obtain ⟨_hane2, hle2, _hmono2⟩ := hwf e2 he2
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred2
    obtain ⟨⟨⟨hf2, _hne2⟩, _hcov2⟩, _hcl2⟩ := hpred2
    have hfresh2 : e2.fresh now = true := (αCacheRR_fresh e2 a2 now hle2 ha2).trans hf2
    have hsame2 : Cache.sameRRKey e2 e = true := by
      obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
      obtain ⟨hcanE2, hvE2⟩ := hcanon e2 he2 a2 ha2
      exact sameKey_sameRRKey e2 e a2 a ha2 ha hcanE2 hcanE hvE2 hvE hsk
    have hmrp := Array.all_eq_true_iff_forall_mem.mp hmaxr e2 he2
    rw [show (e2.fresh now && Cache.sameRRKey e2 e) = true from by rw [hfresh2, hsame2]; rfl,
        Bool.not_true, Bool.false_or, decide_eq_true_eq] at hmrp
    have hce : αCred e.credibility = a.cred := by
      have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hce2 : αCred e2.credibility = a2.cred := by
      have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
    rw [hce, hce2] at hord
    exact Nat.ble_eq.mpr (hord.mp hmrp)
  · rw [Bool.not_eq_true] at hsk
    simp only [hsk, Bool.not_false, Bool.true_or]

theorem cond_eq (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (he : e ∈ c.records) (a : VeriDNS.Spec.Net.CacheRR) (ha : αCacheRR e = some a) :
    (Cache.answerableEntry e name qt qc now && c.maxCredForKey e name qt qc now)
      = ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
            && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && (a.cred.usable && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank))) := by
  obtain ⟨hane, hle, hmono⟩ := hwf e he
  obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hans, hmaxc⟩
    obtain ⟨hf, hne, hcov, hcl, hus⟩ :=
      answerableEntry_matching e a name qt qc now q t hqn ht hqq hqc hle hans ha
    exact ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩, hus, served_maximal_of_maxCredForKey c name qt qc now q t ht hqq
      hqc hcanN hvN hwf hcanon hused e a he ha hmaxc⟩
  · rintro ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩, hus, hmax⟩
    exact ⟨matching_answerableEntry e a name qt qc now q t ht hqq hqc hle ha hcanE hcanN hvE hvN
        hf hne hcov hcl hus,
      maxCredForKey_of_served_maximal c name qt qc now q t hqn ht hqq hqc hwf hused e a he ha hmax⟩

theorem cond_eq_top (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (he : e ∈ c.records) (a : VeriDNS.Spec.Net.CacheRR) (ha : αCacheRR e = some a) :
    (Cache.liveEntry e name qt qc now && c.maxRankForKey e now)
      = ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
            && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) := by
  obtain ⟨hane, hle, hmono⟩ := hwf e he
  obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hlive, hmaxr⟩
    obtain ⟨hf, hne, hcov, hcl⟩ :=
      liveEntry_matching e a name qt qc now q t hqn ht hqq hqc hle hlive ha
    exact ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩,
      topServed_maximal_of_maxRankForKey c now q hwf hcanon hused e a he ha hmaxr⟩
  · rintro ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩, hmax⟩
    have hlive := matching_liveEntry e a name qt qc now q t ht hqq hqc hle ha hcanE hcanN hvE hvN
      hf hne hcov hcl
    exact ⟨hlive,
      maxRankForKey_of_topServed_maximal c name qt qc now q t hqn ht hqq hqc hwf hused e a he ha hlive hmax⟩

theorem αName_rrRdata_of_ns (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : VeriDNS.Spec.Net.Name)
    (harr : αRR rr = some r) (hns : r.rdata = VeriDNS.Spec.Net.RData.ns h) :
    αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some h := by
  unfold αRR at harr
  split at harr
  · rename_i owner rdata cls hn hrd hcl
    injection harr with harr
    have hrdata : rdata = VeriDNS.Spec.Net.RData.ns h := by rw [← harr] at hns; exact hns
    rw [hrdata] at hrd
    show αName rr.rdata = some h
    unfold αRData at hrd
    split at hrd
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨na, hna, hx⟩ := hrd
      injection hx with hx; subst hx; exact hna
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · exact absurd (αSoa_rtype hrd) (by simp [VeriDNS.Spec.Net.RData.rtype])
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · simp at hrd
  · simp at harr

theorem hone_of_CacheWf (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcut_ne : (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = false) :
    ∃ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
      (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none := by
  obtain ⟨rr, hrr⟩ := Array.exists_mem_of_ne_empty
    (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now) (by simpa using hcut_ne)
  have hns := mem_lookupTopCred_rrType c cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now rr hrr
  obtain ⟨e, he, hrd, htp⟩ := mem_lookupTopCred_entry c cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now rr hrr
  obtain ⟨ce, hce⟩ := Option.isSome_iff_exists.mp (hwf e he).1
  have harr := αCacheRR_rr hce
  have hrt := αRR_rtype e.rr ce.rr harr
  have hetype : e.rr.type = BitVec.ofNat 16 2 := by
    have h2 : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) e.rr == BitVec.ofNat 16 2) = true := by
      rw [← htp]; exact hns
    exact eq_of_beq h2
  obtain ⟨h, hh⟩ : ∃ h, ce.rr.rdata = VeriDNS.Spec.Net.RData.ns h := by
    have hard := αRR_rdata e.rr ce.rr harr
    rw [hetype] at hard
    obtain ⟨host, -, hh⟩ := αRData_ns_inv hard
    exact ⟨host, hh⟩
  refine ⟨rr, by simpa using hrr, ?_⟩
  rw [if_pos hns, hrd, αName_rrRdata_of_ns e.rr ce.rr h harr hh]
  simp

theorem hhost_of_rdata_canonical (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (hrdcanon : ∀ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2) = true →
        ∃ na, αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some na
          ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
            = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    ∀ n ∈ ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).toList,
      ∃ qn, αName n = some qn ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63)
        ∧ qn.length ≤ 127 := by
  intro n hn
  rw [Array.toList_filterMap, List.mem_filterMap] at hn
  obtain ⟨rr, hrr, hsome⟩ := hn
  split at hsome
  · rename_i hns'
    rw [Option.some.injEq] at hsome
    subst hsome
    exact hrdcanon rr hrr hns'
  · exact absurd hsome (by simp)

def CacheNsCanon (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.records.toList, e.rr.type = BitVec.ofNat 16 2 →
    ∃ na, αName e.rr.rdata = some na
      ∧ e.rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
      ∧ na.length ≤ 127

theorem hrdcanon_of_CacheNsCanon (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (h : CacheNsCanon c) :
    ∀ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
      (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2) = true →
      ∃ na, αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some na
        ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
            = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127 := by
  intro rr hmem hns
  rw [Cache.DnsCache.lookupTopCred, Array.toList_filterMap, List.mem_filterMap] at hmem
  obtain ⟨e, he, hsome⟩ := hmem
  split at hsome
  · rw [Option.some.injEq] at hsome
    subst hsome
    have hb : (e.rr.type == BitVec.ofNat 16 2) = true := hns
    have htype : e.rr.type = BitVec.ofNat 16 2 := by simpa using hb
    exact h e he htype
  · exact absurd hsome (by simp)

def CacheCnameCanon (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.records.toList, e.rr.type = BitVec.ofNat 16 5 →
    ∃ na, αName e.rr.rdata = some na
      ∧ e.rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
      ∧ na.length ≤ 127

theorem cname_rdata_canonical_of_CacheCnameCanon (c : Cache.DnsCache) (sname : ByteArray)
    (qc : BitVec 16) (now : UInt32) (h : CacheCnameCanon c) :
    ∀ rr ∈ (VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) c sname (5 : BitVec 16) qc now).toList,
      ∃ na, αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some na
        ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
            = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127 := by
  intro rr hmem
  rw [show VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) c sname (5 : BitVec 16) qc now
      = c.lookupAnswerable sname (5 : BitVec 16) qc now from rfl,
    Cache.DnsCache.lookupAnswerable, Array.toList_filterMap, List.mem_filterMap] at hmem
  obtain ⟨e, he, hsome⟩ := hmem
  split at hsome
  · rename_i hcond
    rw [Option.some.injEq] at hsome
    subst hsome
    have hcond' := hcond
    unfold VeriDNS.Impl.Cache.answerableEntry VeriDNS.Impl.Cache.liveEntry at hcond'
    simp only [Bool.and_eq_true] at hcond'
    have htyb : (e.rr.type == (5 : BitVec 16)) = true := hcond'.1.1.1.1.2
    have htype : e.rr.type = BitVec.ofNat 16 5 := by simpa using htyb
    exact h e he htype
  · exact absurd hsome (by simp)

theorem CacheNsCanon_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsCanon c)
    (hnew : rr.type = BitVec.ofNat 16 2 →
      ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127) :
    CacheNsCanon (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := rfl
    intro e he hetype
    rw [hrec, Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [Array.toList_filter] at he
      exact h e (List.mem_filter.mp he).1 hetype
    · exact hnew hetype

theorem CacheCnameCanon_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheCnameCanon c)
    (hnew : rr.type = BitVec.ofNat 16 5 →
      ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127) :
    CacheCnameCanon (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := rfl
    intro e he hetype
    rw [hrec, Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [Array.toList_filter] at he
      exact h e (List.mem_filter.mp he).1 hetype
    · exact hnew hetype

theorem CacheNsCanon_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheNsCanon cache →
      (∀ bytes ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 2 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) →
      CacheNsCanon (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) := by
  intro l
  induction l with
  | nil => intro cache hc _; exact hc
  | cons b bs ih =>
    intro cache hc hraw
    rw [List.foldl_cons]
    apply ih
    · cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => simp only [hp]; exact hc
      | some rr =>
        simp only [hp]
        exact CacheNsCanon_storeChecked cache rr cred now hc (hraw b (List.mem_cons_self ..) rr hp)
    · intro bytes hb rr hp; exact hraw bytes (List.mem_cons_of_mem _ hb) rr hp

theorem CacheCnameCanon_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheCnameCanon cache →
      (∀ bytes ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 5 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) →
      CacheCnameCanon (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) := by
  intro l
  induction l with
  | nil => intro cache hc _; exact hc
  | cons b bs ih =>
    intro cache hc hraw
    rw [List.foldl_cons]
    apply ih
    · cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => simp only [hp]; exact hc
      | some rr =>
        simp only [hp]
        exact CacheCnameCanon_storeChecked cache rr cred now hc (hraw b (List.mem_cons_self ..) rr hp)
    · intro bytes hb rr hp; exact hraw bytes (List.mem_cons_of_mem _ hb) rr hp

theorem CacheNsCanon_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 2 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheNsCanon (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheNsCanon_foldl_storeChecked cred now raws.toList cache h hraw

theorem CacheCnameCanon_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheCnameCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 5 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheCnameCanon (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheCnameCanon_foldl_storeChecked cred now raws.toList cache h hraw

theorem CacheNsCanon_cacheUnlessTruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 2 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheNsCanon (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]
    exact CacheNsCanon_cacheRRs cache _ cred now h
      (VeriDNS.Proof.NameTree.normRaws_forall_transfer (fun _ _ hP => hP) hraw)

theorem CacheCnameCanon_cacheUnlessTruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheCnameCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 5 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheCnameCanon (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]
    exact CacheCnameCanon_cacheRRs cache _ cred now h
      (VeriDNS.Proof.NameTree.normRaws_forall_transfer (fun _ _ hP => hP) hraw)

def CacheNsDistinct (c : Cache.DnsCache) : Prop :=
  c.records.toList.Pairwise (fun e1 e2 =>
    ¬(e1.rr.type = BitVec.ofNat 16 2 ∧ e2.rr.type = BitVec.ofNat 16 2
      ∧ (VeriDNS.Impl.DomainName.nameEqCI e1.rr.name e2.rr.name) = true
      ∧ e1.rr.class = e2.rr.class ∧ e1.rr.rdata = e2.rr.rdata))

theorem CacheNsDistinct_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsDistinct c) :
    CacheNsDistinct (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := rfl
    show (((c.store rr now cred).records).toList).Pairwise _
    rw [hrec, Array.toList_push, List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [Array.toList_filter]
      exact h.filter _
    · intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      rw [Array.toList_filter, List.mem_filter] at ha
      obtain ⟨_, hap⟩ := ha
      rintro ⟨ht_a, ht_rr, hname, hclass, hrdata⟩
      have e1 : VeriDNS.Impl.DomainName.nameEqCI a.rr.name rr.name = true := hname
      have e2 : a.rr.type = rr.type := ht_a.trans ht_rr.symm
      have e3 : a.rr.class = rr.class := hclass
      have e4 : a.rr.rdata = rr.rdata := hrdata
      rw [e1, e2, e3, e4] at hap
      simp at hap
      have hself : (rr.rdata == rr.rdata) = true := by
        show ByteArray.beq rr.rdata rr.rdata = true
        unfold ByteArray.beq; simp
      rw [hself] at hap
      exact absurd hap.2 (by simp)

theorem CacheNsDistinct_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheNsDistinct cache →
      CacheNsDistinct (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) := by
  intro l
  induction l with
  | nil => intro cache hc; exact hc
  | cons b bs ih =>
    intro cache hc
    rw [List.foldl_cons]
    apply ih
    cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => simp only [hp]; exact hc
    | some rr => simp only [hp]; exact CacheNsDistinct_storeChecked cache rr cred now hc

theorem CacheNsDistinct_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsDistinct cache) :
    CacheNsDistinct (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheNsDistinct_foldl_storeChecked cred now raws.toList cache h

theorem CacheNsDistinct_cacheUnlessTruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsDistinct cache) :
    CacheNsDistinct (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]; exact CacheNsDistinct_cacheRRs cache _ cred now h

theorem CacheNsDistinct_absorb (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray) (now : UInt32)
    (h : CacheNsDistinct cache) :
    CacheNsDistinct (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
        (VeriDNS.Impl.Resolver.credAuthority (resp.header.aa == 1)) now)
      resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
      VeriDNS.Impl.Resolver.credAdditional now) :=
  CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _
    (CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ h)

theorem nodup_filterMap_of_pairwise {α β : Type} (l : List α) (f : α → Option β)
    (h : l.Pairwise (fun a b => ∀ x, f a = some x → f b = some x → False)) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hhead, htail⟩ := h
    cases hfa : f a with
    | none => simp only [List.filterMap_cons, hfa]; exact ih htail
    | some b =>
      simp only [List.filterMap_cons, hfa, List.nodup_cons]
      refine ⟨?_, ih htail⟩
      intro hmem
      rw [List.mem_filterMap] at hmem
      obtain ⟨a', ha', hfa'⟩ := hmem
      exact hhead a' ha' b hfa hfa'

theorem hnd_of_CacheNsDistinct (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (h : CacheNsDistinct c) :
    ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).toList.Nodup := by
  rw [Array.toList_filterMap, Cache.DnsCache.lookupTopCred, Array.toList_filterMap,
      List.filterMap_filterMap]
  apply nodup_filterMap_of_pairwise
  have unpack : ∀ e : Cache.CacheEntry, ∀ y,
      ((if VeriDNS.Impl.Cache.liveEntry e cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
            && c.maxRankForKey e now then
          some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } else none).bind
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)) = some y →
      VeriDNS.Impl.DomainName.nameEqCI e.rr.name cut = true ∧ e.rr.type = BitVec.ofNat 16 2
        ∧ e.rr.class = BitVec.ofNat 16 1 ∧ y = e.rr.rdata := by
    intro e y hy
    by_cases hcond : (VeriDNS.Impl.Cache.liveEntry e cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
        && c.maxRankForKey e now) = true
    · rw [if_pos hcond, Option.bind_some] at hy
      rw [Bool.and_eq_true] at hcond
      obtain ⟨hlive, _⟩ := hcond
      unfold VeriDNS.Impl.Cache.liveEntry at hlive
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hlive
      obtain ⟨⟨⟨hn, ht⟩, hcl⟩, _⟩ := hlive
      have hte : e.rr.type = BitVec.ofNat 16 2 := by simpa using ht
      have hcle : e.rr.class = BitVec.ofNat 16 1 := by simpa using hcl
      rw [if_pos (by show (e.rr.type == BitVec.ofNat 16 2) = true; rw [hte]; simp)] at hy
      rw [Option.some.injEq] at hy
      exact ⟨hn, hte, hcle, hy.symm⟩
    · rw [if_neg hcond, Option.bind_none] at hy
      exact absurd hy (by simp)
  refine List.Pairwise.imp ?_ h
  intro e1 e2 hne x hx1 hx2
  obtain ⟨hn1, ht1, hcl1, hy1⟩ := unpack e1 x hx1
  obtain ⟨hn2, ht2, hcl2, hy2⟩ := unpack e2 x hx2
  exact hne ⟨ht1, ht2, VeriDNS.Proof.NameTree.nameEqCI_trans hn1 (VeriDNS.Proof.NameTree.nameEqCI_symm hn2), hcl1.trans hcl2.symm, hy1 ▸ hy2⟩

theorem CacheNsCanon_empty : CacheNsCanon Cache.DnsCache.empty := by
  intro e he _
  simp [Cache.DnsCache.empty] at he

theorem CacheCnameCanon_empty : CacheCnameCanon Cache.DnsCache.empty := by
  intro e he _
  simp [Cache.DnsCache.empty] at he

theorem CacheNsDistinct_empty : CacheNsDistinct Cache.DnsCache.empty := by
  show (Cache.DnsCache.empty.records.toList).Pairwise _
  simp [Cache.DnsCache.empty]

theorem CacheNsCanon_boundExpiryClasses (c : Cache.DnsCache) (h : CacheNsCanon c) :
    CacheNsCanon c.boundExpiryClasses := by
  intro e he htype
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1 htype

theorem CacheCnameCanon_boundExpiryClasses (c : Cache.DnsCache) (h : CacheCnameCanon c) :
    CacheCnameCanon c.boundExpiryClasses := by
  intro e he htype
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1 htype

theorem CacheNsDistinct_boundExpiryClasses (c : Cache.DnsCache) (h : CacheNsDistinct c) :
    CacheNsDistinct c.boundExpiryClasses := by
  show (c.boundExpiryClasses.records.toList).Pairwise _
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter]
  exact h.filter _

theorem αCacheRR_touchEntry (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (e : Cache.CacheEntry) : αCacheRR (Cache.touchEntry ks tnow e) = αCacheRR e := by
  rcases Cache.touchEntry_cases ks tnow e with h | h
  · rw [h]
  · rw [h]; rfl

theorem αNegRR_touchNegEntry (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (e : Cache.NegativeEntry) : αNegRR (Cache.touchNegEntry ks tnow e) = αNegRR e := by
  rcases Cache.touchNegEntry_cases ks tnow e with h | h
  · rw [h]
  · rw [h]; rfl

theorem αCache_touchKeys (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) : αCache (c.touchKeys ks tnow) = αCache c := by
  unfold αCache
  rw [Cache.touchKeys_records, Cache.touchKeys_negatives, Array.toList_map, Array.toList_map,
    List.filterMap_map, List.filterMap_map,
    show αCacheRR ∘ Cache.touchEntry ks tnow = αCacheRR from
      funext (αCacheRR_touchEntry ks tnow),
    show αNegRR ∘ Cache.touchNegEntry ks tnow = αNegRR from
      funext (αNegRR_touchNegEntry ks tnow)]

theorem CacheNsCanon_touchKeys (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheNsCanon c) : CacheNsCanon (c.touchKeys ks tnow) := by
  intro e he htype
  rw [Cache.touchKeys_records, Array.toList_map, List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  rw [Cache.touchEntry_rr] at htype ⊢
  exact h e₀ he₀ htype

theorem CacheCnameCanon_touchKeys (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheCnameCanon c) : CacheCnameCanon (c.touchKeys ks tnow) := by
  intro e he htype
  rw [Cache.touchKeys_records, Array.toList_map, List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  rw [Cache.touchEntry_rr] at htype ⊢
  exact h e₀ he₀ htype

theorem CacheNsDistinct_touchKeys (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheNsDistinct c) : CacheNsDistinct (c.touchKeys ks tnow) := by
  show ((c.touchKeys ks tnow).records.toList).Pairwise _
  rw [Cache.touchKeys_records, Array.toList_map, List.pairwise_map]
  exact h.imp fun hne => by simpa only [Cache.touchEntry_rr] using hne

theorem CacheNsCanon_boundLruKeys (c : Cache.DnsCache) (h : CacheNsCanon c) :
    CacheNsCanon c.boundLruKeys := by
  intro e he htype
  unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1 htype

theorem CacheCnameCanon_boundLruKeys (c : Cache.DnsCache) (h : CacheCnameCanon c) :
    CacheCnameCanon c.boundLruKeys := by
  intro e he htype
  unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1 htype

theorem CacheNsDistinct_boundLruKeys (c : Cache.DnsCache) (h : CacheNsDistinct c) :
    CacheNsDistinct c.boundLruKeys := by
  show (c.boundLruKeys.records.toList).Pairwise _
  unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  rw [hp, Array.toList_filter]
  exact h.filter _

theorem αCache_boundLruKeys_pos_subset (c : Cache.DnsCache) {e : VeriDNS.Spec.Net.CacheRR}
    (he : e ∈ (αCache c.boundLruKeys).pos) : e ∈ (αCache c).pos := by
  simp only [αCache, List.mem_filterMap] at he ⊢
  obtain ⟨entry, hmem, hα⟩ := he
  unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys at hmem
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at hmem
  exact ⟨entry, hmem.1, hα⟩

theorem CacheNsCanon_boundLru (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheNsCanon c) : CacheNsCanon (c.boundLru ks tnow) :=
  CacheNsCanon_boundLruKeys _ (CacheNsCanon_touchKeys c ks tnow h)

theorem CacheCnameCanon_boundLru (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheCnameCanon c) : CacheCnameCanon (c.boundLru ks tnow) :=
  CacheCnameCanon_boundLruKeys _ (CacheCnameCanon_touchKeys c ks tnow h)

theorem CacheNsDistinct_boundLru (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheNsDistinct c) : CacheNsDistinct (c.boundLru ks tnow) :=
  CacheNsDistinct_boundLruKeys _ (CacheNsDistinct_touchKeys c ks tnow h)

theorem αCache_boundLru_pos_subset (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) {e : VeriDNS.Spec.Net.CacheRR}
    (he : e ∈ (αCache (c.boundLru ks tnow)).pos) : e ∈ (αCache c).pos := by
  have h1 : e ∈ (αCache (c.touchKeys ks tnow).boundLruKeys).pos := he
  have h2 := αCache_boundLruKeys_pos_subset (c.touchKeys ks tnow) h1
  rwa [αCache_touchKeys] at h2



theorem rrclass_eq_of_beq {x y : RRClass} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem sameKey_refl (ce : VeriDNS.Spec.Net.CacheRR) : ce.sameKey ce.rr = true := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey
  rw [nameEq_of_mapfold _ _ rfl, rrtype_beq_self, rrclass_beq_self]
  rfl

theorem sameKey_respects {a b : VeriDNS.Spec.Net.CacheRR} (h : a.sameKey b.rr = true)
    (x : VeriDNS.Spec.Net.CacheRR) : x.sameKey a.rr = x.sameKey b.rr := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at h ⊢
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hn, ht⟩, hc⟩ := h
  have hmap := mapfold_of_nameEq _ _ hn
  rw [rrtype_eq_of_beq ht, rrclass_eq_of_beq hc]
  congr 1
  by_cases hx : VeriDNS.Spec.Net.nameEq x.rr.owner a.rr.owner = true
  · rw [hx, nameEq_of_mapfold _ _ ((mapfold_of_nameEq _ _ hx).trans hmap)]
  · rw [Bool.not_eq_true] at hx
    rw [hx]
    cases hxb : VeriDNS.Spec.Net.nameEq x.rr.owner b.rr.owner with
    | false => rfl
    | true =>
      have := nameEq_of_mapfold _ _ ((mapfold_of_nameEq _ _ hxb).trans hmap.symm)
      rw [this] at hx
      cases hx

theorem sameRRKey_rrKey_eq {e₁ e₂ : Cache.CacheEntry}
    (h : Cache.sameRRKey e₁ e₂ = true) :
    VeriDNS.Impl.Cache.rrKey e₁ = VeriDNS.Impl.Cache.rrKey e₂ := by
  unfold Cache.sameRRKey at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hn, ht⟩, hc⟩ := h
  unfold VeriDNS.Impl.Cache.rrKey VeriDNS.Impl.Cache.demandKey
  rw [VeriDNS.Proof.NameTree.nameEqCI_iff.mp hn, eq_of_beq ht, eq_of_beq hc]

theorem αCacheRR_canonical {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR}
    (hα : αCacheRR e = some ce) (hwf : VeriDNS.Proof.NameTree.WfRR e.rr) :
    e.rr.name = DomainName.labelsToWireFormatGo ce.rr.owner
      ∧ ∀ x ∈ ce.rr.owner, x.size ≤ 63 := by
  have howner : αName e.rr.name = some ce.rr.owner :=
    (αRR_fields _ _ (αCacheRR_rr hα)).1
  obtain ⟨⟨labels, hval, -, hname⟩, -⟩ := hwf
  have h2 : αName e.rr.name = some labels.toList := by
    rw [hname]; exact αName_labelsToWireFormat labels hval
  have howl : ce.rr.owner = labels.toList := by
    rw [howner] at h2; exact Option.some.inj h2
  refine ⟨?_, fun x hx => (αName_valid howner x hx).2⟩
  rw [howl, hname]
  rfl

theorem αCache_boundLruKeys_pos_filter (c : Cache.DnsCache)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      (αCache c.boundLruKeys).pos = (αCache c).pos.filter qf
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.sameKey ce₂.rr = true → qf ce₁ = qf ce₂) := by
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  refine ⟨fun ce => (VeriDNS.Impl.Cache.evictLruKeys c.records c.records.size).any
      (fun e' => match αCacheRR e' with
        | some ce' => ce'.sameKey ce.rr
        | none => false), ?_, ?_⟩
  · show (c.boundLruKeys.records).toList.filterMap αCacheRR
      = ((c.records).toList.filterMap αCacheRR).filter _
    unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys
    rw [hp, Array.toList_filter]
    apply filterMap_filter_comm
    intro entry hentry ce hce
    have hentryA : entry ∈ c.records := Array.mem_def.mpr hentry
    by_cases hr : p (VeriDNS.Impl.Cache.rrKey entry) = true
    · rw [hr]
      symm
      rw [← Array.any_toList]
      apply List.any_eq_true.mpr
      refine ⟨entry, Array.mem_def.mp (Array.mem_filter.mpr ⟨hentryA, hr⟩), ?_⟩
      simp only [hce]
      exact sameKey_refl ce
    · rw [Bool.not_eq_true] at hr
      rw [hr]
      symm
      apply Bool.eq_false_iff.mpr
      intro hq
      rw [← Array.any_toList] at hq
      obtain ⟨e', he'L, hpred⟩ := List.any_eq_true.mp hq
      obtain ⟨he'A, hre'⟩ := Array.mem_filter.mp (Array.mem_def.mpr he'L)
      revert hpred
      cases hα' : αCacheRR e' with
      | none => intro hpred; cases hpred
      | some ce' =>
        intro hpred
        have hsk : ce'.sameKey ce.rr = true := hpred
        obtain ⟨hcan', hv'⟩ := αCacheRR_canonical hα' (hwfrr e' he'A)
        obtain ⟨hcanE, hvE⟩ := αCacheRR_canonical hce (hwfrr entry hentryA)
        have hrr : Cache.sameRRKey e' entry = true :=
          sameKey_sameRRKey e' entry ce' ce hα' hce hcan' hcanE hv' hvE hsk
        have hpp : p (VeriDNS.Impl.Cache.rrKey e') = p (VeriDNS.Impl.Cache.rrKey entry) := by
          rw [sameRRKey_rrKey_eq hrr]
        rw [hpp, hr] at hre'
        cases hre'
  · intro ce₁ ce₂ hk
    have hfun : (fun e' => match αCacheRR e' with
        | some ce' => ce'.sameKey ce₁.rr
        | none => false)
      = (fun e' => match αCacheRR e' with
        | some ce' => ce'.sameKey ce₂.rr
        | none => false) := by
      funext e'
      cases αCacheRR e' with
      | none => rfl
      | some ce' => exact sameKey_respects hk ce'
    simp only [hfun]

theorem αCache_boundLruKeys_eq (c : Cache.DnsCache)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      αCache c.boundLruKeys
        = { pos := (αCache c).pos.filter qf, neg := (αCache c).neg }
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.sameKey ce₂.rr = true → qf ce₁ = qf ce₂) := by
  obtain ⟨qf, hpos, hkey⟩ := αCache_boundLruKeys_pos_filter c hwfrr
  refine ⟨qf, ?_, hkey⟩
  have hneg : (αCache c.boundLruKeys).neg = (αCache c).neg := rfl
  cases hαbe : αCache c.boundLruKeys with
  | mk pos neg =>
    have hp : pos = (αCache c).pos.filter qf := by rw [← hpos, hαbe]
    have hn : neg = (αCache c).neg := by rw [← hneg, hαbe]
    rw [hp, hn]

theorem αCache_boundLru_eq (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      αCache (c.boundLru ks tnow)
        = { pos := (αCache c).pos.filter qf, neg := (αCache c).neg }
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.sameKey ce₂.rr = true → qf ce₁ = qf ce₂) := by
  have hwfrr' : ∀ e ∈ (c.touchKeys ks tnow).records, VeriDNS.Proof.NameTree.WfRR e.rr := by
    intro e he
    rw [VeriDNS.Impl.Cache.touchKeys_records] at he
    obtain ⟨e₀, he₀, rfl⟩ := Array.mem_map.mp he
    rw [VeriDNS.Impl.Cache.touchEntry_rr]
    exact hwfrr e₀ he₀
  obtain ⟨qf, heq, hkey⟩ := αCache_boundLruKeys_eq (c.touchKeys ks tnow) hwfrr'
  rw [αCache_touchKeys] at heq
  exact ⟨qf, heq, hkey⟩

theorem αCache_boundLru_noop (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : c.records.size ≤ Cache.DnsCache.capacity) :
    αCache (c.boundLru ks tnow) = αCache c := by
  show αCache ((c.touchKeys ks tnow).boundLruKeys) = αCache c
  rw [VeriDNS.Proof.Cache.boundLruKeys_noop _ (by
      rw [VeriDNS.Impl.Cache.touchKeys_records, Array.size_map]; exact h),
    αCache_touchKeys]

theorem isEmpty_filterMap_of_all_isSome {α β : Type} (l : List α) (f : α → Option β)
    (h : ∀ x ∈ l, (f x).isSome = true) : (l.filterMap f).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons a t =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    simp [List.filterMap_cons, hb]

theorem filterMap_flatMap {α β γ : Type} (l : List α) (g : α → List β) (h : β → Option γ) :
    (l.flatMap g).filterMap h = l.flatMap (fun x => (g x).filterMap h) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, List.filterMap_append, ih]

theorem filterMap_then_flatMap {α β γ : Type} (l : List α) (f : α → Option β) (g : β → List γ) :
    (l.filterMap f).flatMap g = l.flatMap (fun x => (f x).elim [] g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hf : f a with
    | none => simp [List.filterMap_cons, hf, List.flatMap_cons, ih]
    | some b => simp [List.filterMap_cons, hf, List.flatMap_cons, ih]

theorem filterMap_map_comm {α β γ : Type} (l : List α) (f : α → Option β) (g : β → γ) :
    (l.filterMap f).map g = l.filterMap (fun x => (f x).map g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hf : f a with
    | none => simp [List.filterMap_cons, hf, ih]
    | some b => simp [List.filterMap_cons, hf, ih]

theorem mkGlue_keyed (aRRs : Array VeriDNS.Spec.ResourceRecord) (m : ByteArray) :
    ∀ gp ∈ ((aRRs.filterMap (fun rr =>
        if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
          some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
            (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
        else none)).toList), gp.1 = m := by
  intro gp hgp
  rw [Array.toList_filterMap, List.mem_filterMap] at hgp
  obtain ⟨rr, _, heq⟩ := hgp
  by_cases hsz : ((VeriDNS.Spec.RRParse.rrRdata rr).size == 4) = true
  · rw [if_pos hsz] at heq; injection heq with heq; rw [← heq]
  · rw [if_neg hsz] at heq; exact absurd heq.symm (by simp)

theorem impl_glue_per_name_model (aRRs : Array VeriDNS.Spec.ResourceRecord) (n : ByteArray) :
    (((aRRs.filterMap (fun rr =>
        if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
          some (n, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
            (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
        else none)).toList.map Prod.snd).map
      (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))
      = aRRs.toList.filterMap (fun rr =>
          (αIPv4 (VeriDNS.Spec.RRParse.rrRdata rr)).map (fun ip => ip.toDotted)) := by
  rw [Array.toList_filterMap, List.map_map, filterMap_map_comm]
  apply filterMap_congr_mem
  intro rr _
  rw [a_extract_reconcile]
  by_cases hsz : ((VeriDNS.Spec.RRParse.rrRdata rr).size == 4) = true
  · simp [hsz, Function.comp_apply]
  · simp only [Bool.not_eq_true] at hsz; simp [hsz]

theorem byteArray_beq_iff_eq {a b : ByteArray} : (a == b) = true ↔ a = b := by
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

theorem flatMap_indicator_self {α β : Type} [BEq α] (l : List α) (n : α) (g : α → List β)
    (hbeq : ∀ a b : α, (a == b) = true ↔ a = b) (hn : n ∈ l) (hnd : l.Nodup) :
    l.flatMap (fun m => if m == n then g m else []) = g n := by
  induction l with
  | nil => exact absurd hn (by simp)
  | cons a t ih =>
    obtain ⟨hat, hnt'⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp hn with rfl | hnt
    · rw [if_pos ((hbeq n n).mpr rfl)]
      have htail : t.flatMap (fun m => if m == n then g m else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro m hm
        rw [if_neg (fun hc => hat (((hbeq m n).mp hc) ▸ hm))]
      rw [htail, List.append_nil]
    · rw [if_neg (fun hc => hat (((hbeq a n).mp hc) ▸ hnt)), List.nil_append]
      exact ih hnt hnt'

theorem keyed_glue_filterMap_self {β : Type} (names : Array ByteArray) (n : ByteArray)
    (h : ByteArray → Array (ByteArray × β))
    (hkey : ∀ m, ∀ gp ∈ (h m).toList, gp.1 = m)
    (hbeq : ∀ a b : ByteArray, (a == b) = true ↔ a = b)
    (hn : n ∈ names.toList) (hnd : names.toList.Nodup) :
    ((names.flatMap h).filterMap (fun gp => if gp.1 == n then some gp.2 else none)).toList
      = (h n).toList.map Prod.snd := by
  rw [Array.toList_filterMap, Array.toList_flatMap, filterMap_flatMap]
  have hperm : (fun m => (h m).toList.filterMap (fun gp => if gp.1 == n then some gp.2 else none))
      = (fun m => if m == n then (h m).toList.map Prod.snd else []) := by
    funext m
    by_cases hmn : (m == n) = true
    · rw [if_pos hmn, ← List.filterMap_eq_map]
      apply filterMap_congr_mem
      intro gp hgp
      simp [hkey m gp hgp, hmn, Function.comp_apply]
    · rw [if_neg hmn]
      apply List.filterMap_eq_nil_iff.mpr
      intro gp hgp
      rw [hkey m gp hgp, if_neg hmn]
  rw [hperm]
  exact flatMap_indicator_self names.toList n (fun m => (h m).toList.map Prod.snd) hbeq hn hnd

theorem flatMap_glue_keyed {α β : Type} (l : List α) (h : α → List (ByteArray × β)) (n : ByteArray)
    (key : α → ByteArray) (hkey : ∀ m, ∀ gp ∈ h m, gp.1 = key m) :
    (l.flatMap h).filterMap (fun gp => if VeriDNS.Impl.DomainName.nameEqCI gp.1 n then some gp.2 else none)
      = l.flatMap (fun m =>
          if VeriDNS.Impl.DomainName.nameEqCI (key m) n then (h m).map Prod.snd else []) := by
  rw [filterMap_flatMap]
  congr 1
  funext m
  by_cases hk : VeriDNS.Impl.DomainName.nameEqCI (key m) n = true
  · rw [if_pos hk, ← List.filterMap_eq_map]
    apply filterMap_congr_mem
    intro gp hgp
    rw [hkey m gp hgp]; simp [hk]
  · rw [if_neg hk]
    apply List.filterMap_eq_nil_iff.mpr
    intro gp hgp
    rw [hkey m gp hgp]
    simp only [Bool.not_eq_true] at hk
    simp [hk]

def nsGlueByteFlat (names : Array ByteArray) (glue : Array (ByteArray × BitVec 32)) : List String :=
  names.toList.flatMap (fun n =>
    (glue.filterMap (fun gp => if gp.1 == n then some gp.2 else none)).toList.map
      (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))

theorem modelSlistOf_fromNsWithGlueAll (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc)
      = names.toList.flatMap (fun n =>
          (glue.filterMap (fun gp => if DomainName.foldNameCase gp.1 == DomainName.foldNameCase n then some gp.2 else none)).toList.map
            (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll
  dsimp only
  rw [Array.toList_flatMap, filterMap_flatMap]
  congr 1
  funext n
  by_cases hemp : (glue.filterMap (fun gp =>
      if DomainName.foldNameCase gp.1 == DomainName.foldNameCase n then some gp.2 else none)).isEmpty = true
  · rw [if_pos hemp]; simp [Array.isEmpty_iff.mp hemp]
  · rw [if_neg hemp, Array.toList_map, List.filterMap_map]; simp [Function.comp_def]

theorem nsGlueByteFlat_sublist_fold (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    (nsGlueByteFlat names glue).Sublist (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc)) := by
  rw [modelSlistOf_fromNsWithGlueAll]
  unfold nsGlueByteFlat

  have hflat : ∀ (l : List ByteArray) (F G : ByteArray → List String),
      (∀ x ∈ l, (F x).Sublist (G x)) → (l.flatMap F).Sublist (l.flatMap G) := by
    intro l F G h
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons]
      exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))
  have hfm : ∀ {α β : Type} (P Q : α → Option β) (l : List α),
      (∀ a b, P a = some b → Q a = some b) → (List.filterMap P l).Sublist (List.filterMap Q l) := by
    intro α β P Q l h
    induction l with
    | nil => simp
    | cons a t ih =>
      cases hp : P a with
      | none =>
        rw [List.filterMap_cons_none hp]
        cases hq : Q a with
        | none => rw [List.filterMap_cons_none hq]; exact ih
        | some b => rw [List.filterMap_cons_some hq]; exact ih.cons _
      | some b =>
        rw [List.filterMap_cons_some hp, List.filterMap_cons_some (h a b hp)]
        exact ih.cons_cons _
  apply hflat
  intro n _
  refine List.Sublist.map _ ?_
  rw [Array.toList_filterMap, Array.toList_filterMap]
  apply hfm
  intro gp b hgp
  by_cases hbe : (gp.1 == n) = true
  · have heq : gp.1 = n := byteArray_beq_iff_eq.mp hbe
    rw [if_pos hbe] at hgp
    injection hgp with hgpb
    rw [heq, hgpb, if_pos (byteArray_beq_iff_eq.mpr rfl)]
  · rw [if_neg hbe] at hgp; exact absurd hgp (by simp)

theorem findSome?_toList_sublist_filterMap {α β : Type} (p : α → Option β) (l : List α) :
    (l.findSome? p).toList.Sublist (l.filterMap p) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.findSome?_cons, List.filterMap_cons]
    cases hp : p a with
    | none => simp only [hp]; exact ih
    | some b => simp only [hp, Option.toList_some]; exact (List.nil_sublist _).cons_cons b

theorem filterMap_eq_flatMap_toList {α β : Type} (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap (fun a => (f a).toList) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons, List.flatMap_cons, ih]
    cases f a <;> simp

theorem modelSlistOf_fromNsWithGlue_subperm_all (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc mc' : Nat) :
    (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)).Subperm
      (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc')) := by
  rw [modelSlistOf_fromNsWithGlue, modelSlistOf_fromNsWithGlueAll, filterMap_eq_flatMap_toList]
  refine List.Sublist.subperm ?_
  have hflat : ∀ (l : List ByteArray) (F G : ByteArray → List String),
      (∀ x ∈ l, (F x).Sublist (G x)) → (l.flatMap F).Sublist (l.flatMap G) := by
    intro l F G h
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons]
      exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))
  apply hflat
  intro n _

  have hP : (fun (gp : ByteArray × BitVec 32) =>
      if VeriDNS.Impl.DomainName.nameEqCI gp.1 n then some gp.2 else none)
      = (fun gp => if DomainName.foldNameCase gp.1 == DomainName.foldNameCase n then some gp.2 else none) := rfl
  have hom : ∀ (o : Option (BitVec 32)),
      (o.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))).toList
        = o.toList.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)) := by
    intro o; cases o <;> rfl
  rw [hP, hom, ← Array.findSome?_toList, Array.toList_filterMap]
  refine List.Sublist.map _ ?_
  exact findSome?_toList_sublist_filterMap _ _

theorem αIPv4_rrRdata_of_a (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (addr : VeriDNS.Spec.Net.IPv4)
    (harr : αRR rr = some r) (ha : r.rdata = VeriDNS.Spec.Net.RData.a addr) :
    αIPv4 (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some addr := by
  unfold αRR at harr
  split at harr
  · rename_i owner rdata cls hn hrd hcl
    injection harr with harr
    have hrdata : rdata = VeriDNS.Spec.Net.RData.a addr := by rw [← harr] at ha; exact ha
    rw [hrdata] at hrd
    show αIPv4 rr.rdata = some addr
    unfold αRData at hrd
    split at hrd
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, hx1, hx⟩ := hrd
      injection hx with hx; subst hx; exact hx1
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · exact absurd (αSoa_rtype hrd) (by simp [VeriDNS.Spec.Net.RData.rtype])
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · simp at hrd
  · simp at harr

theorem lookupTopCred_ns_eq_nsHostsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns,
      RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList.filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)
      = (αCache c).nsHostsAt (αTime now) q.qname := by
  have ht : αType (BitVec.ofNat 16 2) = some RRType.ns := rfl
  have hqq : q.qtype = VeriDNS.Spec.Net.QType.rr RRType.ns := by rw [hq4]
  have hqc : αClass (BitVec.ofNat 16 1) = some q.qclass := by rw [hq4]; rfl
  rw [lookupTopCred_toList_filterMap]
  unfold VeriDNS.Spec.Net.Cache.nsHostsAt
  rw [show (⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns,
        RRClass.in, false⟩ : VeriDNS.Spec.Net.Query) = q from hq4.symm,
      VeriDNS.Spec.Net.Cache.topServed]
  generalize hsp : (fun (e : VeriDNS.Spec.Net.CacheRR) =>
      ((αCache c).matching (αTime now) q).all
        (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) = sp
  rw [filter_filterMap_eq, VeriDNS.Spec.Net.Cache.matching,
      filter_filterMap_eq, show (αCache c).pos = c.records.toList.filterMap αCacheRR from rfl,
      List.filterMap_filterMap]
  subst hsp
  apply filterMap_congr_mem
  intro e he
  have he' : e ∈ c.records := Array.mem_def.mpr he
  obtain ⟨hane, hle, hmono⟩ := hwf e he'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
  rw [ha, Option.bind_some]
  have hce := cond_eq_top c name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now q
    RRType.ns hqn ht hqq hqc hcanN hvN hwf hcanon hused e he' a ha
  by_cases hgate : (Cache.liveEntry e name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
      && c.maxRankForKey e now) = true
  ·
    have htype : (e.rr.type == BitVec.ofNat 16 2) = true := by
      rw [Bool.and_eq_true] at hgate
      have hl := hgate.1; unfold Cache.liveEntry at hl
      simp only [Bool.and_eq_true] at hl; exact hl.1.1.2

    have harr : αRR e.rr = some a.rr := by
      unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
      obtain ⟨r, hr, rfl⟩ := ha; exact hr
    have hnsrd : ∃ h, a.rr.rdata = VeriDNS.Spec.Net.RData.ns h := by
      have hard := αRR_rdata e.rr a.rr harr
      rw [(show e.rr.type = BitVec.ofNat 16 2 from eq_of_beq htype)] at hard
      obtain ⟨host, -, hh⟩ := αRData_ns_inv hard
      exact ⟨host, hh⟩
    obtain ⟨h, hh⟩ := hnsrd
    rw [if_pos hgate, if_pos (show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord)
          { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } == BitVec.ofNat 16 2)
        = true from htype)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = true := hce ▸ hgate
    rw [Bool.and_eq_true] at hmodel
    obtain ⟨hmp, hsp⟩ := hmodel
    simp only [hmp, hsp, cond_true, hh]
    exact αName_rrRdata_of_ns e.rr a.rr h harr hh
  · rw [Bool.not_eq_true] at hgate
    rw [if_neg (by rw [hgate]; simp)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = false := hce ▸ hgate
    rcases Bool.and_eq_false_iff.mp hmodel with h | h <;> simp [h]

theorem nsHostsAt_empty_of_lookupTopCred_empty (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (he : (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true) :
    ((αCache c).nsHostsAt (αTime now) q.qname).isEmpty = true := by
  have heq := lookupTopCred_ns_eq_nsHostsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused
  rw [← heq]
  have hnil : (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now) = #[] := by
    simpa using he
  rw [hnil]
  rfl

theorem nsHostsAt_nonempty_of_lookupTopCred (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hone : ∃ rr ∈ (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none) :
    ((αCache c).nsHostsAt (αTime now) q.qname).isEmpty = false := by
  have heq := lookupTopCred_ns_eq_nsHostsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused
  rw [← heq]
  obtain ⟨rr, hrr, hg⟩ := hone
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hg
  have hmem : b ∈ (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList.filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) :=
    List.mem_filterMap.mpr ⟨rr, hrr, hb⟩
  cases hl : (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList.filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) with
  | nil => rw [hl] at hmem; exact absurd hmem (by simp)
  | cons x xs => rfl

theorem model_empties_of_impl (c : Cache.DnsCache) (now : UInt32)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (nodes : List ByteArray)
    (hcanonNode : ∀ m ∈ nodes, ∃ na, αName m = some na ∧ m = DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63))
    (himpl_empty : ∀ m ∈ nodes,
        (c.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true) :
    ∀ mm ∈ nodes.map (fun w => (αName w).getD []),
      ((αCache c).nsHostsAt (αTime now) mm).isEmpty = true := by
  intro mm hmm
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hmm
  obtain ⟨na, hαm, hcanM, hvM⟩ := hcanonNode m hm
  rw [show (αName m).getD [] = na from by simp [hαm]]
  exact nsHostsAt_empty_of_lookupTopCred_empty c m now
    ⟨na, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩ hαm rfl hcanM hvM hwf hcanon hused
    (himpl_empty m hm)

theorem walkNs_nsNames_αName_eq_nsHostsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (((c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.filterMap αName)
      = (αCache c).nsHostsAt (αTime now) q.qname := by
  rw [Array.toList_filterMap, List.filterMap_filterMap,
      ← lookupTopCred_ns_eq_nsHostsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused]
  apply filterMap_congr_mem
  intro rr _
  by_cases hrt : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2) = true
  · simp [hrt]
  · simp only [Bool.not_eq_true] at hrt; simp [hrt]

theorem lookupTopCred_a_eq_glueAddrsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupTopCred name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).toList.filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 1
          then (αIPv4 (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)).map
            (fun ip => ip.toDotted)
          else none)
      = (αCache c).glueAddrsAt (αTime now) q.qname := by
  have ht : αType (BitVec.ofNat 16 1) = some RRType.a := rfl
  have hqq : q.qtype = VeriDNS.Spec.Net.QType.rr RRType.a := by rw [hq4]
  have hqc : αClass (BitVec.ofNat 16 1) = some q.qclass := by rw [hq4]; rfl
  rw [lookupTopCred_toList_filterMap]
  unfold VeriDNS.Spec.Net.Cache.glueAddrsAt
  rw [show (⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩
        : VeriDNS.Spec.Net.Query) = q from hq4.symm, VeriDNS.Spec.Net.Cache.topServed]
  generalize hsp : (fun (e : VeriDNS.Spec.Net.CacheRR) =>
      ((αCache c).matching (αTime now) q).all
        (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) = sp
  rw [filter_filterMap_eq, VeriDNS.Spec.Net.Cache.matching,
      filter_filterMap_eq, show (αCache c).pos = c.records.toList.filterMap αCacheRR from rfl,
      List.filterMap_filterMap]
  subst hsp
  apply filterMap_congr_mem
  intro e he
  have he' : e ∈ c.records := Array.mem_def.mpr he
  obtain ⟨hane, hle, hmono⟩ := hwf e he'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
  rw [ha, Option.bind_some]
  have hce := cond_eq_top c name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now q
    RRType.a hqn ht hqq hqc hcanN hvN hwf hcanon hused e he' a ha
  by_cases hgate : (Cache.liveEntry e name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      && c.maxRankForKey e now) = true
  · have htype : (e.rr.type == BitVec.ofNat 16 1) = true := by
      rw [Bool.and_eq_true] at hgate
      have hl := hgate.1; unfold Cache.liveEntry at hl
      simp only [Bool.and_eq_true] at hl; exact hl.1.1.2
    have harr : αRR e.rr = some a.rr := by
      unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
      obtain ⟨r, hr, rfl⟩ := ha; exact hr
    have hard : ∃ addr, a.rr.rdata = VeriDNS.Spec.Net.RData.a addr := by
      have hard0 := αRR_rdata e.rr a.rr harr
      rw [(show e.rr.type = BitVec.ofNat 16 1 from eq_of_beq htype)] at hard0
      obtain ⟨ip, -, hh⟩ := αRData_a_inv hard0
      exact ⟨ip, hh⟩
    obtain ⟨addr, hh⟩ := hard
    rw [if_pos hgate, if_pos (show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord)
          { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } == BitVec.ofNat 16 1)
        = true from htype)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = true := hce ▸ hgate
    rw [Bool.and_eq_true] at hmodel
    obtain ⟨hmp, hsp⟩ := hmodel
    simp only [hmp, hsp, cond_true, hh]
    show (αIPv4 (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) e.rr)).map
        (fun ip => ip.toDotted) = some addr.toDotted
    rw [αIPv4_rrRdata_of_a e.rr a.rr addr harr hh]; rfl
  · rw [Bool.not_eq_true] at hgate
    rw [if_neg (by rw [hgate]; simp)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = false := hce ▸ hgate
    rcases Bool.and_eq_false_iff.mp hmodel with h | h <;> simp [h]

theorem lookupTopCred_a_noguard_eq_glueAddrsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupTopCred name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).toList.filterMap
        (fun rr => (αIPv4 (VeriDNS.Spec.RRParse.rrRdata rr)).map (fun ip => ip.toDotted))
      = (αCache c).glueAddrsAt (αTime now) q.qname := by
  rw [← lookupTopCred_a_eq_glueAddrsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused]
  apply filterMap_congr_mem
  intro rr hrr
  rw [if_pos (mem_lookupTopCred_rrType c name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now rr
    (Array.mem_def.mpr hrr))]

theorem per_host_glue (c : Cache.DnsCache) (now : UInt32) (nsNames : Array ByteArray) (n : ByteArray)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName n = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩)
    (hcanN : n = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hn : n ∈ nsNames.toList) (hnd : nsNames.toList.Nodup) :
    ((nsNames.flatMap (fun m =>
        (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
          if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
            some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
              (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
          else none))).filterMap
        (fun gp => if gp.1 == n then some gp.2 else none)).toList.map
      (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))
      = (αCache c).glueAddrsAt (αTime now) q.qname := by
  rw [keyed_glue_filterMap_self nsNames n
        (fun m => (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
          if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
            some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
              (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
          else none))
        (fun m => mkGlue_keyed _ m) (fun _ _ => byteArray_beq_iff_eq) hn hnd,
      impl_glue_per_name_model (c.lookupTopCred n (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now) n]
  exact lookupTopCred_a_noguard_eq_glueAddrsAt c n now q hqn hq4 hcanN hvN hwf hcanon hused

theorem keystone_glue_assembly (c : Cache.DnsCache) (now : UInt32) (nsNames : Array ByteArray) (mc : Nat)
    (hnd : nsNames.toList.Nodup)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hhost : ∀ n ∈ nsNames.toList, ∃ qn, αName n = some qn
        ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63)) :
    nsGlueByteFlat nsNames
        (nsNames.flatMap (fun m =>
          (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
            if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
              some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
                (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
            else none)))
      = (nsNames.toList.filterMap αName).flatMap ((αCache c).glueAddrsAt (αTime now)) := by
  unfold nsGlueByteFlat
  rw [filterMap_then_flatMap]
  apply flatMap_congr_mem
  intro n hn
  obtain ⟨qn, hqn, hcanN, hvN⟩ := hhost n hn
  rw [hqn]
  exact per_host_glue c now nsNames n ⟨qn, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩
    hqn rfl hcanN hvN hwf hcanon hused hn hnd

theorem referralSlist_base (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (nm : VeriDNS.Spec.Net.Name) (fuel : Nat) (h : (c.nsHostsAt now nm).isEmpty = false) :
    c.referralSlist now nm (fuel + 1) = (c.nsHostsAt now nm).flatMap (c.glueAddrsAt now) := by
  unfold VeriDNS.Spec.Net.Cache.referralSlist
  rw [if_neg (by rw [h]; simp)]

theorem referralSlist_one_hop (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (start cut : VeriDNS.Spec.Net.Name) (fuel : Nat)
    (htail : start.tail = cut) (hstart_ne : start ≠ [])
    (hstart_empty : (c.nsHostsAt now start).isEmpty = true)
    (hcut : (c.nsHostsAt now cut).isEmpty = false) :
    c.referralSlist now start (fuel + 2) = (c.nsHostsAt now cut).flatMap (c.glueAddrsAt now) := by
  obtain ⟨sh, st, rfl⟩ := List.exists_cons_of_ne_nil hstart_ne
  simp only [List.tail_cons] at htail
  subst htail
  unfold VeriDNS.Spec.Net.Cache.referralSlist
  rw [if_pos hstart_empty]
  show c.referralSlist now st (fuel + 1) = (c.nsHostsAt now st).flatMap (c.glueAddrsAt now)
  exact referralSlist_base c now st fuel hcut

theorem referralSlist_ascend (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (cut : VeriDNS.Spec.Net.Name) (hcut : (c.nsHostsAt now cut).isEmpty = false) :
    ∀ (inter : List VeriDNS.Spec.Net.Name) (start : VeriDNS.Spec.Net.Name) (fuel : Nat),
      inter.length + 2 ≤ fuel →
      List.Chain (fun a b => a ≠ [] ∧ a.tail = b) start (inter ++ [cut]) →
      (∀ m ∈ start :: inter, (c.nsHostsAt now m).isEmpty = true) →
      c.referralSlist now start fuel = (c.nsHostsAt now cut).flatMap (c.glueAddrsAt now) := by
  intro inter
  induction inter with
  | nil =>
    intro start fuel hfuel hchain hempty
    rw [List.nil_append] at hchain
    obtain ⟨⟨hne, htail⟩, _⟩ := List.chain_cons.mp hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    exact referralSlist_one_hop c now start cut f htail hne (hempty start (by simp)) hcut
  | cons m rest ih =>
    intro start fuel hfuel hchain hempty
    obtain ⟨⟨hne, htail⟩, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    obtain ⟨sh, st, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.tail_cons] at htail
    subst htail
    unfold VeriDNS.Spec.Net.Cache.referralSlist
    rw [if_pos (hempty (sh :: st) (by simp))]
    show c.referralSlist now st f = (c.nsHostsAt now cut).flatMap (c.glueAddrsAt now)
    exact ih st f (by simp at hfuel; omega) hchain' (fun k hk => hempty k (List.mem_cons_of_mem _ hk))

theorem keystone_at_cut (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32) (mc : Nat)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName cut = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : cut = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hnd : ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.Nodup)
    (hhost : ∀ n ∈ ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList, ∃ qn, αName n = some qn
            ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63)) :
    nsGlueByteFlat
        ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none))
        (((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).flatMap
          (fun m => (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
            if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
              some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
                (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
            else none)))
      = ((αCache c).nsHostsAt (αTime now) q.qname).flatMap ((αCache c).glueAddrsAt (αTime now)) := by
  rw [keystone_glue_assembly c now _ mc hnd hwf hcanon hused hhost,
      walkNs_nsNames_αName_eq_nsHostsAt c cut now q hqn hq4 hcanN hvN hwf hcanon hused]

theorem referralSlist_eq_nsHostsAt_at_cut (c : Cache.DnsCache) (now : UInt32)
    (sname cut : ByteArray) (sname_lab : Array ByteArray) (cutNa : VeriDNS.Spec.Net.Name)
    (inter : List ByteArray) (fuel' : Nat)
    (hsna : DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hcutNa : αName cut = some cutNa)
    (hcut_canN : cut = DomainName.labelsToWireFormatGo cutNa) (hcut_vN : ∀ x ∈ cutNa, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (himpl_chain : List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut]))
    (himpl_empty : ∀ m ∈ sname :: inter,
        (c.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true)
    (hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63))
    (hone : ∃ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none)
    (hfuel : inter.length + 2 ≤ fuel') :
    (αCache c).referralSlist (αTime now) sname_lab.toList fuel'
      = ((αCache c).nsHostsAt (αTime now) cutNa).flatMap ((αCache c).glueAddrsAt (αTime now)) := by
  have hmchain := parentDomainWire_chain_αName (inter ++ [cut]) sname sname_lab hsna hsnav himpl_chain
  simp only [List.map_append, List.map_cons, List.map_nil] at hmchain
  rw [show (αName cut).getD [] = cutNa from by simp [hcutNa]] at hmchain
  have hmempty := model_empties_of_impl c now hwf hcanon hused (sname :: inter) hcanonNode himpl_empty
  simp only [List.map_cons] at hmempty
  rw [show (αName sname).getD [] = sname_lab.toList from by simp [αName, hsna]] at hmempty
  have hcutNe : ((αCache c).nsHostsAt (αTime now) cutNa).isEmpty = false := by
    have := nsHostsAt_nonempty_of_lookupTopCred c cut now ⟨cutNa, VeriDNS.Spec.Net.QType.rr RRType.ns,
      RRClass.in, false⟩ hcutNa rfl hcut_canN hcut_vN hwf hcanon hused hone
    exact this
  exact referralSlist_ascend (αCache c) (αTime now) cutNa hcutNe
    (inter.map (fun w => (αName w).getD [])) sname_lab.toList fuel' (by rwa [List.length_map]) hmchain hmempty

def reGlue {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (cache : C) (now : UInt32) (nsNames : Array ByteArray) : Array (ByteArray × BitVec 32) :=
  nsNames.flatMap fun nsName =>
    (VeriDNS.Spec.CacheSpec.lookupTopCred cache nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap
      fun rr =>
        if (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).size == 4 then
          some (nsName, ((VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
            ((VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
            ((VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
            (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[3]!.toBitVec.setWidth 32)
        else none

set_option maxHeartbeats 1000000 in
theorem full_walk_keystone (c : Cache.DnsCache) (now : UInt32)
    (sname cut : ByteArray) (sname_lab : Array ByteArray) (cutNa : VeriDNS.Spec.Net.Name)
    (inter : List ByteArray) (mc : Nat) (fuel' : Nat)
    (hsna : DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hcutNa : αName cut = some cutNa)
    (hcut_canN : cut = DomainName.labelsToWireFormatGo cutNa) (hcut_vN : ∀ x ∈ cutNa, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hnd : ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.Nodup)
    (hhost : ∀ n ∈ ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList, ∃ qn, αName n = some qn
            ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63))
    (himpl_chain : List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut]))
    (himpl_empty : ∀ m ∈ sname :: inter,
        (c.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true)
    (hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63))
    (hone : ∃ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none)
    (hfuel : inter.length + 2 ≤ fuel') :
    nsGlueByteFlat
        ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none))
        (reGlue (RR := VeriDNS.Spec.ResourceRecord) c now
          ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
            (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
              then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)))
      = (αCache c).referralSlist (αTime now) sname_lab.toList fuel' := by
  have hA := keystone_at_cut c cut now mc ⟨cutNa, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩
    hcutNa rfl hcut_canN hcut_vN hwf hcanon hused hnd hhost
  have hB := referralSlist_eq_nsHostsAt_at_cut c now sname cut sname_lab cutNa inter fuel' hsna hsnav
    hcutNa hcut_canN hcut_vN hwf hcanon hused himpl_chain himpl_empty hcanonNode hone hfuel
  exact hA.trans hB.symm

set_option maxHeartbeats 1000000 in
theorem refer_continue_keystone (cache : Cache.DnsCache) (sname cut : ByteArray)
    (sname_lab : Array ByteArray) (cutNa : VeriDNS.Spec.Net.Name) (inter : List ByteArray)
    (nsNames : Array ByteArray) (mc : Nat) (now : UInt32) (fuel' : Nat)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) sname cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 128 = some (nsNames, mc))
    (himpl_chain : List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut]))
    (himpl_empty : ∀ m ∈ sname :: inter,
        (cache.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true)
    (hcut_ne_impl : (cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = false)
    (hfuel128 : inter.length + 2 ≤ 128)
    (hsna : DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hcutNa : αName cut = some cutNa)
    (hcut_canN : cut = DomainName.labelsToWireFormatGo cutNa) (hcut_vN : ∀ x ∈ cutNa, x.size ≤ 63)
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ cache.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hnd : ((cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.Nodup)
    (hhost : ∀ n ∈ ((cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList, ∃ qn, αName n = some qn
            ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63))
    (hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63))
    (hone : ∃ rr ∈ (cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none)
    (hfuel : inter.length + 2 ≤ fuel') :
    ((αCache cache).referralSlist (αTime now) sname_lab.toList fuel').Subperm
      (modelSlistOf (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList)
        (NS := VeriDNS.Spec.SlistEntry) nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now nsNames) mc)) := by
  have hasc := walkNs_ascend cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now cut hcut_ne_impl
    inter sname 128 hfuel128 himpl_chain himpl_empty
  have hbase := walkNs_base cut cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 0 hcut_ne_impl
  rw [hasc, hbase] at hwalk
  have heq := Option.some.inj hwalk
  rw [Prod.mk.injEq] at heq
  obtain ⟨hnn, hmm⟩ := heq
  subst hnn; subst hmm
  have hfull := full_walk_keystone cache now sname cut sname_lab cutNa inter 0 fuel' hsna hsnav hcutNa
    hcut_canN hcut_vN hwf hcanon hused hnd hhost himpl_chain himpl_empty hcanonNode hone hfuel

  rw [← hfull]
  exact (nsGlueByteFlat_sublist_fold _ _ _).subperm

theorem hit_subset_lookupAnswerable (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (rm : VeriDNS.Spec.Net.RR) (hrm : rm ∈ (αCache c).hit (αTime now) q) :
    ∃ rr, rr ∈ c.lookupAnswerable name qt qc now ∧ αRR rr = some rm := by
  unfold VeriDNS.Spec.Net.Cache.hit at hrm
  rw [List.mem_map] at hrm
  obtain ⟨a, hserved, rfl⟩ := hrm
  unfold VeriDNS.Spec.Net.Cache.served at hserved
  rw [List.mem_filter] at hserved
  obtain ⟨hmatch, hsfilt⟩ := hserved
  rw [Bool.and_eq_true] at hsfilt
  obtain ⟨hus, hmaxpred⟩ := hsfilt
  unfold VeriDNS.Spec.Net.Cache.matching at hmatch
  rw [List.mem_filter] at hmatch
  obtain ⟨hpos, hpred⟩ := hmatch
  obtain ⟨e, he, ha⟩ := mem_αCache_pos c a hpos
  obtain ⟨hane, hle, hmono⟩ := hwf e he
  obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred
  obtain ⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩ := hpred
  have hfr : e.fresh now = true := by
    rw [αCacheRR_fresh e a now hle ha]; exact hf
  have hans : Cache.answerableEntry e name qt qc now = true :=
    matching_answerableEntry e a name qt qc now q t ht hqq hqc hle ha hcanE hcanN hvE hvN
      hf hne hcov hcl hus
  have hmaxc : c.maxCredForKey e name qt qc now = true :=
    maxCredForKey_of_served_maximal c name qt qc now q t hqn ht hqq hqc hwf hused e a he ha hmaxpred
  refine ⟨{ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }, ?_, ?_⟩
  · unfold Cache.DnsCache.lookupAnswerable
    rw [Array.mem_filterMap]
    exact ⟨e, he, by rw [hans, hmaxc]; rfl⟩
  · exact αRR_aged e a now hle hfr hmono ha

theorem lookupAnswerable_mem_entry {cache : Cache.DnsCache} {name : ByteArray} {qt qc : BitVec 16}
    {now : UInt32} {rr : VeriDNS.Spec.ResourceRecord}
    (h : rr ∈ (cache.lookupAnswerable name qt qc now).toList) :
    ∃ e ∈ cache.records, Cache.answerableEntry e name qt qc now = true
      ∧ rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  rw [Cache.DnsCache.lookupAnswerable, Array.toList_filterMap, List.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  split at hsome
  · rename_i hcond
    rw [Option.some.injEq] at hsome
    rw [Bool.and_eq_true] at hcond
    exact ⟨e, Array.mem_def.mpr he, hcond.1, hsome.symm⟩
  · exact absurd hsome (by simp)

theorem lookupAnswerable_αRR_isSome {cache : Cache.DnsCache} {name : ByteArray} {qt qc : BitVec 16}
    {now : UInt32} {rr : VeriDNS.Spec.ResourceRecord}
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (h : rr ∈ (cache.lookupAnswerable name qt qc now).toList) :
    (∃ cn, αRR rr = some cn) ∧ rr.type = qt := by
  obtain ⟨e, he, hae, hrr⟩ := lookupAnswerable_mem_entry h
  have hae' := hae
  unfold Cache.answerableEntry Cache.liveEntry at hae'
  simp only [Bool.and_eq_true] at hae'
  have hfr : e.fresh now = true := hae'.1.2
  have hty : e.rr.type = qt := by
    have := hae'.1.1.1.2
    simpa using this
  obtain ⟨hsome, hle, hmono⟩ := hwf e he
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  subst hrr
  exact ⟨⟨_, αRR_aged e a now hle hfr hmono ha⟩, hty⟩

theorem lookupAnswerable_αRR_eq_hit (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupAnswerable name qt qc now).toList.filterMap αRR = (αCache c).hit (αTime now) q := by
  rw [Cache.DnsCache.lookupAnswerable, Array.toList_filterMap, List.filterMap_filterMap]
  rw [VeriDNS.Spec.Net.Cache.hit, VeriDNS.Spec.Net.Cache.served]
  generalize hsp : (fun e : VeriDNS.Spec.Net.CacheRR => e.cred.usable
      && ((αCache c).matching (αTime now) q).all
          (fun e2 => !e2.sameKey e.rr || Nat.ble e2.cred.rank e.cred.rank)) = sp
  rw [filter_map_eq_filterMap, VeriDNS.Spec.Net.Cache.matching, filter_filterMap_eq,
      show (αCache c).pos = c.records.toList.filterMap αCacheRR from rfl, List.filterMap_filterMap]
  subst hsp
  apply filterMap_congr_mem
  intro e he
  have he' : e ∈ c.records := Array.mem_def.mpr he
  obtain ⟨hane, hle, hmono⟩ := hwf e he'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
  have hce := cond_eq c name qt qc now q t hqn ht hqq hqc hcanN hvN hwf hcanon hused e he' a ha
  rw [ha, Option.bind_some]
  by_cases hcl : (Cache.answerableEntry e name qt qc now && c.maxCredForKey e name qt qc now) = true
  · have hfr : e.fresh now = true := by
      unfold Cache.answerableEntry Cache.liveEntry at hcl
      simp only [Bool.and_eq_true] at hcl; exact hcl.1.1.2
    have hcond : (a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)
          && (a.cred.usable && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank))) = true := hce ▸ hcl
    obtain ⟨hmp, hspa⟩ := Bool.and_eq_true_iff.mp hcond
    rw [if_pos hcl]
    simp only [hmp, hspa, cond_true]
    exact αRR_aged e a now hle hfr hmono ha
  · rw [Bool.not_eq_true] at hcl
    have hcond : (a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)
          && (a.cred.usable && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank))) = false := hce ▸ hcl
    rw [if_neg (by rw [hcl]; simp)]
    rcases Bool.and_eq_false_iff.mp hcond with h | h <;> simp [h]

theorem hhit_of_invariants (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hwfrr : ∀ rr ∈ c.lookupAnswerable name qt qc now, VeriDNS.Proof.NameTree.WfRR rr) :
    αSection ((c.lookupAnswerable name qt qc now).map
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
      = (αCache c).hit (αTime now) q := by
  rw [αSection_map_rrBytes_wf _ hwfrr,
      lookupAnswerable_αRR_eq_hit c name qt qc now q t hqn ht hqq hqc hcanN hvN hwf hcanon hused]

theorem localAnswer_answerHit_hit (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname0 : ByteArray) (chain0 visited0 : Array ByteArray)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (h : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname0 chain0 visited0 = .answerHit sname chain rrs)
    (hqn : αName sname = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : sname = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ cache.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    rrs.toList.filterMap αRR = (αCache cache).hit (αTime now) q := by
  obtain ⟨-, hans, -⟩ :=
    localAnswer_answerHit_inv cache qt qc now fuel sname0 chain0 visited0 sname chain rrs h
  rw [← hans]
  exact lookupAnswerable_αRR_eq_hit cache sname qt qc now q t hqn ht hqq hqc hcanN hvN hwf hcanon hused

theorem findNegative_fresh (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (e : Cache.NegativeEntry)
    (h : c.findNegative name qt qc now = some e) : now < e.expiry := by
  have hpred : ∀ x : Cache.NegativeEntry, decide (x.expiry > now) = true → now < x.expiry :=
    fun x hx => of_decide_eq_true hx
  unfold Cache.DnsCache.findNegative at h
  cases hf1 : c.negatives.find? (fun y => nameEqCI y.name name && y.qclass == qc
      && y.expiry > now && y.rcode == VeriDNS.Spec.Rcode.nameError) with
  | some a =>
    rw [hf1] at h
    change some a = some e at h
    have hae : a = e := Option.some.inj h
    have hp := Array.find?_some hf1
    simp only [Bool.and_eq_true] at hp
    rw [hae] at hp
    exact hpred e hp.1.2
  | none =>
    rw [hf1] at h
    change c.negatives.find? (fun y => nameEqCI y.name name && y.qtype == qt
        && y.qclass == qc && y.expiry > now) = some e at h
    have hp := Array.find?_some h
    simp only [Bool.and_eq_true] at hp
    exact hpred e hp.2

theorem computeNegativeTtl_eq_min (soa : VeriDNS.Spec.RData.Soa.SoaRdata) (ttl : BitVec 32) :
    (Server.computeNegativeTtl soa ttl).toNat = min soa.minimum.toNat ttl.toNat := by
  unfold Server.computeNegativeTtl
  by_cases h : soa.minimum ≤ ttl
  · simp only [if_pos h]
    have : soa.minimum.toNat ≤ ttl.toNat := BitVec.le_def.mp h
    omega
  · simp only [if_neg h]
    have : ¬ soa.minimum.toNat ≤ ttl.toNat := fun hc => h (BitVec.le_def.mpr hc)
    omega

theorem negativelyCacheable_iff_absorbNeg_trigger (resp : VeriDNS.Spec.Format)
    (htc : resp.header.tc = 0) :
    Server.negativelyCacheable resp = true
      ↔ (αRCode resp.header.rcode = VeriDNS.Spec.Net.RCode.nameError
          ∨ (αRCode resp.header.rcode = VeriDNS.Spec.Net.RCode.noError
              ∧ resp.answer.isEmpty = true)) := by
  unfold Server.negativelyCacheable αRCode
  rw [htc]
  cases resp.header.rcode <;> simp_all +decide

theorem cacheUnlessTruncated_truncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32)
    (h : resp.header.tc = 1) :
    Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache resp raws cred now = cache := by
  simp [Resolver.cacheUnlessTruncated, h]

theorem buildSubQuery_clears_rd
    (s : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (sub : VeriDNS.Spec.Format) (revealed : Nat)
    (h : Resolver.buildSubQuery s revealed = some sub) : sub.header.rd = 0 := by
  unfold Resolver.buildSubQuery at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rw [← Option.some.inj h]

theorem cnameToChase_some (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (h : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target) :
    Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false
      ∧ ∃ qu, resp.question[0]? = some qu
          ∧ Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) qu.qname resp.answer
              = some target := by
  unfold Resolver.cnameToChase at h
  split at h
  · exact absurd h (by simp)
  · rename_i hni
    split at h
    next qu hq => exact ⟨by simpa using hni, qu, hq, h⟩
    next => exact absurd h (by simp)

theorem mkAddressQuery_spec (name : ByteArray) :
    (Server.mkAddressQuery name).header.rd = 0
      ∧ (Server.mkAddressQuery name).question
        = #[{ qname := name, qtype := (1 : BitVec 16), qclass := (1 : BitVec 16) }]
      ∧ αType 1 = some RRType.a ∧ αClass 1 = some RRClass.in :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem αResp_negativeResponse {RR : Type} [VeriDNS.Spec.RRParse RR]
    (q : VeriDNS.Spec.Format) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR) :
    (αResp (Resolver.negativeResponse (RR := RR) q rc soaAuth)).answer = []
      ∧ (αResp (Resolver.negativeResponse (RR := RR) q rc soaAuth)).rcode
        = αRCode rc := by
  refine ⟨?_, rfl⟩
  simp [αResp, αSection, Resolver.negativeResponse]

theorem αResp_cacheResponse {RR : Type} [VeriDNS.Spec.RRParse RR]
    (q : VeriDNS.Spec.Format) (rrs : Array RR) :
    (αResp (Resolver.cacheResponse (RR := RR) q rrs)).rcode
      = VeriDNS.Spec.Net.RCode.noError := rfl

theorem αSection_append (a b : Array ByteArray) :
    αSection (a ++ b) = αSection a ++ αSection b := by
  unfold αSection
  rw [Array.toList_append, List.filterMap_append]

theorem αSection_empty_of_isEmpty {a : Array ByteArray} (h : a.isEmpty = true) :
    αSection a = [] := by
  rw [Array.isEmpty_iff] at h; subst h; rfl

theorem prependChain_answer (chain : Array ByteArray) (resp : VeriDNS.Spec.Format) :
    (Resolver.prependChain chain resp).answer
      = (if chain.isEmpty then resp.answer else chain ++ resp.answer) := by
  unfold Resolver.prependChain; split <;> rfl

theorem finalizeAnswer_answer {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s resp).answer = (Resolver.prependChain s.cnameChain resp).answer := by
  unfold Resolver.finalizeAnswer; cases s.lastQuery <;> rfl

theorem αSection_prependChain (chain : Array ByteArray) (resp : VeriDNS.Spec.Format) :
    αSection (Resolver.prependChain chain resp).answer
      = αSection chain ++ αSection resp.answer := by
  rw [prependChain_answer]
  by_cases h : chain.isEmpty
  · rw [if_pos h, αSection_empty_of_isEmpty h, List.nil_append]
  · rw [if_neg h, αSection_append]

theorem αSection_prependCnameLink (chain : Array ByteArray) (resp : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (cnBytes : ByteArray)
    (rr : VeriDNS.Spec.ResourceRecord) (cn : VeriDNS.Spec.Net.RR)
    (hq : resp.question[0]? = some qu)
    (hext : Resolver.extractCnameRR (RR := VeriDNS.Spec.ResourceRecord) qu.qname resp.answer
        = some cnBytes)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) cnBytes = some rr)
    (har : αRR rr = some cn) :
    αSection (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) chain resp)
      = αSection chain ++ [cn] := by
  simp only [Resolver.prependCnameLink, hq, hext]
  unfold αSection
  rw [Array.toList_push, List.filterMap_append]
  simp only [List.filterMap_cons, hp, har, List.filterMap_nil]

theorem finalizeAnswer_rcode {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s resp).header.rcode = resp.header.rcode := by
  unfold Resolver.finalizeAnswer Resolver.prependChain
  split <;> split <;> rfl

theorem finalizeAnswer_abstracts_rcode {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) :
    (αResp (Resolver.finalizeAnswer s resp)).rcode = αRCode resp.header.rcode := by
  rw [(αResp_components _).1, finalizeAnswer_rcode]

theorem αResp_finalizeAnswer_negativeResponse {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (st : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (rc : VeriDNS.Spec.Rcode)
    (soaAuth : Array RR) (hcc : st.cnameChain = #[]) :
    (αResp (Resolver.finalizeAnswer st (Resolver.negativeResponse (RR := RR) q rc soaAuth))).answer = []
      ∧ (αResp (Resolver.finalizeAnswer st (Resolver.negativeResponse (RR := RR) q rc soaAuth))).rcode
        = αRCode rc := by
  constructor
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hcc]
    rw [show αSection (Resolver.negativeResponse (RR := RR) q rc soaAuth).answer = []
        from (αResp_negativeResponse q rc soaAuth).1, List.append_nil]
    rfl
  · rw [finalizeAnswer_abstracts_rcode]
    rfl

theorem stepCheckLocal_negHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR) (chain : Array ByteArray)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .negative rc soaAuth chain) :
    Resolver.stepCheckLocal s
      = .answer (Resolver.finalizeAnswer { s with cnameChain := chain }
          (Resolver.negativeResponse q rc soaAuth))
          { s with cnameChain := chain } := by
  simp only [Resolver.stepCheckLocal, hq, hqu, hneg]

theorem stepCheckLocal_answerHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .answerHit sname chain rrs) :
    Resolver.stepCheckLocal s
      = .answer (Resolver.finalizeAnswer { s with cnameChain := chain } (Resolver.cacheResponse q rrs))
          { s with cnameChain := chain } := by
  simp only [Resolver.stepCheckLocal, hq, hqu, hhit]

theorem loop_checkAnswer_answerHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .answerHit sname chain rrs)
    (n : Nat) :
    Resolver.resolve.loop X (n + 1)
      = .ok (.done (Resolver.finalizeAnswer { X with cnameChain := chain } (Resolver.cacheResponse q rrs))
          { X with cnameChain := chain }) := by
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, hcs, stepCheckLocal_answerHit X q qu sname chain rrs hq hqu hhit]

theorem loop_checkAnswer_negHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR) (chain : Array ByteArray)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .negative rc soaAuth chain)
    (n : Nat) :
    Resolver.resolve.loop X (n + 1)
      = .ok (.done (Resolver.finalizeAnswer { X with cnameChain := chain }
          (Resolver.negativeResponse q rc soaAuth))
          { X with cnameChain := chain }) := by
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, hcs, stepCheckLocal_negHit X q qu rc soaAuth chain hq hqu hneg]

theorem stepCheckLocal_abort {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (habort : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .abort) :
    Resolver.stepCheckLocal s = .error "cname chain too long" := by
  simp only [Resolver.stepCheckLocal, hq, hqu, habort]

theorem loop_checkAnswer_abort {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (habort : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .abort)
    (n : Nat) :
    Resolver.resolve.loop X (n + 1) = .error "cname chain too long" := by
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, hcs, stepCheckLocal_abort X q qu hq hqu habort]

theorem stepCheckLocal_miss_goto {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname' : ByteArray) (chain : Array ByteArray)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .miss sname' chain) :
    ∃ s', Resolver.stepCheckLocal s = .goto .findServers s' ∧ s'.lastResponse = s.lastResponse := by
  simp only [Resolver.stepCheckLocal, hq, hqu, hmiss]
  split <;> exact ⟨_, rfl, rfl⟩

theorem stepAnalyzeResponse_cname {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false) :
    Resolver.stepAnalyzeResponse s = .goto .checkAnswer { s with
      resources := { s.resources with
        sname := target
        cache := Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
          (Resolver.ownerRaws (RR := RR) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) s.now
        slist := default }
      cnameChain := Resolver.prependCnameLink (RR := RR) s.cnameChain resp
      lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname, htc, hnrev,
    Bool.false_eq_true, if_false]

theorem stepAnalyzeResponse_cname_revisit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hrev : ((Resolver.cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true) :
    Resolver.stepAnalyzeResponse s = .error "cname loop detected" := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname, htc, hrev,
    Bool.false_eq_true, if_false, if_true]

theorem stepAnalyzeResponse_bizarre {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    Resolver.stepAnalyzeResponse s = .goto .sendQueries { s with lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname]
  rw [if_pos hbiz]

theorem stepAnalyzeResponse_lame {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (h4b : (!Resolver.answersQueryB (RR := RR) resp
              && !(resp.header.rcode == VeriDNS.Spec.Rcode.nameError)
              && resp.answer.isEmpty
              && !resp.authority.isEmpty) = true)
    (href : (Resolver.hasRRTypeIn (RR := RR) resp.authority 2
              && (resp.header.aa == 0)
              && (resp.header.rcode == VeriDNS.Spec.Rcode.noError)
              && !Resolver.hasRRTypeIn (RR := RR) resp.authority 6) = false)
    (hnodata : ((resp.header.rcode == VeriDNS.Spec.Rcode.noError)
              && resp.answer.isEmpty) = false) :
    Resolver.stepAnalyzeResponse s = .goto .sendQueries { s with lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname]
  rw [if_neg (by simp [hbiz]), if_pos h4b,
    if_neg (by simp only [href]; exact Bool.false_ne_true),
    if_neg (by simp only [hnodata]; exact Bool.false_ne_true)]

theorem answersQueryB_nonempty {RR : Type} [VeriDNS.Spec.RRParse RR] (resp : VeriDNS.Spec.Format)
    (h : Resolver.answersQueryB (RR := RR) resp = true) : resp.answer.isEmpty = false := by
  unfold Resolver.answersQueryB at h
  split at h
  · unfold Resolver.hasRRTypeIn at h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, _⟩ := h
    simp only [Array.isEmpty_eq_false_iff_exists_mem]
    exact ⟨resp.answer[i], resp.answer.getElem_mem hi⟩
  · exact absurd h (by simp)

theorem stepAnalyzeResponse_answer {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := RR) resp = true) :
    Resolver.stepAnalyzeResponse s = .answer (Resolver.finalizeAnswer s resp)
      { s with resources := { s.resources with
          cache := Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
            (Resolver.ownerRaws (RR := RR) (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) s.now } } := by
  have hne : resp.answer.isEmpty = false := answersQueryB_nonempty resp hans
  simp [Resolver.stepAnalyzeResponse, hresp, hcname, hsf, hcls, hans, hne]

theorem stepAnalyzeResponse_nameError {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := RR) resp = false) :
    Resolver.stepAnalyzeResponse s = .answer (Resolver.finalizeAnswer s resp) s := by
  simp [Resolver.stepAnalyzeResponse, hresp, hcname, hsf, hcls, hnerr, hans]

theorem stepAnalyzeResponse_referral {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := RR) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := RR) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := RR) resp.authority 6 = false) :
    Resolver.stepAnalyzeResponse s = .goto .findServers
      { s with
        resources := { s.resources with
          slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (NS := NS)
            (Resolver.extractNsNames (RR := RR) resp.authority)
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := RR)
              (Resolver.referralCutRaw (RR := RR) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := RR) resp.authority s.resources.sname),
          cache := Resolver.cacheUnlessTruncated (RR := RR)
            (Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
              (Resolver.bailiwickRaws (RR := RR)
                (Resolver.referralCutRaw (RR := RR) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) s.now)
            resp
            (Resolver.bailiwickRaws (RR := RR)
              (Resolver.referralCutRaw (RR := RR) resp.authority) resp.additional)
            Resolver.credAdditional s.now }
        lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname]
  rw [if_neg (by simp [hbiz]), if_pos (by simp [hans, hnerr, hansEmpty, hauth]),
    if_pos (by simp only [hns, haa, hrc, hsoa, Bool.not_false, Bool.and_true, Bool.true_and])]

theorem stepAnalyzeResponse_answer_payload_neg {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp X : VeriDNS.Spec.Format)
    (Xst : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hans : Resolver.answersQueryB (RR := RR) resp = false)
    (hsa : Resolver.stepAnalyzeResponse s = .answer X Xst) :
    X = Resolver.finalizeAnswer s resp ∧ Xst = s := by
  unfold Resolver.stepAnalyzeResponse at hsa
  rw [hresp] at hsa
  simp only [hcname, hans, Bool.false_eq_true, if_false] at hsa
  repeat' split at hsa
  all_goals simp_all
  all_goals exact (hsa.2 ▸ hsa.1).symm

theorem stepAnalyzeResponse_answer_payload_pos {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp X : VeriDNS.Spec.Format)
    (Xst : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hans : Resolver.answersQueryB (RR := RR) resp = true)
    (hsa : Resolver.stepAnalyzeResponse s = .answer X Xst) :
    X = Resolver.finalizeAnswer s resp
      ∧ Xst = { s with resources := { s.resources with
          cache := Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
            (Resolver.ownerRaws (RR := RR) (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) s.now } } := by
  by_cases hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = true
  · rw [stepAnalyzeResponse_bizarre s resp hresp hcname (by rw [hsf]; rfl)] at hsa
    exact absurd hsa (by simp)
  · by_cases hcls : Resolver.classifiableB resp = true
    · rw [stepAnalyzeResponse_answer s resp hresp hcname
        (Bool.eq_false_iff.mpr hsf) hcls hans] at hsa
      injection hsa with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    · rw [stepAnalyzeResponse_bizarre s resp hresp hcname
        (by rw [Bool.eq_false_iff.mpr hcls]; simp)] at hsa
      exact absurd hsa (by simp)

theorem stepAnalyzeResponse_goto_shape {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (ns : VeriDNS.Spec.AlgorithmStep)
    (s' : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hsa : Resolver.stepAnalyzeResponse s = .goto ns s') :
    (ns = .findServers ∨ ns = .sendQueries) ∧ s'.lastResponse = none := by
  unfold Resolver.stepAnalyzeResponse at hsa
  rw [hresp] at hsa
  simp only [hcname] at hsa
  repeat' split at hsa
  all_goals simp_all
  · rw [← hsa.2]
  · rw [← hsa.2]

theorem stepAnalyzeResponse_goto_cases {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (ns : VeriDNS.Spec.AlgorithmStep)
    (s' : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hsa : Resolver.stepAnalyzeResponse s = .goto ns s') :
    (ns = .findServers
      ∧ (Resolver.answersQueryB (RR := RR) resp = false
        ∧ (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false
        ∧ resp.answer.isEmpty = true ∧ resp.authority.isEmpty = false
        ∧ Resolver.hasRRTypeIn (RR := RR) resp.authority 2 = true
        ∧ (resp.header.aa == 0) = true
        ∧ (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true
        ∧ Resolver.hasRRTypeIn (RR := RR) resp.authority 6 = false))
    ∨ (ns = .sendQueries ∧ s' = { s with lastResponse := none }
      ∧ (!Resolver.answersQueryB (RR := RR) resp
          && !(resp.header.rcode == VeriDNS.Spec.Rcode.nameError)
          && resp.answer.isEmpty
          && !resp.authority.isEmpty) = true
      ∧ (Resolver.hasRRTypeIn (RR := RR) resp.authority 2
          && (resp.header.aa == 0)
          && (resp.header.rcode == VeriDNS.Spec.Rcode.noError)
          && !Resolver.hasRRTypeIn (RR := RR) resp.authority 6) = false
      ∧ ((resp.header.rcode == VeriDNS.Spec.Rcode.noError)
          && resp.answer.isEmpty) = false) := by
  unfold Resolver.stepAnalyzeResponse at hsa
  rw [hresp] at hsa
  simp only [hcname] at hsa
  split at hsa
  · rename_i hbz; simp [hbiz] at hbz
  · split at hsa
    · rename_i hcond
      split at hsa
      · rename_i hhns
        obtain ⟨hns, -⟩ := Resolver.StepResult.goto.inj hsa
        simp only [Bool.and_eq_true] at hcond hhns
        exact Or.inl ⟨hns.symm, by simpa using hcond.1.1.1, by simpa using hcond.1.1.2, hcond.1.2,
          by simpa using hcond.2, hhns.1.1.1, hhns.1.1.2, hhns.1.2, by simpa using hhns.2⟩
      · rename_i hhns
        split at hsa <;> rename_i hnodata
        · exact absurd hsa (by simp)
        · obtain ⟨hns, hs'⟩ := Resolver.StepResult.goto.inj hsa
          exact Or.inr ⟨hns.symm, hs'.symm, hcond,
            Bool.eq_false_iff.mpr hhns, Bool.eq_false_iff.mpr hnodata⟩
    · rename_i hcond
      repeat' split at hsa
      all_goals simp_all

theorem afterResume_continue_stepAnalyze_goto
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA : VeriDNS.Spec.Format)
    (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hAR : Server.afterResume state entryName respA = .continue st) :
    ∃ ns s', Resolver.stepAnalyzeResponse
      ({ state with lastResponse := some respA, currentStep := .analyzeResponse } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      = .goto ns s' := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  unfold Server.afterResume at hAR
  rw [hdrop, Resolver.resume] at hAR
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step, hstep, Resolver.stepSendQueries] at hAR
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step] at hAR
  split at hAR
  · exact absurd hAR (by simp)
  · rename_i X heq
    split at heq
    · exact absurd heq (by simp)
    · rename_i ns s' heq2; exact ⟨ns, s', heq2⟩
    ·
      rename_i s'x heqio
      simp only [Resolver.stepAnalyzeResponse, hcname] at heqio
      repeat' split at heqio
      all_goals simp_all
    · exact absurd heq (by simp)
  · exact absurd hAR (by simp)

theorem respInBailiwick_sound (sname : ByteArray) (resp : VeriDNS.Spec.Format)
    (hb : Server.respInBailiwick sname resp = true)
    (i : Nat) (hi : i < resp.authority.size)
    (rr : VeriDNS.Spec.ResourceRecord)
    (hparse : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        resp.authority[i] = some rr)
    (hns : (VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)) = true)
    (ownerLabels snameLabels : Array ByteArray)
    (ho : DomainName.wireFormatToLabels (VeriDNS.Spec.RRParse.rrName rr) = .ok ownerLabels)
    (hsn : DomainName.wireFormatToLabels sname = .ok snameLabels) :
    Resolver.suffixMatchCount snameLabels ownerLabels = ownerLabels.size := by
  unfold Server.respInBailiwick at hb
  rw [Array.all_eq_true] at hb
  have hp := hb i hi
  rw [hparse] at hp
  simp only [hns, if_true, ho, hsn] at hp
  simpa using hp

theorem respInBailiwick_of_not_unfollowable (slist : SList.DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hunf : Server.unfollowableDelegationB slist sname resp = false)
    (hdel : Server.delegationShapedB resp = true) :
    Server.respInBailiwick sname resp = true := by
  unfold Server.unfollowableDelegationB at hunf
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, hdel, Bool.true_eq_false, false_or] at hunf
  simpa using hunf.2

theorem delegationShapedB_of (resp : VeriDNS.Spec.Format)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none) :
    Server.delegationShapedB resp = true := by
  unfold Server.delegationShapedB
  simp only [hns, hans, hnerr, hcn, Bool.not_false, Bool.true_and, Bool.and_true,
    Option.isNone_none]

theorem delegationCloserB_of_not_unfollowable (slist : SList.DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hunf : Server.unfollowableDelegationB slist sname resp = false)
    (hdel : Server.delegationShapedB resp = true) :
    Server.delegationCloserB slist sname resp = true := by
  unfold Server.unfollowableDelegationB Server.bogusDelegationB at hunf
  rw [Bool.or_eq_false_iff] at hunf
  have h1 := hunf.1
  rw [hdel, Bool.true_and] at h1
  simpa using h1

theorem respInBailiwick_complete (sname : ByteArray) (resp : VeriDNS.Spec.Format)
    (h : ∀ (i : Nat) (_ : i < resp.authority.size),
       ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
           resp.authority[i] = some rr ∧
         ((VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)) = true →
           ∃ ownerLabels snameLabels,
             DomainName.wireFormatToLabels (VeriDNS.Spec.RRParse.rrName rr) = .ok ownerLabels ∧
             DomainName.wireFormatToLabels sname = .ok snameLabels ∧
             Resolver.suffixMatchCount snameLabels ownerLabels = ownerLabels.size)) :
    Server.respInBailiwick sname resp = true := by
  unfold Server.respInBailiwick
  rw [Array.all_eq_true]
  intro i hi
  obtain ⟨rr, hparse, hns⟩ := h i hi
  simp only [hparse]
  split
  · rename_i hisns
    obtain ⟨ol, sl, ho, hsn, hsuf⟩ := hns hisns
    simp only [ho, hsn]
    simpa using hsuf
  · rfl

theorem resolve_negHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR)
    (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .negative rc soaAuth chain) :
    Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
      = (.ok (.done (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain })
          : Except String (Resolver.ResolveYield S C NS RR)) := by
  have hsname : (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache).resources.sname = qu.qname := by
    simp only [Resolver.initFromQuery, hqu]
  have hstep : Resolver.step (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache)
      = .answer (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain } := by
    unfold Resolver.step
    show Resolver.stepCheckLocal _ = _
    apply stepCheckLocal_negHit (qu := qu)
    · rfl
    · exact hqu
    · show Resolver.localAnswer cache qu.qtype qu.qclass now 8 _ #[]
          (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = _
      rw [hsname]; exact hneg
  unfold Resolver.resolve
  show Resolver.resolve.loop _ (n + 1) = _
  rw [Resolver.resolve.loop, hstep]

theorem resolve_answerHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .answerHit sname chain rrs) :
    Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
      = (.ok (.done (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain })
          : Except String (Resolver.ResolveYield S C NS RR)) := by
  have hsname : (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache).resources.sname
      = qu.qname := by simp only [Resolver.initFromQuery, hqu]
  have hstep : Resolver.step (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache)
      = .answer (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain } := by
    unfold Resolver.step
    show Resolver.stepCheckLocal _ = _
    apply stepCheckLocal_answerHit (qu := qu) (sname := sname)
    · rfl
    · exact hqu
    · show Resolver.localAnswer cache qu.qtype qu.qclass now 8 _ #[]
          (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = _
      rw [hsname]; exact hhit
  unfold Resolver.resolve
  show Resolver.resolve.loop _ (n + 1) = _
  rw [Resolver.resolve.loop, hstep]

theorem resolve_negHit_abstracts {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR)
    (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .negative rc soaAuth chain) :
    ∃ resp stF, Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
        = (.ok (.done resp stF) : Except String (Resolver.ResolveYield S C NS RR))
      ∧ (αResp resp).answer = αSection chain
      ∧ (αResp resp).rcode = αRCode rc := by
  refine ⟨_, _, resolve_negHit query sbelt n now cache qu rc soaAuth chain hqu hneg, ?_, ?_⟩
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
    rw [show αSection (Resolver.negativeResponse (RR := RR) query rc soaAuth).answer = []
        from (αResp_negativeResponse query rc soaAuth).1, List.append_nil]
  · rw [finalizeAnswer_abstracts_rcode]
    rfl

theorem resolve_answerHit_abstracts {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .answerHit sname chain rrs) :
    ∃ resp stF, Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
        = (.ok (.done resp stF) : Except String (Resolver.ResolveYield S C NS RR))
      ∧ (αResp resp).rcode = VeriDNS.Spec.Net.RCode.noError
      ∧ (αResp resp).answer
          = αSection chain ++ αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := RR))) := by
  refine ⟨_, _, resolve_answerHit query sbelt n now cache qu sname chain rrs hqu hhit, ?_, ?_⟩
  · show αRCode (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs)).header.rcode = _
    rw [finalizeAnswer_rcode]
    rfl
  · show (αResp (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs))).answer = _
    rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
    rfl

theorem resolveWithIO_negHit {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (soaAuth : Array VeriDNS.Spec.ResourceRecord) (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .negative rc soaAuth chain) :
    Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
      = pure (.ok (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
              query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth)), cache) := by
  unfold Server.resolveWithIO
  rw [show (64 : Nat) = 63 + 1 from rfl,
    resolve_negHit query sbelt 63 now cache qu rc soaAuth chain hqu hneg]

theorem resolveWithIO_answerHit {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
      = pure (.ok (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
              query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs)), cache) := by
  unfold Server.resolveWithIO
  rw [show (64 : Nat) = 63 + 1 from rfl,
    resolve_answerHit query sbelt 63 now cache qu sname chain rrs hqu hhit]

theorem resolveWithIO_answerHit_payload {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    ∃ resp, Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ (αResp resp).rcode = VeriDNS.Spec.Net.RCode.noError
      ∧ (αResp resp).answer
          = αSection chain ++ αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes
              (RR := VeriDNS.Spec.ResourceRecord))) := by
  refine ⟨_, resolveWithIO_answerHit query sbelt cache now fuel depth budget qu sname chain rrs
    hqu hhit, ?_, ?_⟩
  · show αRCode (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs)).header.rcode = _
    rw [finalizeAnswer_rcode]
    rfl
  · show (αResp (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs))).answer = _
    rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
    rfl

theorem afterResume_answer
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    Server.afterResume state entryName resp
      = .finished (.ok (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp))

          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundLru
            (Server.roundTouches state resp) state.now) := by
  have hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB resp) = false := by rw [hsf, hcls]; rfl
  have hne : resp.answer.isEmpty = false := answersQueryB_nonempty resp hans
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hsa : Resolver.stepAnalyzeResponse
      { state with lastResponse := some resp, currentStep := .analyzeResponse }
      = .answer (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp)
          { { state with lastResponse := some resp, currentStep := .analyzeResponse } with
            resources := { state.resources with
              cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                state.resources.cache resp
                (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.echoedQname resp) resp.answer)
                (Resolver.credAnswer (resp.header.aa == 1)) state.now } } := by
    apply stepAnalyzeResponse_answer <;> first | rfl | assumption
  unfold Server.afterResume
  rw [hdrop, Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]
  rfl

theorem afterResume_answer_payload
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    ∃ out cout, Server.afterResume state entryName resp = .finished (.ok out) cout
      ∧ (αResp out).rcode = αRCode resp.header.rcode
      ∧ (αResp out).answer = αSection state.cnameChain ++ αSection resp.answer := by
  refine ⟨_, _, afterResume_answer state entryName resp hstep hcname hsf hcls hans, ?_, ?_⟩
  · exact finalizeAnswer_abstracts_rcode _ resp
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]

theorem respAgree_answer_bridge
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA resp : VeriDNS.Spec.Format} {ref : VeriDNS.Spec.Net.Response}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok resp) cout)
    (hchain : state.cnameChain = #[])
    (hragA : RespAgree (αResp respA) ref) :
    RespAgree (αResp resp) { ref with aa := false } := by
  obtain ⟨out, cout', hout, hrc, han⟩ :=
    afterResume_answer_payload state entryName respA hstep hcname hsf hcls hans
  rw [hAR] at hout
  injection hout with ho hco; injection ho with ho; subst ho
  rw [hchain] at han
  refine RespAgree.trans (RespAgree.of_eq ?_ ?_) hragA
  · rw [hrc, (αResp_components respA).1]
  · rw [han, (αResp_components respA).2.1]
    simp [αSection]

theorem αSection_finalizeAnswer_cacheResponse
    (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Format) (rrs : Array VeriDNS.Spec.ResourceRecord) :
    αSection (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)).answer
      = αSection st.cnameChain ++ αSection (Resolver.cacheResponse q rrs).answer := by
  rw [finalizeAnswer_answer, αSection_prependChain]

theorem respAgree_cname_finished_bridge
    (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Format) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (cnBytes : ByteArray) (rr : VeriDNS.Spec.ResourceRecord) (cn : VeriDNS.Spec.Net.RR)
    (final : VeriDNS.Spec.Net.Response)
    (hstchain : st.cnameChain = #[cnBytes])
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) cnBytes = some rr)
    (har : αRR rr = some cn)
    (hperm : (αSection (Resolver.cacheResponse q rrs).answer).Perm final.answer)
    (hfinrc : final.rcode = VeriDNS.Spec.Net.RCode.noError) :
    RespAgree (αResp (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)))
      { final with answer := cn :: final.answer } := by
  refine ⟨?_, ?_⟩
  · rw [(αResp_components _).1, finalizeAnswer_rcode]
    show αRCode (Resolver.cacheResponse q rrs).header.rcode = final.rcode
    rw [hfinrc]; rfl
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hstchain]
    have hcn1 : αSection #[cnBytes] = [cn] := by
      unfold αSection
      rw [show #[cnBytes].toList = [cnBytes] from rfl]
      simp only [List.filterMap_cons, hp, har, List.filterMap_nil]
    rw [hcn1, List.singleton_append]
    exact List.Perm.cons cn hperm

theorem afterResume_nameError
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false) :
    Server.afterResume state entryName resp
      = .finished (.ok (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp))
          (Server.boundStateCache (Server.roundTouches state resp)
            { state with lastResponse := some resp, currentStep := .analyzeResponse }).resources.cache := by
  have hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB resp) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hsa : Resolver.stepAnalyzeResponse
      { state with lastResponse := some resp, currentStep := .analyzeResponse }
      = .answer (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp)
          { state with lastResponse := some resp, currentStep := .analyzeResponse } := by
    apply stepAnalyzeResponse_nameError <;> first | rfl | assumption
  unfold Server.afterResume
  rw [hdrop, Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]

theorem afterResume_bizarre
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    Server.afterResume state entryName resp
      = .continue (Server.boundStateCache
          (Server.roundTouches (Server.dropIfBizarre state entryName resp) resp)
          { Server.dropIfBizarre state entryName resp with
            lastResponse := none, currentStep := .sendQueries }) := by
  have hcs : (Server.dropIfBizarre state entryName resp).currentStep = .sendQueries := by
    unfold Server.dropIfBizarre; split <;> exact hstep
  have hsa : Resolver.stepAnalyzeResponse
      { Server.dropIfBizarre state entryName resp with
        lastResponse := some resp, currentStep := .analyzeResponse }
      = .goto .sendQueries
          { { Server.dropIfBizarre state entryName resp with
              lastResponse := some resp, currentStep := .analyzeResponse } with
            lastResponse := none } := by
    apply stepAnalyzeResponse_bizarre <;> first | rfl | assumption
  unfold Server.afterResume
  rw [Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]
  rw [show (62 : Nat) = 61 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, Resolver.stepSendQueries]

theorem afterResume_lame
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (h4b : (!Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp
              && !(resp.header.rcode == VeriDNS.Spec.Rcode.nameError)
              && resp.answer.isEmpty
              && !resp.authority.isEmpty) = true)
    (href : (Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2
              && (resp.header.aa == 0)
              && (resp.header.rcode == VeriDNS.Spec.Rcode.noError)
              && !Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6) = false)
    (hnodata : ((resp.header.rcode == VeriDNS.Spec.Rcode.noError)
              && resp.answer.isEmpty) = false) :
    Server.afterResume state entryName resp
      = .continue (Server.boundStateCache
          (Server.roundTouches state resp)
          { state with lastResponse := none, currentStep := .sendQueries }) := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hsa : Resolver.stepAnalyzeResponse
      { state with lastResponse := some resp, currentStep := .analyzeResponse }
      = .goto .sendQueries
          { { state with lastResponse := some resp, currentStep := .analyzeResponse } with
            lastResponse := none } :=
    stepAnalyzeResponse_lame _ resp rfl hcname hbiz h4b href hnodata
  unfold Server.afterResume
  rw [hdrop, Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]
  rw [show (62 : Nat) = 61 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, Resolver.stepSendQueries]

theorem stepFindServers_goto {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) :
    ∃ s', Resolver.stepFindServers s = .goto .sendQueries s' ∧ s'.lastResponse = s.lastResponse := by
  unfold Resolver.stepFindServers; dsimp only
  split <;> split <;> (try split) <;> exact ⟨_, rfl, rfl⟩

theorem stepFindServers_frame {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s s' : Resolver.State S C NS RR)
    (h : Resolver.stepFindServers s = .goto .sendQueries s') :
    s'.resources.cache = s.resources.cache ∧ s'.resources.sname = s.resources.sname
      ∧ s'.now = s.now ∧ s'.cnameChain = s.cnameChain ∧ s'.lastQuery = s.lastQuery
      ∧ s'.lastResponse = s.lastResponse ∧ s'.currentStep = s.currentStep := by
  unfold Resolver.stepFindServers at h; dsimp only at h
  split at h <;> split at h <;> (try split at h) <;>
    (injection h with _ h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem stepFindServers_rebuild {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (nsNames : Array ByteArray) (mc : Nat)
    (hwalk : Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = false)
    (hnb : ((reGlue (RR := RR) s.resources.cache s.now nsNames).isEmpty && (mc == 0)) = false) :
    Resolver.stepFindServers s = .goto .sendQueries
      { s with resources := { s.resources with
          slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
            (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } } := by
  have hunf : Resolver.stepFindServers s = (
      match Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
          (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
      | some (nsNames, mc) =>
        if (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
            && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) then
          .goto .sendQueries s
        else if (reGlue (RR := RR) s.resources.cache s.now nsNames).isEmpty && (mc == 0) then
          .goto .sendQueries { s with resources := { s.resources with slist := s.resources.sbelt } }
        else
          .goto .sendQueries { s with resources := { s.resources with
            slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
              (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } }
      | none =>
        if (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
            && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) then
          .goto .sendQueries s
        else
          .goto .sendQueries { s with resources := { s.resources with slist := s.resources.sbelt } }) := rfl
  rw [hunf, hwalk]
  simp only [hclose, hnb, if_false, Bool.false_eq_true]

theorem stepFindServers_keep {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR)
    (hkeep : ∀ walkMc : Nat,
        (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
          && decide (walkMc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = true) :
    Resolver.stepFindServers s = .goto .sendQueries s := by
  unfold Resolver.stepFindServers
  dsimp only
  cases hw : Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
  | none =>
    simp only [hkeep 0, if_true]
  | some p =>
    obtain ⟨nsNames, mc⟩ := p
    simp only [hkeep mc, if_true]

theorem stepFindServers_cases {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) :
    ∃ s', Resolver.stepFindServers s = .goto .sendQueries s'
      ∧ s'.resources.cache = s.resources.cache ∧ s'.resources.sname = s.resources.sname
      ∧ s'.now = s.now ∧ s'.cnameChain = s.cnameChain ∧ s'.lastQuery = s.lastQuery
      ∧ s'.lastResponse = s.lastResponse
      ∧ s'.resources.sbelt = s.resources.sbelt
      ∧ ( s'.resources.slist = s.resources.slist
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
                (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = false
              ∧ s'.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
                  (reGlue (RR := RR) s.resources.cache s.now nsNames) mc)
          ∨ (s'.resources.slist = s.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = false) ) := by
  have hunf : Resolver.stepFindServers s = (
      match Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
          (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
      | some (nsNames, mc) =>
        if (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
            && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) then
          .goto .sendQueries s
        else if (reGlue (RR := RR) s.resources.cache s.now nsNames).isEmpty && (mc == 0) then
          .goto .sendQueries { s with resources := { s.resources with slist := s.resources.sbelt } }
        else
          .goto .sendQueries { s with resources := { s.resources with
            slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
              (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } }
      | none =>
        if (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
            && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) then
          .goto .sendQueries s
        else
          .goto .sendQueries { s with resources := { s.resources with slist := s.resources.sbelt } }) := rfl
  rw [hunf]
  cases hw : Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
  | none =>
    dsimp only
    by_cases hc : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
        && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = true
    · refine ⟨s, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
      rw [if_pos hc]
    · rw [Bool.not_eq_true] at hc
      refine ⟨{ s with resources := { s.resources with slist := s.resources.sbelt } },
        ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, hc⟩)⟩
      rw [if_neg (by rw [hc]; simp)]
  | some p =>
    obtain ⟨nsNames, mc⟩ := p
    dsimp only
    by_cases hc : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = true
    · refine ⟨s, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
      rw [if_pos hc]
    · rw [Bool.not_eq_true] at hc
      by_cases hg : ((reGlue (RR := RR) s.resources.cache s.now nsNames).isEmpty && (mc == 0)) = true
      ·
        have hmc0 : mc = 0 := by
          have h2 := hg
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          exact h2.2
        refine ⟨{ s with resources := { s.resources with slist := s.resources.sbelt } },
          ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, hmc0 ▸ hc⟩)⟩
        rw [if_neg (by rw [hc]; simp), if_pos hg]
      · rw [Bool.not_eq_true] at hg
        refine ⟨{ s with resources := { s.resources with
            slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
              (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } },
          ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨nsNames, mc, rfl, hc, rfl⟩)⟩
        rw [if_neg (by rw [hc]; simp), if_neg (by rw [hg]; simp)]

theorem loop_findServers_paused {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st) := by
  obtain ⟨s', hfs, hs'⟩ := stepFindServers_goto X
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  have : s'.lastResponse = none := hs'.trans hlr
  simp only [Resolver.step, Resolver.stepSendQueries, this]
  exact ⟨_, rfl⟩

theorem loop_findServers_paused_struct {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st)
      ∧ st.resources.cache = X.resources.cache ∧ st.resources.sname = X.resources.sname
      ∧ st.now = X.now ∧ st.cnameChain = X.cnameChain ∧ st.currentStep = .sendQueries := by
  obtain ⟨s', hfs, hs'⟩ := stepFindServers_goto X
  obtain ⟨hc, hsn, hnw, hcc, _, _, _⟩ := stepFindServers_frame X s' hfs
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  have hlr' : s'.lastResponse = none := hs'.trans hlr
  simp only [Resolver.step, Resolver.stepSendQueries, hlr']
  exact ⟨_, rfl, hc, hsn, hnw, hcc, rfl⟩

theorem loop_findServers_paused_slist {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (nsNames : Array ByteArray) (mc : Nat)
    (hwalk : Resolver.stepFindServers.walkNs (RR := RR) X.resources.sname X.resources.cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) X.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) X.resources.slist
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) X.resources.slist)) = false)
    (hnb : ((reGlue (RR := RR) X.resources.cache X.now nsNames).isEmpty && (mc == 0)) = false)
    (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st)
      ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
          (reGlue (RR := RR) X.resources.cache X.now nsNames) mc
      ∧ st.resources.cache = X.resources.cache ∧ st.resources.sname = X.resources.sname
      ∧ st.now = X.now ∧ st.cnameChain = X.cnameChain ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = X.lastQuery := by
  have hfs := stepFindServers_rebuild X nsNames mc hwalk hclose hnb
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, Resolver.stepSendQueries, hlr]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem loop_findServers_paused_cases {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st)
      ∧ st.resources.cache = X.resources.cache ∧ st.resources.sname = X.resources.sname
      ∧ st.now = X.now ∧ st.cnameChain = X.cnameChain ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = X.lastQuery
      ∧ st.resources.sbelt = X.resources.sbelt
      ∧ ( st.resources.slist = X.resources.slist
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := RR) X.resources.sname X.resources.cache
                (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) X.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) X.resources.slist
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) X.resources.slist)) = false
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
                  (reGlue (RR := RR) X.resources.cache X.now nsNames) mc)
          ∨ (st.resources.slist = X.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) X.resources.slist
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) X.resources.slist)) = false) ) := by
  obtain ⟨s', hfs, hc, hsn, hnw, hcc, hlq, hlrs, hsb, hdisj⟩ := stepFindServers_cases X
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  have hlr' : s'.lastResponse = none := hlrs.trans hlr
  simp only [Resolver.step, Resolver.stepSendQueries, hlr']
  refine ⟨_, rfl, hc, hsn, hnw, hcc, rfl, hlq, hsb, ?_⟩
  exact hdisj

theorem loop_checkAnswer_miss {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname' : ByteArray) (chain : Array ByteArray)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .miss sname' chain)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 3) = .ok (.paused st) := by
  obtain ⟨s', hsc, hs'⟩ := stepCheckLocal_miss_goto X q qu sname' chain hq hqu hmiss
  rw [show n + 3 = (n + 2) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hsc]
  exact loop_findServers_paused { s' with currentStep := .findServers } rfl (hs'.trans hlr) n

theorem resume_referral_paused
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st) := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused _ rfl rfl 60

theorem resume_referral_paused_struct
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st)
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) state.now)
            resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
            Resolver.credAdditional state.now
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused_struct _ rfl rfl 60

set_option maxHeartbeats 2000000 in
theorem resume_referral_paused_slist
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (nsNames : Array ByteArray) (mc : Nat)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false)
    (hnb : ((reGlue (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        state.now nsNames).isEmpty && (mc == 0)) = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st)
      ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry) nsNames
          (reGlue (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
                (Resolver.credAuthority (resp.header.aa == 1)) state.now)
              resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
              Resolver.credAdditional state.now)
            state.now nsNames) mc
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) state.now)
            resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
            Resolver.credAdditional state.now
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  refine loop_findServers_paused_slist _ rfl rfl nsNames mc hwalk hclose ?_ 60
  exact hnb

theorem resume_referral_paused_cases
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st)
      ∧ st.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery
      ∧ st.resources.sbelt = state.resources.sbelt
      ∧ ( st.resources.slist = (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) nsNames
                  (reGlue (RR := VeriDNS.Spec.ResourceRecord) (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now) state.now nsNames) mc)
          ∨ (st.resources.slist = state.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false) ) := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused_cases _ rfl rfl 60

theorem resume_cname_answerHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp)) = .answerHit sname chain rrs) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Resolver.resume state resp 64
        = .ok (.done (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)) st)
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  refine ⟨{ ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      with cnameChain := chain }, ?_, rfl, rfl⟩
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 61 + 1 from rfl]
  exact loop_checkAnswer_answerHit
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp })
    q qu sname chain rrs rfl hq hqu hhit 61

theorem afterResume_cname_answerHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) = .answerHit sname chain rrs) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Server.afterResume state entryName respA
        = .finished (.ok (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)))
            (Server.boundStateCache (Server.roundTouches state respA) st).resources.cache
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hrs, hcc, hca⟩ :=
    resume_cname_answerHit state respA target q qu sname chain rrs hstep hcn htc hnrev hq hqu hhit
  refine ⟨st, ?_, hcc, hca⟩
  unfold Server.afterResume
  rw [hdrop, hrs]

theorem resume_cname_negHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
    (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp)) = .negative rc soaAuth chain) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Resolver.resume state resp 64
        = .ok (.done (Resolver.finalizeAnswer st (Resolver.negativeResponse q rc soaAuth)) st)
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  refine ⟨{ ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      with cnameChain := chain }, ?_, rfl, rfl⟩
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 61 + 1 from rfl]
  exact loop_checkAnswer_negHit
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp })
    q qu rc soaAuth chain rfl hq hqu hneg 61

theorem afterResume_cname_negHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
    (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) = .negative rc soaAuth chain) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Server.afterResume state entryName respA
        = .finished (.ok (Resolver.finalizeAnswer st (Resolver.negativeResponse q rc soaAuth)))
            (Server.boundStateCache (Server.roundTouches state respA) st).resources.cache
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hrs, hcc, hca⟩ :=
    resume_cname_negHit state respA target q qu rc soaAuth chain hstep hcn htc hnrev hq hqu hneg
  refine ⟨st, ?_, hcc, hca⟩
  unfold Server.afterResume
  rw [hdrop, hrs]

theorem resume_cname_miss
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (sname' : ByteArray) (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp)) = .miss sname' chain) :
    ∃ st', Resolver.resume state resp 64 = .ok (.paused st') := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 59 + 3 from rfl]
  exact loop_checkAnswer_miss
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp })
    q qu sname' chain rfl hq hqu hmiss rfl 59

theorem resume_cname_abort
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (habort : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp)) = .abort) :
    Resolver.resume state resp 64 = .error "cname chain too long" := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 61 + 1 from rfl]
  exact loop_checkAnswer_abort
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname resp) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp })
    q qu rfl hq hqu habort 61

theorem resume_cname_revisit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true) :
    Resolver.resume state resp 64 = .error "cname loop detected" := by
  have hcname_step := stepAnalyzeResponse_cname_revisit
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hrev
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]

theorem afterResume_cname_revisit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA : VeriDNS.Spec.Format) (target : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true) :
    Server.afterResume state entryName respA
      = .finished (.error "cname loop detected") state.resources.cache := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  unfold Server.afterResume
  rw [hdrop, resume_cname_revisit state respA target hstep hcn htc hrev]

theorem afterResume_cname_miss
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (sname' : ByteArray) (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) = .miss sname' chain) :
    ∃ st', Server.afterResume state entryName respA = .continue st' := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st', hrs⟩ := resume_cname_miss state respA target q qu sname' chain hstep hcn htc hnrev hq hqu hmiss
  refine ⟨Server.boundStateCache (Server.roundTouches state respA) st', ?_⟩
  unfold Server.afterResume
  rw [hdrop, hrs]

theorem afterResume_cname_finished_inv
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    (∃ (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
        (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
      Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) = .answerHit sname chain rrs ∧
      out = Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs) ∧ st.cnameChain = chain ∧
      cout = (Server.boundStateCache (Server.roundTouches state respA) st).resources.cache) ∨
    (∃ (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
        (chain : Array ByteArray)
        (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
      Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) = .negative rc soaAuth chain ∧
      out = Resolver.finalizeAnswer st (Resolver.negativeResponse q rc soaAuth) ∧ st.cnameChain = chain ∧
      cout = (Server.boundStateCache (Server.roundTouches state respA) st).resources.cache) := by
  cases hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
      qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) with
  | answerHit sname chain rrs =>
    obtain ⟨st, hAR', hcc, -⟩ :=
      afterResume_cname_answerHit state entryName respA q target qu sname chain rrs hstep hcn htc hnrev hsf hcls hq hqu hla
    have he := hAR.symm.trans hAR'
    simp only [Server.IoStep.finished.injEq, Except.ok.injEq] at he
    exact Or.inl ⟨sname, chain, rrs, st, rfl, he.1, hcc, he.2⟩
  | negative rc soaAuth chain =>
    obtain ⟨st, hAR', hcc, -⟩ :=
      afterResume_cname_negHit state entryName respA q target qu rc soaAuth chain hstep hcn htc hnrev hsf hcls hq hqu hla
    have he := hAR.symm.trans hAR'
    simp only [Server.IoStep.finished.injEq, Except.ok.injEq] at he
    exact Or.inr ⟨rc, soaAuth, chain, st, rfl, he.1, hcc, he.2⟩
  | miss sname' chain =>
    obtain ⟨st', hAR'⟩ :=
      afterResume_cname_miss state entryName respA q target qu sname' chain hstep hcn htc hnrev hsf hcls hq hqu hla
    exact absurd (hAR.symm.trans hAR') (by simp)
  | abort =>
    have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
    have hdrop : Server.dropIfBizarre state entryName respA = state := by
      unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
    have hres := resume_cname_abort state respA target q qu hstep hcn htc hnrev hq hqu hla
    unfold Server.afterResume at hAR
    rw [hdrop, hres] at hAR
    exact absurd hAR (by simp)

theorem afterResume_finished_payload_neg
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    out = Resolver.finalizeAnswer
      { state with lastResponse := some respA, currentStep := .analyzeResponse } respA ∧
    cout = (Server.boundStateCache (Server.roundTouches state respA)
      { state with lastResponse := some respA, currentStep := .analyzeResponse }).resources.cache := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hresp1 :
      ({ state with lastResponse := some respA, currentStep := .analyzeResponse } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
          VeriDNS.Spec.ResourceRecord).lastResponse = some respA := rfl
  unfold Server.afterResume at hAR
  rw [hdrop, Resolver.resume] at hAR
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step, hstep, Resolver.stepSendQueries] at hAR
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step] at hAR

  split at hAR
  ·
    rename_i X Xst heq
    injection hAR with h hcout
    injection h with h
    split at heq
    ·
      rename_i resp rst heq2
      have hpay := stepAnalyzeResponse_answer_payload_neg _ respA resp rst hresp1 hcname hans heq2
      injection heq with he
      injection he with he hst
      constructor
      · rw [← h, ← he]; exact hpay.1
      · rw [← hcout, ← hst, hpay.2]
    ·
      rename_i ns s' heq2
      obtain ⟨hns, hlr⟩ := stepAnalyzeResponse_goto_shape _ respA ns s' hresp1 hcname hbiz heq2
      rcases hns with hns | hns <;> subst hns
      · rw [show (62 : Nat) = 60 + 2 from rfl] at heq
        obtain ⟨st, hp⟩ := loop_findServers_paused
          ({ s' with currentStep := VeriDNS.Spec.AlgorithmStep.findServers }) rfl hlr 60
        rw [hp] at heq; exact absurd heq (by simp)
      ·
        rw [show (62 : Nat) = 61 + 1 from rfl, Resolver.resolve.loop] at heq
        simp only [Resolver.step, Resolver.stepSendQueries, hlr] at heq
        exact absurd heq (by simp)
    ·
      exact absurd heq (by simp)
    ·
      exact absurd heq (by simp)
  ·
    exact absurd hAR (by simp)
  ·
    exact absurd hAR (by simp)

theorem afterResume_finished_payload_pos
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    out = Resolver.finalizeAnswer
      { state with lastResponse := some respA, currentStep := .analyzeResponse } respA ∧
    cout = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      state.resources.cache respA
      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname respA) respA.answer)
      (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
      (Server.roundTouches state respA) state.now) := by
  rw [afterResume_answer state entryName respA hstep hcname hsf hcls hans] at hAR
  injection hAR with h hcout
  injection h with h
  exact ⟨h.symm, hcout.symm⟩

theorem afterResume_finished_payload_out
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    out = Resolver.finalizeAnswer
      { state with lastResponse := some respA, currentStep := .analyzeResponse } respA := by
  by_cases hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true
  · exact (afterResume_finished_payload_pos state entryName respA out
      hstep hcname hsf hcls hans hAR).1
  · exact (afterResume_finished_payload_neg state entryName respA out
      hstep hcname hsf hcls (Bool.eq_false_iff.mpr hans) hAR).1

theorem respAgree_finished_bridge
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA resp : VeriDNS.Spec.Format} {ref : VeriDNS.Spec.Net.Response}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok resp) cout)
    (hchain : state.cnameChain = #[])
    (hragA : RespAgree (αResp respA) ref) :
    RespAgree (αResp resp) { ref with aa := false } := by
  have hpay := afterResume_finished_payload_out state entryName respA resp
    hstep hcname hsf hcls hAR
  have hrc : (αResp resp).rcode = αRCode respA.header.rcode := by
    rw [hpay]; exact finalizeAnswer_abstracts_rcode _ respA
  have han : (αResp resp).answer = αSection state.cnameChain ++ αSection respA.answer := by
    rw [hpay, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
  rw [hchain] at han
  refine RespAgree.trans (RespAgree.of_eq ?_ ?_) hragA
  · rw [hrc, (αResp_components respA).1]
  · rw [han, (αResp_components respA).2.1]
    simp [αSection]

theorem afterResume_finished_not_bizarre
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA : VeriDNS.Spec.Format} {result : Except String VeriDNS.Spec.Format}
    {cout : Cache.DnsCache}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hAR : Server.afterResume state entryName respA = .finished result cout) :
    (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
      ∧ Resolver.classifiableB respA = true := by
  by_cases hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
  · by_cases hcls : Resolver.classifiableB respA = true
    · exact ⟨hsf, hcls⟩
    · exfalso
      have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
          || !Resolver.classifiableB respA) = true := by
        simp only [Bool.not_eq_true] at hcls; rw [hcls]; simp
      rw [afterResume_bizarre state entryName respA hstep hcname hbiz] at hAR
      exact Server.IoStep.noConfusion hAR
  · exfalso
    have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = true := by
      simp only [Bool.not_eq_false] at hsf; rw [hsf]; simp
    rw [afterResume_bizarre state entryName respA hstep hcname hbiz] at hAR
    exact Server.IoStep.noConfusion hAR

theorem extractNsNames_ne_of_hasRRTypeIn {RR : Type} [VeriDNS.Spec.RRParse RR]
    (authority : Array ByteArray)
    (h : Resolver.hasRRTypeIn (RR := RR) authority 2 = true) :
    Resolver.extractNsNames (RR := RR) authority ≠ #[] := by
  unfold Resolver.hasRRTypeIn at h
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, hp⟩ := h
  have hmem : authority[i] ∈ authority := Array.getElem_mem hi
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := RR) authority[i] with
  | none => rw [hpr] at hp; exact absurd hp (by simp)
  | some rr =>
    simp only [hpr] at hp
    intro hempty
    have hmemNs : VeriDNS.Spec.RRParse.rrRdata rr ∈ Resolver.extractNsNames (RR := RR) authority := by
      unfold Resolver.extractNsNames
      rw [Array.mem_filterMap]
      refine ⟨authority[i], hmem, ?_⟩
      simp only [hpr]
      split
      · rfl
      · rename_i hne; exact absurd hp hne
    rw [hempty] at hmemNs
    exact absurd hmemNs (by simp)

theorem currentCloser_false_referral (resp : VeriDNS.Spec.Format) (walkMc : Nat) (sname : ByteArray)
    (glue : Array (ByteArray × BitVec 32))
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname ≤ walkMc) :
    (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority) glue
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname))
      && decide (walkMc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority) glue
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname)))) = false := by
  apply currentCloser_false_of_ge
  · have hne := extractNsNames_ne_of_hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority hns
    simpa using hne
  · exact hge

theorem mem_extractNsNames {RR : Type} [VeriDNS.Spec.RRParse RR] (authority : Array ByteArray) (b : ByteArray)
    (h : b ∈ Resolver.extractNsNames (RR := RR) authority) :
    ∃ raw ∈ authority, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := RR) raw = some rr
      ∧ (VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)) = true
      ∧ VeriDNS.Spec.RRParse.rrRdata rr = b := by
  simp only [Resolver.extractNsNames, Array.mem_filterMap] at h
  obtain ⟨raw, hraw, hcond⟩ := h
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := RR) raw with
  | none => rw [hpr] at hcond; simp at hcond
  | some rr =>
    simp only [hpr] at hcond
    split at hcond
    · next hty => exact ⟨raw, hraw, rr, hpr, hty, Option.some.inj hcond⟩
    · simp at hcond

theorem mem_extractGlueRecords (additional : Array ByteArray) (name : ByteArray) (addr : BitVec 32)
    (h : (name, addr) ∈ Resolver.extractGlueRecords additional) :
    ∃ raw ∈ additional, ∃ rr off, DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw = .ok (rr, off)
      ∧ (rr.type == (1 : BitVec 16)) = true ∧ (rr.rdata.size == 4) = true ∧ rr.name = name := by
  simp only [Resolver.extractGlueRecords, Array.mem_filterMap] at h
  obtain ⟨raw, hraw, hcond⟩ := h
  cases hpr : DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw with
  | error e => simp only [hpr] at hcond; simp at hcond
  | ok p =>
    obtain ⟨rr, off⟩ := p
    simp only [hpr] at hcond
    split at hcond
    · next hc =>
      rw [Bool.and_eq_true] at hc
      refine ⟨raw, hraw, rr, off, hpr, hc.1, hc.2, ?_⟩
      exact (Prod.mk.inj (Option.some.inj hcond)).1
    · simp at hcond

theorem extractGlueRecords_model_addr (additional : Array ByteArray) (name : ByteArray) (addr : BitVec 32)
    (h : (name, addr) ∈ Resolver.extractGlueRecords additional) :
    ∃ raw ∈ additional, ∃ rr off a, DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw = .ok (rr, off)
      ∧ (rr.type == (1 : BitVec 16)) = true ∧ rr.name = name ∧ αIPv4 rr.rdata = some a
      ∧ byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr addr) = a.toDotted := by
  simp only [Resolver.extractGlueRecords, Array.mem_filterMap] at h
  obtain ⟨raw, hraw, hcond⟩ := h
  cases hpr : DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw with
  | error e => simp only [hpr] at hcond; simp at hcond
  | ok p =>
    obtain ⟨rr, off⟩ := p
    simp only [hpr] at hcond
    split at hcond
    · next hc =>
      rw [Bool.and_eq_true] at hc
      obtain ⟨hname, haddr⟩ := Prod.mk.inj (Option.some.inj hcond)
      have hsz : rr.rdata.size = 4 := by simpa using hc.2
      have ha : αIPv4 rr.rdata
          = some ⟨rr.rdata.data[0]!, rr.rdata.data[1]!, rr.rdata.data[2]!, rr.rdata.data[3]!⟩ := by
        unfold αIPv4; rw [if_pos hsz]
      refine ⟨raw, hraw, rr, off, _, hpr, hc.1, hname, ha, ?_⟩
      rw [← haddr]
      exact extractGlue_addr_αIPv4 rr.rdata _ ha
    · simp at hcond

theorem modelSlistOf_fromNsWithGlue_model (names additional : Array ByteArray) (mc : Nat) (s : String)
    (h : s ∈ modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names
        (Resolver.extractGlueRecords additional) mc)) :
    ∃ raw ∈ additional, ∃ rr off a, DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw = .ok (rr, off)
      ∧ (rr.type == (1 : BitVec 16)) = true ∧ αIPv4 rr.rdata = some a ∧ s = a.toDotted := by
  rw [modelSlistOf_fromNsWithGlue, List.mem_filterMap] at h
  obtain ⟨n, _, hmap⟩ := h
  rw [Option.map_eq_some_iff] at hmap
  obtain ⟨ga, hga, hs⟩ := hmap
  obtain ⟨p, hmem, hpred⟩ := Array.exists_of_findSome?_eq_some hga
  obtain ⟨gn, ga'⟩ := p
  simp only [] at hpred
  have hga'eq : ga' = ga := by
    split at hpred
    · exact Option.some.inj hpred
    · simp at hpred
  subst ga'
  obtain ⟨raw, hraw, rr, off, a, hdec, htype, _, hαiv, haddr⟩ :=
    extractGlueRecords_model_addr additional gn ga hmem
  exact ⟨raw, hraw, rr, off, a, hdec, htype, hαiv, by rw [← hs, haddr]⟩

theorem modelSlistOf_referral_eq_glueAddresses
    (names : Array ByteArray) (glueRaw : Array (ByteArray × BitVec 32)) (mc : Nat)
    (ref : VeriDNS.Spec.Net.Response)
    (hhosts : names.toList.filterMap αName = VeriDNS.Spec.Net.referredServers ref)
    (hpoint : ∀ n ∈ names.toList,
        (glueRaw.findSome? (fun (gn, ga) =>
            if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none)).map
            (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))
          = (αName n).bind (fun h =>
              (ref.additional.find? (fun r =>
                  (match r.rdata with | VeriDNS.Spec.Net.RData.a _ => true | _ => false)
                    && VeriDNS.Spec.Net.nameEq h r.owner
                    && VeriDNS.Spec.Net.isAncestor (VeriDNS.Spec.Net.referralCut ref) r.owner)).bind
                (fun r => match r.rdata with
                  | VeriDNS.Spec.Net.RData.a a => some a.toDotted | _ => none))) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glueRaw mc)
      = VeriDNS.Spec.Net.glueAddresses ref := by
  rw [modelSlistOf_fromNsWithGlue]
  unfold VeriDNS.Spec.Net.glueAddresses
  rw [← hhosts, List.filterMap_filterMap]
  exact filterMap_congr_mem _ _ _ hpoint

theorem extractGlueRecords_bailiwickRaws_fused (cut : ByteArray) (additional : Array ByteArray) :
    Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut additional)
      = additional.filterMap (fun bytes =>
          if (match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
                | some rr => Resolver.isAncestorB cut
                    (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr)
                | none => false)
          then (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
                | .ok (rr, _) =>
                  if rr.type == BitVec.ofNat 16 1 && rr.rdata.size == 4 then
                    some (rr.name,
                      (rr.rdata.data[0]!.toBitVec.setWidth 32 <<< 24) |||
                      (rr.rdata.data[1]!.toBitVec.setWidth 32 <<< 16) |||
                      (rr.rdata.data[2]!.toBitVec.setWidth 32 <<< 8) |||
                      rr.rdata.data[3]!.toBitVec.setWidth 32)
                  else none
                | .error _ => none)
          else none) := by
  unfold Resolver.extractGlueRecords Resolver.bailiwickRaws
  rw [Array.filterMap_filter]
  congr 1
  funext bytes
  cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes <;> rfl

theorem findSome?_filterMap_list {α β γ : Type} (f : α → Option β) (p : β → Option γ) (l : List α) :
    (l.filterMap f).findSome? p = l.findSome? (fun x => (f x).bind p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hfa : f a with
    | none => simp_all [List.filterMap_cons]
    | some b =>
      cases hpb : p b with
      | none => simp_all [List.filterMap_cons]
      | some c => simp_all [List.filterMap_cons]

theorem findSome?_congr_pred {α β : Type} (l : List α) (f g : α → Option β) (h : ∀ x ∈ l, f x = g x) :
    l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a (List.mem_cons_self ..)]
    cases g a with
    | none => exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | some b => rfl

theorem perm_of_nodup_mem {α : Type} [BEq α] [LawfulBEq α] {l l' : List α}
    (h : l.Nodup) (h' : l'.Nodup) (hmem : ∀ a, a ∈ l ↔ a ∈ l') : l.Perm l' := by
  rw [List.perm_iff_count]
  intro a
  rw [List.Nodup.count h, List.Nodup.count h']
  simp only [hmem a]

theorem find?_congr_pred {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..)]
    cases hq : q a with
    | true => rfl
    | false => exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem findSome?_map_comm {α β γ : Type} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.findSome? f).map g = l.findSome? (fun x => (f x).map g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hfa : f a with
    | none =>
      rw [List.findSome?_cons_of_isNone (by simp [hfa]),
          List.findSome?_cons_of_isNone (by simp [hfa])]
      exact ih
    | some b =>
      rw [List.findSome?_cons_of_isSome (by simp [hfa]),
          List.findSome?_cons_of_isSome (by simp [hfa])]

theorem αType_soa_six {t : BitVec 16} (h : αType t = some RRType.soa) :
    t = (6 : BitVec 16) := by
  have htn : t.toNat = 6 := by
    unfold αType at h
    split at h <;> simp_all
  exact BitVec.eq_of_toNat_eq (by rw [htn]; rfl)

theorem soaNegTtl_extractSoaNegative {probeB : ByteArray} {pqN : VeriDNS.Spec.Net.Name}
    {authority : Array ByteArray} {msg : VeriDNS.Spec.Net.Response}
    (hn : αName probeB = some pqN)
    (hauth : αSection authority = msg.authority)
    (hvld : ∀ b ∈ authority.toList, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
          ∧ αRR rr ≠ none) :
    VeriDNS.Spec.Net.soaNegTtl pqN msg
      = (Server.extractSoaNegative probeB authority).map (fun p => p.1.toNat) := by
  unfold VeriDNS.Spec.Net.soaNegTtl Server.extractSoaNegative
  rw [← hauth, ← Array.findSome?_toList, findSome?_map_comm]
  unfold αSection
  rw [findSome?_filterMap_list]
  apply findSome?_congr_pred
  intro b hb
  obtain ⟨rr, hpr, hne⟩ := hvld b hb
  obtain ⟨r, hα⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨pos', hdec⟩ : ∃ pos',
      DnsParser.run VeriDNS.Impl.ResourceRecord.decode b = .ok (rr, pos') := by
    have hm : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
        | .ok (rr, _) => some rr | .error _ => none) = some rr := hpr
    cases hdc : DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
    | error e => simp [hdc] at hm
    | ok p =>
      obtain ⟨rr', pos''⟩ := p
      simp only [hdc] at hm
      obtain rfl : rr' = rr := Option.some.inj hm
      exact ⟨pos'', rfl⟩
  simp only [hpr, hα, hdec, Option.bind_some]
  by_cases hty : (rr.type == (6 : BitVec 16)) = true
  · have h6 : rr.type = (6 : BitVec 16) := eq_of_beq hty
    have hαrd : αRData rr.type rr.rdata = some r.rdata := by
      unfold αRR at hα
      split at hα
      · next o rd cl ho hrd hcl =>
        rw [show r = _ from (Option.some.inj hα).symm]
        exact hrd
      · simp at hα
    rw [h6, αRData_six] at hαrd
    obtain ⟨soa, rest2, mn, rn, hdecS, hmn, hrn, hrdEq⟩ := αSoa_inv hαrd
    have hown : αName rr.name = some r.owner := (αRR_fields rr r hα).1
    have httl : r.ttl = rr.ttl.toNat := (αRR_fields rr r hα).2.1
    have hanc : Resolver.isAncestorB rr.name probeB
        = VeriDNS.Spec.Net.isAncestor r.owner pqN :=
      isAncestorB_eq rr.name probeB r.owner pqN hown hn
    rw [hrdEq]
    simp only [hty, Bool.true_and, hanc, hdecS]
    by_cases hb2 : VeriDNS.Spec.Net.isAncestor r.owner pqN = true
    · simp only [hb2, if_true, Option.map_some]
      rw [httl, computeNegativeTtl_eq_min, Nat.min_comm]
    · simp only [Bool.not_eq_true] at hb2
      simp [hb2]
  · rw [Bool.not_eq_true] at hty
    have hnot : r.rdata.rtype ≠ RRType.soa := by
      intro hsoa
      have h6t : αType rr.type = some RRType.soa := hsoa ▸ αRR_rtype rr r hα
      rw [αType_soa_six h6t] at hty
      simp at hty
    simp only [hty, Bool.false_and, Bool.false_eq_true, if_false, Option.map_none]
    cases hrd : r.rdata with
    | soa m1 m2 s rf rt ex mi =>
      exact absurd (by rw [hrd]; rfl) hnot
    | a addr => rfl
    | ns x => rfl
    | cname x => rfl
    | mx p e => rfl
    | hinfo cu os => rfl
    | ptr x => rfl
    | generic t d => rfl

theorem find?_bind_eq_findSome? {α β : Type} (p : α → Bool) (g : α → Option β) (l : List α)
    (h : ∀ x ∈ l, p x = true → (g x).isSome = true) :
    (l.find? p).bind g = l.findSome? (fun x => if p x then g x else none) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hpa : p a with
    | false =>
      simp only [List.find?_cons, hpa, Bool.false_eq_true, if_false]
      rw [List.findSome?_cons_of_isNone (by simp [hpa])]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | true =>
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..) hpa)
      simp [List.find?_cons, hpa, hc]

theorem findSome?_ite_some {α β : Type} (p : α → Bool) (h : α → β) (l : List α) :
    l.findSome? (fun x => if p x then some (h x) else none) = (l.find? p).map h := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hpa : p a with
    | true => simp_all [List.find?_cons]
    | false => simp_all [List.find?_cons]

theorem rederived_glue_keyed {β : Type} (nsNames : List ByteArray) (n : ByteArray)
    (hglue : ByteArray → Option (ByteArray × β))
    (hkey : ∀ m, ∀ gp ∈ hglue m, gp.1 = m) :
    (nsNames.filterMap hglue).findSome? (fun gp => if DomainName.nameEqCI gp.1 n then some gp.2 else none)
      = nsNames.findSome? (fun m => if DomainName.nameEqCI m n then (hglue m).map Prod.snd else none) := by
  rw [findSome?_filterMap_list]
  apply findSome?_congr_pred
  intro m _
  cases hgm : hglue m with
  | none => simp
  | some gp =>
    have hk : gp.1 = m := hkey m gp (Option.mem_def.mpr hgm)
    simp only [Option.bind_some, hk, Option.map_some]

theorem findSome?_const_on_pred {α β : Type} (l : List α) (p : α → Bool) (g : α → Option β) (v : Option β)
    (hconst : ∀ m ∈ l, p m = true → g m = v) (hex : ∃ m ∈ l, p m = true) :
    l.findSome? (fun m => if p m then g m else none) = v := by
  cases v with
  | none =>
    rw [List.findSome?_eq_none_iff]
    intro m hm
    show (if p m then g m else none) = none
    by_cases hp : p m
    · rw [if_pos hp, hconst m hm hp]
    · rw [if_neg hp]
  | some w =>
    induction l with
    | nil => exact absurd hex (by simp)
    | cons a t ih =>
      by_cases hp : p a
      · have hfa : (if p a then g a else none) = some w := by
          rw [if_pos hp, hconst a (List.mem_cons_self ..) hp]
        rw [List.findSome?_cons, hfa]
      · have hfa : (if p a then g a else none) = none := by rw [if_neg hp]
        rw [List.findSome?_cons, hfa]
        exact ih
          (by obtain ⟨m, hm, hpm⟩ := hex
              rcases List.mem_cons.mp hm with rfl | hmt
              · exact absurd hpm hp
              · exact ⟨m, hmt, hpm⟩)
          (fun m hm hpm => hconst m (List.mem_cons_of_mem a hm) hpm)

theorem gluePerHost_rederived {β : Type} (nsNames : List ByteArray) (n : ByteArray)
    (aGlue : ByteArray → Option β) (hn : n ∈ nsNames)
    (hresp : ∀ m ∈ nsNames, nameEqCI m n = true → aGlue m = aGlue n) :
    (nsNames.filterMap (fun m => (aGlue m).map (Prod.mk m))).findSome?
        (fun gp => if nameEqCI gp.1 n then some gp.2 else none)
      = aGlue n := by
  have hkey : ∀ m, ∀ gp ∈ (fun m => (aGlue m).map (Prod.mk m)) m, gp.1 = m := by
    intro m gp hgp
    change gp ∈ (aGlue m).map (Prod.mk m) at hgp
    cases hag : aGlue m with
    | none => rw [hag] at hgp; simp at hgp
    | some a => rw [hag] at hgp; simp only [Option.map_some, Option.mem_some_iff] at hgp; subst hgp; rfl
  rw [rederived_glue_keyed nsNames n (fun m => (aGlue m).map (Prod.mk m)) hkey]
  have hmap : ∀ m, ((aGlue m).map (Prod.mk m)).map Prod.snd = aGlue m := by
    intro m; cases aGlue m <;> rfl
  simp only [hmap]
  exact findSome?_const_on_pred nsNames (fun m => nameEqCI m n) aGlue (aGlue n)
    (fun m hm hpm => hresp m hm hpm) ⟨n, hn, VeriDNS.Proof.NameTree.nameEqCI_refl n⟩

theorem afterResume_referral_continues
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp⟩ := resume_referral_paused state resp hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  unfold Server.afterResume
  rw [hdrop, hp]
  exact ⟨_, rfl⟩

theorem afterResume_referral_continue_struct
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) state.now)
            resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
            Resolver.credAdditional state.now).boundLru
            (Server.roundTouches state resp) state.now
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp, hc, hsn, hnw, hcc, hcs⟩ :=
    resume_referral_paused_struct state resp hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  unfold Server.afterResume
  rw [hdrop, hp]
  refine ⟨Server.boundStateCache (Server.roundTouches state resp) st, rfl, ?_, hsn, hnw, hcc, hcs⟩
  show st.resources.cache.boundLru (Server.roundTouches state resp) st.now = _
  rw [hc, hnw]

theorem afterResume_referral_continue_cases
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now).boundLru
          (Server.roundTouches state resp) state.now
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery
      ∧ st.resources.sbelt = state.resources.sbelt
      ∧ ( st.resources.slist = (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) nsNames
                  (reGlue (RR := VeriDNS.Spec.ResourceRecord) (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now) state.now nsNames) mc)
          ∨ (st.resources.slist = state.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false) ) := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp, hcache, hsn, hnw, hcc, hcs, hlq, hsb, hdisj⟩ :=
    resume_referral_paused_cases state resp hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  unfold Server.afterResume
  rw [hdrop, hp]
  refine ⟨Server.boundStateCache (Server.roundTouches state resp) st, rfl, ?_, hsn, hnw, hcc, hcs, hlq, ?_, ?_⟩
  · show st.resources.cache.boundLru (Server.roundTouches state resp) st.now = _
    rw [hcache, hnw]
  · exact hsb
  · exact hdisj

theorem afterResume_referral_continue_slist
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format) (nsNames : Array ByteArray) (mc : Nat)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false)
    (hnb : ((reGlue (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        state.now nsNames).isEmpty && (mc == 0)) = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry) nsNames
          (reGlue (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
                (Resolver.credAuthority (resp.header.aa == 1)) state.now)
              resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
              Resolver.credAdditional state.now)
            state.now nsNames) mc
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp, hsl, _hc, hsn, hnw, hcc, hcs, hlq⟩ :=
    resume_referral_paused_slist state resp nsNames mc hstep hcname hbiz hans hnerr hansEmpty hauth hns
      haa hrc hsoa hwalk hclose hnb
  unfold Server.afterResume
  rw [hdrop, hp]
  exact ⟨Server.boundStateCache (Server.roundTouches state resp) st, rfl, hsl, hsn, hnw, hcc, hcs, hlq⟩

theorem storeChecked_ttl_zero (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) (h : rr.ttl = 0) :
    c.storeChecked rr cred now = c := by
  unfold Cache.DnsCache.storeChecked
  simp [h]

theorem storeChecked_blocks_weaker (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32)
    (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hname : DomainName.nameEqCI e.rr.name rr.name = true)
    (htype : (e.rr.type == rr.type) = true) (hclass : (e.rr.class == rr.class) = true)
    (hfresh : e.expiry > now)
    (hbetter : e.credibility.toCode < cred.toCode)
    (hnz : rr.ttl ≠ 0) :
    c.storeChecked rr cred now = c := by
  obtain ⟨i, hi, hei⟩ := Array.getElem_of_mem he
  have hz : (rr.ttl == 0) = false := by rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; exact hnz
  have hcond : (c.records.any fun e2 =>
      DomainName.nameEqCI e2.rr.name rr.name && e2.rr.type == rr.type && e2.rr.class == rr.class
        && (e2.expiry > now || e2.expiry == now + rr.ttl.toNat.toUInt32)
        && e2.credibility.toCode < cred.toCode) = true := by
    rw [Array.any_eq_true]
    exact ⟨i, hi, by rw [hei]; simp [hname, htype, hclass, hfresh, hbetter]⟩
  unfold Cache.DnsCache.storeChecked
  simp only [hz, hcond, if_false, if_true, Bool.false_eq_true]

theorem finalizeForClient_flags (resp : VeriDNS.Spec.Format) :
    (Server.finalizeForClient resp).header.qr = 1
      ∧ (Server.finalizeForClient resp).header.aa = 0
      ∧ (Server.finalizeForClient resp).header.ra = 1
      ∧ (Server.finalizeForClient resp).header.z = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem acceptResponse_requires_match (sent resp : VeriDNS.Spec.Format)
    (h : Server.acceptResponse sent resp = some resp) :
    (resp.header.id == sent.header.id) = true
      ∧ Server.questionMatches resp.question sent.question = true := by
  unfold Server.acceptResponse at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    exact hcond
  · exact absurd h (by simp)

theorem resolveWithIO_negHit_nx_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqu : query.question[0]? = some qu)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t)
    (hnx : cache.lookupNxdomain qu.qname qu.qclass now = some rc) :
    ∃ resp,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ RespAgree (αResp resp) ((αCache cache).negResponse (αTime now) q)
      ∧ VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q
          ((αCache cache).negTrace (αTime now) q) [] (αTime now) (αCache cache)
          ((αCache cache).negResponse (αTime now) q) := by
  have hlk : cache.lookupNegative qu.qname qu.qtype qu.qclass now = some rc := by
    unfold Cache.DnsCache.lookupNegative; rw [hnx]; rfl
  have hneg : (αCache cache).negHit (αTime now) q = true :=
    lookupNegative_negHit cache qu.qname qu.qtype qu.qclass now rc q t hlk hqn ht hqq
  have hnxName : rc = VeriDNS.Spec.Rcode.nameError :=
    lookupNxdomain_nameError cache qu.qname qu.qclass now rc hnx
  have hnxnx : (αCache cache).negHitNx (αTime now) q = true :=
    lookupNxdomain_negHitNx cache qu.qname qu.qclass now rc q hnx hqn
  have hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection
          (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qu.qname qu.qtype qu.qclass now) #[] :=
    localAnswer_negative cache qu.qtype qu.qclass now 7 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) rc hlk
  refine ⟨_, resolveWithIO_negHit query sbelt cache now fuel depth budget qu rc _ #[] hqu hla, ?_, ?_⟩
  · refine RespAgree.of_eq ?_ ?_
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).2]
      simp only [VeriDNS.Spec.Net.Cache.negResponse, hnxnx, hnxName]
      rfl
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).1]
      simp only [VeriDNS.Spec.Net.Cache.negResponse]
  · exact VeriDNS.Spec.Net.Resolves.negHit (αCache cache) slist q hneg


theorem resolveWithIO_negHit_nodata_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqu : query.question[0]? = some qu)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t)
    (hlk : cache.lookupNegative qu.qname qu.qtype qu.qclass now = some rc)
    (hnodata : (αCache cache).negHitNx (αTime now) q = false)
    (hrc : rc = VeriDNS.Spec.Rcode.noError) :
    ∃ resp,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ RespAgree (αResp resp) ((αCache cache).negResponse (αTime now) q)
      ∧ VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q
          ((αCache cache).negTrace (αTime now) q) [] (αTime now) (αCache cache)
          ((αCache cache).negResponse (αTime now) q) := by
  have hneg : (αCache cache).negHit (αTime now) q = true :=
    lookupNegative_negHit cache qu.qname qu.qtype qu.qclass now rc q t hlk hqn ht hqq
  have hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection
          (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qu.qname qu.qtype qu.qclass now) #[] :=
    localAnswer_negative cache qu.qtype qu.qclass now 7 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) rc hlk
  refine ⟨_, resolveWithIO_negHit query sbelt cache now fuel depth budget qu rc _ #[] hqu hla, ?_, ?_⟩
  · refine RespAgree.of_eq ?_ ?_
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).2]
      simp only [VeriDNS.Spec.Net.Cache.negResponse, hnodata, hrc]
      rfl
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).1]
      simp only [VeriDNS.Spec.Net.Cache.negResponse]
  · exact VeriDNS.Spec.Net.Resolves.negHit (αCache cache) slist q hneg


theorem resolveWithIO_cacheHit_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hnoneg : cache.lookupNegative qu.qname qu.qtype qu.qclass now = none)
    (hans : VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now = rrs)
    (hrne : rrs.isEmpty = false)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qu.qclass = some q.qclass)
    (hcanN : qu.qname = DomainName.labelsToWireFormatGo q.qname)
    (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ cache.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∃ resp,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ RespAgree (αResp resp)
          { aa := false, rcode := VeriDNS.Spec.Net.RCode.noError,
            answer := (αCache cache).hit (αTime now) q, authority := [], additional := [] }
      ∧ VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q
          [VeriDNS.Spec.Net.Step.fromCache] [] (αTime now) (αCache cache)
          { aa := false, rcode := VeriDNS.Spec.Net.RCode.noError,
            answer := (αCache cache).hit (αTime now) q, authority := [], additional := [] } := by
  have hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .answerHit qu.qname #[] rrs :=
    localAnswer_answerHit cache qu.qtype qu.qclass now 7 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) rrs hnoneg hans hrne
  obtain ⟨resp, hresp, hrc, hansr⟩ :=
    resolveWithIO_answerHit_payload (M := M) (Sock := Sock)
      query sbelt cache now fuel depth budget qu qu.qname #[] rrs hqu hla
  have hrrs : rrs = cache.lookupAnswerable qu.qname qu.qtype qu.qclass now := hans.symm
  have hwfrrs : ∀ rr ∈ cache.lookupAnswerable qu.qname qu.qtype qu.qclass now,
      VeriDNS.Proof.NameTree.WfRR rr := by
    intro rr hrr
    obtain ⟨e, he, -, hrre⟩ := lookupAnswerable_mem_entry (Array.mem_def.mp hrr)
    rw [hrre]
    exact VeriDNS.Proof.NameTree.wfRR_set_ttl (hwfrr e he) _
  have hhit : αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
      = (αCache cache).hit (αTime now) q := by
    rw [hrrs]
    exact hhit_of_invariants cache qu.qname qu.qtype qu.qclass now q t hqn ht hqq hqc hcanN hvN
      hwf hcanon hused hwfrrs
  have heq : (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now).toList.filterMap αRR
      = (αCache cache).hit (αTime now) q :=
    lookupAnswerable_αRR_eq_hit cache qu.qname qu.qtype qu.qclass now q t hqn ht hqq hqc hcanN hvN
      hwf hcanon hused
  have hne : 0 < ((αCache cache).hit (αTime now) q).length := by
    have hnil : cache.lookupAnswerable qu.qname qu.qtype qu.qclass now ≠ #[] := by
      intro h0
      rw [h0] at hrrs
      rw [hrrs] at hrne
      exact absurd hrne (by simp)
    have hsz : 0 < (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now).size := by
      rcases Nat.eq_zero_or_pos
          (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now).size with h0 | h
      · exact absurd (Array.size_eq_zero_iff.mp h0) hnil
      · exact h
    have hmem0 : (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now)[0]
        ∈ (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now).toList :=
      Array.mem_def.mp (Array.getElem_mem hsz)
    obtain ⟨⟨cn0, hαcn0⟩, -⟩ := lookupAnswerable_αRR_isSome hwf hmem0
    have hmemM : cn0 ∈ (αCache cache).hit (αTime now) q := by
      rw [← heq]
      exact List.mem_filterMap.mpr ⟨_, hmem0, hαcn0⟩
    cases hml : (αCache cache).hit (αTime now) q with
    | nil => rw [hml] at hmemM; exact absurd hmemM (by simp)
    | cons a l => simp
  refine ⟨resp, hresp, ⟨hrc, ?_⟩, ?_⟩
  · rw [hansr, show αSection #[] = [] from rfl, List.nil_append, hhit]
  · exact VeriDNS.Spec.Net.Resolves.cacheHit (αCache cache) slist q
      ((αCache cache).hit (αTime now) q) rfl hne

section NetworkBranches
open VeriDNS.Spec.Net

theorem answer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step)
    (resp : Response) (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr resp)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q)
        (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
    (hnr : reply.msg.isReferral = false)
    (hnc : cnameRR q.qname reply.msg.answer = none ∨ q.qtype.covers RRType.cname = true
            ∨ (∃ rr ∈ reply.msg.answer, q.qtype.covers rr.rdata.rtype = true))
    (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply
     htrans hacc hwire hnr hnc htc, hbridge⟩

theorem trustedReply_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hnr : reply.msg.isReferral = false) (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false })

    (cf0 : Cache)
    (hcf0 : WriteRefines now cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname))
            ∨ cf0 = c)
    (cf : Cache) (hcf : WriteRefines now cf cf0) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc
     cf0 hcf0 cf hcf, hbridge⟩

theorem trustedReferral_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (frontier : Name)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hcut : isAncestor (referralCut reply.msg) q.qname = true)
    (hdesc : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String) (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick frontier (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ftr, rpath, tEnd, cout, final, hres, hbridge⟩ := hrec
  exact ⟨_, _, _, _, _,
    Resolves.trustedReferral addr origin rest q q frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss (ProbeQuery.refl q) reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hres,
    hbridge⟩

theorem refer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
    (id srcPort : Nat) (c cout : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hglue : glueAddresses reply.msg ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now')
    (sl : List String)
    (hsl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm sl)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg)
        sl q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.refer addr rest q q srv tr ref ftr rpath tEnd final id srcPort c cout
     hmiss hnmiss (ProbeQuery.refl q) hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec,
   hbridge⟩

theorem referForget_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
    (id srcPort : Nat) (c cout : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now')
    (sl : List String)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache)
    (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        cf sl q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.referForget addr rest q q srv tr ref ftr rpath tEnd final id srcPort c cout
     hmiss hnmiss (ProbeQuery.refl q) hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec,
   hbridge⟩

theorem answerCname_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (resp : Response)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr resp)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q)
        (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
    (hcn : cnameRR q.qname reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname)))
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
     hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

theorem trustedCname_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hcn : cnameRR q.qname reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname)))
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
     hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

theorem cacheCname_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (slist : List String) (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen)
    (cf : Cache) (hcf : CacheRefines cf c)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
        { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v :=
  ⟨_, _, _, _, _,
   Resolves.cacheCname slist q cn target c nsl ftr rpath tEnd cout final
     hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec, hbridge⟩

theorem cacheCname_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (slist : List String) (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen)
    (cf : Cache) (hcf : CacheRefines cf c)
    (vsub v : Response) (hrc : v.rcode = vsub.rcode) (hva : v.answer = cn :: vsub.answer)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
        { q with qname := target } vsub) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v := by
  obtain ⟨tr', sp', tEnd', cout', resp', hres, hag⟩ := hrec
  refine ⟨_, _, _, _, _, Resolves.cacheCname slist q cn target c nsl tr' sp' tEnd' cout' resp'
    hmiss hnmiss hcn hqt htgt hfresh cf hcf hres, ?_⟩
  exact ⟨hrc.trans hag.1, by rw [hva]; exact List.Perm.cons cn hag.2⟩

theorem cacheHit_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query) (here : List RR)
    (hhit : c.hit now q = here) (hne : 0 < here.length)
    (v : Response)
    (hbridge : RespAgree v (VeriDNS.Spec.Net.Response.mk false VeriDNS.Spec.Net.RCode.noError here [] [] false false)) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v :=
  ⟨_, _, _, _, _, Resolves.cacheHit c slist q here hhit hne, hbridge⟩

theorem negHit_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query)
    (hneg : c.negHit now q = true)
    (v : Response) (hbridge : RespAgree v (c.negResponse now q)) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v :=
  ⟨_, _, _, _, _, Resolves.negHit c slist q hneg, hbridge⟩

theorem timeout_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache) (d : Datagram)
    (hdrop : Transit (linkReach net ns resolverAddr) addr resolverAddr d none)
    (hmono : now ≤ now')
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _, Resolves.timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec, hbridge⟩

theorem hasVerdict_timeout_prepend
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (q : Query) (v : Response) (L : List String) {rest : List String}
    (h : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (L ++ rest) q v := by
  induction L with
  | nil => simpa using h
  | cons a t ih =>
    obtain ⟨tr, sp, tEnd, cout, resp, hres, hrag⟩ := ih
    exact ⟨_, _, _, _, _,
      Resolves.timeout a (t ++ rest) q tr sp tEnd resp c cout default
        (Transit.lost a resolverAddr default) (Nat.le_refl now) hres, hrag⟩

theorem skipMissing_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache)
    (hfind : serverAt net addr = none)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _, Resolves.skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec, hbridge⟩

theorem gluelessNs_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now1 : Time} {nseen : List Name} {seen : List Name}
    (q : Query) (zone : Name) (nsHost : Name) (nsAddr : String)
    (nsNseen nsSeen : List Name) (nsSlist : List String) (nsTr : List Step)
    (nsPath : List String) (nsEnd : Time) (nsResp : Response)
    (slist2 : List String) (ftr : List Step) (rpath : List String) (tEnd : Time)
    (final : Response) (c c2 cout : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hanc : isAncestor zone q.qname = true)
    (cprov : Cache)
    (hns : nsHost ∈ cprov.nsHostsAt now zone)
    (hmono1 : now ≤ now1)
    (hnsres : Resolves net ns resolverAddr ednsBuf rttOf now1 nsNseen nsSeen c nsSlist
        ⟨nsHost, QType.rr RRType.a, RRClass.in, false⟩ nsTr nsPath nsEnd c2 nsResp)
    (hnsaddr : addressOf nsResp = some nsAddr)
    (hmem : nsAddr ∈ slist2)
    (c2f : Cache) (hc2f : CacheRefines c2f c2)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c2f slist2 q
        ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c [] q v :=
  ⟨_, _, _, _, _,
   Resolves.gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
     slist2 ftr rpath tEnd final c c2 cout hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem
     c2f hc2f hrec,
   hbridge⟩

theorem rejectSpoof_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache) (id srcPort : Nat) (reply : Datagram)
    (hreject : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = false)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.rejectSpoof addr rest q q ftr rpath tEnd final c cout id srcPort reply (ProbeQuery.refl q) hreject hrec, hbridge⟩

theorem exhausted_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (q : Query)
    (v : Response)
    (hbridge : RespAgree v
      { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c [] q v :=
  ⟨_, _, _, _, _, Resolves.exhausted c q, hbridge⟩

theorem chooseServer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (slist slist' : List String) (q : Query)
    (c : Cache) (v : Response)
    (hperm : slist'.Perm slist)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist' q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v := by
  obtain ⟨tr, sp, tEnd, cout, resp, hres, hag⟩ := hrec
  exact ⟨tr, sp, tEnd, cout, resp, Resolves.chooseServer slist slist' q tr sp tEnd resp c cout hperm hres, hag⟩



theorem refer_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hglue : glueAddresses reply.msg ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String)
    (hsl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm sl)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg)
        sl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact refer_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref _ _ _ _ id srcPort
    c _ hmiss hnmiss hfind hans reply htrans hacc hwire href hbail hdesc frontier hdescF hglue hfresh hmono sl hsl hres v hag

theorem referForget_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache)
    (hcf : WriteRefines now' cf cf0)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact referForget_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref _ _ _ _ id srcPort
    c _ hmiss hnmiss hfind hans reply htrans hacc hwire href hbail hdesc frontier hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hres v hag

theorem refer_hasVerdict_perm
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hglue : glueAddresses reply.msg ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (gl : List String)
    (hgl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm gl)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg)
        gl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=

  refer_hasVerdict_hv net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref id srcPort c
    hmiss hnmiss hfind hans reply htrans hacc hwire href hbail hdesc frontier hdescF hglue hfresh hmono v gl hgl hrec

theorem timeout_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache) (d : Datagram)
    (hdrop : Transit (linkReach net ns resolverAddr) addr resolverAddr d none)
    (hmono : now ≤ now') (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact timeout_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ d hdrop hmono
    hres v hag

theorem skipMissing_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache)
    (hfind : serverAt net addr = none) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact skipMissing_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ hfind hres v hag

theorem rejectSpoof_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache) (id srcPort : Nat) (reply : Datagram)
    (hreject : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = false) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact rejectSpoof_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ id srcPort
    reply hreject hres v hag

theorem badResponse_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache) (id srcPort : Nat) (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hbad : reply.msg.rcode = RCode.servFail)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.badResponse addr rest q q ftr rpath tEnd final c cout id srcPort reply (ProbeQuery.refl q) htrans hacc (Or.inl hbad) hrec,
   hbridge⟩

theorem badResponse_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache) (id srcPort : Nat) (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hbad : reply.msg.rcode = RCode.servFail) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact badResponse_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ id srcPort
    reply htrans hacc hbad hres v hag

theorem unfollowableReferral_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (href : reply.msg.isReferral = true)
    (hunfollow : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = false) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact ⟨_, _, _, _, _,
    Resolves.unfollowableReferral addr rest q q srv tr ref id srcPort _ _ _ _ c _ reply hmiss hnmiss
      (ProbeQuery.refl q) hfind hans htrans hacc href hunfollow hres, hag⟩



theorem trustedReply_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hnr : reply.msg.isReferral = false) (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false })
    (cf0 : Cache)
    (hcf0 : WriteRefines now cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname))
            ∨ cf0 = c)
    (cf : Cache) (hcf : WriteRefines now cf cf0) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v cf :=
  ⟨_, _, _, _,
   Resolves.trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc
     cf0 hcf0 cf hcf, hbridge⟩

theorem ancestorDenied_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q pq : Query) (id srcPort : Nat) (c : Cache)
    (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hprobe : StrictProbe pq q)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
    (hrc : reply.msg.rcode = RCode.nameError)
    (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false })
    (cf0 : Cache)
    (hcf0 : WriteRefines now cf0 (c.absorbNeg now pq reply.msg) ∨ cf0 = c)
    (cf : Cache) (hcf : NegWriteRefines now cf cf0) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v cf :=
  ⟨_, _, _, _,
   Resolves.ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans
     hacc hrc htc cf0 hcf0 cf hcf, hbridge⟩

theorem trustedReferral_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (frontier : Name)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hcut : isAncestor (referralCut reply.msg) q.qname = true)
    (hdesc : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String) (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick frontier (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache) (hcf : WriteRefines now' cf cf0) (coutM : Cache)
    (hrec : HasVerdictAt net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v coutM := by
  obtain ⟨ftr, rpath, tEnd, final, hres, hbridge⟩ := hrec
  exact ⟨_, _, _, _,
    Resolves.trustedReferral addr origin rest q q frontier ftr rpath tEnd final id srcPort c coutM
      hmiss hnmiss (ProbeQuery.refl q) reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hres,
    hbridge⟩

theorem trustedReferralProbe_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q pq : Query) (frontier : Name)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hprobe : ProbeQuery pq q)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hcut : isAncestor (referralCut reply.msg) pq.qname = true)
    (hdesc : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String) (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick frontier (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache) (hcf : WriteRefines now' cf cf0) (coutM : Cache)
    (hrec : HasVerdictAt net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v coutM := by
  obtain ⟨ftr, rpath, tEnd, final, hres, hbridge⟩ := hrec
  exact ⟨_, _, _, _,
    Resolves.trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c coutM
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hres,
    hbridge⟩

theorem trustedCname_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hcn : cnameRR q.qname reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname)))
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v cout :=
  ⟨_, _, _, _,
   Resolves.trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
     hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

theorem cacheCname_hasVerdictAt_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (slist : List String) (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen)
    (cf : Cache) (hcf : CacheRefines cf c)
    (vsub v : Response) (hrc : v.rcode = vsub.rcode) (hva : v.answer = cn :: vsub.answer)
    (coutM : Cache)
    (hrec : HasVerdictAt net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
        { q with qname := target } vsub coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v coutM := by
  obtain ⟨tr', sp', tEnd', resp', hres, hag⟩ := hrec
  refine ⟨_, _, _, _, Resolves.cacheCname slist q cn target c nsl tr' sp' tEnd' coutM resp'
    hmiss hnmiss hcn hqt htgt hfresh cf hcf hres, ?_⟩
  exact ⟨hrc.trans hag.1, by rw [hva]; exact List.Perm.cons cn hag.2⟩

theorem cacheHit_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query) (here : List RR)
    (hhit : c.hit now q = here) (hne : 0 < here.length)
    (v : Response)
    (hbridge : RespAgree v (VeriDNS.Spec.Net.Response.mk false VeriDNS.Spec.Net.RCode.noError here [] [] false false)) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v c :=
  ⟨_, _, _, _, Resolves.cacheHit c slist q here hhit hne, hbridge⟩

theorem negHit_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query)
    (hneg : c.negHit now q = true)
    (v : Response) (hbridge : RespAgree v (c.negResponse now q)) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v c :=
  ⟨_, _, _, _, Resolves.negHit c slist q hneg, hbridge⟩

theorem hasVerdictAt_timeout_prepend
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (q : Query) (v : Response) (coutM : Cache) (L : List String) {rest : List String}
    (h : HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (L ++ rest) q v coutM := by
  induction L with
  | nil => simpa using h
  | cons a t ih =>
    obtain ⟨tr, sp, tEnd, resp, hres, hrag⟩ := ih
    exact ⟨_, _, _, _,
      Resolves.timeout a (t ++ rest) q tr sp tEnd resp c coutM default
        (Transit.lost a resolverAddr default) (Nat.le_refl now) hres, hrag⟩

end NetworkBranches

theorem initFromQuery_cache (q : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (now : UInt32)
    (initCache : Cache.DnsCache) :
    (Resolver.initFromQuery (S := SList.DnsSList) (C := Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
      (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache).resources.cache = initCache := rfl

theorem initFromQuery_now (q : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (now : UInt32)
    (initCache : Cache.DnsCache) :
    (Resolver.initFromQuery (S := SList.DnsSList) (C := Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
      (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache).now = now := rfl

theorem initFromQuery_sname (q : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (now : UInt32)
    (initCache : Cache.DnsCache) (qu : VeriDNS.Spec.Question) (hqu : q.question[0]? = some qu) :
    (Resolver.initFromQuery (S := SList.DnsSList) (C := Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
      (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache).resources.sname = qu.qname := by
  unfold Resolver.initFromQuery
  simp only [hqu]




theorem resolveWithIO_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqu : query.question[0]? = some qu)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t)
    (houtcome :
      (∃ rc, cache.lookupNxdomain qu.qname qu.qclass now = some rc)
      ∨ (∃ rc, cache.lookupNegative qu.qname qu.qtype qu.qclass now = some rc
            ∧ (αCache cache).negHitNx (αTime now) q = false ∧ rc = VeriDNS.Spec.Rcode.noError)
      ∨ (∃ rrs, cache.lookupNegative qu.qname qu.qtype qu.qclass now = none
            ∧ VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
                (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now = rrs
            ∧ rrs.isEmpty = false
            ∧ αClass qu.qclass = some q.qclass
            ∧ qu.qname = DomainName.labelsToWireFormatGo q.qname
            ∧ (∀ x ∈ q.qname, x.size ≤ 63)
            ∧ (∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
                ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
            ∧ (∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
                e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner
                ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
            ∧ (∀ e ∈ cache.records, e.credibility = Trustworthiness.authoritativeSection
                ∨ e.credibility = Trustworthiness.authoritySection
                ∨ e.credibility = Trustworthiness.sectionNonauthoritative
                ∨ e.credibility = Trustworthiness.additionalAuthoritative)
            ∧ (∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr))
      ∨ (∃ resp cout,
            Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
              = pure (.ok resp, cout)
            ∧ HasVerdict net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
                (αCache cache) slist q (αResp resp))) :
    ∃ resp cout,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cout)
      ∧ HasVerdict net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q (αResp resp) := by
  rcases houtcome with ⟨rc, hnx⟩ | ⟨rc, hlk, hnodata, hrc⟩
    | ⟨rrs, hnoneg, hans, hrne, hqc, hcanN, hvN, hwf, hcanon, hused, hwfrr⟩ | hnet
  ·
    obtain ⟨resp, hrun, hagree, hres⟩ := resolveWithIO_negHit_nx_simulates (M := M) (Sock := Sock)
      net ns resolverAddr
      ednsBuf rttOf nseen seen slist query sbelt cache now fuel depth budget qu rc q t
      hqu hqn ht hqq hnx
    exact ⟨resp, cache, hrun, _, _, _, _, _, hres, hagree⟩
  ·
    obtain ⟨resp, hrun, hagree, hres⟩ := resolveWithIO_negHit_nodata_simulates (M := M) (Sock := Sock)
      net ns resolverAddr
      ednsBuf rttOf nseen seen slist query sbelt cache now fuel depth budget qu rc q t
      hqu hqn ht hqq hlk hnodata hrc
    exact ⟨resp, cache, hrun, _, _, _, _, _, hres, hagree⟩
  ·
    obtain ⟨resp, hrun, hagree, hres⟩ := resolveWithIO_cacheHit_simulates (M := M) (Sock := Sock)
      net ns resolverAddr
      ednsBuf rttOf nseen seen slist query sbelt cache now fuel depth budget qu q t rrs
      hqu hnoneg hans hrne hqn ht hqq hqc hcanN hvN hwf hcanon hused hwfrr
    exact ⟨resp, cache, hrun, _, _, _, _, _, hres, hagree⟩
  ·
    obtain ⟨resp, cout, hrun, hverdict⟩ := hnet
    exact ⟨resp, cout, hrun, hverdict⟩

end VeriDNS.Proof.Refinement

rfc_proves VeriDNS.Proof.Refinement.served_is_per_key_maximal [1035][2589:2591]

rfc_proves VeriDNS.Proof.Refinement.acceptResponse_requires_match [5452][349:353]
