import VeriDNS.Proof.Depth1Adequacy




namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message


theorem nameEqCI_symm {a b : ByteArray}
    (h : VeriDNS.Impl.DomainName.nameEqCI a b = true) :
    VeriDNS.Impl.DomainName.nameEqCI b a = true := by
  unfold VeriDNS.Impl.DomainName.nameEqCI at h ⊢
  rw [VeriDNS.Proof.Refinement.byteArray_beq_iff_eq] at h ⊢
  exact h.symm

theorem nameEqCI_trans {a b c : ByteArray}
    (h1 : VeriDNS.Impl.DomainName.nameEqCI a b = true)
    (h2 : VeriDNS.Impl.DomainName.nameEqCI b c = true) :
    VeriDNS.Impl.DomainName.nameEqCI a c = true := by
  unfold VeriDNS.Impl.DomainName.nameEqCI at h1 h2 ⊢
  rw [VeriDNS.Proof.Refinement.byteArray_beq_iff_eq] at h1 h2 ⊢
  exact h1.trans h2


def DescentGlueInv (c : DnsCache) (used : Array ByteArray) : Prop :=
  ∀ e ∈ c.records,
    (e.rr.type == BitVec.ofNat 16 1 && e.rr.class == BitVec.ofNat 16 1) = true →
    ∃ g ∈ used, VeriDNS.Impl.DomainName.nameEqCI e.rr.name g = true

theorem DescentGlueInv.of_empty {c : DnsCache} (h : c.records = #[]) (used : Array ByteArray) :
    DescentGlueInv c used := by
  intro e he
  rw [h] at he
  simp at he

theorem DescentGlueInv.mono {c : DnsCache} {used used' : Array ByteArray}
    (hinv : DescentGlueInv c used) (h : ∀ g ∈ used, g ∈ used') : DescentGlueInv c used' := by
  intro e he ht
  obtain ⟨g, hg, hci⟩ := hinv e he ht
  exact ⟨g, h g hg, hci⟩

theorem DescentGlueInv.aNone {c : DnsCache} {used : Array ByteArray}
    (hinv : DescentGlueInv c used) (target : ByteArray)
    (hfresh : ∀ g ∈ used, VeriDNS.Impl.DomainName.nameEqCI g target = false) :
    ∀ e ∈ c.records,
      (VeriDNS.Impl.DomainName.nameEqCI e.rr.name target
        && e.rr.type == BitVec.ofNat 16 1 && e.rr.class == BitVec.ofNat 16 1) = false := by
  intro e he
  by_cases ht : (e.rr.type == BitVec.ofNat 16 1) = true
  · by_cases hc : (e.rr.class == BitVec.ofNat 16 1) = true
    · obtain ⟨g, hg, hci⟩ := hinv e he (by rw [ht, hc]; rfl)
      have hne : VeriDNS.Impl.DomainName.nameEqCI e.rr.name target = false := by
        cases hx : VeriDNS.Impl.DomainName.nameEqCI e.rr.name target with
        | false => rfl
        | true =>
          have hgt := nameEqCI_trans (nameEqCI_symm hci) hx
          rw [hfresh g hg] at hgt
          exact absurd hgt (by simp)
      simp [hne]
    · simp [Bool.eq_false_iff.mpr hc]
  · simp [Bool.eq_false_iff.mpr ht]

theorem DescentGlueInv.write {c : DnsCache} {used : Array ByteArray} (used' : Array ByteArray)
    (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32) (touches : Array RRKey)
    (hinv : DescentGlueInv c used)
    (hmono : ∀ g ∈ used, g ∈ used')
    (hauthA : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) authRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 1 && rr.class == BitVec.ofNat 16 1) = true →
          ∃ g ∈ used', VeriDNS.Impl.DomainName.nameEqCI rr.name g = true)
    (haddA : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) addRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 1 && rr.class == BitVec.ofNat 16 1) = true →
          ∃ g ∈ used', VeriDNS.Impl.DomainName.nameEqCI rr.name g = true) :
    DescentGlueInv ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          c resp authRaws credA now)
        resp addRaws credD now).boundLru touches now) used' := by
  intro e he ht
  obtain ⟨e', he', hrr, _hcred⟩ := mem_boundLru_inv _ _ _ e he
  rw [hrr] at ht ⊢
  rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e' he' with h1 | ⟨b, hb, rr, hp, hpush⟩
  · rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e' h1 with h0 | ⟨b, hb, rr, hp, hpush⟩
    · obtain ⟨g, hg, hci⟩ := hinv e' h0 ht
      exact ⟨g, hmono g hg, hci⟩
    · subst hpush
      exact hauthA b hb rr hp ht
  · subst hpush
    exact haddA b hb rr hp ht


theorem referralWrite_reGlue_exact_warm
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32) (nsNames : Array ByteArray)
    (nsRaw glueRaw : ByteArray) (nsrr grr : VeriDNS.Spec.ResourceRecord)
    (htc : (resp.header.tc == 1) = false)
    (hAnone : ∀ n ∈ nsNames, ∀ e ∈ c.records,
        (VeriDNS.Impl.DomainName.nameEqCI e.rr.name n
          && e.rr.type == BitVec.ofNat 16 1 && e.rr.class == BitVec.ofNat 16 1) = false)
    (hauthN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) authRaws
        = #[nsRaw])
    (hpns : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsrr)
    (hnsType : nsrr.type = BitVec.ofNat 16 2)
    (haddN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws
        = #[glueRaw])
    (hpg : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) glueRaw = some grr) :
    ∀ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
          resp addRaws credD now) now nsNames →
      ga = glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr) := by
  intro gn ga hmem
  have hw : Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
      resp addRaws credD now
      = Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (c.storeChecked nsrr credA now)
          (VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws)
          credD now := by
    unfold Resolver.cacheUnlessTruncated
    simp only [htc, Bool.false_eq_true, if_false]
    rw [hauthN, cacheRRs_singleton, hpns]
  rw [hw] at hmem
  obtain ⟨hgn, rr, hrr, _hsz, hga⟩ := mem_reGlue_inv _ now nsNames gn ga hmem
  obtain ⟨e, he, hlv, hreq⟩ := mem_lookupTopCred_inv _ gn _ _ now rr hrr
  unfold liveEntry at hlv
  simp only [Bool.and_eq_true] at hlv
  obtain ⟨⟨⟨hnm, htp⟩, hcl⟩, _hfr⟩ := hlv
  rcases mem_cacheRRs_inv _ _ credD now e he with h1 | ⟨b, hb, rr', hp', hpush⟩
  · rcases mem_storeChecked_inv c nsrr credA now e h1 with hc | hpush
    ·
      have hkill := hAnone gn hgn e hc
      rw [hnm, htp, hcl] at hkill
      exact absurd hkill (by decide)
    ·
      exfalso
      have herr : e.rr = nsrr := by rw [hpush]
      rw [herr, hnsType] at htp
      exact absurd htp (by decide)
  ·
    rw [haddN, Array.mem_singleton] at hb
    subst hb
    rw [hpg] at hp'
    rw [Option.some.injEq] at hp'
    subst hp'
    have herr : e.rr = grr := by rw [hpush]
    rw [hga, hreq, herr]
    rfl



def SlistShape (s : DnsSList) (nsName : ByteArray) (ip : BitVec 32) (mc : Nat) : Prop :=
  (∀ e ∈ s.servers, e.name = nsName ∧ e.address = some ip)
  ∧ (∃ e, e ∈ s.servers)
  ∧ s.matchCount = mc

theorem SlistShape.bestWithAddress {s : DnsSList} {nsName : ByteArray} {ip : BitVec 32} {mc : Nat}
    (h : SlistShape s nsName ip mc) :
    ∃ entry, s.bestWithAddress = some (entry, ip) ∧ entry.name = nsName := by
  obtain ⟨hall, ⟨e0, he0⟩, _⟩ := h
  have hsome := bestWithAddress_isSome_of_mem s e0 ip he0 (hall e0 he0).2
  obtain ⟨⟨e', a'⟩, hbw⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hmem', ha'⟩ := bestWithAddress_mem s e' a' hbw
  obtain ⟨hn, ha⟩ := hall e' hmem'
  rw [ha, Option.some.injEq] at ha'
  refine ⟨e', ?_, hn⟩
  rw [hbw, ha']

theorem SlistShape.addressTargets_none {s : DnsSList} {nsName : ByteArray} {ip : BitVec 32}
    {mc : Nat} (h : SlistShape s nsName ip mc) :
    s.addressTargets[0]? = none := by
  obtain ⟨hall, _, _⟩ := h
  have hempty : s.addressTargets = #[] := by
    unfold DnsSList.addressTargets
    rw [Array.filterMap_eq_empty_iff]
    intro e he
    rw [(hall e he).2]
  rw [hempty]
  rfl

theorem SlistShape.markQueried {s : DnsSList} {nsName : ByteArray} {ip : BitVec 32} {mc : Nat}
    (h : SlistShape s nsName ip mc) (n : ByteArray) :
    SlistShape (s.markQueried n) nsName ip mc := by
  obtain ⟨hall, ⟨e0, he0⟩, hmc⟩ := h
  refine ⟨?_, ?_, hmc⟩
  · intro e he
    unfold DnsSList.markQueried at he
    replace he : e ∈ s.servers.map _ := he
    rw [Array.mem_map] at he
    obtain ⟨a, ha, hae⟩ := he
    obtain ⟨hn, haddr⟩ := hall a ha
    subst hae
    constructor
    · split <;> exact hn
    · split <;> exact haddr
  · exact ⟨_, Array.mem_map.mpr ⟨e0, he0, rfl⟩⟩

theorem SlistShape.of_fromNsWithGlueAll
    (nsNames : Array ByteArray) (G : Array (ByteArray × BitVec 32)) (mc : Nat)
    (nsName gn0 : ByteArray) (ip : BitVec 32)
    (hnames : ∀ n ∈ nsNames, n = nsName)
    (hmem : nsName ∈ nsNames)
    (hg : (gn0, ip) ∈ G)
    (hgm : (VeriDNS.Impl.DomainName.foldNameCase gn0
        == VeriDNS.Impl.DomainName.foldNameCase nsName) = true)
    (hval : ∀ gn ga, (gn, ga) ∈ G → ga = ip) :
    SlistShape (DnsSList.fromNsWithGlueAll nsNames G mc) nsName ip mc := by
  have hip : ip ∈ G.filterMap
      (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
        == VeriDNS.Impl.DomainName.foldNameCase nsName then some x.2 else none) := by
    rw [Array.mem_filterMap]
    exact ⟨(gn0, ip), hg, by simp only [hgm, if_true]⟩
  have hne : (G.filterMap
      (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
        == VeriDNS.Impl.DomainName.foldNameCase nsName then some x.2 else none)).isEmpty
      = false :=
    Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨ip, hip⟩
  refine ⟨?_, ?_, rfl⟩
  · intro e he
    unfold DnsSList.fromNsWithGlueAll at he
    simp only [Array.mem_flatMap] at he
    obtain ⟨n, hn, hemem⟩ := he
    have hneq := hnames n hn
    subst hneq
    rw [hne, if_neg (by simp)] at hemem
    obtain ⟨ga, hga, rfl⟩ := Array.mem_map.mp hemem
    refine ⟨rfl, ?_⟩
    rw [Array.mem_filterMap] at hga
    obtain ⟨⟨gn, gv⟩, hgmem, hgif⟩ := hga
    by_cases hc : (VeriDNS.Impl.DomainName.foldNameCase gn
        == VeriDNS.Impl.DomainName.foldNameCase n) = true
    · rw [if_pos hc] at hgif
      have hgv : gv = ga := by simpa using hgif
      show some ga = some ip
      rw [← hgv, hval gn gv hgmem]
    · rw [if_neg hc] at hgif
      exact absurd hgif (by simp)
  · refine ⟨(⟨nsName, some ip, 0⟩ : SlistEntry), ?_⟩
    show _ ∈ (DnsSList.fromNsWithGlueAll nsNames G mc).servers
    unfold DnsSList.fromNsWithGlueAll
    simp only [Array.mem_flatMap]
    refine ⟨nsName, hmem, ?_⟩
    split
    · rename_i hc
      rw [Array.isEmpty_iff] at hc
      rw [hc] at hip
      simp at hip
    · exact Array.mem_map.mpr ⟨ip, hip, rfl⟩

theorem delegationCloserB_of_matchCount (slist : DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hlt : slist.matchCount < Resolver.delegationMatchCount
        (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname) :
    Server.delegationCloserB slist sname resp = true := by
  unfold Server.delegationCloserB
  have hd : decide (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
      resp.authority sname
      > VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := SlistEntry) slist)
      = true := decide_eq_true hlt
  rw [hd, Bool.or_true]



private theorem extract_suffix_toList' (ls : Array ByteArray) (i : Nat) :
    (ls.extract i ls.size).toList = ls.toList.drop i := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  exact List.take_of_length_le (by simp)

private theorem goWire_size_drop_le (l : List ByteArray) : ∀ i : Nat,
    (VeriDNS.Impl.DomainName.labelsToWireFormatGo (l.drop i)).size
      ≤ (VeriDNS.Impl.DomainName.labelsToWireFormatGo l).size := by
  induction l with
  | nil => intro i; simp
  | cons x rest ih =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      have hsz : (VeriDNS.Impl.DomainName.labelsToWireFormatGo (x :: rest)).size
          = 1 + x.size + (VeriDNS.Impl.DomainName.labelsToWireFormatGo rest).size := by
        simp [VeriDNS.Impl.DomainName.labelsToWireFormatGo, ByteArray.size_append,
          ByteArray.size_push]
      have := ih i
      simp only [List.drop_succ_cons]
      omega

private theorem goWire_size_drop_lt (l : List ByteArray) (hv : ∀ x ∈ l, 0 < x.size) :
    ∀ i j : Nat, i < j → j ≤ l.length →
    (VeriDNS.Impl.DomainName.labelsToWireFormatGo (l.drop j)).size
      < (VeriDNS.Impl.DomainName.labelsToWireFormatGo (l.drop i)).size := by
  induction l with
  | nil =>
    intro i j hij hj
    simp at hj
    omega
  | cons x rest ih =>
    intro i j hij hj
    have hsz : (VeriDNS.Impl.DomainName.labelsToWireFormatGo (x :: rest)).size
        = 1 + x.size + (VeriDNS.Impl.DomainName.labelsToWireFormatGo rest).size := by
      simp [VeriDNS.Impl.DomainName.labelsToWireFormatGo, ByteArray.size_append,
        ByteArray.size_push]
    cases i with
    | zero =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.drop_succ_cons, List.drop_zero]
      have hle := goWire_size_drop_le rest j'
      have hx := hv x (by simp)
      omega
    | succ i =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.drop_succ_cons]
      exact ih (fun y hy => hv y (List.mem_cons_of_mem x hy)) i j' (by omega) (by simpa using hj)

theorem minimisedName_size_lt {m : ByteArray} (h : CanonicalName m) {j j' : Nat}
    (hjj : j < j') (hj' : j' ≤ VeriDNS.Impl.DomainName.labelCount m) :
    (VeriDNS.Impl.DomainName.minimisedName m j).size
      < (VeriDNS.Impl.DomainName.minimisedName m j').size := by
  obtain ⟨ls, hv, _hle, rfl⟩ := h
  rw [VeriDNS.Proof.QnameMin.labelCount_wire ls hv] at hj'
  rw [VeriDNS.Proof.QnameMin.minimisedName_wire ls hv,
    VeriDNS.Proof.QnameMin.minimisedName_wire ls hv]
  unfold VeriDNS.Impl.DomainName.labelsToWireFormat
  rw [extract_suffix_toList', extract_suffix_toList']
  have hvl : ∀ x ∈ ls.toList, 0 < x.size := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using hx)
    exact (hv i hi).1
  exact goWire_size_drop_lt ls.toList hvl (ls.size - j') (ls.size - j) (by omega) (by simp)

theorem parentDomainWire_minimisedName {m : ByteArray} (h : CanonicalName m) {j : Nat}
    (hj : j < VeriDNS.Impl.DomainName.labelCount m) :
    VeriDNS.Impl.DomainName.parentDomainWire (VeriDNS.Impl.DomainName.minimisedName m (j + 1))
      = some (VeriDNS.Impl.DomainName.minimisedName m j) := by
  obtain ⟨ls, hv, _hle, rfl⟩ := h
  rw [VeriDNS.Proof.QnameMin.labelCount_wire ls hv] at hj
  rw [VeriDNS.Proof.QnameMin.minimisedName_wire ls hv (j + 1),
    VeriDNS.Proof.QnameMin.minimisedName_wire ls hv j]
  have hne : (ls.extract (ls.size - (j + 1)) ls.size).size ≠ 0 := by
    rw [Array.size_extract]; omega
  rw [VeriDNS.Proof.Refinement.parentDomainWire_labelsToWireFormat
    (VeriDNS.Proof.QnameMin.validLabels_extract ls hv _ _) hne]
  rw [VeriDNS.Proof.Refinement.extract_extract_one]
  have harith : ls.size - (j + 1) + 1 = ls.size - j := by omega
  rw [harith]

theorem wireFormatToLabels_minimisedName {m : ByteArray} (h : CanonicalName m) {keep : Nat}
    (hk : keep ≤ VeriDNS.Impl.DomainName.labelCount m) :
    ∃ ls', VeriDNS.Impl.DomainName.wireFormatToLabels
        (VeriDNS.Impl.DomainName.minimisedName m keep) = .ok ls'
      ∧ ls'.size = keep := by
  obtain ⟨ls, hv, _hle, rfl⟩ := h
  rw [VeriDNS.Proof.QnameMin.labelCount_wire ls hv] at hk
  rw [VeriDNS.Proof.QnameMin.minimisedName_wire ls hv]
  refine ⟨ls.extract (ls.size - keep) ls.size, ?_, ?_⟩
  · exact VeriDNS.Proof.DomainName.wireFormat_roundtrip _
      (VeriDNS.Proof.QnameMin.validLabels_extract ls hv _ _)
  · rw [Array.size_extract]; omega

theorem lookupTopCred_isEmpty_of_keyless (c : DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32)
    (h : ∀ e ∈ c.records,
        (VeriDNS.Impl.DomainName.nameEqCI e.rr.name name
          && e.rr.type == qt && e.rr.class == qc) = false) :
    ((VeriDNS.Spec.CacheSpec.lookupTopCred c name qt qc now
      : Array VeriDNS.Spec.ResourceRecord)).isEmpty = true := by
  show (c.lookupTopCred name qt qc now).isEmpty = true
  have hempty : c.lookupTopCred name qt qc now = #[] := by
    rw [DnsCache.lookupTopCred, Array.filterMap_eq_empty_iff]
    intro e he
    have hlv : liveEntry e name qt qc now = false := by
      unfold liveEntry
      rw [h e he]
      exact Bool.false_and _
    simp [hlv]
  rw [hempty]
  rfl

theorem DescentCacheInv.write_pre {c : DnsCache} {bound : Nat} (bound' : Nat)
    (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32)
    (hinv : DescentCacheInv c bound)
    (hmono : bound ≤ bound')
    (hcredA : Resolver.credAdditional.toCode ≤ credA.toCode)
    (hcredD : Resolver.credAdditional.toCode ≤ credD.toCode)
    (hauthB : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) authRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 2) = true → rr.name.size < bound')
    (haddB : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) addRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 2) = true → rr.name.size < bound') :
    DescentCacheInv (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          c resp authRaws credA now)
        resp addRaws credD now) bound' := by
  intro e he
  rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e he with h1 | ⟨b, hb, rr, hp, hpush⟩
  · rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e h1 with h0 | ⟨b, hb, rr, hp, hpush⟩
    · have h := hinv e h0
      exact ⟨fun ht => Nat.lt_of_lt_of_le (h.1 ht) hmono, h.2⟩
    · subst hpush
      exact ⟨fun ht => hauthB b hb rr hp ht, hcredA⟩
  · subst hpush
    exact ⟨fun ht => haddB b hb rr hp ht, hcredD⟩

theorem walkNs_minimised_ascend (cache : DnsCache) (nsType inClass : BitVec 16) (now : UInt32)
    {m : ByteArray} (hcanon : CanonicalName m) (cutLen : Nat)
    (hcutle : cutLen ≤ VeriDNS.Impl.DomainName.labelCount m)
    (hne : ((VeriDNS.Spec.CacheSpec.lookupTopCred cache
        (VeriDNS.Impl.DomainName.minimisedName m cutLen) nsType inClass now
        : Array VeriDNS.Spec.ResourceRecord)).isEmpty = false)
    (hempty : ∀ jj, cutLen < jj → jj ≤ VeriDNS.Impl.DomainName.labelCount m →
        ((VeriDNS.Spec.CacheSpec.lookupTopCred cache
          (VeriDNS.Impl.DomainName.minimisedName m jj) nsType inClass now
          : Array VeriDNS.Spec.ResourceRecord)).isEmpty = true) :
    ∀ (j fuel : Nat), cutLen ≤ j → j ≤ VeriDNS.Impl.DomainName.labelCount m →
      j - cutLen < fuel →
      Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
          (VeriDNS.Impl.DomainName.minimisedName m j) cache nsType inClass now fuel
        = some (((VeriDNS.Spec.CacheSpec.lookupTopCred cache
              (VeriDNS.Impl.DomainName.minimisedName m cutLen) nsType inClass now
              : Array VeriDNS.Spec.ResourceRecord)).filterMap
            (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
                == nsType
              then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
              else none),
          cutLen) := by
  have key : ∀ (d j fuel : Nat), j - cutLen = d → cutLen ≤ j →
      j ≤ VeriDNS.Impl.DomainName.labelCount m → d < fuel →
      Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
          (VeriDNS.Impl.DomainName.minimisedName m j) cache nsType inClass now fuel
        = some (((VeriDNS.Spec.CacheSpec.lookupTopCred cache
              (VeriDNS.Impl.DomainName.minimisedName m cutLen) nsType inClass now
              : Array VeriDNS.Spec.ResourceRecord)).filterMap
            (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
                == nsType
              then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
              else none),
          cutLen) := by
    intro d
    induction d with
    | zero =>
      intro j fuel hd hle hub hf
      have hj : j = cutLen := by omega
      subst hj
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [VeriDNS.Proof.Refinement.walkNs_base _ cache nsType inClass now f hne]
      obtain ⟨ls', hok, hsz⟩ := wireFormatToLabels_minimisedName hcanon hub
      simp only [hok, hsz]
    | succ d ih =>
      intro j fuel hd hle hub hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [VeriDNS.Proof.Refinement.walkNs_step _ cache nsType inClass now f _
        (hempty (j' + 1) (by omega) hub)
        (parentDomainWire_minimisedName hcanon (by omega))]
      exact ih j' f (by omega) (by omega) (by omega) (by omega)
  intro j fuel hle hub hf
  exact key (j - cutLen) j fuel rfl hle hub hf

theorem referralWrite_walkNs_facts
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32) (sname : ByteArray)
    (nsRaw : ByteArray) (nsrr : VeriDNS.Spec.ResourceRecord) (cutLen bound : Nat)
    (hcanon : CanonicalName sname)
    (hcutle : cutLen ≤ VeriDNS.Impl.DomainName.labelCount sname)
    (h127 : VeriDNS.Impl.DomainName.labelCount sname ≤ 127)
    (htc : (resp.header.tc == 1) = false)
    (hcredA : Resolver.credAdditional.toCode ≤ credA.toCode)
    (hcredD : Resolver.credAdditional.toCode ≤ credD.toCode)
    (hauthN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) authRaws
        = #[nsRaw])
    (hpns : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsrr)
    (hnsName : VeriDNS.Impl.DomainName.nameEqCI nsrr.name
        (VeriDNS.Impl.DomainName.minimisedName sname cutLen) = true)
    (hnsType : nsrr.type = BitVec.ofNat 16 2)
    (hnsClass : nsrr.class = BitVec.ofNat 16 1)
    (hnz : (nsrr.ttl == 0) = false)
    (hfresh : now + nsrr.ttl.toNat.toUInt32 > now)
    (haddT : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) addRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 2) = false)
    (hinv : DescentCacheInv c bound)
    (hble : bound ≤ (VeriDNS.Impl.DomainName.minimisedName sname cutLen).size) :
    ∃ nsNames,
      Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) sname
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              c resp authRaws credA now)
            resp addRaws credD now)
          (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 128 = some (nsNames, cutLen)
      ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr ∈ nsNames
      ∧ ∀ n ∈ nsNames, n = VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr
      := by
  have hkey := referralWrite_nsKey_facts c resp authRaws addRaws credA credD now
    (VeriDNS.Impl.DomainName.minimisedName sname cutLen) nsRaw nsrr
    htc hauthN hpns hnsName hnsType hnsClass hnz hfresh haddT
    (hinv.nsKey_none _ hble)
  have hinv' : DescentCacheInv (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp authRaws credA now)
      resp addRaws credD now)
      ((VeriDNS.Impl.DomainName.minimisedName sname cutLen).size + 1) := by
    refine DescentCacheInv.write_pre _ resp authRaws addRaws credA credD now hinv
      (by omega) hcredA hcredD ?_ ?_
    · intro b hb rr hp ht
      rw [hauthN, Array.mem_singleton] at hb
      subst hb
      rw [hpns, Option.some.injEq] at hp
      subst hp
      have := nameEqCI_size hnsName
      omega
    · intro b hb rr hp ht
      have := haddT b hb rr hp
      rw [ht] at this
      exact absurd this (by decide)
  have hempty : ∀ jj, cutLen < jj → jj ≤ VeriDNS.Impl.DomainName.labelCount sname →
      ((VeriDNS.Spec.CacheSpec.lookupTopCred
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            c resp authRaws credA now)
          resp addRaws credD now)
        (VeriDNS.Impl.DomainName.minimisedName sname jj)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
        : Array VeriDNS.Spec.ResourceRecord)).isEmpty = true := by
    intro jj hjj hub
    refine lookupTopCred_isEmpty_of_keyless _ _ _ _ _ (hinv'.nsKey_none _ ?_)
    have := minimisedName_size_lt hcanon hjj hub
    omega
  have hasc := walkNs_minimised_ascend
    (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp authRaws credA now)
      resp addRaws credD now)
    (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now hcanon cutLen hcutle hkey.1 hempty
    (VeriDNS.Impl.DomainName.labelCount sname) 128 hcutle (Nat.le_refl _) (by omega)
  rw [VeriDNS.Proof.QnameMin.minimisedName_full (Nat.le_refl _)] at hasc
  exact ⟨_, hasc, hkey.2.1, hkey.2.2⟩



theorem minimisedName_size_le {m : ByteArray} (h : CanonicalName m) {j j' : Nat}
    (hjj : j ≤ j') (hj' : j' ≤ VeriDNS.Impl.DomainName.labelCount m) :
    (VeriDNS.Impl.DomainName.minimisedName m j).size
      ≤ (VeriDNS.Impl.DomainName.minimisedName m j').size := by
  rcases Nat.eq_or_lt_of_le hjj with rfl | hlt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (minimisedName_size_lt h hlt hj')

def hopRespond (cutSize : Nat) (nsAuth glue : Array ByteArray)
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (q : VeriDNS.Spec.Format) : VeriDNS.Spec.Format :=
  match q.question[0]? with
  | some qu =>
    if cutSize ≤ qu.qname.size then referralReply q nsAuth glue
    else treeRespond T negAuth q
  | none => treeRespond T negAuth q

theorem hopRespond_refer (cutSize : Nat) (nsAuth glue : Array ByteArray)
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hq : q.question[0]? = some qu) (hsize : cutSize ≤ qu.qname.size) :
    hopRespond cutSize nsAuth glue T negAuth q = referralReply q nsAuth glue := by
  unfold hopRespond
  simp only [hq]
  rw [if_pos hsize]

theorem hopRespond_tree (cutSize : Nat) (nsAuth glue : Array ByteArray)
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hq : q.question[0]? = some qu) (hsize : qu.qname.size < cutSize) :
    hopRespond cutSize nsAuth glue T negAuth q = treeRespond T negAuth q := by
  unfold hopRespond
  simp only [hq]
  rw [if_neg (by omega)]

theorem DescentCacheInv.noBetterGlue_after_auth_write {c : DnsCache} {bound : Nat}
    (hinv : DescentCacheInv c bound)
    (resp : VeriDNS.Spec.Format) (authRaws : Array ByteArray) (credA : Trustworthiness)
    (now : UInt32) (grr : VeriDNS.Spec.ResourceRecord)
    (hcredA : Resolver.credAdditional.toCode ≤ credA.toCode) :
    NoBetterGlue (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp authRaws credA now) grr Resolver.credAdditional now := by
  intro e2 he2 _hf _hnm _htp _hcl
  rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e2 he2 with h0 | ⟨b, hb, rr, hp, hpush⟩
  · exact (hinv e2 h0).2
  · subst hpush
    exact hcredA


structure SpineHop where
  nsAuth : Array ByteArray
  glue : Array ByteArray
  nsRaw : ByteArray
  glueRaw : ByteArray
  nsrr : VeriDNS.Spec.ResourceRecord
  grr : VeriDNS.Spec.ResourceRecord
  cutLen : Nat
  T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord

structure HopOk (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (negAuth : Array ByteArray) (sname : ByteArray) (now : UInt32)
    (used : Array ByteArray) (prevCut : Nat) (ip : BitVec 32) (hop : SpineHop) : Prop where
  resp_eq : ∀ q', respond (Server.ipv4ToAddr ip) q'
    = hopRespond (VeriDNS.Impl.DomainName.minimisedName sname hop.cutLen).size
        hop.nsAuth hop.glue hop.T negAuth q'
  plk : ∀ (seed : UInt16) (r : Nat), prevCut < r → r < hop.cutLen →
    VeriDNS.Impl.NameTree.treeLookup hop.T
      (DomainName.randomizeCase seed (DomainName.minimisedName sname r))
      (BitVec.ofNat 16 1) = .nodata
  cut_gt : prevCut < hop.cutLen
  cut_le : hop.cutLen ≤ VeriDNS.Impl.DomainName.labelCount sname
  ns_sz : hop.nsAuth.size < 65536
  glue_sz : hop.glue.size < 65536
  ns_canon : CanonicalSection hop.nsAuth
  glue_canon : CanonicalSection hop.glue
  glue_opt : ∀ b ∈ hop.glue, Edns.isOptRR b = false
  ns_cap : ∀ b ∈ hop.nsAuth, Server.capTtlRR b = b
  glue_cap : ∀ b ∈ hop.glue, Server.capTtlRR b = b
  has_ns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) hop.nsAuth 2 = true
  no_soa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) hop.nsAuth 6 = false
  dmc : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) hop.nsAuth sname
    = hop.cutLen
  bailiwick : ∀ q', Server.respInBailiwick sname (referralReply q' hop.nsAuth hop.glue) = true
  authN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
    (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) hop.nsAuth) hop.nsAuth)
    = #[hop.nsRaw]
  pns : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) hop.nsRaw
    = some hop.nsrr
  ns_name : VeriDNS.Impl.DomainName.nameEqCI hop.nsrr.name
    (VeriDNS.Impl.DomainName.minimisedName sname hop.cutLen) = true
  ns_type : hop.nsrr.type = BitVec.ofNat 16 2
  ns_class : hop.nsrr.class = BitVec.ofNat 16 1
  ns_nz : (hop.nsrr.ttl == 0) = false
  ns_fresh : now + hop.nsrr.ttl.toNat.toUInt32 > now
  addN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
    (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) hop.nsAuth) hop.glue)
    = #[hop.glueRaw]
  pg : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) hop.glueRaw
    = some hop.grr
  g_key : VeriDNS.Impl.DomainName.nameEqCI hop.grr.name
    (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.nsrr) = true
  g_type : hop.grr.type = BitVec.ofNat 16 1
  g_class : hop.grr.class = BitVec.ofNat 16 1
  g_nz : (hop.grr.ttl == 0) = false
  g_fresh : now + hop.grr.ttl.toNat.toUInt32 > now
  g_size : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr).size == 4)
    = true
  g_fresh_owner : ∀ g ∈ used, VeriDNS.Impl.DomainName.nameEqCI g
    (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.nsrr) = false
  next_egress : Server.blockedEgress
    (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr)) = false

structure LeafOk (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (negAuth : Array ByteArray) (sname : ByteArray)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord)
    (prevCut : Nat) (ip : BitVec 32) : Prop where
  resp_eq : ∀ q', respond (Server.ipv4ToAddr ip) q' = treeRespond leafT negAuth q'
  plk : ∀ (seed : UInt16) (r : Nat), prevCut < r → r < VeriDNS.Impl.DomainName.labelCount sname →
    VeriDNS.Impl.NameTree.treeLookup leafT
      (DomainName.randomizeCase seed (DomainName.minimisedName sname r))
      (BitVec.ofNat 16 1) = .nodata

def SpineOk (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (negAuth : Array ByteArray) (sname : ByteArray) (now : UInt32)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) :
    Nat → BitVec 32 → Array ByteArray → List SpineHop → Prop
  | prevCut, ip, _used, [] => LeafOk respond negAuth sname leafT prevCut ip
  | prevCut, ip, used, hop :: rest =>
    HopOk respond negAuth sname now used prevCut ip hop
    ∧ SpineOk respond negAuth sname now leafT hop.cutLen
        (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr))
        (used.push hop.grr.name) rest



theorem treeProbeRound_node
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hcoop : CooperativeNetworkAddr respond w)
    (hrespEq : respond (Server.ipv4ToAddr ipAddr)
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
      = treeRespond T negAuth
          (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hcanonS : CanonicalName state.resources.sname)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (hlkP : VeriDNS.Impl.NameTree.treeLookup T
        (DomainName.randomizeCase (w.ids (w.idCtr + 1))
          (DomainName.minimisedName state.resources.sname revealed))
        (BitVec.ofNat 16 1) = .nodata)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
        DescentChain sbelt deadline depth out
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } fuel'
          (Resolver.bumpRevealed state.resources.sname revealed) w') :
    DescentChain sbelt deadline depth out state (fuel' + 1) revealed w := by
  have hhdr := buildSubQuery_withSecrets_header state revealed subQuery₀
    (w.ids w.idCtr) (w.ids (w.idCtr + 1)) q hlq hbuild
  have hsects := buildSubQuery_withSecrets_sections state revealed subQuery₀
    (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild
  have htcS : ((Server.withSecrets subQuery₀ (w.ids w.idCtr)
      (w.ids (w.idCtr + 1))).header.tc == 1) = false := by
    rw [hhdr.1]; exact htcq
  have hsent := buildSubQuery_withSecrets_roundtrips_probe state revealed subQuery₀
    (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild hprobe hcanonS
  have hqSent := buildSubQuery_withSecrets_question_probe state revealed subQuery₀
    (w.ids w.idCtr) (w.ids (w.idCtr + 1)) q qu hlq hqu hbuild hprobe
  have hrcS : (Server.withSecrets subQuery₀ (w.ids w.idCtr)
      (w.ids (w.idCtr + 1))).header.rcode = VeriDNS.Spec.Rcode.noError := by
    rw [hhdr.2, hrcq]
  have hguards := treeRespond_nodata_probeConsumed T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (state.resources.slist.markQueried entry.name) state.resources.sname
    { qname := DomainName.randomizeCase (w.ids (w.idCtr + 1))
        (DomainName.minimisedName state.resources.sname revealed),
      qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
    hqSent hlkP hsects.1 hnoNs hrcS htcS
  have hndeq := treeRespond_nodata_eq T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    { qname := DomainName.randomizeCase (w.ids (w.idCtr + 1))
        (DomainName.minimisedName state.resources.sname revealed),
      qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
    hqSent hlkP
  have hadd := treeRespond_additional_empty T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) _ hqSent
  have hoptP : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).additional,
      Edns.isOptRR b = false := by
    rw [hadd.1]; intro b hb; simp at hb
  have harcP : (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).header.arcount
      = BitVec.ofNat 16 (treeRespond T negAuth
          (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).additional.size
      := by
    rw [hadd.1, hadd.2]; rfl
  have haP : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).answer,
      Server.capTtlRR b = b := by
    have hans : (treeRespond T negAuth
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).answer = #[] := by
      rw [hndeq]; exact hsects.1
    rw [hans]; intro b hb; simp at hb
  have hnP : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).authority,
      Server.capTtlRR b = b := by
    have hauth : (treeRespond T negAuth
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).authority
        = negAuth := by
      rw [hndeq]
    rw [hauth]; exact hnegCap
  have hdP : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))).additional,
      Server.capTtlRR b = b := by
    rw [hadd.1]; intro b hb; simp at hb
  have hsanEqP : Server.capTtls (Edns.stripOpt (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))))
      = treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr)
          (w.ids (w.idCtr + 1))) := by
    rw [Edns.stripOpt_eq_self _ hoptP harcP]
    exact capTtls_eq_self _ haP hnP hdP
  have hrtP := treeRespond_nodata_roundtrips T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    { qname := DomainName.randomizeCase (w.ids (w.idCtr + 1))
        (DomainName.minimisedName state.resources.sname revealed),
      qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
    hsent hqSent hlkP hnsz hcanNeg
  exact delegatingProbeConsumeRound_node respond sbelt state deadline depth fuel' revealed w
    entry ipAddr subQuery₀
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    { qname := DomainName.randomizeCase (w.ids (w.idCtr + 1))
        (DomainName.minimisedName state.resources.sname revealed),
      qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
    out hcoop rfl hrespEq hsent hdl hbest hegress hbuild hprobe hrtP
    (treeRespond_header_id T negAuth _) (treeRespond_question T negAuth _)
    hqSent hsanEqP hguards.1 hguards.2.1 hguards.2.2.1 hguards.2.2.2 hnext


theorem treeAnswerRound_delivers_pinned
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat)
    (entry : SlistEntry) (ipAddr : BitVec 32)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (I : Nat → UInt16) (C : UInt32) (ctr : Nat)
    (hdl : ¬ (C ≥ deadline))
    (hresp : ∀ q', respond (Server.ipv4ToAddr ipAddr) q' = treeRespond T negAuth q')
    (hsendq : state.currentStep = .sendQueries)
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hegress : Server.blockedEgress ipAddr = false)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcanonS : CanonicalName state.resources.sname)
    (hrev : DomainName.labelCount state.resources.sname ≤ revealed)
    (hchain : state.cnameChain = #[])
    (hlk : VeriDNS.Impl.NameTree.treeLookup T
        (DomainName.randomizeCase (I (ctr + 1)) state.resources.sname) qu.qtype
        = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      (∀ w : World, w.oracle = mkHonestOracleAddr respond →
          w.ids = I → w.clock = C → w.idCtr = ctr →
        Delivers sbelt state deadline depth (fuel' + 1) revealed w (.ok resp, cout))
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question := by
  have hbq : (Resolver.buildSubQuery state revealed).isSome = true := by
    simp only [Resolver.buildSubQuery, hlq, hqu, Option.isSome_some]
  obtain ⟨subQuery₀, hbuild⟩ := Option.isSome_iff_exists.mp hbq
  have hprobeF : Resolver.probeRoundB state.resources.sname revealed = false :=
    probeRoundB_false_of_fullReveal _ _ hrev
  have hhdr := buildSubQuery_withSecrets_header state revealed subQuery₀
    (I ctr) (I (ctr + 1)) q hlq hbuild
  have hsects := buildSubQuery_withSecrets_sections state revealed subQuery₀
    (I ctr) (I (ctr + 1)) hbuild
  have hsent := buildSubQuery_withSecrets_roundtrips state revealed subQuery₀
    (I ctr) (I (ctr + 1)) hbuild hprobeF hcanonS
  have hqSent := buildSubQuery_withSecrets_question state revealed subQuery₀
    (I ctr) (I (ctr + 1)) q qu hlq hqu hbuild hprobeF
  have htcS : ((Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.tc == 1) = false := by
    rw [hhdr.1]; exact htcq
  have hsfS : ((Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.rcode
      == VeriDNS.Spec.Rcode.serverFailure) = false := by
    rw [hhdr.2]; exact hqsf
  have hpos := (treeLookup_answer T _ qu.qtype rrs hlk).1
  have hmem : rrs[0] ∈ rrs := Array.getElem_mem hpos
  have hrtRR := parseRaw_rrBytes (hwfRR rrs[0] (Array.mem_def.mp hmem)).1
  obtain ⟨htcT, hunfT, hcnameT, hsfT, hclsT, hansT⟩ :=
    treeRespond_answer_classified T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
      (state.resources.slist.markQueried entry.name) state.resources.sname
      { qname := DomainName.randomizeCase (I (ctr + 1)) state.resources.sname,
        qtype := qu.qtype, qclass := qu.qclass } rrs rrs[0]
      hqSent hlk hmem hrtRR htcS hsfS
  have haeq := treeRespond_answer_eq T negAuth
    (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
    { qname := DomainName.randomizeCase (I (ctr + 1)) state.resources.sname,
      qtype := qu.qtype, qclass := qu.qclass } rrs hqSent hlk
  have hadd := treeRespond_additional_empty T negAuth
    (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) _ hqSent
  have hopt : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional,
      Edns.isOptRR b = false := by
    rw [hadd.1]; intro b hb; simp at hb
  have harc : (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).header.arcount
      = BitVec.ofNat 16 (treeRespond T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional.size := by
    rw [hadd.1, hadd.2]; rfl
  have ha : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).answer,
      Server.capTtlRR b = b := by
    have hans : (treeRespond T negAuth
        (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).answer
        = rrs.map VeriDNS.Spec.RRParse.rrBytes := by rw [haeq]
    rw [hans]; intro b hb
    rw [Array.mem_map] at hb; obtain ⟨rr, hrr, rfl⟩ := hb
    exact capTtlRR_rrBytes (hwfRR rr (Array.mem_def.mp hrr))
  have hn' : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).authority,
      Server.capTtlRR b = b := by
    have hauth : (treeRespond T negAuth
        (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).authority = #[] := by
      rw [haeq]; exact hsects.2
    rw [hauth]; intro b hb; simp at hb
  have hd : ∀ b ∈ (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional,
      Server.capTtlRR b = b := by
    rw [hadd.1]; intro b hb; simp at hb
  have hsanEq : Server.capTtls (Edns.stripOpt (treeRespond T negAuth
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))))
      = treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) := by
    rw [Edns.stripOpt_eq_self _ hopt harc]
    exact capTtls_eq_self _ ha hn' hd
  have hrt := treeRespond_answer_roundtrips T negAuth
    (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
    { qname := DomainName.randomizeCase (I (ctr + 1)) state.resources.sname,
      qtype := qu.qtype, qclass := qu.qclass } rrs hsent hqSent hlk hsz
    (fun rr h => (hwfRR rr h).1)
  refine ⟨_, _, fun w hwo hwids hwclk hwctr =>
    delegatingAnswerRound_delivers respond sbelt state deadline depth fuel' revealed w
      entry ipAddr subQuery₀
      (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
      (treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))))
      (treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))))
      { qname := DomainName.randomizeCase (I (ctr + 1)) state.resources.sname,
        qtype := qu.qtype, qclass := qu.qclass }
      hwo (by rw [hwids, hwctr]) (hresp _) hsent hsendq (by rw [hwclk]; exact hdl)
      hbest hglueless hegress hbuild hprobeF hrt
      (treeRespond_header_id T negAuth _) (treeRespond_question T negAuth _)
      hqSent hsanEq htcT hunfT hcnameT hsfT hclsT hansT, ?_, ?_⟩
  · rw [finalizeAnswer_answer, haeq]
    exact hchain
  · exact finalizeAnswer_question _ _ q hlq

theorem spineOk_cons_iff (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (negAuth : Array ByteArray) (sname : ByteArray) (now : UInt32)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord)
    (prevCut : Nat) (ip : BitVec 32) (used : Array ByteArray)
    (hop : SpineHop) (rest : List SpineHop) :
    SpineOk respond negAuth sname now leafT prevCut ip used (hop :: rest)
      ↔ HopOk respond negAuth sname now used prevCut ip hop
        ∧ SpineOk respond negAuth sname now leafT hop.cutLen
            (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr))
            (used.push hop.grr.name) rest := Iff.rfl

theorem spineOk_nil_iff (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (negAuth : Array ByteArray) (sname : ByteArray) (now : UInt32)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord)
    (prevCut : Nat) (ip : BitVec 32) (used : Array ByteArray) :
    SpineOk respond negAuth sname now leafT prevCut ip used []
      ↔ LeafOk respond negAuth sname leafT prevCut ip := Iff.rfl


set_option maxHeartbeats 1600000 in
theorem spineDelegation_chain
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sbelt : DnsSList) (deadline : UInt32) (depth : Nat)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (I : Nat → UInt16) (C nowS : UInt32)
    (hdl : ¬ (C ≥ deadline))
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcanon : CanonicalName qu.qname)
    (h127 : DomainName.labelCount qu.qname ≤ 127)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup leafT
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∀ (spine : List SpineHop) (revealed prevCut : Nat) (ip : BitVec 32)
      (used : Array ByteArray) (nsName : ByteArray) (fuel ctr : Nat)
      (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord),
      SpineOk respond negAuth qu.qname nowS leafT prevCut ip used spine →
      spine.length * 128 + (DomainName.labelCount qu.qname - revealed) < fuel →
      prevCut < revealed →
      state.currentStep = .sendQueries →
      state.resources.sname = qu.qname →
      state.now = nowS →
      state.lastQuery = some q →
      state.cnameChain = #[] →
      SlistShape state.resources.slist nsName ip prevCut →
      Server.blockedEgress ip = false →
      DescentCacheInv state.resources.cache
        ((DomainName.minimisedName qu.qname prevCut).size + 1) →
      DescentGlueInv state.resources.cache used →
      ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
        (∀ w : World, w.oracle = mkHonestOracleAddr respond →
            w.ids = I → w.clock = C → w.idCtr = ctr →
          DescentChain sbelt deadline depth (.ok resp, cout) state fuel revealed w)
        ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
        ∧ resp.question = q.question := by
  have key : ∀ (μ : Nat) (spine : List SpineHop) (revealed prevCut : Nat) (ip : BitVec 32)
      (used : Array ByteArray) (nsName : ByteArray) (fuel ctr : Nat)
      (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord),
      spine.length * 128 + (DomainName.labelCount qu.qname - revealed) = μ →
      SpineOk respond negAuth qu.qname nowS leafT prevCut ip used spine →
      spine.length * 128 + (DomainName.labelCount qu.qname - revealed) < fuel →
      prevCut < revealed →
      state.currentStep = .sendQueries →
      state.resources.sname = qu.qname →
      state.now = nowS →
      state.lastQuery = some q →
      state.cnameChain = #[] →
      SlistShape state.resources.slist nsName ip prevCut →
      Server.blockedEgress ip = false →
      DescentCacheInv state.resources.cache
        ((DomainName.minimisedName qu.qname prevCut).size + 1) →
      DescentGlueInv state.resources.cache used →
      ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
        (∀ w : World, w.oracle = mkHonestOracleAddr respond →
            w.ids = I → w.clock = C → w.idCtr = ctr →
          DescentChain sbelt deadline depth (.ok resp, cout) state fuel revealed w)
        ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
        ∧ resp.question = q.question := by
    intro μ
    induction μ using Nat.strongRecOn with
    | _ μ IH =>
    intro spine revealed prevCut ip used nsName fuel ctr state hμ hok hfuel hrev hstep hsn
      hnow hlq hchain hshape hegressC hcinv hginv
    have hcanS : CanonicalName state.resources.sname := by rw [hsn]; exact hcanon
    obtain ⟨entry, hbest, hename⟩ := SlistShape.bestWithAddress hshape
    have hglueless := SlistShape.addressTargets_none hshape
    have hbq : (Resolver.buildSubQuery state revealed).isSome = true := by
      simp only [Resolver.buildSubQuery, hlq, hqu, Option.isSome_some]
    obtain ⟨subQuery₀, hbuild⟩ := Option.isSome_iff_exists.mp hbq
    cases fuel with
    | zero => omega
    | succ fuel' =>
    cases spine with
    | nil =>
      have hleaf : LeafOk respond negAuth qu.qname leafT prevCut ip := hok
      by_cases hfull : DomainName.labelCount qu.qname ≤ revealed
      ·
        obtain ⟨resp, cout, hterm, hpinA, hpinQ⟩ := treeAnswerRound_delivers_pinned respond
          leafT negAuth sbelt state deadline depth fuel' revealed entry ip q qu rrs I C ctr
          hdl hleaf.resp_eq hstep hbest hglueless hegressC hlq hqu htcq hqsf hcanS
          (by rw [hsn]; exact hfull) hchain
          (by rw [hsn]; exact hflk (I (ctr + 1))) hsz hwfRR
        exact ⟨resp, cout, fun w hwo hwids hwclk hwctr =>
          DescentChain.terminal (hterm w hwo hwids hwclk hwctr), hpinA, hpinQ⟩
      ·
        rw [Nat.not_le] at hfull
        have hblt : DomainName.labelCount qu.qname
            - Resolver.bumpRevealed state.resources.sname revealed
            < DomainName.labelCount qu.qname - revealed := by
          rw [hsn]; exact bumpRevealed_metric_lt _ _ hfull
        have hbrev : prevCut < Resolver.bumpRevealed state.resources.sname revealed := by
          rw [hsn]; unfold Resolver.bumpRevealed; split <;> omega
        obtain ⟨resp, cout, htail, hpinA, hpinQ⟩ := IH
          (([] : List SpineHop).length * 128 + (DomainName.labelCount qu.qname
            - Resolver.bumpRevealed state.resources.sname revealed))
          (by simp only [List.length_nil]; omega)
          [] (Resolver.bumpRevealed state.resources.sname revealed) prevCut ip used nsName
          fuel' (ctr + 2)
          ({ state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } })
          rfl hok (by simp only [List.length_nil] at hμ ⊢; omega) hbrev hstep hsn hnow hlq
          hchain (hshape.markQueried entry.name) hegressC hcinv hginv
        refine ⟨resp, cout, fun w hwo hwids hwclk hwctr => ?_, hpinA, hpinQ⟩
        exact treeProbeRound_node respond leafT negAuth sbelt state deadline depth fuel'
          revealed w entry ip subQuery₀ q qu (.ok resp, cout) hwo
          (hleaf.resp_eq _) (by rw [hwclk]; exact hdl) hbest hegressC hbuild hlq hqu htcq
          hrcq hcanS
          (by rw [hsn]; exact probeRoundB_true_of_lt _ _ (by omega) hfull)
          (by rw [hsn]; exact hleaf.plk (w.ids (w.idCtr + 1)) revealed hrev hfull)
          hnoNs hnsz hcanNeg hnegCap
          (fun w' ho hto hids hclk hctr => htail w' (ho.trans hwo) (hids.trans hwids)
            (hclk.trans hwclk) (by rw [hctr, hwctr]))
    | cons hop rest =>
      obtain ⟨hhop, hrest⟩ :=
        (spineOk_cons_iff respond negAuth qu.qname nowS leafT prevCut ip used hop rest).mp hok
      by_cases hrefer : hop.cutLen ≤ revealed
      ·
        obtain ⟨qu', hq1, hqsize, hsent⟩ :
            ∃ qu', (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).question[0]? = some qu'
              ∧ (DomainName.minimisedName qu.qname hop.cutLen).size ≤ qu'.qname.size
              ∧ VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode
                    (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))))
                  = .ok (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) := by
          by_cases hfullR : DomainName.labelCount state.resources.sname ≤ revealed
          · have hprobeF := probeRoundB_false_of_fullReveal state.resources.sname revealed hfullR
            refine ⟨_, buildSubQuery_withSecrets_question state revealed subQuery₀
              (I ctr) (I (ctr + 1)) q qu hlq hqu hbuild hprobeF, ?_,
              buildSubQuery_withSecrets_roundtrips state revealed subQuery₀
                (I ctr) (I (ctr + 1)) hbuild hprobeF hcanS⟩
            show (DomainName.minimisedName qu.qname hop.cutLen).size
              ≤ (DomainName.randomizeCase (I (ctr + 1)) state.resources.sname).size
            rw [VeriDNS.Proof.NameTree.randomizeCase_size, hsn]
            calc (DomainName.minimisedName qu.qname hop.cutLen).size
                ≤ (DomainName.minimisedName qu.qname
                    (DomainName.labelCount qu.qname)).size :=
                  minimisedName_size_le hcanon hhop.cut_le (Nat.le_refl _)
              _ = qu.qname.size := by
                  rw [VeriDNS.Proof.QnameMin.minimisedName_full (Nat.le_refl _)]
          · rw [Nat.not_le] at hfullR
            have hprobeT : Resolver.probeRoundB state.resources.sname revealed = true :=
              probeRoundB_true_of_lt _ _ (by omega) hfullR
            refine ⟨_, buildSubQuery_withSecrets_question_probe state revealed subQuery₀
              (I ctr) (I (ctr + 1)) q qu hlq hqu hbuild hprobeT, ?_,
              buildSubQuery_withSecrets_roundtrips_probe state revealed subQuery₀
                (I ctr) (I (ctr + 1)) hbuild hprobeT hcanS⟩
            show (DomainName.minimisedName qu.qname hop.cutLen).size
              ≤ (DomainName.randomizeCase (I (ctr + 1))
                  (DomainName.minimisedName state.resources.sname revealed)).size
            rw [VeriDNS.Proof.NameTree.randomizeCase_size, hsn]
            rw [hsn] at hfullR
            exact minimisedName_size_le hcanon hrefer (by omega)
        have hrespR : respond (Server.ipv4ToAddr ip)
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            = referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue := by
          rw [hhop.resp_eq]
          exact hopRespond_refer _ _ _ _ _ _ _ hq1 hqsize
        have hrt := referralReply_roundtrips
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) hop.nsAuth hop.glue
          hsent hhop.ns_sz hhop.glue_sz hhop.ns_canon hhop.glue_canon
        have hhdr := buildSubQuery_withSecrets_header state revealed subQuery₀
          (I ctr) (I (ctr + 1)) q hlq hbuild
        have hansE : (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).answer = #[] := rfl
        have hauthE : (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).authority = hop.nsAuth := rfl
        have hrcR : (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
        have haaR : (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).header.aa = 0 := rfl
        have hnoerr : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.noError) = true := by
          decide
        have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by
          decide
        have hnne : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by
          decide
        have hclsR : Resolver.classifiableB (referralReply
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) hop.nsAuth hop.glue)
            = true := by
          simp only [Resolver.classifiableB, hrcR, hnoerr, Bool.or_true, Bool.true_or]
        have htcR : ((referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).header.tc == 1) = false := by
          show ((Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.tc == 1) = false
          rw [hhdr.1]; exact htcq
        have hauthN' : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).authority)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority) = #[hop.nsRaw] := hhop.authN
        have haddN' : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).authority)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).additional) = #[hop.glueRaw] := hhop.addN
        have haddT : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
            (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).authority)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).additional),
            ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
              (rr.type == BitVec.ofNat 16 2) = false := by
          intro b hb rr hpr
          rw [haddN', Array.mem_singleton] at hb
          subst hb
          rw [hhop.pg, Option.some.injEq] at hpr
          subst hpr
          rw [hhop.g_type]
          decide
        have hcredA : Resolver.credAdditional.toCode
            ≤ (Resolver.credAuthority ((referralReply
                (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).header.aa == 1)).toCode := Nat.le_refl _
        have hfreshNs' : state.now + hop.nsrr.ttl.toNat.toUInt32 > state.now := by
          rw [hnow]; exact hhop.ns_fresh
        have hfreshG' : state.now + hop.grr.ttl.toNat.toUInt32 > state.now := by
          rw [hnow]; exact hhop.g_fresh
        have hbleLt := minimisedName_size_lt hcanon hhop.cut_gt hhop.cut_le
        obtain ⟨nsNames, hwalkQ, hnsMemQ, hallQ⟩ := referralWrite_walkNs_facts
          state.resources.cache
          (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).additional)
          (Resolver.credAuthority ((referralReply
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).header.aa == 1))
          Resolver.credAdditional state.now qu.qname hop.nsRaw hop.nsrr hop.cutLen
          ((DomainName.minimisedName qu.qname prevCut).size + 1)
          hcanon hhop.cut_le h127 htcR hcredA (Nat.le_refl _) hauthN' hhop.pns hhop.ns_name
          hhop.ns_type hhop.ns_class hhop.ns_nz hfreshNs' haddT hcinv (by omega)
        have hwalkS : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.sname
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                state.resources.cache
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue)
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                    (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                      hop.nsAuth hop.glue).authority)
                  (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue).authority)
                (Resolver.credAuthority ((referralReply
                  (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).header.aa == 1)) state.now)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue)
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                  (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue).authority)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).additional)
              Resolver.credAdditional state.now)
            (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128
            = some (nsNames, hop.cutLen) := by
          rw [hsn]; exact hwalkQ
        have hneNs : (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority).isEmpty = false := by
          have h := VeriDNS.Proof.Refinement.extractNsNames_ne_of_hasRRTypeIn
            (RR := VeriDNS.Spec.ResourceRecord)
            ((referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority) hhop.has_ns
          simpa using h
        have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority state.resources.sname ≤ hop.cutLen := by
          rw [hsn]; exact Nat.le_of_eq hhop.dmc
        have hclose := VeriDNS.Proof.Refinement.currentCloser_false_of_ge
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority state.resources.sname)
          hop.cutLen hneNs hge
        have hnb0 := hcinv.noBetterGlue_after_auth_write
          (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority)
          (Resolver.credAuthority ((referralReply
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).header.aa == 1))
          state.now hop.grr hcredA
        have hexp : ∀ b' ∈ VeriDNS.Spec.RRParse.normalizeSection
            (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).authority)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).additional),
            ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
            DomainName.nameEqCI rr.name hop.grr.name = true → (rr.type == hop.grr.type) = true →
            (rr.class == hop.grr.class) = true →
            (state.now + rr.ttl.toNat.toUInt32 > state.now)
              ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4)
                  = true := by
          intro b' hb' rr hpr _ _ _
          rw [haddN', Array.mem_singleton] at hb'
          subst hb'
          rw [hhop.pg, Option.some.injEq] at hpr
          subst hpr
          exact ⟨hfreshG', hhop.g_size⟩
        have hbmem : hop.glueRaw ∈ VeriDNS.Spec.RRParse.normalizeSection
            (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).authority)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).additional) := by
          rw [haddN']
          exact Array.mem_singleton.mpr rfl
        obtain ⟨ga0, hgB⟩ := reGlue_preBoundLru_of_referral_glue
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).authority)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (Resolver.credAuthority ((referralReply
              (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).header.aa == 1)) state.now)
          (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).additional)
          Resolver.credAdditional state.now nsNames hop.grr hop.glueRaw
          (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.nsrr)
          hnsMemQ hhop.g_key htcR hbmem hhop.pg hhop.g_nz hhop.g_type hhop.g_class
          hfreshG' hhop.g_size hnb0 hexp
        have hAnone : ∀ n ∈ nsNames, ∀ e ∈ state.resources.cache.records,
            (VeriDNS.Impl.DomainName.nameEqCI e.rr.name n
              && e.rr.type == BitVec.ofNat 16 1 && e.rr.class == BitVec.ofNat 16 1) = false := by
          intro n hn e he
          rw [hallQ n hn]
          exact hginv.aNone _ hhop.g_fresh_owner e he
        have hvals := referralWrite_reGlue_exact_warm state.resources.cache
          (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).authority)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue).authority)
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue).additional)
          (Resolver.credAuthority ((referralReply
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            hop.nsAuth hop.glue).header.aa == 1))
          Resolver.credAdditional state.now nsNames hop.nsRaw hop.glueRaw hop.nsrr hop.grr
          htcR hAnone hauthN' hhop.pns hhop.ns_type haddN' hhop.pg
        have hga0 : ga0 = glueIpOf (VeriDNS.Spec.RRParse.rrRdata
            (RR := VeriDNS.Spec.ResourceRecord) hop.grr) := hvals _ _ hgB
        have hnbGate : ((VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                state.resources.cache
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue)
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                    (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                      hop.nsAuth hop.glue).authority)
                  (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue).authority)
                (Resolver.credAuthority ((referralReply
                  (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).header.aa == 1)) state.now)
              (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                hop.nsAuth hop.glue)
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                  (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue).authority)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue).additional)
              Resolver.credAdditional state.now)
            state.now nsNames).isEmpty && (hop.cutLen == 0)) = false := by
          rw [Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨_, hgB⟩]
          rfl
        obtain ⟨st, hcont, hslEq, hsnP, hnowP, hccP, hcsP, hlqP⟩ :=
          VeriDNS.Proof.Refinement.afterResume_referral_continue_slist
            ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
            entry.name
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue)
            nsNames hop.cutLen hstep
            (cnameToChase_of_emptyAnswer _ hansE)
            (by rw [hrcR, hclsR]; simp only [hnsf, Bool.not_true, Bool.or_false])
            (answersQueryB_of_emptyAnswer _ hansE)
            (by rw [hrcR]; exact hnne)
            (by rw [hansE]; rfl)
            (by rw [hauthE]; exact hasRRTypeIn_nonempty hop.nsAuth 2 hhop.has_ns)
            (by rw [hauthE]; exact hhop.has_ns)
            (by rw [haaR]; rfl)
            (by rw [hrcR]; exact hnoerr)
            (by rw [hauthE]; exact hhop.no_soa)
            hwalkS hclose hnbGate
        obtain ⟨st₂, hcont₂, hcacheEq, _, _, _, _⟩ :=
          VeriDNS.Proof.Refinement.afterResume_referral_continue_struct
            ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
            entry.name
            (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
              hop.nsAuth hop.glue)
            hstep
            (cnameToChase_of_emptyAnswer _ hansE)
            (by rw [hrcR, hclsR]; simp only [hnsf, Bool.not_true, Bool.or_false])
            (answersQueryB_of_emptyAnswer _ hansE)
            (by rw [hrcR]; exact hnne)
            (by rw [hansE]; rfl)
            (by rw [hauthE]; exact hasRRTypeIn_nonempty hop.nsAuth 2 hhop.has_ns)
            (by rw [hauthE]; exact hhop.has_ns)
            (by rw [haaR]; rfl)
            (by rw [hrcR]; exact hnoerr)
            (by rw [hauthE]; exact hhop.no_soa)
        have hst₂ : st = st₂ := by
          have h := hcont.symm.trans hcont₂
          injection h
        subst hst₂
        have hgB' : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.nsrr),
            glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr))
            ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                  state.resources.cache
                  (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue)
                  (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                    (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                      (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                        hop.nsAuth hop.glue).authority)
                    (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                      hop.nsAuth hop.glue).authority)
                  (Resolver.credAuthority ((referralReply
                    (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue).header.aa == 1)) state.now)
                (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                  hop.nsAuth hop.glue)
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                    (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                      hop.nsAuth hop.glue).authority)
                  (referralReply (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
                    hop.nsAuth hop.glue).additional)
                Resolver.credAdditional state.now)
              state.now nsNames := by
          rw [← hga0]
          exact hgB
        have hshape' : SlistShape st.resources.slist
            (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.nsrr)
            (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr))
            hop.cutLen := by
          rw [hslEq]
          exact SlistShape.of_fromNsWithGlueAll nsNames _ hop.cutLen _ _ _
            hallQ hnsMemQ hgB' (VeriDNS.Impl.Cache.byteArray_beq_refl _)
            (fun gn ga hm => hvals gn ga hm)
        have hcinv' : DescentCacheInv st.resources.cache
            ((DomainName.minimisedName qu.qname hop.cutLen).size + 1) := by
          rw [hcacheEq]
          refine DescentCacheInv.write _ _ _ _ _ _ _ _ hcinv (by omega) hcredA (Nat.le_refl _)
            ?_ ?_
          · intro b hb rr hp ht
            rw [hauthN', Array.mem_singleton] at hb
            subst hb
            rw [hhop.pns, Option.some.injEq] at hp
            subst hp
            have := nameEqCI_size hhop.ns_name
            omega
          · intro b hb rr hp ht
            have := haddT b hb rr hp
            rw [ht] at this
            exact absurd this (by decide)
        have hginv' : DescentGlueInv st.resources.cache (used.push hop.grr.name) := by
          rw [hcacheEq]
          refine DescentGlueInv.write _ _ _ _ _ _ _ _ hginv
            (fun g hg => Array.mem_push.mpr (Or.inl hg)) ?_ ?_
          · intro b hb rr hp ht
            rw [hauthN', Array.mem_singleton] at hb
            subst hb
            rw [hhop.pns, Option.some.injEq] at hp
            subst hp
            rw [hhop.ns_type,
              show ((BitVec.ofNat 16 2 : BitVec 16) == BitVec.ofNat 16 1) = false from by decide,
              Bool.false_and] at ht
            exact absurd ht (by decide)
          · intro b hb rr hp _
            rw [haddN', Array.mem_singleton] at hb
            subst hb
            rw [hhop.pg, Option.some.injEq] at hp
            subst hp
            refine ⟨hop.grr.name, Array.mem_push.mpr (Or.inr rfl), ?_⟩
            unfold VeriDNS.Impl.DomainName.nameEqCI
            exact VeriDNS.Impl.Cache.byteArray_beq_refl _
        have hsnSt : st.resources.sname = state.resources.sname := hsnP
        have hseed : Server.seedRevealed st = hop.cutLen + 1 := by
          show VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := SlistEntry)
            st.resources.slist + 1 = hop.cutLen + 1
          show st.resources.slist.matchCount + 1 = hop.cutLen + 1
          rw [hshape'.2.2]
        have hrevEq : Server.revealedAfterContinue state.resources.sname revealed st
            = max revealed (hop.cutLen + 1) := by
          unfold Server.revealedAfterContinue
          rw [hsnSt, VeriDNS.Impl.Cache.byteArray_beq_refl, hseed]
          simp
        have hrev' : hop.cutLen
            < Server.revealedAfterContinue state.resources.sname revealed st := by
          rw [hrevEq]; omega
        have hμcons : (hop :: rest).length * 128
            + (DomainName.labelCount qu.qname - revealed) = μ := hμ
        simp only [List.length_cons] at hμcons
        have hfuel' : rest.length * 128 + (DomainName.labelCount qu.qname
            - Server.revealedAfterContinue state.resources.sname revealed st) < fuel' := by
          rw [hrevEq]; omega
        obtain ⟨resp, cout, htail, hpinA, hpinQ⟩ := IH
          (rest.length * 128 + (DomainName.labelCount qu.qname
            - Server.revealedAfterContinue state.resources.sname revealed st))
          (by rw [hrevEq]; omega)
          rest (Server.revealedAfterContinue state.resources.sname revealed st) hop.cutLen
          (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.grr))
          (used.push hop.grr.name)
          (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) hop.nsrr)
          fuel' (ctr + 2) st rfl hrest hfuel' hrev' hcsP (hsnSt.trans hsn) (hnowP.trans hnow)
          (hlqP.trans hlq) (hccP.trans hchain) hshape' hhop.next_egress hcinv' hginv'
        refine ⟨resp, cout, fun w hwo hwids hwclk hwctr => ?_, hpinA, hpinQ⟩
        refine delegatingReferralRound_node respond sbelt state deadline depth fuel' revealed w
          entry ip subQuery₀ (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
          hop.nsAuth hop.glue qu' (.ok resp, cout)
          hwo (by rw [hwids, hwctr]) hrespR hsent hstep (by rw [hwclk]; exact hdl) hbest
          hegressC hbuild hrt hhop.glue_opt hhop.ns_cap hhop.glue_cap hq1 hhop.has_ns
          hhop.no_soa htcR
          (delegationCloserB_of_matchCount _ _ _ (by
            rw [markQueried_matchCount, hshape.2.2, hsn]
            show prevCut < Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
              hop.nsAuth qu.qname
            rw [hhop.dmc]
            exact hhop.cut_gt))
          (by rw [hsn]; exact hhop.bailiwick _) ?_
        intro st' hcont' w' ho hto hids hclk hctr
        have hst : st = st' := by
          have h := hcont.symm.trans hcont'
          injection h
        subst hst
        exact htail w' (ho.trans hwo) (hids.trans hwids) (hclk.trans hwclk)
          (by rw [hctr, hwctr])
      ·
        rw [Nat.not_le] at hrefer
        have hlcS : revealed < DomainName.labelCount qu.qname := by
          have := hhop.cut_le
          omega
        have hblt : DomainName.labelCount qu.qname
            - Resolver.bumpRevealed state.resources.sname revealed
            < DomainName.labelCount qu.qname - revealed := by
          rw [hsn]
          exact bumpRevealed_metric_lt _ _ (by omega)
        have hbrev : prevCut < Resolver.bumpRevealed state.resources.sname revealed := by
          rw [hsn]; unfold Resolver.bumpRevealed; split <;> omega
        obtain ⟨resp, cout, htail, hpinA, hpinQ⟩ := IH
          ((hop :: rest).length * 128 + (DomainName.labelCount qu.qname
            - Resolver.bumpRevealed state.resources.sname revealed))
          (by omega)
          (hop :: rest) (Resolver.bumpRevealed state.resources.sname revealed) prevCut ip used
          nsName fuel' (ctr + 2)
          ({ state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } })
          rfl hok (by omega) hbrev hstep hsn hnow hlq hchain
          (hshape.markQueried entry.name) hegressC hcinv hginv
        refine ⟨resp, cout, fun w hwo hwids hwclk hwctr => ?_, hpinA, hpinQ⟩
        have hprobeT : Resolver.probeRoundB state.resources.sname revealed = true := by
          rw [hsn]; exact probeRoundB_true_of_lt _ _ (by omega) (by omega)
        have hqSentW := buildSubQuery_withSecrets_question_probe state revealed subQuery₀
          (w.ids w.idCtr) (w.ids (w.idCtr + 1)) q qu hlq hqu hbuild hprobeT
        refine treeProbeRound_node respond hop.T negAuth sbelt state deadline depth fuel'
          revealed w entry ip subQuery₀ q qu (.ok resp, cout) hwo
          ?_ (by rw [hwclk]; exact hdl) hbest hegressC hbuild hlq hqu htcq hrcq hcanS hprobeT
          (by rw [hsn]; exact hhop.plk (w.ids (w.idCtr + 1)) revealed hrev hrefer)
          hnoNs hnsz hcanNeg hnegCap
          (fun w' ho hto hids hclk hctr => htail w' (ho.trans hwo) (hids.trans hwids)
            (hclk.trans hwclk) (by rw [hctr, hwctr]))
        rw [hhop.resp_eq]
        refine hopRespond_tree _ _ _ _ _ _ _ hqSentW ?_
        show (DomainName.randomizeCase (w.ids (w.idCtr + 1))
            (DomainName.minimisedName state.resources.sname revealed)).size
          < (DomainName.minimisedName qu.qname hop.cutLen).size
        rw [VeriDNS.Proof.NameTree.randomizeCase_size, hsn]
        exact minimisedName_size_lt hcanon hrefer hhop.cut_le
  intro spine revealed prevCut ip used nsName fuel ctr state hok hfuel hrev hstep hsn hnow hlq
    hchain hshape hegressC hcinv hginv
  exact key (spine.length * 128 + (DomainName.labelCount qu.qname - revealed)) spine revealed
    prevCut ip used nsName fuel ctr state rfl hok hfuel hrev hstep hsn hnow hlq hchain hshape
    hegressC hcinv hginv


theorem resolveWithIO_spine_adequate_warm
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (spine : List SpineHop) (prevCut : Nat) (ip : BitVec 32) (nsName : ByteArray)
    (used₀ : Array ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetworkAddr respond w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hdl : ¬ (w.clock ≥ now + budget))
    (hok : SpineOk respond negAuth qu.qname state.now leafT prevCut ip used₀ spine)
    (hfuel : spine.length * 128
        + (DomainName.labelCount qu.qname - Server.seedRevealed state) < fuel)
    (hstep : state.currentStep = .sendQueries)
    (hsn : state.resources.sname = qu.qname)
    (hlq : state.lastQuery = some q)
    (hchain0 : state.cnameChain = #[])
    (hshape : SlistShape state.resources.slist nsName ip prevCut)
    (hegress : Server.blockedEgress ip = false)
    (hcinv : DescentCacheInv state.resources.cache
        ((DomainName.minimisedName qu.qname prevCut).size + 1))
    (hginv : DescentGlueInv state.resources.cache used₀)
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcanon : CanonicalName qu.qname)
    (h127 : DomainName.labelCount qu.qname ≤ 127)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup leafT
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∃ (K : Nat) (w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w = some ((.ok resp, cout), w')
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question := by
  have hrevS : prevCut < Server.seedRevealed state := by
    show prevCut < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := SlistEntry)
      state.resources.slist + 1
    show prevCut < state.resources.slist.matchCount + 1
    rw [hshape.2.2]
    omega
  obtain ⟨resp, cout, hch, hpinA, hpinQ⟩ := spineDelegation_chain respond leafT negAuth sbelt
    (now + budget) depth q qu rrs w.ids w.clock state.now hdl hqu htcq hrcq hqsf hcanon h127
    hnoNs hnsz hcanNeg hnegCap hflk hsz hwfRR
    spine (Server.seedRevealed state) prevCut ip used₀ nsName fuel w.idCtr state
    hok hfuel hrevS hstep hsn rfl hlq hchain0 hshape hegress hcinv hginv
  obtain ⟨K, w', hrun⟩ := resolveWithIO_adequate_of_chain query sbelt cache now fuel depth
    budget w state (.ok resp, cout) hpause (hch w hcoop rfl rfl rfl)
  exact ⟨K, w', resp, cout, hrun, hpinA, hpinQ⟩

theorem resolveWithIO_spine_adequate
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (spine : List SpineHop) (prevCut : Nat) (ip : BitVec 32) (nsName : ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetworkAddr respond w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hdl : ¬ (w.clock ≥ now + budget))
    (hok : SpineOk respond negAuth qu.qname state.now leafT prevCut ip #[] spine)
    (hfuel : spine.length * 128
        + (DomainName.labelCount qu.qname - Server.seedRevealed state) < fuel)
    (hstep : state.currentStep = .sendQueries)
    (hsn : state.resources.sname = qu.qname)
    (hlq : state.lastQuery = some q)
    (hchain0 : state.cnameChain = #[])
    (hshape : SlistShape state.resources.slist nsName ip prevCut)
    (hegress : Server.blockedEgress ip = false)
    (hcold : state.resources.cache.records = #[])
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcanon : CanonicalName qu.qname)
    (h127 : DomainName.labelCount qu.qname ≤ 127)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup leafT
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∃ (K : Nat) (w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w = some ((.ok resp, cout), w')
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question :=
  resolveWithIO_spine_adequate_warm respond leafT negAuth query sbelt cache now fuel depth
    budget w state spine prevCut ip nsName #[] q qu rrs hcoop hpause hdl hok hfuel hstep hsn
    hlq hchain0 hshape hegress (DescentCacheInv.of_empty hcold _)
    (DescentGlueInv.of_empty hcold _) hqu htcq hrcq hqsf hcanon h127 hnoNs hnsz hcanNeg
    hnegCap hflk hsz hwfRR



def spineFuelBound (spine : List SpineHop) : Nat := spine.length * 128 + 128

theorem resolveWithIO_within_bound
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (spine : List SpineHop) (prevCut : Nat) (ip : BitVec 32) (nsName : ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetworkAddr respond w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hdl : ¬ (w.clock ≥ now + budget))
    (hok : SpineOk respond negAuth qu.qname state.now leafT prevCut ip #[] spine)
    (hfb : spineFuelBound spine ≤ fuel)
    (hstep : state.currentStep = .sendQueries)
    (hsn : state.resources.sname = qu.qname)
    (hlq : state.lastQuery = some q)
    (hchain0 : state.cnameChain = #[])
    (hshape : SlistShape state.resources.slist nsName ip prevCut)
    (hegress : Server.blockedEgress ip = false)
    (hcold : state.resources.cache.records = #[])
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcanon : CanonicalName qu.qname)
    (h127 : DomainName.labelCount qu.qname ≤ 127)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup leafT
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∃ (K : Nat) (w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w = some ((.ok resp, cout), w')
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question := by
  refine resolveWithIO_spine_adequate respond leafT negAuth query sbelt cache now fuel depth
    budget w state spine prevCut ip nsName q qu rrs hcoop hpause hdl hok ?_ hstep hsn hlq
    hchain0 hshape hegress hcold hqu htcq hrcq hqsf hcanon h127 hnoNs hnsz hcanNeg hnegCap
    hflk hsz hwfRR
  have hfb' : spine.length * 128 + 128 ≤ fuel := hfb
  omega

theorem resolveWithIO_spine_no_starvation
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (leafT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (spine : List SpineHop) (prevCut : Nat) (ip : BitVec 32) (nsName : ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetworkAddr respond w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hdl : ¬ (w.clock ≥ now + budget))
    (hok : SpineOk respond negAuth qu.qname state.now leafT prevCut ip #[] spine)
    (hfb : spineFuelBound spine ≤ fuel)
    (hstep : state.currentStep = .sendQueries)
    (hsn : state.resources.sname = qu.qname)
    (hlq : state.lastQuery = some q)
    (hchain0 : state.cnameChain = #[])
    (hshape : SlistShape state.resources.slist nsName ip prevCut)
    (hegress : Server.blockedEgress ip = false)
    (hcold : state.resources.cache.records = #[])
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcanon : CanonicalName qu.qname)
    (h127 : DomainName.labelCount qu.qname ≤ 127)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup leafT
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∀ (K : Nat) (out : Except String VeriDNS.Spec.Format × DnsCache) (wK : World),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w = some (out, wK) →
      ∃ (resp : VeriDNS.Spec.Format),
        out.1 = .ok resp
        ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
        ∧ resp.question = q.question := by
  intro K out wK hrun
  obtain ⟨K', w', resp, cout, hrun', hpinA, hpinQ⟩ := resolveWithIO_within_bound respond leafT
    negAuth query sbelt cache now fuel depth budget w state spine prevCut ip nsName q qu rrs
    hcoop hpause hdl hok hfb hstep hsn hlq hchain0 hshape hegress hcold hqu htcq hrcq hqsf
    hcanon h127 hnoNs hnsz hcanNeg hnegCap hflk hsz hwfRR
  have hout : out = (.ok resp, cout) := congrArg Prod.fst (run_agree hrun hrun')
  exact ⟨resp, by rw [hout], hpinA, hpinQ⟩

end VeriDNS.Proof.Adequacy
