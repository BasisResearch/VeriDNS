import VeriDNS.Proof.Refinement
import VeriDNS.Proof.AnswerTerminal
import VeriDNS.Proof.AnswerScrub
import VeriDNS.Proof.DeliveredWire
import VeriDNS.Spec.AnswerAuthenticity



namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (RRParse ResourceRecord)
open VeriDNS.Spec.Net (Name RData nameEq nameEq_symm CnameReachable scrubAnswer)
open VeriDNS.Impl.DomainName (nameEqCI)
open VeriDNS.Impl.Resolver (CnameReachableB scrubAnswerB scrubAnswerB_authentic)

def AllAbstract (answer : Array ByteArray) : Prop :=
  ∀ b ∈ answer, ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr → ∃ r, αRR rr = some r

theorem αRR_cname {rr : ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hαr : αRR rr = some r) (hty : (rr.type == (5 : BitVec 16)) = true) :
    ∃ mt, αName rr.rdata = some mt ∧ r.rdata = RData.cname mt := by
  have he : rr.type = (5 : BitVec 16) := by
    have h := hty; simp only [beq_iff_eq] at h; exact h
  have h5 : rr.type.toNat = 5 := by rw [he]; decide
  unfold αRR at hαr
  split at hαr
  · rename_i owner rdata cls hn hrd hcl
    obtain rfl := Option.some.inj hαr
    unfold αRData at hrd
    rw [h5] at hrd
    change Option.map RData.cname (αName rr.rdata) = some rdata at hrd
    rw [Option.map_eq_some_iff] at hrd
    obtain ⟨mt, hmt, hcn⟩ := hrd
    exact ⟨mt, hmt, hcn.symm⟩
  · exact absurd hαr (by simp)

theorem αName_reachableB {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hab : AllAbstract answer) (hq : αName qname = some mqname) :
    ∀ {w : ByteArray}, CnameReachableB (RR := ResourceRecord) qname answer w →
      ∃ mw, αName w = some mw := by
  intro w hcr
  induction hcr with
  | root => exact ⟨mqname, hq⟩
  | step bytes hmem rr hpr hty n hn _hmatch _ih =>
    obtain ⟨r', hr'⟩ := hab bytes hmem rr hpr
    obtain ⟨mt, hmt, _⟩ := αRR_cname hr' hty
    exact ⟨mt, hmt⟩

theorem cnameReachableB_to_model {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hab : AllAbstract answer) (hq : αName qname = some mqname) :
    ∀ {w : ByteArray}, CnameReachableB (RR := ResourceRecord) qname answer w →
      ∀ mw, αName w = some mw → CnameReachable mqname (αSection answer) mw := by
  intro w hcr
  induction hcr with
  | root =>
    intro mw hmw
    rw [hq] at hmw; obtain rfl := Option.some.inj hmw
    exact CnameReachable.root
  | step bytes hmem rr hpr hty n hn hmatch ih =>
    intro mw hmw
    obtain ⟨r', hr'⟩ := hab bytes hmem rr hpr
    obtain ⟨mt, hmt, hrd⟩ := αRR_cname hr' hty
    obtain rfl : mt = mw := Option.some.inj (hmt.symm.trans hmw)
    have hr'mem : r' ∈ αSection answer := αSection_mem (Array.mem_def.mp hmem) hpr hr'
    have hown : αName rr.name = some r'.owner := (αRR_fields rr r' hr').1
    have hmatchCI : nameEqCI n rr.name = true := VeriDNS.Proof.NameTree.nameEqCI_symm hmatch
    obtain ⟨mn, hmn, hnt⟩ := αName_of_nameEqCI hmatchCI hown
    refine CnameReachable.step r' hr'mem mt hrd mn (ih mn hmn) ?_
    rw [nameEq_symm]; exact hnt



def AllParse (answer : Array ByteArray) : Prop :=
  ∀ b ∈ answer, ∃ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr

theorem allParse_of_canonicalSection {answer : Array ByteArray}
    (h : VeriDNS.Proof.DeliveredWire.CanonicalSection answer) : AllParse answer := by
  intro b hb
  obtain ⟨ls, t, c, ttl, rdata, -, -, -, -, hpr⟩ :=
    VeriDNS.Proof.DeliveredWire.canonicalRR_parse (h b hb)
  exact ⟨_, hpr⟩

theorem αType_cname_five {qt : BitVec 16} (h : αType qt = some VeriDNS.Spec.RRType.cname) :
    qt = (5 : BitVec 16) := by
  have h5 : qt.toNat = 5 := by
    unfold αType at h
    split at h <;> simp_all
  exact BitVec.eq_of_toNat_eq (by simpa using h5)

theorem αSection_mem_inv {rrs : Array ByteArray} {r : VeriDNS.Spec.Net.RR}
    (h : r ∈ αSection rrs) :
    ∃ b ∈ rrs, ∃ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧ αRR rr = some r := by
  unfold αSection at h
  rw [List.mem_filterMap] at h
  obtain ⟨b, hb, hmatch⟩ := h
  refine ⟨b, Array.mem_def.mpr hb, ?_⟩
  cases hpr : RRParse.parseRaw (RR := ResourceRecord) b with
  | none => rw [hpr] at hmatch; simp at hmatch
  | some rr => rw [hpr] at hmatch; exact ⟨rr, rfl, hmatch⟩

def NameCorr (w : ByteArray) (n : Name) : Prop :=
  αName w = some n
  ∧ w = VeriDNS.Impl.DomainName.labelsToWireFormatGo n
  ∧ (∀ x ∈ n, 0 < x.size ∧ x.size ≤ 63)
  ∧ w.size ≤ 255

inductive NamesCorr : List ByteArray → List Name → Prop where
  | nil : NamesCorr [] []
  | cons {w : ByteArray} {n : Name} {ws : List ByteArray} {ns : List Name}
      (hw : NameCorr w n) (ht : NamesCorr ws ns) : NamesCorr (w :: ws) (n :: ns)

theorem NamesCorr.append {a c : List ByteArray} {b d : List Name}
    (h1 : NamesCorr a b) (h2 : NamesCorr c d) : NamesCorr (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons hw _ ih => exact .cons hw ih

theorem NamesCorr.mem_left {ws : List ByteArray} {ns : List Name}
    (h : NamesCorr ws ns) {w : ByteArray} (hw : w ∈ ws) : ∃ n ∈ ns, NameCorr w n := by
  induction h with
  | nil => cases hw
  | cons hc _ ih =>
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact ⟨_, List.mem_cons_self .., hc⟩
    · obtain ⟨n, hn, hcn⟩ := ih hw'
      exact ⟨n, List.mem_cons_of_mem _ hn, hcn⟩

theorem NamesCorr.mem_right {ws : List ByteArray} {ns : List Name}
    (h : NamesCorr ws ns) {n : Name} (hn : n ∈ ns) : ∃ w ∈ ws, NameCorr w n := by
  induction h with
  | nil => cases hn
  | cons hc _ ih =>
    rcases List.mem_cons.mp hn with rfl | hn'
    · exact ⟨_, List.mem_cons_self .., hc⟩
    · obtain ⟨w, hw, hcw⟩ := ih hn'
      exact ⟨w, List.mem_cons_of_mem _ hw, hcw⟩

theorem NamesCorr.find?_corr {ws : List ByteArray} {ns : List Name} (h : NamesCorr ws ns)
    {pB : ByteArray → Bool} {pM : Name → Bool}
    (hpt : ∀ {w n}, NameCorr w n → pB w = pM n) :
    (ws.find? pB = none ∧ ns.find? pM = none)
    ∨ ∃ w n, ws.find? pB = some w ∧ ns.find? pM = some n ∧ NameCorr w n := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons w n ws' ns' hc _ ih =>
    cases hp : pB w with
    | true =>
      have hq : pM n = true := by rw [← hpt hc]; exact hp
      exact Or.inr ⟨w, n, List.find?_cons_of_pos hp, List.find?_cons_of_pos hq, hc⟩
    | false =>
      have hq : pM n = false := by rw [← hpt hc]; exact hp
      have hp' : ¬ pB w = true := by simp [hp]
      have hq' : ¬ pM n = true := by simp [hq]
      rcases ih with ⟨h1, h2⟩ | ⟨w', n', h1, h2, hc'⟩
      · exact Or.inl ⟨by rw [List.find?_cons_of_neg hp']; exact h1,
          by rw [List.find?_cons_of_neg hq']; exact h2⟩
      · exact Or.inr ⟨w', n', by rw [List.find?_cons_of_neg hp']; exact h1,
          by rw [List.find?_cons_of_neg hq']; exact h2, hc'⟩

theorem nameCorr_pred_eq {b : ByteArray} {rr : ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rr) (hr : αRR rr = some r)
    {w : ByteArray} {n : Name} (hc : NameCorr w n) :
    nameEqCI (RRParse.rrName (RR := ResourceRecord) rr) w = nameEq r.owner n := by
  obtain ⟨hαw, hcw, hvw, -⟩ := hc
  have hown : αName rr.name = some r.owner := (αRR_fields rr r hr).1
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hci
    obtain ⟨no, hαo, hno⟩ := αName_of_nameEqCI hci hαw
    obtain rfl : no = r.owner := Option.some.inj (hαo.symm.trans hown)
    exact hno
  · intro hne
    obtain ⟨no, hαo, hcano, hvo⟩ := parseRaw_name_canonical hpr
    obtain rfl : no = r.owner := Option.some.inj (hαo.symm.trans hown)
    exact nameEqCI_of_αName_canonical hne hcano hcw hvo (fun x hx => (hvw x hx).2)

theorem namesCorr_nameMemB_eq {reachB : Array ByteArray} {reachM : List Name}
    (hcorr : NamesCorr reachB.toList reachM)
    {b : ByteArray} {rr : ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rr) (hr : αRR rr = some r) :
    VeriDNS.Impl.Resolver.nameMemB (RRParse.rrName (RR := ResourceRecord) rr) reachB
      = reachM.any (fun n => nameEq r.owner n) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    unfold VeriDNS.Impl.Resolver.nameMemB at h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hlt, hci⟩ := h
    obtain ⟨n, hn, hcn⟩ := hcorr.mem_left (Array.mem_def.mp (Array.getElem_mem hlt))
    rw [List.any_eq_true]
    refine ⟨n, hn, ?_⟩
    rw [← nameCorr_pred_eq hpr hr hcn]
    exact hci
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨n, hn, hne⟩ := h
    obtain ⟨w, hw, hcn⟩ := hcorr.mem_right hn
    unfold VeriDNS.Impl.Resolver.nameMemB
    rw [Array.any_eq_true]
    obtain ⟨i, hlt, hEq⟩ := Array.getElem_of_mem (Array.mem_def.mpr hw)
    refine ⟨i, hlt, ?_⟩
    show nameEqCI (RRParse.rrName (RR := ResourceRecord) rr) reachB[i] = true
    rw [hEq, nameCorr_pred_eq hpr hr hcn]
    exact hne

theorem cnameTarget_nameCorr {answer : Array ByteArray}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer)
    {b : ByteArray} (hb : b ∈ answer) {rr : ResourceRecord}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rr)
    (hty : (rr.type == (5 : BitVec 16)) = true)
    {mt : Name} (hmt : αName rr.rdata = some mt) :
    NameCorr rr.rdata mt := by
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl, hpr'⟩ :=
    VeriDNS.Proof.DeliveredWire.canonicalRR_parse (hca b hb)
  obtain rfl : _ = rr := Option.some.inj (hpr'.symm.trans hpr)
  have ht5 : t = (5 : BitVec 16) := beq_iff_eq.mp hty
  subst ht5
  cases hrd with
  | nameType ht' hv' hle' =>
    rename_i rdLs
    have hα : αName (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs) = some rdLs.toList :=
      αName_labelsToWireFormat rdLs hv'
    obtain rfl : rdLs.toList = mt := Option.some.inj (hα.symm.trans hmt)
    refine ⟨hmt, rfl, ?_, hle'⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact hv' i (by simpa using hi)
  | prefixedName ht' hv' hle' =>
    rcases ht' with ⟨h15, -⟩ | ⟨h33, -⟩
    · exact absurd h15 (by decide)
    · exact absurd h33 (by decide)
  | other h2 h5 h12 h6 h15 h33 hsz => exact absurd rfl h5

theorem namesCorr_filterMap {α : Type} {l : List α} {f : α → Option ByteArray}
    {g : α → Option Name}
    (h : ∀ a ∈ l, (f a = none ∧ g a = none)
      ∨ ∃ w n, f a = some w ∧ g a = some n ∧ NameCorr w n) :
    NamesCorr (l.filterMap f) (l.filterMap g) := by
  induction l with
  | nil => exact .nil
  | cons a t ih =>
    rw [List.filterMap_cons, List.filterMap_cons]
    rcases h a (List.mem_cons_self ..) with ⟨hf, hg⟩ | ⟨w, n, hf, hg, hc⟩
    · rw [hf, hg]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    · rw [hf, hg]
      exact .cons hc (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem namesCorr_reachStep {answer : Array ByteArray}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer) (habs : AllAbstract answer)
    {reachB : Array ByteArray} {reachM : List Name}
    (hc : NamesCorr reachB.toList reachM) :
    NamesCorr (VeriDNS.Impl.Resolver.reachStepB (RR := ResourceRecord) answer reachB).toList
      (VeriDNS.Spec.Net.reachStep (αSection answer) reachM) := by
  unfold VeriDNS.Impl.Resolver.reachStepB VeriDNS.Spec.Net.reachStep αSection
  rw [Array.toList_append, Array.toList_filterMap, List.filterMap_filterMap]
  refine hc.append (namesCorr_filterMap ?_)
  intro b hb
  have hbmem : b ∈ answer := Array.mem_def.mpr hb
  obtain ⟨rr, hpr⟩ := allParse_of_canonicalSection hca b hbmem
  obtain ⟨r, hr⟩ := habs b hbmem rr hpr
  unfold VeriDNS.Impl.Resolver.reachTarget?
  simp only [hpr, hr, Option.bind_some]
  by_cases hty : (rr.type == (5 : BitVec 16)) = true
  · obtain ⟨mt, hmt, hrdmt⟩ := αRR_cname hr hty
    have hctr : VeriDNS.Spec.Net.cnameTarget? r = some mt := by
      unfold VeriDNS.Spec.Net.cnameTarget?; rw [hrdmt]
    have hmemEq := namesCorr_nameMemB_eq hc hpr hr
    by_cases hmem : VeriDNS.Impl.Resolver.nameMemB
        (RRParse.rrName (RR := ResourceRecord) rr) reachB = true
    · have hcond : (RRParse.rrType (RR := ResourceRecord) rr == (5 : BitVec 16)
          && VeriDNS.Impl.Resolver.nameMemB
            (RRParse.rrName (RR := ResourceRecord) rr) reachB) = true := by
        rw [Bool.and_eq_true]; exact ⟨hty, hmem⟩
      have hanyM : (reachM.any (fun n => nameEq r.owner n)) = true := by
        rw [← hmemEq]; exact hmem
      refine Or.inr ⟨RRParse.rrRdata (RR := ResourceRecord) rr, mt, ?_, ?_,
        cnameTarget_nameCorr hca hbmem hpr hty hmt⟩
      · rw [if_pos hcond]
      · rw [hctr]
        simp only [Option.bind_some]
        rw [if_pos hanyM]
    · have hcond : ¬ (RRParse.rrType (RR := ResourceRecord) rr == (5 : BitVec 16)
          && VeriDNS.Impl.Resolver.nameMemB
            (RRParse.rrName (RR := ResourceRecord) rr) reachB) = true := by
        rw [Bool.and_eq_true]; rintro ⟨-, hm⟩; exact hmem hm
      have hanyM : ¬ (reachM.any (fun n => nameEq r.owner n)) = true := by
        rw [← hmemEq]; exact hmem
      refine Or.inl ⟨by rw [if_neg hcond], ?_⟩
      rw [hctr]
      simp only [Option.bind_some]
      rw [if_neg hanyM]
  · have hcond : ¬ (RRParse.rrType (RR := ResourceRecord) rr == (5 : BitVec 16)
        && VeriDNS.Impl.Resolver.nameMemB
          (RRParse.rrName (RR := ResourceRecord) rr) reachB) = true := by
      rw [Bool.and_eq_true]; rintro ⟨hty', -⟩; exact hty hty'
    refine Or.inl ⟨by rw [if_neg hcond], ?_⟩
    cases hct : VeriDNS.Spec.Net.cnameTarget? r with
    | none => rfl
    | some t' =>
      exfalso
      have hrdc := VeriDNS.Spec.Net.cnameTarget?_some hct
      have hrt := αRR_rtype rr r hr
      rw [hrdc] at hrt
      exact hty (by rw [αType_cname_five hrt]; rfl)

theorem namesCorr_reachIter {answer : Array ByteArray}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer) (habs : AllAbstract answer) :
    ∀ (k : Nat) (reachB : Array ByteArray) (reachM : List Name),
      NamesCorr reachB.toList reachM →
      NamesCorr (VeriDNS.Impl.Resolver.reachIterB (RR := ResourceRecord) answer k reachB).toList
        (VeriDNS.Spec.Net.reachIter (αSection answer) k reachM) := by
  intro k
  induction k with
  | zero => intro rB rM h; exact h
  | succ k ih => intro rB rM h; exact ih _ _ (namesCorr_reachStep hca habs h)

theorem length_filterMap_of_isSome {α β : Type} (g : α → Option β) :
    ∀ (l : List α), (∀ b ∈ l, (g b).isSome = true) → (l.filterMap g).length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b t ih =>
    intro h
    rw [List.filterMap_cons]
    cases hg : g b with
    | none =>
      have hb := h b (by simp)
      rw [hg] at hb
      exact absurd hb (by simp)
    | some r =>
      simp only [List.length_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem b hx))]

theorem αSection_length {answer : Array ByteArray}
    (hparse : AllParse answer) (habs : AllAbstract answer) :
    (αSection answer).length = answer.size := by
  unfold αSection
  rw [← Array.length_toList]
  apply length_filterMap_of_isSome
  intro b hb
  obtain ⟨rr, hpr⟩ := hparse b (Array.mem_def.mpr hb)
  obtain ⟨r, hr⟩ := habs b (Array.mem_def.mpr hb) rr hpr
  simp only [hpr, hr, Option.isSome_some]

theorem namesCorr_reachableNames {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer) (habs : AllAbstract answer)
    (hqcorr : NameCorr qname mqname) :
    NamesCorr
      (VeriDNS.Impl.Resolver.reachableNamesB (RR := ResourceRecord) qname answer).toList
      (VeriDNS.Spec.Net.reachableNames mqname (αSection answer)) := by
  unfold VeriDNS.Impl.Resolver.reachableNamesB VeriDNS.Spec.Net.reachableNames
  rw [αSection_length (allParse_of_canonicalSection hca) habs]
  apply namesCorr_reachIter hca habs
  have hseed : (#[qname] : Array ByteArray).toList = [qname] := by simp
  rw [hseed]
  exact .cons hqcorr .nil

theorem αRR_setName {rr : ResourceRecord} {r : VeriDNS.Spec.Net.RR} {w : ByteArray}
    {n : Name} (h : αRR rr = some r) (hw : αName w = some n) :
    αRR { rr with name := w } = some { r with owner := n } := by
  unfold αRR at h ⊢
  split at h
  · rename_i owner rdata cls hn hrd hcl
    obtain rfl := Option.some.inj h
    simp only [hw, hrd, hcl]
  · exact absurd h (by simp)

theorem αSection_scrubAnswerB_eq {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer)
    (habs : AllAbstract answer)
    (hq : αName qname = some mqname)
    (hqc : qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo mqname)
    (hqv : ∀ x ∈ mqname, 0 < x.size ∧ x.size ≤ 63)
    (hq255 : qname.size ≤ 255) :
    αSection (scrubAnswerB (RR := ResourceRecord) qname answer)
      = scrubAnswer mqname (αSection answer) := by
  have hqcorr : NameCorr qname mqname := ⟨hq, hqc, hqv, hq255⟩
  have hcorr := namesCorr_reachableNames hca habs hqcorr
  unfold VeriDNS.Impl.Resolver.scrubAnswerB VeriDNS.Spec.Net.scrubAnswer αSection
  rw [Array.toList_filterMap, List.filterMap_filterMap, List.filterMap_filterMap]
  apply filterMap_congr_mem
  intro b hb
  have hbmem : b ∈ answer := Array.mem_def.mpr hb
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl, hpr⟩ :=
    VeriDNS.Proof.DeliveredWire.canonicalRR_parse (hca _ hbmem)
  obtain ⟨r, hr⟩ := habs _ hbmem _ hpr
  simp only [hpr, hr, Option.bind_some]
  rw [← Array.find?_toList]
  rcases hcorr.find?_corr (fun {w n} hc => nameCorr_pred_eq hpr hr hc)
    with ⟨hfB, hfM⟩ | ⟨w, n, hfB, hfM, hcn⟩
  · unfold αSection at hfM
    rw [hfB, hfM]
    rfl
  · unfold αSection at hfM
    rw [hfB, hfM]
    simp only [Option.map_some, Option.bind_some]
    obtain ⟨hαw, hcw, hvw, hw255⟩ := hcn
    have hwArr : w = VeriDNS.Impl.DomainName.labelsToWireFormat n.toArray := by
      rw [hcw]
      show VeriDNS.Impl.DomainName.labelsToWireFormatGo n
        = VeriDNS.Impl.DomainName.labelsToWireFormatGo n.toArray.toList
      rw [List.toList_toArray]
    have hvArr : VeriDNS.Proof.DomainName.ValidLabels n.toArray := by
      intro i hlt
      exact hvw (n.toArray[i]) (by
        have := Array.getElem_mem hlt
        rwa [Array.mem_def, List.toList_toArray] at this)
    have hleArr : (VeriDNS.Impl.DomainName.labelsToWireFormat n.toArray).size ≤ 255 := by
      rw [← hwArr]; exact hw255
    have hαArr : αName (VeriDNS.Impl.DomainName.labelsToWireFormat n.toArray) = some n := by
      rw [← hwArr]; exact hαw
    rw [hwArr,
      VeriDNS.Proof.DeliveredWire.setOwnerB_rrWire ls n.toArray t c ttl rdata rfl,
      VeriDNS.Proof.DeliveredWire.parseRaw_rrWire n.toArray hvArr hleArr t c ttl rdata
        (VeriDNS.Proof.Message.canonicalRdata_size_lt hrd)]
    exact αRR_setName hr hαArr

theorem scrubAnswerB_delivered_model_authentic
    {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer)
    (habs : AllAbstract answer)
    (hq : αName qname = some mqname)
    (hqc : qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo mqname)
    (hqv : ∀ x ∈ mqname, 0 < x.size ∧ x.size ≤ 63)
    (hq255 : qname.size ≤ 255)
    {r : VeriDNS.Spec.Net.RR}
    (hr : r ∈ αSection (scrubAnswerB (RR := ResourceRecord) qname answer)) :
    ∃ n, CnameReachable mqname (αSection answer) n ∧ nameEq r.owner n = true := by
  rw [αSection_scrubAnswerB_eq hca habs hq hqc hqv hq255] at hr
  exact VeriDNS.Spec.Net.scrubAnswer_authentic mqname (αSection answer) r hr

end VeriDNS.Proof.Refinement
