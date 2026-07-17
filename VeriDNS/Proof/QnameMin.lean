import VeriDNS.Proof.Refinement
import VeriDNS.Proof.DeliveredWire



namespace VeriDNS.Proof.QnameMin

open VeriDNS.Impl.DomainName
open VeriDNS.Proof.DomainName (ValidLabels wireFormat_roundtrip wireFormatToLabels_valid)
open VeriDNS.Proof.DeliveredWire (CanonicalName)
open VeriDNS.Proof.Refinement (αName foldNameCase_labelsToWireFormat)


theorem validLabels_extract (ls : Array ByteArray) (hv : ValidLabels ls) (i j : Nat) :
    ValidLabels (ls.extract i j) := by
  intro k hk
  simp only [Array.getElem_extract]
  have hsz : (ls.extract i j).size = min j ls.size - i := Array.size_extract
  exact hv (i + k) (by omega)

private theorem le63_of_valid {ls : Array ByteArray} (hv : ValidLabels ls) :
    ∀ x ∈ ls, x.size ≤ 63 := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  exact (hv i hi).2

private theorem extract_suffix_toList (ls : Array ByteArray) (i : Nat) :
    (ls.extract i ls.size).toList = ls.toList.drop i := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  exact List.take_of_length_le (by simp)

private theorem go_size_drop (l : List ByteArray) (i : Nat) :
    (labelsToWireFormatGo (l.drop i)).size ≤ (labelsToWireFormatGo l).size := by
  induction l generalizing i with
  | nil => simp
  | cons x rest ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hsz : (labelsToWireFormatGo (x :: rest)).size
          = 1 + x.size + (labelsToWireFormatGo rest).size := by
        simp [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push]
      have := ih i
      simp only [List.drop_succ_cons]
      omega

theorem labelsToWireFormat_suffix_size_le (ls : Array ByteArray) (i : Nat) :
    (labelsToWireFormat (ls.extract i ls.size)).size ≤ (labelsToWireFormat ls).size := by
  unfold labelsToWireFormat
  rw [extract_suffix_toList]
  exact go_size_drop ls.toList i


theorem minimisedName_wire (ls : Array ByteArray) (hv : ValidLabels ls) (keep : Nat) :
    minimisedName (labelsToWireFormat ls) keep
      = labelsToWireFormat (ls.extract (ls.size - keep) ls.size) := by
  unfold minimisedName
  rw [wireFormat_roundtrip ls hv]
  by_cases h : keep < ls.size
  · simp [h]
  · have h0 : ls.size - keep = 0 := by omega
    simp [h, h0]

theorem minimisedName_canonical {m : ByteArray} (h : CanonicalName m) (keep : Nat) :
    CanonicalName (minimisedName m keep) := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  rw [minimisedName_wire ls hv]
  exact ⟨ls.extract (ls.size - keep) ls.size, validLabels_extract ls hv _ _,
    Nat.le_trans (labelsToWireFormat_suffix_size_le ls _) hle, rfl⟩

theorem minimisedName_go {qn : List ByteArray}
    (hval : ∀ x ∈ qn, 0 < x.size ∧ x.size ≤ 63) (keep : Nat) :
    minimisedName (labelsToWireFormatGo qn) keep
      = labelsToWireFormatGo (qn.drop (qn.length - keep)) := by
  have hv : ValidLabels qn.toArray := by
    intro i hi
    exact hval _ (by simpa using Array.getElem_mem hi)
  have hgo : labelsToWireFormatGo qn = labelsToWireFormat qn.toArray := by
    unfold labelsToWireFormat
    simp
  rw [hgo, minimisedName_wire _ hv]
  unfold labelsToWireFormat
  rw [extract_suffix_toList]
  simp


theorem labelCount_wire (ls : Array ByteArray) (hv : ValidLabels ls) :
    labelCount (labelsToWireFormat ls) = ls.size := by
  unfold labelCount
  rw [wireFormat_roundtrip ls hv]

theorem labelCount_minimisedName {m : ByteArray} (h : CanonicalName m) (keep : Nat) :
    labelCount (minimisedName m keep) = min (labelCount m) keep := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  rw [minimisedName_wire ls hv, labelCount_wire ls hv,
    labelCount_wire _ (validLabels_extract ls hv _ _), Array.size_extract]
  omega

theorem minimisedName_full {m : ByteArray} {keep : Nat} (h : labelCount m ≤ keep) :
    minimisedName m keep = m := by
  unfold minimisedName
  unfold labelCount at h
  split
  · next ls heq =>
    simp only [heq] at h
    simp only [if_neg (by omega : ¬ keep < ls.size)]
  · rfl


theorem isAncestorB_minimisedName {m : ByteArray} (h : CanonicalName m) (keep : Nat) :
    VeriDNS.Impl.Resolver.isAncestorB (minimisedName m keep) m = true := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  rw [minimisedName_wire ls hv]
  unfold VeriDNS.Impl.Resolver.isAncestorB
  rw [wireFormat_roundtrip ls hv, wireFormat_roundtrip _ (validLabels_extract ls hv _ _)]
  simp only [extract_suffix_toList, List.map_drop]
  refine (Bool.and_eq_true ..).mpr ⟨decide_eq_true ?_, decide_eq_true ?_⟩
  · simp only [List.length_drop]
    omega
  · congr 1
    simp only [List.length_drop, List.length_map, Array.length_toList]
    omega


theorem foldNameCase_minimisedName {m : ByteArray} (h : CanonicalName m) (keep : Nat) :
    foldNameCase (minimisedName m keep) = minimisedName (foldNameCase m) keep := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  have hvf : ValidLabels (ls.map foldNameCase) := by
    intro i hi
    have hi' : i < ls.size := by simpa using hi
    simp only [Array.getElem_map]
    have hsz : (foldNameCase (ls[i]'hi')).size = (ls[i]'hi').size :=
      VeriDNS.Proof.NameTree.foldNameCase_size _
    rw [hsz]
    exact hv i hi'
  rw [minimisedName_wire ls hv,
    foldNameCase_labelsToWireFormat _ (le63_of_valid (validLabels_extract ls hv _ _)),
    foldNameCase_labelsToWireFormat ls (le63_of_valid hv), minimisedName_wire _ hvf]
  rw [Array.map_extract]
  simp [Array.size_map]


theorem αName_minimisedName {m : ByteArray} {n : VeriDNS.Spec.Net.Name}
    (h : αName m = some n) (keep : Nat) :
    αName (minimisedName m keep) = some (n.drop (n.length - keep)) := by
  unfold αName at h
  cases hm : wireFormatToLabels m with
  | error e => rw [hm] at h; exact absurd h (by simp)
  | ok ls =>
    rw [hm] at h
    have hn : n = ls.toList := by injection h with h; exact h.symm
    subst hn
    have hvls : ValidLabels ls := by
      intro i hi
      exact (wireFormatToLabels_valid hm ls[i]
        (by simp))
    unfold minimisedName
    simp only [hm]
    by_cases hk : keep < ls.size
    · simp only [if_pos hk]
      unfold αName
      rw [wireFormat_roundtrip _ (validLabels_extract ls hvls _ _)]
      simp only [extract_suffix_toList, Array.length_toList]
    · simp only [if_neg hk]
      unfold αName
      simp only [hm]
      have h0 : ls.toList.length - keep = 0 := by
        have : ls.toList.length = ls.size := Array.length_toList
        omega
      rw [h0, List.drop_zero]


open VeriDNS.Spec.Net in
theorem probeFor_facts {probe qname cut : Name} (h : ProbeFor probe qname cut = true) :
    isAncestor cut probe = true ∧ isAncestor probe qname = true
      ∧ cut.length < probe.length ∧ probe.length < qname.length := by
  unfold ProbeFor at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

open VeriDNS.Spec.Net in
theorem probeFor_ne {probe qname cut : Name} (h : ProbeFor probe qname cut = true) :
    probe ≠ qname := by
  intro hcontra
  have := (probeFor_facts h).2.2.2
  subst hcontra
  omega

end VeriDNS.Proof.QnameMin
