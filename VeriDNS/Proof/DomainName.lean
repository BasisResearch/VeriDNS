import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName
import VeriDNS.Proof.Primitives

namespace VeriDNS.Proof.DomainName

open VeriDNS.Impl.DomainName

-- ============================================================
-- labelsToWireFormat / wireFormatToLabels roundtrip
-- ============================================================

/-- A label array is valid if every label has length 1–63 (per RFC 1035 §2.3.1). -/
def ValidLabels (labels : Array ByteArray) : Prop :=
  ∀ (i : Nat) (h : i < labels.size), 0 < labels[i].size ∧ labels[i].size ≤ 63

-- ============================================================
-- ByteArray helper lemmas
-- ============================================================

private theorem ba_append_assoc (a b c : ByteArray) : a ++ b ++ c = a ++ (b ++ c) := by
  ext1; simp [ByteArray.data_append, Array.append_assoc]

private theorem ba_empty_append (a : ByteArray) : ByteArray.empty ++ a = a := by
  ext1; simp [ByteArray.data_append]

theorem labelsToWireFormatGo_size_pos (ls : List ByteArray) :
    0 < (labelsToWireFormatGo ls).size := by
  induction ls with
  | nil => simp [labelsToWireFormatGo]; decide
  | cons l rest ih =>
    simp [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push]; omega

private theorem ba_extract_at_size (a b : ByteArray) (i j : Nat) :
    (a ++ b).extract (a.size + i) (a.size + j) = b.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have hsd : a.data.size = a.size := ByteArray.size_data
  have h1 : a.data.extract (a.size + i) (a.size + j) = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  simp only [h1, Array.empty_append, hsd]; congr 1 <;> omega

private theorem ba_extract_zero_size (l rest : ByteArray) :
    (l ++ rest).extract 0 l.size = l := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  simp [ByteArray.size_data, Array.extract_eq_self_of_le]

private theorem extract_label (pre hdr l tail : ByteArray) :
    ((pre ++ hdr) ++ l ++ tail).extract (pre.size + hdr.size)
      (pre.size + hdr.size + l.size) = l := by
  rw [ba_append_assoc (pre ++ hdr) l tail,
      ← ByteArray.size_append (a := pre) (b := hdr)]
  exact (ba_extract_at_size (pre ++ hdr) (l ++ tail) 0 l.size).trans
    (ba_extract_zero_size l tail)

-- ============================================================
-- Combined frame+roundtrip: wireFormatToLabelsGo with prefix
-- ============================================================

set_option maxHeartbeats 800000 in
private theorem wireFormatToLabelsGo_prepend (pre : ByteArray) (ls : List ByteArray)
    (hv : ∀ l ∈ ls, 0 < l.size ∧ l.size ≤ 63) :
    wireFormatToLabelsGo (pre ++ labelsToWireFormatGo ls) pre.size = .ok ls := by
  induction ls generalizing pre with
  | nil =>
    simp only [labelsToWireFormatGo]
    rw [wireFormatToLabelsGo]
    have hsz1 : (⟨#[0]⟩ : ByteArray).size = 1 := by decide
    have hlt : pre.size < (pre ++ (⟨#[0]⟩ : ByteArray)).size := by
      rw [ByteArray.size_append, hsz1]; omega
    simp only [dif_pos hlt]
    have hbyte : (pre ++ (⟨#[0]⟩ : ByteArray)).data[pre.size]'hlt = (0 : UInt8) := by
      simp only [ByteArray.data_append]
      rw [Array.getElem_append_right (show pre.data.size ≤ pre.size from by
        simp [ByteArray.size_data])]
      simp [ByteArray.size_data]
    simp only [hbyte, UInt8.toNat_zero, ↓reduceDIte]
  | cons l rest ih =>
    have hl := hv l List.mem_cons_self
    have hvrest : ∀ l' ∈ rest, 0 < l'.size ∧ l'.size ≤ 63 :=
      fun l' hl' => hv l' (List.mem_cons_of_mem l hl')
    simp only [labelsToWireFormatGo]
    -- wire = pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++ labelsToWireFormatGo rest)
    rw [wireFormatToLabelsGo]
    have hlt : pre.size <
        (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).size := by
      simp [ByteArray.size_append, ByteArray.size_push]; omega
    simp only [dif_pos hlt]
    -- Byte at pre.size is l.size
    have hbyte : ((pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
        labelsToWireFormatGo rest)).data[pre.size]'hlt).toNat = l.size := by
      simp only [ByteArray.data_append, ByteArray.data_push, ByteArray.data_empty]
      show (pre.data ++ (#[l.size.toUInt8] ++ l.data ++
        (labelsToWireFormatGo rest).data))[pre.size].toNat = l.size
      rw [Array.getElem_append_right (show pre.data.size ≤ pre.size from by
        simp [ByteArray.size_data])]
      simp only [ByteArray.size_data]
      rw [Array.getElem_append_left (show pre.size - pre.size <
        (#[l.size.toUInt8] ++ l.data).size from by simp; omega)]
      rw [Array.getElem_append_left (show pre.size - pre.size <
        #[l.size.toUInt8].size from by simp)]
      simp [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]; omega
    simp only [hbyte]
    -- Resolve branches
    have hbnd : pre.size + 1 + l.size ≤
        (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).size := by
      simp [ByteArray.size_append, ByteArray.size_push]; omega
    simp only [dif_neg (show ¬(l.size = 0) from by omega),
               dif_neg (show ¬(l.size > 63) from by omega),
               dif_pos hbnd]
    -- Recursive call
    have hrec : wireFormatToLabelsGo
        (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++ labelsToWireFormatGo rest))
        (pre.size + 1 + l.size) = .ok rest := by
      rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8 ++ l)
        (labelsToWireFormatGo rest)]
      rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8) l]
      rw [show pre.size + 1 + l.size =
        (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l).size from by
          simp [ByteArray.size_append, ByteArray.size_push]]
      exact ih (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l) hvrest
    rw [hrec]
    -- Extract gives l
    have hext : (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
        labelsToWireFormatGo rest)).extract (pre.size + 1) (pre.size + 1 + l.size) = l := by
      rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8 ++ l)
        (labelsToWireFormatGo rest)]
      rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8) l]
      show ((pre ++ ByteArray.empty.push l.size.toUInt8) ++ l ++
        labelsToWireFormatGo rest).extract
        (pre.size + (ByteArray.empty.push l.size.toUInt8).size)
        (pre.size + (ByteArray.empty.push l.size.toUInt8).size + l.size) = l
      exact extract_label pre (ByteArray.empty.push l.size.toUInt8) l
        (labelsToWireFormatGo rest)
    simp only [hext]

-- ============================================================
-- Main roundtrip theorem
-- ============================================================

theorem wireFormat_roundtrip (labels : Array ByteArray) (hv : ValidLabels labels) :
    wireFormatToLabels (labelsToWireFormat labels) = .ok labels := by
  simp only [wireFormatToLabels, labelsToWireFormat]
  have hvl : ∀ l ∈ labels.toList, 0 < l.size ∧ l.size ≤ 63 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hl)
    exact hv i hi
  have h := wireFormatToLabelsGo_prepend ByteArray.empty labels.toList hvl
  rw [ba_empty_append] at h
  change wireFormatToLabelsGo (labelsToWireFormatGo labels.toList) 0 = .ok labels.toList at h
  simp only [h, Array.toArray_toList]

-- ============================================================
-- UInt8 helper lemmas
-- ============================================================

private theorem toUInt8_toNat (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

-- ============================================================
-- decodeNameAux with prefix: the fuel-based decoder roundtrip
-- ============================================================

set_option maxHeartbeats 1600000 in
private theorem decodeNameAux_prepend (pre : ByteArray) (ls : List ByteArray)
    (hv : ∀ l ∈ ls, 0 < l.size ∧ l.size ≤ 63) (fuel : Nat) (hfuel : ls.length < fuel) :
    decodeNameAux (pre ++ labelsToWireFormatGo ls) pre.size fuel none
    = .ok (ls.toArray, (pre ++ labelsToWireFormatGo ls).size) := by
  induction ls generalizing pre fuel with
  | nil =>
    match fuel, hfuel with
    | fuel + 1, _ =>
      simp only [labelsToWireFormatGo, decodeNameAux]
      have hlt : pre.size < (pre ++ (⟨#[0]⟩ : ByteArray)).data.size := by
        simp [ByteArray.size_data]
      simp only [dif_pos hlt]
      have hbyte : (pre ++ (⟨#[0]⟩ : ByteArray)).data[pre.size] = (0 : UInt8) := by
        simp only [ByteArray.data_append]
        rw [Array.getElem_append_right (show pre.data.size ≤ pre.size from by
          simp [ByteArray.size_data])]
        simp [ByteArray.size_data]
      simp only [hbyte]; simp (config := { decide := true })
  | cons l rest ih =>
    match fuel, hfuel with
    | fuel + 1, hfuel =>
      have hl := hv l List.mem_cons_self
      have hvrest : ∀ l' ∈ rest, 0 < l'.size ∧ l'.size ≤ 63 :=
        fun l' hl' => hv l' (List.mem_cons_of_mem l hl')
      have h256 : l.size < 256 := by omega
      have htoNat : l.size.toUInt8.toNat = l.size := toUInt8_toNat l.size h256
      have hne0 : (l.size.toUInt8 == (0 : UInt8)) = false := by
        apply beq_false_of_ne; intro h; have h2 := congrArg UInt8.toNat h
        simp only [UInt8.toNat_zero, toUInt8_toNat l.size h256] at h2; omega
      show decodeNameAux (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
        labelsToWireFormatGo rest)) pre.size (fuel + 1) none
        = .ok ((l :: rest).toArray, (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).size)
      simp only [decodeNameAux]
      have hlt : pre.size < (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).data.size := by
        simp [ByteArray.size_data]; omega
      simp only [dif_pos hlt]
      have hbyte : (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).data[pre.size] = l.size.toUInt8 := by
        simp only [ByteArray.data_append, ByteArray.data_push, ByteArray.data_empty]
        show (pre.data ++ (#[l.size.toUInt8] ++ l.data ++
          (labelsToWireFormatGo rest).data))[pre.size] = l.size.toUInt8
        rw [Array.getElem_append_right (show pre.data.size ≤ pre.size from by
          simp [ByteArray.size_data])]
        simp only [ByteArray.size_data]
        show (#[l.size.toUInt8] ++ l.data ++
          (labelsToWireFormatGo rest).data)[pre.size - pre.size] = _
        rw [Array.getElem_append_left (show pre.size - pre.size <
          (#[l.size.toUInt8] ++ l.data).size from by simp; omega)]
        rw [Array.getElem_append_left (show pre.size - pre.size <
          #[l.size.toUInt8].size from by simp)]
        simp
      simp only [hbyte, hne0, ite_false, htoNat, show ¬(l.size > 63) from by omega]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnocomp2 : (l.size &&& 192 == 192) = false := by
        have : l.size &&& 192 ≤ l.size := Nat.and_le_left
        exact beq_false_of_ne (by omega)
      simp only [hnocomp2, Bool.false_eq_true, ↓reduceIte]
      have hbnd : pre.size + 1 + l.size ≤ (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).data.size := by
        simp [ByteArray.size_data]
      simp only [show (pre.size + 1 + l.size ≤ (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++
        l) ++ labelsToWireFormatGo rest)).data.size) = True from eq_true hbnd, ↓reduceIte]
      -- Recursive call
      have hrec : decodeNameAux
          (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++ labelsToWireFormatGo rest))
          (pre.size + 1 + l.size) fuel none
          = .ok (rest.toArray, (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
            labelsToWireFormatGo rest)).size) := by
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8 ++ l)
          (labelsToWireFormatGo rest)]
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8) l]
        rw [show pre.size + 1 + l.size =
          (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l).size from by
            simp [ByteArray.size_append, ByteArray.size_push]]
        exact ih (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l) hvrest fuel
          (by simp at hfuel; omega)
      rw [hrec]
      -- Extract gives l
      have hext : (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).extract (pre.size + 1) (pre.size + 1 + l.size) = l := by
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8 ++ l)
          (labelsToWireFormatGo rest)]
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8) l]
        show ((pre ++ ByteArray.empty.push l.size.toUInt8) ++ l ++
          labelsToWireFormatGo rest).extract
          (pre.size + (ByteArray.empty.push l.size.toUInt8).size)
          (pre.size + (ByteArray.empty.push l.size.toUInt8).size + l.size) = l
        exact extract_label pre (ByteArray.empty.push l.size.toUInt8) l
          (labelsToWireFormatGo rest)
      simp only [hext]; simp

-- ============================================================
-- decodeNameAux / encodeName roundtrip (uncompressed names)
-- ============================================================

/-- Decoding a name from a buffer produced by encodeName recovers the labels.
    This is the core roundtrip property for uncompressed domain names. -/
theorem decode_encode_name (labels : Array ByteArray) (hv : ValidLabels labels) :
    let wire := labelsToWireFormat labels
    decodeNameAux wire 0 wire.size none = .ok (labels, wire.size) := by
  simp only [labelsToWireFormat]
  have hvl : ∀ l ∈ labels.toList, 0 < l.size ∧ l.size ≤ 63 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hl)
    exact hv i hi
  have hfuel : labels.toList.length < (labelsToWireFormatGo labels.toList).size := by
    induction labels.toList with
    | nil => simp [labelsToWireFormatGo]; decide
    | cons l rest ih_fuel =>
      simp [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push]
      have := labelsToWireFormatGo_size_pos rest; omega
  have h := decodeNameAux_prepend ByteArray.empty labels.toList hvl _ hfuel
  rw [ba_empty_append] at h
  change decodeNameAux (labelsToWireFormatGo labels.toList) 0 _ none
    = .ok (labels.toList.toArray, _) at h
  simp only [Array.toArray_toList] at h
  exact h

-- ============================================================
-- decodeNameAux with prefix AND suffix
-- ============================================================

private theorem ba_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  ext1; simp [ByteArray.data_append]

set_option maxHeartbeats 1600000 in
theorem decodeNameAux_prepend_append (pre suf : ByteArray) (ls : List ByteArray)
    (hv : ∀ l ∈ ls, 0 < l.size ∧ l.size ≤ 63) (fuel : Nat) (hfuel : ls.length < fuel) :
    decodeNameAux (pre ++ labelsToWireFormatGo ls ++ suf) pre.size fuel none
    = .ok (ls.toArray, pre.size + (labelsToWireFormatGo ls).size) := by
  induction ls generalizing pre fuel with
  | nil =>
    match fuel, hfuel with
    | fuel + 1, _ =>
      simp only [labelsToWireFormatGo, decodeNameAux]
      have hlt : pre.size < (pre ++ (⟨#[0]⟩ : ByteArray) ++ suf).data.size := by
        simp [ByteArray.size_data]; omega
      simp only [dif_pos hlt]
      have hbyte : (pre ++ (⟨#[0]⟩ : ByteArray) ++ suf).data[pre.size] = (0 : UInt8) := by
        simp only [ByteArray.data_append]
        rw [Array.getElem_append_left (show pre.size <
          (pre.data ++ (⟨#[0]⟩ : ByteArray).data).size from by simp [ByteArray.size_data])]
        rw [Array.getElem_append_right (show pre.data.size ≤ pre.size from by
          simp [ByteArray.size_data])]
        simp [ByteArray.size_data]
      simp only [hbyte]; simp (config := { decide := true })
  | cons l rest ih =>
    match fuel, hfuel with
    | fuel + 1, hfuel =>
      have hl := hv l List.mem_cons_self
      have hvrest : ∀ l' ∈ rest, 0 < l'.size ∧ l'.size ≤ 63 :=
        fun l' hl' => hv l' (List.mem_cons_of_mem l hl')
      have h256 : l.size < 256 := by omega
      have htoNat : l.size.toUInt8.toNat = l.size := toUInt8_toNat l.size h256
      have hne0 : (l.size.toUInt8 == (0 : UInt8)) = false := by
        apply beq_false_of_ne; intro h; have h2 := congrArg UInt8.toNat h
        simp only [UInt8.toNat_zero, toUInt8_toNat l.size h256] at h2; omega
      show decodeNameAux (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
        labelsToWireFormatGo rest) ++ suf) pre.size (fuel + 1) none
        = .ok ((l :: rest).toArray, pre.size + ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest).size)
      simp only [decodeNameAux]
      have hlt : pre.size < (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest) ++ suf).data.size := by
        simp [ByteArray.size_data]; omega
      simp only [dif_pos hlt]
      have hbyte : (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest) ++ suf).data[pre.size] = l.size.toUInt8 := by
        simp only [ByteArray.data_append, ByteArray.data_push, ByteArray.data_empty]
        show ((pre.data ++ (#[l.size.toUInt8] ++ l.data ++
          (labelsToWireFormatGo rest).data)) ++ suf.data)[pre.size] = l.size.toUInt8
        rw [Array.getElem_append_left (show pre.size <
          (pre.data ++ (#[l.size.toUInt8] ++ l.data ++ (labelsToWireFormatGo rest).data)).size
          from by simp; omega)]
        rw [Array.getElem_append_right (show pre.data.size ≤ pre.size from by
          simp [ByteArray.size_data])]
        simp only [ByteArray.size_data]
        show (#[l.size.toUInt8] ++ l.data ++
          (labelsToWireFormatGo rest).data)[pre.size - pre.size] = _
        rw [Array.getElem_append_left (show pre.size - pre.size <
          (#[l.size.toUInt8] ++ l.data).size from by simp; omega)]
        rw [Array.getElem_append_left (show pre.size - pre.size <
          #[l.size.toUInt8].size from by simp)]
        simp
      simp only [hbyte, hne0, ite_false, htoNat, show ¬(l.size > 63) from by omega]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnocomp2 : (l.size &&& 192 == 192) = false := by
        have : l.size &&& 192 ≤ l.size := Nat.and_le_left
        exact beq_false_of_ne (by omega)
      simp only [hnocomp2, Bool.false_eq_true, ↓reduceIte]
      have hbnd : pre.size + 1 + l.size ≤ (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest) ++ suf).data.size := by
        simp [ByteArray.size_data]
      simp only [show (pre.size + 1 + l.size ≤ (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++
        l) ++ labelsToWireFormatGo rest) ++ suf).data.size) = True from eq_true hbnd, ↓reduceIte]
      -- Recursive call
      have hrec : decodeNameAux
          (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++ labelsToWireFormatGo rest) ++ suf)
          (pre.size + 1 + l.size) fuel none
          = .ok (rest.toArray, (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l).size +
            (labelsToWireFormatGo rest).size) := by
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8 ++ l)
          (labelsToWireFormatGo rest)]
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8) l]
        rw [show pre.size + 1 + l.size =
          (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l).size from by
            simp [ByteArray.size_append, ByteArray.size_push]]
        exact ih (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l) hvrest fuel
          (by simp at hfuel; omega)
      rw [hrec]
      -- Extract gives l
      have hext : (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest) ++ suf).extract (pre.size + 1) (pre.size + 1 + l.size) = l := by
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8 ++ l)
          (labelsToWireFormatGo rest)]
        rw [← ba_append_assoc pre (ByteArray.empty.push l.size.toUInt8) l]
        rw [ba_append_assoc (pre ++ ByteArray.empty.push l.size.toUInt8 ++ l)
          (labelsToWireFormatGo rest) suf]
        show ((pre ++ ByteArray.empty.push l.size.toUInt8) ++ l ++
          (labelsToWireFormatGo rest ++ suf)).extract
          (pre.size + (ByteArray.empty.push l.size.toUInt8).size)
          (pre.size + (ByteArray.empty.push l.size.toUInt8).size + l.size) = l
        exact extract_label pre (ByteArray.empty.push l.size.toUInt8) l
          (labelsToWireFormatGo rest ++ suf)
      simp only [hext]
      congr 1; simp [ByteArray.size_append, ByteArray.size_push]; omega

-- ============================================================
-- decodeName frame lemma (for use in Question/RR roundtrips)
-- ============================================================

open VeriDNS.Impl in
/-- `decodeName` on `pre ++ labelsToWireFormat labels ++ suf` at `pre.size`
    returns the original labels and advances past the wire format. -/
theorem decodeName_frame_labels
    (labels : Array ByteArray) (hv : ValidLabels labels)
    (pre suf : ByteArray) :
    DnsParser.run decodeName
      (pre ++ labelsToWireFormat labels ++ suf) pre.size
    = .ok (labels, pre.size + (labelsToWireFormat labels).size) := by
  simp only [decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure]
  -- Goal is now: match decodeNameAux buf pos buf.size none with ...
  -- We need to show decodeNameAux reduces correctly
  simp only [labelsToWireFormat]
  have hvl : ∀ l ∈ labels.toList, 0 < l.size ∧ l.size ≤ 63 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hl)
    exact hv i hi
  have hfuel : labels.toList.length <
      (pre ++ labelsToWireFormatGo labels.toList ++ suf).size := by
    simp only [ByteArray.size_append]
    have : labels.toList.length < (labelsToWireFormatGo labels.toList).size := by
      induction labels.toList with
      | nil => simp [labelsToWireFormatGo]; decide
      | cons l rest ih =>
        simp [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push]
        have := labelsToWireFormatGo_size_pos rest; omega
    omega
  rw [decodeNameAux_prepend_append pre suf labels.toList hvl _ hfuel]
  simp [Array.toArray_toList]

-- ============================================================
-- Adversarial-input safety
-- ============================================================

/-- Adversarial-input safety for the name decoder. Termination on ANY
    input is structural (recursion on `fuel`, initialized to `buf.size` by
    `decodeName`; a compression-pointer loop burns one fuel per hop and
    errors out), so this theorem pins the resource bounds of every
    SUCCESSFUL decode of arbitrary bytes: at most `fuel` labels, each at
    most 63 bytes (output linear in input size), and the final parser
    position inside the buffer (the caller's `setPos` cannot escape it).
    No well-formedness hypothesis on `buf`. -/
theorem decodeNameAux_adversarial_bounds (fuel : Nat) (buf : ByteArray)
    (pos : Nat) (firstEndPos : Option Nat)
    (hfep : ∀ e, firstEndPos = some e → e ≤ buf.size)
    (labels : Array ByteArray) (endPos : Nat)
    (h : decodeNameAux buf pos fuel firstEndPos = .ok (labels, endPos)) :
    labels.size ≤ fuel ∧ (∀ l ∈ labels, l.size ≤ 63) ∧ endPos ≤ buf.size := by
  induction fuel generalizing pos firstEndPos labels endPos with
  | zero =>
    unfold decodeNameAux at h
    simp at h
  | succ fuel ih =>
    unfold decodeNameAux at h
    split at h
    · rename_i hpos
      dsimp only [] at h
      split at h
      · -- null terminator
        injection h with hpair
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
        refine ⟨by simp, by simp, ?_⟩
        cases hf : firstEndPos with
        | some e =>
          have := hfep e hf
          simp only [hf, Option.getD_some]
          exact this
        | none =>
          simp only [hf, Option.getD_none]
          have hsz : pos < buf.size := hpos
          omega
      · split at h
        · -- compression pointer
          split at h
          · rename_i hpos2
            split at h
            · rename_i p hrec
              injection h with hpair
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
              have hend : firstEndPos.getD (pos + 2) ≤ buf.size := by
                cases hf : firstEndPos with
                | some e =>
                  have := hfep e hf
                  simp only [hf, Option.getD_some]
                  exact this
                | none =>
                  simp only [hf, Option.getD_none]
                  have hsz : pos + 1 < buf.size := hpos2
                  omega
              obtain ⟨hsz, hmem, _⟩ := ih _ _
                (fun e he => by rw [← Option.some.inj he]; exact hend) _ _ hrec
              exact ⟨Nat.le_succ_of_le hsz, hmem, hend⟩
            · simp at h
          · simp at h
        · -- plain label
          split at h
          · simp at h
          · rename_i hlen
            split at h
            · rename_i hroom
              split at h
              · rename_i p hrec
                injection h with hpair
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
                obtain ⟨hsz, hmem, hend⟩ := ih _ _ hfep _ _ hrec
                refine ⟨?_, ?_, hend⟩
                · simp only [Array.size_append, Array.size_singleton]
                  omega
                · intro l hl
                  rcases Array.mem_append.mp hl with hl | hl
                  · have hleq : l = buf.extract (pos + 1)
                        (pos + 1 + buf.data[pos].toNat) := by
                      simpa using hl
                    subst hleq
                    have hx := @ByteArray.size_extract buf (pos + 1)
                      (pos + 1 + buf.data[pos].toNat)
                    omega
                  · exact hmem l hl
              · simp at h
            · simp at h
    · simp at h

open VeriDNS.Impl in
/-- Parser-level corollary: ANY successful `decodeName` over arbitrary
    bytes yields at most `buf.size` labels of at most 63 bytes each, and
    leaves the parser position inside the buffer. Together with structural
    fuel termination, this closes the adversarial-input question for the
    name decoder: a hostile datagram (compression-pointer loop, deep
    chain, truncated label) either errors out or produces linearly bounded
    output. -/
theorem decodeName_adversarial_bounds (buf : ByteArray) (pos : Nat)
    (labels : Array ByteArray) (endPos : Nat)
    (h : DnsParser.run decodeName buf pos = .ok (labels, endPos)) :
    labels.size ≤ buf.size ∧ (∀ l ∈ labels, l.size ≤ 63) ∧ endPos ≤ buf.size := by
  simp only [decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure] at h
  split at h
  · rename_i p hrec
    injection h with hpair
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
    exact decodeNameAux_adversarial_bounds _ _ _ _ (by simp) _ _ hrec
  · simp at h

-- ============================================================
-- RFC 1035 §3.1: case-insensitive comparison conformance
-- (generated specs in Spec/DomainName.lean from "must compare labels in
--  a case-insensitive manner (i.e., A=a), assuming ASCII with zero
--  parity.  Non-alphabetic codes must match exactly.")
-- ============================================================

open VeriDNS.Spec in
/-- `nameEqCI` satisfies the generated `namespace_compare_caseinsensitive`:
    names identified by `foldNameCase` compare equal. This is the
    end-to-end direction that matters operationally — `EXAMPLE.com` must
    match a cache entry stored as `example.com`. -/
theorem nameEqCI_conforms :
    namespace_compare_caseinsensitive ByteArray nameEqCI foldNameCase := by
  intro a b h
  show nameEqCI a b = true
  unfold nameEqCI
  rw [h]
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp

open VeriDNS.Spec in
/-- The byte-level comparison underlying `nameEqCI` satisfies the generated
    `namespace_compare_example` ("(i.e., A=a)"): byte 65 ('A') matches
    byte 97 ('a'). -/
theorem foldCaseByte_example_conforms :
    namespace_compare_example (fun a b => foldCaseByte a == foldCaseByte b) := by
  show (foldCaseByte 65 == foldCaseByte 97) = true
  decide

open VeriDNS.Spec in
/-- The byte-level comparison satisfies the generated
    `namespace_nonalphabetic_match_exactly`: outside the alphabetic range
    the fold is the identity, so the comparison is exact equality. -/
theorem foldCaseByte_nonalphabetic_exact :
    namespace_nonalphabetic_match_exactly
      (fun a b => foldCaseByte a == foldCaseByte b) alphabeticByte := by
  intro a b ha hb
  show (foldCaseByte a == foldCaseByte b) = (a == b)
  have fix : ∀ (c : UInt8), alphabeticByte c = false → foldCaseByte c = c := by
    intro c hc
    unfold alphabeticByte at hc
    unfold foldCaseByte
    rw [Bool.or_eq_false_iff] at hc
    rw [hc.1]
    simp
  rw [fix a ha, fix b hb]

end VeriDNS.Proof.DomainName
