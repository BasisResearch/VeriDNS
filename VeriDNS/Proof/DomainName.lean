import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName
import VeriDNS.Proof.Primitives

namespace VeriDNS.Proof.DomainName

open VeriDNS.Impl.DomainName

def ValidLabels (labels : Array ByteArray) : Prop :=
  ∀ (i : Nat) (h : i < labels.size), 0 < labels[i].size ∧ labels[i].size ≤ 63

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

/-- Each nonempty label contributes at least 2 wire bytes (length octet + content), plus the root
    octet: `2·len + 1 ≤ wire size`. With the RFC 1035 §2.3.4 total ≤255 cap this bounds a canonical
    wire name to ≤127 labels — the label-count side of the name budget. -/
theorem labelsToWireFormatGo_length_bound (ls : List ByteArray)
    (hpos : ∀ x ∈ ls, 0 < x.size) :
    2 * ls.length + 1 ≤ (labelsToWireFormatGo ls).size := by
  induction ls with
  | nil => simp [labelsToWireFormatGo]; decide
  | cons l rest ih =>
    have he : (ByteArray.empty).size = 0 := rfl
    have hsz : (labelsToWireFormatGo (l :: rest)).size
        = 1 + l.size + (labelsToWireFormatGo rest).size := by
      simp only [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push, he]
    have hl := hpos l (List.mem_cons_self ..)
    have hr := ih (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons]
    omega

/-- The accumulator form of `encodedNameLen`: `foldl (·+1+size) acc ls + 1 = acc + wire size`. -/
private theorem foldl_encodedLen_eq (ls : List ByteArray) (acc : Nat) :
    List.foldl (fun a (l : ByteArray) => a + 1 + l.size) acc ls + 1
      = acc + (labelsToWireFormatGo ls).size := by
  induction ls generalizing acc with
  | nil =>
    have h0 : (labelsToWireFormatGo ([] : List ByteArray)).size = 1 := rfl
    simp [h0]
  | cons l rest ih =>
    have he : (ByteArray.empty).size = 0 := rfl
    have hsz : (labelsToWireFormatGo (l :: rest)).size
        = 1 + l.size + (labelsToWireFormatGo rest).size := by
      simp only [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push, he]
    rw [List.foldl_cons, ih (acc + 1 + l.size), hsz]
    omega

/-- The impl's `encodedNameLen` equals the wire-encoded size — so the ≤255 guard in `decodeName` is exactly
    a bound on `(labelsToWireFormat labels).size`. -/
theorem encodedNameLen_eq (labels : Array ByteArray) :
    Impl.DomainName.encodedNameLen labels = (Impl.DomainName.labelsToWireFormat labels).size := by
  unfold Impl.DomainName.encodedNameLen Impl.DomainName.labelsToWireFormat
  rw [← Array.foldl_toList]
  have h := foldl_encodedLen_eq labels.toList 1
  omega

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
    have hltd : pre.size < (pre ++ (⟨#[0]⟩ : ByteArray)).data.size := hlt
    simp only [dif_pos hltd]
    have hbyte : (pre ++ (⟨#[0]⟩ : ByteArray)).data[pre.size]'hltd = (0 : UInt8) := by
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

    rw [wireFormatToLabelsGo]
    have hlt : pre.size <
        (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).size := by
      simp [ByteArray.size_append, ByteArray.size_push]; omega
    have hltd : pre.size <
        (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).data.size := hlt
    simp only [dif_pos hltd]

    have hbyte : ((pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
        labelsToWireFormatGo rest)).data[pre.size]'hltd).toNat = l.size := by
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

    have hbnd : pre.size + 1 + l.size ≤
        (pre ++ ((ByteArray.empty.push l.size.toUInt8 ++ l) ++
          labelsToWireFormatGo rest)).size := by
      simp [ByteArray.size_append, ByteArray.size_push]; omega
    simp only [dif_neg (show ¬(l.size = 0) from by omega),
               dif_neg (show ¬(l.size > 63) from by omega),
               dif_pos hbnd]

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

/-- **Decoder validity**: every label produced by a successful `wireFormatToLabelsGo` run is
    DNS-valid — nonempty (a zero length byte terminates the name, producing `[]`) and ≤63 bytes
    (larger length bytes are rejected with an error). The label itself is
    `wire.extract (pos+1) (pos+1+len)` whose size is exactly the (1..63) length byte. The
    name-intrinsic fact the glueless-provenance driver invariant carries for address-less SLIST
    targets. -/
theorem wireFormatToLabelsGo_valid {wire : ByteArray} {pos : Nat} {ls : List ByteArray}
    (hw : wireFormatToLabelsGo wire pos = .ok ls) :
    ∀ l ∈ ls, 0 < l.size ∧ l.size ≤ 63 := by
  unfold wireFormatToLabelsGo at hw
  by_cases hpos : pos < wire.data.size
  · rw [dif_pos hpos] at hw
    dsimp only [] at hw
    split at hw
    · cases hw
      intro x hx
      simp at hx
    · next hzero =>
      split at hw
      · exact absurd hw (by simp)
      · next hbig =>
        split at hw
        · next hroom =>
          split at hw
          · next rest hrec =>
            cases hw
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · have hds : wire.data.size = wire.size := rfl
              constructor
              · rw [ByteArray.size_extract]
                omega
              · rw [ByteArray.size_extract]
                omega
            · exact wireFormatToLabelsGo_valid hrec x hx'
          · exact absurd hw (by simp)
        · exact absurd hw (by simp)
  · rw [dif_neg hpos] at hw
    cases hw
    intro x hx
    simp at hx
termination_by wire.size - pos
decreasing_by omega

/-- Corollary of `wireFormatToLabelsGo_valid` at the `wireFormatToLabels` entry point: a
    successfully decoded wire name has only valid (nonempty, ≤63-byte) labels. -/
theorem wireFormatToLabels_valid {wire : ByteArray} {labels : Array ByteArray}
    (h : wireFormatToLabels wire = .ok labels) :
    ∀ l ∈ labels.toList, 0 < l.size ∧ l.size ≤ 63 := by
  unfold wireFormatToLabels at h
  split at h
  · next ls hgo =>
    have harr : ls.toArray = labels := by injection h
    intro l hl
    refine wireFormatToLabelsGo_valid hgo l ?_
    rw [← harr] at hl
    simpa using hl
  · exact absurd h (by simp)

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

private theorem toUInt8_toNat (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

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

open VeriDNS.Impl in

theorem decodeName_frame_labels
    (labels : Array ByteArray) (hv : ValidLabels labels)
    (hle : (labelsToWireFormat labels).size ≤ 255)
    (pre suf : ByteArray) :
    DnsParser.run decodeName
      (pre ++ labelsToWireFormat labels ++ suf) pre.size
    = .ok (labels, pre.size + (labelsToWireFormat labels).size) := by
  simp only [decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure]

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
  simp only [Array.toArray_toList]
  rw [if_pos (by rw [encodedNameLen_eq]; exact hle)]
  simp [Array.toArray_toList]

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
      ·
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
        ·
          split at h
          · rename_i hpos2
            split at h
            · split at h
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
          · simp at h
        ·
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

theorem decodeName_adversarial_bounds (buf : ByteArray) (pos : Nat)
    (labels : Array ByteArray) (endPos : Nat)
    (h : DnsParser.run decodeName buf pos = .ok (labels, endPos)) :
    labels.size ≤ buf.size ∧ (∀ l ∈ labels, l.size ≤ 63) ∧ endPos ≤ buf.size := by
  simp only [decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure] at h
  split at h
  · rename_i p hrec
    split at h
    · injection h with hpair
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
      exact decodeNameAux_adversarial_bounds _ _ _ _ (by simp) _ _ hrec
    · simp at h
  · simp at h

open VeriDNS.Impl in
/-- **A successfully decoded name is ≤255 octets** (RFC 1035 §2.3.4) — the payoff of the `decodeName` length
    guard. This is the fact that discharges `decodeName_frame_labels`'s `hle` at the top-level round-trip: every
    name in a decoded message satisfies the cap, so re-encoding it fits the 16-bit length fields and re-decodes. -/
theorem run_decodeName_le255 (buf : ByteArray) (pos : Nat)
    (labels : Array ByteArray) (endPos : Nat)
    (h : DnsParser.run decodeName buf pos = .ok (labels, endPos)) :
    (labelsToWireFormat labels).size ≤ 255 := by
  simp only [decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure] at h
  split at h
  · rename_i p hrec
    split at h
    · rename_i hcond
      injection h with hpair
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
      rw [← encodedNameLen_eq]; exact hcond
    · simp at h
  · simp at h

open VeriDNS.Impl VeriDNS.Spec in

theorem decodeName_namespace_conforms (buf : ByteArray) (pos : Nat)
    (labels : Array ByteArray) (endPos : Nat)
    (h : DnsParser.run decodeName buf pos = .ok (labels, endPos)) :
    namespace_prop_0 ⟨labels⟩ := by
  intro l hl
  have hb := (decodeName_adversarial_bounds buf pos labels endPos h).2.1 l hl
  omega

open VeriDNS.Spec in

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

theorem foldCaseByte_example_conforms :
    namespace_compare_example (fun a b => foldCaseByte a == foldCaseByte b) := by
  show (foldCaseByte 65 == foldCaseByte 97) = true
  decide

open VeriDNS.Spec in

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
