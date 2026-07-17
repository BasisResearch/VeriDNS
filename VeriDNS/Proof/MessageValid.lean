import VeriDNS.Proof.Message
import VeriDNS.Proof.ResourceRecord
import VeriDNS.Impl.Cache

namespace VeriDNS.Proof.Message

open VeriDNS.Impl
open VeriDNS.Spec

private theorem uint8_toNat_pos_of_ne_zero {b : UInt8} (h : ¬(b == 0) = true) :
    0 < b.toNat := by
  have hne : b ≠ 0 := by simpa using h
  cases hn : b.toNat with
  | zero =>
    exact absurd (by simpa using UInt8.toNat_inj.mp (by simpa using hn)) hne
  | succ n => omega

theorem decodeNameAux_validLabels (fuel : Nat) (buf : ByteArray)
    (pos : Nat) (fep : Option Nat) (labels : Array ByteArray) (endPos : Nat)
    (h : Impl.DomainName.decodeNameAux buf pos fuel fep = .ok (labels, endPos)) :
    ∀ l ∈ labels, 0 < l.size ∧ l.size ≤ 63 := by
  induction fuel generalizing pos fep labels endPos with
  | zero =>
    unfold Impl.DomainName.decodeNameAux at h
    exact absurd h (by simp)
  | succ fuel ih =>
    unfold Impl.DomainName.decodeNameAux at h
    split at h
    · rename_i hpos
      dsimp only [] at h
      split at h
      ·
        obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        subst h1
        intro l hl
        simp at hl
      · split at h
        ·
          split at h
          · split at h
            · split at h <;> rename_i hrec
              · rename_i ls' ep'
                obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
                subst h1
                intro l hl
                exact ih _ _ _ _ hrec l hl
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        ·
          rename_i hb0 _hptr
          split at h
          · exact absurd h (by simp)
          · rename_i hlen63
            split at h
            · rename_i hbound
              split at h <;> rename_i hrec
              · rename_i rest ep'
                obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
                subst h1
                intro l hl
                rcases Array.mem_append.mp hl with hl | hl
                · have hleq : l = buf.extract (pos + 1)
                      (pos + 1 + (buf.data[pos]'hpos).toNat) := by
                    simpa using hl
                  subst hleq
                  have hsz : (buf.extract (pos + 1)
                      (pos + 1 + (buf.data[pos]'hpos).toNat)).size
                      = (buf.data[pos]'hpos).toNat := by
                    simp only [ByteArray.size_extract]
                    have hbsz : pos + 1 + (buf.data[pos]'hpos).toNat
                        ≤ buf.size := by
                      simpa [ByteArray.size_data] using hbound
                    omega
                  rw [hsz]
                  exact ⟨uint8_toNat_pos_of_ne_zero hb0, by omega⟩
                · exact ih _ _ _ _ hrec l hl
              · exact absurd h (by simp)
            · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem run_decodeName_validLabels {buf : ByteArray} {pos : Nat}
    {labels : Array ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.DomainName.decodeName buf pos = .ok (labels, pos')) :
    DomainName.ValidLabels labels := by
  have hmem : ∀ l ∈ labels, 0 < l.size ∧ l.size ≤ 63 := by
    simp only [Impl.DomainName.decodeName, Primitives.run_bind,
      Primitives.run_getBuffer, Primitives.run_getPos] at h
    split at h <;> rename_i haux
    · rename_i ls' ep'
      split at h
      · simp only [Primitives.run_bind, Primitives.run_setPos,
          Primitives.run_pure] at h
        obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        subst h1
        exact decodeNameAux_validLabels _ _ _ _ _ _ haux
      · exact absurd h (by simp [Primitives.run_fail])
    · exact absurd h (by simp [Primitives.run_fail])
  intro i hi
  exact hmem labels[i] (labels.getElem_mem hi)

theorem run_decodeMany_size {α : Type} (p : DnsParser α) :
    ∀ (n : Nat) (acc : Array α) (buf : ByteArray) (pos : Nat)
      (arr : Array α) (pos' : Nat),
    DnsParser.run (Impl.Message.decodeMany p n acc) buf pos = .ok (arr, pos') →
    arr.size = acc.size + n
  | 0, acc, buf, pos, arr, pos', h => by
    simp only [Impl.Message.decodeMany, Primitives.run_pure] at h
    obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
    subst h1
    rfl
  | n + 1, acc, buf, pos, arr, pos', h => by
    simp only [Impl.Message.decodeMany, Primitives.run_bind] at h
    split at h <;> rename_i hp
    · rename_i x posx
      have := run_decodeMany_size p n (acc.push x) buf posx arr pos' h
      simp only [Array.size_push] at this
      omega
    · exact absurd h (by simp)

theorem run_decodeMany_mem {α : Type} (P : α → Prop) (p : DnsParser α)
    (hp : ∀ {buf : ByteArray} {pos : Nat} {x : α} {pos' : Nat},
      DnsParser.run p buf pos = .ok (x, pos') → P x) :
    ∀ (n : Nat) (acc : Array α) (buf : ByteArray) (pos : Nat)
      (arr : Array α) (pos' : Nat),
    DnsParser.run (Impl.Message.decodeMany p n acc) buf pos = .ok (arr, pos') →
    (∀ x ∈ acc, P x) → ∀ x ∈ arr, P x
  | 0, acc, buf, pos, arr, pos', h, hacc => by
    simp only [Impl.Message.decodeMany, Primitives.run_pure] at h
    obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
    subst h1
    exact hacc
  | n + 1, acc, buf, pos, arr, pos', h, hacc => by
    simp only [Impl.Message.decodeMany, Primitives.run_bind] at h
    split at h <;> rename_i hp'
    · rename_i x posx
      refine run_decodeMany_mem P p hp n (acc.push x) buf posx arr pos' h ?_
      intro y hy
      rcases Array.mem_push.mp hy with hy | hy
      · exact hacc y hy
      · exact hy ▸ hp hp'
    · exact absurd h (by simp)

def QuestionFromLabels (q : VeriDNS.Spec.Question) : Prop :=
  ∃ ls : Array ByteArray, DomainName.ValidLabels ls ∧
    (Impl.DomainName.labelsToWireFormat ls).size ≤ 255 ∧
    Impl.DomainName.labelsToWireFormat ls = q.qname

theorem run_questionDecode_valid {buf : ByteArray} {pos : Nat}
    {q : VeriDNS.Spec.Question} {pos' : Nat}
    (h : DnsParser.run Question.decode buf pos = .ok (q, pos')) :
    QuestionFromLabels q := by
  simp only [Question.decode, Primitives.run_bind] at h
  split at h <;> rename_i hname
  · rename_i ls posn
    refine ⟨ls, run_decodeName_validLabels hname,
      Proof.DomainName.run_decodeName_le255 _ _ _ _ hname, ?_⟩
    simp only [Primitives.run_bind, Primitives.run_readBV16,
      Primitives.run_pure] at h
    split at h
    · split at h
      · obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        rw [← h1]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem run_resourceRecordDecode_valid {buf : ByteArray} {pos : Nat}
    {rr : VeriDNS.Spec.ResourceRecord} {pos' : Nat}
    (h : DnsParser.run Impl.ResourceRecord.decode buf pos = .ok (rr, pos')) :
    ∃ labels, DomainName.ValidLabels labels
      ∧ Impl.DomainName.labelsToWireFormat labels = rr.name
      ∧ rr.rdlength.toNat = rr.rdata.size
      ∧ (Impl.DomainName.labelsToWireFormat labels).size ≤ 255 := by
  simp only [Impl.ResourceRecord.decode, Primitives.run_bind] at h
  split at h <;> rename_i hname
  case h_2 => exact absurd h (by simp)
  rename_i ls posn
  simp only [Primitives.run_bind, Primitives.run_readBV16, Primitives.run_readBV32,
    Primitives.run_readBytes, Primitives.run_pure] at h
  split at h <;> [skip; exact absurd h (by simp)]
  split at h <;> [skip; exact absurd h (by simp)]
  split at h <;> [skip; exact absurd h (by simp)]
  split at h <;> [skip; exact absurd h (by simp)]
  split at h <;> rename_i hcond
  case h_2 => exact absurd h (by simp)
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
  refine ⟨ls, run_decodeName_validLabels hname, ?_, ?_,
    Proof.DomainName.run_decodeName_le255 _ _ _ _ hname⟩
  · rw [← h1]
  · rw [← h1]
    split at hcond
    · obtain ⟨hext, _⟩ := Prod.mk.inj (Except.ok.inj hcond)
      rename_i hc2
      dsimp only
      rw [← hext, ByteArray.size_extract]; omega
    · exact absurd hcond (by simp)

noncomputable def validQuestionsOfForall {qs : Array VeriDNS.Spec.Question}
    (h : ∀ i : Fin qs.size, QuestionFromLabels qs[i]) : ValidQuestions qs where
  labels i := (h i).choose
  valid i := (h i).choose_spec.1
  le255 i := (h i).choose_spec.2.1
  corresponds i := (h i).choose_spec.2.2

private theorem ba_extract_at_size' (a b : ByteArray) (i j : Nat) :
    (a ++ b).extract (a.size + i) (a.size + j) = b.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have hsd : a.data.size = a.size := ByteArray.size_data
  have h1 : a.data.extract (a.size + i) (a.size + j) = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  simp only [h1, Array.empty_append, hsd]; congr 1 <;> omega

private theorem ba_extract_zero_size' (l rest : ByteArray) :
    (l ++ rest).extract 0 l.size = l := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  simp [ByteArray.size_data, Array.extract_eq_self_of_le]

private theorem ba_extract_mid (a b c : ByteArray) :
    (a ++ b ++ c).extract a.size (a.size + b.size) = b := by
  rw [ba_append_assoc]
  have h := ba_extract_at_size' a (b ++ c) 0 b.size
  rw [Nat.add_zero] at h
  rw [h]
  exact ba_extract_zero_size' b c

theorem appends_writeBV32 (v : BitVec 32) :
    Appends (writeBV32 v)
      (⟨#[UInt8.ofBitVec ((v >>> 24).setWidth 8)]⟩ ++
        (⟨#[UInt8.ofBitVec ((v >>> 16).setWidth 8)]⟩ ++
          (⟨#[UInt8.ofBitVec ((v >>> 8).setWidth 8)]⟩ ++
            ⟨#[UInt8.ofBitVec (v.setWidth 8)]⟩))) :=
  appends_seq (appends_writeUInt8 _)
    (appends_seq (appends_writeUInt8 _)
      (appends_seq (appends_writeUInt8 _) (appends_writeUInt8 _)))

def rrFixed (t c : BitVec 16) (ttl : BitVec 32) (rl : BitVec 16) : ByteArray :=
  ⟨#[UInt8.ofBitVec ((t >>> 8).setWidth 8), UInt8.ofBitVec (t.setWidth 8),
     UInt8.ofBitVec ((c >>> 8).setWidth 8), UInt8.ofBitVec (c.setWidth 8),
     UInt8.ofBitVec ((ttl >>> 24).setWidth 8), UInt8.ofBitVec ((ttl >>> 16).setWidth 8),
     UInt8.ofBitVec ((ttl >>> 8).setWidth 8), UInt8.ofBitVec (ttl.setWidth 8),
     UInt8.ofBitVec ((rl >>> 8).setWidth 8), UInt8.ofBitVec (rl.setWidth 8)]⟩

theorem rrFixed_size (t c : BitVec 16) (ttl : BitVec 32) (rl : BitVec 16) :
    (rrFixed t c ttl rl).size = 10 := rfl

def rrWire (ls : Array ByteArray) (t c : BitVec 16) (ttl : BitVec 32)
    (rdata : ByteArray) : ByteArray :=
  Impl.DomainName.labelsToWireFormat ls
    ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ rdata)

private theorem regroup5 (A B C D E F : ByteArray) :
    A ++ (B ++ (C ++ (D ++ (E ++ F)))) = A ++ ((B ++ (C ++ (D ++ E))) ++ F) := by
  simp only [ba_append_assoc]

theorem rrWire_encoder (name : ByteArray) (t c : BitVec 16) (ttl : BitVec 32)
    (rl : BitVec 16) (rdata : ByteArray) :
    DnsSerializer.runBytes (do
      DnsSerializer.writeBytes name
      writeBV16 t
      writeBV16 c
      writeBV32 ttl
      writeBV16 rl
      DnsSerializer.writeBytes rdata)
    = name ++ (rrFixed t c ttl rl ++ rdata) := by
  refine (appends_runBytes (appends_seq (appends_writeBytes name)
    (appends_seq (appends_writeBV16 t)
      (appends_seq (appends_writeBV16 c)
        (appends_seq (appends_writeBV32 ttl)
          (appends_seq (appends_writeBV16 rl)
            (appends_writeBytes rdata))))))).trans ?_
  rw [regroup5]
  rfl

inductive CanonicalRdata : BitVec 16 → ByteArray → Prop
  | nameType {t : BitVec 16} {rdLs : Array ByteArray}
      (ht : t = 2 ∨ t = 5 ∨ t = 12) (hv : DomainName.ValidLabels rdLs)
      (hle : (Impl.DomainName.labelsToWireFormat rdLs).size ≤ 255) :
      CanonicalRdata t (Impl.DomainName.labelsToWireFormat rdLs)
  | soa {m r : Array ByteArray} {tail : ByteArray}
      (hm : DomainName.ValidLabels m) (hr : DomainName.ValidLabels r)
      (hlem : (Impl.DomainName.labelsToWireFormat m).size ≤ 255)
      (hler : (Impl.DomainName.labelsToWireFormat r).size ≤ 255)
      (htail : tail.size = 20) :
      CanonicalRdata 6 (Impl.DomainName.labelsToWireFormat m
        ++ Impl.DomainName.labelsToWireFormat r ++ tail)
  | prefixedName {t : BitVec 16} {fixedPre : ByteArray} {rdLs : Array ByteArray}
      (ht : (t = 15 ∧ fixedPre.size = 2) ∨ (t = 33 ∧ fixedPre.size = 6))
      (hv : DomainName.ValidLabels rdLs)
      (hle : (Impl.DomainName.labelsToWireFormat rdLs).size ≤ 255) :
      CanonicalRdata t (fixedPre ++ Impl.DomainName.labelsToWireFormat rdLs)
  | other {t : BitVec 16} {rdata : ByteArray}
      (h2 : t ≠ 2) (h5 : t ≠ 5) (h12 : t ≠ 12) (h6 : t ≠ 6)
      (h15 : t ≠ 15) (h33 : t ≠ 33)
      (hsz : rdata.size < 65536) :
      CanonicalRdata t rdata

def CanonicalRR (out : ByteArray) : Prop :=
  ∃ (ls : Array ByteArray) (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray),
    DomainName.ValidLabels ls ∧ (Impl.DomainName.labelsToWireFormat ls).size ≤ 255 ∧
    CanonicalRdata t rdata ∧ out = rrWire ls t c ttl rdata

theorem canonicalRdata_size_lt {t : BitVec 16} {rdata : ByteArray}
    (h : CanonicalRdata t rdata) : rdata.size < 65536 := by
  cases h with
  | nameType ht hv hle => exact Nat.lt_of_le_of_lt hle (by decide)
  | soa hm hr hlem hler htail => simp only [ByteArray.size_append]; omega
  | prefixedName ht hv hle =>
    simp only [ByteArray.size_append]
    rcases ht with ⟨-, hp⟩ | ⟨-, hp⟩ <;> omega
  | other _ _ _ _ _ _ hsz => exact hsz

theorem run_decodeRRCanonical_shape {buf : ByteArray} {pos : Nat}
    {out : ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.Message.decodeRRCanonical buf pos = .ok (out, pos')) :
    CanonicalRR out := by
  simp only [Impl.Message.decodeRRCanonical, Primitives.run_bind] at h
  split at h <;> rename_i hname
  case h_2 => exact absurd h (by simp)
  rename_i ls posn
  have hvls := run_decodeName_validLabels hname
  have hlels := Proof.DomainName.run_decodeName_le255 _ _ _ _ hname

  split at h <;> rename_i hr1
  case h_2 => exact absurd h (by simp)
  rename_i t post
  split at h <;> rename_i hr2
  case h_2 => exact absurd h (by simp)
  rename_i c posc
  split at h <;> rename_i hr3
  case h_2 => exact absurd h (by simp)
  rename_i ttl posttl
  split at h <;> rename_i hr4
  case h_2 => exact absurd h (by simp)
  rename_i rl posrl

  split at h <;> rename_i hcond
  ·
    simp only [Primitives.run_bind, Primitives.run_getPos] at h
    split at h <;> rename_i hrdname
    case h_2 => exact absurd h (by simp)
    rename_i rdLs posrd
    have hvrd := run_decodeName_validLabels hrdname
    split at h <;> rename_i hrdlen
    · simp only [Primitives.run_bind, Primitives.run_pure] at h
      obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨ls, t, c, ttl, _, hvls, hlels,
        .nameType ?_ hvrd (Proof.DomainName.run_decodeName_le255 _ _ _ _ hrdname), ?_⟩
      · have := hcond
        simp only [Bool.or_eq_true, beq_iff_eq] at this
        rcases this with (h2 | h5) | h12
        · exact Or.inl h2
        · exact Or.inr (Or.inl h5)
        · exact Or.inr (Or.inr h12)
      · rw [← h1, rrWire_encoder]
        rfl
    · exact absurd h (by simp)
  · split at h <;> rename_i hcond6
    ·
      simp only [Primitives.run_bind, Primitives.run_getPos] at h
      split at h <;> rename_i hmname
      case h_2 => exact absurd h (by simp)
      rename_i mLs posm
      split at h <;> rename_i hrname
      case h_2 => exact absurd h (by simp)
      rename_i rLs posr
      split at h <;> rename_i htail
      case h_2 => exact absurd h (by simp)
      rename_i tailv postail
      have htsz : tailv.size = 20 := by
        simp only [Primitives.run_readBytes] at htail
        split at htail <;> rename_i hbound
        · obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj htail)
          rw [← h1]
          simp only [ByteArray.size_extract]
          omega
        · exact absurd htail (by simp)
      split at h <;> rename_i hrdlen
      · simp only [Primitives.run_bind, Primitives.run_pure] at h
        obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        have ht6 : t = (6 : BitVec 16) := by simpa using hcond6
        subst ht6
        refine ⟨ls, 6, c, ttl, _, hvls, hlels,
          .soa (run_decodeName_validLabels hmname)
            (run_decodeName_validLabels hrname)
            (Proof.DomainName.run_decodeName_le255 _ _ _ _ hmname)
            (Proof.DomainName.run_decodeName_le255 _ _ _ _ hrname) htsz, ?_⟩
        rw [← h1, rrWire_encoder]
        rfl
      · exact absurd h (by simp)
    · split at h <;> rename_i hcond15
      ·
        simp only [Primitives.run_bind, Primitives.run_getPos] at h
        split at h <;> rename_i hpre
        case h_2 => exact absurd h (by simp)
        rename_i prev pospre
        split at h <;> rename_i hrdname
        case h_2 => exact absurd h (by simp)
        rename_i rdLs posrd
        split at h <;> rename_i hrdlen
        · simp only [Primitives.run_bind, Primitives.run_pure] at h
          obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
          have hvrd := run_decodeName_validLabels hrdname
          have hlerd := Proof.DomainName.run_decodeName_le255 _ _ _ _ hrdname
          simp only [Bool.or_eq_true, beq_iff_eq] at hcond15
          rcases hcond15 with h15 | h33
          · subst h15
            have hpsz : prev.size = 2 := by
              rw [show (if ((15 : BitVec 16) == (15 : BitVec 16)) = true
                then (2 : Nat) else 6) = 2 from by decide] at hpre
              simp only [Primitives.run_readBytes] at hpre
              split at hpre <;> rename_i hbound
              · obtain ⟨hp1, _⟩ := Prod.mk.inj (Except.ok.inj hpre)
                rw [← hp1]
                simp only [ByteArray.size_extract]
                omega
              · exact absurd hpre (by simp)
            refine ⟨ls, 15, c, ttl, _, hvls, hlels,
              .prefixedName (Or.inl ⟨rfl, hpsz⟩) hvrd hlerd, ?_⟩
            rw [← h1, rrWire_encoder]
            rfl
          · subst h33
            have hpsz : prev.size = 6 := by
              rw [show (if ((33 : BitVec 16) == (15 : BitVec 16)) = true
                then (2 : Nat) else 6) = 6 from by decide] at hpre
              simp only [Primitives.run_readBytes] at hpre
              split at hpre <;> rename_i hbound
              · obtain ⟨hp1, _⟩ := Prod.mk.inj (Except.ok.inj hpre)
                rw [← hp1]
                simp only [ByteArray.size_extract]
                omega
              · exact absurd hpre (by simp)
            refine ⟨ls, 33, c, ttl, _, hvls, hlels,
              .prefixedName (Or.inr ⟨rfl, hpsz⟩) hvrd hlerd, ?_⟩
            rw [← h1, rrWire_encoder]
            rfl
        · exact absurd h (by simp)
      ·
        simp only [Primitives.run_bind] at h
        split at h <;> rename_i hrd
        case h_2 => exact absurd h (by simp)
        rename_i rdata posrd
        have hrdsz : rdata.size < 65536 := by
          simp only [Primitives.run_readBytes] at hrd
          split at hrd <;> rename_i hbound
          · obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrd)
            rw [← h1]
            simp only [ByteArray.size_extract]
            have hlt : rl.toNat < 65536 := rl.isLt
            omega
          · exact absurd hrd (by simp)
        simp only [Primitives.run_pure] at h
        obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hcond
        obtain ⟨⟨hne2, hne5⟩, hne12⟩ := hcond
        have hne6 : t ≠ (6 : BitVec 16) := by simpa using hcond6
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hcond15
        obtain ⟨hne15, hne33⟩ := hcond15
        refine ⟨ls, t, c, ttl, rdata, hvls, hlels,
          .other hne2 hne5 hne12 hne6 hne15 hne33 hrdsz, ?_⟩
        rw [← h1, rrWire_encoder]
        rfl

set_option maxHeartbeats 12800000 in

theorem rrWire_frame (ls : Array ByteArray) (hv : DomainName.ValidLabels ls)
    (hle_ls : (Impl.DomainName.labelsToWireFormat ls).size ≤ 255)
    (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray)
    (hrd : CanonicalRdata t rdata) (pre suf : ByteArray) :
    DnsParser.run Impl.Message.decodeRRCanonical
      (pre ++ rrWire ls t c ttl rdata ++ suf) pre.size
    = .ok (rrWire ls t c ttl rdata, pre.size + (rrWire ls t c ttl rdata).size) := by

  have hWsz : (rrWire ls t c ttl rdata).size
      = (Impl.DomainName.labelsToWireFormat ls).size + (10 + rdata.size) := by
    simp [rrWire, ByteArray.size_append, rrFixed_size]

  have hB : pre ++ rrWire ls t c ttl rdata ++ suf
      = pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) := by
    unfold rrWire
    simp only [ba_append_assoc]
  rw [hB]
  have hBsz : (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size
      = pre.size + (Impl.DomainName.labelsToWireFormat ls).size
        + (10 + (rdata.size + suf.size)) := by
    simp only [ByteArray.size_data, ByteArray.size_append, rrFixed_size]

  have hcb1 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 1
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hcb2 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 1
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hcb3 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 3
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hcb4 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 1
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega

  have hkbound : ∀ k : Nat, k < 10 → k < (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
      ++ (rdata ++ suf)).data.size := by
    intro k hk
    simp only [ByteArray.data_append, Array.size_append, ByteArray.size_data,
      rrFixed_size]
    omega
  have hb0 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size]'hlt
      = UInt8.ofBitVec ((t >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 0
      (by omega) _ (hkbound 0 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb1 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 1]'hlt
      = UInt8.ofBitVec (t.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 1
      (by omega) _ (hkbound 1 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb2 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2]'hlt
      = UInt8.ofBitVec ((c >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 2
      (by omega) _ (hkbound 2 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb3 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 1]'hlt
      = UInt8.ofBitVec (c.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 3
      (by omega) _ (hkbound 3 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb4 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2]'hlt
      = UInt8.ofBitVec ((ttl >>> 24).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 4
      (by omega) _ (hkbound 4 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb5 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 1]'hlt
      = UInt8.ofBitVec ((ttl >>> 16).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 5
      (by omega) _ (hkbound 5 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb6 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 2]'hlt
      = UInt8.ofBitVec ((ttl >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 6
      (by omega) _ (hkbound 6 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb7 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 3]'hlt
      = UInt8.ofBitVec (ttl.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 7
      (by omega) _ (hkbound 7 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb8 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4]'hlt
      = UInt8.ofBitVec ((BitVec.ofNat 16 rdata.size >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 8
      (by omega) _ (hkbound 8 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb9 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 1]'hlt
      = UInt8.ofBitVec ((BitVec.ofNat 16 rdata.size).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 9
      (by omega) _ (hkbound 9 (by omega))]
    simp [ByteArray.data_append, rrFixed]

  have h16_id : ∀ v : BitVec 16,
      (UInt8.ofBitVec ((v >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8
      ||| (UInt8.ofBitVec (v.setWidth 8)).toBitVec.setWidth 16 = v :=
    fun v => VeriDNS.Proof.Primitives.reassemble16 v
  have h32_id :
      (UInt8.ofBitVec ((ttl >>> 24).setWidth 8)).toBitVec.setWidth 32 <<< 24
      ||| (UInt8.ofBitVec ((ttl >>> 16).setWidth 8)).toBitVec.setWidth 32 <<< 16
      ||| (UInt8.ofBitVec ((ttl >>> 8).setWidth 8)).toBitVec.setWidth 32 <<< 8
      ||| (UInt8.ofBitVec (ttl.setWidth 8)).toBitVec.setWidth 32 = ttl :=
    VeriDNS.Proof.Primitives.reassemble32 ttl

  simp only [Impl.Message.decodeRRCanonical, Primitives.run_bind,
    Proof.DomainName.decodeName_frame_labels ls hv hle_ls pre
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)),
    Primitives.run_readBV16, Primitives.run_readBV32,
    dif_pos hcb1, dif_pos hcb2, dif_pos hcb3, dif_pos hcb4,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
    h16_id, h32_id]

  cases hrd with
  | @nameType _ rdLs ht hvrd hle_rd =>
    have hcondT : ((t == (2 : BitVec 16) || t == (5 : BitVec 16)
        || t == (12 : BitVec 16)) = true) := by
      rcases ht with rfl | rfl | rfl <;> decide
    rw [if_pos hcondT]
    simp only [Primitives.run_bind, Primitives.run_getPos]
    have hB2 : pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat rdLs).size)
          ++ (Impl.DomainName.labelsToWireFormat rdLs ++ suf))
        = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed t c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat rdLs).size))
          ++ Impl.DomainName.labelsToWireFormat rdLs ++ suf := by
      simp only [ba_append_assoc]
    rw [hB2]
    have hP : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 2
        = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed t c ttl (BitVec.ofNat 16
              (Impl.DomainName.labelsToWireFormat rdLs).size)).size := by
      simp [ByteArray.size_append, rrFixed_size]
    rw [hP]
    rw [Proof.DomainName.decodeName_frame_labels rdLs hvrd hle_rd
      (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ rrFixed t c ttl (BitVec.ofNat 16
          (Impl.DomainName.labelsToWireFormat rdLs).size)) suf]
    simp only []
    split
    · simp only [Primitives.run_bind, Primitives.run_pure]
      rw [rrWire_encoder]
      have hpos : (pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ rrFixed t c ttl (BitVec.ofNat 16
            (Impl.DomainName.labelsToWireFormat rdLs).size)).size
          + (Impl.DomainName.labelsToWireFormat rdLs).size
          = pre.size + (rrWire ls t c ttl
              (Impl.DomainName.labelsToWireFormat rdLs)).size := by
        simp [rrWire, ByteArray.size_append, rrFixed_size]
        omega
      rw [hpos]
      rfl
    · rename_i hc
      refine absurd ?_ hc
      simp only [Nat.add_sub_cancel_left, beq_iff_eq, BitVec.toNat_ofNat]
      have h255 : (Impl.DomainName.labelsToWireFormat rdLs).size ≤ 255 := hle_rd
      omega
  | @soa m r tail hm hr hlem hler htail =>
    rw [if_neg (by decide :
      ¬(((6 : BitVec 16) == (2 : BitVec 16) || (6 : BitVec 16) == (5 : BitVec 16)
        || (6 : BitVec 16) == (12 : BitVec 16)) = true))]
    rw [if_pos (by decide : (((6 : BitVec 16) == (6 : BitVec 16))= true))]
    simp only [Primitives.run_bind, Primitives.run_getPos]

    have hB2 : pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
            ++ Impl.DomainName.labelsToWireFormat r ++ tail).size)
          ++ ((Impl.DomainName.labelsToWireFormat m
            ++ Impl.DomainName.labelsToWireFormat r ++ tail) ++ suf))
        = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m
          ++ (Impl.DomainName.labelsToWireFormat r ++ (tail ++ suf)) := by
      simp only [ba_append_assoc]
    rw [hB2]
    have hP : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 2
        = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size)).size := by
      simp [ByteArray.size_append, rrFixed_size]
    rw [hP]
    rw [Proof.DomainName.decodeName_frame_labels m hm hlem _
      (Impl.DomainName.labelsToWireFormat r ++ (tail ++ suf))]
    simp only []

    have hB3 : (pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
            ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m
          ++ (Impl.DomainName.labelsToWireFormat r ++ (tail ++ suf))
        = ((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m)
          ++ Impl.DomainName.labelsToWireFormat r ++ (tail ++ suf) := by
      simp only [ba_append_assoc]
    rw [hB3]
    have hP2 : (pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
            ++ Impl.DomainName.labelsToWireFormat r ++ tail).size)).size
          + (Impl.DomainName.labelsToWireFormat m).size
        = ((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m).size := by
      simp [ByteArray.size_append]
    rw [hP2]
    rw [Proof.DomainName.decodeName_frame_labels r hr hler _ (tail ++ suf)]
    simp only [Primitives.run_readBytes]

    have hB4 : ((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m)
          ++ Impl.DomainName.labelsToWireFormat r ++ (tail ++ suf)
        = (((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m)
          ++ Impl.DomainName.labelsToWireFormat r)
          ++ tail ++ suf := by
      simp only [ba_append_assoc]
    rw [hB4]
    have hP3 : ((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m).size
          + (Impl.DomainName.labelsToWireFormat r).size
        = (((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m)
          ++ Impl.DomainName.labelsToWireFormat r).size := by
      simp [ByteArray.size_append]
    rw [hP3]
    rw [if_pos (by
      simp only [ByteArray.size_append]
      omega)]
    rw [show (((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m)
          ++ Impl.DomainName.labelsToWireFormat r).size + 20
        = (((pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
          ++ Impl.DomainName.labelsToWireFormat m)
          ++ Impl.DomainName.labelsToWireFormat r).size + tail.size from by omega]
    rw [ba_extract_mid]
    simp only []
    split
    · simp only [Primitives.run_bind, Primitives.run_pure]
      rw [rrWire_encoder]
      have hpos : (((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 6 c ttl (BitVec.ofNat 16 (Impl.DomainName.labelsToWireFormat m
                ++ Impl.DomainName.labelsToWireFormat r ++ tail).size))
            ++ Impl.DomainName.labelsToWireFormat m)
            ++ Impl.DomainName.labelsToWireFormat r).size + tail.size
          = pre.size + (rrWire ls 6 c ttl (Impl.DomainName.labelsToWireFormat m
              ++ Impl.DomainName.labelsToWireFormat r ++ tail)).size := by
        simp [rrWire, ByteArray.size_append, rrFixed_size]
        omega
      rw [hpos]
      rfl
    · rename_i hc
      refine absurd ?_ hc
      simp only [beq_iff_eq, BitVec.toNat_ofNat, ByteArray.size_append, rrFixed_size]
      have hm255 : (Impl.DomainName.labelsToWireFormat m).size ≤ 255 := hlem
      have hr255 : (Impl.DomainName.labelsToWireFormat r).size ≤ 255 := hler
      omega
  | @prefixedName _ fixedPre rdLs ht hvrd hle_rd =>
    rcases ht with ⟨rfl, hpre⟩ | ⟨rfl, hpre⟩
    ·
      rw [if_neg (by decide : ¬(((15 : BitVec 16) == (2 : BitVec 16)
          || (15 : BitVec 16) == (5 : BitVec 16)
          || (15 : BitVec 16) == (12 : BitVec 16)) = true))]
      rw [if_neg (by decide : ¬(((15 : BitVec 16) == (6 : BitVec 16)) = true))]
      rw [if_pos (by decide : (((15 : BitVec 16) == (15 : BitVec 16)
          || (15 : BitVec 16) == (33 : BitVec 16)) = true))]
      simp only [Primitives.run_bind, Primitives.run_getPos]
      rw [show (if ((15 : BitVec 16) == (15 : BitVec 16)) = true
          then (2 : Nat) else 6) = 2 from by decide]
      simp only [Primitives.run_readBytes]
      have hB2 : pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ (rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)
            ++ ((fixedPre ++ Impl.DomainName.labelsToWireFormat rdLs) ++ suf))
          = (pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre ++ (Impl.DomainName.labelsToWireFormat rdLs ++ suf) := by
        simp only [ba_append_assoc]
      rw [hB2]
      have hP : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 2
          = (pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size := by
        simp [ByteArray.size_append, rrFixed_size]
      rw [hP]
      rw [if_pos (by
        simp only [ByteArray.size_append]
        omega)]
      rw [show (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size + 2
          = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size + fixedPre.size
          from by omega]
      rw [ba_extract_mid]
      simp only []
      have hB3 : (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre ++ (Impl.DomainName.labelsToWireFormat rdLs ++ suf)
          = ((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre) ++ Impl.DomainName.labelsToWireFormat rdLs ++ suf := by
        simp only [ba_append_assoc]
      rw [hB3]
      have hP2 : (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size + fixedPre.size
          = ((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre).size := by
        simp [ByteArray.size_append]
      rw [hP2]
      rw [Proof.DomainName.decodeName_frame_labels rdLs hvrd hle_rd _ suf]
      simp only []
      split
      · simp only [Primitives.run_bind, Primitives.run_pure]
        rw [rrWire_encoder]
        have hpos : ((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 15 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
              ++ fixedPre).size + (Impl.DomainName.labelsToWireFormat rdLs).size
            = pre.size + (rrWire ls 15 c ttl (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs)).size := by
          simp [rrWire, ByteArray.size_append, rrFixed_size]
          omega
        rw [hpos]
        rfl
      · rename_i hc
        refine absurd ?_ hc
        simp only [beq_iff_eq, BitVec.toNat_ofNat, ByteArray.size_append, rrFixed_size]
        have h255 : (Impl.DomainName.labelsToWireFormat rdLs).size ≤ 255 := hle_rd
        omega
    ·
      rw [if_neg (by decide : ¬(((33 : BitVec 16) == (2 : BitVec 16)
          || (33 : BitVec 16) == (5 : BitVec 16)
          || (33 : BitVec 16) == (12 : BitVec 16)) = true))]
      rw [if_neg (by decide : ¬(((33 : BitVec 16) == (6 : BitVec 16)) = true))]
      rw [if_pos (by decide : (((33 : BitVec 16) == (15 : BitVec 16)
          || (33 : BitVec 16) == (33 : BitVec 16)) = true))]
      simp only [Primitives.run_bind, Primitives.run_getPos]
      rw [show (if ((33 : BitVec 16) == (15 : BitVec 16)) = true
          then (2 : Nat) else 6) = 6 from by decide]
      simp only [Primitives.run_readBytes]
      have hB2 : pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ (rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)
            ++ ((fixedPre ++ Impl.DomainName.labelsToWireFormat rdLs) ++ suf))
          = (pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre ++ (Impl.DomainName.labelsToWireFormat rdLs ++ suf) := by
        simp only [ba_append_assoc]
      rw [hB2]
      have hP : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 2
          = (pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size := by
        simp [ByteArray.size_append, rrFixed_size]
      rw [hP]
      rw [if_pos (by
        simp only [ByteArray.size_append]
        omega)]
      rw [show (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size + 6
          = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size + fixedPre.size
          from by omega]
      rw [ba_extract_mid]
      simp only []
      have hB3 : (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre ++ (Impl.DomainName.labelsToWireFormat rdLs ++ suf)
          = ((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre) ++ Impl.DomainName.labelsToWireFormat rdLs ++ suf := by
        simp only [ba_append_assoc]
      rw [hB3]
      have hP2 : (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
              ++ Impl.DomainName.labelsToWireFormat rdLs).size)).size + fixedPre.size
          = ((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
            ++ fixedPre).size := by
        simp [ByteArray.size_append]
      rw [hP2]
      rw [Proof.DomainName.decodeName_frame_labels rdLs hvrd hle_rd _ suf]
      simp only []
      split
      · simp only [Primitives.run_bind, Primitives.run_pure]
        rw [rrWire_encoder]
        have hpos : ((pre ++ Impl.DomainName.labelsToWireFormat ls
              ++ rrFixed 33 c ttl (BitVec.ofNat 16 (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs).size))
              ++ fixedPre).size + (Impl.DomainName.labelsToWireFormat rdLs).size
            = pre.size + (rrWire ls 33 c ttl (fixedPre
                ++ Impl.DomainName.labelsToWireFormat rdLs)).size := by
          simp [rrWire, ByteArray.size_append, rrFixed_size]
          omega
        rw [hpos]
        rfl
      · rename_i hc
        refine absurd ?_ hc
        simp only [beq_iff_eq, BitVec.toNat_ofNat, ByteArray.size_append, rrFixed_size]
        have h255 : (Impl.DomainName.labelsToWireFormat rdLs).size ≤ 255 := hle_rd
        omega
  | @other _ _ h2 h5 h12 h6 h15 h33 hsz =>
    rw [if_neg (by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or]
      exact ⟨⟨h2, h5⟩, h12⟩)]
    rw [if_neg (by simp only [beq_iff_eq]; exact h6)]
    rw [if_neg (by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or]
      exact ⟨h15, h33⟩)]
    have hlen : (BitVec.ofNat 16 rdata.size).toNat = rdata.size := by
      rw [BitVec.toNat_ofNat]
      have h216 : 2 ^ 16 = 65536 := rfl
      omega
    rw [hlen]
    simp only [Primitives.run_bind, Primitives.run_readBytes]
    have hB2 : pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))
        = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed t c ttl (BitVec.ofNat 16 rdata.size))
          ++ rdata ++ suf := by
      simp only [ba_append_assoc]
    rw [hB2]
    have hP : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 2
        = (pre ++ Impl.DomainName.labelsToWireFormat ls
            ++ rrFixed t c ttl (BitVec.ofNat 16 rdata.size)).size := by
      simp [ByteArray.size_append, rrFixed_size]
    rw [hP]
    rw [if_pos (by
      simp only [ByteArray.size_append]
      omega)]
    rw [ba_extract_mid]
    simp only [Primitives.run_pure]
    rw [rrWire_encoder]
    have hpos : (pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ rrFixed t c ttl (BitVec.ofNat 16 rdata.size)).size + rdata.size
        = pre.size + (rrWire ls t c ttl rdata).size := by
      simp [rrWire, ByteArray.size_append, rrFixed_size]
      omega
    rw [hpos]
    rfl

theorem run_resourceRecordDecode_rrWire (ls : Array ByteArray) (hv : DomainName.ValidLabels ls)
    (hle_ls : (Impl.DomainName.labelsToWireFormat ls).size ≤ 255)
    (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray) (hsz : rdata.size < 65536)
    (pre suf : ByteArray) :
    DnsParser.run Impl.ResourceRecord.decode (pre ++ rrWire ls t c ttl rdata ++ suf) pre.size
    = .ok ({ name := Impl.DomainName.labelsToWireFormat ls, type := t, «class» := c, ttl := ttl,
             rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata },
           pre.size + (rrWire ls t c ttl rdata).size) := by
  have hWsz : (rrWire ls t c ttl rdata).size
      = (Impl.DomainName.labelsToWireFormat ls).size + (10 + rdata.size) := by
    simp [rrWire, ByteArray.size_append, rrFixed_size]
  have hB : pre ++ rrWire ls t c ttl rdata ++ suf
      = pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) := by
    unfold rrWire
    simp only [ba_append_assoc]
  rw [hB]
  have hBsz : (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size
      = pre.size + (Impl.DomainName.labelsToWireFormat ls).size
        + (10 + (rdata.size + suf.size)) := by
    simp only [ByteArray.size_data, ByteArray.size_append, rrFixed_size]
  have hcb1 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 1
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hcb2 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 1
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hcb3 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 3
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hcb4 : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 1
      < (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))).data.size := by
    rw [hBsz]; omega
  have hkbound : ∀ k : Nat, k < 10 → k < (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
      ++ (rdata ++ suf)).data.size := by
    intro k hk
    simp only [ByteArray.data_append, Array.size_append, ByteArray.size_data,
      rrFixed_size]
    omega
  have hb0 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size]'hlt
      = UInt8.ofBitVec ((t >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 0
      (by omega) _ (hkbound 0 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb1 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 1]'hlt
      = UInt8.ofBitVec (t.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 1
      (by omega) _ (hkbound 1 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb2 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2]'hlt
      = UInt8.ofBitVec ((c >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 2
      (by omega) _ (hkbound 2 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb3 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 1]'hlt
      = UInt8.ofBitVec (c.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 3
      (by omega) _ (hkbound 3 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb4 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2]'hlt
      = UInt8.ofBitVec ((ttl >>> 24).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 4
      (by omega) _ (hkbound 4 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb5 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 1]'hlt
      = UInt8.ofBitVec ((ttl >>> 16).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 5
      (by omega) _ (hkbound 5 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb6 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 2]'hlt
      = UInt8.ofBitVec ((ttl >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 6
      (by omega) _ (hkbound 6 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb7 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 3]'hlt
      = UInt8.ofBitVec (ttl.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 7
      (by omega) _ (hkbound 7 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb8 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4]'hlt
      = UInt8.ofBitVec ((BitVec.ofNat 16 rdata.size >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 8
      (by omega) _ (hkbound 8 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have hb9 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size)
        ++ (rdata ++ suf))).data[pre.size
          + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 1]'hlt
      = UInt8.ofBitVec ((BitVec.ofNat 16 rdata.size).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat ls)
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)) _ 9
      (by omega) _ (hkbound 9 (by omega))]
    simp [ByteArray.data_append, rrFixed]
  have h16_id : ∀ v : BitVec 16,
      (UInt8.ofBitVec ((v >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8
      ||| (UInt8.ofBitVec (v.setWidth 8)).toBitVec.setWidth 16 = v :=
    fun v => VeriDNS.Proof.Primitives.reassemble16 v
  have h32_id :
      (UInt8.ofBitVec ((ttl >>> 24).setWidth 8)).toBitVec.setWidth 32 <<< 24
      ||| (UInt8.ofBitVec ((ttl >>> 16).setWidth 8)).toBitVec.setWidth 32 <<< 16
      ||| (UInt8.ofBitVec ((ttl >>> 8).setWidth 8)).toBitVec.setWidth 32 <<< 8
      ||| (UInt8.ofBitVec (ttl.setWidth 8)).toBitVec.setWidth 32 = ttl :=
    VeriDNS.Proof.Primitives.reassemble32 ttl
  simp only [Impl.ResourceRecord.decode, Primitives.run_bind,
    Proof.DomainName.decodeName_frame_labels ls hv hle_ls pre
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)),
    Primitives.run_readBV16, Primitives.run_readBV32,
    dif_pos hcb1, dif_pos hcb2, dif_pos hcb3, dif_pos hcb4,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
    h16_id, h32_id]
  have hlen : (BitVec.ofNat 16 rdata.size).toNat = rdata.size := by
    rw [BitVec.toNat_ofNat]
    have h216 : 2 ^ 16 = 65536 := rfl
    omega
  rw [hlen]
  simp only [Primitives.run_bind, Primitives.run_readBytes]
  have hB2 : pre ++ Impl.DomainName.labelsToWireFormat ls
      ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf))
      = (pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ rrFixed t c ttl (BitVec.ofNat 16 rdata.size))
        ++ rdata ++ suf := by
    simp only [ba_append_assoc]
  rw [hB2]
  have hP : pre.size + (Impl.DomainName.labelsToWireFormat ls).size + 2 + 2 + 4 + 2
      = (pre ++ Impl.DomainName.labelsToWireFormat ls
          ++ rrFixed t c ttl (BitVec.ofNat 16 rdata.size)).size := by
    simp [ByteArray.size_append, rrFixed_size]
  rw [hP]
  rw [if_pos (by
    simp only [ByteArray.size_append]
    omega)]
  rw [ba_extract_mid]
  simp only [Primitives.run_pure]
  have hpos : (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ rrFixed t c ttl (BitVec.ofNat 16 rdata.size)).size + rdata.size
      = pre.size + (rrWire ls t c ttl rdata).size := by
    simp [rrWire, ByteArray.size_append, rrFixed_size]
    omega
  rw [hpos]

theorem run_decodeRRCanonical_canonical {buf : ByteArray} {pos : Nat}
    {out : ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.Message.decodeRRCanonical buf pos = .ok (out, pos')) :
    ∀ (pre suf : ByteArray),
      DnsParser.run Impl.Message.decodeRRCanonical (pre ++ out ++ suf) pre.size
      = .ok (out, pre.size + out.size) := by
  obtain ⟨ls, t, c, ttl, rdata, hvls, hlels, hrd, rfl⟩ := run_decodeRRCanonical_shape h
  intro pre suf
  exact rrWire_frame ls hvls hlels t c ttl rdata hrd pre suf

def validRRBytesOfMem {rrs : Array ByteArray}
    (h : ∀ b ∈ rrs, ∀ (pre suf : ByteArray),
      DnsParser.run Impl.Message.decodeRRCanonical (pre ++ b ++ suf) pre.size
      = .ok (b, pre.size + b.size)) : ValidRRBytes rrs where
  canonical i pre suf := h rrs[i] (rrs.getElem_mem i.isLt) pre suf

theorem decode_encode_of_decode {buf : ByteArray} {msg : Format}
    (h : Impl.Message.decode buf = .ok msg) :
    Impl.Message.decode (Impl.Message.encode msg) = .ok msg := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = msg := by
    injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  have hnone : ∀ {α : Type} (P : α → Prop) (x : α), x ∈ (#[] : Array α) → P x := by
    intro α P x hx
    simp at hx
  refine decode_encode _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_

  · have h : hdr.qdcount.toNat = qs.size := by
      simpa using (run_decodeMany_size Question.decode _ _ _ _ _ _ hqs).symm
    exact h
  · have h : hdr.ancount.toNat = ans.size := by
      simpa using (run_decodeMany_size Impl.Message.decodeRRCanonical _ _ _ _ _ _ hans).symm
    exact h
  · have h : hdr.nscount.toNat = auth.size := by
      simpa using (run_decodeMany_size Impl.Message.decodeRRCanonical _ _ _ _ _ _ hauth).symm
    exact h
  · have h : hdr.arcount.toNat = add.size := by
      simpa using (run_decodeMany_size Impl.Message.decodeRRCanonical _ _ _ _ _ _ hadd).symm
    exact h
  · exact validQuestionsOfForall (fun i =>
      run_decodeMany_mem QuestionFromLabels Question.decode
        (fun hq => run_questionDecode_valid hq) _ _ _ _ _ _ hqs
        (hnone _) _ (qs.getElem_mem i.isLt))
  · exact validRRBytesOfMem (fun b hb =>
      run_decodeMany_mem _ Impl.Message.decodeRRCanonical
        (fun hb' => run_decodeRRCanonical_canonical hb') _ _ _ _ _ _ hans
        (hnone _) b hb)
  · exact validRRBytesOfMem (fun b hb =>
      run_decodeMany_mem _ Impl.Message.decodeRRCanonical
        (fun hb' => run_decodeRRCanonical_canonical hb') _ _ _ _ _ _ hauth
        (hnone _) b hb)
  · exact validRRBytesOfMem (fun b hb =>
      run_decodeMany_mem _ Impl.Message.decodeRRCanonical
        (fun hb' => run_decodeRRCanonical_canonical hb') _ _ _ _ _ _ hadd
        (hnone _) b hb)

theorem decodeRRCanonical_parseRaw {buf : ByteArray} {pos pos' : Nat} {b : ByteArray}
    (h : DnsParser.run Impl.Message.decodeRRCanonical buf pos = .ok (b, pos')) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b ≠ none := by
  unfold Impl.Message.decodeRRCanonical at h
  rw [Primitives.run_bind] at h
  generalize hdn : DnsParser.run DomainName.decodeName buf pos = rdn at h
  rcases rdn with _ | ⟨labels, p1⟩
  · simp at h
  simp only [] at h
  rw [Primitives.run_bind] at h
  generalize hrt : DnsParser.run readBV16 buf p1 = rrt at h
  rcases rrt with _ | ⟨rt, p2⟩
  · simp at h
  simp only [] at h
  rw [Primitives.run_bind] at h
  generalize hct : DnsParser.run readBV16 buf p2 = rct at h
  rcases rct with _ | ⟨ct, p3⟩
  · simp at h
  simp only [] at h
  rw [Primitives.run_bind] at h
  generalize htt : DnsParser.run readBV32 buf p3 = rtt at h
  rcases rtt with _ | ⟨tt, p4⟩
  · simp at h
  simp only [] at h
  rw [Primitives.run_bind] at h
  generalize hrl : DnsParser.run readBV16 buf p4 = rrl at h
  rcases rrl with _ | ⟨rl, p5⟩
  · simp at h
  simp only [] at h

  have hv := run_decodeName_validLabels hdn
  have hle255 := Proof.DomainName.run_decodeName_le255 _ _ _ _ hdn
  have finish : ∀ (rdata : ByteArray),
      DnsSerializer.runBytes (ResourceRecord.encode
        { name := DomainName.labelsToWireFormat labels, type := rt, «class» := ct, ttl := tt,
          rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata }) = b →
      RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b ≠ none := by
    intro rdata hb
    rw [← hb]
    obtain ⟨x, hx⟩ := VeriDNS.Proof.ResourceRecord.decode_succeeds_of_encode
      { name := DomainName.labelsToWireFormat labels, type := rt, «class» := ct, ttl := tt,
        rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata }
      labels hv hle255 rfl (by simp only [BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
    change (match DnsParser.run ResourceRecord.decode _ with
      | .ok (rr, _) => some rr | .error _ => none) ≠ none
    rw [hx]; simp

  split at h
  ·
    rw [Primitives.run_bind] at h
    simp only [Primitives.run_getPos] at h
    rw [Primitives.run_bind] at h
    generalize DnsParser.run DomainName.decodeName buf p5 = rd2 at h
    rcases rd2 with _ | ⟨rdl, q⟩
    · simp at h
    simp only [Primitives.run_bind, Primitives.run_getPos] at h
    split at h
    · simp only [Primitives.run_bind, Primitives.run_pure] at h
      obtain ⟨hb, _⟩ := Prod.mk.inj (Except.ok.inj h)
      exact finish _ hb
    · simp at h
  · split at h
    ·
      rw [Primitives.run_bind] at h
      simp only [Primitives.run_getPos] at h
      rw [Primitives.run_bind] at h
      generalize DnsParser.run DomainName.decodeName buf p5 = rm at h
      rcases rm with _ | ⟨ml, q1⟩
      · simp at h
      simp only [] at h
      rw [Primitives.run_bind] at h
      generalize DnsParser.run DomainName.decodeName buf q1 = rn at h
      rcases rn with _ | ⟨nl, q2⟩
      · simp at h
      simp only [] at h
      rw [Primitives.run_bind] at h
      generalize DnsParser.run (DnsParser.readBytes 20) buf q2 = rtl at h
      rcases rtl with _ | ⟨tl, q3⟩
      · simp at h
      simp only [Primitives.run_bind, Primitives.run_getPos] at h
      split at h
      · simp only [Primitives.run_bind, Primitives.run_pure] at h
        obtain ⟨hb, _⟩ := Prod.mk.inj (Except.ok.inj h)
        exact finish _ hb
      · simp at h
    · split at h
      ·
        rw [Primitives.run_bind] at h
        simp only [Primitives.run_getPos] at h
        rw [Primitives.run_bind] at h
        split at h <;> rename_i hpre
        case h_2 => exact absurd h (by simp)
        rename_i fp q1
        rw [Primitives.run_bind] at h
        split at h <;> rename_i hrdn
        case h_2 => exact absurd h (by simp)
        rename_i rdl q2
        simp only [Primitives.run_bind, Primitives.run_getPos] at h
        split at h
        · simp only [Primitives.run_bind, Primitives.run_pure] at h
          obtain ⟨hb, _⟩ := Prod.mk.inj (Except.ok.inj h)
          exact finish _ hb
        · simp at h
      ·
        rw [Primitives.run_bind] at h
        generalize DnsParser.run (DnsParser.readBytes rl.toNat) buf p5 = ry at h
        rcases ry with _ | ⟨y, q⟩
        · simp at h
        simp only [Primitives.run_pure] at h
        obtain ⟨hb, _⟩ := Prod.mk.inj (Except.ok.inj h)
        exact finish _ hb

theorem decode_answer_parseRaw {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    ∀ rr ∈ f.answer, RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rr ≠ none := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  exact run_decodeMany_mem (fun rr => RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rr ≠ none)
    Impl.Message.decodeRRCanonical (fun hp => decodeRRCanonical_parseRaw hp)
    _ #[] buf posq ans posa hans (by simp)

theorem decode_authority_parseRaw {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    ∀ rr ∈ f.authority, RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rr ≠ none := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  exact run_decodeMany_mem (fun rr => RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rr ≠ none)
    Impl.Message.decodeRRCanonical (fun hp => decodeRRCanonical_parseRaw hp)
    _ #[] buf posa auth posn hauth (by simp)

theorem decode_additional_parseRaw {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    ∀ rr ∈ f.additional, RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rr ≠ none := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  exact run_decodeMany_mem (fun rr => RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rr ≠ none)
    Impl.Message.decodeRRCanonical (fun hp => decodeRRCanonical_parseRaw hp)
    _ #[] buf posn add posd hadd (by simp)

theorem decode_answer_canonicalRR {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    ∀ rr ∈ f.answer, CanonicalRR rr := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  exact run_decodeMany_mem CanonicalRR
    Impl.Message.decodeRRCanonical (fun hp => run_decodeRRCanonical_shape hp)
    _ #[] buf posq ans posa hans (by simp)

theorem decode_authority_canonicalRR {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    ∀ rr ∈ f.authority, CanonicalRR rr := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  exact run_decodeMany_mem CanonicalRR
    Impl.Message.decodeRRCanonical (fun hp => run_decodeRRCanonical_shape hp)
    _ #[] buf posa auth posn hauth (by simp)

theorem decode_additional_canonicalRR {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    ∀ rr ∈ f.additional, CanonicalRR rr := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  exact run_decodeMany_mem CanonicalRR
    Impl.Message.decodeRRCanonical (fun hp => run_decodeRRCanonical_shape hp)
    _ #[] buf posn add posd hadd (by simp)

theorem decode_answer_size {buf : ByteArray} {f : VeriDNS.Spec.Format}
    (h : Impl.Message.decode buf = .ok f) :
    f.answer.size = f.header.ancount.toNat := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = f := by injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  simpa using run_decodeMany_size Impl.Message.decodeRRCanonical _ #[] buf posq ans posa hans

end VeriDNS.Proof.Message
