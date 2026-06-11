import VeriDNS.Proof.Message

/-!
Decode-side validity: the hypotheses of `decode_encode` hold for every
message `decode` accepts.

`decode_encode` (Proof/Message.lean) proves `decode (encode msg) = .ok msg`
under four count hypotheses plus `ValidQuestions` / `ValidRRBytes`. Those
hypotheses were stated as the invariants `decode` maintains — this file
PROVES that:

- `decodeNameAux` only ever produces labels of length 1–63
  (`decodeNameAux_validLabels`), so parsed questions carry valid label
  decompositions (`run_questionDecode_valid`);
- `decodeMany` returns exactly as many items as requested
  (`run_decodeMany_size`), so the header counts match the section sizes;
- every byte string `decodeRRCanonical` produces is CANONICAL — embedded
  at any position it re-parses to exactly itself (`rrWire_frame` via
  `run_decodeRRCanonical_shape`), giving `ValidRRBytes`;
- therefore anything `decode` accepts survives an encode/decode roundtrip
  end-to-end (`decode_encode_of_decode`), with no side conditions.
-/

namespace VeriDNS.Proof.Message

open VeriDNS.Impl
open VeriDNS.Spec

-- ============================================================
-- decodeNameAux output validity: labels are 1–63 bytes
-- ============================================================

private theorem uint8_toNat_pos_of_ne_zero {b : UInt8} (h : ¬(b == 0) = true) :
    0 < b.toNat := by
  have hne : b ≠ 0 := by simpa using h
  cases hn : b.toNat with
  | zero =>
    exact absurd (by simpa using UInt8.toNat_inj.mp (by simpa using hn)) hne
  | succ n => omega

/-- Every label a successful `decodeNameAux` run produces has length 1–63:
    the zero byte terminates, lengths over 63 error out, and pointer hops
    recurse. (The companion `decodeNameAux_adversarial_bounds` bounds count
    and end position; this lemma adds the positivity needed for
    `ValidLabels`.) -/
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
      · -- null terminator: no labels
        obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        subst h1
        intro l hl
        simp at hl
      · split at h
        · -- compression pointer: labels come from the recursive decode
          split at h
          · split at h <;> rename_i hrec
            · rename_i ls' ep'
              obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
              subst h1
              intro l hl
              exact ih _ _ _ _ hrec l hl
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · -- label branch
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

/-- Parser-level corollary: `decodeName` only returns valid label arrays. -/
theorem run_decodeName_validLabels {buf : ByteArray} {pos : Nat}
    {labels : Array ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.DomainName.decodeName buf pos = .ok (labels, pos')) :
    DomainName.ValidLabels labels := by
  have hmem : ∀ l ∈ labels, 0 < l.size ∧ l.size ≤ 63 := by
    simp only [Impl.DomainName.decodeName, Primitives.run_bind,
      Primitives.run_getBuffer, Primitives.run_getPos] at h
    split at h <;> rename_i haux
    · rename_i ls' ep'
      simp only [Primitives.run_bind, Primitives.run_setPos,
        Primitives.run_pure] at h
      obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
      subst h1
      exact decodeNameAux_validLabels _ _ _ _ _ _ haux
    · exact absurd h (by simp [Primitives.run_fail])
  intro i hi
  exact hmem labels[i] (labels.getElem_mem hi)

-- ============================================================
-- decodeMany: size and element invariants
-- ============================================================

/-- `decodeMany p n acc` returns exactly `acc.size + n` items. -/
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

/-- Every element `decodeMany p n acc` returns either was in `acc` or is an
    output of `p`. -/
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

-- ============================================================
-- Question validity from decode
-- ============================================================

/-- A question whose qname is the wire format of SOME valid label array —
    the per-element form of `ValidQuestions`. -/
def QuestionFromLabels (q : VeriDNS.Spec.Question) : Prop :=
  ∃ ls : Array ByteArray, DomainName.ValidLabels ls ∧
    Impl.DomainName.labelsToWireFormat ls = q.qname

/-- Every question `Question.decode` produces carries a valid label
    decomposition. -/
theorem run_questionDecode_valid {buf : ByteArray} {pos : Nat}
    {q : VeriDNS.Spec.Question} {pos' : Nat}
    (h : DnsParser.run Question.decode buf pos = .ok (q, pos')) :
    QuestionFromLabels q := by
  simp only [Question.decode, Primitives.run_bind] at h
  split at h <;> rename_i hname
  · rename_i ls posn
    refine ⟨ls, run_decodeName_validLabels hname, ?_⟩
    simp only [Primitives.run_bind, Primitives.run_readBV16,
      Primitives.run_pure] at h
    split at h
    · split at h
      · obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
        rw [← h1]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Package the per-element witnesses into the `ValidQuestions` record
    (the function form `decode_encode` consumes). -/
noncomputable def validQuestionsOfForall {qs : Array VeriDNS.Spec.Question}
    (h : ∀ i : Fin qs.size, QuestionFromLabels qs[i]) : ValidQuestions qs where
  labels i := (h i).choose
  valid i := (h i).choose_spec.1
  corresponds i := (h i).choose_spec.2

-- ============================================================
-- Canonical RR bytes: shape of decodeRRCanonical's output
-- ============================================================

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

/-- Extract exactly the middle segment of a three-part concatenation. -/
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

/-- The 10 fixed bytes of a canonical RR after its owner name:
    TYPE (2) + CLASS (2) + TTL (4) + RDLENGTH (2), big-endian. -/
def rrFixed (t c : BitVec 16) (ttl : BitVec 32) (rl : BitVec 16) : ByteArray :=
  ⟨#[UInt8.ofBitVec ((t >>> 8).setWidth 8), UInt8.ofBitVec (t.setWidth 8),
     UInt8.ofBitVec ((c >>> 8).setWidth 8), UInt8.ofBitVec (c.setWidth 8),
     UInt8.ofBitVec ((ttl >>> 24).setWidth 8), UInt8.ofBitVec ((ttl >>> 16).setWidth 8),
     UInt8.ofBitVec ((ttl >>> 8).setWidth 8), UInt8.ofBitVec (ttl.setWidth 8),
     UInt8.ofBitVec ((rl >>> 8).setWidth 8), UInt8.ofBitVec (rl.setWidth 8)]⟩

theorem rrFixed_size (t c : BitVec 16) (ttl : BitVec 32) (rl : BitVec 16) :
    (rrFixed t c ttl rl).size = 10 := rfl

/-- Canonical wire bytes of an RR: owner name (as wire-format labels),
    the 10 fixed bytes (with RDLENGTH = the rdata's true size), rdata. -/
def rrWire (ls : Array ByteArray) (t c : BitVec 16) (ttl : BitVec 32)
    (rdata : ByteArray) : ByteArray :=
  Impl.DomainName.labelsToWireFormat ls
    ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ rdata)

private theorem regroup5 (A B C D E F : ByteArray) :
    A ++ (B ++ (C ++ (D ++ (E ++ F)))) = A ++ ((B ++ (C ++ (D ++ E))) ++ F) := by
  simp only [ba_append_assoc]

/-- The re-encoder inside `decodeRRCanonical` produces exactly the
    `rrWire` shape. -/
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

/-- The rdata shapes `decodeRRCanonical` can produce, by RR type:
    decompressed name (NS/CNAME/PTR), decompressed SOA names + 20-byte
    tail, or raw bytes (RDLENGTH-delimited, hence < 2^16). -/
inductive CanonicalRdata : BitVec 16 → ByteArray → Prop
  | nameType {t : BitVec 16} {rdLs : Array ByteArray}
      (ht : t = 2 ∨ t = 5 ∨ t = 12) (hv : DomainName.ValidLabels rdLs) :
      CanonicalRdata t (Impl.DomainName.labelsToWireFormat rdLs)
  | soa {m r : Array ByteArray} {tail : ByteArray}
      (hm : DomainName.ValidLabels m) (hr : DomainName.ValidLabels r)
      (htail : tail.size = 20) :
      CanonicalRdata 6 (Impl.DomainName.labelsToWireFormat m
        ++ Impl.DomainName.labelsToWireFormat r ++ tail)
  | other {t : BitVec 16} {rdata : ByteArray}
      (h2 : t ≠ 2) (h5 : t ≠ 5) (h12 : t ≠ 12) (h6 : t ≠ 6)
      (hsz : rdata.size < 65536) :
      CanonicalRdata t rdata

/-- A byte string `decodeRRCanonical` could have produced. -/
def CanonicalRR (out : ByteArray) : Prop :=
  ∃ (ls : Array ByteArray) (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray),
    DomainName.ValidLabels ls ∧ CanonicalRdata t rdata ∧
    out = rrWire ls t c ttl rdata

/-- Whatever `decodeRRCanonical` accepts, its output has the canonical
    shape: a valid owner name, the 10 fixed bytes with true RDLENGTH, and
    branch-shaped rdata. -/
theorem run_decodeRRCanonical_shape {buf : ByteArray} {pos : Nat}
    {out : ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.Message.decodeRRCanonical buf pos = .ok (out, pos')) :
    CanonicalRR out := by
  simp only [Impl.Message.decodeRRCanonical, Primitives.run_bind] at h
  split at h <;> rename_i hname
  case h_2 => exact absurd h (by simp)
  rename_i ls posn
  have hvls := run_decodeName_validLabels hname
  -- the four fixed-field reads: the values are existential witnesses, so
  -- only their SUCCESS matters here
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
  -- branch on rdata shape
  split at h <;> rename_i hcond
  · -- NS/CNAME/PTR: rdata is a decompressed name
    simp only [Primitives.run_bind] at h
    split at h <;> rename_i hrdname
    case h_2 => exact absurd h (by simp)
    rename_i rdLs posrd
    have hvrd := run_decodeName_validLabels hrdname
    simp only [Primitives.run_pure] at h
    obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
    refine ⟨ls, t, c, ttl, _, hvls, .nameType ?_ hvrd, ?_⟩
    · have := hcond
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with (h2 | h5) | h12
      · exact Or.inl h2
      · exact Or.inr (Or.inl h5)
      · exact Or.inr (Or.inr h12)
    · rw [← h1, rrWire_encoder]
      rfl
  · split at h <;> rename_i hcond6
    · -- SOA: two decompressed names + 20-byte tail
      simp only [Primitives.run_bind] at h
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
      simp only [Primitives.run_pure] at h
      obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
      have ht6 : t = (6 : BitVec 16) := by simpa using hcond6
      subst ht6
      refine ⟨ls, 6, c, ttl, _, hvls,
        .soa (run_decodeName_validLabels hmname)
          (run_decodeName_validLabels hrname) htsz, ?_⟩
      rw [← h1, rrWire_encoder]
      rfl
    · -- default: RDLENGTH-delimited raw bytes
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
      refine ⟨ls, t, c, ttl, rdata, hvls,
        .other hne2 hne5 hne12 hne6 hrdsz, ?_⟩
      rw [← h1, rrWire_encoder]
      rfl

-- ============================================================
-- Frame theorem: canonical RR bytes re-parse to exactly themselves
-- ============================================================

set_option maxHeartbeats 12800000 in
/-- Re-parsing canonical RR bytes embedded at any position reproduces
    exactly those bytes and consumes exactly them — the `ValidRRBytes`
    frame property, proven for everything `decodeRRCanonical` outputs. -/
theorem rrWire_frame (ls : Array ByteArray) (hv : DomainName.ValidLabels ls)
    (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray)
    (hrd : CanonicalRdata t rdata) (pre suf : ByteArray) :
    DnsParser.run Impl.Message.decodeRRCanonical
      (pre ++ rrWire ls t c ttl rdata ++ suf) pre.size
    = .ok (rrWire ls t c ttl rdata, pre.size + (rrWire ls t c ttl rdata).size) := by
  -- abbreviations (definitionally transparent)
  have hWsz : (rrWire ls t c ttl rdata).size
      = (Impl.DomainName.labelsToWireFormat ls).size + (10 + rdata.size) := by
    simp [rrWire, ByteArray.size_append, rrFixed_size]
  -- normalize the buffer so the name is a frame segment
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
  -- bounds for the four fixed-field reads
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
  -- the ten fixed bytes: byte k of the rrFixed segment, as literals
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
  -- the read values are exactly t, c, ttl, and the RDLENGTH
  have h16_id : ∀ v : BitVec 16,
      (UInt8.ofBitVec ((v >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8
      ||| (UInt8.ofBitVec (v.setWidth 8)).toBitVec.setWidth 16 = v := by
    intro v
    bv_decide
  have h32_id :
      (UInt8.ofBitVec ((ttl >>> 24).setWidth 8)).toBitVec.setWidth 32 <<< 24
      ||| (UInt8.ofBitVec ((ttl >>> 16).setWidth 8)).toBitVec.setWidth 32 <<< 16
      ||| (UInt8.ofBitVec ((ttl >>> 8).setWidth 8)).toBitVec.setWidth 32 <<< 8
      ||| (UInt8.ofBitVec (ttl.setWidth 8)).toBitVec.setWidth 32 = ttl := by
    bv_decide
  -- one pass: unfold the parser chain, discharge the four bounds, resolve
  -- the ten byte accesses, and collapse the read values to t/c/ttl/rdlen
  simp only [Impl.Message.decodeRRCanonical, Primitives.run_bind,
    Proof.DomainName.decodeName_frame_labels ls hv pre
      (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ (rdata ++ suf)),
    Primitives.run_readBV16, Primitives.run_readBV32,
    dif_pos hcb1, dif_pos hcb2, dif_pos hcb3, dif_pos hcb4,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
    h16_id, h32_id]
  -- rdata branches
  cases hrd with
  | @nameType _ rdLs ht hvrd =>
    have hcondT : ((t == (2 : BitVec 16) || t == (5 : BitVec 16)
        || t == (12 : BitVec 16)) = true) := by
      rcases ht with rfl | rfl | rfl <;> decide
    rw [if_pos hcondT]
    simp only [Primitives.run_bind]
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
    rw [Proof.DomainName.decodeName_frame_labels rdLs hvrd
      (pre ++ Impl.DomainName.labelsToWireFormat ls
        ++ rrFixed t c ttl (BitVec.ofNat 16
          (Impl.DomainName.labelsToWireFormat rdLs).size)) suf]
    simp only [Primitives.run_pure]
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
  | @soa m r tail hm hr htail =>
    rw [if_neg (by decide :
      ¬(((6 : BitVec 16) == (2 : BitVec 16) || (6 : BitVec 16) == (5 : BitVec 16)
        || (6 : BitVec 16) == (12 : BitVec 16)) = true))]
    rw [if_pos (by decide : (((6 : BitVec 16) == (6 : BitVec 16))= true))]
    simp only [Primitives.run_bind]
    -- first name (MNAME)
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
    rw [Proof.DomainName.decodeName_frame_labels m hm _
      (Impl.DomainName.labelsToWireFormat r ++ (tail ++ suf))]
    simp only [Primitives.run_bind]
    -- second name (RNAME)
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
    rw [Proof.DomainName.decodeName_frame_labels r hr _ (tail ++ suf)]
    simp only [Primitives.run_bind, Primitives.run_readBytes]
    -- the 20-byte tail
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
    simp only [Primitives.run_pure]
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
  | @other _ _ h2 h5 h12 h6 hsz =>
    rw [if_neg (by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or]
      exact ⟨⟨h2, h5⟩, h12⟩)]
    rw [if_neg (by simp only [beq_iff_eq]; exact h6)]
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

-- ============================================================
-- Assembly: decode discharges every decode_encode hypothesis
-- ============================================================

/-- Everything `decodeRRCanonical` outputs is canonical: embedded at any
    position, it re-parses to exactly itself. -/
theorem run_decodeRRCanonical_canonical {buf : ByteArray} {pos : Nat}
    {out : ByteArray} {pos' : Nat}
    (h : DnsParser.run Impl.Message.decodeRRCanonical buf pos = .ok (out, pos')) :
    ∀ (pre suf : ByteArray),
      DnsParser.run Impl.Message.decodeRRCanonical (pre ++ out ++ suf) pre.size
      = .ok (out, pre.size + out.size) := by
  obtain ⟨ls, t, c, ttl, rdata, hvls, hrd, rfl⟩ := run_decodeRRCanonical_shape h
  intro pre suf
  exact rrWire_frame ls hvls t c ttl rdata hrd pre suf

/-- Build `ValidRRBytes` from the per-element frame property. -/
def validRRBytesOfMem {rrs : Array ByteArray}
    (h : ∀ b ∈ rrs, ∀ (pre suf : ByteArray),
      DnsParser.run Impl.Message.decodeRRCanonical (pre ++ b ++ suf) pre.size
      = .ok (b, pre.size + b.size)) : ValidRRBytes rrs where
  canonical i pre suf := h rrs[i] (rrs.getElem_mem i.isLt) pre suf

/-- Anything `decode` accepts survives the encode/decode roundtrip
    END-TO-END: every hypothesis of `decode_encode` — section counts,
    question label validity, RR byte canonicity — is established by the
    decode run itself, with no side conditions. -/
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
  -- the four generated count predicates unfold definitionally to the
  -- decodeMany size equations
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

end VeriDNS.Proof.Message
