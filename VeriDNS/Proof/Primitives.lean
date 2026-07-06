import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Parsec
import Std.Tactic.BVDecide
import Batteries.Data.ByteArray

namespace VeriDNS.Proof.Primitives

open VeriDNS.Impl

set_option linter.unusedSimpArgs false in
/-- **16-bit byte-split round-trip, axiom-clean (`getLsbD` bit-blast, no `bv_decide` native LRAT axiom).**
    Splitting a `BitVec 16` into its two bytes (high `x >>> 8`, low `x`) and reassembling via the decode
    path (`setWidth 16` of each byte, high one `<<< 8`, OR'd) recovers `x`. Replaces `bv_decide` in the
    codec value round-trips (type/class/rdlength/qtype/qclass) — shrinks the TCB toward kernel+FFI-only. -/
theorem reassemble16 (x : BitVec 16) :
    (UInt8.ofBitVec ((x >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (x.setWidth 8)).toBitVec.setWidth 16 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt8.toBitVec_ofBitVec, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 8
  · simp only [h, hi, decide_true, Bool.true_and, Bool.and_true, decide_false,
      Nat.not_le.mpr h, Bool.not_true, Bool.false_and, Bool.false_or]
  · rw [show 8 + (i - 8) = i from by omega]
    have c2 : i - 8 < 16 := by omega
    have c3 : i - 8 < 8 := by omega
    simp only [h, hi, c2, c3, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.not_false, Bool.and_self, Bool.false_and, Bool.or_false]

/-- **32-bit byte-split round-trip, axiom-clean** (the `ttl` analogue of `reassemble16`; four bytes). -/
theorem reassemble32 (x : BitVec 32) :
    (UInt8.ofBitVec ((x >>> 24).setWidth 8)).toBitVec.setWidth 32 <<< 24 |||
      (UInt8.ofBitVec ((x >>> 16).setWidth 8)).toBitVec.setWidth 32 <<< 16 |||
        (UInt8.ofBitVec ((x >>> 8).setWidth 8)).toBitVec.setWidth 32 <<< 8 |||
          (UInt8.ofBitVec (x.setWidth 8)).toBitVec.setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt8.toBitVec_ofBitVec, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  rcases Nat.lt_or_ge i 8 with h | h
  · have a1 : ¬ (16:Nat) ≤ i := by omega
    have a2 : ¬ (24:Nat) ≤ i := by omega
    simp [hi, h, Nat.not_le.mpr h, a1, a2]
  rcases Nat.lt_or_ge i 16 with h2 | h2
  · rw [show 8 + (i - 8) = i from by omega]
    have a1 : i < 24 := by omega
    have a2 : ¬ i < 8 := by omega
    have a3 : i - 8 < 32 := by omega
    have a4 : i - 8 < 8 := by omega
    simp [hi, a1, h2, a2, a3, a4]
  rcases Nat.lt_or_ge i 24 with h3 | h3
  · rw [show 16 + (i - 16) = i from by omega]
    have a2 : ¬ i < 16 := by omega
    have a2b : ¬ i < 8 := by omega
    have a3 : i - 16 < 32 := by omega
    have a4 : i - 16 < 8 := by omega
    have a5 : ¬ i - 8 < 8 := by omega
    simp [hi, h3, a2, a2b, a3, a4, a5]
  · rw [show 24 + (i - 24) = i from by omega]
    have a1 : ¬ i < 24 := by omega
    have a2 : ¬ i < 16 := by omega
    have a2b : ¬ i < 8 := by omega
    have a3 : i - 24 < 32 := by omega
    have a4 : i - 24 < 8 := by omega
    have a5 : ¬ i - 8 < 8 := by omega
    have a6 : ¬ i - 16 < 8 := by omega
    simp [hi, a1, a2, a2b, a3, a4, a5, a6]

/-- `getLsbD` of the 16-bit `0xFF` mask: true exactly on the low byte. Axiom-clean; for `uint16_split`. -/
theorem getLsbD_255_16 (i : Nat) : (255#16).getLsbD i = decide (i < 8) := by
  rw [show (255#16) = BitVec.ofNat 16 (2^8 - 1) from rfl,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp [h, (by omega : i < 16)]
  · simp only [decide_eq_false (show ¬ i < 8 from by omega), Bool.and_false]

/-- **UInt16 byte-split round-trip, axiom-clean** (`getLsbD` bit-blast; the UInt16-op version of
    `reassemble16`, with `&&& 255` mask and BitVec-amount shifts reduced to `Nat`-8 by `rfl`). -/
theorem uint16_split (bv : BitVec 16) :
    (({ toBitVec := bv } : UInt16) >>> 8).toUInt8.toUInt16 <<< 8 |||
      (({ toBitVec := bv } : UInt16) &&& 255).toUInt8.toUInt16 = ({ toBitVec := bv } : UInt16) := by
  apply UInt16.toBitVec_inj.mp
  simp only [UInt16.toBitVec_or, UInt16.toBitVec_shiftLeft, UInt16.toBitVec_shiftRight,
    UInt16.toBitVec_toUInt8, UInt8.toBitVec_toUInt16, UInt16.toBitVec_and, UInt16.toBitVec_ofNat,
    BitVec.setWidth_setWidth,
    show ∀ (y : BitVec 16), y <<< (8#16 % 16) = y <<< (8 : Nat) from fun _ => rfl,
    show bv >>> (8#16 % 16) = bv >>> (8 : Nat) from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, getLsbD_255_16]
  by_cases h : i < 8
  · simp [h, hi, Nat.not_le.mpr h]
  · rw [show 8 + (i - 8) = i from by omega]
    simp [h, hi, (show i - 8 < 8 from by omega), (show i - 8 < 16 from by omega)]

example : DnsParser.run DnsParser.readUInt8 ⟨#[42]⟩ 0 = .ok (42, 1) := by decide

@[simp] theorem exec_writeUInt8 (init : ByteArray) (b : UInt8) :
    (StateT.run (DnsSerializer.writeUInt8 b) init).2 = init.push b := by rfl

@[simp] theorem exec_writeBytes (init : ByteArray) (bs : ByteArray) :
    (StateT.run (DnsSerializer.writeBytes bs) init).2 = init ++ bs := by rfl

@[simp] theorem run_readUInt8 (buf : ByteArray) (pos : Nat) :
    DnsParser.run DnsParser.readUInt8 buf pos =
    if h : pos < buf.data.size then .ok (buf.data[pos], pos + 1)
    else .error "readUInt8: unexpected end of input" := by rfl

@[simp] theorem run_readUInt16BE (buf : ByteArray) (pos : Nat) :
    DnsParser.run DnsParser.readUInt16BE buf pos =
    if h : pos + 1 < buf.data.size then
      .ok (((buf.data[pos]'(by omega)).toUInt16 <<< 8) ||| (buf.data[pos + 1]).toUInt16, pos + 2)
    else .error "readUInt16BE: unexpected end of input" := by rfl

@[simp] theorem run_readUInt32BE (buf : ByteArray) (pos : Nat) :
    DnsParser.run DnsParser.readUInt32BE buf pos =
    if h : pos + 3 < buf.data.size then
      .ok (((buf.data[pos]'(by omega)).toUInt32 <<< 24) |||
           ((buf.data[pos + 1]'(by omega)).toUInt32 <<< 16) |||
           ((buf.data[pos + 2]'(by omega)).toUInt32 <<< 8) |||
           (buf.data[pos + 3]).toUInt32, pos + 4)
    else .error "readUInt32BE: unexpected end of input" := by rfl

@[simp] theorem run_readBytes (buf : ByteArray) (pos n : Nat) :
    DnsParser.run (DnsParser.readBytes n) buf pos =
    if pos + n ≤ buf.size then .ok (buf.extract pos (pos + n), pos + n)
    else .error s!"readBytes: need {n} bytes at offset {pos}, have {buf.size - pos}" := by rfl

@[simp] theorem run_readBV16 (buf : ByteArray) (pos : Nat) :
    DnsParser.run readBV16 buf pos =
    if h : pos + 1 < buf.data.size then
      .ok ((buf.data[pos]'(by omega)).toBitVec.setWidth 16 <<< 8 |||
           (buf.data[pos + 1]).toBitVec.setWidth 16, pos + 2)
    else .error "readBV16: unexpected end of input" := by rfl

@[simp] theorem run_readBV32 (buf : ByteArray) (pos : Nat) :
    DnsParser.run readBV32 buf pos =
    if h : pos + 3 < buf.data.size then
      .ok ((buf.data[pos]'(by omega)).toBitVec.setWidth 32 <<< 24 |||
           (buf.data[pos + 1]'(by omega)).toBitVec.setWidth 32 <<< 16 |||
           (buf.data[pos + 2]'(by omega)).toBitVec.setWidth 32 <<< 8 |||
           (buf.data[pos + 3]).toBitVec.setWidth 32, pos + 4)
    else .error "readBV32: unexpected end of input" := by rfl

@[simp] theorem run_readBV8 (buf : ByteArray) (pos : Nat) :
    DnsParser.run readBV8 buf pos =
    if h : pos < buf.data.size then .ok ((buf.data[pos]).toBitVec, pos + 1)
    else .error "readBV8: unexpected end of input" := by rfl

@[simp] theorem run_getPos (buf : ByteArray) (pos : Nat) :
    DnsParser.run DnsParser.getPos buf pos = .ok (pos, pos) := by rfl

@[simp] theorem run_setPos (buf : ByteArray) (pos newPos : Nat) :
    DnsParser.run (DnsParser.setPos newPos) buf pos = .ok ((), newPos) := by rfl

@[simp] theorem run_getBuffer (buf : ByteArray) (pos : Nat) :
    DnsParser.run DnsParser.getBuffer buf pos = .ok (buf, pos) := by rfl

@[simp] theorem run_fail {α : Type} (buf : ByteArray) (pos : Nat) (msg : String) :
    DnsParser.run (DnsParser.fail msg : DnsParser α) buf pos = .error msg := by rfl

@[simp] theorem run_pure {α : Type} (buf : ByteArray) (pos : Nat) (a : α) :
    DnsParser.run (pure a : DnsParser α) buf pos = .ok (a, pos) := by rfl

@[simp] theorem run_bind {α β : Type} (buf : ByteArray) (pos : Nat)
    (p : DnsParser α) (f : α → DnsParser β) :
    DnsParser.run (p >>= f) buf pos =
    match DnsParser.run p buf pos with
    | .ok (a, pos') => DnsParser.run (f a) buf pos'
    | .error e => .error e := by
  simp [DnsParser.run, bind, ReaderT.bind, StateT.bind, Except.bind]
  cases p buf pos with
  | ok val => rfl
  | error e => rfl

@[simp] theorem run_map {α β : Type} (buf : ByteArray) (pos : Nat)
    (f : α → β) (p : DnsParser α) :
    DnsParser.run (f <$> p) buf pos =
    match DnsParser.run p buf pos with
    | .ok (a, pos') => .ok (f a, pos')
    | .error e => .error e := by
  simp [DnsParser.run, Functor.map, StateT.map, Except.map]
  cases p buf pos with
  | ok val => cases val; rfl
  | error e => rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
@[simp] theorem readBV16_writeBV16 (v : BitVec 16) :
    DnsParser.run readBV16 (DnsSerializer.runBytes (writeBV16 v)) 0 =
    .ok (v, 2) := by
  unfold DnsParser.run readBV16 DnsSerializer.runBytes writeBV16 DnsSerializer.writeUInt8
  dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
              bind, StateT.bind, pure, StateT.pure, StateT.run,
              EStateM.modifyGet, EStateM.bind, EStateM.pure]
  simp only [ByteArray.data_push, Array.getElem_push, ByteArray.empty, Array.size,
             Array.toList_push, List.length_append, List.length_cons,
             ByteArray.emptyWithCapacity, List.length_nil]
  simp (config := { decide := true }) only []
  simp only [dite_true, dite_false]
  congr 1; simp only [Prod.mk.injEq]; exact ⟨reassemble16 v, trivial⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
@[simp] theorem readBV32_writeBV32 (v : BitVec 32) :
    DnsParser.run readBV32 (DnsSerializer.runBytes (writeBV32 v)) 0 =
    .ok (v, 4) := by
  unfold DnsParser.run readBV32 DnsSerializer.runBytes writeBV32 DnsSerializer.writeUInt8
  dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
              bind, StateT.bind, pure, StateT.pure, StateT.run,
              EStateM.modifyGet, EStateM.bind, EStateM.pure]
  simp only [ByteArray.data_push, Array.getElem_push, ByteArray.empty, Array.size,
             Array.toList_push, List.length_append, List.length_cons,
             ByteArray.emptyWithCapacity, List.length_nil]
  simp (config := { decide := true }) only []
  simp only [dite_true, dite_false]
  congr 1; simp only [Prod.mk.injEq]; exact ⟨reassemble32 v, trivial⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
@[simp] theorem readBV8_writeBV8 (v : BitVec 8) :
    DnsParser.run readBV8 (DnsSerializer.runBytes (writeBV8 v)) 0 =
    .ok (v, 1) := by
  unfold DnsParser.run readBV8 DnsSerializer.runBytes writeBV8 DnsSerializer.writeUInt8
  dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
              bind, StateT.bind, pure, StateT.pure, StateT.run,
              EStateM.modifyGet, EStateM.bind, EStateM.pure]
  simp only [ByteArray.data_push, Array.getElem_push, ByteArray.empty, Array.size,
             Array.toList_push, List.length_append, List.length_cons,
             ByteArray.emptyWithCapacity, List.length_nil]
  simp (config := { decide := true }) only []
  simp only [dite_true, dite_false]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
@[simp] theorem readUInt16BE_writeUInt16BE (v : UInt16) :
    DnsParser.run DnsParser.readUInt16BE
      (DnsSerializer.runBytes (DnsSerializer.writeUInt16BE v)) 0 =
    .ok (v, 2) := by
  unfold DnsParser.run DnsParser.readUInt16BE DnsSerializer.runBytes
  unfold DnsSerializer.writeUInt16BE DnsSerializer.writeUInt8
  dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
              bind, StateT.bind, pure, StateT.pure, StateT.run,
              EStateM.modifyGet, EStateM.bind, EStateM.pure]
  simp only [ByteArray.data_push, Array.getElem_push, ByteArray.empty, Array.size,
             Array.toList_push, List.length_append, List.length_cons,
             ByteArray.emptyWithCapacity, List.length_nil]
  simp (config := { decide := true }) only []
  simp only [dite_true, dite_false]
  congr 1; simp only [Prod.mk.injEq]
  refine ⟨?_, trivial⟩

  suffices h : ∀ bv : BitVec 16,
      (({ toBitVec := bv } : UInt16) >>> 8).toUInt8.toUInt16 <<< 8 |||
      (({ toBitVec := bv } : UInt16) &&& 255).toUInt8.toUInt16 =
      ({ toBitVec := bv } : UInt16) from h v.toBitVec
  exact uint16_split

@[simp] theorem uint16_byte_roundtrip (v : UInt16) :
    (v >>> 8).toUInt8.toUInt16 <<< 8 ||| (v &&& 255).toUInt8.toUInt16 = v := by
  suffices ∀ bv : BitVec 16,
      (({ toBitVec := bv } : UInt16) >>> 8).toUInt8.toUInt16 <<< 8 |||
      (({ toBitVec := bv } : UInt16) &&& 255).toUInt8.toUInt16 =
      ({ toBitVec := bv } : UInt16) from this v.toBitVec
  exact uint16_split

theorem bv16_byte_identity (v : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 8 (v >>> 8)) <<< 8 |||
    BitVec.setWidth 16 (BitVec.setWidth 8 v) = v :=
  reassemble16 v

@[simp] theorem exec_writeBV16 (init : ByteArray) (v : BitVec 16) :
    (StateT.run (writeBV16 v) init).2 =
    (init.push (UInt8.ofBitVec ((v >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (v.setWidth 8)) := by rfl

@[simp] theorem exec_writeBV32 (init : ByteArray) (v : BitVec 32) :
    (StateT.run (writeBV32 v) init).2 =
    (((init.push (UInt8.ofBitVec ((v >>> 24).setWidth 8))).push
      (UInt8.ofBitVec ((v >>> 16).setWidth 8))).push
      (UInt8.ofBitVec ((v >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (v.setWidth 8)) := by rfl

@[simp] theorem exec_writeBV8 (init : ByteArray) (v : BitVec 8) :
    (StateT.run (writeBV8 v) init).2 = init.push (UInt8.ofBitVec v) := by rfl

@[simp] theorem exec_writeUInt16BE (init : ByteArray) (v : UInt16) :
    (StateT.run (DnsSerializer.writeUInt16BE v) init).2 =
    (init.push (v >>> 8).toUInt8).push (v &&& 0xFF).toUInt8 := by rfl

@[simp] theorem stateM_run_seq {α : Type} (s1 : DnsSerializer Unit) (s2 : DnsSerializer α)
    (init : ByteArray) :
    StateT.run (s1 >>= fun _ => s2) init =
    StateT.run s2 (StateT.run s1 init).2 := by rfl

@[simp] theorem stateM_run_seq_snd (s1 : DnsSerializer Unit) (s2 : DnsSerializer Unit)
    (init : ByteArray) :
    (StateT.run (s1 >>= fun _ => s2) init).2 =
    (StateT.run s2 (StateT.run s1 init).2).2 := by rfl

@[simp] theorem runBytes_seq (s1 : DnsSerializer Unit) (s2 : DnsSerializer Unit) :
    DnsSerializer.runBytes (s1 >>= fun _ => s2) =
    (StateT.run s2 (StateT.run s1 ByteArray.empty).2).2 := by rfl

@[simp] theorem runBytes_writeUInt8 (b : UInt8) :
    DnsSerializer.runBytes (DnsSerializer.writeUInt8 b) = ByteArray.empty.push b := by rfl

@[simp] theorem runBytes_writeBytes (bs : ByteArray) :
    DnsSerializer.runBytes (DnsSerializer.writeBytes bs) = ByteArray.empty ++ bs := by rfl

theorem readBV32_at (buf : ByteArray) (pos : Nat) (v : BitVec 32)
    (hb : pos + 3 < buf.data.size)
    (h0 : buf.data[pos]'(by omega) = UInt8.ofBitVec ((v >>> 24).setWidth 8))
    (h1 : buf.data[pos + 1]'(by omega) = UInt8.ofBitVec ((v >>> 16).setWidth 8))
    (h2 : buf.data[pos + 2]'(by omega) = UInt8.ofBitVec ((v >>> 8).setWidth 8))
    (h3 : buf.data[pos + 3] = UInt8.ofBitVec (v.setWidth 8)) :
    DnsParser.run readBV32 buf pos = .ok (v, pos + 4) := by
  simp only [run_readBV32, dif_pos hb, h0, h1, h2, h3]
  congr 1; congr 1
  exact reassemble32 v

theorem getElem_append3_right (a b c : ByteArray) (k : Nat)
    (h : a.size + b.size + k < (a ++ b ++ c).data.size)
    (hk : k < c.data.size) :
    (a ++ b ++ c).data[a.size + b.size + k]'h = c.data[k] := by
  simp only [ByteArray.data_append] at h ⊢
  rw [Array.getElem_append_right (by simp [ByteArray.size_data, Array.size_append])]
  congr 1
  simp [Array.size_append, ByteArray.size_data]

theorem byte_at_suffix (a b c : ByteArray) (idx k : Nat)
    (hidx : idx = a.size + b.size + k)
    (h : idx < (a ++ b ++ c).data.size)
    (hk : k < c.data.size) :
    (a ++ b ++ c).data[idx]'h = c.data[k] := by
  simp only [ByteArray.data_append] at h ⊢
  rw [Array.getElem_append_right (by simp [Array.size_append, ByteArray.size_data]; omega)]
  congr 1
  simp [Array.size_append, ByteArray.size_data]; omega

end VeriDNS.Proof.Primitives
