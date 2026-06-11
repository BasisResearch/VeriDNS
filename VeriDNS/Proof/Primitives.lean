import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Parsec
import Std.Tactic.BVDecide
import Batteries.Data.ByteArray

namespace VeriDNS.Proof.Primitives

open VeriDNS.Impl

-- ============================================================
-- Test: concrete roundtrip works
-- ============================================================

example : DnsParser.run DnsParser.readUInt8 ⟨#[42]⟩ 0 = .ok (42, 1) := by native_decide

-- ============================================================
-- Serializer exec reductions (definitional)
-- ============================================================

@[simp] theorem exec_writeUInt8 (init : ByteArray) (b : UInt8) :
    (StateT.run (DnsSerializer.writeUInt8 b) init).2 = init.push b := by rfl

@[simp] theorem exec_writeBytes (init : ByteArray) (bs : ByteArray) :
    (StateT.run (DnsSerializer.writeBytes bs) init).2 = init ++ bs := by rfl

-- ============================================================
-- Parser equational lemmas (all by rfl thanks to new type)
-- ============================================================

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

-- ============================================================
-- Monadic bind/pure reduction for DnsParser.run
-- ============================================================

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

-- ============================================================
-- Write-then-read roundtrip lemmas (BV16/BV32/BV8)
-- These are the key infrastructure: encoding then decoding
-- recovers the original value.
--
-- Proof pattern:
--   1. unfold definitions to ByteArray.push + dite
--   2. dsimp to reduce StateM monad operations
--   3. simp to resolve Array.getElem_push and sizes
--   4. decide to resolve Nat comparisons to True/False
--   5. dite_true/dite_false to collapse if-then-else
--   6. bv_decide for the BitVec identity
-- ============================================================

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
  congr 1; simp only [Prod.mk.injEq]; exact ⟨by bv_decide, trivial⟩

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
  congr 1; simp only [Prod.mk.injEq]; exact ⟨by bv_decide, trivial⟩

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

-- ============================================================
-- UInt16 write-then-read roundtrip
-- ============================================================

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
  -- UInt16 roundtrip: ((v >>> 8).toUInt8.toUInt16 <<< 8) ||| (v &&& 0xFF).toUInt8.toUInt16 = v
  -- Prove the UInt16 byte roundtrip via native_decide on a BitVec helper
  suffices h : ∀ bv : BitVec 16,
      (({ toBitVec := bv } : UInt16) >>> 8).toUInt8.toUInt16 <<< 8 |||
      (({ toBitVec := bv } : UInt16) &&& 255).toUInt8.toUInt16 =
      ({ toBitVec := bv } : UInt16) from h v.toBitVec
  native_decide

-- ============================================================
-- Standalone UInt16 byte roundtrip
-- ============================================================

@[simp] theorem uint16_byte_roundtrip (v : UInt16) :
    (v >>> 8).toUInt8.toUInt16 <<< 8 ||| (v &&& 255).toUInt8.toUInt16 = v := by
  suffices ∀ bv : BitVec 16,
      (({ toBitVec := bv } : UInt16) >>> 8).toUInt8.toUInt16 <<< 8 |||
      (({ toBitVec := bv } : UInt16) &&& 255).toUInt8.toUInt16 =
      ({ toBitVec := bv } : UInt16) from this v.toBitVec
  native_decide

-- ============================================================
-- BitVec 16 byte split/merge identity
-- ============================================================

theorem bv16_byte_identity (v : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 8 (v >>> 8)) <<< 8 |||
    BitVec.setWidth 16 (BitVec.setWidth 8 v) = v := by
  bv_decide

-- ============================================================
-- Serializer exec reductions (state transitions)
-- ============================================================

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

-- ============================================================
-- Serializer sequential execution (StateM decomposition)
-- ============================================================

@[simp] theorem stateM_run_seq {α : Type} (s1 : DnsSerializer Unit) (s2 : DnsSerializer α)
    (init : ByteArray) :
    StateT.run (s1 >>= fun _ => s2) init =
    StateT.run s2 (StateT.run s1 init).2 := by rfl

@[simp] theorem stateM_run_seq_snd (s1 : DnsSerializer Unit) (s2 : DnsSerializer Unit)
    (init : ByteArray) :
    (StateT.run (s1 >>= fun _ => s2) init).2 =
    (StateT.run s2 (StateT.run s1 init).2).2 := by rfl

-- ============================================================
-- Serializer run/runBytes reductions
-- ============================================================

@[simp] theorem runBytes_seq (s1 : DnsSerializer Unit) (s2 : DnsSerializer Unit) :
    DnsSerializer.runBytes (s1 >>= fun _ => s2) =
    (StateT.run s2 (StateT.run s1 ByteArray.empty).2).2 := by rfl

@[simp] theorem runBytes_writeUInt8 (b : UInt8) :
    DnsSerializer.runBytes (DnsSerializer.writeUInt8 b) = ByteArray.empty.push b := by rfl

@[simp] theorem runBytes_writeBytes (bs : ByteArray) :
    DnsSerializer.runBytes (DnsSerializer.writeBytes bs) = ByteArray.empty ++ bs := by rfl

-- ============================================================
-- Composite read helpers (reduce proof size for multi-field types)
-- ============================================================

/-- Read a BV32 at a known position with known byte values. -/
theorem readBV32_at (buf : ByteArray) (pos : Nat) (v : BitVec 32)
    (hb : pos + 3 < buf.data.size)
    (h0 : buf.data[pos]'(by omega) = UInt8.ofBitVec ((v >>> 24).setWidth 8))
    (h1 : buf.data[pos + 1]'(by omega) = UInt8.ofBitVec ((v >>> 16).setWidth 8))
    (h2 : buf.data[pos + 2]'(by omega) = UInt8.ofBitVec ((v >>> 8).setWidth 8))
    (h3 : buf.data[pos + 3] = UInt8.ofBitVec (v.setWidth 8)) :
    DnsParser.run readBV32 buf pos = .ok (v, pos + 4) := by
  simp only [run_readBV32, dif_pos hb, h0, h1, h2, h3]
  congr 1; congr 1
  exact by bv_decide

/-- Access byte at offset `a.size + b.size + k` in `(a ++ b ++ c).data` gives `c.data[k]`. -/
theorem getElem_append3_right (a b c : ByteArray) (k : Nat)
    (h : a.size + b.size + k < (a ++ b ++ c).data.size)
    (hk : k < c.data.size) :
    (a ++ b ++ c).data[a.size + b.size + k]'h = c.data[k] := by
  simp only [ByteArray.data_append] at h ⊢
  rw [Array.getElem_append_right (by simp [ByteArray.size_data, Array.size_append])]
  congr 1
  simp [Array.size_append, ByteArray.size_data]

/-- Access byte at arbitrary index `idx` in `(a ++ b ++ c).data`,
    where `idx = a.size + b.size + k` (proved by omega). -/
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
