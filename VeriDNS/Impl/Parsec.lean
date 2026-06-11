import Batteries

namespace VeriDNS.Impl

-- ============================================================
-- DnsParser monad: ReaderT ByteArray over StateT Nat (Except String)
--
-- This formulation returns Except String (α × Nat), putting the
-- state INSIDE the Except. This means DnsParser.run is just
-- function application, making equational lemmas provable by rfl.
-- ============================================================

abbrev DnsParser (α : Type) :=
  ReaderT ByteArray (StateT Nat (Except String)) α

namespace DnsParser

def run {α : Type} (p : DnsParser α) (buf : ByteArray) (pos : Nat := 0)
    : Except String (α × Nat) :=
  p buf pos

def getPos : DnsParser Nat :=
  fun _buf pos => .ok (pos, pos)

def setPos (newPos : Nat) : DnsParser Unit :=
  fun _buf _pos => .ok ((), newPos)

def getBuffer : DnsParser ByteArray :=
  fun buf pos => .ok (buf, pos)

def fail {α : Type} (msg : String) : DnsParser α :=
  fun _buf _pos => .error msg

-- ============================================================
-- Byte-level read primitives (plain functions, no do notation)
-- ============================================================

def readUInt8 : DnsParser UInt8 :=
  fun buf pos =>
    if h : pos < buf.data.size then .ok (buf.data[pos], pos + 1)
    else .error "readUInt8: unexpected end of input"

def peekUInt8 : DnsParser UInt8 :=
  fun buf pos =>
    if h : pos < buf.data.size then .ok (buf.data[pos], pos)
    else .error "peekUInt8: unexpected end of input"

def readUInt16BE : DnsParser UInt16 :=
  fun buf pos =>
    if h : pos + 1 < buf.data.size then
      let hi : UInt16 := (buf.data[pos]'(by omega)).toUInt16
      let lo : UInt16 := (buf.data[pos + 1]).toUInt16
      .ok ((hi <<< 8) ||| lo, pos + 2)
    else .error "readUInt16BE: unexpected end of input"

def readUInt32BE : DnsParser UInt32 :=
  fun buf pos =>
    if h : pos + 3 < buf.data.size then
      let b3 : UInt32 := (buf.data[pos]'(by omega)).toUInt32
      let b2 : UInt32 := (buf.data[pos + 1]'(by omega)).toUInt32
      let b1 : UInt32 := (buf.data[pos + 2]'(by omega)).toUInt32
      let b0 : UInt32 := (buf.data[pos + 3]).toUInt32
      .ok ((b3 <<< 24) ||| (b2 <<< 16) ||| (b1 <<< 8) ||| b0, pos + 4)
    else .error "readUInt32BE: unexpected end of input"

def readBytes (n : Nat) : DnsParser ByteArray :=
  fun buf pos =>
    if pos + n ≤ buf.size then
      .ok (buf.extract pos (pos + n), pos + n)
    else .error s!"readBytes: need {n} bytes at offset {pos}, have {buf.size - pos}"

end DnsParser

-- ============================================================
-- DnsSerializer monad: StateM over a growing ByteArray
-- ============================================================

abbrev DnsSerializer (α : Type) := StateM ByteArray α

namespace DnsSerializer

def run {α : Type} (s : DnsSerializer α) : α × ByteArray :=
  StateT.run s ByteArray.empty

def runBytes (s : DnsSerializer Unit) : ByteArray :=
  (StateT.run s ByteArray.empty).2

-- ============================================================
-- Byte-level write primitives
-- ============================================================

def writeUInt8 (b : UInt8) : DnsSerializer Unit :=
  modify (·.push b)

def writeUInt16BE (v : UInt16) : DnsSerializer Unit := do
  writeUInt8 (v >>> 8).toUInt8
  writeUInt8 (v &&& 0xFF).toUInt8

def writeUInt32BE (v : UInt32) : DnsSerializer Unit := do
  writeUInt8 (v >>> 24).toUInt8
  writeUInt8 ((v >>> 16) &&& 0xFF).toUInt8
  writeUInt8 ((v >>> 8) &&& 0xFF).toUInt8
  writeUInt8 (v &&& 0xFF).toUInt8

def writeBytes (bs : ByteArray) : DnsSerializer Unit :=
  modify (· ++ bs)

def getPos : DnsSerializer Nat := do
  let buf ← get
  return buf.size

end DnsSerializer

-- ============================================================
-- BitVec conversion helpers
-- ============================================================

def bv16OfUInt16 (v : UInt16) : BitVec 16 := BitVec.ofNat 16 v.toNat
def uint16OfBv16 (v : BitVec 16) : UInt16 := v.toNat.toUInt16

def bv32OfUInt32 (v : UInt32) : BitVec 32 := BitVec.ofNat 32 v.toNat
def uint32OfBv32 (v : BitVec 32) : UInt32 := v.toNat.toUInt32

def bv8OfUInt8 (v : UInt8) : BitVec 8 := BitVec.ofNat 8 v.toNat
def uint8OfBv8 (v : BitVec 8) : UInt8 := v.toNat.toUInt8

-- Read/write helpers for BitVec fields
-- These work directly with BitVec operations (setWidth) to avoid
-- UInt↔Nat conversions that block bv_decide in proofs.

def readBV16 : DnsParser (BitVec 16) :=
  fun buf pos =>
    if h : pos + 1 < buf.data.size then
      let hi : BitVec 16 := (buf.data[pos]'(by omega)).toBitVec.setWidth 16
      let lo : BitVec 16 := (buf.data[pos + 1]).toBitVec.setWidth 16
      .ok ((hi <<< 8) ||| lo, pos + 2)
    else .error "readBV16: unexpected end of input"

def writeBV16 (v : BitVec 16) : DnsSerializer Unit := do
  DnsSerializer.writeUInt8 (UInt8.ofBitVec ((v >>> 8).setWidth 8))
  DnsSerializer.writeUInt8 (UInt8.ofBitVec (v.setWidth 8))

def readBV32 : DnsParser (BitVec 32) :=
  fun buf pos =>
    if h : pos + 3 < buf.data.size then
      let b3 : BitVec 32 := (buf.data[pos]'(by omega)).toBitVec.setWidth 32
      let b2 : BitVec 32 := (buf.data[pos + 1]'(by omega)).toBitVec.setWidth 32
      let b1 : BitVec 32 := (buf.data[pos + 2]'(by omega)).toBitVec.setWidth 32
      let b0 : BitVec 32 := (buf.data[pos + 3]).toBitVec.setWidth 32
      .ok ((b3 <<< 24) ||| (b2 <<< 16) ||| (b1 <<< 8) ||| b0, pos + 4)
    else .error "readBV32: unexpected end of input"

def writeBV32 (v : BitVec 32) : DnsSerializer Unit := do
  DnsSerializer.writeUInt8 (UInt8.ofBitVec ((v >>> 24).setWidth 8))
  DnsSerializer.writeUInt8 (UInt8.ofBitVec ((v >>> 16).setWidth 8))
  DnsSerializer.writeUInt8 (UInt8.ofBitVec ((v >>> 8).setWidth 8))
  DnsSerializer.writeUInt8 (UInt8.ofBitVec (v.setWidth 8))

def readBV8 : DnsParser (BitVec 8) :=
  fun buf pos =>
    if h : pos < buf.data.size then
      .ok ((buf.data[pos]).toBitVec, pos + 1)
    else .error "readBV8: unexpected end of input"

def writeBV8 (v : BitVec 8) : DnsSerializer Unit :=
  DnsSerializer.writeUInt8 (UInt8.ofBitVec v)

end VeriDNS.Impl
