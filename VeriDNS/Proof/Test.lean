import Batteries

namespace Test

abbrev TestParser (α : Type) := ReaderT ByteArray (StateT Nat (Except String)) α

namespace TestParser

def run {α : Type} (p : TestParser α) (buf : ByteArray) (pos : Nat := 0)
    : Except String (α × Nat) :=
  p buf pos

def readUInt8 : TestParser UInt8 :=
  fun buf pos =>
    if h : pos < buf.data.size then .ok (buf.data[pos], pos + 1)
    else .error "readUInt8: unexpected end of input"

def readUInt16BE : TestParser UInt16 :=
  fun buf pos =>
    if h : pos + 1 < buf.data.size then
      let hi : UInt16 := (buf.data[pos]'(by omega)).toUInt16
      let lo : UInt16 := (buf.data[pos + 1]).toUInt16
      .ok ((hi <<< 8) ||| lo, pos + 2)
    else .error "readUInt16BE: unexpected end of input"

def readUInt32BE : TestParser UInt32 :=
  fun buf pos =>
    if h : pos + 3 < buf.data.size then
      let b3 : UInt32 := (buf.data[pos]'(by omega)).toUInt32
      let b2 : UInt32 := (buf.data[pos + 1]'(by omega)).toUInt32
      let b1 : UInt32 := (buf.data[pos + 2]'(by omega)).toUInt32
      let b0 : UInt32 := (buf.data[pos + 3]).toUInt32
      .ok ((b3 <<< 24) ||| (b2 <<< 16) ||| (b1 <<< 8) ||| b0, pos + 4)
    else .error "readUInt32BE: unexpected end of input"

def readBytes (n : Nat) : TestParser ByteArray :=
  fun buf pos =>
    if pos + n ≤ buf.size then .ok (buf.extract pos (pos + n), pos + n)
    else .error "readBytes: unexpected end of input"

end TestParser

@[simp] theorem run_readUInt8 (buf : ByteArray) (pos : Nat) :
    TestParser.run TestParser.readUInt8 buf pos =
    if h : pos < buf.data.size then .ok (buf.data[pos], pos + 1)
    else .error "readUInt8: unexpected end of input" := by rfl

@[simp] theorem run_readUInt16BE (buf : ByteArray) (pos : Nat) :
    TestParser.run TestParser.readUInt16BE buf pos =
    if h : pos + 1 < buf.data.size then
      .ok (((buf.data[pos]'(by omega)).toUInt16 <<< 8) ||| (buf.data[pos + 1]).toUInt16, pos + 2)
    else .error "readUInt16BE: unexpected end of input" := by rfl

@[simp] theorem run_readUInt32BE (buf : ByteArray) (pos : Nat) :
    TestParser.run TestParser.readUInt32BE buf pos =
    if h : pos + 3 < buf.data.size then
      .ok (((buf.data[pos]'(by omega)).toUInt32 <<< 24) |||
           ((buf.data[pos + 1]'(by omega)).toUInt32 <<< 16) |||
           ((buf.data[pos + 2]'(by omega)).toUInt32 <<< 8) |||
           (buf.data[pos + 3]).toUInt32, pos + 4)
    else .error "readUInt32BE: unexpected end of input" := by rfl

end Test
