import VeriDNS.Impl.Parsec

namespace VeriDNS.Proof.Parsec

open VeriDNS.Impl

theorem bv16_roundtrip (v : BitVec 16) :
    bv16OfUInt16 (uint16OfBv16 v) = v := by
  simp [bv16OfUInt16, uint16OfBv16]

theorem bv32_roundtrip (v : BitVec 32) :
    bv32OfUInt32 (uint32OfBv32 v) = v := by
  simp [bv32OfUInt32, uint32OfBv32]

theorem bv8_roundtrip (v : BitVec 8) :
    bv8OfUInt8 (uint8OfBv8 v) = v := by
  simp [bv8OfUInt8, uint8OfBv8]

theorem uint16_roundtrip (v : UInt16) :
    uint16OfBv16 (bv16OfUInt16 v) = v := by
  simp [bv16OfUInt16, uint16OfBv16]

theorem uint32_roundtrip (v : UInt32) :
    uint32OfBv32 (bv32OfUInt32 v) = v := by
  simp [bv32OfUInt32, uint32OfBv32]

theorem uint8_roundtrip (v : UInt8) :
    uint8OfBv8 (bv8OfUInt8 v) = v := by
  simp [bv8OfUInt8, uint8OfBv8]

end VeriDNS.Proof.Parsec
