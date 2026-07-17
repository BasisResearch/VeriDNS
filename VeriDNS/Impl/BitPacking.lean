import VeriDNS.Impl.Parsec
import VeriDNS.Spec.Header

namespace VeriDNS.Impl.BitPacking

open VeriDNS.Spec

def packFlags (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) : BitVec 16 :=
  (qr.zeroExtend 16 <<< 15) |||
  (opcode.zeroExtend 16 <<< 11) |||
  (aa.zeroExtend 16 <<< 10) |||
  (tc.zeroExtend 16 <<< 9) |||
  (rd.zeroExtend 16 <<< 8) |||
  (ra.zeroExtend 16 <<< 7) |||
  (z.zeroExtend 16 <<< 4) |||
  rcode.zeroExtend 16

def unpackFlags (flags : BitVec 16)
    : BitVec 1 × BitVec 4 × BitVec 1 × BitVec 1 × BitVec 1 ×
      BitVec 1 × BitVec 3 × BitVec 4 :=
  let qr     := (flags >>> 15).truncate 1
  let opcode := (flags >>> 11).truncate 4
  let aa     := (flags >>> 10).truncate 1
  let tc     := (flags >>> 9).truncate 1
  let rd     := (flags >>> 8).truncate 1
  let ra     := (flags >>> 7).truncate 1
  let z      := (flags >>> 4).truncate 3
  let rcode  := flags.truncate 4
  (qr, opcode, aa, tc, rd, ra, z, rcode)

end VeriDNS.Impl.BitPacking
