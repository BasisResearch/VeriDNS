import VeriDNS.Spec.Header
import VeriDNS.Spec.RRType
import VeriDNS.Spec.RRClass

namespace VeriDNS.Impl.Enum

open VeriDNS.Spec

def Opcode.toBV4 (o : Opcode) : BitVec 4 :=
  BitVec.ofNat 4 (Opcode.toCode o)

def Opcode.ofBV4 (v : BitVec 4) : Except String Opcode :=
  Opcode.ofCode v.toNat

def Rcode.toBV4 (r : Rcode) : BitVec 4 :=
  BitVec.ofNat 4 (Rcode.toCode r)

def Rcode.ofBV4 (v : BitVec 4) : Except String Rcode :=
  Rcode.ofCode v.toNat

end VeriDNS.Impl.Enum
