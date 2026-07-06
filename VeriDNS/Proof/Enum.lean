import VeriDNS.Impl.Enum

namespace VeriDNS.Proof.Enum

open VeriDNS.Spec
open VeriDNS.Impl.Enum

theorem opcode_ofBV4_toBV4 (o : Opcode) : Opcode.ofBV4 (Opcode.toBV4 o) = .ok o := by
  cases o <;> simp [Opcode.ofBV4, Opcode.toBV4, Opcode.ofCode, Opcode.toCode]

theorem rcode_ofBV4_toBV4 (r : Rcode) : Rcode.ofBV4 (Rcode.toBV4 r) = .ok r := by
  cases r <;> simp [Rcode.ofBV4, Rcode.toBV4, Rcode.ofCode, Rcode.toCode]

end VeriDNS.Proof.Enum
