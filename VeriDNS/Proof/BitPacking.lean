import VeriDNS.Impl.BitPacking
import VeriDNS.RFC.Check

namespace VeriDNS.Proof.BitPacking

open VeriDNS.Impl.BitPacking

private theorem truncate_shift_qr (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 15).truncate 1 = qr := by
  unfold packFlags; apply BitVec.eq_of_getLsbD_eq; intro i hi; obtain rfl : i = 0 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]; simp

private theorem truncate_shift_opcode (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 11).truncate 4 = opcode := by
  unfold packFlags
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  rw [BitVec.getLsbD_of_ge aa (11+i-10) (by omega), BitVec.getLsbD_of_ge tc (11+i-9) (by omega),
      BitVec.getLsbD_of_ge rd (11+i-8) (by omega), BitVec.getLsbD_of_ge ra (11+i-7) (by omega),
      BitVec.getLsbD_of_ge z (11+i-4) (by omega), BitVec.getLsbD_of_ge rcode (11+i) (by omega),
      show 11+i-11 = i from by omega]
  simp [hi, (show 11+i < 15 from by omega), (show 11+i < 16 from by omega), (show i < 16 from by omega),
    decide_eq_false (show ¬ 11+i < 11 from by omega)]

private theorem truncate_shift_aa (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 10).truncate 1 = aa := by
  unfold packFlags; apply BitVec.eq_of_getLsbD_eq; intro i hi; obtain rfl : i = 0 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]; simp

private theorem truncate_shift_tc (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 9).truncate 1 = tc := by
  unfold packFlags; apply BitVec.eq_of_getLsbD_eq; intro i hi; obtain rfl : i = 0 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]; simp

private theorem truncate_shift_rd (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 8).truncate 1 = rd := by
  unfold packFlags; apply BitVec.eq_of_getLsbD_eq; intro i hi; obtain rfl : i = 0 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]; simp

private theorem truncate_shift_ra (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 7).truncate 1 = ra := by
  unfold packFlags; apply BitVec.eq_of_getLsbD_eq; intro i hi; obtain rfl : i = 0 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]; simp

private theorem truncate_shift_z (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 4).truncate 3 = z := by
  unfold packFlags
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  rw [BitVec.getLsbD_of_ge rcode (4+i) (by omega), show 4+i-4 = i from by omega]
  simp [hi, (show 4+i < 15 from by omega), (show 4+i < 11 from by omega), (show 4+i < 10 from by omega),
    (show 4+i < 9 from by omega), (show 4+i < 8 from by omega), (show 4+i < 7 from by omega),
    (show 4+i < 16 from by omega), (show i < 16 from by omega), decide_eq_false (show ¬ 4+i < 4 from by omega)]

private theorem truncate_shift_rcode (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    (packFlags qr opcode aa tc rd ra z rcode).truncate 4 = rcode := by
  unfold packFlags
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp [hi, (show i < 15 from by omega), (show i < 11 from by omega), (show i < 10 from by omega),
    (show i < 9 from by omega), (show i < 8 from by omega), (show i < 7 from by omega),
    (show i < 4 from by omega), (show i < 16 from by omega)]

@[blueprint "header_flags_roundtrip"]
theorem unpack_pack (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    unpackFlags (packFlags qr opcode aa tc rd ra z rcode) =
      (qr, opcode, aa, tc, rd, ra, z, rcode) := by
  simp [unpackFlags,
    truncate_shift_qr, truncate_shift_opcode, truncate_shift_aa,
    truncate_shift_tc, truncate_shift_rd, truncate_shift_ra,
    truncate_shift_z, truncate_shift_rcode]

rfc_proves unpack_pack [1035][1401:1529]

end VeriDNS.Proof.BitPacking
