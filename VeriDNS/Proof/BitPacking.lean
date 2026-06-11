import VeriDNS.Impl.BitPacking

namespace VeriDNS.Proof.BitPacking

open VeriDNS.Impl.BitPacking

-- ============================================================
-- unpack ∘ pack = id
-- ============================================================

private theorem truncate_shift_qr (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 15).truncate 1 = qr := by
  unfold packFlags; bv_decide

private theorem truncate_shift_opcode (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 11).truncate 4 = opcode := by
  unfold packFlags; bv_decide

private theorem truncate_shift_aa (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 10).truncate 1 = aa := by
  unfold packFlags; bv_decide

private theorem truncate_shift_tc (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 9).truncate 1 = tc := by
  unfold packFlags; bv_decide

private theorem truncate_shift_rd (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 8).truncate 1 = rd := by
  unfold packFlags; bv_decide

private theorem truncate_shift_ra (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 7).truncate 1 = ra := by
  unfold packFlags; bv_decide

private theorem truncate_shift_z (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    ((packFlags qr opcode aa tc rd ra z rcode) >>> 4).truncate 3 = z := by
  unfold packFlags; bv_decide

private theorem truncate_shift_rcode (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    (packFlags qr opcode aa tc rd ra z rcode).truncate 4 = rcode := by
  unfold packFlags; bv_decide

theorem unpack_pack (qr : BitVec 1) (opcode : BitVec 4) (aa : BitVec 1)
    (tc : BitVec 1) (rd : BitVec 1) (ra : BitVec 1) (z : BitVec 3)
    (rcode : BitVec 4) :
    unpackFlags (packFlags qr opcode aa tc rd ra z rcode) =
      (qr, opcode, aa, tc, rd, ra, z, rcode) := by
  simp [unpackFlags,
    truncate_shift_qr, truncate_shift_opcode, truncate_shift_aa,
    truncate_shift_tc, truncate_shift_rd, truncate_shift_ra,
    truncate_shift_z, truncate_shift_rcode]

end VeriDNS.Proof.BitPacking
