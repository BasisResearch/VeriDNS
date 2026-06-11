import VeriDNS.Impl.Header
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.BitPacking
import VeriDNS.Proof.Enum
import VeriDNS.Proof.Primitives

namespace VeriDNS.Proof.Header

open VeriDNS.Impl
open VeriDNS.Spec
open VeriDNS.Proof

set_option maxRecDepth 32768 in
set_option maxHeartbeats 64000000 in
theorem decode_encode (h : VeriDNS.Spec.Header) :
    DnsParser.run Header.decode (DnsSerializer.runBytes (Header.encode h)) =
      .ok (h, 12) := by
  -- Phase 1: Reduce serializer to concrete push chain using conv
  conv in DnsSerializer.runBytes _ =>
    unfold DnsSerializer.runBytes Header.encode writeBV16
    unfold DnsSerializer.writeUInt16BE DnsSerializer.writeUInt8
    dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
                bind, StateT.bind, pure, StateT.pure, StateT.run,
                EStateM.modifyGet, EStateM.bind, EStateM.pure]
  -- Mega-simp: all phases together so they can iterate
  simp (config := { decide := true }) only [
    -- Parser structure
    Header.decode, Primitives.run_bind, Primitives.run_pure,
    Primitives.run_readBV16, Primitives.run_readUInt16BE, Primitives.run_fail,
    -- ByteArray/Array access
    ByteArray.data_push, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.getElem_push, Array.size, Array.empty, Array.emptyWithCapacity,
    Array.toList_push, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd,
    -- Dite resolution
    dite_true, dite_false,
    -- Roundtrips (keep bv16OfUInt16/uint16OfBv16 opaque for bv16_roundtrip to match)
    Parsec.bv16_roundtrip,
    Primitives.uint16_byte_roundtrip,
    Primitives.bv16_byte_identity,
    BitPacking.unpack_pack,
    Enum.opcode_ofBV4_toBV4, Enum.rcode_ofBV4_toBV4]

end VeriDNS.Proof.Header
