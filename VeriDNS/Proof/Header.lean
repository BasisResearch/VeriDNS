import VeriDNS.Impl.Header
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.BitPacking
import VeriDNS.Proof.Enum
import VeriDNS.Proof.Primitives
import VeriDNS.RFC.Check

namespace VeriDNS.Proof.Header

open VeriDNS.Impl
open VeriDNS.Spec
open VeriDNS.Proof

set_option maxRecDepth 32768 in
set_option maxHeartbeats 64000000 in

@[blueprint "header_roundtrip", uses := ["header", "header_flags_roundtrip"]]
theorem decode_encode (h : VeriDNS.Spec.Header) :
    DnsParser.run Header.decode (DnsSerializer.runBytes (Header.encode h)) =
      .ok (h, 12) := by

  conv in DnsSerializer.runBytes _ =>
    unfold DnsSerializer.runBytes Header.encode writeBV16
    unfold DnsSerializer.writeUInt16BE DnsSerializer.writeUInt8
    dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
                bind, StateT.bind, pure, StateT.pure, StateT.run,
                EStateM.modifyGet, EStateM.bind, EStateM.pure]

  simp (config := { decide := true }) only [

    Header.decode, Primitives.run_bind, Primitives.run_pure,
    Primitives.run_readBV16, Primitives.run_readUInt16BE, Primitives.run_fail,

    ByteArray.data_push, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.getElem_push, Array.size, Array.empty, Array.emptyWithCapacity,
    Array.toList_push, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd,

    dite_true, dite_false,

    Parsec.bv16_roundtrip,
    Primitives.uint16_byte_roundtrip,
    Primitives.bv16_byte_identity,
    BitPacking.unpack_pack,
    Enum.opcode_ofBV4_toBV4, Enum.rcode_ofBV4_toBV4]

rfc_proves decode_encode [1035][1401:1529]

end VeriDNS.Proof.Header
