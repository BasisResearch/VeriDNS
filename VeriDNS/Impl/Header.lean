import VeriDNS.Impl.Parsec
import VeriDNS.Impl.BitPacking
import VeriDNS.Impl.Enum
import VeriDNS.Spec.Header

namespace VeriDNS.Impl.Header

open VeriDNS.Impl
open VeriDNS.Spec

def decode : DnsParser VeriDNS.Spec.Header := do
  let id ← readBV16
  let flagsRaw ← DnsParser.readUInt16BE
  let flags := bv16OfUInt16 flagsRaw
  let (qr, opcodeBV, aa, tc, rd, ra, z, rcodeBV) := BitPacking.unpackFlags flags
  let opcode ← match Enum.Opcode.ofBV4 opcodeBV with
    | .ok v => pure v
    | .error e => DnsParser.fail e
  let rcode ← match Enum.Rcode.ofBV4 rcodeBV with
    | .ok v => pure v
    | .error e => DnsParser.fail e
  let qdcount ← readBV16
  let ancount ← readBV16
  let nscount ← readBV16
  let arcount ← readBV16
  return {
    id := id
    qr := qr
    opcode := opcode
    aa := aa
    tc := tc
    rd := rd
    ra := ra
    z := z
    rcode := rcode
    qdcount := qdcount
    ancount := ancount
    nscount := nscount
    arcount := arcount
  }

def encode (h : VeriDNS.Spec.Header) : DnsSerializer Unit := do
  writeBV16 h.id
  let opcodeBV := Enum.Opcode.toBV4 h.opcode
  let rcodeBV := Enum.Rcode.toBV4 h.rcode
  let flags := BitPacking.packFlags h.qr opcodeBV h.aa h.tc h.rd h.ra h.z rcodeBV
  DnsSerializer.writeUInt16BE (uint16OfBv16 flags)
  writeBV16 h.qdcount
  writeBV16 h.ancount
  writeBV16 h.nscount
  writeBV16 h.arcount

end VeriDNS.Impl.Header
