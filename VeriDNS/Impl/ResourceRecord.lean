import VeriDNS.Impl.Parsec
import VeriDNS.Impl.DomainName
import VeriDNS.Spec.ResourceRecord

namespace VeriDNS.Impl.ResourceRecord

open VeriDNS.Impl
open VeriDNS.Spec

def decode : DnsParser VeriDNS.Spec.ResourceRecord := do
  let labels ← DomainName.decodeName
  let name := DomainName.labelsToWireFormat labels
  let type ← readBV16
  let class_ ← readBV16
  let ttl ← readBV32
  let rdlength ← readBV16
  let rdata ← DnsParser.readBytes rdlength.toNat
  return {
    name := name
    type := type
    «class» := class_
    ttl := ttl
    rdlength := rdlength
    rdata := rdata
  }

def encode (rr : VeriDNS.Spec.ResourceRecord) : DnsSerializer Unit := do
  DnsSerializer.writeBytes rr.name
  writeBV16 rr.type
  writeBV16 rr.«class»
  writeBV32 rr.ttl
  writeBV16 rr.rdlength
  DnsSerializer.writeBytes rr.rdata

end VeriDNS.Impl.ResourceRecord
