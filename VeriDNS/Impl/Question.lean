import VeriDNS.Impl.Parsec
import VeriDNS.Impl.DomainName
import VeriDNS.Spec.Question

namespace VeriDNS.Impl.Question

open VeriDNS.Impl
open VeriDNS.Spec

def decode : DnsParser VeriDNS.Spec.Question := do
  let labels ← DomainName.decodeName
  let qname := DomainName.labelsToWireFormat labels
  let qtype ← readBV16
  let qclass ← readBV16
  return { qname := qname, qtype := qtype, qclass := qclass }

def encode (q : VeriDNS.Spec.Question) : DnsSerializer Unit := do
  DnsSerializer.writeBytes q.qname
  writeBV16 q.qtype
  writeBV16 q.qclass

end VeriDNS.Impl.Question
