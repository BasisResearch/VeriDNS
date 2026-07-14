import VeriDNS.Impl.Parsec
import VeriDNS.Impl.Header
import VeriDNS.Impl.Question
import VeriDNS.Impl.ResourceRecord
import VeriDNS.Spec.Message

namespace VeriDNS.Impl.Message

open VeriDNS.Impl
open VeriDNS.Spec

def decodeRRCanonical : DnsParser ByteArray := do
  let labels ← DomainName.decodeName
  let name := DomainName.labelsToWireFormat labels
  let rrtype ← readBV16
  let cls ← readBV16
  let ttl ← readBV32
  let rdlen ← readBV16

  let rdata ← if rrtype == (2 : BitVec 16) || rrtype == (5 : BitVec 16)
                  || rrtype == (12 : BitVec 16) then do
    let rdStart ← DnsParser.getPos
    let rdataLabels ← DomainName.decodeName
    let rdEnd ← DnsParser.getPos
    if rdEnd - rdStart == rdlen.toNat then
      pure (DomainName.labelsToWireFormat rdataLabels)
    else
      DnsParser.fail "rdlength disagrees with name-bearing rdata (RFC 1035 §3.3)"
  else if rrtype == (6 : BitVec 16) then do
    let rdStart ← DnsParser.getPos
    let mnameLabels ← DomainName.decodeName
    let rnameLabels ← DomainName.decodeName
    let tail ← DnsParser.readBytes 20
    let rdEnd ← DnsParser.getPos
    if rdEnd - rdStart == rdlen.toNat then
      pure (DomainName.labelsToWireFormat mnameLabels
        ++ DomainName.labelsToWireFormat rnameLabels ++ tail)
    else
      DnsParser.fail "rdlength disagrees with SOA rdata (RFC 1035 §3.3.13)"
  else if rrtype == (15 : BitVec 16) || rrtype == (33 : BitVec 16) then do
    let rdStart ← DnsParser.getPos
    let fixedPre ← DnsParser.readBytes (if rrtype == (15 : BitVec 16) then 2 else 6)
    let targetLabels ← DomainName.decodeName
    let rdEnd ← DnsParser.getPos
    if rdEnd - rdStart == rdlen.toNat then
      pure (fixedPre ++ DomainName.labelsToWireFormat targetLabels)
    else
      DnsParser.fail "rdlength disagrees with MX/SRV rdata (RFC 1035 §3.3.9, RFC 2782)"
  else
    DnsParser.readBytes rdlen.toNat

  return DnsSerializer.runBytes do
    DnsSerializer.writeBytes name
    writeBV16 rrtype; writeBV16 cls; writeBV32 ttl
    writeBV16 (BitVec.ofNat 16 rdata.size)
    DnsSerializer.writeBytes rdata

def decodeMany {α : Type} (p : DnsParser α) : Nat → Array α → DnsParser (Array α)
  | 0, acc => pure acc
  | n + 1, acc => do
    let x ← p
    decodeMany p n (acc.push x)

def encodeList {α : Type} (enc : α → DnsSerializer Unit) : List α → DnsSerializer Unit
  | [] => pure ()
  | x :: rest => do
    enc x
    encodeList enc rest

def decode (buf : ByteArray) : Except String Format :=
  match DnsParser.run (do
    let header ← Header.decode
    let questions ← decodeMany Question.decode header.qdcount.toNat #[]
    let answers ← decodeMany decodeRRCanonical header.ancount.toNat #[]
    let authority ← decodeMany decodeRRCanonical header.nscount.toNat #[]
    let additional ← decodeMany decodeRRCanonical header.arcount.toNat #[]
    return {
      header := header
      question := questions
      answer := answers
      authority := authority
      additional := additional
    }
  ) buf with
  | .ok (msg, _) => .ok msg
  | .error e => .error e

def encode (msg : Format) : ByteArray :=
  DnsSerializer.runBytes do
    Header.encode msg.header
    encodeList Question.encode msg.question.toList
    encodeList DnsSerializer.writeBytes msg.answer.toList
    encodeList DnsSerializer.writeBytes msg.authority.toList
    encodeList DnsSerializer.writeBytes msg.additional.toList

end VeriDNS.Impl.Message
