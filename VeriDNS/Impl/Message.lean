import VeriDNS.Impl.Parsec
import VeriDNS.Impl.Header
import VeriDNS.Impl.Question
import VeriDNS.Impl.ResourceRecord
import VeriDNS.Spec.Message

namespace VeriDNS.Impl.Message

open VeriDNS.Impl
open VeriDNS.Spec

/-- Decode a resource record and return canonical (decompressed) wire bytes.
    Domain-name rdata types (NS=2, CNAME=5, PTR=12) have their rdata
    decompressed, and SOA (6) rdata has its MNAME/RNAME decompressed before
    the fixed 20-byte tail (serial/refresh/retry/expire/minimum — RFC 2308
    needs MINIMUM from authority-section SOAs, which e.g. AWS name servers
    send with compressed rdata names). The resulting ByteArray is
    self-contained (no compression pointers). -/
def decodeRRCanonical : DnsParser ByteArray := do
  let labels ← DomainName.decodeName
  let name := DomainName.labelsToWireFormat labels
  let rrtype ← readBV16
  let cls ← readBV16
  let ttl ← readBV32
  let rdlen ← readBV16
  -- For domain-name rdata types, decompress rdata too
  let rdata ← if rrtype == (2 : BitVec 16) || rrtype == (5 : BitVec 16)
                  || rrtype == (12 : BitVec 16) then do
    let rdataLabels ← DomainName.decodeName
    pure (DomainName.labelsToWireFormat rdataLabels)
  else if rrtype == (6 : BitVec 16) then do
    let mnameLabels ← DomainName.decodeName
    let rnameLabels ← DomainName.decodeName
    let tail ← DnsParser.readBytes 20
    pure (DomainName.labelsToWireFormat mnameLabels
      ++ DomainName.labelsToWireFormat rnameLabels ++ tail)
  else
    DnsParser.readBytes rdlen.toNat
  -- Re-encode with correct rdlength
  return DnsSerializer.runBytes do
    DnsSerializer.writeBytes name
    writeBV16 rrtype; writeBV16 cls; writeBV32 ttl
    writeBV16 (BitVec.ofNat 16 rdata.size)
    DnsSerializer.writeBytes rdata

/-- Parse `n` items with parser `p`, accumulating into `acc` in order.
    Structurally recursive so proofs can induct directly (replaces the
    previous `for _ in [:n]` loops, which desugar to `forIn` and resist
    equational reasoning). -/
def decodeMany {α : Type} (p : DnsParser α) : Nat → Array α → DnsParser (Array α)
  | 0, acc => pure acc
  | n + 1, acc => do
    let x ← p
    decodeMany p n (acc.push x)

/-- Run an encoder over each list element in order. Structurally recursive
    counterpart of `for x in xs do enc x` (same semantics in StateM). -/
def encodeList {α : Type} (enc : α → DnsSerializer Unit) : List α → DnsSerializer Unit
  | [] => pure ()
  | x :: rest => do
    enc x
    encodeList enc rest

/-- Decode a full DNS message from raw bytes. -/
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

/-- Encode a full DNS message to raw bytes. -/
def encode (msg : Format) : ByteArray :=
  DnsSerializer.runBytes do
    Header.encode msg.header
    encodeList Question.encode msg.question.toList
    encodeList DnsSerializer.writeBytes msg.answer.toList
    encodeList DnsSerializer.writeBytes msg.authority.toList
    encodeList DnsSerializer.writeBytes msg.additional.toList

end VeriDNS.Impl.Message
