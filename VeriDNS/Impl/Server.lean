import VeriDNS.Impl.Message
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.AnswerScrub
import VeriDNS.Impl.TcpFraming
import VeriDNS.Impl.Cache
import VeriDNS.Impl.SList
import VeriDNS.Impl.RData
import VeriDNS.Spec.Server
import VeriDNS.Spec.NegativeCache

namespace VeriDNS.Impl.Server
open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache

def buildResponse (query : Format) (rcode : Rcode)
    (answers authority additional : Array ByteArray) : Format :=
  { header := { query.header with
      qr := 1
      rcode := rcode
      ancount := (BitVec.ofNat 16 answers.size)
      nscount := (BitVec.ofNat 16 authority.size)
      arcount := (BitVec.ofNat 16 additional.size) }
    question := query.question
    answer := answers
    authority := authority
    additional := additional }

def buildErrorResponse (query : Format) (rcode : Rcode) : Format :=
  buildResponse query rcode #[] #[] #[]

def finalizeForClient (resp : Format) : Format :=

  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }

def withRandomId (q : Format) (rid : UInt16) : Format :=
  { q with header := { q.header with id := bv16OfUInt16 rid } }

def withCaseSeed (q : Format) (cid : UInt16) : Format :=
  { q with question := q.question.map fun qu =>
      { qu with qname := DomainName.randomizeCase cid qu.qname } }

def withSecrets (q : Format) (rid cid : UInt16) : Format :=
  withCaseSeed (withRandomId q rid) cid

def questionMatches (a b : Array VeriDNS.Spec.Question) : Bool :=
  match a[0]?, b[0]? with
  | some qa, some qb =>
    qa.qname == qb.qname
      && qa.qtype == qb.qtype && qa.qclass == qb.qclass
  | _, _ => false

def acceptResponse (sent : Format) (resp : Format) : Option Format :=
  if resp.header.id == sent.header.id
      && questionMatches resp.question sent.question then
    some resp
  else none

def mkAddressQuery (name : ByteArray) : Format :=
  { header := {
      id := 0x4e53
      qr := 0
      opcode := Opcode.query
      aa := 0, tc := 0, rd := 0, ra := 0, z := 0
      rcode := Rcode.noError
      qdcount := 1, ancount := 0, nscount := 0, arcount := 0 }
    question := #[{ qname := name, qtype := 1, qclass := 1 }]
    answer := #[]
    authority := #[]
    additional := #[] }

def computeNegativeTtl (soa : VeriDNS.Spec.RData.Soa.SoaRdata) (ttl : BitVec 32) : BitVec 32 :=
  if soa.minimum ≤ ttl then soa.minimum else ttl

def negativeTtlCap : Nat := 10800

def capNegativeTtl (t : BitVec 32) : BitVec 32 :=
  if t.toNat ≤ negativeTtlCap then t else BitVec.ofNat 32 negativeTtlCap

def extractSoaNegative (qname : ByteArray) (authority : Array ByteArray)
    : Option (BitVec 32 × ResourceRecord) :=
  authority.findSome? fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) =>
      if rr.type == (6 : BitVec 16) && Resolver.isAncestorB rr.name qname then
        match DnsParser.run VeriDNS.Impl.RData.decodeSoa rr.rdata with
        | .ok (soa, _) =>
          let negTtl := computeNegativeTtl soa rr.ttl
          some (negTtl, { rr with ttl := negTtl })
        | .error _ => none
      else none
    | .error _ => none

def extractSoaNegTtl (qname : ByteArray) (authority : Array ByteArray) : Option (BitVec 32) :=
  (extractSoaNegative qname authority).map (·.1)

def clientQname (query : Format) : ByteArray :=
  (query.question[0]?).elim ByteArray.empty (·.qname)

def scrubAuthorityB (qname : ByteArray) (authority : Array ByteArray) : Array ByteArray :=
  authority.filter fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) => Resolver.isAncestorB rr.name qname
    | .error _ => false

def negativelyCacheable (resp : Format) : Bool :=
  resp.header.tc == 0
    && (resp.header.rcode == Rcode.nameError
        || (resp.header.rcode == Rcode.noError && resp.answer.isEmpty))

def supportsQueryKind (q : Format) : Bool :=
  q.header.opcode == Opcode.query

def interpretableQuery (q : Format) : Bool :=
  q.question.size == 1

def performsRequestedOperation (q : Format) : Bool :=
  q.header.rd == 1

def queryProblem (q : Format) : Option Rcode :=
  if !interpretableQuery q then some Rcode.formatError
  else if !supportsQueryKind q then some Rcode.notImplemented
  else if !performsRequestedOperation q then some Rcode.refused
  else none

def rawDatagramReply (queryBytes : ByteArray) : Option ByteArray :=
  match DnsParser.run Header.decode queryBytes with
  | .error _ => none
  | .ok (h, _) =>
    if h.qr == 0 && h.opcode == Opcode.query then
      some (Message.encode
        { header := { h with
                      qr := 1, aa := 0, tc := 0, ra := 1, z := 0
                      rcode := Rcode.formatError
                      qdcount := 0, ancount := 0, nscount := 0, arcount := 0 }
          question := #[], answer := #[], authority := #[], additional := #[] })
    else none



structure AclEntry where
  net : BitVec 32
  plen : Nat
  deriving Inhabited, Repr

def AclEntry.matches (e : AclEntry) (ip : BitVec 32) : Bool :=
  let s := 32 - min e.plen 32
  (ip >>> s) == (e.net >>> s)

abbrev ClientAcl := List AclEntry

def clientIp (addr : ByteArray) : BitVec 32 :=
  ((addr.data.getD 0 0).toBitVec.setWidth 32 <<< 24) |||
  ((addr.data.getD 1 0).toBitVec.setWidth 32 <<< 16) |||
  ((addr.data.getD 2 0).toBitVec.setWidth 32 <<< 8) |||
  ((addr.data.getD 3 0).toBitVec.setWidth 32)

def permitted (acl : ClientAcl) (addr : ByteArray) : Bool :=
  acl.any (fun e => e.matches (clientIp addr))

def defaultAcl : ClientAcl :=
  [ { net := 0x7F000000, plen := 8 }
  , { net := 0x0A000000, plen := 8 }
  , { net := 0xAC100000, plen := 12 }
  , { net := 0xC0A80000, plen := 16 } ]



structure RateBucket where
  counts : Array (BitVec 32 × Nat) := #[]
  deriving Inhabited

def RateBucket.empty : RateBucket := {}

def rateWindowLimit : Nat := 200

def rateBucketCapacity : Nat := 65536

def RateBucket.bump (rb : RateBucket) (ip : BitVec 32) : Option RateBucket :=
  match rb.counts.findIdx? (fun p => p.1 == ip) with
  | some i =>
    let c := (rb.counts.getD i (ip, 0)).2
    if rateWindowLimit ≤ c then none
    else some { rb with counts := rb.counts.set! i (ip, c + 1) }
  | none =>
    if rateBucketCapacity ≤ rb.counts.size then some rb
    else some { rb with counts := rb.counts.push (ip, 1) }

def delegationShapedB (resp : Format) : Bool :=
  Resolver.hasRRTypeIn (RR := ResourceRecord) resp.authority 2
    && !Resolver.answersQueryB (RR := ResourceRecord) resp
    && !(resp.header.rcode == Rcode.nameError)
    && (Resolver.cnameToChase (RR := ResourceRecord) resp).isNone

def delegationCloserB (slist : DnsSList) (sname : ByteArray) (resp : Format) : Bool :=
  SlistFromNameSpec.searchFails (NS := SlistEntry) slist
    || decide (Resolver.delegationMatchCount (RR := ResourceRecord)
        resp.authority sname > SlistFromNameSpec.matchCount (NS := SlistEntry) slist)

def bogusDelegationB (slist : DnsSList) (sname : ByteArray) (resp : Format) : Bool :=
  delegationShapedB resp && !delegationCloserB slist sname resp

def respInBailiwick (sname : ByteArray) (resp : Format) : Bool :=
  resp.authority.all fun bytes =>
    match RRParse.parseRaw (RR := ResourceRecord) bytes with
    | some rr =>
      if RRParse.rrType rr == (2 : BitVec 16) then
        match DomainName.wireFormatToLabels (RRParse.rrName rr),
              DomainName.wireFormatToLabels sname with
        | .ok ownerLabels, .ok snameLabels =>
          Resolver.suffixMatchCount snameLabels ownerLabels == ownerLabels.size
        | _, _ => false
      else true
    | none => false

def unfollowableDelegationB (slist : DnsSList) (sname : ByteArray) (resp : Format) : Bool :=
  bogusDelegationB slist sname resp
    || (delegationShapedB resp && !respInBailiwick sname resp)

def referralShapedB (resp : Format) : Bool :=
  (Resolver.cnameToChase (RR := ResourceRecord) resp).isNone
    && !Resolver.answersQueryB (RR := ResourceRecord) resp
    && resp.answer.isEmpty
    && !resp.authority.isEmpty
    && Resolver.hasRRTypeIn (RR := ResourceRecord) resp.authority 2
    && resp.header.aa == 0
    && resp.header.rcode == Rcode.noError
    && !Resolver.hasRRTypeIn (RR := ResourceRecord) resp.authority 6

def retryShapedB (resp : Format) : Bool :=
  (Resolver.cnameToChase (RR := ResourceRecord) resp).isNone
    && (resp.header.rcode == Rcode.serverFailure || !Resolver.classifiableB resp)

def probePassableB (resp : Format) : Bool :=
  referralShapedB resp || retryShapedB resp

def strictDenialB (resp : Format) : Bool :=
  (Resolver.cnameToChase (RR := ResourceRecord) resp).isNone
    && resp.header.rcode == Rcode.nameError
    && resp.header.tc == 0

def storeProbeNegative (cache : DnsCache) (sub resp : Format) (now : UInt32) : DnsCache :=
  match sub.question[0]? with
  | some qu =>
    match extractSoaNegative qu.qname resp.authority with
    | some (negTtl, soaRR) =>
      let capped := capNegativeTtl negTtl
      cache.storeNegative qu.qname qu.qtype qu.qclass resp.header.rcode
        (some { soaRR with ttl := capped }) (now + capped.toNat.toUInt32) now
    | none => cache
  | none => cache

def excessiveTtl (b : ByteArray) : Bool :=
  match RRParse.parseRaw (RR := ResourceRecord) b with
  | some rr => decide (604800 < rr.ttl.toNat)
  | none => false

def sanitizeTtls (resp : Format) : Option Format :=
  if resp.answer.any excessiveTtl || resp.authority.any excessiveTtl
      || resp.additional.any excessiveTtl then none
  else some resp

def capTtlRR (b : ByteArray) : ByteArray :=
  match RRParse.parseRaw (RR := ResourceRecord) b with
  | some rr =>

    if rr.ttl >>> 31 == 1 then
      DnsSerializer.runBytes (ResourceRecord.encode { rr with ttl := 0 })
    else if 604800 < rr.ttl.toNat then
      DnsSerializer.runBytes (ResourceRecord.encode { rr with ttl := BitVec.ofNat 32 604800 })
    else b
  | none => b

def capTtls (resp : Format) : Format :=
  { resp with
    answer := resp.answer.map capTtlRR
    authority := resp.authority.map capTtlRR
    additional := resp.additional.map capTtlRR }

def sanitizeTtlsCap (resp : Format) : Option Format := some (capTtls (Edns.stripOpt resp))

def escapeNameByte (b : UInt8) : String :=
  let n := b.toNat
  if n == 0x2e || n == 0x5c then
    String.ofList ['\\', Char.ofNat n]
  else if 0x21 ≤ n && n ≤ 0x7e then
    String.ofList [Char.ofNat n]
  else
    String.ofList ['\\', Char.ofNat (0x30 + n / 100),
                   Char.ofNat (0x30 + (n / 10) % 10), Char.ofNat (0x30 + n % 10)]

def nameToString (wire : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  while i < wire.size do
    let len := wire.data[i]!.toNat
    if len == 0 || i + 1 + len > wire.size then break
    if !out.isEmpty then out := out ++ "."
    for j in [i+1 : i+1+len] do
      out := out ++ escapeNameByte wire.data[j]!
    i := i + 1 + len
  return out

def extractAAddress (answers : Array ByteArray) : Option (BitVec 32) :=
  answers.findSome? fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) =>

      if rr.type == (1 : BitVec 16) && rr.class == (1 : BitVec 16) && rr.rdata.size == 4
          && (DomainName.wireFormatToLabels rr.name).isOk then
        let rd := rr.rdata
        some ((rd.data[0]!.toBitVec.setWidth 32 <<< 24) |||
              (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
              (rd.data[2]!.toBitVec.setWidth 32 <<< 8) |||
              rd.data[3]!.toBitVec.setWidth 32)
      else none
    | .error _ => none

def truncateUdp (encoded : ByteArray) (msg : Format) (cap : Nat := 512) : ByteArray × Bool :=
  if encoded.size ≤ cap then (encoded, false)
  else

    let m1 : Format := { msg with header := { msg.header with arcount := 0 }, additional := #[] }
    let e1 := Message.encode m1
    if e1.size ≤ cap then (e1, false)
    else

      let m2 : Format := { m1 with header := { m1.header with tc := 1, nscount := 0 }, authority := #[] }
      let e2 := Message.encode m2
      if e2.size ≤ cap then (e2, true)
      else

        let m3 : Format := { m2 with header := { m2.header with ancount := 0 }, answer := #[] }
        (Message.encode m3, true)



def doNotQueryNets : List AclEntry :=
  [ { net := 0x00000000, plen := 8 }
  , { net := 0x7F000000, plen := 8 }
  , { net := 0x0A000000, plen := 8 }
  , { net := 0x64400000, plen := 10 }
  , { net := 0xA9FE0000, plen := 16 }
  , { net := 0xAC100000, plen := 12 }
  , { net := 0xC0A80000, plen := 16 }
  , { net := 0xF0000000, plen := 4 }
  ]

def readEgressBypassEnv : IO Bool := do
  match ← IO.getEnv "VERI_DNS_ALLOW_LOOPBACK_EGRESS" with
  | some s => pure (s == "1" || s == "true")
  | none => pure false

@[init readEgressBypassEnv] def egressBypassEnabled : Bool := false

def blockedEgress (ip : BitVec 32) : Bool :=
  !egressBypassEnabled && doNotQueryNets.any (fun e => e.matches ip)

def ipv4ToAddr (ip : BitVec 32) (port : UInt16 := 53) : ByteArray :=
  let b0 := (ip >>> 24).toNat.toUInt8
  let b1 := ((ip >>> 16) &&& 0xFF).toNat.toUInt8
  let b2 := ((ip >>> 8) &&& 0xFF).toNat.toUInt8
  let b3 := (ip &&& 0xFF).toNat.toUInt8
  let p0 := (port.toNat / 256).toUInt8
  let p1 := (port.toNat % 256).toUInt8
  ⟨#[b0, b1, b2, b3, p0, p1]⟩

def datagramMatches (queried : ByteArray) (d : Exchanged ByteArray) : Bool :=
  d.source == queried
    && d.destination.extract 0 4 == d.localAddr.extract 0 4
    && d.destination.extract 4 6 == d.localAddr.extract 4 6

def acceptExchanged (queried : ByteArray) (d : Exchanged ByteArray) : Option ByteArray :=
  if datagramMatches queried d then some d.payload else none

section
variable {M : Type → Type} {Sock : Type} [Monad M] [UdpSocket M Sock ByteArray]

def forwardQuery (query : Format) (addr : ByteArray) : M (Option Format) := do
  let encoded := Message.encode query
  match ← UdpSocket.exchange (M := M) (Sock := Sock) encoded addr with
  | none => pure none
  | some d =>
    match acceptExchanged addr d with
    | none => pure none
    | some bytes =>
      match Message.decode bytes with
      | .ok resp => pure (sanitizeTtlsCap resp)
      | .error _ => pure none

def tcpForward (query : Format) (addr : ByteArray) : M (Option Format) := do
  let encoded := Message.encode query
  match ← UdpSocket.tcpExchange (M := M) (Sock := Sock) encoded addr with
  | none => pure none
  | some bytes =>
    match Message.decode bytes with
    | .ok resp => pure (sanitizeTtlsCap resp)
    | .error _ => pure none

end

section
variable {M : Type → Type} {Sock : Type} [Monad M] [UdpSocket M Sock ByteArray]

inductive IoStep where

  | finished (result : Except String Format) (cache : DnsCache)
  | continue (next : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)

def dropIfBizarre
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (resp : Format)
    : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord :=
  if resp.header.rcode == Rcode.serverFailure || !Resolver.classifiableB resp then
    { state with resources := { state.resources with
        slist := state.resources.slist.removeServer entryName } }
  else state



def localAnswerTouches (cache : DnsCache) (qtype qclass : BitVec 16) (now : UInt32)
    : Nat → ByteArray → Array ByteArray → Array RRKey
  | 0, _sname, _visited => #[]
  | fuel + 1, sname, visited =>
    let dk := demandKey sname qtype qclass
    match NegativeCacheSpec.retrieveNegative cache sname qtype qclass now with
    | some _ => #[dk]
    | none =>
      let rrs : Array ResourceRecord :=
        TrustworthinessSpec.answers cache sname qtype qclass now
      if rrs.isEmpty then
        if qtype == (5 : BitVec 16) then #[dk]
        else
          let ck := demandKey sname (5 : BitVec 16) qclass
          match (TrustworthinessSpec.answers cache sname (5 : BitVec 16) qclass now
              : Array ResourceRecord)[0]? with
          | some crr =>
            let tgt := RRParse.rrRdata crr
            if visited.any (fun v => DomainName.nameEqCI v tgt) then #[dk, ck]
            else #[dk, ck] ++ localAnswerTouches cache qtype qclass now fuel
              tgt (visited.push tgt)
          | none => #[dk, ck]
      else #[dk]

def checkLocalTouches
    (s : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) : Array RRKey :=
  match s.lastQuery with
  | none => #[]
  | some q =>
    match q.question[0]? with
    | none => #[]
    | some qu =>
      localAnswerTouches s.resources.cache qu.qtype qu.qclass s.now 8 s.resources.sname
        (Resolver.cnameChaseVisited (RR := ResourceRecord) qu.qname s.cnameChain)

def walkNsTouches (cache : DnsCache) (nsType inClass : BitVec 16) (now : UInt32)
    : Nat → ByteArray → Array RRKey
  | 0, _name => #[]
  | fuel + 1, name =>
    let k := demandKey name nsType inClass
    let rrs : Array ResourceRecord := CacheSpec.lookupTopCred cache name nsType inClass now
    if rrs.isEmpty then
      match DomainName.parentDomainWire name with
      | some parent => #[k] ++ walkNsTouches cache nsType inClass now fuel parent
      | none => #[k]
    else #[k]

def findServersTouches
    (s : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) : Array RRKey :=
  let nsType : BitVec 16 := BitVec.ofNat 16 2
  let inClass : BitVec 16 := BitVec.ofNat 16 1
  let aType : BitVec 16 := BitVec.ofNat 16 1
  let wt := walkNsTouches s.resources.cache nsType inClass s.now 128 s.resources.sname
  let currentCloser (walkMc : Nat) : Bool :=
    !SlistFromNameSpec.searchFails (NS := SlistEntry) s.resources.slist
      && walkMc < SlistFromNameSpec.matchCount (NS := SlistEntry) s.resources.slist
  match Resolver.stepFindServers.walkNs (C := DnsCache) (RR := ResourceRecord)
      s.resources.sname s.resources.cache nsType inClass s.now 128 with
  | some (nsNames, mc) =>
    if currentCloser mc then wt
    else wt ++ nsNames.map (fun nsName => demandKey nsName aType inClass)
  | none => wt

def roundTouches
    (s : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (resp : Format) : Array RRKey :=
  match Resolver.stepAnalyzeResponse { s with lastResponse := some resp } with
  | .goto .checkAnswer s₁ =>
    checkLocalTouches s₁ ++
      (match Resolver.stepCheckLocal s₁ with
       | .goto .findServers s₂ => findServersTouches s₂
       | _ => #[])
  | .goto .findServers s₁ => findServersTouches s₁
  | _ => #[]

def boundStateCache (touches : Array RRKey)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord :=
  { state with resources := { state.resources with
      cache := state.resources.cache.boundLru touches state.now } }

def afterResume
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (resp : Format) : IoStep :=
  match Resolver.resume (dropIfBizarre state entryName resp) resp 64 with
  | .ok (.done finalResp stF) =>
    .finished (.ok finalResp)
      (boundStateCache (roundTouches (dropIfBizarre state entryName resp) resp) stF).resources.cache
  | .ok (.paused state') =>
    .continue (boundStateCache (roundTouches (dropIfBizarre state entryName resp) resp) state')
  | .error msg => .finished (.error msg) state.resources.cache

def gluelessUpdatedSlist (slist : DnsSList) (nsName : ByteArray)
    (subResult : Except String Format) : M DnsSList := do

  if let .ok subResp := subResult then
    if let some addr := extractAAddress subResp.answer then
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"glueless: {nameToString nsName} resolved"
      return slist.addAddress nsName addr
    else
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"glueless: no A record for {nameToString nsName} (answers={subResp.answer.size}), dropping"
  else if let .error e := subResult then
    UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
      s!"glueless: sub-resolution for {nameToString nsName} failed: {e}, dropping"
  return slist.removeServer nsName

def gluelessRecheck
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (subCache : DnsCache) : Option Format :=
  match state.lastQuery with
  | none => none
  | some q =>
    match q.question[0]? with
    | none => none
    | some qu =>
      match NegativeCacheSpec.retrieveNegative subCache state.resources.sname
          qu.qtype qu.qclass state.now with
      | some rc =>
        some (Resolver.finalizeAnswer state (Resolver.negativeResponse q rc
          (NegativeAuthoritySpec.authoritySection (RR := ResourceRecord) subCache
            state.resources.sname qu.qtype qu.qclass state.now)))
      | none =>
        let rrs : Array ResourceRecord := TrustworthinessSpec.answers subCache
          state.resources.sname qu.qtype qu.qclass state.now
        if rrs.isEmpty then none
        else some (Resolver.finalizeAnswer state (Resolver.cacheResponse q rrs))

def recheckTouches
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) : Array RRKey :=
  match state.lastQuery with
  | none => #[]
  | some q =>
    match q.question[0]? with
    | none => #[]
    | some qu => #[demandKey state.resources.sname qu.qtype qu.qclass]

def seedRevealed
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) : Nat :=
  SlistFromNameSpec.matchCount (NS := SlistEntry) state.resources.slist + 1

def revealedAfterContinue (prevSname : ByteArray) (revealed : Nat)
    (state' : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) : Nat :=
  if state'.resources.sname == prevSname then max revealed (seedRevealed state')
  else seedRevealed state'

def ioResumeLoop (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel : Nat) (revealed : Nat)
    : M (Except String Format × DnsCache) :=
  match fuel with
  | 0 => pure (.error "resolveWithIO: max IO rounds", state.resources.cache)
  | fuel' + 1 => do
    let t ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
    if t ≥ deadline then
      return (.error "resolveWithIO: query deadline exceeded", state.resources.cache)

    match state.resources.slist.bestWithAddress with
    | none =>

      match state.resources.slist.addressTargets[0]? with
      | some nsName =>
       match depth with
       | depth' + 1 => do
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"glueless: resolving address of {nameToString nsName} (depth {depth'})"

        match @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord
            _ _ _ _ _ _ _ _ (mkAddressQuery nsName) sbelt 64 state.now
            state.resources.cache with
        | .ok (.done resp _) => do

          let slist' ← gluelessUpdatedSlist (Sock := Sock)
            state.resources.slist nsName (.ok resp)
          ioResumeLoop sbelt
            { state with resources := { state.resources with slist := slist' } }
            deadline depth' fuel' revealed
        | .error msg => do

          let slist' ← gluelessUpdatedSlist (Sock := Sock)
            state.resources.slist nsName (.error msg)
          ioResumeLoop sbelt
            { state with resources := { state.resources with slist := slist' } }
            deadline depth' fuel' revealed
        | .ok (.paused st) => do
          let (subResult, subCache) ← ioResumeLoop sbelt st deadline depth' fuel'
            (seedRevealed st)
          let slist' ← gluelessUpdatedSlist (Sock := Sock)
            state.resources.slist nsName subResult

          match subResult with
          | .ok subResp =>
            match extractAAddress subResp.answer with
            | some _ =>
              match gluelessRecheck state subCache with
              | some hit =>
                pure (.ok hit, subCache.touchKeys (recheckTouches state) state.now)
              | none =>
                let subCacheT := subCache.touchKeys (recheckTouches state) state.now
                ioResumeLoop sbelt
                  { state with resources :=
                    { state.resources with slist := slist', cache := subCacheT } }
                  deadline depth' fuel' revealed
            | none =>
              ioResumeLoop sbelt
                { state with resources := { state.resources with slist := slist' } }
                deadline depth' fuel' revealed
          | .error _ =>
            ioResumeLoop sbelt
              { state with resources := { state.resources with slist := slist' } }
              deadline depth' fuel' revealed
       | 0 =>
         pure (.error "resolveWithIO: glueless depth exhausted",
           state.resources.cache)
      | none =>
        pure (.error "resolveWithIO: no servers with addresses in SLIST",
          state.resources.cache)
    | some (entry, ipAddr) => do

      let some subQuery₀ := Resolver.buildSubQuery state revealed
        | pure (.error "resolveWithIO: cannot build sub-query", state.resources.cache)
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"query {nameToString state.resources.sname} → {nameToString entry.name} (fuel {fuel'})"
      let rid ← UdpSocket.randomId (M := M) (Sock := Sock) (Addr := ByteArray)
      let cid ← UdpSocket.randomId (M := M) (Sock := Sock) (Addr := ByteArray)
      let subQuery := withSecrets subQuery₀ rid cid
      let addr := ipv4ToAddr ipAddr
      let upstreamResp ← if blockedEgress ipAddr then
          do
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"egress blocked (do-not-query address) to {nameToString entry.name} for {nameToString state.resources.sname}"
            pure none
        else forwardQuery (Sock := Sock) subQuery addr

      let state := { state with resources :=
        { state.resources with slist := state.resources.slist.markQueried entry.name } }

      let some resp₀ := upstreamResp
        | ioResumeLoop sbelt state deadline depth fuel' revealed

      let some resp := acceptResponse subQuery resp₀
        | do
          UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
            s!"rejected response (id/question mismatch) for {nameToString state.resources.sname}"
          ioResumeLoop sbelt state deadline depth fuel' revealed
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"resp: rcode={resp.header.rcode.toCode} an={resp.answer.size} ns={resp.authority.size} ar={resp.additional.size} tc={resp.header.tc}"

      let some resp ← (
          if resp.header.tc == 1 then do
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"truncated (TC=1) from {nameToString entry.name}; retrying over TCP for {nameToString state.resources.sname}"
            match ← tcpForward (Sock := Sock) subQuery addr with
            | none => pure none
            | some tcpResp =>
              match acceptResponse subQuery tcpResp with
              | none => pure none
              | some tcpRespA => pure (if tcpRespA.header.tc == 1 then none else some tcpRespA)
          else pure (some resp))
        | do
          UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
            s!"TCP fallback failed for {nameToString state.resources.sname}; dropping {nameToString entry.name}"
          ioResumeLoop sbelt
            { state with resources := { state.resources with
                slist := state.resources.slist.removeServer entry.name } }
            deadline depth fuel' revealed

      if unfollowableDelegationB state.resources.slist state.resources.sname resp then
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"unfollowable delegation (not closer than SLIST, or out of bailiwick) ignored for {nameToString state.resources.sname}"
        ioResumeLoop sbelt state deadline depth fuel' revealed
      else if Resolver.probeRoundB state.resources.sname revealed
          && strictDenialB resp then do
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"strict NXDOMAIN at probe ancestor: denying subtree for {nameToString state.resources.sname} (RFC 8020)"
        pure (.ok (Resolver.finalizeAnswer state resp),
          storeProbeNegative state.resources.cache subQuery₀ resp state.now)
      else if Resolver.probeRoundB state.resources.sname revealed
          && !probePassableB resp then
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"probe outcome (rcode={resp.header.rcode.toCode}) consumed for {nameToString state.resources.sname}: revealing more"
        ioResumeLoop sbelt state deadline depth fuel'
          (Resolver.bumpRevealed state.resources.sname revealed)
      else

        match afterResume state entry.name resp with
        | .finished result cache => pure (result, cache)
        | .continue state'' =>
          ioResumeLoop sbelt state'' deadline depth fuel'
            (revealedAfterContinue state.resources.sname revealed state'')
  termination_by (depth, fuel)
  decreasing_by all_goals (first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega))

def resolveWithIO (query : Format) (sbelt : DnsSList)
    (cache : DnsCache := DnsCache.empty) (now : UInt32 := 0)
    (fuel : Nat := 40) (depth : Nat := 6) (budget : UInt32 := 5)
    : M (Except String Format × DnsCache) := do
  match @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord
      _ _ _ _ _ _ _ _ query sbelt 64 now cache with
  | .ok (.done resp _) => pure (.ok resp, cache)
  | .ok (.paused state) =>
    ioResumeLoop (Sock := Sock) sbelt state (now + budget) depth fuel (seedRevealed state)
  | .error msg => pure (.error msg, cache)

def storeNegativeIfCacheable (resp : Format) (base : DnsCache)
    (nowT : UInt32) : M DnsCache := do
  if negativelyCacheable resp then
    match extractSoaNegative (clientQname resp) resp.authority, resp.question[0]? with
    | some (negTtl, soaRR), some qu =>
      let capped := capNegativeTtl negTtl
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"negative cache store (ttl {capped.toNat})"
      pure (base.storeNegative qu.qname qu.qtype qu.qclass resp.header.rcode
        (some { soaRR with ttl := capped }) (nowT + capped.toNat.toUInt32) nowT)
    | none, _ =>
      if !resp.authority.isEmpty then
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          "negative cacheable but no SOA negTtl extracted"
      pure base
    | some _, none => pure base
  else pure base

def deliveredResponse (query resp : Format) : Format :=
  let scrubbed := Resolver.scrubAnswerB (RR := ResourceRecord) (clientQname query) resp.answer
  let auth := scrubAuthorityB (clientQname query) resp.authority
  finalizeForClient
    { resp with
      answer := scrubbed
      authority := auth
      header := { resp.header with
        id := query.header.id
        rd := query.header.rd
        ancount := BitVec.ofNat 16 scrubbed.size
        nscount := BitVec.ofNat 16 auth.size } }

def replyForResolution (query : Format) (resolveResult : Except String Format)
    (cache' : DnsCache) (nowT : UInt32) : M (Format × DnsCache) := do
  match resolveResult with
  | .error msg =>
    UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray) s!"SERVFAIL: {msg}"
    pure (finalizeForClient (buildErrorResponse query .serverFailure), cache')
  | .ok resp =>
    let response := deliveredResponse query resp

    let base := Resolver.cacheUnlessTruncated (RR := ResourceRecord) cache' resp
      (Resolver.ownerRaws (RR := ResourceRecord) (clientQname query) resp.answer)
      (Resolver.credAnswer (resp.header.aa == 1)) nowT
    let cache'' ← storeNegativeIfCacheable (Sock := Sock) resp base nowT
    pure (response, cache'')

def serveTouches (query : Format) (sbelt : DnsSList) (cache : DnsCache)
    (nowT : UInt32) : Array RRKey :=
  let s0 := Resolver.initFromQuery (S := DnsSList) (C := DnsCache) (NS := SlistEntry)
    (RR := ResourceRecord) query sbelt nowT cache
  checkLocalTouches s0 ++
    (match Resolver.stepCheckLocal s0 with
     | .goto .findServers s₁ => findServersTouches s₁
     | _ => #[])

def serveDatagram (clientSock : Sock) (acl : ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray) : M DnsCache := do
  if !permitted acl clientAddr then return cache

  let (.ok query) <- pure (Message.decode queryBytes)
     | if let some reply := rawDatagramReply queryBytes then
          UdpSocket.sendTo clientSock reply clientAddr
       return cache

  if query.header.qr == 1 then return cache

  if let some rc := queryProblem query then
    UdpSocket.sendTo clientSock
      (Message.encode (finalizeForClient (buildErrorResponse query rc))) clientAddr
    return cache
  let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
  let (resolveResult, cache') ← resolveWithIO (Sock := Sock) query sbelt cache nowT
  let (response, cache'') ← replyForResolution (Sock := Sock) query resolveResult cache' nowT
  let (truncated, _) := truncateUdp (Message.encode response) response (Edns.clientCap query)
  UdpSocket.sendTo clientSock truncated clientAddr

  pure (cache''.boundLru (serveTouches query sbelt cache nowT) nowT)

def serveTcpDatagram (connSock : Sock) (acl : ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray) : M DnsCache := do
  if !permitted acl clientAddr then return cache

  let (.ok query) <- pure (Message.decode queryBytes)
     | if let some reply := rawDatagramReply queryBytes then
          UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
            (TcpFraming.frameTcp reply)
       return cache

  if query.header.qr == 1 then return cache

  if let some rc := queryProblem query then
    UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
      (TcpFraming.frameTcp (Message.encode (finalizeForClient (buildErrorResponse query rc))))
    return cache
  let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
  let (resolveResult, cache') ← resolveWithIO (Sock := Sock) query sbelt cache nowT
  let (response, cache'') ← replyForResolution (Sock := Sock) query resolveResult cache' nowT
  UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
    (TcpFraming.frameTcp (Message.encode response))

  pure (cache''.boundLru (serveTouches query sbelt cache nowT) nowT)

def serveOne (clientSock : Sock) (acl : ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) : M DnsCache := do
  let (queryBytes, clientAddr) : ByteArray × ByteArray ← UdpSocket.recvFrom clientSock 512
  serveDatagram clientSock acl sbelt cache queryBytes clientAddr

def afterRecv (clientSock : Sock) (acl : ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (rb : RateBucket) (queryBytes clientAddr : ByteArray)
    : M (DnsCache × RateBucket) :=
  match rb.bump (clientIp clientAddr) with
  | none => pure (cache, rb)
  | some rb' => (fun c => (c, rb')) <$>
      serveDatagram clientSock acl sbelt cache queryBytes clientAddr

def serveOneLimited (clientSock : Sock) (acl : ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (rb : RateBucket) : M (DnsCache × RateBucket) := do
  let (queryBytes, clientAddr) : ByteArray × ByteArray ← UdpSocket.recvFrom clientSock 512
  afterRecv clientSock acl sbelt cache rb queryBytes clientAddr

def sweepInterval : Nat := 64

partial def serverLoop [Inhabited (M Unit)] (clientSock : Sock)
    (acl : ClientAcl) (sbelt : DnsSList) (cache : DnsCache := DnsCache.empty)
    (rb : RateBucket := RateBucket.empty)
    (untilSweep : Nat := sweepInterval) : M Unit := do
  let (cache', rb') ← serveOneLimited clientSock acl sbelt cache rb
  let (cache', rb', n) <-
    match untilSweep with
    | 0 =>

      let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
      pure ((DnsCache.sweep cache' nowT), RateBucket.empty, sweepInterval)
    | n + 1 =>
      pure (cache', rb', n)
  serverLoop clientSock acl sbelt cache' rb' n

end

end VeriDNS.Impl.Server
