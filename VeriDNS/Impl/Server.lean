import VeriDNS.Impl.Message
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.AnswerScrub
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

def questionMatches (a b : Array VeriDNS.Spec.Question) : Bool :=
  match a[0]?, b[0]? with
  | some qa, some qb =>
    DomainName.nameEqCI qa.qname qb.qname
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

def extractSoaNegative (authority : Array ByteArray)
    : Option (BitVec 32 × ResourceRecord) :=
  authority.findSome? fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) =>
      if rr.type == (6 : BitVec 16) then
        match DnsParser.run VeriDNS.Impl.RData.decodeSoa rr.rdata with
        | .ok (soa, _) =>
          let negTtl := computeNegativeTtl soa rr.ttl
          some (negTtl, { rr with ttl := negTtl })
        | .error _ => none
      else none
    | .error _ => none

def extractSoaNegTtl (authority : Array ByteArray) : Option (BitVec 32) :=
  (extractSoaNegative authority).map (·.1)

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

/-- **Reply policy for a raw client datagram that does not decode as a DNS message.** `none` means
    the datagram is dropped with NO reply. Replying (even a 12-byte FORMERR) to undecodable input
    turns the resolver into a spoofed-source reflector and a fingerprinting oracle;
    hardened resolvers (unbound) silently drop such datagrams. Decodable-but-
    malformed queries are a different case — they are handled by `queryProblem` and still receive a
    proper FORMERR/NOTIMPL/REFUSED. The `serveOne` send on the undecodable path is gated on this
    policy, so restoring a reflective reply would require changing this definition — which
    `rawDatagramReply_drops` (`Proof/Server.lean`) forbids. -/
def rawDatagramReply (_queryBytes : ByteArray) : Option ByteArray := none

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

def sanitizeTtlsCap (resp : Format) : Option Format := some (capTtls resp)

def nameToString (wire : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  while i < wire.size do
    let len := wire.data[i]!.toNat
    if len == 0 || i + 1 + len > wire.size then break
    if !out.isEmpty then out := out ++ "."
    for j in [i+1 : i+1+len] do
      out := out.push (Char.ofNat wire.data[j]!.toNat)
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

def truncateUdp (encoded : ByteArray) (msg : Format) : ByteArray × Bool :=
  if encoded.size ≤ 512 then (encoded, false)
  else

    let m1 : Format := { msg with header := { msg.header with arcount := 0 }, additional := #[] }
    let e1 := Message.encode m1
    if e1.size ≤ 512 then (e1, false)
    else

      let m2 : Format := { m1 with header := { m1.header with tc := 1, nscount := 0 }, authority := #[] }
      let e2 := Message.encode m2
      if e2.size ≤ 512 then (e2, true)
      else

        let m3 : Format := { m2 with header := { m2.header with ancount := 0 }, answer := #[] }
        (Message.encode m3, true)

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

def boundStateCache
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord :=
  { state with resources := { state.resources with
      cache := state.resources.cache.boundExpiryClasses } }

def afterResume
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (resp : Format) : IoStep :=
  match Resolver.resume (dropIfBizarre state entryName resp) resp 64 with
  | .ok (.done finalResp stF) =>
    .finished (.ok finalResp) (boundStateCache stF).resources.cache
  | .ok (.paused state') => .continue (boundStateCache state')
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

/-- RFC 1034 §5.3.3 cache-first re-check after a glueless NETWORK sub-resolution: the sub-run
    may have cached the MAIN query's answer (e.g. sibling-NS glue) or a negative for it — a real
    resolver serves from cache rather than sending a redundant network query. The re-check is
    exactly the first two `Resolver.localAnswer` checks (the negative-cache lookup and the typed
    answerable hit) applied to the sub-run's output cache `subCache` at the main query's
    parameters, delivered in the `Resolver.stepCheckLocal` response shapes. A cached CNAME does
    NOT preempt the network path (only typed hits and negatives block the model's network rules),
    so there is NO cname peeling and `state.cnameChain` rides through `finalizeAnswer` unchanged.
    `none` means "no preemption — continue the main loop as before". -/
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

def ioResumeLoop (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel : Nat) : M (Except String Format × DnsCache) :=
  match fuel with
  | 0 => pure (.error "resolveWithIO: max IO rounds", state.resources.cache)
  | fuel' + 1 => do
    let t ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
    if t ≥ deadline then
      return (.error "resolveWithIO: query deadline exceeded", state.resources.cache)

    match state.resources.slist.bestWithAddress with
    | none =>

      match depth, state.resources.slist.addressTargets[0]? with
      | depth' + 1, some nsName => do
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
            deadline depth' fuel'
        | .error msg => do

          let slist' ← gluelessUpdatedSlist (Sock := Sock)
            state.resources.slist nsName (.error msg)
          ioResumeLoop sbelt
            { state with resources := { state.resources with slist := slist' } }
            deadline depth' fuel'
        | .ok (.paused st) => do
          let (subResult, subCache) ← ioResumeLoop sbelt st deadline depth' fuel'
          let slist' ← gluelessUpdatedSlist (Sock := Sock)
            state.resources.slist nsName subResult

          match subResult with
          | .ok subResp =>
            match extractAAddress subResp.answer with
            | some _ =>
              match gluelessRecheck state subCache with
              | some hit => pure (.ok hit, subCache)
              | none =>
                ioResumeLoop sbelt
                  { state with resources :=
                    { state.resources with slist := slist', cache := subCache } }
                  deadline depth' fuel'
            | none =>
              ioResumeLoop sbelt
                { state with resources := { state.resources with slist := slist' } }
                deadline depth' fuel'
          | .error _ =>
            ioResumeLoop sbelt
              { state with resources := { state.resources with slist := slist' } }
              deadline depth' fuel'
      | _, _ =>
        pure (.error "resolveWithIO: no servers with addresses in SLIST",
          state.resources.cache)
    | some (entry, ipAddr) => do

      let some subQuery₀ := Resolver.buildSubQuery state
        | pure (.error "resolveWithIO: cannot build sub-query", state.resources.cache)
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"query {nameToString state.resources.sname} → {nameToString entry.name} (fuel {fuel'})"
      let rid ← UdpSocket.randomId (M := M) (Sock := Sock) (Addr := ByteArray)
      let subQuery := withRandomId subQuery₀ rid
      let addr := ipv4ToAddr ipAddr
      let upstreamResp ← forwardQuery (Sock := Sock) subQuery addr

      let state := { state with resources :=
        { state.resources with slist := state.resources.slist.markQueried entry.name } }

      let some resp₀ := upstreamResp
        | ioResumeLoop sbelt state deadline depth fuel'

      let some resp := acceptResponse subQuery resp₀
        | do
          UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
            s!"rejected response (id/question mismatch) for {nameToString state.resources.sname}"
          ioResumeLoop sbelt state deadline depth fuel'
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"resp: rcode={resp.header.rcode.toCode} an={resp.answer.size} ns={resp.authority.size} ar={resp.additional.size} tc={resp.header.tc}"

      if unfollowableDelegationB state.resources.slist state.resources.sname resp then
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"unfollowable delegation (not closer than SLIST, or out of bailiwick) ignored for {nameToString state.resources.sname}"
        ioResumeLoop sbelt state deadline depth fuel'
      else

        match afterResume state entry.name resp with
        | .finished result cache => pure (result, cache)
        | .continue state'' => ioResumeLoop sbelt state'' deadline depth fuel'
  termination_by (depth, fuel)
  decreasing_by all_goals (first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega))

def resolveWithIO (query : Format) (sbelt : DnsSList)
    (cache : DnsCache := DnsCache.empty) (now : UInt32 := 0)
    (fuel : Nat := 40) (depth : Nat := 6) (budget : UInt32 := 5)
    : M (Except String Format × DnsCache) := do
  match @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord
      _ _ _ _ _ _ _ _ query sbelt 64 now cache with
  | .ok (.done resp _) => pure (.ok resp, cache)
  | .ok (.paused state) => ioResumeLoop (Sock := Sock) sbelt state (now + budget) depth fuel
  | .error msg => pure (.error msg, cache)

def storeNegativeIfCacheable (resp : Format) (base : DnsCache)
    (nowT : UInt32) : M DnsCache := do
  if negativelyCacheable resp then
    match extractSoaNegative resp.authority, resp.question[0]? with
    | some (negTtl, soaRR), some qu =>
      let capped := capNegativeTtl negTtl
      UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
        s!"negative cache store (ttl {capped.toNat})"
      pure (base.storeNegative qu.qname qu.qtype qu.qclass resp.header.rcode
        (some { soaRR with ttl := capped }) (nowT + capped.toNat.toUInt32))
    | none, _ =>
      if !resp.authority.isEmpty then
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          "negative cacheable but no SOA negTtl extracted"
      pure base
    | some _, none => pure base
  else pure base

def replyForResolution (query : Format) (resolveResult : Except String Format)
    (cache' : DnsCache) (nowT : UInt32) : M (Format × DnsCache) := do
  match resolveResult with
  | .error msg =>
    UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray) s!"SERVFAIL: {msg}"
    pure (finalizeForClient (buildErrorResponse query .serverFailure), cache')
  | .ok resp =>
    let qname : ByteArray := (query.question[0]?).elim ByteArray.empty (·.qname)

    let scrubbed := Resolver.scrubAnswerB (RR := ResourceRecord) qname resp.answer
    let response := finalizeForClient
      { resp with
        answer := scrubbed
        header := { resp.header with
          id := query.header.id
          ancount := BitVec.ofNat 16 scrubbed.size } }

    let base := Resolver.cacheUnlessTruncated (RR := ResourceRecord) cache' resp
      (Resolver.bailiwickRaws (RR := ResourceRecord) qname resp.answer)
      (Resolver.credAnswer (resp.header.aa == 1)) nowT
    let cache'' ← storeNegativeIfCacheable (Sock := Sock) resp base nowT
    pure (response, cache'')

def serveOne (clientSock : Sock) (sbelt : DnsSList)
    (cache : DnsCache) : M DnsCache := do
  let (queryBytes, clientAddr) : ByteArray × ByteArray ← UdpSocket.recvFrom clientSock 512

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
  let (truncated, _) := truncateUdp (Message.encode response) response
  UdpSocket.sendTo clientSock truncated clientAddr

  pure cache''.boundExpiryClasses

def sweepInterval : Nat := 64

partial def serverLoop [Inhabited (M Unit)] (clientSock : Sock)
    (sbelt : DnsSList) (cache : DnsCache := DnsCache.empty)
    (untilSweep : Nat := sweepInterval) : M Unit := do
  let cache' ← serveOne clientSock sbelt cache
  let (cache', n) <-
    match untilSweep with
    | 0 =>

      let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
      pure ((DnsCache.sweep cache' nowT), sweepInterval)
    | n + 1 =>
      pure (cache', n)
  serverLoop clientSock sbelt cache' n

end

end VeriDNS.Impl.Server
