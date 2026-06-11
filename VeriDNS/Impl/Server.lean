import VeriDNS.Impl.Message
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Cache
import VeriDNS.Impl.SList
import VeriDNS.Impl.RData
import VeriDNS.Spec.Server
import VeriDNS.Spec.NegativeCache

namespace VeriDNS.Impl.Server
open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache

-- ============================================================
-- Pure response construction (no IO, fully provable)
-- ============================================================

/-- Build a DNS response from a query. Copies ID, sets QR=1, sets rcode. -/
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

/-- Build an error response with empty sections. -/
def buildErrorResponse (query : Format) (rcode : Rcode) : Format :=
  buildResponse query rcode #[] #[] #[]

/-- Final response flag hygiene before sending to the client: QR=1 (this is a
    response), RA=1 (this server pursues queries recursively), AA=0 (this
    server is not an authority for any zone). Instantiates the generated
    complement-semantics props: `ra_semantics_0` with `isAvailable := true`
    and `aa_semantics_0` with `isAuthority := false` (Proof/Server.lean). -/
def finalizeForClient (resp : Format) : Format :=
  -- z := 0: RFC 1035 §4.1.1 reserved bits "must be zero in all ... responses";
  -- also clears an echoed/upstream AD bit we did not validate (RFC 4035 §3.2.3).
  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }

/-- RFC 5452: outgoing queries use an unpredictable ID. -/
def withRandomId (q : Format) (rid : UInt16) : Format :=
  { q with header := { q.header with id := bv16OfUInt16 rid } }

/-- First questions match on name, type, and class. The name comparison is
    case-insensitive (RFC 1035 §3.1, generated
    `namespace_compare_caseinsensitive`): an upstream that echoes the QNAME
    in different case — e.g. 0x20-randomizing or case-normalizing servers —
    still matches its own response. -/
def questionMatches (a b : Array VeriDNS.Spec.Question) : Bool :=
  match a[0]?, b[0]? with
  | some qa, some qb =>
    DomainName.nameEqCI qa.qname qb.qname
      && qa.qtype == qb.qtype && qa.qclass == qb.qclass
  | _, _ => false

/-- RFC 1035 §7.4: "When a resolver receives unsolicited responses or RR data
    other than that requested, it should discard it without caching it."
    Accept only responses that echo our (unpredictable) query ID and our
    question; everything else is dropped before it can reach the cache.
    Instantiates `usingthecache_discard_unrequested` (Proof/Server.lean). -/
def acceptResponse (sent : Format) (resp : Format) : Option Format :=
  if resp.header.id == sent.header.id
      && questionMatches resp.question sent.question then
    some resp
  else none

/-- Build a fresh A-record query for a name (glueless NS sub-resolution). -/
def mkAddressQuery (name : ByteArray) : Format :=
  { header := {
      id := 0x4e53  -- "NS"
      qr := 0
      opcode := Opcode.query
      aa := 0, tc := 0, rd := 0, ra := 0, z := 0
      rcode := Rcode.noError
      qdcount := 1, ancount := 0, nscount := 0, arcount := 0 }
    question := #[{ qname := name, qtype := 1, qclass := 1 }]
    answer := #[]
    authority := #[]
    additional := #[] }

/-- RFC 2308 §3: the negative-answer TTL is "the minimum of the MINIMUM field
    of the SOA record and the TTL of the SOA itself". Instantiates the
    generated `negativeanswersfromauthoritativeservers_negative_ttl`
    (Proof/Cache.lean). -/
def computeNegativeTtl (soa : VeriDNS.Spec.RData.Soa.SoaRdata) (ttl : BitVec 32) : BitVec 32 :=
  if soa.minimum ≤ ttl then soa.minimum else ttl

/-- RFC 2308 §5 cap on how long a negative response is cached: the upper
    bound of the generated `cachingnegativeanswers_limit_negativeresponse_ttl`
    range ("Values of one to three hours have been found to work well and
    would make sensible a default") — 10800 seconds. -/
def negativeTtlCap : Nat := 10800

/-- Clamp a negative TTL to `negativeTtlCap` before storing (proven against
    the generated cap Prop in Proof/Server.lean). -/
def capNegativeTtl (t : BitVec 32) : BitVec 32 :=
  if t.toNat ≤ negativeTtlCap then t else BitVec.ofNat 32 negativeTtlCap

/-- Extract the SOA from an authority section: the (uncapped) negative TTL
    per §3 (`computeNegativeTtl`) and the SOA RR itself carrying that TTL —
    the record stored alongside the negative entry so §6 can return it from
    the cache. -/
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

/-- Extract the negative TTL from the SOA record in an authority section. -/
def extractSoaNegTtl (authority : Array ByteArray) : Option (BitVec 32) :=
  (extractSoaNegative authority).map (·.1)

/-- A response is negatively cacheable: NXDOMAIN, or NODATA per the generated
    `nodata_indicated` (NOERROR with an empty answer section). Truncated
    responses are excluded (§7.4). -/
def negativelyCacheable (resp : Format) : Bool :=
  resp.header.tc == 0
    && (resp.header.rcode == Rcode.nameError
        || (resp.header.rcode == Rcode.noError && resp.answer.isEmpty))

-- ============================================================
-- Query hygiene (RFC 1035 §4.1.1 RCODE use conditions)
-- ============================================================

/-- The kinds of query this server supports: standard queries only
    (OPCODE 0). IQUERY and STATUS are answered NOTIMP per
    `rcode_notImplemented_semantics` ("The name server does not support the
    requested kind of query"). -/
def supportsQueryKind (q : Format) : Bool :=
  q.header.opcode == Opcode.query

/-- A query this server can interpret: exactly one question.
    (`rcode_formatError_semantics`: "The name server was unable to
    interpret the query".) -/
def interpretableQuery (q : Format) : Bool :=
  q.question.size == 1

/-- This server offers recursive service only: a query with RD=0 requests
    the one operation it refuses to perform (iterative service), so the
    operation is not performed — REFUSED per the generated
    `rcode_refused_semantics` ("The name server refuses to perform the
    specified operation for policy reasons"). -/
def performsRequestedOperation (q : Format) : Bool :=
  q.header.rd == 1

/-- Classify a decoded query per the §4.1.1 RCODE use conditions;
    `none` = serve it. Interpretability is checked first: a query we cannot
    interpret cannot have its kind judged; a supported kind may still ask
    for an operation the server refuses (RD=0). -/
def queryProblem (q : Format) : Option Rcode :=
  if !interpretableQuery q then some Rcode.formatError
  else if !supportsQueryKind q then some Rcode.notImplemented
  else if !performsRequestedOperation q then some Rcode.refused
  else none

/-- Minimal FORMERR reply for an undecodable datagram: echo the raw 16-bit
    ID if present (QR=1, RCODE=1, all counts zero); `none` = drop (datagram
    too short to carry an ID worth echoing). -/
def rawFormatError (queryBytes : ByteArray) : Option ByteArray :=
  if queryBytes.size < 12 then none
  else some ⟨#[queryBytes.data[0]!, queryBytes.data[1]!, 0x80, 0x01,
               0, 0, 0, 0, 0, 0, 0, 0]⟩

-- ============================================================
-- RFC 1034 §5.3.3: delegation validation (bogus-delegation gate)
-- ============================================================

/-- The response is a delegation as 4b would classify it: NS records in
    authority, does not answer the query, no name error, and no CNAME to
    chase (4c takes precedence over 4b). -/
def delegationShapedB (resp : Format) : Bool :=
  Resolver.hasRRTypeIn (RR := ResourceRecord) resp.authority 2
    && !Resolver.answersQueryB (RR := ResourceRecord) resp
    && !(resp.header.rcode == Rcode.nameError)
    && (Resolver.cnameToChase (RR := ResourceRecord) resp).isNone

/-- "The delegation is closer to the answer than the servers in SLIST are":
    its match count (trailing labels shared between SNAME and the NS owner
    zone) strictly exceeds the SLIST's. An SLIST with no servers compares
    closer trivially (there are no servers to be closer than). -/
def delegationCloserB (slist : DnsSList) (sname : ByteArray) (resp : Format) : Bool :=
  SlistFromNameSpec.searchFails (NS := SlistEntry) slist
    || decide (Resolver.delegationMatchCount (RR := ResourceRecord)
        resp.authority sname > SlistFromNameSpec.matchCount (NS := SlistEntry) slist)

/-- §5.3.3: "the resolver should check to see that the delegation is
    'closer' to the answer than the servers in SLIST are ... If not, the
    reply is bogus and should be ignored." A bogus delegation never reaches
    `resume` (so neither resolution state nor the cache sees it) — this is
    the in-protocol cache-poisoning defense: a server answering our query
    cannot install NS/glue for zones no closer to SNAME than where we
    already are. Instantiates the generated `obligation_replyIgnored`
    (`shim_obligation_replyIgnored`). -/
def bogusDelegationB (slist : DnsSList) (sname : ByteArray) (resp : Format) : Bool :=
  delegationShapedB resp && !delegationCloserB slist sname resp

/-- An RR whose TTL exceeds one week (RFC 1035 §7.3's "excessively long
    TTL"). Unparseable bytes are not flagged here; they are rejected by the
    decoder. -/
def excessiveTtl (b : ByteArray) : Bool :=
  match RRParse.parseRaw (RR := ResourceRecord) b with
  | some rr => decide (604800 < rr.ttl.toNat)
  | none => false

/-- RFC 1035 §7.3 TTL sanity: "If a RR has an excessively long TTL, say
    greater than 1 week, either discard the whole response, or limit all
    TTLs in the response to 1 week." This takes the discard arm — a
    response carrying an excessive TTL is dropped like any other bogus
    response, so the sending server is removed from SLIST and the next one
    tried. (The limit arm would require re-encoding RRs, whose roundtrip
    proof needs decode-side label-validity lemmas we don't have.)
    Instantiates the generated `processingresponses_limit_ttls`. -/
def sanitizeTtls (resp : Format) : Option Format :=
  if resp.answer.any excessiveTtl || resp.authority.any excessiveTtl
      || resp.additional.any excessiveTtl then none
  else some resp

/-- Render a wire-format name for diagnostics (labels joined with dots). -/
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

/-- Extract the first A-record address from a response's answer section. -/
def extractAAddress (answers : Array ByteArray) : Option (BitVec 32) :=
  answers.findSome? fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) =>
      if rr.type == (1 : BitVec 16) && rr.rdata.size == 4 then
        let rd := rr.rdata
        some ((rd.data[0]!.toBitVec.setWidth 32 <<< 24) |||
              (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
              (rd.data[2]!.toBitVec.setWidth 32 <<< 8) |||
              rd.data[3]!.toBitVec.setWidth 32)
      else none
    | .error _ => none

/-- Truncate encoded message to ≤512 bytes per RFC 1035 §4.2.1.
    Re-encodes with TC=1, progressively dropping sections from the end. -/
def truncateUdp (encoded : ByteArray) (msg : Format) : ByteArray × Bool :=
  if encoded.size ≤ 512 then (encoded, false)
  else
    let tcHdr := { msg.header with tc := 1 }
    -- Drop additional
    let m1 : Format := { msg with header := { tcHdr with arcount := 0 }, additional := #[] }
    let e1 := Message.encode m1
    if e1.size ≤ 512 then (e1, true)
    else
      -- Drop authority
      let m2 : Format := { m1 with header := { m1.header with nscount := 0 }, authority := #[] }
      let e2 := Message.encode m2
      if e2.size ≤ 512 then (e2, true)
      else
        -- Drop answers (header+question only)
        let m3 : Format := { m2 with header := { m2.header with ancount := 0 }, answer := #[] }
        (Message.encode m3, true)

-- ============================================================
-- Address conversion for FFI
-- ============================================================

/-- Convert BitVec 32 IPv4 address to 6-byte FFI format (4-byte IP BE + 2-byte port BE).
    Uses port 53 (standard DNS). -/
def ipv4ToAddr (ip : BitVec 32) (port : UInt16 := 53) : ByteArray :=
  let b0 := (ip >>> 24).toNat.toUInt8
  let b1 := ((ip >>> 16) &&& 0xFF).toNat.toUInt8
  let b2 := ((ip >>> 8) &&& 0xFF).toNat.toUInt8
  let b3 := (ip &&& 0xFF).toNat.toUInt8
  let p0 := (port.toNat / 256).toUInt8
  let p1 := (port.toNat % 256).toUInt8
  ⟨#[b0, b1, b2, b3, p0, p1]⟩

-- ============================================================
-- RFC 5452 §9.1 datagram-level matching (decided in Lean)
-- ============================================================

/-- RFC 5452 §9.1 source/destination matching over the transport-reported
    addressing metadata, decided HERE (the transport reports, Lean decides):

    * the datagram's source must be the queried server — address (bytes
      0–3) and port (bytes 4–5);
    * the datagram's destination address must be the address the query
      left from;
    * the datagram's destination port (its delivery port) must be the
      query's source port.

    Each conjunct instantiates one matcher of the generated
    `querymatchingrules_match_obligation` (`accept_match_obligation`,
    Proof/Server.lean). -/
def datagramMatches (queried : ByteArray) (d : Exchanged ByteArray) : Bool :=
  d.source == queried
    && d.destination.extract 0 4 == d.localAddr.extract 0 4
    && d.destination.extract 4 6 == d.localAddr.extract 4 6

/-- The §9.1 datagram gate: yield the payload only when every
    source/destination matcher passes; "A mismatch and the response MUST
    be considered invalid." -/
def acceptExchanged (queried : ByteArray) (d : Exchanged ByteArray) : Option ByteArray :=
  if datagramMatches queried d then some d.payload else none

-- ============================================================
-- Iterative resolution with IO
-- ============================================================

section
variable {M : Type → Type} {Sock : Type} [Monad M] [UdpSocket M Sock ByteArray]

/-- Forward a query to a specific address and receive the response, on a
    per-exchange unconnected socket (RFC 5452 §9.2: unpredictable ephemeral
    local port). The §9.1 source/destination match is decided by
    `acceptExchanged` — in Lean, on the transport-reported metadata — and a
    mismatched datagram is treated like a timeout. -/
def forwardQuery (query : Format) (addr : ByteArray) : M (Option Format) := do
  let encoded := Message.encode query
  match ← UdpSocket.exchange (M := M) (Sock := Sock) encoded addr with
  | none => pure none
  | some d =>
    match acceptExchanged addr d with
    | none => pure none  -- §9.1 mismatch: invalid, dropped before decode
    | some bytes =>
      match Message.decode bytes with
      | .ok resp => pure (sanitizeTtls resp)  -- §7.3 TTL sanity
      | .error _ => pure none

end

section
variable {M : Type → Type} {Sock : Type} [Monad M] [UdpSocket M Sock ByteArray]

/-- IO resume loop: picks best server from SLIST, builds fresh sub-query, forwards upstream.
    True iterative resolution per RFC 1034 §5.3.3.
    Each upstream query runs on its own connected socket (RFC 5452).

    `deadline` is the absolute wall-clock time (Unix seconds) after which the
    whole resolution gives up — RFC 1035 §7.2's per-request bound on total
    work, independent of per-exchange timeouts and fuel.

    When no server in the SLIST has a known address (glueless delegation),
    follows RFC 1034 §5.3.3 step 2 — "It may be the case that the addresses
    are not available... the best is to start parallel resolver processes
    looking for the addresses" — by sub-resolving an NS name's A record
    (sequentially; `depth` bounds glueless nesting). -/
private def ioResumeLoop (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel : Nat) : M (Except String Format × DnsCache) :=
  match fuel with
  | 0 => pure (.error "resolveWithIO: max IO rounds", state.resources.cache)
  | fuel' + 1 => do
    let t ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
    if t ≥ deadline then
      return (.error "resolveWithIO: query deadline exceeded", state.resources.cache)
    -- Pick best server with a known address from SLIST
    match state.resources.slist.bestWithAddress with
    | none =>
      -- Glueless: look up an NS address via sub-resolution
      -- (instantiates recommendation_addressesAvailable). The sub-resolution
      -- shares this resolution's cache and learns into it.
      match depth, state.resources.slist.addressTargets[0]? with
      | depth' + 1, some nsName => do
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"glueless: resolving address of {nameToString nsName} (depth {depth'})"
        let addrQuery := mkAddressQuery nsName
        let (subResult, subCache) ←
          match @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord
              _ _ _ _ _ _ _ _ addrQuery sbelt 64 state.now DnsCache.empty with
          | .ok (.done resp) => pure (.ok resp, state.resources.cache)
          | .ok (.paused st) =>
            let (r, _) ← ioResumeLoop sbelt st deadline depth' fuel'
            pure (r, state.resources.cache)
          | .error msg => pure (.error msg, state.resources.cache)
        match subResult with
        | .ok subResp =>
          match extractAAddress subResp.answer with
          | some addr =>
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"glueless: {nameToString nsName} resolved"
            let _ ← pure ()
            let slist' := state.resources.slist.addAddress nsName addr
            let state' := { state with resources :=
              { state.resources with slist := slist', cache := subCache } }
            ioResumeLoop sbelt state' deadline depth' fuel'
          | none =>
            -- No A record for this NS name; drop it and try the next target
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"glueless: no A record for {nameToString nsName} (answers={subResp.answer.size}), dropping"
            let slist' := state.resources.slist.removeServer nsName
            let state' := { state with resources :=
              { state.resources with slist := slist', cache := subCache } }
            ioResumeLoop sbelt state' deadline depth' fuel'
        | .error e =>
          UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
            s!"glueless: sub-resolution for {nameToString nsName} failed: {e}, dropping"
          let slist' := state.resources.slist.removeServer nsName
          let state' := { state with resources :=
            { state.resources with slist := slist', cache := subCache } }
          ioResumeLoop sbelt state' deadline depth' fuel'
      | _, _ =>
        pure (.error "resolveWithIO: no servers with addresses in SLIST",
          state.resources.cache)
    | some (entry, ipAddr) =>
      -- Build fresh sub-query for current SNAME, with an unpredictable ID
      -- (RFC 5452)
      match Resolver.buildSubQuery state with
      | none => pure (.error "resolveWithIO: cannot build sub-query",
          state.resources.cache)
      | some subQuery₀ =>
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"query {nameToString state.resources.sname} → {nameToString entry.name} (fuel {fuel'})"
        let rid ← UdpSocket.randomId (M := M) (Sock := Sock) (Addr := ByteArray)
        let subQuery := withRandomId subQuery₀ rid
        let addr := ipv4ToAddr ipAddr
        let upstreamResp ← forwardQuery (Sock := Sock) subQuery addr
        -- Mark server as queried
        let slist' := state.resources.slist.markQueried entry.name
        let state := { state with resources := { state.resources with slist := slist' } }
        match upstreamResp with
        | none =>
          -- Timeout: KEEP the server. It is already marked queried, so
          -- §7.2's selection rule (least-queried first, instantiating
          -- `sendingthequeries_prevent_selection`) prefers every
          -- less-tried address before retrying it — retransmission "until
          -- all other addresses have been tried", bounded by fuel and the
          -- deadline. Servers are only removed for bizarre responses (4d)
          -- or failed glueless resolution.
          ioResumeLoop sbelt state deadline depth fuel'
        | some resp₀ =>
          -- §7.4: discard unsolicited / non-matching responses before they
          -- can influence resolution or the cache (acceptResponse gate)
          match acceptResponse subQuery resp₀ with
          | none => do
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"rejected response (id/question mismatch) for {nameToString state.resources.sname}"
            ioResumeLoop sbelt state deadline depth fuel'
          | some resp =>
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"resp: rcode={resp.header.rcode.toCode} an={resp.answer.size} ns={resp.authority.size} ar={resp.additional.size} tc={resp.header.tc}"
            -- §5.3.3 delegation validation: a not-closer delegation is
            -- bogus and IGNORED — it reaches neither resolution state nor
            -- the cache; the next candidate server is tried (this server
            -- stays marked queried).
            if bogusDelegationB state.resources.slist state.resources.sname resp then do
              UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
                s!"bogus delegation (not closer than SLIST) ignored for {nameToString state.resources.sname}"
              ioResumeLoop sbelt state deadline depth fuel'
            else
            -- §7.2: "If a resolver gets a server error or other bizarre
            -- response from a name server, it should remove it from SLIST"
            -- — deletion happens here, where the server identity is known;
            -- 4d (the same test) then retries with the next candidate.
            let state := if resp.header.rcode == Rcode.serverFailure
                || !Resolver.classifiableB resp then
              { state with resources := { state.resources with
                  slist := state.resources.slist.removeServer entry.name } }
            else state
            let resumed : Except String (Resolver.ResolveYield DnsSList DnsCache SlistEntry ResourceRecord) :=
              Resolver.resume state resp 64
            match resumed with
            | .ok (.done finalResp) => pure (.ok finalResp, state.resources.cache)
            | .ok (.paused state') => ioResumeLoop sbelt state' deadline depth fuel'
            | .error msg => do
              UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
                s!"resume error for {nameToString state.resources.sname}: {msg}"
              pure (.error msg, state.resources.cache)
  termination_by (depth, fuel)
  decreasing_by all_goals (first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega))

/-- Resolve with IO: runs pure resolver, forwards to upstream on pause, resumes.
    Upstream queries each use a per-exchange connected socket (RFC 5452).
    `budget` is the total wall-clock allowance in seconds for the whole
    resolution (RFC 1035 §7.2 per-request bound); `depth` bounds glueless NS
    sub-resolution nesting. `cache` is the persistent cache; the updated
    cache is returned alongside the result. -/
def resolveWithIO (query : Format) (sbelt : DnsSList)
    (cache : DnsCache := DnsCache.empty) (now : UInt32 := 0)
    (fuel : Nat := 40) (depth : Nat := 6) (budget : UInt32 := 5)
    : M (Except String Format × DnsCache) := do
  match @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord
      _ _ _ _ _ _ _ _ query sbelt 64 now cache with
  | .ok (.done resp) => pure (.ok resp, cache)
  | .ok (.paused state) => ioResumeLoop (Sock := Sock) sbelt state (now + budget) depth fuel
  | .error msg => pure (.error msg, cache)

/-- Serve one query with iterative resolution: recv → resolve (with IO) → send.
    clientSock: no timeout (blocks waiting for queries); upstream queries use
    per-exchange connected sockets.
    Threads the persistent TTL cache: returns the updated cache, and stores
    the final answer RRs (§5.3.3 4a "cache the data as well as returning it
    back to the client") unless truncated (§7.4). -/
def serveOne (clientSock : Sock) (sbelt : DnsSList)
    (cache : DnsCache) : M DnsCache := do
  let result : ByteArray × ByteArray ← UdpSocket.recvFrom clientSock 512
  let queryBytes := result.1
  let clientAddr := result.2
  match Message.decode queryBytes with
  | .error _ =>
    -- §4.1.1 RCODE 1 "unable to interpret the query": FORMERR with the raw
    -- ID echoed, or a silent drop if the datagram is too short to carry one
    match rawFormatError queryBytes with
    | some reply => do
      UdpSocket.sendTo clientSock reply clientAddr
      pure cache
    | none => pure cache
  | .ok query => do
    -- §4.1.1 RCODE use conditions: FORMERR (uninterpretable) / NOTIMP
    -- (unsupported kind) before resolution
    match queryProblem query with
    | some rc => do
      let reply := finalizeForClient (buildErrorResponse query rc)
      UdpSocket.sendTo clientSock (Message.encode reply) clientAddr
      pure cache
    | none =>
    let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
    let (resolveResult, cache') ← resolveWithIO (Sock := Sock) query sbelt cache nowT
    -- Restore the CLIENT's query ID: upstream sub-queries use unpredictable
    -- IDs (RFC 5452), so the final response carries an upstream ID that must
    -- be replaced before replying to the client.
    (match resolveResult with
      | .ok _ => pure ()
      | .error msg =>
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray) s!"SERVFAIL: {msg}")
    let resp0 := match resolveResult with
      | .ok resp => resp
      | .error _ => buildErrorResponse query .serverFailure
    let response := finalizeForClient
      { resp0 with header := { resp0.header with id := query.header.id } }
    (match resolveResult with
      | .ok resp =>
        if negativelyCacheable resp then
          match extractSoaNegTtl resp.authority, resp.question[0]? with
          | some negTtl, some _ =>
            UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
              s!"negative cache store (ttl {(capNegativeTtl negTtl).toNat})"
          | none, _ =>
            -- only a NODATA/NXDOMAIN whose authority lacks a usable SOA is
            -- noteworthy (cache-served negatives DO carry the §6 SOA and
            -- re-store harmlessly: the served TTL is the remaining
            -- lifetime, so the entry's absolute expiry never extends)
            if !resp.authority.isEmpty then
              UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
                "negative cacheable but no SOA negTtl extracted"
            else pure ()
          | _, none => pure ()
        else pure ()
      | .error _ => pure ())
    let cache'' := match resolveResult with
      | .ok resp =>
        let cp := Resolver.cacheUnlessTruncated (RR := ResourceRecord) cache' resp resp.answer
          (Resolver.credAnswer (resp.header.aa == 1)) nowT
        -- RFC 2308: cache NXDOMAIN/NODATA negatively, TTL = min(SOA.MINIMUM,
        -- SOA's TTL) from the authority section (computeNegativeTtl), capped
        -- at the §5 limit (capNegativeTtl); the SOA is stored alongside
        -- carrying the capped TTL so §6 can serve it decremented.
        if negativelyCacheable resp then
          match extractSoaNegative resp.authority, resp.question[0]? with
          | some (negTtl, soaRR), some qu =>
            let capped := capNegativeTtl negTtl
            cp.storeNegative qu.qname qu.qtype qu.qclass resp.header.rcode
              (some { soaRR with ttl := capped }) (nowT + capped.toNat.toUInt32)
          | _, _ => cp
        else cp
      | .error _ => cache'
    let encoded := Message.encode response
    let (truncated, _) := truncateUdp encoded response
    UdpSocket.sendTo clientSock truncated clientAddr
    pure cache''

/-- Queries between cache sweeps (§5.3.2 "discards them during periodic
    sweeps to reclaim the memory consumed by old RRs"). -/
def sweepInterval : Nat := 64

/-- Main server loop, threading the persistent cache. Every `sweepInterval`
    queries the cache is swept at the current wall clock — the periodic
    discard that the generated `sweep_subset` law (and
    `sweep_removes_expired`) governs; between sweeps, expired entries are
    already invisible to lookups (`lookup_fresh`). -/
partial def serverLoop [Inhabited (M Unit)] (clientSock : Sock)
    (sbelt : DnsSList) (cache : DnsCache := DnsCache.empty)
    (untilSweep : Nat := sweepInterval) : M Unit := do
  let cache' ← serveOne clientSock sbelt cache
  match untilSweep with
  | 0 => do
    let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
    serverLoop clientSock sbelt (DnsCache.sweep cache' nowT) sweepInterval
  | n + 1 =>
    serverLoop clientSock sbelt cache' n

end

end VeriDNS.Impl.Server
