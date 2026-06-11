import VeriDNS.Impl.Message
import VeriDNS.Impl.ResourceRecord
import VeriDNS.Impl.DomainName
import VeriDNS.Spec.Resolver
import VeriDNS.Spec.NegativeCache
import VeriDNS.Spec.Credibility

namespace VeriDNS.Impl.Resolver

open VeriDNS.Spec
open VeriDNS.Impl

variable {S C NS RR : Type}
    [SlistSpec S NS] [SlistFromNameSpec S NS]
    [CacheSpec C RR] [TrustworthinessSpec C RR] [NegativeAuthoritySpec C RR] [RRParse RR]
    [Inhabited S] [Inhabited C]

structure State (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where
  resources : Resources S C NS RR
  currentStep : AlgorithmStep
  lastQuery : Option Format
  lastResponse : Option Format
  /-- CNAME RRs accumulated while chasing (RFC 1034 §5.3.3 4c); prepended to
      the final answer so the client sees the full alias chain. -/
  cnameChain : Array ByteArray := #[]
  /-- Absolute time (seconds) when this resolution started; used for cache
      expiry (RFC 1035 §6.1.3 "convert the interval ... to absolute time"). -/
  now : UInt32 := 0
  deriving Inhabited

inductive StepResult (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where
  | answer (response : Format)
  | «goto» (step : AlgorithmStep) (state : State S C NS RR)
  | needsIO (state : State S C NS RR)
  | error (msg : String)

-- ============================================================
-- RR helpers for working with wire-format ByteArray records
-- ============================================================

def extractNsNames [RRParse RR] (authority : Array ByteArray) : Array ByteArray :=
  let nsType : BitVec 16 := BitVec.ofNat 16 2
  authority.filterMap fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => if RRParse.rrType rr == nsType then some (RRParse.rrRdata rr) else none
    | none => none

def extractCname [RRParse RR] (answer : Array ByteArray) : Option ByteArray :=
  answer.findSome? fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => if RRParse.rrType rr == (5 : BitVec 16) then some (RRParse.rrRdata rr) else none
    | none => none

/-- The section contains an RR of the given type code. Implementation
    instantiation of the Spec's abstract `hasRRType` predicate
    (guardRefined_* / obligation_* in Spec/Resolver.lean). -/
def hasRRTypeIn [RRParse RR] (rrs : Array ByteArray) (code : BitVec 16) : Bool :=
  rrs.any fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => RRParse.rrType rr == code
    | none => false

/-- The response answers its own (echoed) question: the answer section
    contains an RR of the queried type. Implementation instantiation of the
    Spec's abstract `answersQuery` predicate. A query for CNAME records is
    answered by a CNAME, so no special case is needed. -/
def answersQueryB [RRParse RR] (resp : Format) : Bool :=
  match resp.question[0]? with
  | some qu => hasRRTypeIn (RR := RR) resp.answer qu.qtype
  | none => false

/-- 4c trigger (RFC 1034 §5.3.3): the response shows a CNAME "and that is not
    the answer itself". Instantiates guardRefined_cname: a CNAME is
    present and the response does not answer the query. Returns the canonical
    name to chase. -/
def cnameToChase [RRParse RR] (resp : Format) : Option ByteArray :=
  if answersQueryB (RR := RR) resp then none
  else extractCname (RR := RR) resp.answer

/-- Count of matching trailing labels (the DNS root side): the §5.3.2
    "match count of the number of labels" closeness measure. Consecutive
    from the end — stops at the first mismatch. -/
def suffixMatchCount (a b : Array ByteArray) : Nat := Id.run do
  let mut n := 0
  for i in [:min a.size b.size] do
    -- labels compare case-insensitively (RFC 1035 §3.1)
    if n == i && DomainName.nameEqCI a[a.size - 1 - i]! b[b.size - 1 - i]! then
      n := n + 1
  return n

/-- Match count of a delegation: trailing labels shared between SNAME and
    the owner zone of the delegation's NS records (§5.3.3: "comparing the
    match count in SLIST with that computed from SNAME and the NS RRs in
    the delegation"). 0 when no NS owner is parseable. -/
def delegationMatchCount [RRParse RR] (authority : Array ByteArray)
    (sname : ByteArray) : Nat :=
  let owner? := authority.findSome? fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr =>
      if RRParse.rrType rr == (2 : BitVec 16) then some (RRParse.rrName rr) else none
    | none => none
  match owner? with
  | none => 0
  | some zone =>
    match DomainName.wireFormatToLabels sname, DomainName.wireFormatToLabels zone with
    | .ok a, .ok b => suffixMatchCount a b
    | _, _ => 0

/-- Prepend the accumulated CNAME chain to a final response's answer section,
    updating ANCOUNT. Identity when no chasing occurred. -/
def prependChain (chain : Array ByteArray) (resp : Format) : Format :=
  if chain.isEmpty then resp
  else { resp with
    answer := chain ++ resp.answer
    header := { resp.header with
      ancount := BitVec.ofNat 16 (chain.size + resp.answer.size) } }

/-- Finalize an answer for the client: prepend the accumulated CNAME chain and
    restore the original question section. After chasing, the last sub-query's
    question names the canonical name; stub resolvers discard responses whose
    question does not match what they asked. -/
def finalizeAnswer (s : State S C NS RR) (resp : Format) : Format :=
  let withChain := prependChain s.cnameChain resp
  match s.lastQuery with
  | none => withChain
  | some q => { withChain with
      question := q.question
      header := { withChain.header with qdcount := BitVec.ofNat 16 q.question.size } }

/-- RFC 2181 §5.4.1 credibility tiers, as observed by a recursive resolver
    receiving a reply (`aa` = the response's Authoritative Answer bit), in
    the generated `Trustworthiness` enum: answer section of an
    authoritative / non-authoritative reply; authority section of an
    authoritative answer (a non-authoritative one is floor-tier); additional
    information / glue (the least-trustworthy floor — never answerable). -/
def credAnswer (aa : Bool) : Trustworthiness :=
  if aa then .authoritativeSection else .sectionNonauthoritative
def credAuthority (aa : Bool) : Trustworthiness :=
  if aa then .authoritySection else .additionalAuthoritative
def credAdditional : Trustworthiness := .additionalAuthoritative

/-- Cache RRs at a §5.4.1 credibility tier (credibility-checked store —
    more-trustworthy same-key data is retained). -/
def cacheRRs [TrustworthinessSpec C RR] [RRParse RR] (cache : C) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) : C :=
  raws.foldl (fun c bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => TrustworthinessSpec.acceptRrset c rr cred now | none => c) cache

/-- Cache response RRs at credibility `cred` unless the response is
    truncated. RFC 1035 §7.4: "When a response is truncated, and a resolver
    doesn't know whether it has a complete set, it should not cache a
    possibly partial set of RRs." -/
def cacheUnlessTruncated [TrustworthinessSpec C RR] [RRParse RR] (cache : C) (resp : Format)
    (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32) : C :=
  if resp.header.tc == 1 then cache
  else cacheRRs (RR := RR) cache raws cred now

/-- Extract A record glue from additional section: (name wire bytes, IPv4 address).
    Uses concrete ResourceRecord.decode since additional section is always wire-format. -/
def extractGlueRecords (additional : Array ByteArray) : Array (ByteArray × BitVec 32) :=
  let aType : BitVec 16 := BitVec.ofNat 16 1
  additional.filterMap fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) =>
      if rr.type == aType && rr.rdata.size == 4 then
        let rd := rr.rdata
        let addr : BitVec 32 :=
          (rd.data[0]!.toBitVec.setWidth 32 <<< 24) |||
          (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
          (rd.data[2]!.toBitVec.setWidth 32 <<< 8) |||
          rd.data[3]!.toBitVec.setWidth 32
        some (rr.name, addr)
      else none
    | .error _ => none

-- ============================================================
-- Step implementations
-- ============================================================

/-- A negative response (RFC 2308): cached negative rcode; the authority
    section carries the cached SOA with decremented TTL (§6: a server
    answering from the negative cache "MUST add the cached SOA record to
    the authority section of the response"). -/
def negativeResponse [RRParse RR] (q : Format) (rc : Rcode) (soaAuth : Array RR) : Format :=
  { header := { q.header with
      qr := 1, rcode := rc
      ancount := 0, nscount := BitVec.ofNat 16 soaAuth.size, arcount := 0 }
    question := q.question
    answer := #[], authority := soaAuth.map RRParse.rrBytes, additional := #[] }

/-- A response synthesized from cached RRs (RFC 1034 §5.3.3 step 1: the
    answer is in local information → return it to the client). The RRs carry
    remaining TTLs from the lookup. -/
def cacheResponse [RRParse RR] (q : Format) (rrs : Array RR) : Format :=
  { header := { q.header with
      qr := 1, rcode := Rcode.noError
      ancount := BitVec.ofNat 16 rrs.size, nscount := 0, arcount := 0 }
    question := q.question
    answer := rrs.map RRParse.rrBytes
    authority := #[], additional := #[] }

/-- Result of the local-information check at step 1. A negative hit
    carries the §6 authority RRs (the cached SOA, TTL decremented). -/
inductive LocalResult (RR : Type) where
  | negative (rc : Rcode) (soaAuth : Array RR)
  | answerHit (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
  | miss (sname : ByteArray) (chain : Array ByteArray)

/-- Step 1's cache consultation, following cached CNAMEs (RFC 1034 §3.6.2:
    CNAME processing "restarts the query at the canonical name") when the
    query key itself misses. Lookups come FIRST at each name, so a direct
    hit is never shadowed by an alias; the chase is fuel-bounded. -/
def localAnswer [TrustworthinessSpec C RR] [NegativeAuthoritySpec C RR] [RRParse RR] (cache : C)
    (qtype qclass : BitVec 16) (now : UInt32)
    : Nat → ByteArray → Array ByteArray → LocalResult RR
  | 0, sname, chain => .miss sname chain
  | fuel + 1, sname, chain =>
    match NegativeCacheSpec.retrieveNegative cache sname qtype qclass now with
    | some rc =>
      .negative rc (NegativeAuthoritySpec.authoritySection cache sname qtype qclass now)
    | none =>
      -- answer path: only answer-grade data may be served (RFC 2181 §5.4.1)
      let rrs : Array RR := TrustworthinessSpec.answers cache sname qtype qclass now
      if rrs.isEmpty then
        if qtype == (5 : BitVec 16) then .miss sname chain
        else
          match (TrustworthinessSpec.answers cache sname (5 : BitVec 16) qclass now
              : Array RR)[0]? with
          | some crr =>
            localAnswer cache qtype qclass now fuel
              (RRParse.rrRdata crr) (chain.push (RRParse.rrBytes crr))
          | none => .miss sname chain
      else .answerHit sname chain rrs

/-- Step 1: Check local cache for the desired data.
    A fresh negative cache entry (RFC 2308) answers immediately; a fresh
    positive entry — possibly through a chain of cached CNAMEs — is
    returned to the client (instantiates the generated
    `obligation_checkAnswer`: "See if the answer is in local information,
    and if so return it to the client"). A partial cached-CNAME chase that
    ends in a miss continues resolution at the canonical name (with the
    SLIST reset: its match count measured closeness to the OLD sname). -/
def stepCheckLocal (s : State S C NS RR) : StepResult S C NS RR :=
  match s.lastQuery with
  | none => .goto .findServers s
  | some q =>
    match q.question[0]? with
    | none => .goto .findServers s
    | some qu =>
      match localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
          s.now 8 s.resources.sname s.cnameChain with
      | .negative rc soaAuth => .answer (negativeResponse q rc soaAuth)
      | .answerHit _ chain rrs =>
        -- finalizeAnswer prepends the accumulated chain and restores the
        -- original client question.
        .answer (finalizeAnswer { s with cnameChain := chain } (cacheResponse q rrs))
      | .miss sname' chain =>
        if sname' == s.resources.sname then .goto .findServers s
        else
          .goto .findServers { s with
            resources := { s.resources with sname := sname', slist := default }
            cnameChain := chain }

/-- Step 2: Find the best servers to ask.
    Walks SNAME labels looking for NS records in cache; falls back to SBELT.

    RFC 1034 §5.3.2: the SLIST match count "is used as a measure of how
    'close' the resolver is to SNAME". A delegation (4b) may have installed a
    closer SLIST than the cache walk can reproduce — e.g. when the referral
    was truncated and therefore not cached per §7.4 — so the current SLIST is
    kept whenever it is strictly closer than the walk result. -/
def stepFindServers (s : State S C NS RR) : StepResult S C NS RR :=
  let nsType : BitVec 16 := BitVec.ofNat 16 2
  let inClass : BitVec 16 := BitVec.ofNat 16 1
  let currentCloser (walkMc : Nat) : Bool :=
    !SlistFromNameSpec.searchFails (NS := NS) s.resources.slist
      && walkMc < SlistFromNameSpec.matchCount (NS := NS) s.resources.slist
  match walkNs s.resources.sname s.resources.cache nsType inClass s.now 128 with
  | some (nsNames, mc) =>
    if currentCloser mc then
      .goto .sendQueries s
    else
      -- Look up A records (type 1) in cache for each NS name to get glue addresses
      let aType : BitVec 16 := BitVec.ofNat 16 1
      let glue : Array (ByteArray × BitVec 32) := nsNames.filterMap fun nsName =>
        let aRRs : Array RR := CacheSpec.lookup s.resources.cache nsName aType inClass s.now
        aRRs.findSome? fun rr =>
          let rd := RRParse.rrRdata rr
          if rd.size == 4 then
            let addr : BitVec 32 :=
              (rd.data[0]!.toBitVec.setWidth 32 <<< 24) |||
              (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
              (rd.data[2]!.toBitVec.setWidth 32 <<< 8) |||
              rd.data[3]!.toBitVec.setWidth 32
            some (nsName, addr)
          else none
      let slist' : S := SlistFromNameSpec.setUpAddresses (NS := NS) nsNames glue mc
      .goto .sendQueries { s with resources := { s.resources with slist := slist' } }
  | none =>
    if currentCloser 0 then
      .goto .sendQueries s
    else
      .goto .sendQueries { s with resources := { s.resources with
        slist := s.resources.sbelt } }
where
  walkNs (name : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32)
      : Nat → Option (Array ByteArray × Nat)
    | 0 => none
    | fuel + 1 =>
      let rrs : Array RR := CacheSpec.lookup cache name nsType inClass now
      if rrs.isEmpty then
        match DomainName.parentDomainWire name with
        | some parent => walkNs parent cache nsType inClass now fuel
        | none => none
      else
        let nsNames := rrs.filterMap fun rr =>
          if RRParse.rrType rr == nsType then some (RRParse.rrRdata rr) else none
        let mc : Nat := match DomainName.wireFormatToLabels name with
          | .ok labels => labels.size
          | .error _ => 0
        some (nsNames, mc)

/-- Step 3: Send queries until a response is received. -/
def stepSendQueries (s : State S C NS RR) : StepResult S C NS RR :=
  match s.lastResponse with
  | some _ => .goto .analyzeResponse s
  | none => .needsIO s

/-- The response shapes this resolver classifies and handles: a non-empty
    answer (4a/4c), name error (4a), a populated authority (4b / RFC 2308
    NODATA), NOERROR (NODATA), or truncation (§4.2.1 passthrough). Its
    complement is §5.3.3 4d's "other bizarre contents"; instantiates the
    abstract `handled` parameter of the generated refined guards. -/
def classifiableB (resp : Format) : Bool :=
  !resp.answer.isEmpty
    || resp.header.rcode == Rcode.nameError
    || !resp.authority.isEmpty
    || resp.header.rcode == Rcode.noError
    || resp.header.tc == 1

/-- Step 4: Analyze the response.
    4c: CNAME (not itself the answer) → chase: step 1; 4d: server failure or
    other bizarre contents → step 3; 4b: delegation (non-answering response
    with NS authority) → step 2; 4a: answer/name error → return with
    accumulated chain. Branch conditions instantiate the generated refined
    guards so the implementation satisfies the obligation_* props
    (Proof/Resolver.lean). -/
def stepAnalyzeResponse (s : State S C NS RR) : StepResult S C NS RR :=
  match s.lastResponse with
  | none => .error "no response to analyze"
  | some resp =>
    -- 4c: CNAME redirect, checked first (RFC 1034 §5.3.3: "if the response
    -- shows a CNAME and that is not the answer itself, cache the CNAME,
    -- change the SNAME to the canonical name in the CNAME RR and go to
    -- step 1"). Justified by StepSpec.cname; obligation:
    -- impl_obligation_cname.
    match cnameToChase (RR := RR) resp with
    | some canonicalName =>
      let cache' := cacheUnlessTruncated (RR := RR) s.resources.cache resp resp.answer
        (credAnswer (resp.header.aa == 1)) s.now
      -- "change the SNAME to the canonical name ... and go to step 1": the
      -- SLIST is reset because its match count measured closeness to the OLD
      -- SNAME; step 2 rebuilds it for the canonical name.
      .goto .checkAnswer { s with
        resources := { s.resources with
          sname := canonicalName, cache := cache', slist := default }
        cnameChain := s.cnameChain ++ resp.answer
        lastResponse := none }
    | none =>
      -- 4d: "if the response shows a servers failure or other bizarre
      -- contents, delete the server from the SLIST and go back to step 3."
      -- Widened beyond rcode=2 to the complement of classifiable responses
      -- (e.g. REFUSED with empty sections), instantiating the widened
      -- guardRefined_serverFailure with handled := classifiableB. The
      -- deletion happens shim-side (ioResumeLoop knows the server identity).
      -- lastResponse is cleared so step 3 transmits to the next candidate
      -- instead of re-analyzing the same response.
      if resp.header.rcode == Rcode.serverFailure || !classifiableB resp then
        .goto .sendQueries { s with lastResponse := none }
      -- 4b: delegation — a non-answering, non-negative response whose
      -- authority section is populated (with NS records: inner check)
      else if !answersQueryB (RR := RR) resp
          && !(resp.header.rcode == Rcode.nameError)
          && !resp.authority.isEmpty then
        if hasRRTypeIn (RR := RR) resp.authority 2 then
          let nsNames := extractNsNames (RR := RR) resp.authority
          -- Cache authority and additional sections. (A bogus — not-closer —
          -- delegation never reaches this point: the shim's
          -- `bogusDelegationB` gate drops it before `resume`, per §5.3.3
          -- "the reply is bogus and should be ignored".)
          let cache' := cacheUnlessTruncated (RR := RR) s.resources.cache resp resp.authority
            (credAuthority (resp.header.aa == 1)) s.now
          let cache'' := cacheUnlessTruncated (RR := RR) cache' resp resp.additional
            credAdditional s.now
          -- §5.3.2 closeness: the new SLIST's match count is the labels the
          -- delegation zone shares with SNAME (NOT SNAME's full label
          -- count, which would inflate closeness and break comparisons).
          let mc : Nat := delegationMatchCount (RR := RR) resp.authority s.resources.sname
          -- Extract glue A records from additional section and populate SLIST with addresses
          let glue := extractGlueRecords resp.additional
          let slist' : S := SlistFromNameSpec.setUpAddresses (NS := NS) nsNames glue mc
          .goto .findServers { s with
            resources := { s.resources with slist := slist', cache := cache'' }
            lastResponse := none }
        -- RFC 2308 §2.2 NODATA, TYPE 2/3: authority has SOA but no NS records
        -- ("NODATA is indicated by an answer with the RCODE set to NOERROR
        -- and no relevant answers" — `nodata_indicated`). The empty NOERROR
        -- response IS the answer; the shim caches it negatively.
        else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty then
          .answer (finalizeAnswer s resp)
        else .error "4b: no NS records in authority"
      -- 4a: answer or name error → return the response with the accumulated
      -- CNAME chain prepended. Condition matches guard_answerOrNameError
      -- (answer.size > 0 ∨ rcode = nameError) so that responseHandled covers
      -- the branch space (step_analyzeResponse_coverage).
      else if !resp.answer.isEmpty || resp.header.rcode == Rcode.nameError then
        .answer (finalizeAnswer s resp)
      -- RFC 2308 NODATA with empty authority (TYPE 3-ish)
      else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty then
        .answer (finalizeAnswer s resp)
      -- Truncated and unclassifiable: return to the client with TC set so it
      -- can retry over TCP (RFC 1035 §4.2.1); never cached (§7.4)
      else if resp.header.tc == 1 then
        .answer (finalizeAnswer s resp)
      else .error "unhandled response type"

def step (s : State S C NS RR) : StepResult S C NS RR :=
  match s.currentStep with
  | .checkAnswer => stepCheckLocal s
  | .findServers => stepFindServers s
  | .sendQueries => stepSendQueries s
  | .analyzeResponse => stepAnalyzeResponse s

/-- Build a fresh query message for the current SNAME.
    Used by the IO shim instead of replaying the client query. -/
def buildSubQuery (s : State S C NS RR) : Option Format :=
  match s.lastQuery with
  | none => none
  | some origQuery =>
    match origQuery.question[0]? with
    | none => none
    | some qu =>
      some {
        header := { origQuery.header with
          qr := 0
          qdcount := BitVec.ofNat 16 1
          ancount := 0
          nscount := 0
          arcount := 0 }
        question := #[{ qname := s.resources.sname, qtype := qu.qtype, qclass := qu.qclass }]
        answer := #[]
        authority := #[]
        additional := #[] }

/-- Initialize resolver state from a query message with a pre-built SBELT.
    `now` is the resolution start time; `initCache` seeds a persistent cache. -/
def initFromQuery (q : Format) (sbelt : S) (now : UInt32 := 0)
    (initCache : C := default) : State S C NS RR :=
  let sname := match q.question[0]? with
    | some qu => qu.qname
    | none => ByteArray.empty
  { resources := {
      sname := sname
      stype := default
      sclass := default
      slist := default
      sbelt := sbelt
      cache := initCache
    }
    currentStep := .checkAnswer
    lastQuery := some q
    lastResponse := none
    cnameChain := #[]
    now := now }

/-- Result of a resolver run: either done with a response or paused waiting for IO. -/
inductive ResolveYield (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where
  | done (resp : Format)
  | paused (state : State S C NS RR)

/-- Run the resolver with fuel-bounded iteration.
    Returns `.paused` when the resolver needs IO (network query). -/
def resolve (query : Format) (sbelt : S) (fuel : Nat := 64) (now : UInt32 := 0)
    (initCache : C := default)
    : Except String (ResolveYield S C NS RR) :=
  loop (initFromQuery query sbelt now initCache) fuel
where
  loop (s : State S C NS RR) : Nat → Except String (ResolveYield S C NS RR)
    | 0 => .error "resolver: max iterations"
    | n + 1 => match step s with
      | .answer resp => .ok (.done resp)
      | .goto nextStep s' => loop { s' with currentStep := nextStep } n
      | .needsIO s' => .ok (.paused s')
      | .error msg => .error msg

/-- Resume a paused resolver with a response from IO. -/
def resume (s : State S C NS RR) (resp : Format) (fuel : Nat := 64)
    : Except String (ResolveYield S C NS RR) :=
  let s' := { s with lastResponse := some resp }
  resolve.loop s' fuel

end VeriDNS.Impl.Resolver
