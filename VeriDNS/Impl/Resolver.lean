import VeriDNS.Impl.Message
import VeriDNS.Impl.ResourceRecord
import VeriDNS.Impl.DomainName
import VeriDNS.Impl.Edns
import VeriDNS.Impl.AnswerScrub
import VeriDNS.Spec.Resolver
import VeriDNS.Spec.NegativeCache
import VeriDNS.Spec.Credibility
import VeriDNS.Spec.Classify

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

  cnameChain : Array ByteArray := #[]

  /-- RFC 6891 §6.2.2 (finding 055): set once an upstream answers FORMERR to
      an OPT-bearing sub-query; every subsequent sub-query of this resolution
      is built WITHOUT the OPT record (see `buildSubQuery`), so the retry to
      that server (and its siblings) is EDNS-free instead of FORMERR-looping
      to SERVFAIL. -/
  noEdns : Bool := false

  now : UInt32 := 0
  deriving Inhabited

inductive StepResult (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where

  | answer (response : Format) (state : State S C NS RR)
  | «goto» (step : AlgorithmStep) (state : State S C NS RR)
  | needsIO (state : State S C NS RR)
  | error (msg : String)

def extractNsNames [RRParse RR] (authority : Array ByteArray) : Array ByteArray :=
  let nsType : BitVec 16 := BitVec.ofNat 16 2
  authority.filterMap fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => if RRParse.rrType rr == nsType then some (RRParse.rrRdata rr) else none
    | none => none

def extractCname [RRParse RR] (sname : ByteArray) (answer : Array ByteArray) : Option ByteArray :=
  answer.findSome? fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr =>
      if RRParse.rrType rr == (5 : BitVec 16) && DomainName.nameEqCI (RRParse.rrName rr) sname
      then some (RRParse.rrRdata rr) else none
    | none => none

def extractCnameRR [RRParse RR] (sname : ByteArray) (answer : Array ByteArray) : Option ByteArray :=
  answer.find? fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => RRParse.rrType rr == (5 : BitVec 16) && DomainName.nameEqCI (RRParse.rrName rr) sname
    | none => false

def prependCnameLink [RRParse RR] (chain : Array ByteArray) (resp : Format) : Array ByteArray :=
  match resp.question[0]? with
  | some qu =>
    match extractCnameRR (RR := RR) qu.qname resp.answer with
    | some cnBytes => chain.push cnBytes
    | none => chain
  | none => chain

def hasRRTypeIn [RRParse RR] (rrs : Array ByteArray) (code : BitVec 16) : Bool :=
  rrs.any fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => RRParse.rrType rr == code
    | none => false

def answersQueryB [RRParse RR] (resp : Format) : Bool :=
  match resp.question[0]? with
  | some qu => hasRRTypeIn (RR := RR) resp.answer qu.qtype
  | none => false

/-- A response *actually* answers the query when it carries a record of the
    query type whose owner lies on the CNAME chain rooted at the query name —
    i.e. an ENTITLED answer record (RFC 1034 §4.3.2; the `Entitled .answer`
    relation of `Spec/Entitlement.lean`).  A response whose answer records are
    all off-owner (foreign / not on the chain) is NOT an answer: it scrubs to
    empty at delivery, so accepting it would manufacture a spurious NODATA for
    a name whose status is actually unresolved.  This is the acceptance-layer
    tightening for findings 036 (off-owner CNAME) and off-owner-A: a foreign
    answer fails to answer and the resolver keeps resolving (retry) rather than
    accepting-then-scrubbing-to-NODATA. -/
def entitledAnswerB [RRParse RR] (resp : Format) : Bool :=
  match resp.question[0]? with
  | some qu =>
    let reach := reachableNamesB (RR := RR) qu.qname resp.answer
    resp.answer.any fun bytes =>
      match RRParse.parseRaw (RR := RR) bytes with
      | some rr => RRParse.rrType rr == qu.qtype && nameMemB (RRParse.rrName rr) reach
      | none => false
  | none => false

/-- `entitledAnswerB` refines `answersQueryB`: an entitled answer is in
    particular a type-matching answer (drop the owner conjunct). -/
theorem answersQueryB_of_entitled [RRParse RR] (resp : Format)
    (h : entitledAnswerB (RR := RR) resp = true) : answersQueryB (RR := RR) resp = true := by
  unfold entitledAnswerB at h
  unfold answersQueryB
  split at h
  · next qu _ =>
    simp only at h
    unfold hasRRTypeIn
    rw [Array.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbe⟩ := h
    refine ⟨b, hb, ?_⟩
    split at hbe
    · next rr hpr => exact (Bool.and_eq_true _ _ |>.mp hbe).1
    · next => exact absurd hbe (by simp)
  · next => exact absurd h (by simp)

/-- A response is an ENTITLED answer if some answer record has the query type
    and is owned (case-insensitively) at the query name — the query name is
    always the root of the CNAME-chain closure (`qname_mem_reachableNamesB`).
    The honest-answer witness for the off-owner acceptance guard. -/
theorem entitledAnswerB_of_owned_qtype [RRParse RR] (resp : Format)
    (qu : Question) (hq : resp.question[0]? = some qu)
    (b : ByteArray) (rr : RR) (hb : b ∈ resp.answer)
    (hpr : RRParse.parseRaw (RR := RR) b = some rr)
    (hty : (RRParse.rrType rr == qu.qtype) = true)
    (hown : DomainName.nameEqCI (RRParse.rrName rr) qu.qname = true) :
    entitledAnswerB (RR := RR) resp = true := by
  unfold entitledAnswerB
  rw [hq, Array.any_eq_true']
  refine ⟨b, hb, ?_⟩
  rw [hpr, Bool.and_eq_true]
  refine ⟨hty, ?_⟩
  unfold nameMemB
  rw [Array.any_eq_true']
  exact ⟨qu.qname, qname_mem_reachableNamesB _ _, hown⟩

def cnameToChase [RRParse RR] (resp : Format) : Option ByteArray :=
  if answersQueryB (RR := RR) resp then none
  else match resp.question[0]? with
    | some qu => extractCname (RR := RR) qu.qname resp.answer
    | none => none

def echoedQname (resp : Format) : ByteArray :=
  (resp.question[0]?).elim ByteArray.empty (·.qname)

def suffixMatchCount (a b : Array ByteArray) : Nat := Id.run do
  let mut n := 0
  for i in [:min a.size b.size] do

    if n == i && DomainName.nameEqCI a[a.size - 1 - i]! b[b.size - 1 - i]! then
      n := n + 1
  return n

def isAncestorB (bw owner : ByteArray) : Bool :=
  match DomainName.wireFormatToLabels bw, DomainName.wireFormatToLabels owner with
  | .ok bwL, .ok ownerL =>
    let b := bwL.toList.map DomainName.foldNameCase
    let o := ownerL.toList.map DomainName.foldNameCase
    decide (b.length ≤ o.length) && decide (b = o.drop (o.length - b.length))
  | _, _ => false

def bailiwickRaws [RRParse RR] (bw : ByteArray) (raws : Array ByteArray) : Array ByteArray :=
  raws.filter fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => isAncestorB bw (RRParse.rrName rr)
    | none => false

theorem bailiwickRaws_subset [RRParse RR] (bw : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} (h : b ∈ (bailiwickRaws (RR := RR) bw raws).toList) :
    b ∈ raws.toList := by
  have h' : b ∈ bailiwickRaws (RR := RR) bw raws := Array.mem_def.mpr h
  unfold bailiwickRaws at h'
  exact Array.mem_def.mp (Array.mem_filter.mp h').1

theorem bailiwickRaws_owner_inBailiwick [RRParse RR] (bw : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} {rr : RR} (hb : b ∈ (bailiwickRaws (RR := RR) bw raws).toList)
    (hpr : RRParse.parseRaw (RR := RR) b = some rr) :
    isAncestorB bw (RRParse.rrName rr) = true := by
  have hbf : b ∈ bailiwickRaws (RR := RR) bw raws := Array.mem_def.mpr hb
  unfold bailiwickRaws at hbf
  have hp := (Array.mem_filter.mp hbf).2
  simp only [hpr] at hp
  exact hp

def ownerRaws [RRParse RR] (sname : ByteArray) (raws : Array ByteArray) : Array ByteArray :=
  raws.filter fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => DomainName.nameEqCI (RRParse.rrName rr) sname
    | none => false

theorem ownerRaws_subset [RRParse RR] (sname : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} (h : b ∈ (ownerRaws (RR := RR) sname raws).toList) :
    b ∈ raws.toList := by
  have h' : b ∈ ownerRaws (RR := RR) sname raws := Array.mem_def.mpr h
  unfold ownerRaws at h'
  exact Array.mem_def.mp (Array.mem_filter.mp h').1

theorem ownerRaws_owner_eq [RRParse RR] (sname : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} {rr : RR} (hb : b ∈ (ownerRaws (RR := RR) sname raws).toList)
    (hpr : RRParse.parseRaw (RR := RR) b = some rr) :
    DomainName.nameEqCI (RRParse.rrName rr) sname = true := by
  have hbf : b ∈ ownerRaws (RR := RR) sname raws := Array.mem_def.mpr hb
  unfold ownerRaws at hbf
  have hp := (Array.mem_filter.mp hbf).2
  simp only [hpr] at hp
  exact hp

/-- Finding 019: the cache slice of a chased-CNAME response — ONLY the
    qname-owned CNAME records (the chase link).  `ownerRaws` restricted with a
    type conjunct: a same-owner record of any OTHER type riding a CNAME
    response never enters the cache through the chase arm (the delivery side
    already restricts to the chased link, `prependCnameLink`).  The predicate
    is exactly `extractCname`/`extractCnameRR`'s, so the cached slice is the
    chase-link image. -/
def cnameRaws [RRParse RR] (sname : ByteArray) (raws : Array ByteArray) : Array ByteArray :=
  raws.filter fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => RRParse.rrType rr == (5 : BitVec 16)
        && DomainName.nameEqCI (RRParse.rrName rr) sname
    | none => false

theorem cnameRaws_subset [RRParse RR] (sname : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} (h : b ∈ (cnameRaws (RR := RR) sname raws).toList) :
    b ∈ raws.toList := by
  have h' : b ∈ cnameRaws (RR := RR) sname raws := Array.mem_def.mpr h
  unfold cnameRaws at h'
  exact Array.mem_def.mp (Array.mem_filter.mp h').1

theorem cnameRaws_pred [RRParse RR] (sname : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} {rr : RR} (hb : b ∈ (cnameRaws (RR := RR) sname raws).toList)
    (hpr : RRParse.parseRaw (RR := RR) b = some rr) :
    (RRParse.rrType rr == (5 : BitVec 16)
      && DomainName.nameEqCI (RRParse.rrName rr) sname) = true := by
  have hbf : b ∈ cnameRaws (RR := RR) sname raws := Array.mem_def.mpr hb
  unfold cnameRaws at hbf
  have hp := (Array.mem_filter.mp hbf).2
  simp only [hpr] at hp
  exact hp

theorem cnameRaws_owner_eq [RRParse RR] (sname : ByteArray) (raws : Array ByteArray)
    {b : ByteArray} {rr : RR} (hb : b ∈ (cnameRaws (RR := RR) sname raws).toList)
    (hpr : RRParse.parseRaw (RR := RR) b = some rr) :
    DomainName.nameEqCI (RRParse.rrName rr) sname = true :=
  (Bool.and_eq_true _ _ |>.mp (cnameRaws_pred (RR := RR) sname raws hb hpr)).2

def referralCutRaw [RRParse RR] (authority : Array ByteArray) : ByteArray :=
  match authority.findSome? (fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => if RRParse.rrType rr == (2 : BitVec 16) then some (RRParse.rrName rr) else none
    | none => none) with
  | some owner => owner
  | none => ByteArray.empty

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

def prependChain (chain : Array ByteArray) (resp : Format) : Format :=
  if chain.isEmpty then resp
  else { resp with
    answer := chain ++ resp.answer
    header := { resp.header with
      ancount := BitVec.ofNat 16 (chain.size + resp.answer.size) } }

def finalizeAnswer (s : State S C NS RR) (resp : Format) : Format :=
  let withChain := prependChain s.cnameChain resp
  match s.lastQuery with
  | none => withChain
  | some q => { withChain with
      question := q.question
      header := { withChain.header with qdcount := BitVec.ofNat 16 q.question.size } }

def credAnswer (aa : Bool) : Trustworthiness :=
  if aa then .authoritativeSection else .sectionNonauthoritative
def credAuthority (aa : Bool) : Trustworthiness :=
  if aa then .authoritySection else .additionalAuthoritative
def credAdditional : Trustworthiness := .additionalAuthoritative

def cacheRRs [TrustworthinessSpec C RR] [RRParse RR] (cache : C) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) : C :=
  raws.foldl (fun c bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => TrustworthinessSpec.acceptRrset c rr cred now | none => c) cache

def cacheUnlessTruncated [TrustworthinessSpec C RR] [RRParse RR] (cache : C) (resp : Format)
    (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32) : C :=
  if resp.header.tc == 1 then cache
  else cacheRRs (RR := RR) cache (RRParse.normalizeSection (RR := RR) raws) cred now

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

def negativeResponse [RRParse RR] (q : Format) (rc : Rcode) (soaAuth : Array RR) : Format :=
  { header := { q.header with
      qr := 1, rcode := rc
      ancount := 0, nscount := BitVec.ofNat 16 soaAuth.size, arcount := 0 }
    question := q.question
    answer := #[], authority := soaAuth.map RRParse.rrBytes, additional := #[] }

def cacheResponse [RRParse RR] (q : Format) (rrs : Array RR) : Format :=
  { header := { q.header with
      qr := 1, rcode := Rcode.noError
      ancount := BitVec.ofNat 16 rrs.size, nscount := 0, arcount := 0 }
    question := q.question
    answer := rrs.map RRParse.rrBytes
    authority := #[], additional := #[] }

inductive LocalResult (RR : Type) where

  | negative (rc : Rcode) (soaAuth : Array RR) (chain : Array ByteArray)
  | answerHit (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
  | miss (sname : ByteArray) (chain : Array ByteArray)

  | abort

def cnameChaseVisited [RRParse RR] (qname0 : ByteArray) (chain : Array ByteArray) : Array ByteArray :=
  #[qname0] ++ chain.filterMap (fun b => (RRParse.parseRaw (RR := RR) b).map RRParse.rrRdata)

def localAnswer [TrustworthinessSpec C RR] [NegativeAuthoritySpec C RR] [RRParse RR] (cache : C)
    (qtype qclass : BitVec 16) (now : UInt32)
    : Nat → ByteArray → Array ByteArray → Array ByteArray → LocalResult RR
  | 0, _sname, _chain, _visited => .abort
  | fuel + 1, sname, chain, visited =>
    match NegativeCacheSpec.retrieveNegative cache sname qtype qclass now with
    | some rc =>
      .negative rc (NegativeAuthoritySpec.authoritySection cache sname qtype qclass now) chain
    | none =>

      let rrs : Array RR := TrustworthinessSpec.answers cache sname qtype qclass now
      if rrs.isEmpty then
        if qtype == (5 : BitVec 16) then .miss sname chain
        else
          match (TrustworthinessSpec.answers cache sname (5 : BitVec 16) qclass now
              : Array RR)[0]? with
          | some crr =>

            let tgt := RRParse.rrRdata crr
            if visited.any (fun v => DomainName.nameEqCI v tgt) then .miss sname chain
            else
              localAnswer cache qtype qclass now fuel
                tgt (chain.push (RRParse.rrBytes crr)) (visited.push tgt)
          | none => .miss sname chain
      else .answerHit sname chain rrs

def stepCheckLocal (s : State S C NS RR) : StepResult S C NS RR :=
  match s.lastQuery with
  | none => .goto .findServers s
  | some q =>
    match q.question[0]? with
    | none => .goto .findServers s
    | some qu =>
      match localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
          s.now 8 s.resources.sname s.cnameChain
          (cnameChaseVisited (RR := RR) qu.qname s.cnameChain) with
      | .negative rc soaAuth chain =>
        .answer (finalizeAnswer { s with cnameChain := chain } (negativeResponse q rc soaAuth))
          { s with cnameChain := chain }
      | .answerHit _ chain rrs =>

        .answer (finalizeAnswer { s with cnameChain := chain } (cacheResponse q rrs))
          { s with cnameChain := chain }
      | .miss sname' chain =>
        if sname' == s.resources.sname then .goto .findServers s
        else
          .goto .findServers { s with
            resources := { s.resources with sname := sname', slist := default }
            cnameChain := chain }
      | .abort => .error "cname chain too long"

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

      let aType : BitVec 16 := BitVec.ofNat 16 1

      let glue : Array (ByteArray × BitVec 32) := nsNames.flatMap fun nsName =>
        let aRRs : Array RR := CacheSpec.lookupTopCred s.resources.cache nsName aType inClass s.now
        aRRs.filterMap fun rr =>
          let rd := RRParse.rrRdata rr
          if rd.size == 4 then
            let addr : BitVec 32 :=
              (rd.data[0]!.toBitVec.setWidth 32 <<< 24) |||
              (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
              (rd.data[2]!.toBitVec.setWidth 32 <<< 8) |||
              rd.data[3]!.toBitVec.setWidth 32
            some (nsName, addr)
          else none
      if glue.isEmpty && mc == 0 then
        .goto .sendQueries { s with resources := { s.resources with
          slist := s.resources.sbelt } }
      else
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
      let rrs : Array RR := CacheSpec.lookupTopCred cache name nsType inClass now
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

def stepSendQueries (s : State S C NS RR) : StepResult S C NS RR :=
  match s.lastResponse with
  | some _ => .goto .analyzeResponse s
  | none => .needsIO s

def classifiableB (resp : Format) : Bool :=
  !resp.answer.isEmpty
    || resp.header.rcode == Rcode.nameError
    || !resp.authority.isEmpty
    || resp.header.rcode == Rcode.noError
    || resp.header.tc == 1

/-- The SOA record type code (RFC 1035 §3.3.13). -/
def soaTypeCode : BitVec 16 := 6

/-- A response carries a *valid negative proof* for `qname` when its authority
    section contains an SOA record owned by an ancestor (the zone apex) of
    `qname`.  RFC 2308 §2.2: a NODATA answer "will contain an SOA record" that
    proves the negative from the zone apex.  Without it, an empty NOERROR is a
    "bizarre contents" response (RFC 1034 §4.3.2.d) or an ambiguous NODATA
    TYPE 3 (RFC 2308 §2.2, l.287-290) that must be re-queried, not synthesised
    into a believed NODATA. -/
def hasSoaAuthorityFor [RRParse RR] (qname : ByteArray) (authority : Array ByteArray) : Bool :=
  authority.any fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => RRParse.rrType rr == soaTypeCode && isAncestorB (RRParse.rrName rr) qname
    | none => false

/-- The RFC 1034 §4.3.2 / RFC 2308 §2 classification of a received response,
    computed on exactly the conditions `stepAnalyzeResponse` branches on (see
    `classifyResponse_stepAnalyze` for the refinement).  Total.  A `nodata`
    verdict requires a valid negative proof (SOA in authority owned by an
    ancestor of the query name); an empty response without one is `retry`. -/
def classifyResponse [RRParse RR] (qname : ByteArray) (resp : Format) : Spec.ClassOutcome :=
  match cnameToChase (RR := RR) resp with
  | some _ => .cname
  | none =>
    if resp.header.rcode == Rcode.serverFailure || !classifiableB resp then .retry
    else if !answersQueryB (RR := RR) resp
        && !(resp.header.rcode == Rcode.nameError)
        && resp.answer.isEmpty
        && !resp.authority.isEmpty then
      if hasRRTypeIn (RR := RR) resp.authority 2
          && resp.header.aa == 0
          && resp.header.rcode == Rcode.noError
          && !hasRRTypeIn (RR := RR) resp.authority 6 then .referral
      else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty
          && hasSoaAuthorityFor (RR := RR) (echoedQname resp) resp.authority then .nodata
      else .retry
    else if entitledAnswerB (RR := RR) resp then .answer
    else if resp.header.rcode == Rcode.nameError then .nameError
    else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty
        && hasSoaAuthorityFor (RR := RR) (echoedQname resp) resp.authority then .nodata
    else if resp.header.tc == 1 then .answer
    else .retry

def stepAnalyzeResponse (s : State S C NS RR) : StepResult S C NS RR :=
  match s.lastResponse with
  | none => .error "no response to analyze"
  | some resp =>

    match cnameToChase (RR := RR) resp with
    | some canonicalName =>
      let qname0 : ByteArray := (s.lastQuery.bind (fun q => q.question[0]?)).elim
        s.resources.sname (fun qu => qu.qname)

      if resp.header.tc == 1 then
        .answer (finalizeAnswer s resp) s

      else if (cnameChaseVisited (RR := RR) qname0 s.cnameChain).any
          (fun v => DomainName.nameEqCI v canonicalName) then
        .error "cname loop detected"
      else
        -- Finding 019: cache ONLY the chased CNAME link (`cnameRaws`), not
        -- every qname-owned record of any type — a junk same-owner record
        -- riding a CNAME response must not enter the cache through the chase
        -- arm (mirrors `prependCnameLink` on the delivery side; model twin:
        -- `Response.cnameOwned` in the `answerCname`/`trustedCname` rules).
        let cache' := cacheUnlessTruncated (RR := RR) s.resources.cache resp
          (cnameRaws (RR := RR) (echoedQname resp) resp.answer)
          (credAnswer (resp.header.aa == 1)) s.now

        .goto .checkAnswer { s with
          resources := { s.resources with
            sname := canonicalName, cache := cache', slist := default }
          cnameChain := prependCnameLink (RR := RR) s.cnameChain resp
          lastResponse := none }
    | none =>

      if resp.header.rcode == Rcode.serverFailure || !classifiableB resp then
        .goto .sendQueries { s with lastResponse := none }

      else if !answersQueryB (RR := RR) resp
          && !(resp.header.rcode == Rcode.nameError)
          && resp.answer.isEmpty
          && !resp.authority.isEmpty then

        if hasRRTypeIn (RR := RR) resp.authority 2
            && resp.header.aa == 0
            && resp.header.rcode == Rcode.noError
            && !hasRRTypeIn (RR := RR) resp.authority 6 then

          let cut := referralCutRaw (RR := RR) resp.authority

          let nsNames := extractNsNames (RR := RR) (ownerRaws (RR := RR) cut resp.authority)
          let cache' := cacheUnlessTruncated (RR := RR) s.resources.cache resp
            (bailiwickRaws (RR := RR) cut resp.authority)
            (credAuthority (resp.header.aa == 1)) s.now
          let cache'' := cacheUnlessTruncated (RR := RR) cache' resp
            (bailiwickRaws (RR := RR) cut resp.additional)
            credAdditional s.now

          let mc : Nat := delegationMatchCount (RR := RR) resp.authority s.resources.sname

          let glue := extractGlueRecords (bailiwickRaws (RR := RR) cut resp.additional)
          let slist' : S := SlistFromNameSpec.setUpAddresses (NS := NS) nsNames glue mc
          .goto .findServers { s with
            resources := { s.resources with slist := slist', cache := cache'' }
            lastResponse := none }

        else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty
            && hasSoaAuthorityFor (RR := RR) (echoedQname resp) resp.authority then
          .answer (finalizeAnswer s resp) s
        else
          .goto .sendQueries { s with lastResponse := none }

      else if entitledAnswerB (RR := RR) resp then

        let cache' := cacheUnlessTruncated (RR := RR) s.resources.cache resp
          (ownerRaws (RR := RR) (echoedQname resp) resp.answer)
          (credAnswer (resp.header.aa == 1)) s.now
        .answer (finalizeAnswer s resp)
          { s with resources := { s.resources with cache := cache' } }

      else if resp.header.rcode == Rcode.nameError && resp.answer.isEmpty then
        .answer (finalizeAnswer s resp) s

      else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty
          && hasSoaAuthorityFor (RR := RR) (echoedQname resp) resp.authority then
        .answer (finalizeAnswer s resp) s

      else if resp.header.tc == 1 then
        .answer (finalizeAnswer s resp) s
      -- A foreign non-empty answer (not entitled, not NXDOMAIN, no SOA proof,
      -- not truncated) is NOT accepted: it scrubs to empty at delivery, so
      -- accepting it would manufacture a spurious NODATA (findings 036 /
      -- off-owner-A).  A `nameError` (NXDOMAIN) carrying ANY answer record is
      -- likewise contradictory — a genuine NXDOMAIN has no answer — so a
      -- non-empty NXDOMAIN (e.g. a spoofed junk answer) is not delivered either;
      -- both keep resolving (retry).
      else
        .goto .sendQueries { s with lastResponse := none }

def step (s : State S C NS RR) : StepResult S C NS RR :=
  match s.currentStep with
  | .checkAnswer => stepCheckLocal s
  | .findServers => stepFindServers s
  | .sendQueries => stepSendQueries s
  | .analyzeResponse => stepAnalyzeResponse s

def maxMinimiseSteps : Nat := 10

def probeRoundB (sname : ByteArray) (revealed : Nat) : Bool :=
  decide (0 < revealed) && decide (revealed < DomainName.labelCount sname)

def subQuestion (sname : ByteArray) (revealed : Nat) (qu : Question) : Question :=
  if probeRoundB sname revealed then
    { qname := DomainName.minimisedName sname revealed
      qtype := BitVec.ofNat 16 1
      qclass := qu.qclass }
  else
    { qname := sname, qtype := qu.qtype, qclass := qu.qclass }

def bumpRevealed (sname : ByteArray) (revealed : Nat) : Nat :=
  if maxMinimiseSteps ≤ revealed then DomainName.labelCount sname else revealed + 1

def buildSubQuery (s : State S C NS RR) (revealed : Nat) : Option Format :=
  match s.lastQuery with
  | none => none
  | some origQuery =>
    match origQuery.question[0]? with
    | none => none
    | some qu =>
      some {
        header := { origQuery.header with
          qr := 0
          opcode := VeriDNS.Spec.Opcode.query
          rd := 0
          qdcount := BitVec.ofNat 16 1
          ancount := 0
          nscount := 0
          -- RFC 6891 §6.2.2 (055): after an upstream FORMERR to an
          -- OPT-bearing sub-query, advertise no EDNS at all.
          arcount := if s.noEdns then 0 else 1 }
        question := #[subQuestion s.resources.sname revealed qu]
        answer := #[]
        authority := #[]
        additional := if s.noEdns then #[] else #[Edns.optRRBytes Edns.advertisedUdpSize] }

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

inductive ResolveYield (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where

  | done (resp : Format) (state : State S C NS RR)
  | paused (state : State S C NS RR)

def resolve (query : Format) (sbelt : S) (fuel : Nat := 64) (now : UInt32 := 0)
    (initCache : C := default)
    : Except String (ResolveYield S C NS RR) :=
  loop (initFromQuery query sbelt now initCache) fuel
where
  loop (s : State S C NS RR) : Nat → Except String (ResolveYield S C NS RR)
    | 0 => .error "resolver: max iterations"
    | n + 1 => match step s with
      | .answer resp stF => .ok (.done resp stF)
      | .goto nextStep s' => loop { s' with currentStep := nextStep } n
      | .needsIO s' => .ok (.paused s')
      | .error msg => .error msg

def resume (s : State S C NS RR) (resp : Format) (fuel : Nat := 64)
    : Except String (ResolveYield S C NS RR) :=
  let s' := { s with lastResponse := some resp }
  resolve.loop s' fuel

end VeriDNS.Impl.Resolver
