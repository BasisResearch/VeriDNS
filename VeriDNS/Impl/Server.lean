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

/-- The canonical question echo of a gate/error reply (033): at most the FIRST
    question is echoed back, with `qdcount` matching. A multi-question query is
    FORMERRed (`interpretableQuery`), and its FORMERR reply must not amplify the
    client's stuffing by reflecting every question — unbound reflects the raw
    packet here; we deliberately echo only the safe prefix (the one question a
    legitimate client matches replies on). -/
def trimQuestion (query : Format) : Format :=
  { query with
    question := query.question.extract 0 1
    header := { query.header with
      qdcount := BitVec.ofNat 16 (query.question.extract 0 1).size } }

def buildErrorResponse (query : Format) (rcode : Rcode) : Format :=
  buildResponse (trimQuestion query) rcode #[] #[] #[]

/-- Finalize a reply for the client. `tc := 0` is the (032) no-echo pin: TC on a
    client-bound reply may only ever be set by `truncateUdp` (i.e. TC is exactly
    the truncation flag), never inherited from the client's query or an upstream
    response — every client-bound reply passes through here before `truncateUdp`
    decides truncation. -/
def finalizeForClient (resp : Format) : Format :=

  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, tc := 0, z := 0 } }

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

/-- Upstream-response admissibility (RFC 5452 §4.2–4.4 + RFC 1035 §4.1.1):
the reply must echo the transaction id and the (0x20-cased) question section,
AND it must actually be shaped like a response to the query we sent — QR=1
(a query reflected back is not a response) and OPCODE echoing the standard
QUERY opcode of every query this resolver originates.  A datagram with QR=0
or a non-QUERY opcode is never accepted (finding 030). -/
def acceptResponse (sent : Format) (resp : Format) : Option Format :=
  if resp.header.id == sent.header.id
      && questionMatches resp.question sent.question
      && resp.header.qr == 1
      && resp.header.opcode == Opcode.query then
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

/-- The client's query type (first question).  The `0` fallback for a
    question-less query is a type code no record carries, so the 068 delivery
    filter fails closed. -/
def clientQtype (query : Format) : BitVec 16 :=
  (query.question[0]?).elim 0 (·.qtype)

def scrubAuthorityB (qname : ByteArray) (authority : Array ByteArray) : Array ByteArray :=
  authority.filter fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) => Resolver.isAncestorB rr.name qname
    | .error _ => false

/-- Scrub the delivered ADDITIONAL section to entitled records only (047).
An additional record delivered to the client is entitled iff its owner lies
in the bailiwick of the query name (RFC 2181 §5.4.1 / the delegation-glue
role of `VeriDNS.Spec.Net.Entitled`): an off-cut / foreign additional record
(e.g. glue for a name the delegation never named) is dropped before it reaches
the client. This mirrors `scrubAuthorityB`; an unparseable record is dropped
fail-closed. -/
def scrubAdditionalB (qname : ByteArray) (additional : Array ByteArray) : Array ByteArray :=
  additional.filter fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) => Resolver.isAncestorB qname rr.name
    | .error _ => false

/-- RFC 2308 negative-cache trigger, in lockstep with the model
    `Spec.Net.Cache.absorbNeg` (see `negativelyCacheable_iff_absorbNeg_trigger`).
    Both arms require an EMPTY answer section (finding 039, RFC 6604 §3): an
    NXDOMAIN that terminates a CNAME chase reaches this point with the chain
    prepended to the answer (`finalizeAnswer`), and the nonexistence it proves
    is of the CHAIN-FINAL target, not the original query name (which exists —
    it owns a CNAME).  Caching such a response name-wide at the echoed qname
    would deny every other type of a name that exists (matches unbound, which
    keys chained negatives at the chain-final target only). -/
def negativelyCacheable (resp : Format) : Bool :=
  resp.header.tc == 0
    && ((resp.header.rcode == Rcode.nameError && resp.answer.isEmpty)
        || (resp.header.rcode == Rcode.noError && resp.answer.isEmpty))

def supportsQueryKind (q : Format) : Bool :=
  q.header.opcode == Opcode.query

def interpretableQuery (q : Format) : Bool :=
  q.question.size == 1

/-- Gate (032): a query with the TC bit set is malformed. TC is meaningful only
    on responses (RFC 1035 §4.1.1: "specifies that this message was truncated"
    describes the *replier's* message); a request arriving with TC=1 is either
    junk or the un-retried tail of somebody else's truncation. unbound parity
    (1.24.2, `worker_check_request`): TC-set request → FORMERR, with TC cleared
    in the reply (see `finalizeForClient`). -/
def tcClear (q : Format) : Bool :=
  q.header.tc == 0

/-- Gate (042), additional-section shape: a query's additional section is either
    empty or exactly one EDNS OPT record (RFC 6891 §6.1.1 — at most one OPT,
    which is the only record a QUERY legitimately carries there). unbound parity:
    a non-OPT additional record or a second additional record → FORMERR. -/
def additionalQueryShaped (q : Format) : Bool :=
  match q.additional[0]? with
  | none => true
  | some b => q.additional.size == 1 && Edns.isOptRR b

/-- Gate (042): RFC 1035 §4.1 — a standard QUERY carries empty answer and
    authority sections. A query arriving with stuffed sections is malformed
    (and historically a cache-poisoning conduit); unbound FORMERRs these. -/
def sectionsQueryShaped (q : Format) : Bool :=
  q.answer.isEmpty && q.authority.isEmpty && additionalQueryShaped q

/-- Zone-transfer QTYPEs (044b): AXFR=252 (RFC 5936) and IXFR=251 (RFC 1995).
    A recursive resolver has no zone to transfer, so these are declined as a
    matter of local policy → REFUSED. unbound parity (verified against 1.24.2:
    `dig AXFR`/`IXFR` → REFUSED). -/
def zoneTransferQtype (t : BitVec 16) : Bool :=
  t == 252 || t == 251

/-- Meta-QTYPEs that cannot be asked as questions (044b): OPT=41 is not a query
    type (RFC 6891 §6.1.1 — it lives in the additional section only); TKEY=249 /
    TSIG=250 / MAILB=253 / MAILA=254 and the reserved meta range 128–248 are
    likewise not resolvable RR types. Such a question is malformed → FORMERR.
    unbound parity (verified against 1.24.2: all of these → FORMERR). Excludes
    ANY=255 (served via the RFC 8482 arm) and AXFR/IXFR (REFUSED, see
    `zoneTransferQtype`). -/
def metaQtype (t : BitVec 16) : Bool :=
  t == 41 || t == 253 || t == 254
    || (decide (128 ≤ t.toNat) && decide (t.toNat ≤ 250))

/-- Is the (guaranteed-present under `interpretableQuery`) first question a
    zone-transfer request? -/
def qtypeZoneTransfer (q : Format) : Bool :=
  match q.question[0]? with
  | some qu => zoneTransferQtype qu.qtype
  | none => false

/-- Does the first question carry a non-askable meta-QTYPE? -/
def qtypeMetaQuery (q : Format) : Bool :=
  match q.question[0]? with
  | some qu => metaQtype qu.qtype
  | none => false

def performsRequestedOperation (q : Format) : Bool :=
  q.header.rd == 1

/-- The QCLASS code for the Internet class (IN), RFC 1035 §3.2.4. -/
def inClassCode : BitVec 16 := BitVec.ofNat 16 1

/-- A recursive resolver serves only Internet-class (IN) queries; a query in
    any other class (e.g. CHAOS `version.bind`) is answered `REFUSED` as a
    matter of local policy, matching a stock recursive resolver (unbound).
    Guarded by `interpretableQuery` so `question[0]?` is `some`. -/
def queryClassSupported (q : Format) : Bool :=
  match q.question[0]? with
  | some qu => qu.qclass == inClassCode
  | none => false

/-- The total ingress query-shape classifier. Gate order (FORMERR shape gates,
    then NOTIMP, then policy REFUSEDs, then per-QTYPE gates) mirrors unbound's
    `worker_check_request` + `worker_handle_request` checks so that every
    single-dimension malformation gets the same rcode unbound gives it:

    1. multi- or zero-question → FORMERR (RFC 1035 §4.1.2 leniency limit)
    2. TC bit set → FORMERR (032)
    3. non-empty answer/authority, non-OPT additional → FORMERR (042)
    4. opcode ≠ QUERY → NOTIMP
    5. rd ≠ 1 → REFUSED (iterative service declined, local policy)
    6. qclass ≠ IN → REFUSED (local policy, e.g. CHAOS)
    7. qtype AXFR/IXFR → REFUSED (044b, no zone to transfer)
    8. qtype meta (OPT/TKEY/TSIG/MAILB/MAILA/128–248) → FORMERR (044b)

    `queryProblem_spec` (Proof/Server.lean) is the sound-and-complete
    characterization of this classifier. -/
def queryProblem (q : Format) : Option Rcode :=
  if !interpretableQuery q then some Rcode.formatError
  else if !tcClear q then some Rcode.formatError
  else if !sectionsQueryShaped q then some Rcode.formatError
  else if !supportsQueryKind q then some Rcode.notImplemented
  else if !performsRequestedOperation q then some Rcode.refused
  else if !queryClassSupported q then some Rcode.refused
  else if qtypeZoneTransfer q then some Rcode.refused
  else if qtypeMetaQuery q then some Rcode.formatError
  else none

/-- A served query (`queryProblem = none`) passed every gate: the full gate
    conjunction, read off the classifier. -/
theorem queryProblem_none_gates {q : Format} (h : queryProblem q = none) :
    interpretableQuery q = true ∧ tcClear q = true ∧ sectionsQueryShaped q = true
      ∧ supportsQueryKind q = true ∧ performsRequestedOperation q = true
      ∧ queryClassSupported q = true ∧ qtypeZoneTransfer q = false
      ∧ qtypeMetaQuery q = false := by
  unfold queryProblem at h
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  split at h; · exact absurd h (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-- A served query (`queryProblem = none`) is Internet-class: passing the gates
    includes `queryClassSupported`. -/
theorem queryProblem_none_class {q : Format} (h : queryProblem q = none) :
    queryClassSupported q = true :=
  (queryProblem_none_gates h).2.2.2.2.2.1

/-- The Internet-class gate, read off the question head: a served query's
    first question carries `qclass = inClassCode`. -/
theorem queryProblem_none_qclass {q : Format} {qu : VeriDNS.Spec.Question}
    (h : queryProblem q = none) (hqu : q.question[0]? = some qu) :
    qu.qclass = inClassCode := by
  have hc := queryProblem_none_class h
  unfold queryClassSupported at hc
  rw [hqu] at hc
  exact eq_of_beq (by simpa using hc)

/-- Reply for an EDNS-malformed query (RFC 6891), gated after `queryProblem`:
    * multiple OPT RRs → FORMERR (§6.1.1);
    * EDNS version > 0 → BADVERS (§6.1.3).  BADVERS is extended rcode 16 =
      high byte 1 in the response OPT's TTL, header rcode 0 (NOERROR) — the
      response honestly carries an OPT with the ext-rcode byte set and
      version 0, so the client can retry with version 0. -/
def ednsProblemResponse (q : Format) (ep : Edns.EdnsProblem) : Format :=
  match ep with
  | .multiOpt => finalizeForClient (buildErrorResponse q .formatError)
  | .badVersion =>
    finalizeForClient
      (buildResponse q .noError #[] #[] #[Edns.optRRBadVersBytes Edns.advertisedUdpSize])

/-! ## RFC 8482: minimal responses to QTYPE=ANY

A recursive resolver receiving a QTYPE=ANY query does not perform the full,
amplification-prone multi-type resolution.  Per RFC 8482 §4.2 it instead
returns a single synthesized HINFO RRset: CPU = "RFC8482", OS = the null string.
This is a serve-boundary decision — the synthesized answer is emitted before any
resolution, so the resolver core never sees an ANY query. -/

/-- The QTYPE code for a `*`/ANY query (RFC 1035 §3.2.3, QTYPE=255). -/
def anyQTypeCode : BitVec 16 := BitVec.ofNat 16 255

/-- The RR type code for HINFO (RFC 1035 §3.3.11, type 13). -/
def hinfoType : BitVec 16 := BitVec.ofNat 16 13

/-- The synthesized HINFO RDATA of RFC 8482 §4.2: two character-strings, the
    CPU field `"RFC8482"` (a length octet 7 followed by the 7 ASCII bytes) and
    the OS field the null string (a single length octet 0). -/
def rfc8482Rdata : ByteArray :=
  ⟨#[7, 0x52, 0x46, 0x43, 0x38, 0x34, 0x38, 0x32, 0]⟩

/-- The synthesized HINFO resource record of RFC 8482 §4.2, owned by `qname`. -/
def hinfoRFC8482RR (qname : ByteArray) : VeriDNS.Spec.ResourceRecord :=
  { name := qname
    type := hinfoType
    «class» := inClassCode
    ttl := BitVec.ofNat 32 3600
    rdlength := BitVec.ofNat 16 rfc8482Rdata.size
    rdata := rfc8482Rdata }

/-- Is this a QTYPE=ANY query?  Read off the (guaranteed-present under
    `interpretableQuery`) first question. -/
def isAnyQuery (q : Format) : Bool :=
  match q.question[0]? with
  | some qu => qu.qtype == anyQTypeCode
  | none => false

/-- The synthesized RFC 8482 minimal response to an ANY query: a NOERROR reply
    carrying exactly one HINFO answer RR (owned by the client's qname), the
    question echoed, and no authority/additional records.  Finalized for the
    client (QR=1, RA=1, AA=0). -/
def synthAnyResponse (query : Format) : Format :=
  finalizeForClient
    (buildResponse query Rcode.noError
      #[DnsSerializer.runBytes (ResourceRecord.encode (hinfoRFC8482RR (clientQname query)))]
      #[] #[])

/-- A non-ANY served query (`isAnyQuery = false`) has a first question whose
    qtype is not the ANY code, i.e. `qu.qtype.toNat ≠ 255`.  This is what removes
    the `hqany` gate from the serve capstones: the query-shape ANY restriction is
    the branch condition of the ANY arm, not an assumed hypothesis. -/
theorem not_anyQuery_qtype {q : Format} {qu : VeriDNS.Spec.Question}
    (h : isAnyQuery q = false) (hqu : q.question[0]? = some qu) :
    qu.qtype.toNat ≠ 255 := by
  unfold isAnyQuery at h
  rw [hqu] at h
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  intro he
  exact h (by apply BitVec.eq_of_toNat_eq; simpa [anyQTypeCode] using he)

/-- Converse of `not_anyQuery_qtype`: a query whose first question is not an ANY
    qtype (`qu.qtype.toNat ≠ 255`) is not an ANY query. -/
theorem isAnyQuery_false_of_qtype {q : Format} {qu : VeriDNS.Spec.Question}
    (hqu : q.question[0]? = some qu) (h : qu.qtype.toNat ≠ 255) :
    isAnyQuery q = false := by
  unfold isAnyQuery
  rw [hqu]
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro he
  exact h (by rw [he]; rfl)

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

/-- Root-priming ingest filter: keep only the record shapes a priming reply
    may legitimately seed — class-IN NS records (the root NS set) and
    class-IN A records with a well-formed 4-byte address (glue).  Everything
    else a hostile first hop could smuggle under the root bailiwick
    (SOA/TXT/CNAME junk, odd classes, malformed A rdata) is dropped before it
    can reach the cache. -/
def primeKeepRR (bytes : ByteArray) : Bool :=
  match RRParse.parseRaw (RR := ResourceRecord) bytes with
  | some rr =>
    rr.class == (1 : BitVec 16)
      && (rr.type == (2 : BitVec 16)
          || (rr.type == (1 : BitVec 16) && rr.rdata.size == 4))
  | none => false

/-- The pure cache-write core of root priming (`Main.primeRootHints`): the
    two `cacheUnlessTruncated` ingests of a priming reply (answer NS set,
    additional glue), filtered by `primeKeepRR`, then bounded like every
    other serve-path write (`boundLru`).  Factored out of the IO loop so the
    serve capstones can be based at the primed cache
    (`ServePack_primeWrites` in `Proof/ServeSequence.lean`). -/
def primeWrites (cache : DnsCache) (resp : Format) (now : UInt32) : DnsCache :=
  let root : ByteArray := ⟨#[0]⟩
  let c1 := Resolver.cacheUnlessTruncated (RR := ResourceRecord) cache resp
    ((Resolver.bailiwickRaws (RR := ResourceRecord) root resp.answer).filter primeKeepRR)
    (Resolver.credAnswer (resp.header.aa == 1)) now
  let c2 := Resolver.cacheUnlessTruncated (RR := ResourceRecord) c1 resp
    ((Resolver.bailiwickRaws (RR := ResourceRecord) root resp.additional).filter primeKeepRR)
    Resolver.credAdditional now
  c2.boundLru #[] now

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

def extractAAddress (owner : ByteArray) (answers : Array ByteArray) : Option (BitVec 32) :=
  answers.findSome? fun bytes =>
    match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
    | .ok (rr, _) =>

      if rr.type == (1 : BitVec 16) && rr.class == (1 : BitVec 16) && rr.rdata.size == 4
          && (DomainName.wireFormatToLabels rr.name).isOk
          && Resolver.nameMemB rr.name
              (Resolver.reachableNamesB (RR := ResourceRecord) owner answers) then
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
    if let some addr := extractAAddress nsName subResp.answer then
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

/-- RFC 9156 §2.3 fallback: when a *minimised probe* round fails (times out, or
    is denied by a broken ENT-mishandling server), retry with the **full**
    qname rather than burning the retry budget on the probe.  At a non-probe
    round this is the identity, so full-name retransmissions are unaffected.
    Findings 051/052/064. -/
def fallbackRevealed (sname : ByteArray) (revealed : Nat) : Nat :=
  if Resolver.probeRoundB sname revealed then DomainName.labelCount sname else revealed

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
            match extractAAddress nsName subResp.answer with
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
        | ioResumeLoop sbelt state deadline depth fuel'
            (fallbackRevealed state.resources.sname revealed)

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
      else if resp.header.rcode == Rcode.formatError && !state.noEdns then do
        -- RFC 6891 §6.2.2 (finding 055): a FORMERR to an OPT-bearing sub-query
        -- means the responder (or a middlebox) cannot parse EDNS.  Retry
        -- WITHOUT the OPT record instead of retry-looping to SERVFAIL: the
        -- flag makes every subsequent `buildSubQuery` of this resolution omit
        -- the OPT (the `!state.noEdns` guard means the arm fires at most once,
        -- so a FORMERR to an already-EDNS-free query takes the ordinary retry
        -- path and burns fuel normally).
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"FORMERR from {nameToString entry.name} to an EDNS sub-query: retrying without EDNS (RFC 6891 §6.2.2)"
        ioResumeLoop sbelt { state with noEdns := true } deadline depth fuel' revealed
      else if Resolver.probeRoundB state.resources.sname revealed
          && strictDenialB resp then do
        -- RFC 9156 §2.3 / unbound `qname-minimisation-strict: no` (findings
        -- 051/064): many real zones (broken middleboxes, ENT-mishandling
        -- servers) answer NXDOMAIN for an empty non-terminal even though the
        -- full name exists.  A minimised-probe NXDOMAIN is therefore NOT
        -- authoritative for the client: fall back and re-probe with the FULL
        -- qname against the same servers.  Only a full-name NXDOMAIN (a
        -- non-probe round, handled by `afterResume` below) is delivered.
        UdpSocket.log (M := M) (Sock := Sock) (Addr := ByteArray)
          s!"NXDOMAIN at probe ancestor for {nameToString state.resources.sname}: falling back to full qname (RFC 9156 §2.3)"
        ioResumeLoop sbelt state deadline depth fuel'
          (DomainName.labelCount state.resources.sname)
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
  -- 068: owner scrub (CNAME-chain entitlement) composed with the qtype
  -- relevance filter (RFC 1034 §3.6.2) — a delivered answer record matches
  -- the query type or is a chase-chain CNAME.
  let scrubbed := Resolver.typeScrubB (RR := ResourceRecord) (clientQtype query)
    (Resolver.scrubAnswerB (RR := ResourceRecord) (clientQname query) resp.answer)
  let auth := scrubAuthorityB (clientQname query) resp.authority
  let addl := scrubAdditionalB (clientQname query) resp.additional
  finalizeForClient
    { resp with
      answer := scrubbed
      authority := auth
      additional := addl
      header := { resp.header with
        id := query.header.id
        rd := query.header.rd
        ancount := BitVec.ofNat 16 scrubbed.size
        nscount := BitVec.ofNat 16 auth.size
        arcount := BitVec.ofNat 16 addl.size } }

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

  if let some ep := Edns.ednsProblem query then
    UdpSocket.sendTo clientSock
      (Message.encode (ednsProblemResponse query ep)) clientAddr
    return cache

  if isAnyQuery query then
    let response := Edns.withReplyOpt query (synthAnyResponse query)
    let (truncated, _) := truncateUdp (Message.encode response) response (Edns.clientCap query)
    UdpSocket.sendTo clientSock truncated clientAddr
    return cache
  let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
  let (resolveResult, cache') ← resolveWithIO (Sock := Sock) query sbelt cache nowT
  let (response, cache'') ← replyForResolution (Sock := Sock) query resolveResult cache' nowT
  let reply := Edns.withReplyOpt query response
  let (truncated, _) := truncateUdp (Message.encode reply) reply (Edns.clientCap query)
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

  if let some ep := Edns.ednsProblem query then
    UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
      (TcpFraming.frameTcp (Message.encode (ednsProblemResponse query ep)))
    return cache

  if isAnyQuery query then
    UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
      (TcpFraming.frameTcp (Message.encode (Edns.withReplyOpt query (synthAnyResponse query))))
    return cache
  let nowT ← UdpSocket.now (M := M) (Sock := Sock) (Addr := ByteArray)
  let (resolveResult, cache') ← resolveWithIO (Sock := Sock) query sbelt cache nowT
  let (response, cache'') ← replyForResolution (Sock := Sock) query resolveResult cache' nowT
  UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
    (TcpFraming.frameTcp (Message.encode (Edns.withReplyOpt query response)))

  pure (cache''.boundLru (serveTouches query sbelt cache nowT) nowT)

/-- Inbound client-datagram receive size.  Must be `Edns.advertisedUdpSize`
    (1232), not 512: an EDNS client may legitimately send a query larger than
    512 octets (e.g. a long qname plus OPT options), and a 512-octet receive
    buffer would clip it into a FORMERR/drop (finding 066). -/
def serveRecvSize : Nat := Edns.advertisedUdpSize

theorem serveRecvSize_eq_advertised : serveRecvSize = Edns.advertisedUdpSize := rfl

def serveOne (clientSock : Sock) (acl : ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) : M DnsCache := do
  let (queryBytes, clientAddr) : ByteArray × ByteArray
    ← UdpSocket.recvFrom clientSock serveRecvSize
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
  let (queryBytes, clientAddr) : ByteArray × ByteArray
    ← UdpSocket.recvFrom clientSock serveRecvSize
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
