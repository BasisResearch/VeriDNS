import VeriDNS.Impl.Server
import VeriDNS.Impl.NameTree

namespace VeriDNS.Test.Loop

open VeriDNS.Spec
open VeriDNS.Impl
open VeriDNS.Impl.Server
open VeriDNS.Impl.SList
open VeriDNS.Impl.Cache

def mockLocal : ByteArray := ⟨#[192, 168, 0, 2, 0xAB, 0xCD]⟩

structure MockState where
  inbox : ByteArray × ByteArray
  script : List (ByteArray → Option ByteArray)
  sent : Array (ByteArray × ByteArray) := #[]
  exchanged : Array ByteArray := #[]
  clock : UInt32 := 100000
  nextId : UInt16 := 7777
  spoofSource : Option ByteArray := none
  spoofDest : Option ByteArray := none

abbrev MockM := StateM MockState

instance : UdpSocket MockM Unit ByteArray where
  recvFrom _ _ := do pure (← get).inbox
  sendTo _ bytes addr := modify fun s => { s with sent := s.sent.push (bytes, addr) }
  now := do pure (← get).clock
  randomId := do
    let s ← get
    set { s with nextId := s.nextId + 1 }
    pure s.nextId
  exchange q addr := do
    let s ← get
    match s.script with
    | [] => pure none
    | h :: t =>
      set { s with script := t, exchanged := s.exchanged.push q }
      match h q with
      | none => pure none
      | some resp =>

        pure (some { payload := resp
                     source := s.spoofSource.getD addr
                     destination := s.spoofDest.getD mockLocal
                     localAddr := mockLocal })

def wireName (labels : List String) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for l in labels do
    out := out.push (UInt8.ofNat l.length)
    out := out ++ l.toUTF8
  return out.push 0

def exampleCom : ByteArray := wireName ["example", "com"]
def comName : ByteArray := wireName ["com"]

def nsName : ByteArray := wireName ["ns1", "com"]
def rootName : ByteArray := wireName ["a", "root-servers", "net"]
def clientAddr : ByteArray := ⟨#[127, 0, 0, 1, 0x13, 0x88]⟩
def aRdata : ByteArray := ⟨#[93, 184, 216, 34]⟩

def mkQuery (qname : ByteArray) (qtype : BitVec 16 := 1)
    (id : BitVec 16 := 0x1234) (rd : BitVec 1 := 1) : Format :=
  { header := { id := id, qr := 0, opcode := Opcode.query, aa := 0, tc := 0,
                rd := rd, ra := 0, z := 0, rcode := Rcode.noError,
                qdcount := 1, ancount := 0, nscount := 0, arcount := 0 }
    question := #[{ qname := qname, qtype := qtype, qclass := 1 }]
    answer := #[], authority := #[], additional := #[] }

def mkRR (name : ByteArray) (type_ : BitVec 16) (rdata : ByteArray)
    (ttl : BitVec 32 := 300) : ByteArray :=
  DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode
    { name := name, type := type_, «class» := 1, ttl := ttl,
      rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata })

def answerHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata] }

def spoofHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with
                  id := query.header.id + 1
                  qr := 1
                  aa := 1
                  ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata] }

def referralHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, nscount := 1, arcount := 1 }
      authority := #[mkRR comName 2 nsName]
      additional := #[mkRR nsName 1 ⟨#[93, 184, 216, 53]⟩] }

def soaRdata : ByteArray :=
  wireName ["ns1", "test"] ++ wireName ["host", "test"] ++
  ⟨#[0, 0, 0, 1, 0, 0, 14, 16, 0, 0, 3, 132, 0, 9, 58, 128, 0, 0, 0, 60]⟩

def nxdomainHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with
                  qr := 1
                  aa := 1
                  rcode := Rcode.nameError
                  nscount := 1 }
      authority := #[mkRR comName 6 soaRdata (ttl := 60)] }

def sbelt : DnsSList := DnsSList.mkSbelt #[(rootName, BitVec.ofNat 32 0x01010101)]

def runServe (query : Format) (script : List (ByteArray → Option ByteArray))
    (cache : DnsCache := DnsCache.empty) : DnsCache × MockState :=
  let st0 : MockState := { inbox := (Message.encode query, clientAddr), script := script }
  (serveOne (M := MockM) (Sock := Unit) () defaultAcl sbelt cache).run st0

def sentResponse (st : MockState) : Option Format :=
  st.sent[0]?.bind fun (bytes, _) =>
    match Message.decode bytes with
    | .ok f => some f
    | .error _ => none

def directAnswer : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  return st.sent.size == 1 &&
    resp.header.id == 0x1234 && resp.header.qr == 1 &&
    resp.header.ra == 1 && resp.header.aa == 0 && resp.header.z == 0 &&
    resp.header.rcode == Rcode.noError && resp.answer.size == 1 &&
    resp.question[0]?.any (fun qu => qu.qname == exampleCom && qu.qtype == 1)

#guard directAnswer

def spoofRejected : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [spoofHandler]
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard spoofRejected

def caseEchoHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    let flipped : ByteArray :=
      ⟨query.question[0]!.qname.data.map DomainName.toggleCaseByte⟩
    some <| Message.encode
      { query with
        header := { query.header with qr := 1, aa := 1, ancount := 1 }
        question := #[{ query.question[0]! with qname := flipped }]
        answer := #[mkRR flipped 1 aRdata] }

def caseVaryingEchoRejected : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [caseEchoHandler]
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard caseVaryingEchoRejected

/-! ### Finding 030: QR/OPCODE admissibility

A datagram that fails the response-shape gate — QR=0 (a reflected query) or a
non-QUERY opcode — must never be consumed as the reply, even when it echoes the
transaction id and question perfectly. -/

def qrZeroEchoHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 0, aa := 1, ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata] }

def qrZeroInjectionRejected : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [qrZeroEchoHandler]
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

def opcodeMutantHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, opcode := Opcode.status, aa := 1, ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata] }

def opcodeMutantRejected : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [opcodeMutantHandler]
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard qrZeroInjectionRejected
#guard opcodeMutantRejected

def sentQnameCaseVaries : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler, answerHandler]
  let some probeBytes := st.exchanged[0]? | return false
  let .ok probeSent := Message.decode probeBytes | return false
  let some quP := probeSent.question[0]? | return false
  let some sentBytes := st.exchanged[1]? | return false
  let .ok sent := Message.decode sentBytes | return false
  let some qu := sent.question[0]? | return false
  let st0 : MockState := { inbox := (Message.encode (mkQuery exampleCom), clientAddr)
                           script := [answerHandler, answerHandler], nextId := 12345 }
  let (_, st2) := (serveOne (M := MockM) (Sock := Unit) () defaultAcl sbelt DnsCache.empty).run st0
  let some sentBytes2 := st2.exchanged[1]? | return false
  let .ok sent2 := Message.decode sentBytes2 | return false
  let some qu2 := sent2.question[0]? | return false
  return quP.qname == DomainName.randomizeCase 7778 comName
    && qu.qname == DomainName.randomizeCase 7780 exampleCom
    && DomainName.nameEqCI qu.qname exampleCom
    && qu.qname != exampleCom
    && DomainName.nameEqCI qu2.qname exampleCom
    && qu2.qname != qu.qname

#guard sentQnameCaseVaries

/-- Per-retry fresh secrets (item 4) under the RFC 9156 §2.3 timeout fallback
(finding 052): the probe timeout falls back to the FULL qname (exchange 2),
the full-name timeout retransmits the SAME name (exchange 3), and every
(re)transmission draws a fresh TXID + case seed. -/
def retransmitFreshSecrets : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [fun _ => none, fun _ => none, answerHandler]
  let some b1 := st.exchanged[0]? | return false
  let some b2 := st.exchanged[1]? | return false
  let some b3 := st.exchanged[2]? | return false
  let .ok s1 := Message.decode b1 | return false
  let .ok s2 := Message.decode b2 | return false
  let .ok s3 := Message.decode b3 | return false
  let some q1 := s1.question[0]? | return false
  let some q2 := s2.question[0]? | return false
  let some q3 := s3.question[0]? | return false
  let some resp := sentResponse st | return false
  return st.exchanged.size == 3
    && s1.header.id == 7777 && s2.header.id == 7779 && s3.header.id == 7781
    && q1.qname == DomainName.randomizeCase 7778 comName
    && q2.qname == DomainName.randomizeCase 7780 exampleCom
    && q3.qname == DomainName.randomizeCase 7782 exampleCom
    && b2 != b3
    && resp.header.rcode == Rcode.noError && resp.answer.size == 1

#guard retransmitFreshSecrets

def wrongSourceRejected : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr)
                           script := [answerHandler]
                           spoofSource := some ⟨#[6, 6, 6, 6, 0, 53]⟩ }
  let (_, st) := (serveOne (M := MockM) (Sock := Unit) () defaultAcl sbelt DnsCache.empty).run st0
  let some resp := sentResponse st | return false

  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard wrongSourceRejected

def wrongDestRejected : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr)
                           script := [answerHandler]
                           spoofDest := some ⟨#[10, 9, 9, 9, 0xAB, 0xCD]⟩ }
  let (_, st) := (serveOne (M := MockM) (Sock := Unit) () defaultAcl sbelt DnsCache.empty).run st0
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError

#guard wrongDestRejected

def aclDeniedNoService : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, ⟨#[8, 8, 8, 8, 0x13, 0x88]⟩)
                           script := [answerHandler] }
  let (cache', st) := (serveOne (M := MockM) (Sock := Unit) () defaultAcl sbelt DnsCache.empty).run st0
  return st.sent.isEmpty && st.exchanged.isEmpty && cache'.records.isEmpty

#guard aclDeniedNoService

def rateLimitDrops : Bool := Id.run do
  let ip := clientIp clientAddr
  let full : RateBucket := { counts := #[(ip, rateWindowLimit)] }
  match full.bump ip with
  | none =>
    let query := mkQuery exampleCom
    let st0 : MockState := { inbox := (Message.encode query, clientAddr), script := [answerHandler] }
    let ((cache', rb'), st) :=
      (afterRecv (M := MockM) (Sock := Unit) () defaultAcl sbelt DnsCache.empty full
        (Message.encode query) clientAddr).run st0
    return st.sent.isEmpty && st.exchanged.isEmpty && cache'.records.isEmpty
      && rb'.counts.size == 1
  | some _ => return false

#guard rateLimitDrops

def rateLimitAdmits : Bool := Id.run do
  let ip := clientIp clientAddr
  let rb : RateBucket := RateBucket.empty
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr), script := [answerHandler] }
  let ((_, rb'), st) :=
    (afterRecv (M := MockM) (Sock := Unit) () defaultAcl sbelt DnsCache.empty rb
      (Message.encode query) clientAddr).run st0
  return st.sent.size == 1 && rb'.counts.size == 1 &&
    (rb'.counts.getD 0 (ip, 0)).2 == 1

#guard rateLimitAdmits

def delegationChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [referralHandler, answerHandler]
  let some resp := sentResponse st | return false
  return st.exchanged.size == 2 && resp.header.rcode == Rcode.noError &&
    resp.answer.size == 1 && resp.header.id == 0x1234

#guard delegationChased

def rootWire : ByteArray := wireName []

def rootNsRR : ResourceRecord :=
  { name := rootWire, type := 2, «class» := 1, ttl := 300,
    rdlength := BitVec.ofNat 16 rootName.size, rdata := rootName }

-- Finding 015 end-to-end sanity check.  The property this mock exercises — that an
-- address-less root NS RRset falls back to SBELT rather than looping — is now pinned as
-- a real theorem: `VeriDNS.Proof.Resolver.stepFindServers_rootCut_sbelt_fallback` (and its
-- forward-progress corollary `stepFindServers_rootCut_sbelt_progress`).  This `#guard`
-- stays as a belt-and-braces integration check.
def addresslessRootNsSbeltFallback : Bool := Id.run do
  let cache0 := DnsCache.empty.storeChecked rootNsRR Trustworthiness.authoritativeSection 100000
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler, answerHandler] cache0
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 1 &&
    st.exchanged.size == 2 && resp.header.id == 0x1234

#guard addresslessRootNsSbeltFallback

def attackerName : ByteArray := wireName ["attacker", "chosen"]
def victimName : ByteArray := wireName ["victim-internal", "test"]

def offOwnerCnameHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 1 }
      answer := #[mkRR attackerName 5 victimName] }

def offOwnerCnameNotChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler, offOwnerCnameHandler]
  let some resp := sentResponse st | return false
  let noVictimQuery := st.exchanged.all fun qb =>
    match Message.decode qb with
    | .ok f => f.question[0]?.all (fun qu => !(DomainName.nameEqCI qu.qname victimName))
    | .error _ => true
  return st.exchanged.size == 2 && noVictimQuery &&
    resp.answer.size == 0 && resp.header.id == 0x1234

#guard offOwnerCnameNotChased

def poisonSoaOwner : ByteArray := wireName ["poison", "attacker", "test"]

def offOwnerSoaNxdomainHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with
                  qr := 1
                  aa := 1
                  rcode := Rcode.nameError
                  nscount := 1 }
      authority := #[mkRR poisonSoaOwner 6 soaRdata (ttl := 60)] }

def offOwnerSoaNotNegativelyCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [answerHandler, offOwnerSoaNxdomainHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery exampleCom) [answerHandler, answerHandler] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.nameError && cache1.negatives.isEmpty &&
    st2.exchanged.size == 2 && r2.header.rcode == Rcode.noError &&
    r2.answer.size == 1 && r2.header.id == 0x1234

#guard offOwnerSoaNotNegativelyCached

def truncatedNxdomainHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with
                  qr := 1
                  aa := 1
                  tc := 1
                  rcode := Rcode.nameError
                  nscount := 1 }
      authority := #[mkRR comName 6 soaRdata (ttl := 60)] }

def truncatedReplyNotNegativelyCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [answerHandler, truncatedNxdomainHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery exampleCom) [answerHandler, answerHandler] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.serverFailure && cache1.negatives.isEmpty &&
    cache1.records.isEmpty &&
    st2.exchanged.size == 2 && r2.header.rcode == Rcode.noError &&
    r2.answer.size == 1 && r2.header.id == 0x1234

#guard truncatedReplyNotNegativelyCached

def rdEchoedUniformly : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [answerHandler, answerHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery exampleCom) [] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rd == 1 && r2.header.rd == 1 &&
    st2.exchanged.size == 0 && r2.answer.size == 1

#guard rdEchoedUniformly

def deliveredAuthorityScrubbed : Bool := Id.run do
  let (_, st1) := runServe (mkQuery exampleCom) [answerHandler, offOwnerSoaNxdomainHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery exampleCom) [answerHandler, nxdomainHandler]
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.nameError && r1.authority.size == 0 &&
    r1.header.nscount == 0 &&
    r2.header.rcode == Rcode.nameError && r2.authority.size == 1 &&
    r2.header.nscount == 1

#guard deliveredAuthorityScrubbed

def deliveredOwnerClientCase : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  let some rrBytes := resp.answer[0]? | return false
  let some rr := RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rrBytes | return false
  let some sentBytes := st.exchanged[1]? | return false
  let .ok sent := Message.decode sentBytes | return false
  let some qu := sent.question[0]? | return false
  let mixed := wireName ["eXaMpLe", "CoM"]
  let (_, st2) := runServe (mkQuery mixed) [answerHandler, answerHandler]
  let some resp2 := sentResponse st2 | return false
  let some rrBytes2 := resp2.answer[0]? | return false
  let some rr2 := RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rrBytes2 | return false
  return qu.qname != exampleCom
    && rr.name == exampleCom
    && rr2.name == mixed
    && rr.rdata == aRdata && rr2.rdata == aRdata

#guard deliveredOwnerClientCase

def subExampleCom : ByteArray := wireName ["sub", "example", "com"]
def evilRdata : ByteArray := ⟨#[6, 6, 6, 6]⟩

def subdomainRidingHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 2 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata,
                  mkRR subExampleCom 1 evilRdata] }

def subdomainRiderNotCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [answerHandler, subdomainRidingHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery subExampleCom)
    [answerHandler, answerHandler, answerHandler] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.noError && r1.answer.size == 1 &&
    st2.exchanged.size == 3 && r2.header.rcode == Rcode.noError &&
    r2.answer.size == 1 && r2.header.id == 0x1234 &&
    r2.answer[0]?.all (fun raw =>
      match RRParse.parseRaw (RR := ResourceRecord) raw with
      | some rr => rr.rdata == aRdata
      | none => false)

#guard subdomainRiderNotCached

def negativeCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [answerHandler, nxdomainHandler]
  let some r1 := sentResponse st1 | return false

  let (_, st2) := runServe (mkQuery exampleCom 28) [] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.nameError && r1.authority.size == 1 &&
    r2.header.rcode == Rcode.nameError && r2.authority.size == 1 &&
    st2.exchanged.isEmpty && r2.header.id == 0x1234

#guard negativeCached

def refusedIterative : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom (rd := 0)) [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.refused && st.exchanged.isEmpty

#guard refusedIterative

section TreeNetwork

open VeriDNS.Impl.NameTree

def lab (s : String) : ByteArray := s.toUTF8

def wwwExampleCom : ByteArray := wireName ["www", "example", "com"]
def missingName : ByteArray := wireName ["missing", "example", "com"]

def aRR : ResourceRecord :=
  { name := exampleCom, type := 1, «class» := 1, ttl := 300,
    rdlength := 4, rdata := aRdata }

def cnameRR : ResourceRecord :=
  { name := wwwExampleCom, type := 5, «class» := 1, ttl := 300,
    rdlength := BitVec.ofNat 16 exampleCom.size, rdata := exampleCom }

def txtExampleCom : ByteArray := wireName ["txt", "example", "com"]
def txtRdata : ByteArray := ⟨#[5, 0x68, 0x65, 0x6C, 0x6C, 0x6F]⟩

def txtRR : ResourceRecord :=
  { name := txtExampleCom, type := 16, «class» := 1, ttl := 300,
    rdlength := BitVec.ofNat 16 txtRdata.size, rdata := txtRdata }

def theTree : Node ResourceRecord :=
  .mk ByteArray.empty #[] #[
    .mk (lab "com") #[] #[
      .mk (lab "example") #[aRR] #[
        .mk (lab "www") #[cnameRR] #[],
        .mk (lab "txt") #[txtRR] #[]]]]

def treeHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    match query.question[0]? with
    | none => none
    | some qu =>
      match treeLookup theTree qu.qname qu.qtype with
      | .answer rrs =>
        let h := { query.header with
                     qr := 1
                     aa := 1
                     ancount := BitVec.ofNat 16 rrs.size }
        some <| Message.encode
          { query with header := h, answer := rrs.map RRParse.rrBytes }
      | .redirect rr _ =>
        let h := { query.header with qr := 1, aa := 1, ancount := 1 }
        some <| Message.encode
          { query with header := h, answer := #[RRParse.rrBytes rr] }
      | .nodata =>
        let h := { query.header with qr := 1, aa := 1, nscount := 1 }
        some <| Message.encode
          { query with header := h
                       authority := #[mkRR comName 6 soaRdata (ttl := 60)] }
      | .nameError =>
        let h := { query.header with
                     qr := 1
                     aa := 1
                     rcode := Rcode.nameError
                     nscount := 1 }
        some <| Message.encode
          { query with header := h
                       authority := #[mkRR comName 6 soaRdata (ttl := 60)] }

def treeAnswered : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  let some bytes := resp.answer[0]? | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 1 &&
    bytes == RRParse.rrBytes aRR && resp.header.id == 0x1234

#guard treeAnswered

def treeMissing : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery missingName) [treeHandler, treeHandler, treeHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery missingName 28) [] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.nameError &&
    r2.header.rcode == Rcode.nameError && st2.exchanged.isEmpty

#eval show IO Unit from do
  unless treeMissing do
    throw <| IO.userError "treeMissing regressed"

def deepMissingName : ByteArray := wireName ["foo", "bar", "missing", "example", "com"]
def probeMissing : ByteArray := wireName ["missing", "example", "com"]

/-- Findings 051/064 (RFC 9156 §2.3 / unbound `qname-minimisation-strict: no`):
a minimised-probe NXDOMAIN is NOT delivered — the resolver falls back and
re-probes with the FULL qname (exchange 4 below), and only the full name's
NXDOMAIN is authoritative for the client.  The warm re-query shows the
client-level negative is cached for the FULL qname (RFC 2308). -/
def fullNameNxdomainFinal : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery deepMissingName)
    [treeHandler, treeHandler, treeHandler, treeHandler]
  let some r1 := sentResponse st1 | return false
  let some bProbe := st1.exchanged[2]? | return false
  let .ok sProbe := Message.decode bProbe | return false
  let some quProbe := sProbe.question[0]? | return false
  let some bLast := st1.exchanged[3]? | return false
  let .ok sLast := Message.decode bLast | return false
  let some quLast := sLast.question[0]? | return false
  let (_, st2) := runServe (mkQuery deepMissingName) [] cache1
  let some r2 := sentResponse st2 | return false
  return st1.exchanged.size == 4
    && r1.header.rcode == Rcode.nameError
    && r1.header.id == 0x1234
    && DomainName.nameEqCI quProbe.qname probeMissing
    && quProbe.qtype == 1
    && DomainName.nameEqCI quLast.qname deepMissingName
    && r2.header.rcode == Rcode.nameError
    && st2.exchanged.isEmpty

#eval show IO Unit from do
  unless fullNameNxdomainFinal do
    throw <| IO.userError "fullNameNxdomainFinal regressed"

/-- Finding 051/064 headline: the queried name EXISTS even though an
ENT-mishandling server answers NXDOMAIN for the empty non-terminal above it.
Strict RFC 8020 would deny the whole subtree and NXDOMAIN an existing name;
the RFC 9156 §2.3 fallback re-probes with the full qname and resolves it. -/
def entName : ByteArray := wireName ["ent", "example", "com"]
def aEntName : ByteArray := wireName ["a", "ent", "example", "com"]

def aEntRR : ResourceRecord :=
  { name := aEntName, type := 1, «class» := 1, ttl := 300,
    rdlength := 4, rdata := aRdata }

def entTree : Node ResourceRecord :=
  .mk ByteArray.empty #[] #[
    .mk (lab "com") #[] #[
      .mk (lab "example") #[aRR] #[
        .mk (lab "ent") #[] #[
          .mk (lab "a") #[aEntRR] #[]]]]]

/-- An ENT-mishandling authoritative server over `entTree`: answers NXDOMAIN
for the empty non-terminal `ent.example.com` (an RFC 8020 §3.1 violation —
the correct response is NODATA), answers everything else from the tree. -/
def brokenEntHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    match query.question[0]? with
    | none => none
    | some qu =>
      if DomainName.nameEqCI qu.qname entName then
        some <| Message.encode
          { query with
            header := { query.header with
                        qr := 1, aa := 1, rcode := Rcode.nameError, nscount := 1 }
            authority := #[mkRR comName 6 soaRdata (ttl := 60)] }
      else
        match treeLookup entTree qu.qname qu.qtype with
        | .answer rrs =>
          some <| Message.encode
            { query with
              header := { query.header with
                          qr := 1, aa := 1, ancount := BitVec.ofNat 16 rrs.size }
              answer := rrs.map RRParse.rrBytes }
        | _ =>
          some <| Message.encode
            { query with
              header := { query.header with qr := 1, aa := 1, nscount := 1 }
              authority := #[mkRR comName 6 soaRdata (ttl := 60)] }

def probeNxdomainEntRecovered : Bool := Id.run do
  let (_, st) := runServe (mkQuery aEntName)
    [brokenEntHandler, brokenEntHandler, brokenEntHandler, brokenEntHandler]
  let some resp := sentResponse st | return false
  let some b3 := st.exchanged[2]? | return false
  let .ok s3 := Message.decode b3 | return false
  let some q3 := s3.question[0]? | return false
  let some b4 := st.exchanged[3]? | return false
  let .ok s4 := Message.decode b4 | return false
  let some q4 := s4.question[0]? | return false
  return st.exchanged.size == 4
    && DomainName.nameEqCI q3.qname entName
    && DomainName.nameEqCI q4.qname aEntName
    && resp.header.rcode == Rcode.noError
    && resp.answer.size == 1
    && resp.header.id == 0x1234

#eval show IO Unit from do
  unless probeNxdomainEntRecovered do
    throw <| IO.userError "probeNxdomainEntRecovered regressed"

/-- Finding 052 (RFC 9156 §2.3): a minimised-probe TIMEOUT falls back to the
full qname instead of re-sending the probe until the budget expires — the
second exchange carries the full name and resolves. -/
def probeTimeoutFallsBackToFull : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [fun _ => none, treeHandler]
  let some resp := sentResponse st | return false
  let some b1 := st.exchanged[0]? | return false
  let some b2 := st.exchanged[1]? | return false
  let .ok s1 := Message.decode b1 | return false
  let .ok s2 := Message.decode b2 | return false
  let some q1 := s1.question[0]? | return false
  let some q2 := s2.question[0]? | return false
  return st.exchanged.size == 2
    && DomainName.nameEqCI q1.qname comName && q1.qtype == 1
    && DomainName.nameEqCI q2.qname exampleCom
    && resp.header.rcode == Rcode.noError && resp.answer.size == 1
    && resp.header.id == 0x1234

#eval show IO Unit from do
  unless probeTimeoutFallsBackToFull do
    throw <| IO.userError "probeTimeoutFallsBackToFull regressed"

/-- Finding 055 (RFC 6891 §6.2.2): an upstream that answers FORMERR to an
OPT-bearing sub-query cannot parse EDNS — the resolver retries WITHOUT the
OPT record (the `noEdns` flag makes every subsequent `buildSubQuery` of the
resolution EDNS-free) instead of retry-looping the same EDNS query to
SERVFAIL. -/
def formerrOnEdnsHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    if Edns.hasOpt query then
      some <| Message.encode
        { query with
          header := { query.header with
                      qr := 1, rcode := Rcode.formatError,
                      ancount := 0, nscount := 0, arcount := 0 }
          answer := #[], authority := #[], additional := #[] }
    else treeHandler q

def formerrRetriesWithoutEdns : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom)
    [formerrOnEdnsHandler, formerrOnEdnsHandler, formerrOnEdnsHandler]
  let some resp := sentResponse st | return false
  let some b1 := st.exchanged[0]? | return false
  let some b2 := st.exchanged[1]? | return false
  let .ok s1 := Message.decode b1 | return false
  let .ok s2 := Message.decode b2 | return false
  return st.exchanged.size == 3
    && s1.additional.size == 1     -- first sub-query advertises EDNS
    && s2.additional.size == 0     -- the retry is EDNS-free (RFC 6891 §6.2.2)
    && resp.header.rcode == Rcode.noError && resp.answer.size == 1
    && resp.header.id == 0x1234

#eval show IO Unit from do
  unless formerrRetriesWithoutEdns do
    throw <| IO.userError "formerrRetriesWithoutEdns regressed"

def treeCaseInsensitive : Bool := Id.run do
  let upper := wireName ["EXAMPLE", "COM"]
  let (_, st) := runServe (mkQuery upper) [treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 1

#guard treeCaseInsensitive

def treeChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery wwwExampleCom)
    [treeHandler, treeHandler, treeHandler, treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  return st.exchanged.size == 5 && resp.header.rcode == Rcode.noError &&
    resp.answer.size == 2 && resp.header.id == 0x1234 &&
    resp.question[0]?.any (fun qu => qu.qname == wwwExampleCom)

#guard treeChased

def treeNodata : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom 15) [treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 0

#eval show IO Unit from do
  unless treeNodata do
    throw <| IO.userError "treeNodata regressed"

def probeSequenceMinimised : Bool := Id.run do
  let (_, st) := runServe (mkQuery txtExampleCom 16) [treeHandler, treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  let some b1 := st.exchanged[0]? | return false
  let some b2 := st.exchanged[1]? | return false
  let some b3 := st.exchanged[2]? | return false
  let .ok s1 := Message.decode b1 | return false
  let .ok s2 := Message.decode b2 | return false
  let .ok s3 := Message.decode b3 | return false
  let some q1 := s1.question[0]? | return false
  let some q2 := s2.question[0]? | return false
  let some q3 := s3.question[0]? | return false
  return st.exchanged.size == 3
    && DomainName.nameEqCI q1.qname comName && q1.qtype == 1
    && DomainName.nameEqCI q2.qname exampleCom && q2.qtype == 1
    && DomainName.nameEqCI q3.qname txtExampleCom && q3.qtype == 16
    && resp.header.rcode == Rcode.noError && resp.answer.size == 1
    && resp.header.id == 0x1234
    && resp.answer[0]?.all (fun raw =>
      match RRParse.parseRaw (RR := ResourceRecord) raw with
      | some rr => rr.type == 16 && rr.rdata == txtRdata
      | none => false)

#eval show IO Unit from do
  unless probeSequenceMinimised do
    throw <| IO.userError "probeSequenceMinimised regressed"

def probeNodataRevealsMore : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  let some b1 := st.exchanged[0]? | return false
  let some b2 := st.exchanged[1]? | return false
  let .ok s1 := Message.decode b1 | return false
  let .ok s2 := Message.decode b2 | return false
  let some q1 := s1.question[0]? | return false
  let some q2 := s2.question[0]? | return false
  return st.exchanged.size == 2
    && DomainName.nameEqCI q1.qname comName && q1.qtype == 1
    && DomainName.nameEqCI q2.qname exampleCom && q2.qtype == 1
    && resp.header.rcode == Rcode.noError && resp.answer.size == 1
    && resp.answer[0]?.all (fun raw =>
      match RRParse.parseRaw (RR := ResourceRecord) raw with
      | some rr => rr.rdata == aRdata
      | none => false)

#eval show IO Unit from do
  unless probeNodataRevealsMore do
    throw <| IO.userError "probeNodataRevealsMore regressed"

def evilProbeHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 1 evilRdata] }

def probeAnswerNotDelivered : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery txtExampleCom 16)
    [treeHandler, evilProbeHandler, treeHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery exampleCom) [treeHandler, treeHandler] cache1
  let some r2 := sentResponse st2 | return false
  return st1.exchanged.size == 3
    && r1.header.rcode == Rcode.noError && r1.answer.size == 1
    && r1.answer[0]?.all (fun raw =>
      match RRParse.parseRaw (RR := ResourceRecord) raw with
      | some rr => rr.type == 16 && rr.rdata == txtRdata
      | none => false)
    && !st2.exchanged.isEmpty && st2.exchanged.size == 2
    && r2.header.rcode == Rcode.noError && r2.answer.size == 1
    && r2.answer[0]?.all (fun raw =>
      match RRParse.parseRaw (RR := ResourceRecord) raw with
      | some rr => rr.rdata == aRdata
      | none => false)

#eval show IO Unit from do
  unless probeAnswerNotDelivered do
    throw <| IO.userError "probeAnswerNotDelivered regressed"

def probeCnameHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 5 attackerName] }

def probeCnameNotChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery txtExampleCom 16)
    [treeHandler, probeCnameHandler, treeHandler]
  let some resp := sentResponse st | return false
  let noAttackerQuery := st.exchanged.all fun qb =>
    match Message.decode qb with
    | .ok f => f.question[0]?.all (fun qu => !(DomainName.nameEqCI qu.qname attackerName))
    | .error _ => true
  return st.exchanged.size == 3 && noAttackerQuery
    && resp.header.rcode == Rcode.noError && resp.answer.size == 1
    && resp.header.id == 0x1234
    && resp.answer[0]?.all (fun raw =>
      match RRParse.parseRaw (RR := ResourceRecord) raw with
      | some rr => rr.type == 16 && rr.rdata == txtRdata
      | none => false)

#eval show IO Unit from do
  unless probeCnameNotChased do
    throw <| IO.userError "probeCnameNotChased regressed"

end TreeNetwork


section ParserHardening

def headerPointerQuery : ByteArray :=
  ⟨#[0x12, 0x34, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0xC0, 0x00,
     0x00, 0x01, 0x00, 0x01]⟩

def headerPointerRejected : Bool :=
  match Message.decode headerPointerQuery with
  | .ok _ => false
  | .error _ => true

#guard headerPointerRejected

def compressedAnswerResponse : ByteArray :=
  ⟨#[0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]⟩
  ++ wireName ["a"]
  ++ ⟨#[0x00, 0x01, 0x00, 0x01]⟩
  ++ ⟨#[0xC0, 0x0C]⟩
  ++ ⟨#[0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04, 1, 2, 3, 4]⟩

def compressionStillAccepted : Bool :=
  match Message.decode compressedAnswerResponse with
  | .ok f => f.answer.size == 1
  | .error _ => false

#guard compressionStillAccepted

def runServeRaw (raw : ByteArray) (script : List (ByteArray → Option ByteArray))
    (cache : DnsCache := DnsCache.empty) : DnsCache × MockState :=
  let st0 : MockState := { inbox := (raw, clientAddr), script := script }
  (serveOne (M := MockM) (Sock := Unit) () defaultAcl sbelt cache).run st0

def garbageDatagramDropped : Bool :=
  let (_, st) := runServeRaw ⟨#[0x12, 0x34]⟩ [answerHandler]
  st.sent.isEmpty && st.exchanged.isEmpty

def responseDatagramDropped : Bool :=
  let raw : ByteArray :=
    ⟨#[0xBE, 0xEF, 0x81, 0x80, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF]⟩
  let (_, st) := runServeRaw raw [answerHandler]
  st.sent.isEmpty && st.exchanged.isEmpty

def malformedQueryFormerr : Bool := Id.run do
  let raw : ByteArray :=
    ⟨#[0xBE, 0xEF, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF]⟩
  let (_, st) := runServeRaw raw [answerHandler]
  let some (bytes, _) := st.sent[0]? | return false
  let .ok resp := Message.decode bytes | return false
  return st.sent.size == 1 && st.exchanged.isEmpty && bytes.size == 12 &&
    resp.header.id == 0xBEEF && resp.header.qr == 1 &&
    resp.header.rcode == Rcode.formatError &&
    resp.question.isEmpty && resp.answer.isEmpty &&
    resp.authority.isEmpty && resp.additional.isEmpty

#guard garbageDatagramDropped
#guard responseDatagramDropped
#guard malformedQueryFormerr

def label63 : String := "".pushn 'a' 63

def overlongQname : ByteArray := wireName [label63, label63, label63, label63]

def overlongNameRejected : Bool :=
  match Message.decode (Message.encode (mkQuery overlongQname)) with
  | .ok _ => false
  | .error _ => true

#guard overlongNameRejected

def compressedMxResponse : ByteArray :=
  ⟨#[0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]⟩
  ++ wireName ["a"] ++ ⟨#[0x00, 0x0F, 0x00, 0x01]⟩
  ++ ⟨#[0xC0, 0x0C, 0x00, 0x0F, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
        0x00, 0x0A, 0xC0, 0x0C]⟩

def mxPointerDecompressed : Bool :=
  match Message.decode compressedMxResponse with
  | .ok f => f.answer[0]? ==
      some (mkRR (wireName ["a"]) 15 (⟨#[0x00, 0x0A]⟩ ++ wireName ["a"]) (ttl := 60))
  | .error _ => false

#guard mxPointerDecompressed

def compressedSrvResponse : ByteArray :=
  ⟨#[0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]⟩
  ++ wireName ["a"] ++ ⟨#[0x00, 0x21, 0x00, 0x01]⟩
  ++ ⟨#[0xC0, 0x0C, 0x00, 0x21, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x08,
        0x00, 0x01, 0x00, 0x02, 0x00, 0x35, 0xC0, 0x0C]⟩

def srvPointerDecompressed : Bool :=
  match Message.decode compressedSrvResponse with
  | .ok f => f.answer[0]? ==
      some (mkRR (wireName ["a"]) 33
        (⟨#[0x00, 0x01, 0x00, 0x02, 0x00, 0x35]⟩ ++ wireName ["a"]) (ttl := 60))
  | .error _ => false

#guard srvPointerDecompressed

def mxBadRdlenRejected : Bool :=
  let raw : ByteArray :=
    ⟨#[0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]⟩
    ++ wireName ["a"] ++ ⟨#[0x00, 0x0F, 0x00, 0x01]⟩
    ++ ⟨#[0xC0, 0x0C, 0x00, 0x0F, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x03,
          0x00, 0x0A, 0xC0, 0x0C]⟩
  match Message.decode raw with
  | .ok _ => false
  | .error _ => true

#guard mxBadRdlenRejected

end ParserHardening


section LruEviction

def mkPlainRR (name : ByteArray) (rdata : ByteArray) : ResourceRecord :=
  { name := name, type := 1, «class» := 1, ttl := 300,
    rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata }

def fillerName (i : Nat) : ByteArray := wireName [s!"f{i}", "test"]

def lruReadIsAUse : Bool := Id.run do
  let a := wireName ["a", "test"]
  let b := wireName ["b", "test"]
  let c0 := (DnsCache.empty.store (mkPlainRR a aRdata) 1).store (mkPlainRR b aRdata) 2
  let c1 := c0.touchKeys #[demandKey a 1 1] 3
  let some vTouched := lruVictim c1.records | return false
  let some vPlain := lruVictim c0.records | return false
  return DomainName.nameEqCI vTouched.rr.name b && DomainName.nameEqCI vPlain.rr.name a

#guard lruReadIsAUse

def lruHotSurvivesEviction : Bool := Id.run do
  let hot := wireName ["hot", "test"]
  let cold := wireName ["cold", "test"]
  let warm := (DnsCache.empty.store (mkPlainRR hot aRdata) 99990
      (cred := Resolver.credAnswer true)).store
    (mkPlainRR cold aRdata) 99995 (cred := Resolver.credAnswer true)
  let (cacheOut, st) := runServe (mkQuery hot) [] warm
  let some resp := sentResponse st | return false
  let some v := lruVictim cacheOut.records | return false
  return st.exchanged.size == 0 && resp.answer.size == 1
    && DomainName.nameEqCI v.rr.name cold

#guard lruHotSurvivesEviction

def lruRRsetAtomic : Bool := Id.run do
  let pair := wireName ["pair", "test"]
  let solo := wireName ["solo", "test"]
  let rd2 : ByteArray := ⟨#[1, 2, 3, 4]⟩
  let c0 := ((DnsCache.empty.store (mkPlainRR pair aRdata) 1).store
    (mkPlainRR pair rd2) 1).store (mkPlainRR solo aRdata) 2
  let cFull := (List.range (DnsCache.capacity - 2)).foldl
    (fun c i => c.store (mkPlainRR (fillerName i) aRdata) (10 + i.toUInt32)) c0
  let cB := cFull.boundLruKeys
  let pairCount := cB.records.foldl
    (fun n e => if DomainName.nameEqCI e.rr.name pair then n + 1 else n) 0
  let soloCount := cB.records.foldl
    (fun n e => if DomainName.nameEqCI e.rr.name solo then n + 1 else n) 0
  return cFull.records.size == DnsCache.capacity + 1
    && pairCount == 0 && soloCount == 1 && cB.records.size ≤ DnsCache.capacity

#guard lruRRsetAtomic

def lruNegativeRecency : Bool := Id.run do
  let a := wireName ["na", "test"]
  let b := wireName ["nb", "test"]
  let c0 := (DnsCache.empty.storeNegative a 1 1 Rcode.nameError none 500 1).storeNegative
    b 1 1 Rcode.nameError none 500 2
  let c1 := c0.touchKeys #[demandKey a 1 1] 3
  let some v := minRecBy (·.lastUsed) c1.negatives.toList | return false
  return DomainName.nameEqCI v.name b

#guard lruNegativeRecency

def lruNegativeEvictsCold : Bool := Id.run do
  let hotN := wireName ["hotn", "test"]
  let c0 := DnsCache.empty.storeNegative hotN 1 1 Rcode.nameError none 500 1
  let cFull := (List.range (DnsCache.capacity - 1)).foldl
    (fun c i => c.storeNegative (fillerName i) 1 1 Rcode.nameError none 500 (10 + i.toUInt32))
    c0
  let cT := cFull.touchKeys #[demandKey hotN 1 1] 100000
  let cNew := cT.storeNegative (wireName ["new", "test"]) 1 1 Rcode.nameError none 500 100001
  return (cNew.lookupNxdomain hotN 1 400).isSome
    && (cNew.lookupNxdomain (fillerName 0) 1 400).isNone
    && cNew.negatives.size ≤ DnsCache.capacity

#guard lruNegativeEvictsCold

end LruEviction

/-! ### Egress do-not-query mask vectors (finding 060b)

Empirical pins that `AclEntry.matches` blocks the ENTIRE CIDR range —
in particular the upper half of every blocked range (the 060b claim of a
mask off-by-one is FALSE) — and that the just-outside neighbours are not
blocked.  Exercised both at the `BitVec 32` level (the egress guard's
input) and through the full wire pipeline (sockaddr bytes → `clientIp` →
match, and `ipv4ToAddr` round-trip). -/
section EgressMask

def ip4 (a b c d : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (a * 16777216 + b * 65536 + c * 256 + d)

def egressBlocked (ip : BitVec 32) : Bool :=
  doNotQueryNets.any (fun e => e.matches ip)

-- upper half of every blocked range IS blocked
#guard egressBlocked (ip4 10 128 0 1)      -- 10.0.0.0/8 upper half
#guard egressBlocked (ip4 172 24 0 1)      -- 172.16.0.0/12 upper half
#guard egressBlocked (ip4 192 168 200 5)   -- 192.168.0.0/16 upper half
#guard egressBlocked (ip4 100 100 0 1)     -- 100.64.0.0/10 upper half
#guard egressBlocked (ip4 169 254 200 1)   -- 169.254.0.0/16 upper half
#guard egressBlocked (ip4 249 0 0 1)       -- 240.0.0.0/4 upper half
#guard egressBlocked (ip4 127 255 255 255) -- 127/8 top
#guard egressBlocked (ip4 0 200 0 1)       -- 0/8 upper half
-- just-outside neighbours are NOT blocked
#guard !egressBlocked (ip4 11 0 0 1)
#guard !egressBlocked (ip4 172 32 0 1)
#guard !egressBlocked (ip4 192 169 0 1)
#guard !egressBlocked (ip4 100 128 0 1)
#guard !egressBlocked (ip4 9 255 255 255)
#guard !egressBlocked (ip4 169 253 255 255)
#guard !egressBlocked (ip4 239 255 255 255)
-- full pipeline from raw sockaddr bytes (as the ingress ACL consumes them)
#guard egressBlocked (clientIp ⟨#[10, 128, 0, 1, 0, 53]⟩)
#guard egressBlocked (clientIp ⟨#[172, 24, 0, 1, 0, 53]⟩)
#guard !egressBlocked (clientIp ⟨#[11, 0, 0, 1, 0, 53]⟩)
-- egress-address round-trip: the IP the guard checked is the IP on the wire
#guard clientIp (ipv4ToAddr (ip4 10 128 0 1)) == ip4 10 128 0 1
#guard clientIp (ipv4ToAddr (ip4 249 7 3 9)) == ip4 249 7 3 9
#guard clientIp (ipv4ToAddr (ip4 8 8 8 8)) == ip4 8 8 8 8
-- blockedEgress itself (egressBypassEnabled is defeq false in proofs/tests)
#guard blockedEgress (ip4 10 128 0 1)
#guard !blockedEgress (ip4 8 8 8 8)

end EgressMask

/-! ## EDNS0 sizing / negotiation conformance vectors (RFC 6891)

Findings 049/050/063 (clientCap trio), 056 (multi-OPT FORMERR), 065 (BADVERS),
016 (OPT echo). -/

section EdnsVectors

/-- An OPT pseudo-RR with a chosen advertised size and TTL field (the TTL
    packs EXTENDED-RCODE hi byte | VERSION | DO/Z, RFC 6891 §6.1.3). -/
def mkOptRR (bufsize : Nat) (ttl : BitVec 32 := 0) : ByteArray :=
  DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode
    { name := ⟨#[0]⟩, type := 41, «class» := BitVec.ofNat 16 bufsize,
      ttl := ttl, rdlength := 0, rdata := ByteArray.empty })

def mkEdnsQuery (qname : ByteArray) (bufsize : Nat) (optTtl : BitVec 32 := 0)
    (dupOpt : Bool := false) : Format :=
  let base := mkQuery qname
  let opts := if dupOpt then #[mkOptRR bufsize optTtl, mkOptRR bufsize optTtl]
              else #[mkOptRR bufsize optTtl]
  { base with
    header := { base.header with arcount := BitVec.ofNat 16 opts.size }
    additional := opts }

/-- Upstream handler answering with `k` distinct A records at the query owner
    (each RR ≈ 27 bytes on the wire for a 13-byte owner). -/
def multiAnswerHandler (k : Nat) (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := BitVec.ofNat 16 k }
      answer := (Array.range k).map fun i =>
        mkRR query.question[0]!.qname 1
          ⟨#[10, 0, UInt8.ofNat (i / 250), UInt8.ofNat (i % 250)]⟩ }

/-- Finding 049: a legacy (no-OPT) client asking for a >512-byte answer gets a
    reply capped at 512 bytes with TC=1 — never an over-size datagram. -/
def legacyBigAnswerTruncatedAt512 : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom)
    [multiAnswerHandler 30, multiAnswerHandler 30]
  let some (bytes, _) := st.sent[0]? | return false
  let .ok resp := Message.decode bytes | return false
  return bytes.size ≤ 512 && resp.header.tc == 1
    && (Edns.findOptSize resp.additional).isNone

/-- Finding 050: a client advertising a 600-byte buffer is truncated at 600
    (not 1232) when the answer exceeds it. -/
def edns600SmallBufferHonored : Bool := Id.run do
  let (_, st) := runServe (mkEdnsQuery exampleCom 600)
    [multiAnswerHandler 30, multiAnswerHandler 30]
  let some (bytes, _) := st.sent[0]? | return false
  let .ok resp := Message.decode bytes | return false
  return bytes.size ≤ 600 && resp.header.tc == 1

/-- Finding 050/063 (fits side): a 600-byte-buffer client whose answer fits in
    600 bytes gets it whole — beyond the legacy 512 floor, untruncated. -/
def edns600MidSizeAnswerDelivered : Bool := Id.run do
  let (_, st) := runServe (mkEdnsQuery exampleCom 600)
    [multiAnswerHandler 18, multiAnswerHandler 18]
  let some (bytes, _) := st.sent[0]? | return false
  let .ok resp := Message.decode bytes | return false
  return 512 < bytes.size && bytes.size ≤ 600 && resp.header.tc == 0
    && resp.answer.size == 18

/-- Finding 063: a client advertising 4096 gets a >512-byte answer whole (up
    to our 1232 clamp) — no over-truncation at 512. -/
def edns4096LargeAnswerUntruncated : Bool := Id.run do
  let (_, st) := runServe (mkEdnsQuery exampleCom 4096)
    [multiAnswerHandler 30, multiAnswerHandler 30]
  let some (bytes, _) := st.sent[0]? | return false
  let .ok resp := Message.decode bytes | return false
  return 512 < bytes.size && bytes.size ≤ 1232 && resp.header.tc == 0
    && resp.answer.size == 30

/-- Finding 016: the reply to an EDNS query carries exactly one OPT
    advertising our 1232 buffer; the reply to a legacy query carries none. -/
def ednsReplyCarriesOpt : Bool := Id.run do
  let (_, st) := runServe (mkEdnsQuery exampleCom 1232)
    [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  return Edns.countOpt resp.additional == 1
    && Edns.findOptSize resp.additional == some 1232

def legacyReplyNoOpt : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  return Edns.countOpt resp.additional == 0

/-- Finding 056: two OPT RRs → FORMERR before any resolution (RFC 6891
    §6.1.1). -/
def multiOptFormerr : Bool := Id.run do
  let (_, st) := runServe (mkEdnsQuery exampleCom 1232 (dupOpt := true))
    [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty
    && resp.header.id == 0x1234

/-- Finding 065: EDNS version 1 → BADVERS (header rcode NOERROR + OPT
    ext-rcode high byte 1, version 0), no resolution (RFC 6891 §6.1.3). -/
def badVersionBadvers : Bool := Id.run do
  let (_, st) := runServe (mkEdnsQuery exampleCom 1232 (optTtl := BitVec.ofNat 32 (1 <<< 16)))
    [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  let some optBytes := resp.additional[0]? | return false
  let some rr := Edns.parseRR optBytes | return false
  return resp.header.rcode == Rcode.noError && st.exchanged.isEmpty
    && rr.type == 41
    && ((rr.ttl >>> 24) &&& 0xFF) == 1
    && ((rr.ttl >>> 16) &&& 0xFF) == 0

#guard legacyBigAnswerTruncatedAt512
#guard edns600SmallBufferHonored
#guard edns600MidSizeAnswerDelivered
#guard edns4096LargeAnswerUntruncated
#guard ednsReplyCarriesOpt
#guard legacyReplyNoOpt
#guard multiOptFormerr
#guard badVersionBadvers

end EdnsVectors

section IngressGates

/-! ### Query-shape gate conformance vectors (032 / 042 / 044b / 033)

Mock-loop duals of the classifier pins in `Proof/Server.lean`
(`queryProblem_spec`): each malformed query shape gets exactly the rcode a
stock recursive resolver gives it (verified against unbound 1.24.2), no
resolution is attempted (`exchanged.isEmpty`), and the reply never echoes the
client's TC bit or stuffed sections. -/

/-- (032): a TC-set query is FORMERRed with TC *cleared* in the reply (the
    classifier gate + the `finalizeForClient` no-echo pin), and never reaches
    the resolver. -/
def tcSetQueryFormerr : Bool := Id.run do
  let q0 := mkQuery exampleCom
  let q := { q0 with header := { q0.header with tc := 1 } }
  let (_, st) := runServe q [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && resp.header.tc == 0
    && st.exchanged.isEmpty && resp.answer.isEmpty

#guard tcSetQueryFormerr

/-- (042): a query with a stuffed answer section is FORMERRed and the stuffing
    is not echoed back. -/
def stuffedAnswerFormerr : Bool := Id.run do
  let q0 := mkQuery exampleCom
  let q := { q0 with
    header := { q0.header with ancount := 1 }
    answer := #[mkRR exampleCom 1 aRdata] }
  let (_, st) := runServe q [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty
    && resp.answer.isEmpty

#guard stuffedAnswerFormerr

/-- (042): a query with a stuffed authority section is FORMERRed. -/
def stuffedAuthorityFormerr : Bool := Id.run do
  let q0 := mkQuery exampleCom
  let q := { q0 with
    header := { q0.header with nscount := 1 }
    authority := #[mkRR comName 2 nsName] }
  let (_, st) := runServe q [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty
    && resp.authority.isEmpty

#guard stuffedAuthorityFormerr

/-- (042)/(056): a second additional record (here two OPTs, RFC 6891 §6.1.1
    forbids more than one) is FORMERRed. -/
def doubleAdditionalFormerr : Bool := Id.run do
  let q0 := mkQuery exampleCom
  let q := { q0 with
    header := { q0.header with arcount := 2 }
    additional := #[Edns.optRRBytes 1232, Edns.optRRBytes 512] }
  let (_, st) := runServe q [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty

#guard doubleAdditionalFormerr

/-- (042) negative control: a single well-formed EDNS OPT in the additional
    section is NOT stuffing — the query is served normally. -/
def optAdditionalStillServed : Bool := Id.run do
  let q0 := mkQuery exampleCom
  let q := { q0 with
    header := { q0.header with arcount := 1 }
    additional := #[Edns.optRRBytes 1232] }
  let (_, st) := runServe q [answerHandler, answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 1

#guard optAdditionalStillServed

/-- (044b): AXFR from a recursive resolver → REFUSED (no zone to transfer,
    RFC 5936; unbound parity), before any resolution. -/
def axfrRefused : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom 252) [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.refused && st.exchanged.isEmpty

#guard axfrRefused

/-- (044b): IXFR → REFUSED, as for AXFR. -/
def ixfrRefused : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom 251) [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.refused && st.exchanged.isEmpty

#guard ixfrRefused

/-- (044b): OPT as a QTYPE → FORMERR (RFC 6891 §6.1.1: OPT is not a query
    type; unbound parity). -/
def optQtypeFormerr : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom 41) [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty

#guard optQtypeFormerr

/-- (044b): MAILB (253, a meta-QTYPE) → FORMERR; reserved meta range likewise. -/
def mailbQtypeFormerr : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom 253) [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty

#guard mailbQtypeFormerr

/-- (033): a multi-question query is FORMERRed echoing ONLY the first question
    (`qdcount` = 1, no over-echo of the client's stuffing). -/
def multiQuestionFormerrTrimmedEcho : Bool := Id.run do
  let q0 := mkQuery exampleCom
  let q := { q0 with
    header := { q0.header with qdcount := 2 }
    question := q0.question.push { qname := comName, qtype := 1, qclass := 1 } }
  let (_, st) := runServe q [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.formatError && st.exchanged.isEmpty
    && resp.question.size == 1 && resp.header.qdcount == 1
    && resp.question[0]?.any (fun qu => qu.qname == exampleCom)

#guard multiQuestionFormerrTrimmedEcho

end IngressGates

/-! ### Finding 068: qtype-relevant delivery (RFC 1034 §3.6.2)

The owner scrub (`scrubAnswerB`) keeps every record owned on the CNAME chain
regardless of TYPE, so an entitled answer could smuggle a same-owner
wrong-type record (e.g. a junk TXT riding along with the queried A) into the
delivered answer section.  `typeScrubB` now drops every delivered record that
neither matches the query type nor is a chase-chain CNAME.  Pinned by
`VeriDNS.Proof.Server.deliveredResponse_answer_qtype_relevant` and
`VeriDNS.Spec.Net.typeScrub_relevant`. -/
section QtypeRelevantVectors

def evilTxtRdata : ByteArray :=
  let s := "attacker-data".toUTF8
  ByteArray.mk #[UInt8.ofNat s.size] ++ s

/-- An authoritative answer carrying the queried A record PLUS a same-owner
    junk TXT record. -/
def junkRideAlongHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 2 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata,
                  mkRR query.question[0]!.qname 16 evilTxtRdata] }

def rrTypeOf (b : ByteArray) : Option (BitVec 16) :=
  match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | .ok (rr, _) => some rr.type
  | .error _ => none

/-- The delivered answer to an A query contains ONLY A records: the same-owner
    junk TXT is scrubbed at delivery (was: both records delivered). -/
def wrongTypeRideAlongScrubbed : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [junkRideAlongHandler, junkRideAlongHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError
    && resp.answer.size == 1
    && resp.header.ancount == 1
    && resp.answer.all (fun b => rrTypeOf b == some 1)
    && resp.header.id == 0x1234

#guard wrongTypeRideAlongScrubbed

def chainTargetName : ByteArray := wireName ["target", "com"]

/-- CNAME at the query name, A at the chain target, filler A for probe
    rounds. -/
def cnameChainHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    let qn := query.question[0]!.qname
    if DomainName.nameEqCI qn exampleCom then
      some <| Message.encode
        { query with
          header := { query.header with qr := 1, aa := 1, ancount := 1 }
          answer := #[mkRR qn 5 chainTargetName] }
    else if DomainName.nameEqCI qn chainTargetName then
      some <| Message.encode
        { query with
          header := { query.header with qr := 1, aa := 1, ancount := 1 }
          answer := #[mkRR qn 1 aRdata] }
    else
      some <| Message.encode
        { query with
          header := { query.header with qr := 1, aa := 1, ancount := 1 }
          answer := #[mkRR qn 1 aRdata] }

/-- Regression guard: the qtype filter must KEEP chase-chain CNAMEs — a chased
    A answer still delivers the CNAME link plus the terminal A record
    (RFC 1034 §3.6.2). -/
def cnameChainSurvivesTypeScrub : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom)
    [cnameChainHandler, cnameChainHandler, cnameChainHandler,
     cnameChainHandler, cnameChainHandler, cnameChainHandler]
  let some resp := sentResponse st | return false
  let types := resp.answer.filterMap rrTypeOf
  return resp.header.rcode == Rcode.noError
    && resp.answer.size == 2
    && types.contains 5
    && types.contains 1
    && resp.header.id == 0x1234

#guard cnameChainSurvivesTypeScrub

end QtypeRelevantVectors

/-! ### Finding 039: a CNAME-target NXDOMAIN must not be wide-keyed at the
original name (RFC 6604 §3)

The NXDOMAIN terminating a CNAME chain denies the CHAIN-FINAL target, not the
original query name — that name exists (it owns a CNAME).  The serve-layer
negative store must NOT plant a name-wide `lookupNxdomain` entry at the echoed
qname (the SOA below is deliberately an ancestor of BOTH names, so only the
empty-answer gate of `negativelyCacheable` blocks the wide-key store).  Pinned
by `VeriDNS.Proof.Server.negativelyCacheable_chained_nxdomain` and the model
dual `VeriDNS.Spec.Net.absorbNeg_chained_nxdomain`. -/
section ChainedNxdomainVectors

/-- CNAME at the original name; SOA-proved NXDOMAIN for every other name
    (in particular the chain target).  The SOA owner (`com`) is an ancestor of
    both `exampleCom` and `chainTargetName`. -/
def cnameNxdomainHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    let qn := query.question[0]!.qname
    if DomainName.nameEqCI qn exampleCom then
      some <| Message.encode
        { query with
          header := { query.header with qr := 1, aa := 1, ancount := 1 }
          answer := #[mkRR qn 5 chainTargetName] }
    else
      some <| Message.encode
        { query with
          header := { query.header with
                      qr := 1
                      aa := 1
                      rcode := Rcode.nameError
                      nscount := 1 }
          authority := #[mkRR comName 6 soaRdata (ttl := 60)] }

def cnameNxScript : List (ByteArray → Option ByteArray) :=
  [cnameNxdomainHandler, cnameNxdomainHandler, cnameNxdomainHandler,
   cnameNxdomainHandler, cnameNxdomainHandler, cnameNxdomainHandler]

/-- The client still receives the NXDOMAIN rcode with the chain link in the
    answer (RFC 6604 §3, matches unbound), but NO negative entry is keyed at
    the original name. -/
def chainedNxdomainNotWideKeyed : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) cnameNxScript
  let some r1 := sentResponse st1 | return false
  return r1.header.rcode == Rcode.nameError
    && (r1.answer.filterMap rrTypeOf).contains 5
    && cache1.negatives.all (fun e => !DomainName.nameEqCI e.name exampleCom)

#guard chainedNxdomainNotWideKeyed

/-- A follow-up query for a DIFFERENT type at the original name is NOT denied
    from the cache: a qtype=CNAME query after the chained NXDOMAIN answers
    NOERROR with the CNAME record (was: NXDOMAIN served from the wide-key
    negative). -/
def otherTypeAfterChainedNxdomainNotDenied : Bool := Id.run do
  let (cache1, _) := runServe (mkQuery exampleCom) cnameNxScript
  let (_, st2) := runServe (mkQuery exampleCom (qtype := 5)) cnameNxScript cache1
  let some r2 := sentResponse st2 | return false
  return r2.header.rcode == Rcode.noError
    && (r2.answer.filterMap rrTypeOf).contains 5

#guard otherTypeAfterChainedNxdomainNotDenied

end ChainedNxdomainVectors

/-! ### Finding 019: the CNAME conduit caches ONLY the chased link

The resolver-core chase arm used to cache every qname-owned record of ANY type
from a CNAME response (`ownerRaws`); a junk same-owner record riding the
chased CNAME entered the cache.  The arm now caches the `cnameRaws` slice
(owner ∧ type=CNAME), in lockstep with the model `Response.cnameOwned` in the
`answerCname`/`trustedCname` rules. -/
section CnameConduitVectors

/-- CNAME + junk same-owner TXT at the original name; A at the chain
    target. -/
def cnameJunkHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query =>
    let qn := query.question[0]!.qname
    if DomainName.nameEqCI qn exampleCom then
      some <| Message.encode
        { query with
          header := { query.header with qr := 1, aa := 1, ancount := 2 }
          answer := #[mkRR qn 5 chainTargetName, mkRR qn 16 evilTxtRdata] }
    else
      some <| Message.encode
        { query with
          header := { query.header with qr := 1, aa := 1, ancount := 1 }
          answer := #[mkRR qn 1 aRdata] }

/-- After the chase, the chased CNAME is cached at the original name but the
    junk same-owner TXT is NOT (was: both were cached by the chase arm). -/
def junkRideAlongCnameNotCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom)
    [cnameJunkHandler, cnameJunkHandler, cnameJunkHandler,
     cnameJunkHandler, cnameJunkHandler, cnameJunkHandler]
  let some r1 := sentResponse st1 | return false
  return r1.header.rcode == Rcode.noError
    && cache1.records.any (fun e =>
        DomainName.nameEqCI e.rr.name exampleCom && e.rr.type == 5)
    && cache1.records.all (fun e =>
        !(DomainName.nameEqCI e.rr.name exampleCom && e.rr.type == 16))

#guard junkRideAlongCnameNotCached

end CnameConduitVectors

/-! ### Finding 053: 0x20-cased rdata names must not defeat cache dedup -/

section CiDedup

def nsRdataLower : ByteArray := wireName ["ns1", "example", "com"]
def nsRdataUpper : ByteArray := wireName ["NS1", "EXAMPLE", "com"]

/-- Two direct stores of the same NS record whose rdata differs only in 0x20
case (the per-retry case-randomization echo) dedup to ONE cache member
(RFC 4343 §3). Before the `rdataEqCI` fix this returned 2. -/
def ciDedupOneMember : Bool :=
  let rr1 : ResourceRecord :=
    { name := exampleCom, type := 2, «class» := 1, ttl := 300,
      rdlength := BitVec.ofNat 16 nsRdataLower.size, rdata := nsRdataLower }
  let rr2 : ResourceRecord :=
    { rr1 with rdata := nsRdataUpper, rdlength := BitVec.ofNat 16 nsRdataUpper.size }
  let c := (DnsCache.empty.storeChecked rr1 .authoritySection 1000).storeChecked
    rr2 .authoritySection 1000
  c.records.size == 1

#guard ciDedupOneMember

/-- The same property through the real cache write path: two upstream rounds
(`cacheUnlessTruncated`, same second) delivering the case-varied NS raw bytes
leave ONE member under the RRset key. -/
def ciDedupViaCachePath : Bool :=
  let resp := mkQuery exampleCom  -- any tc=0 Format works as the write gate
  let raw1 := mkRR exampleCom 2 nsRdataLower
  let raw2 := mkRR exampleCom 2 nsRdataUpper
  let c1 := Resolver.cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
    DnsCache.empty resp #[raw1] (Resolver.credAuthority true) 1000
  let c2 := Resolver.cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
    c1 resp #[raw2] (Resolver.credAuthority true) 1000
  (c2.records.filter (fun e =>
    DomainName.nameEqCI e.rr.name exampleCom && e.rr.type == 2)).size == 1

#guard ciDedupViaCachePath

/-- RFC 3597 §7 boundary: an UNKNOWN-type record's rdata is opaque bytes —
case-varied rdata of an unknown type is a DIFFERENT record and both members
are kept (no rewriting/folding of unknown types). -/
def ciUnknownTypeNotFolded : Bool :=
  let t : BitVec 16 := 4242
  let rr1 : ResourceRecord :=
    { name := exampleCom, type := t, «class» := 1, ttl := 300,
      rdlength := BitVec.ofNat 16 nsRdataLower.size, rdata := nsRdataLower }
  let rr2 : ResourceRecord :=
    { rr1 with rdata := nsRdataUpper, rdlength := BitVec.ofNat 16 nsRdataUpper.size }
  let c := (DnsCache.empty.storeChecked rr1 .authoritySection 1000).storeChecked
    rr2 .authoritySection 1000
  c.records.size == 2

#guard ciUnknownTypeNotFolded

end CiDedup

/-! ### Finding 059 (documented deviation): DS queries at a cached zone cut -/

section DsRouting

/-- **FINDING 059, intended-behavior marker.** `stepFindServers.walkNs` is
qtype-blind and starts the NS walk at `sname` itself, so once the CHILD's NS
set is cached, a qtype=DS query descends to the CHILD zone — but DS RRs live
in the PARENT (RFC 4035 §3.1.4.1): the walk for DS should stop one label
short of the cut. This guard documents TODAY's behavior (walk matches at the
child apex, matchCount = 2 labels); the INTENDED behavior when the
qtype-aware descent lands is a parent-side match (matchCount = 1) — flip
this guard then. See the ScopeLedger `behaviour` row on
`resolveWithIO_verdict_sound` for why the fix is deferred (walkNs is
mirrored in lockstep by the model findServers rule, findServersTouches, and
the SentMinimised ladder). -/
def dsWalkTargetsChildToday : Bool :=
  let nsRR : ResourceRecord :=
    { name := exampleCom, type := 2, «class» := 1, ttl := 300,
      rdlength := BitVec.ofNat 16 nsName.size, rdata := nsName }
  let cache := DnsCache.empty.storeChecked nsRR .authoritySection 1000
  match Resolver.stepFindServers.walkNs (C := DnsCache) (RR := ResourceRecord)
      exampleCom cache 2 1 1000 128 with
  | some (_, mc) => mc == 2   -- child apex captured the walk (intended for DS: 1)
  | none => false

#guard dsWalkTargetsChildToday

end DsRouting

/-! ### Finding 060a: DNAME (type 39) and the delivery scrub -/

section DnameScrub

def dnameType : BitVec 16 := 39

/-- When qtype=DNAME the DNAME record IS the entitled answer: its owner is
the qname (the chain-reachable seed), so `scrubAnswerB` delivers it — the
scrub filters by owner reachability, never by type. -/
def dnameAtQnameDelivered : Bool :=
  let raw := mkRR exampleCom dnameType (wireName ["example", "net"])
  (Resolver.scrubAnswerB (RR := ResourceRecord) exampleCom #[raw]).size == 1

#guard dnameAtQnameDelivered

/-- **FINDING 060a, documented deviation.** An upstream DNAME accompanying
its RFC 6672 §3.2 synthesized CNAME is scrubbed from the delivered answer:
the DNAME's owner (an ANCESTOR of the chain link) is not itself
chain-reachable, so only the synthesized CNAME survives. Correctness is
preserved — a DNAME-oblivious client follows the delivered CNAME — but
unbound forwards both. INTENDED (when the scrub gains the
type-39-owner-is-strict-ancestor-of-a-chain-link arm): size 2 — flip this
guard then. See the ScopeLedger `behaviour` row on
`serveDatagram_verdict_sound`. -/
def dnameChainLinkScrubbedToday : Bool :=
  let dname := mkRR exampleCom dnameType (wireName ["example", "net"])
  let synthCname := mkRR wwwExampleCom 5 (wireName ["www", "example", "net"])
  let scrubbed := Resolver.scrubAnswerB (RR := ResourceRecord) wwwExampleCom
    #[dname, synthCname]
  scrubbed.size == 1

#guard dnameChainLinkScrubbedToday

end DnameScrub

end VeriDNS.Test.Loop
