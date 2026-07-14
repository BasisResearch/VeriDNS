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

def retransmitFreshSecrets : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [fun _ => none, answerHandler, answerHandler]
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
    && q2.qname == DomainName.randomizeCase 7780 comName
    && q3.qname == DomainName.randomizeCase 7782 exampleCom
    && b1 != b2
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

def probeStrictNxdomainFinal : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery deepMissingName)
    [treeHandler, treeHandler, treeHandler]
  let some r1 := sentResponse st1 | return false
  let some bLast := st1.exchanged[2]? | return false
  let .ok sLast := Message.decode bLast | return false
  let some quLast := sLast.question[0]? | return false
  let (_, st2) := runServe (mkQuery probeMissing) [] cache1
  let some r2 := sentResponse st2 | return false
  return st1.exchanged.size == 3
    && r1.header.rcode == Rcode.nameError
    && r1.header.id == 0x1234
    && DomainName.nameEqCI quLast.qname probeMissing
    && quLast.qtype == 1
    && r2.header.rcode == Rcode.nameError
    && st2.exchanged.isEmpty

#eval show IO Unit from do
  unless probeStrictNxdomainFinal do
    throw <| IO.userError "probeStrictNxdomainFinal regressed"

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

end VeriDNS.Test.Loop
