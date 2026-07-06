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
      additional := #[mkRR nsName 1 ⟨#[10, 0, 0, 53]⟩] }

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
  (serveOne (M := MockM) (Sock := Unit) () sbelt cache).run st0

def sentResponse (st : MockState) : Option Format :=
  st.sent[0]?.bind fun (bytes, _) =>
    match Message.decode bytes with
    | .ok f => some f
    | .error _ => none

def directAnswer : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler]
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

def wrongSourceRejected : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr)
                           script := [answerHandler]
                           spoofSource := some ⟨#[6, 6, 6, 6, 0, 53]⟩ }
  let (_, st) := (serveOne (M := MockM) (Sock := Unit) () sbelt DnsCache.empty).run st0
  let some resp := sentResponse st | return false

  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard wrongSourceRejected

def wrongDestRejected : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr)
                           script := [answerHandler]
                           spoofDest := some ⟨#[10, 9, 9, 9, 0xAB, 0xCD]⟩ }
  let (_, st) := (serveOne (M := MockM) (Sock := Unit) () sbelt DnsCache.empty).run st0
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError

#guard wrongDestRejected

def delegationChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [referralHandler, answerHandler]
  let some resp := sentResponse st | return false
  return st.exchanged.size == 2 && resp.header.rcode == Rcode.noError &&
    resp.answer.size == 1 && resp.header.id == 0x1234

#guard delegationChased

def negativeCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [nxdomainHandler]
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

def theTree : Node ResourceRecord :=
  .mk ByteArray.empty #[] #[
    .mk (lab "com") #[] #[
      .mk (lab "example") #[aRR] #[
        .mk (lab "www") #[cnameRR] #[]]]]

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
  let (_, st) := runServe (mkQuery exampleCom) [treeHandler]
  let some resp := sentResponse st | return false
  let some bytes := resp.answer[0]? | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 1 &&
    bytes == RRParse.rrBytes aRR && resp.header.id == 0x1234

#guard treeAnswered

def treeMissing : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery missingName) [treeHandler]
  let some r1 := sentResponse st1 | return false
  let (_, st2) := runServe (mkQuery missingName 28) [] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.nameError &&
    r2.header.rcode == Rcode.nameError && st2.exchanged.isEmpty

#eval show IO Unit from do
  unless treeMissing do
    throw <| IO.userError "treeMissing regressed"

def treeCaseInsensitive : Bool := Id.run do
  let upper := wireName ["EXAMPLE", "COM"]
  let (_, st) := runServe (mkQuery upper) [treeHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 1

#guard treeCaseInsensitive

def treeChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery wwwExampleCom) [treeHandler, treeHandler]
  let some resp := sentResponse st | return false
  return st.exchanged.size == 2 && resp.header.rcode == Rcode.noError &&
    resp.answer.size == 2 && resp.header.id == 0x1234 &&
    resp.question[0]?.any (fun qu => qu.qname == wwwExampleCom)

#guard treeChased

def treeNodata : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom 15) [treeHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.noError && resp.answer.size == 0

#eval show IO Unit from do
  unless treeNodata do
    throw <| IO.userError "treeNodata regressed"

end TreeNetwork

end VeriDNS.Test.Loop
