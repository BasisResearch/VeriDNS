import VeriDNS.Impl.Server

/-!
# Compile-time verification of the IO shim

`serveOne` / `resolveWithIO` / `ioResumeLoop` are parametric over the
`UdpSocket` typeclass, so the whole serving loop runs in a pure `StateM`
over a scripted mock socket — only the C FFI layer sits outside. Each
`#guard` below evaluates at compile time: the build fails if the loop's
end-to-end behavior regresses.

Covered: direct answers (ID restoration, RFC 1035 §4.1.1 flag hygiene),
spoofed-ID rejection (RFC 5452 §9.1), iterative delegation chase
(RFC 1034 §5.3.3 4b), negative caching with qtype invariance and the §6
SOA authority (RFC 2308), and query hygiene (REFUSED for RD=0).
-/

namespace VeriDNS.Test.Loop

open VeriDNS.Spec
open VeriDNS.Impl
open VeriDNS.Impl.Server
open VeriDNS.Impl.SList
open VeriDNS.Impl.Cache

/-- The mock exchange socket's local binding (delivery address of
    well-behaved responses). -/
def mockLocal : ByteArray := ⟨#[192, 168, 0, 2, 0xAB, 0xCD]⟩

/-- Scripted-socket state: one inbound client datagram, a script of
    upstream exchange handlers (query ↦ response; an exhausted script is
    a timeout), and everything the server sent back. `spoofSource`
    overrides the source address the transport reports for every scripted
    response (off-path attacker); `spoofDest` overrides the reported
    delivery address. -/
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
        -- the transport REPORTS addressing; the Lean gate decides.
        pure (some { payload := resp
                     source := s.spoofSource.getD addr
                     destination := s.spoofDest.getD mockLocal
                     localAddr := mockLocal })

-- ## Wire helpers

/-- ["example", "com"] → `7example3com0` wire bytes. -/
def wireName (labels : List String) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for l in labels do
    out := out.push (UInt8.ofNat l.length)
    out := out ++ l.toUTF8
  return out.push 0

def exampleCom : ByteArray := wireName ["example", "com"]
def comName : ByteArray := wireName ["com"]
def nsName : ByteArray := wireName ["ns1", "test"]
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

-- ## Upstream handlers

/-- Authoritative answer: echo id + question, one A record. -/
def answerHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, aa := 1, ancount := 1 }
      answer := #[mkRR query.question[0]!.qname 1 aRdata] }

/-- Forged answer: correct content but the WRONG transaction ID. -/
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

/-- Referral: no answer; NS for `com` (closer than SBELT's root match
    count) with glue for the delegated server. -/
def referralHandler (q : ByteArray) : Option ByteArray :=
  match Message.decode q with
  | .error _ => none
  | .ok query => some <| Message.encode
    { query with
      header := { query.header with qr := 1, nscount := 1, arcount := 1 }
      authority := #[mkRR comName 2 nsName]
      additional := #[mkRR nsName 1 ⟨#[10, 0, 0, 53]⟩] }

/-- SOA rdata: MNAME + RNAME + serial/refresh/retry/expire + MINIMUM 60. -/
def soaRdata : ByteArray :=
  wireName ["ns1", "test"] ++ wireName ["host", "test"] ++
  ⟨#[0, 0, 0, 1, 0, 0, 14, 16, 0, 0, 3, 132, 0, 9, 58, 128, 0, 0, 0, 60]⟩

/-- NXDOMAIN carrying the RFC 2308 §3 SOA in the authority section. -/
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

-- ## Harness

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

-- ## 1. Direct answer: ID restored, §4.1.1 flag hygiene, answer delivered

def directAnswer : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [answerHandler]
  let some resp := sentResponse st | return false
  return st.sent.size == 1 &&
    resp.header.id == 0x1234 && resp.header.qr == 1 &&
    resp.header.ra == 1 && resp.header.aa == 0 && resp.header.z == 0 &&
    resp.header.rcode == Rcode.noError && resp.answer.size == 1 &&
    resp.question[0]?.any (fun qu => qu.qname == exampleCom && qu.qtype == 1)

#guard directAnswer

-- ## 2. RFC 5452: a forged-ID response must never reach the client

def spoofRejected : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [spoofHandler]
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard spoofRejected

-- ## 2b. RFC 5452 §9.1: a response from the wrong source address must be
-- dropped by the Lean datagram gate (the transport does not filter)

def wrongSourceRejected : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr)
                           script := [answerHandler]
                           spoofSource := some ⟨#[6, 6, 6, 6, 0, 53]⟩ }
  let (_, st) := (serveOne (M := MockM) (Sock := Unit) () sbelt DnsCache.empty).run st0
  let some resp := sentResponse st | return false
  -- the (correct-ID!) answer arrived from the wrong address: rejected,
  -- upstream retried until fuel/servers exhausted, client gets SERVFAIL
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError &&
    resp.header.id == 0x1234

#guard wrongSourceRejected

-- ## 2c. RFC 5452 §9.1: a response delivered to the wrong destination
-- address (delivery metadata ≠ the binding the query left from) is dropped

def wrongDestRejected : Bool := Id.run do
  let query := mkQuery exampleCom
  let st0 : MockState := { inbox := (Message.encode query, clientAddr)
                           script := [answerHandler]
                           spoofDest := some ⟨#[10, 9, 9, 9, 0xAB, 0xCD]⟩ }
  let (_, st) := (serveOne (M := MockM) (Sock := Unit) () sbelt DnsCache.empty).run st0
  let some resp := sentResponse st | return false
  return resp.answer.size == 0 && resp.header.rcode != Rcode.noError

#guard wrongDestRejected

-- ## 3. Iterative resolution: referral chased to the delegated server

def delegationChased : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom) [referralHandler, answerHandler]
  let some resp := sentResponse st | return false
  return st.exchanged.size == 2 && resp.header.rcode == Rcode.noError &&
    resp.answer.size == 1 && resp.header.id == 0x1234

#guard delegationChased

-- ## 4. RFC 2308: NXDOMAIN cached, qtype-invariant, §6 SOA served back

def negativeCached : Bool := Id.run do
  let (cache1, st1) := runServe (mkQuery exampleCom) [nxdomainHandler]
  let some r1 := sentResponse st1 | return false
  -- AAAA re-query answered ENTIRELY from cache (empty script = any
  -- upstream exchange would time out), SOA still in the authority
  let (_, st2) := runServe (mkQuery exampleCom 28) [] cache1
  let some r2 := sentResponse st2 | return false
  return r1.header.rcode == Rcode.nameError && r1.authority.size == 1 &&
    r2.header.rcode == Rcode.nameError && r2.authority.size == 1 &&
    st2.exchanged.isEmpty && r2.header.id == 0x1234

#guard negativeCached

-- ## 5. Query hygiene: RD=0 is REFUSED before any upstream work

def refusedIterative : Bool := Id.run do
  let (_, st) := runServe (mkQuery exampleCom (rd := 0)) [answerHandler]
  let some resp := sentResponse st | return false
  return resp.header.rcode == Rcode.refused && st.exchanged.isEmpty

#guard refusedIterative

end VeriDNS.Test.Loop
