import VeriDNS.Impl.UdpSocket




namespace VeriDNS.Test.ExchangeJunk

open VeriDNS.Impl.UdpSocket

def addr6 (a b c d : UInt8) (port : UInt16) : ByteArray :=
  ⟨#[a, b, c, d, UInt8.ofNat (port.toNat / 256), UInt8.ofNat (port.toNat % 256)]⟩

def mockPort : UInt16 := 5391
def junkPort : UInt16 := 5392

def serverAddr : ByteArray := addr6 127 0 0 1 mockPort

/-- Question section shared by the query and its legitimate reply:
    QNAME `www.foo.` · QTYPE A · QCLASS IN (an uncompressed question). -/
def question : Array UInt8 :=
  #[ 0x03, 0x77, 0x77, 0x77,       -- "www"
     0x03, 0x66, 0x6F, 0x6F,       -- "foo"
     0x00,                          -- root
     0x00, 0x01,                    -- QTYPE = A
     0x00, 0x01 ]                   -- QCLASS = IN

/-- Well-formed query: txid 0xABCD, RD=1, QDCOUNT=1, one question. -/
def queryBytes : ByteArray :=
  ⟨#[0xAB, 0xCD, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    ++ question⟩

/-- The legitimate reply: same txid, QR=1, echoes the question verbatim. -/
def replyBytes : ByteArray :=
  ⟨#[0xAB, 0xCD, 0x81, 0x80, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    ++ question⟩

/-- Content-junk that decodes as a header but fails the query match: same
    txid, but a DIFFERENT question (`bad.foo.`) — the shape of a spoof/stale
    datagram from the legitimate source:port that must NOT consume the round. -/
def junkContentBytes : ByteArray :=
  ⟨#[0xAB, 0xCD, 0x81, 0x80, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x03, 0x62, 0x61, 0x64,       -- "bad"
     0x03, 0x66, 0x6F, 0x6F,       -- "foo"
     0x00, 0x00, 0x01, 0x00, 0x01]⟩

/-- Short garbage (no DNS header) — the classic wrong-source junk payload. -/
def junkBytes : ByteArray := ⟨#[0xDE, 0xAD, 0xBE, 0xEF]⟩

def fail (msg : String) : IO Unit :=
  throw <| IO.userError s!"exchange-junk-test: {msg}"

def joinMock (t : Task (Except IO.Error Unit)) : IO Unit := do
  match t.get with
  | .ok _ => pure ()
  | .error e => throw e

def run : IO Unit := do
  let mockSock ← mkUdpSocket
  bindSocket mockSock mockPort
  let junkSock ← mkUdpSocket
  bindSocket junkSock junkPort

  -- Case 1: junk from a NON-queried source (junkPort), then the real reply
  -- from the queried source. Source filtering drops the former.
  let mock1 ← IO.asTask (prio := .dedicated) do
    let (_, client) ← recvFromRaw mockSock 512
    sendToRaw junkSock junkBytes client
    sendToRaw junkSock junkBytes client
    IO.sleep 50
    sendToRaw mockSock replyBytes client
  match ← exchangeRaw queryBytes serverAddr with
  | none => fail "case 1: got none — reply lost behind junk (or deadline hit)"
  | some (payload, src, _, _) =>
    unless src == serverAddr do
      fail "case 1: datagram from a non-queried source was returned"
    unless payload == replyBytes do
      fail "case 1: wrong payload returned"
  joinMock mock1
  IO.println "exchange-junk-test: case 1 OK (wrong-source junk skipped, real reply returned)"

  -- Case 2: junk-only from a non-queried source — no reply ever matches, so
  -- exchange must return none at the deadline (never a junk datagram).
  let mock2 ← IO.asTask (prio := .dedicated) do
    let (_, client) ← recvFromRaw mockSock 512
    for _ in [0:4] do
      sendToRaw junkSock junkBytes client
      IO.sleep 300
  let t0 ← IO.monoMsNow
  let r2 ← exchangeRaw queryBytes serverAddr
  let elapsed := (← IO.monoMsNow) - t0
  if r2.isSome then
    fail "case 2: a junk datagram was accepted as the reply"
  unless elapsed < 4000 do
    fail s!"case 2: deadline not enforced (took {elapsed}ms)"
  joinMock mock2
  IO.println s!"exchange-junk-test: case 2 OK (junk-only → none at deadline, {elapsed}ms)"

  -- Case 3 (single-shot pin): the exchange sends the query EXACTLY ONCE on the
  -- wire. A retransmit loop at the shim would show as >1 datagram here.
  let count ← IO.mkRef (0 : Nat)
  let sentinel : ByteArray := ⟨#[0x51, 0x51, 0x51, 0x51]⟩
  let mock3 ← IO.asTask (prio := .dedicated) do
    let mut go := true
    while go do
      let (payload, _) ← recvFromRaw mockSock 512
      if payload == sentinel then go := false
      else count.modify (· + 1)
  let t3 ← IO.monoMsNow
  let r3 ← VeriDNS.Spec.UdpSocket.exchange (M := IO) (Sock := UInt32) queryBytes serverAddr
  let elapsed3 := (← IO.monoMsNow) - t3
  if r3.isSome then
    fail "case 3: silent server produced a reply"
  unless elapsed3 < 4000 do
    fail s!"case 3: not single-shot in time ({elapsed3}ms — a transport retry loop re-appeared?)"
  IO.sleep 200
  sendToRaw junkSock sentinel serverAddr
  joinMock mock3
  let n ← count.get
  unless n == 1 do
    fail s!"case 3: expected exactly 1 datagram on the wire, saw {n}"
  IO.println s!"exchange-junk-test: case 3 OK (single-shot: 1 datagram, none at {elapsed3}ms)"

  -- Case 4 (finding 017): CONTENT junk from the LEGITIMATE source:port arrives
  -- first — same txid, wrong question — then the real reply. The pre-fix
  -- resolver treated the first datagram as the (failed) round; the read-until-
  -- match floor must skip it and deliver the real reply from the same source.
  let mock4 ← IO.asTask (prio := .dedicated) do
    let (_, client) ← recvFromRaw mockSock 512
    sendToRaw mockSock junkContentBytes client   -- legit source, wrong content
    sendToRaw mockSock junkContentBytes client
    IO.sleep 50
    sendToRaw mockSock replyBytes client          -- the genuine reply
  match ← exchangeRaw queryBytes serverAddr with
  | none => fail "case 4: got none — real reply lost behind same-source content junk"
  | some (payload, src, _, _) =>
    unless src == serverAddr do
      fail "case 4: datagram from a non-queried source was returned"
    unless payload == replyBytes do
      fail "case 4: content junk from the legitimate source was accepted as the reply"
  joinMock mock4
  IO.println "exchange-junk-test: case 4 OK (same-source content junk skipped, real reply returned)"

  -- Case 5 (finding 017, deadline): content junk ONLY from the legitimate
  -- source — no matching reply ever arrives, so exchange returns none at the
  -- deadline rather than surfacing the junk.
  let mock5 ← IO.asTask (prio := .dedicated) do
    let (_, client) ← recvFromRaw mockSock 512
    for _ in [0:4] do
      sendToRaw mockSock junkContentBytes client
      IO.sleep 300
  let t5 ← IO.monoMsNow
  let r5 ← exchangeRaw queryBytes serverAddr
  let elapsed5 := (← IO.monoMsNow) - t5
  if r5.isSome then
    fail "case 5: same-source content junk was accepted as the reply"
  unless elapsed5 < 4000 do
    fail s!"case 5: deadline not enforced (took {elapsed5}ms)"
  joinMock mock5
  IO.println s!"exchange-junk-test: case 5 OK (same-source content junk only → none at deadline, {elapsed5}ms)"

end VeriDNS.Test.ExchangeJunk
