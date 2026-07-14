import VeriDNS.Impl.UdpSocket




namespace VeriDNS.Test.ExchangeJunk

open VeriDNS.Impl.UdpSocket

def addr6 (a b c d : UInt8) (port : UInt16) : ByteArray :=
  ⟨#[a, b, c, d, UInt8.ofNat (port.toNat / 256), UInt8.ofNat (port.toNat % 256)]⟩

def mockPort : UInt16 := 5391
def junkPort : UInt16 := 5392

def serverAddr : ByteArray := addr6 127 0 0 1 mockPort

def queryBytes : ByteArray := ⟨#[0xAB, 0xCD, 0x01, 0x00]⟩
def junkBytes : ByteArray := ⟨#[0xDE, 0xAD, 0xBE, 0xEF]⟩
def replyBytes : ByteArray := ⟨#[0xAB, 0xCD, 0x81, 0x80]⟩

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
  IO.println "exchange-junk-test: case 1 OK (junk skipped, real reply returned)"

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

end VeriDNS.Test.ExchangeJunk
