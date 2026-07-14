import VeriDNS.Impl.Server
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Cache
import VeriDNS.Impl.SList
import VeriDNS.Impl.UdpSocket
import VeriDNS.Impl.Message
import VeriDNS.Impl.ResourceRecord
import Std.Sync.Mutex

open VeriDNS.Impl.Server VeriDNS.Impl.SList VeriDNS.Impl.UdpSocket VeriDNS.Spec
open VeriDNS.Impl.Cache (DnsCache)

private def rootName (letter : UInt8) : ByteArray :=
  let label1 : ByteArray := ⟨#[1, letter]⟩
  let label2 : ByteArray := ⟨#[12, 114, 111, 111, 116, 45, 115, 101, 114, 118, 101, 114, 115]⟩
  let label3 : ByteArray := ⟨#[3, 110, 101, 116]⟩
  let null : ByteArray := ⟨#[0]⟩
  label1 ++ label2 ++ label3 ++ null

private def rootServers : Array (ByteArray × BitVec 32) :=
  #[ (rootName 97,  BitVec.ofNat 32 0xC6290004)
   , (rootName 98,  BitVec.ofNat 32 0xC7090EC9)
   , (rootName 99,  BitVec.ofNat 32 0xC0210E1E)
   , (rootName 100, BitVec.ofNat 32 0xC7075B0D)
   , (rootName 101, BitVec.ofNat 32 0xC0CBE60A)
   ]

def rootPrimeQuery : Format :=
  { header := { id := 0x5052, qr := 0, opcode := Opcode.query,
                aa := 0, tc := 0, rd := 0, ra := 0, z := 0, rcode := Rcode.noError,
                qdcount := 1, ancount := 0, nscount := 0, arcount := 0 }
    question := #[{ qname := ⟨#[0]⟩, qtype := 2, qclass := 1 }]
    answer := #[], authority := #[], additional := #[] }



def primeRootHints (roots : Array (ByteArray × BitVec 32))
    (cache : VeriDNS.Impl.Cache.DnsCache) (now : UInt32) :
    IO VeriDNS.Impl.Cache.DnsCache := do
  let root : ByteArray := ⟨#[0]⟩
  for (_, ip) in roots do
    let rid ← UdpSocket.randomId (M := IO) (Sock := UInt32) (Addr := ByteArray)
    let cid ← UdpSocket.randomId (M := IO) (Sock := UInt32) (Addr := ByteArray)
    let q := withSecrets rootPrimeQuery rid cid
    match ← forwardQuery (M := IO) (Sock := UInt32) q (ipv4ToAddr ip) with
    | none => continue
    | some resp₀ =>
      let some resp := acceptResponse q resp₀ | continue
      if resp.header.rcode == Rcode.noError
          && VeriDNS.Impl.Resolver.hasRRTypeIn (RR := ResourceRecord) resp.answer 2 then
        let c1 := VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := ResourceRecord) cache resp
          (VeriDNS.Impl.Resolver.bailiwickRaws (RR := ResourceRecord) root resp.answer)
          (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now
        let c2 := VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := ResourceRecord) c1 resp
          (VeriDNS.Impl.Resolver.bailiwickRaws (RR := ResourceRecord) root resp.additional)
          VeriDNS.Impl.Resolver.credAdditional now
        IO.println s!"veri-dns: root hints primed (an={resp.answer.size} ar={resp.additional.size})"
        return c2
  IO.println "veri-dns: root priming failed on all hints; serving from SBELT"
  return cache

private def parseIpv4 (s : String) : Option (BitVec 32) := do
  let parts := s.splitOn "."
  if parts.length ≠ 4 then none else
  let bytes ← parts.mapM (fun p => do
    let n ← p.toNat?
    if n ≤ 255 then some n else none)
  some (BitVec.ofNat 32 ((bytes[0]! <<< 24) ||| (bytes[1]! <<< 16)
    ||| (bytes[2]! <<< 8) ||| bytes[3]!))

private def resolvedRootServers : IO (Array (ByteArray × BitVec 32)) := do
  match ← IO.getEnv "VERI_DNS_ROOT_HINT" with
  | none => pure rootServers
  | some hp =>
    match parseIpv4 hp with
    | some ip =>
      IO.println s!"veri-dns: TEST root-hint override → {hp} (single mock root)"
      pure #[(rootName 97, ip)]
    | none =>
      IO.println s!"veri-dns: VERI_DNS_ROOT_HINT={hp} is not a dotted-quad IPv4; ignoring"
      pure rootServers


partial def udpServeLoop (cacheMx : Std.Mutex DnsCache) (clientSock : UInt32)
    (acl : ClientAcl) (sbelt : DnsSList)
    (rb : RateBucket := RateBucket.empty) (untilSweep : Nat := sweepInterval) : IO Unit := do
  let (queryBytes, clientAddr) ← UdpSocket.recvFrom (M := IO) (Sock := UInt32) clientSock 512
  let rb' ← match rb.bump (clientIp clientAddr) with
    | none => pure rb
    | some rb2 => do
      let snapshot ← cacheMx.atomically get
      let served ← (serveDatagram (Sock := UInt32) clientSock acl sbelt snapshot
        queryBytes clientAddr : IO DnsCache)
      cacheMx.atomically do set ((← get).absorb served)
      pure rb2
  match untilSweep with
  | 0 =>
    let nowT ← nowRaw
    cacheMx.atomically do set (DnsCache.sweep (← get) nowT)
    udpServeLoop cacheMx clientSock acl sbelt RateBucket.empty sweepInterval
  | n + 1 => udpServeLoop cacheMx clientSock acl sbelt rb' n


partial def tcpServeLoop (cacheMx : Std.Mutex DnsCache) (listenSock : UInt32)
    (acl : ClientAcl) (sbelt : DnsSList)
    (rb : RateBucket := RateBucket.empty) (untilSweep : Nat := sweepInterval) : IO Unit := do
  let rb' ← try
    let (conn, clientAddr) ← tcpAccept listenSock
    try
      match rb.bump (clientIp clientAddr) with
      | none => pure rb
      | some rb2 =>
        match ← tcpRecvMsg conn with
        | none => pure rb2
        | some queryBytes =>
          let snapshot ← cacheMx.atomically get
          let served ← (serveTcpDatagram (Sock := UInt32) conn acl sbelt snapshot
            queryBytes clientAddr : IO DnsCache)
          cacheMx.atomically do set ((← get).absorb served)
          pure rb2
    finally
      tcpClose conn
  catch e =>
    IO.eprintln s!"[veri-dns] tcp serve error: {e}"
    pure rb
  match untilSweep with
  | 0 => tcpServeLoop cacheMx listenSock acl sbelt RateBucket.empty sweepInterval
  | n + 1 => tcpServeLoop cacheMx listenSock acl sbelt rb' n

def main : IO Unit := do
  let port : UInt16 := 5300
  let clientSock ← mkUdpSocket
  bindSocket clientSock port

  let rootServers ← resolvedRootServers
  let sbelt := DnsSList.mkSbelt rootServers

  let now ← nowRaw
  IO.println "veri-dns: priming root hints"
  let primedCache ← primeRootHints rootServers VeriDNS.Impl.Cache.DnsCache.empty now
  let cacheMx ← Std.Mutex.new primedCache

  try
    let tcpSock ← tcpListen port
    let _ ← IO.asTask (tcpServeLoop cacheMx tcpSock defaultAcl sbelt) Task.Priority.dedicated
    IO.println s!"veri-dns: listening on TCP port {port}"
  catch e =>
    IO.eprintln s!"[veri-dns] TCP listen failed ({e}); serving UDP only"

  IO.println s!"veri-dns: listening on UDP port {port}"
  udpServeLoop cacheMx clientSock defaultAcl sbelt
