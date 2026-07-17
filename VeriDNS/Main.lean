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
        -- `resp` is decode→sanitizeTtlsCap output (`forwardQuery`), so the
        -- writes below ingest only TTL-capped, OPT-stripped, canonically
        -- re-encoded records; `primeWrites` additionally keeps only IN
        -- NS/A-glue records and bounds the cache.  `ServePack_primeWrites`
        -- (Proof/ServeSequence.lean) proves the serve invariant pack holds
        -- on the result.
        let c2 := primeWrites cache resp now
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
  let (queryBytes, clientAddr) ← UdpSocket.recvFrom (M := IO) (Sock := UInt32) clientSock
    serveRecvSize
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


/-- Maximum concurrent TCP client connections (findings 057/067: a stalled
    client must not block other clients; unbound's `incoming-num-tcp` is 10). -/
def tcpMaxConns : Nat := 32

/-- Per-connection serving loop (RFC 7766 §6.2.1, finding 058): after
    answering, keep reading further length-prefixed queries on the same
    connection until EOF or the 3 s socket read timeout (`tcpRecvMsg` returns
    `none` for both), instead of closing after one query.  Each message is
    served by the verified `serveTcpDatagram`; cache and rate-bucket access go
    through the shared mutexes. -/
partial def tcpConnLoop (cacheMx : Std.Mutex DnsCache) (rbMx : Std.Mutex RateBucket)
    (conn : UInt32) (clientAddr : ByteArray)
    (acl : ClientAcl) (sbelt : DnsSList) : IO Unit := do
  match ← tcpRecvMsg conn with
  | none => pure ()  -- EOF, idle timeout, or short read: drop the connection
  | some queryBytes =>
    let allowed ← rbMx.atomically do
      match (← get).bump (clientIp clientAddr) with
      | none => pure false
      | some rb2 =>
        set rb2
        pure true
    if allowed then
      let snapshot ← cacheMx.atomically get
      let served ← (serveTcpDatagram (Sock := UInt32) conn acl sbelt snapshot
        queryBytes clientAddr : IO DnsCache)
      cacheMx.atomically do set ((← get).absorb served)
    tcpConnLoop cacheMx rbMx conn clientAddr acl sbelt

partial def tcpServeLoop (cacheMx : Std.Mutex DnsCache) (listenSock : UInt32)
    (acl : ClientAcl) (sbelt : DnsSList)
    (rbMx : Std.Mutex RateBucket) (connCount : Std.Mutex Nat)
    (untilSweep : Nat := sweepInterval) : IO Unit := do
  try
    let (conn, clientAddr) ← tcpAccept listenSock
    let admitted ← connCount.atomically do
      let n ← get
      if n < tcpMaxConns then
        set (n + 1)
        pure true
      else
        pure false
    if admitted then
      -- Findings 057/067: serve each connection on its own dedicated task so a
      -- stalled client (accepted but silent) cannot block the accept loop.
      let _ ← IO.asTask (do
        try
          tcpConnLoop cacheMx rbMx conn clientAddr acl sbelt
        catch e =>
          IO.eprintln s!"[veri-dns] tcp conn error: {e}"
        finally
          tcpClose conn
          connCount.atomically do set ((← get) - 1)) Task.Priority.dedicated
    else
      tcpClose conn  -- over the connection cap: shed load, keep accepting
  catch e =>
    IO.eprintln s!"[veri-dns] tcp serve error: {e}"
  match untilSweep with
  | 0 =>
    rbMx.atomically do set RateBucket.empty
    tcpServeLoop cacheMx listenSock acl sbelt rbMx connCount sweepInterval
  | n + 1 => tcpServeLoop cacheMx listenSock acl sbelt rbMx connCount n

/-- Listen port. Defaults to 5300; a test-only `VERI_DNS_LISTEN_PORT` override
    lets a differential rig run alongside a sibling worktree's resolver without
    a bind collision. Off by default, so production behaviour is unchanged. -/
private def resolvedListenPort : IO UInt16 := do
  match ← IO.getEnv "VERI_DNS_LISTEN_PORT" with
  | none => pure 5300
  | some s =>
    match s.toNat? with
    | some n => if n > 0 && n ≤ 0xFFFF then pure (UInt16.ofNat n) else pure 5300
    | none => pure 5300

def main : IO Unit := do
  let port : UInt16 ← resolvedListenPort
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
    let tcpRbMx ← Std.Mutex.new RateBucket.empty
    let tcpConnCount ← Std.Mutex.new (0 : Nat)
    let _ ← IO.asTask (tcpServeLoop cacheMx tcpSock defaultAcl sbelt tcpRbMx tcpConnCount)
      Task.Priority.dedicated
    IO.println s!"veri-dns: listening on TCP port {port}"
  catch e =>
    IO.eprintln s!"[veri-dns] TCP listen failed ({e}); serving UDP only"

  IO.println s!"veri-dns: listening on UDP port {port}"
  udpServeLoop cacheMx clientSock defaultAcl sbelt
