import VeriDNS

open VeriDNS.Impl.Server VeriDNS.Impl.SList VeriDNS.Impl.UdpSocket VeriDNS.Spec

/-- Encode a root server name as DNS wire format (length-prefixed labels + null). -/
private def rootName (letter : UInt8) : ByteArray :=
  let label1 : ByteArray := ⟨#[1, letter]⟩
  let label2 : ByteArray := ⟨#[12, 114, 111, 111, 116, 45, 115, 101, 114, 118, 101, 114, 115]⟩  -- "root-servers"
  let label3 : ByteArray := ⟨#[3, 110, 101, 116]⟩  -- "net"
  let null : ByteArray := ⟨#[0]⟩
  label1 ++ label2 ++ label3 ++ null

/-- RFC root server IPs as BitVec 32. Subset of 13 root servers. -/
private def rootServers : Array (ByteArray × BitVec 32) :=
  #[ (rootName 97,  BitVec.ofNat 32 0xC6290004)   -- a.root-servers.net  198.41.0.4
   , (rootName 98,  BitVec.ofNat 32 0xC7090EC9)   -- b.root-servers.net  199.9.14.201
   , (rootName 99,  BitVec.ofNat 32 0xC0210E1E)   -- c.root-servers.net  192.33.14.30
   , (rootName 100, BitVec.ofNat 32 0xC7075B0D)   -- d.root-servers.net  199.7.91.13
   , (rootName 101, BitVec.ofNat 32 0xC0CBE60A)   -- e.root-servers.net  192.203.230.10
   ]

def main : IO Unit := do
  let port : UInt16 := 5300
  IO.println s!"veri-dns: listening on UDP port {port}"
  let clientSock ← mkUdpSocket
  bindSocket clientSock port
  -- upstream queries use per-exchange connected sockets (RFC 5452 §9.1/§9.2)
  let sbelt := DnsSList.mkSbelt rootServers
  serverLoop clientSock sbelt
