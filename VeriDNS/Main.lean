import VeriDNS

open VeriDNS.Impl.Server VeriDNS.Impl.SList VeriDNS.Impl.UdpSocket VeriDNS.Spec

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

def main : IO Unit := do
  let port : UInt16 := 5300
  IO.println s!"veri-dns: listening on UDP port {port}"
  let clientSock ← mkUdpSocket
  bindSocket clientSock port

  let sbelt := DnsSList.mkSbelt rootServers
  serverLoop clientSock sbelt
