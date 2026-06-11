import VeriDNS.Spec.Server

namespace VeriDNS.Impl.UdpSocket
open VeriDNS.Spec

/-- Create a UDP (IPv4, DGRAM) socket. Returns the file descriptor. -/
@[extern "veri_dns_udp_socket"]
opaque mkUdpSocket : IO UInt32

/-- Create a UDP socket with 2-second recv timeout for upstream queries. -/
@[extern "veri_dns_upstream_socket"]
opaque mkUpstreamSocket : IO UInt32

/-- Bind a socket fd to 0.0.0.0:port. -/
@[extern "veri_dns_bind"]
opaque bindSocket : UInt32 → UInt16 → IO Unit

/-- Send data to a 6-byte encoded address (4-byte IPv4 + 2-byte port big-endian). -/
@[extern "veri_dns_sendto"]
opaque sendToRaw : UInt32 → @& ByteArray → @& ByteArray → IO Unit

/-- Receive a UDP datagram. Returns (data, 6-byte sender address). -/
@[extern "veri_dns_recvfrom"]
opaque recvFromRaw : UInt32 → USize → IO (ByteArray × ByteArray)

/-- Current Unix time in seconds (cache expiry, RFC 1035 §6.1.3). -/
@[extern "veri_dns_now"]
opaque nowRaw : IO UInt32

/-- Unpredictable 16-bit query ID (RFC 5452 resilience; arc4random). -/
@[extern "veri_dns_random_u16"]
opaque randomU16 : IO UInt16

/-- One connected query exchange (RFC 5452 §9.1/§9.2): fresh socket,
    connect, send, recv with 2s timeout, close. `none` on timeout. -/
@[extern "veri_dns_exchange"]
opaque exchangeRaw : @& ByteArray → @& ByteArray → IO (Option ByteArray)

instance : UdpSocket IO UInt32 ByteArray where
  recvFrom fd maxBytes := recvFromRaw fd maxBytes.toUSize
  sendTo fd data addr := sendToRaw fd data addr
  now := nowRaw
  randomId := randomU16
  log msg := IO.eprintln s!"[veri-dns] {msg}"
  exchange := exchangeRaw

end VeriDNS.Impl.UdpSocket
