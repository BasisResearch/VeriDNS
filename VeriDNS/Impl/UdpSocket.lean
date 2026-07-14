import VeriDNS.Spec.Server

namespace VeriDNS.Impl.UdpSocket
open VeriDNS.Spec

@[extern "veri_dns_udp_socket"]
opaque mkUdpSocket : IO UInt32

@[extern "veri_dns_upstream_socket"]
opaque mkUpstreamSocket : IO UInt32

@[extern "veri_dns_bind"]
opaque bindSocket : UInt32 → UInt16 → IO Unit

@[extern "veri_dns_sendto"]
opaque sendToRaw : UInt32 → @& ByteArray → @& ByteArray → IO Unit

@[extern "veri_dns_recvfrom"]
opaque recvFromRaw : UInt32 → USize → IO (ByteArray × ByteArray)

@[extern "veri_dns_now"]
opaque nowRaw : IO UInt32

@[extern "veri_dns_random_u16"]
opaque randomU16 : IO UInt16

@[extern "veri_dns_exchange"]
opaque exchangeRaw : @& ByteArray → @& ByteArray
    → IO (Option (ByteArray × ByteArray × ByteArray × ByteArray))

@[extern "veri_dns_tcp_exchange"]
opaque tcpExchangeRaw : @& ByteArray → @& ByteArray → IO (Option ByteArray)

@[extern "veri_dns_tcp_listen"]
opaque tcpListen : UInt16 → IO UInt32

@[extern "veri_dns_tcp_accept"]
opaque tcpAccept : UInt32 → IO (UInt32 × ByteArray)

@[extern "veri_dns_tcp_recv_msg"]
opaque tcpRecvMsg : UInt32 → IO (Option ByteArray)

@[extern "veri_dns_tcp_send"]
opaque tcpSendRaw : UInt32 → @& ByteArray → IO Unit

@[extern "veri_dns_tcp_close"]
opaque tcpClose : UInt32 → IO Unit

instance : UdpSocket IO UInt32 ByteArray where
  recvFrom fd maxBytes := recvFromRaw fd maxBytes.toUSize
  sendTo fd data addr := sendToRaw fd data addr
  now := nowRaw
  randomId := randomU16
  log msg := IO.eprintln s!"[veri-dns] {msg}"
  exchange q addr := do
    match ← exchangeRaw q addr with
    | none => pure none
    | some (payload, src, dst, loc) =>
      pure (some { payload := payload, source := src
                   destination := dst, localAddr := loc })
  tcpExchange q addr := tcpExchangeRaw q addr
  tcpSend connfd data := tcpSendRaw connfd data

end VeriDNS.Impl.UdpSocket
