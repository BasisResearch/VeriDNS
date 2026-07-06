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

/-- **Bounded retry over an optional action** — the transport-layer retransmit primitive
    for retransmit-before-failover. `retryOption act n` runs `act`, and on `none` (a lost/timed-out reply)
    retries up to `n` more times, returning the first `some`. It is a general combinator over any
    monad; its correctness contract is `retryOption_pure` (`Proof/Server.lean`): over a
    *deterministic* action it collapses to a single attempt — which is exactly why retransmitting
    the same datagram is invisible to the `Prog`-model soundness proof (whose `exchange` oracle is a
    pure function of the query), so `ioResumeLoop_sound` is untouched. Retransmit is pure liveness. -/
def retryOption {M : Type → Type} [Monad M] {α : Type} (act : M (Option α)) : Nat → M (Option α)
  | 0 => act
  | n + 1 => do
    match ← act with
    | some a => pure (some a)
    | none => retryOption act n

/-- Number of *extra* retransmissions of an unanswered query to the same server before failing it
    over (RFC 1035 §4.2.1 / §5.3.3 — a resolver retransmits before declaring a server dead). Total
    attempts per server per round = `retransmitLimit + 1`. -/
def retransmitLimit : Nat := 2

instance : UdpSocket IO UInt32 ByteArray where
  recvFrom fd maxBytes := recvFromRaw fd maxBytes.toUSize
  sendTo fd data addr := sendToRaw fd data addr
  now := nowRaw
  randomId := randomU16
  log msg := IO.eprintln s!"[veri-dns] {msg}"
  exchange q addr :=
    retryOption (do
      match ← exchangeRaw q addr with
      | none => pure none
      | some (payload, src, dst, loc) =>
        pure (some { payload := payload, source := src
                     destination := dst, localAddr := loc })) retransmitLimit

end VeriDNS.Impl.UdpSocket
