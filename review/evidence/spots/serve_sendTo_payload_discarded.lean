import VeriDNS.Proof.FreeIO

/-! SPOT (round 3 — spec-auditor): the client-facing send is a no-op in the Prog model.

    `FreeIO.lean:49`  sendTo _ _ _ := .pure ()
    `FreeIO.lean:54`  tcpSend _ _   := .pure ()

    Every serve-level capstone (serveDatagram_verdict_sound / _total /
    serveDatagram_depth1_adequate / serveSeq_* / serveTcpDatagram_*) is stated at
    M = Prog and its conclusion is a `Prog.run` value.  Since `sendTo`/`tcpSend`
    DISCARD their payload argument (reduce to `.pure ()` for ANY bytes), the exact
    datagram handed to the client is invisible to `Prog.run` — it is not recorded in
    the World, not in `World.trace`, and not an oracle event.

    SENSIBLE (should prove): sending `truncated` and sending `ByteArray.empty` are the
    SAME Prog program, by `rfl`.  So no theorem whose subject is a `Prog.run` of the
    serve pipeline can tell a correct reply from an empty/garbage one.
-/

open VeriDNS.Spec (UdpSocket)

example (sock : Unit) (truncated addr : ByteArray) :
    UdpSocket.sendTo (M := VeriDNS.Proof.FreeIO.Prog) sock truncated addr
      = UdpSocket.sendTo (M := VeriDNS.Proof.FreeIO.Prog) sock ByteArray.empty addr :=
  rfl

example (sock : Unit) (truncated addr : ByteArray) :
    UdpSocket.tcpSend (M := VeriDNS.Proof.FreeIO.Prog) (Addr := ByteArray) sock truncated
      = UdpSocket.tcpSend (M := VeriDNS.Proof.FreeIO.Prog) (Addr := ByteArray) sock ByteArray.empty :=
  rfl

/-- And both equal the trivial `pure ()`, i.e. the send carries no observable content. -/
example (sock : Unit) (bytes addr : ByteArray) :
    UdpSocket.sendTo (M := VeriDNS.Proof.FreeIO.Prog) sock bytes addr = pure () :=
  rfl
