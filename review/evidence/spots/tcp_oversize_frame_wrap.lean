/-! SPOT (round 2, NEW): the DNS-over-TCP send path silently WRAPS the 2-byte length
    prefix for responses whose encoding exceeds 65535 bytes, and every TCP serve
    capstone (`serveTcpDatagram_verdict_sound` / `_total`, ServeTcp.lean:118,:353;
    `unframeTcp_frameTcp`, TcpFraming.lean:38) GUARDS its client-recovery + decode
    round-trip clause behind `... .size ≤ 65535`, so the oversize regime is waived.

    serveTcpDatagram (Impl/Server.lean:821) sends `frameTcp (Message.encode response)`
    with NO truncation stage and NO size cap (unlike UDP's truncateUdp ≤ clientCap).

    Below: PROVE that for a 65536-byte payload, frameTcp emits a [0,0] length prefix
    and unframeTcp recovers the EMPTY string, not the payload — the receiver desyncs.
    A real framing spec must NOT leave this unconstrained. -/

namespace VeriDNS.Impl.TcpFraming

def lenPrefix (n : Nat) : ByteArray :=
  ⟨#[(n / 256).toUInt8, (n % 256).toUInt8]⟩

def frameTcp (payload : ByteArray) : ByteArray :=
  lenPrefix payload.size ++ payload

def unframeTcp (buf : ByteArray) : Option ByteArray :=
  if h : 2 ≤ buf.size then
    let len := (buf[0]'(by omega)).toNat * 256 + (buf[1]'(by omega)).toNat
    let body := buf.extract 2 (2 + len)
    if body.size = len then some body else none
  else none

-- A 65536-byte payload (one over the 16-bit frame limit).
def big : ByteArray := ByteArray.mk (Array.replicate 65536 (0 : UInt8))

theorem big_size : big.size = 65536 := by
  simp [big, ByteArray.size]

/-- (FACT) The length prefix of the oversize frame is [0,0] — the high byte wrapped. -/
theorem lenPrefix_wraps : lenPrefix big.size = ⟨#[0, 0]⟩ := by
  rw [big_size]; decide

/-- (NONSENSE that PROVES — the vacuity) unframeTcp on the framed 65536-byte payload
    recovers the EMPTY byte array, NOT `big`.  The send side therefore produces a frame
    the receiver reads as zero-length; the real payload becomes trailing desync bytes.
    No TCP capstone forbids this because each guards recovery behind size ≤ 65535. -/
theorem oversize_recovers_empty :
    unframeTcp (frameTcp big) = some (ByteArray.mk #[]) := by
  native_decide

/-- The recovered value is the empty array (size 0); `big` has size 65536.  So
    `unframeTcp (frameTcp big) ≠ some big`: the round-trip that the capstones
    prove for `size ≤ 65535` FAILS here, and nothing constrains it. -/
theorem oversize_not_big : (ByteArray.mk #[] : ByteArray).size ≠ big.size := by
  rw [big_size]; decide

end VeriDNS.Impl.TcpFraming
