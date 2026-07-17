import VeriDNS.Impl.Server
import VeriDNS.Impl.AnswerScrub
import VeriDNS.Impl.Message

/-!  Bench for finding 060c: large-RRset reply assembly.

Build and run:
  lake build bench-scrub && .lake/build/bin/bench-scrub [--old]

`--old` additionally times the PRE-060c shape of `scrubAnswerB` (which
recomputed `reachableNamesB` — the reference `reachIterB` iteration — inside
the per-record closure) at n ≤ 300, for a before/after comparison.  The new
`scrubAnswerB` result is asserted equal to the old shape's result.

Not part of `lake build`; not imported by the `VeriDNS` umbrella. -/

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.Server

/-- wire-format name `big.example.` -/
private def bigName : ByteArray :=
  ⟨#[3, 98, 105, 103, 7, 101, 120, 97, 109, 112, 108, 101, 0]⟩

/-- one canonical A RR at `bigName` with rdata = the 4 bytes of `i` -/
private def mkARR (i : Nat) : ByteArray :=
  DnsSerializer.runBytes do
    DnsSerializer.writeBytes bigName
    writeBV16 (1 : BitVec 16)   -- type A
    writeBV16 (1 : BitVec 16)   -- class IN
    writeBV32 (BitVec.ofNat 32 300) -- ttl
    writeBV16 (4 : BitVec 16)   -- rdlen
    DnsSerializer.writeUInt8 (UInt8.ofNat ((i / 16777216) % 256))
    DnsSerializer.writeUInt8 (UInt8.ofNat ((i / 65536) % 256))
    DnsSerializer.writeUInt8 (UInt8.ofNat ((i / 256) % 256))
    DnsSerializer.writeUInt8 (UInt8.ofNat (i % 256))

private def mkAnswer (n : Nat) : Array ByteArray :=
  (Array.range n).map mkARR

private def mkResp (n : Nat) : Format :=
  { header := { id := 0x1234, qr := 1, opcode := Opcode.query,
                aa := 0, tc := 0, rd := 1, ra := 1, z := 0, rcode := Rcode.noError,
                qdcount := 1, ancount := BitVec.ofNat 16 n, nscount := 0, arcount := 0 }
    question := #[{ qname := bigName, qtype := 1, qclass := 1 }]
    answer := mkAnswer n, authority := #[], additional := #[] }

/-- The PRE-060c body of `reachableNamesB`: the reference iteration
    (still in the library as `reachIterB`). -/
private def oldReachableNamesB (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  VeriDNS.Impl.Resolver.reachIterB (RR := ResourceRecord) answer answer.size #[qname]

/-- The PRE-060c body of `scrubAnswerB`: recomputes the reachable set inside
    the per-record closure. -/
private def oldScrubAnswerB (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  answer.filterMap (fun bytes =>
    match RRParse.parseRaw (RR := ResourceRecord) bytes with
    | some rr =>
      ((oldReachableNamesB qname answer).find?
          (fun m => VeriDNS.Impl.DomainName.nameEqCI (RRParse.rrName rr) m)).map
        (VeriDNS.Impl.Resolver.setOwnerB (RR := ResourceRecord) rr bytes)
    | none => none)

private def timeIt {α : Type} (label : String) (act : Unit → α) : IO α := do
  let t0 ← IO.monoNanosNow
  -- `IO.lazyPure` is opaque to the compiler: the thunk is forced HERE, between
  -- the two clock reads (a bare pure `let` gets floated out of the window).
  let r ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / 1000000.0} ms"
  (← IO.getStdout).flush
  pure r

def main (args : List String) : IO Unit := do
  let withOld := args.contains "--old"
  for n in [100, 300, 600, 1000] do
    IO.println s!"--- n = {n} ---"
    let answer := mkAnswer n
    let resp := mkResp n
    IO.println s!"  (answer bytes total: {answer.foldl (fun a b => a + b.size) 0})"
    let scrubbed ← timeIt s!"scrubAnswerB (new) n={n}" (fun _ =>
      VeriDNS.Impl.Resolver.scrubAnswerB (RR := ResourceRecord) bigName answer)
    IO.println s!"  scrubbed size: {scrubbed.size}"
    if withOld && n ≤ 300 then
      let old ← timeIt s!"scrubAnswerB (OLD shape) n={n}" (fun _ =>
        oldScrubAnswerB bigName answer)
      IO.println s!"  old scrubbed size: {old.size} (equal: {old == scrubbed})"
    let delivered ← timeIt s!"deliveredResponse n={n}" (fun _ =>
      deliveredResponse (mkResp 1) resp)
    IO.println s!"  delivered ancount: {delivered.answer.size}"
    let enc ← timeIt s!"Message.encode n={n}" (fun _ => Message.encode resp)
    IO.println s!"  encoded size: {enc.size}"
    let ent ← timeIt s!"entitledAnswerB n={n}" (fun _ =>
      VeriDNS.Impl.Resolver.entitledAnswerB (RR := ResourceRecord) resp)
    IO.println s!"  entitled: {ent}"
    (← IO.getStdout).flush
