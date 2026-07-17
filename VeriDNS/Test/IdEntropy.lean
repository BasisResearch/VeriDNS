import VeriDNS.Impl.UdpSocket





namespace VeriDNS.Test.IdEntropy

open VeriDNS.Impl.UdpSocket

def sampleCount : Nat := 4096

def fail (msg : String) : IO Unit :=
  throw <| IO.userError s!"id-entropy-test: {msg}"

def countTable (samples : Array UInt16) : Array Nat := Id.run do
  let mut t : Array Nat := .replicate 65536 0
  for s in samples do
    t := t.set! s.toNat (t[s.toNat]! + 1)
  return t

def run : IO Unit := do
  let mut samples : Array UInt16 := #[]
  for _ in [0:sampleCount] do
    samples := samples.push (← randomU16)

  let distinct := (countTable samples).foldl (fun n c => if c > 0 then n + 1 else n) 0
  if distinct < 3850 then
    fail s!"only {distinct} distinct ids in {sampleCount} samples (expected ≈ 3968); \
            id source is not uniform over 16 bits"

  for bit in [0:16] do
    let ones := samples.foldl (fun n s => if s.toNat >>> bit &&& 1 == 1 then n + 1 else n) 0
    let mid := sampleCount / 2
    let dev := if ones ≥ mid then ones - mid else mid - ones
    if dev > 192 then
      fail s!"bit {bit} set in {ones}/{sampleCount} samples (expected 2048 ± 192); \
              stuck or biased bit"

  let deltas := (Array.range (sampleCount - 1)).map fun i =>
    samples[i + 1]! - samples[i]!
  let modal := (countTable deltas).foldl max 0
  if modal > 64 then
    fail s!"most common adjacent id delta occurs {modal} times in {deltas.size} \
            (expected ≤ ~10); ids look sequential, not random"

  IO.println s!"id-entropy: {distinct} distinct / {sampleCount}, bits balanced, \
                modal delta ×{modal}"

end VeriDNS.Test.IdEntropy
