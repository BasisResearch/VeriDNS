# The honesty oracle: `NetworkConsistent` — is soundness vacuous?

`Proof/NameTree.lean:1577`:

```lean
def NetworkConsistent (T : Node ResourceRecord) (M) (Sock) : Prop :=
  ∀ (q : Format) (addr : ByteArray),
    SatisfiesM (fun ro => ∀ resp₀ resp, ro = some resp₀ →
        acceptResponse q resp₀ = some resp → ResponseConsistent T resp)
      (forwardQuery (M:=M) (Sock:=Sock) q addr)
```

`ioResumeLoop_sound` / `resolveWithIO_sound` (SatisfiesM form, `:1633`/`:1747`) assume this as a hypothesis and conclude the resolver's delivered answer + cache agree with the ground-truth tree `T`.

## Verdict: a legitimate trust boundary, NOT a vacuity cheat — but the exploitable surface is entirely below it

**Why it is not "assuming away the attack":** the oracle is *gated* by `acceptResponse q resp₀ = some resp`. It only requires responses that **pass the RFC 5452 match (query-ID + question echo)** to be tree-consistent. And `forwardQuery` already applies `datagramMatches` (source+destination check) before `acceptResponse` runs (`pathmap.md` §1). So the assumption is: *responses that pass both source/destination matching and the unpredictable-ID/question match are honest.* That is exactly the standard **non-DNSSEC recursive-resolver trust model** — you trust the in-bailiwick authoritative server you actually queried — which the README explicitly scopes in. An off-path attacker who cannot see traffic, cannot forge the matched source, and cannot guess the 16-bit ID cannot manufacture a response the oracle covers, so nothing real is assumed away.

**Where the real risk lives (below the oracle, in unverified code):** the theorem is stated for any lawful monad and holds at `M = IO`, but `NetworkConsistent` is *assumed*, never discharged, at `M = IO` (it is discharged constructively only at `M = Prog` via `FreeIO`/`NetworkSim`/`WorldNetwork`). At `M = IO` the `(payload, src, dst, local)` tuple that `datagramMatches`/`acceptResponse` inspect is **built by the unverified FFI `veri_dns_exchange`** (`ffi/recvfrom.c`). Two concrete coverage-gaps therefore sit *under* the oracle, invisible to the proof:
1. **ID entropy** — the 16-bit query ID's unpredictability rests entirely on `veri_dns_random_u16` (finding 000). A weak/constant source (mutant `constant-query-id`) makes the ID guessable; the proof cannot see it.
2. **Source/destination fidelity** — if the C fills `src`/`dst` from the intended peer rather than the actual datagram sender, `datagramMatches` passes for a spoofed packet and the oracle's premise is satisfied by a dishonest response. This must be tested empirically (spoofed-response race from the attacker vantage).

## Consequence for the trust verdict
The soundness theorems are meaningful and on-path. Their honesty assumption is the acknowledged non-DNSSEC boundary — reasonable. The residual attack surface is precisely the unverified FFI transport (ID randomness + address matching), which the pentest stage must exercise directly, because no theorem constrains it.
