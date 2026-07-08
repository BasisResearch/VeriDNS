# 034: RFC 2181 §5.2 "lowest TTL" ledger entry is a value-blind tautology about a phantom function (bad-spec)

**Mutation:** `M-setAllTtls-phantom-MAX` — `VeriDNS/Spec/Clarifications.lean:36`

## Claim under test

The RFC-compliance ledger publishes RFC 2181 §5.2 — including the clause
"the client should treat the RRs for all purposes as if all TTLs in the
RRSet had been set to the value of the **lowest** TTL in the RRSet"
(rfc/rfc-2181.txt lines 228-230, inside cited range [215:234]) — as proved:

- `rfc_proves VeriDNS.Spec.rrset_setAllTtls_uniform [2181][203:214]` (Clarifications.lean:64)
- `rfc_proves VeriDNS.Spec.rrset_setAllTtls_uniform [2181][215:234]` (Clarifications.lean:65)
- `rfc_proves VeriDNS.Spec.rrset_setAllTtls_preserves_records [2181][215:234]` (Clarifications.lean:66)
- `rfc_proves VeriDNS.Spec.rrset_setAllTtls_uniform [2181][204:214]` (VeriDNS/RFC/ProofLinks.lean:152)

## Mutation

Replace `setAllTtls`'s body so it ignores the caller-supplied TTL `t` and
instead stamps every member with the per-set **MAXIMUM** — the exact opposite
of the mandated "lowest":

```diff
 def RRSet.setAllTtls (s : RRSet) (t : BitVec 32) : RRSet :=
-  { s with ttls := s.ttls.map (fun _ => t) }
+  { s with ttls := s.ttls.map (fun _ => s.ttls.foldl (fun a b => if a.toNat < b.toNat then b else a) 0) }
```

## Build result: FULL GREEN

```
✔ [277/279] Built VeriDNS.RFC.ProofLinks
✔ [278/279] Built VeriDNS
Build completed successfully (279 jobs).
```

Only diagnostic: `warning: VeriDNS/Spec/Clarifications.lean:35:34: Variable
name 't' is not explicitly referenced.` — Lean itself flags that the theorem
suite lets the TTL argument become dead.

Why green: `rrset_setAllTtls_uniform` asserts only that all resulting TTLs
are *equal to each other* (true for MAX just as for lowest, or for the
constant 0, or 2^32-1); `rrset_setAllTtls_preserves_records` pins only
rdatas and list length. Neither statement constrains the chosen TTL VALUE,
so both remain genuinely provable — this is a semantic hole in the
statements, not proof brittleness.

## Phantom status

```
$ grep -rn "setAllTtls\|RRSet" VeriDNS/Impl   # (Lean sources)
(no matches)
```

`RRSet`, `ttlsUniform`, and `setAllTtls` have zero references anywhere in
`VeriDNS/Impl/` or `VeriDNS/Proof/`. The resolver's real TTL normalization
runs through `minTtlB`/`normRaws` (`VeriDNS/Impl/Cache.lean:323,346`),
which is connected to no §5.2 `rfc_proves` line.

## Wire reproduction (no observable — that is the finding)

Mutated binary deployed via `lake build veri-dns` + `restart-verid.sh`
(service active, sanity dig host.example.test → 10.53.0.101). From the
attacker netns:

```
$ dig @10.53.0.2 -p 5300 example.test A   -> NOERROR, example.test. 3600 IN A 10.53.0.100
$ dig @10.53.0.3 -p 5301 example.test A   -> NOERROR, example.test. 2735 IN A 10.53.0.100 (unbound, cached)
```

Byte-for-byte identical answers before/after mutating the published §5.2
normalization function to its semantic opposite. The mutation cannot be
observed because the function it perverts is never executed.

## Verdict: bad-spec (decorative publication)

Two independent defects compound:

1. **Value-blind statements**: neither published theorem forces the
   normalization TTL to be the RRSet minimum; "set everything to MAX"
   (or any constant) satisfies both. The load-bearing word of the cited
   RFC text — "lowest" — is unverified.
2. **Phantom subject**: even if the statements did pin the minimum, they
   quantify over a function with no implementation callers, so they would
   still say nothing about resolver behavior.

The three §5.2 ledger lines certify RFC text that the proofs neither state
nor connect to the running code.

## Suggested fix

State and prove, about the *live* path, e.g.
`minTtlOf rr rrs = the minimum TTL over the RRSet keyed like rr`
(for `Impl/Cache.lean:328`) and link *that* to [2181][215:234]; either
delete `setAllTtls`/`rrset_setAllTtls_*` or strengthen to
`(s.setAllTtls t).ttls = s.ttls.map (fun _ => t)` plus a caller obligation
that `t` is the set minimum — and only then keep the `rfc_proves` lines.
