# 008 — The TC=1 gate on negative caching is not wired to any load-bearing obligation

- **Severity:** medium (spec/refinement coverage gap with a real security-relevant behaviour behind it); **class:** coverage-gap.
- **Mutation:** `M-neg-trunc-cache` — in `VeriDNS/Impl/Server.lean:87` `negativelyCacheable`, drop the truncation gate: change the first conjunct `resp.header.tc == 0` to `true`, so a truncated (TC=1) reply is still deemed negatively cacheable.
- **Build result:** `lake build` **BROKE** on the mutant, then went **GREEN** after a minimal 2-line dead-tactic repair (details below). So the truncation gate is NOT load-bearing in any theorem *statement*.

## Diff
```
-def negativelyCacheable (resp : Format) : Bool :=
-  resp.header.tc == 0
-    && (resp.header.rcode == Rcode.nameError
+def negativelyCacheable (resp : Format) : Bool :=
+  true
+    && (resp.header.rcode == Rcode.nameError
```

## What broke, and why it is brittle (not semantic)
`lake build` failed at exactly one place:

```
error: VeriDNS/Proof/Cache.lean:285:6: Tactic `rewrite` failed:
  Did not find an occurrence of the pattern
  (true && (resp.header.rcode == Rcode.nameError
     || resp.header.rcode == Rcode.noError && resp.answer.isEmpty)) = true
```

The failing tactic is `rw [htc] at h`, where `htc : resp.header.tc = 0`. After the
mutation the definition no longer mentions `resp.header.tc`, so the `rw` has nothing
to rewrite. This is a **tactic** break, not a statement break: the theorem
`negativelyCacheable_nodata` (`Proof/Cache.lean:279`) is still **true** — with the
weaker (mutated) `negativelyCacheable`, `negativelyCacheable resp = true` together
with `hne : rcode ≠ nameError` still implies `nodata_indicated`. The `htc` hypothesis
simply becomes unused.

The same shape recurs at `negativelyCacheable_iff_absorbNeg_trigger`
(`Proof/Refinement.lean:5863`), whose proof also does `rw [htc]` after `unfold`. Both
theorems **carry `htc : resp.header.tc = 0` as a HYPOTHESIS** rather than deriving it
from `negativelyCacheable`.

### Minimal repair that makes it green (the real test)
Delete the two now-dead `rw [htc]` lines:
- `Proof/Cache.lean:285` — remove `rw [htc] at h`
- `Proof/Refinement.lean:5864-ish` — remove `rw [htc]`

After that, `lake build` → **"Build completed successfully (279 jobs)."** Nothing else
breaks. The truncation refusal was never tied to a load-bearing obligation at the
server layer.

## Why this is a genuine coverage gap (the model *does* forbid it)
The network-sim's trusted `answer` transition **does** guard negative caching on
`tc = false`:

```
-- Spec/NetworkSemantics.lean:1419
(htc : reply.msg.tc = false) :
  Resolves ... ((c.absorb now ... reply.msg).absorbNeg now q reply.msg) ...
```

and the surrounding comment (`:1434-1436`) is explicit that the impl's TC=1 truncated
delivery must be an *unwritten* cache (`cf0 = c` disjunct) — i.e. the model **provably
refuses to `absorbNeg` a truncated reply**. So after the mutation the implementation
negatively caches exactly where the abstract model says it does not — yet no refinement
theorem relates the server-layer `storeNegativeIfCacheable` (`Impl/Server.lean:480`,
called on the FINAL `resolveWithIO` result) to the model's `htc`-guarded `absorbNeg`.
The refinement obligation that *should* force the impl to keep the gate is missing;
the gate is present in both impl and model but nothing binds them.

## The behaviour behind the gap (reachable in principle)
This is not merely cosmetic. The negative-cache write path is genuinely reachable for a
truncated reply:
- `Impl/Resolver.lean:431` — a `nameError` (NXDOMAIN) response is delivered as the
  final answer **regardless of `tc`**; there is no DNS-over-TCP retry (cf. finding
  006 "no-dns-over-tcp"). So a truncated NXDOMAIN whose authority section still parses
  an SOA flows straight through `finalizeAnswer` → `replyForResolution`
  (`Impl/Server.lean:460`) → `storeNegativeIfCacheable` (`:480`).
- Baseline: `negativelyCacheable` returns `false` on TC=1, so the truncated negative is
  NOT cached; a subsequent query re-resolves.
- Mutant: it IS cached and later replayed as an authoritative negative answer.

Security impact of the mutant: a spoofed/partial TC=1 NXDOMAIN with a forged SOA aimed
at a name that *exists* (e.g. `host.example.test`) poisons the negative cache so that
later legitimate queries get NXDOMAIN from cache — a denial-of-existence poisoning that
a battle-tested resolver (unbound) avoids by retrying truncated replies over TCP. This
violates RFC 2308 §5 / RFC 1035 §4.1.1 (truncated responses are incomplete and must not
be trusted/cached).

## Reproduction status (observable = NOT demonstrated end-to-end in this rig)
The mutant binary was built, loaded, and confirmed live; a legitimate NXDOMAIN
(`bogus1.example.test`, TC=0, real SOA) is negatively cacheable in BOTH baseline and
mutant, so it does not distinguish them. The distinguishing case needs a **TC=1**
negative reply to reach veri-dns, which this rig cannot produce:
- the fake hierarchy is unsigned and its NXDOMAINs are tiny, so `nsd` never sets TC=1;
- off-path injection (`spoof.py`) cannot win the txid+source-port race against veri-dns's
  `getrandom` query-ID in the sub-millisecond local RTT window, and `spoof.py` only forges
  positive A answers, not TC=1 NXDOMAIN+SOA.

So the wrong behaviour is established by code+proof reading (reachable write path +
model that provably refuses the same write) but was not reproduced through the live
network rig. Hence `observable = false` and the honest class is **coverage-gap**, not a
confirmed exploit.

## Suggested fix
Add a refinement obligation at the server layer that ties `storeNegativeIfCacheable`
(and `negativelyCacheable`) to the model's `htc`-guarded `absorbNeg`: prove that when
`resp.header.tc = 1` the post-resolution cache is unchanged (mirroring
`cacheUnlessTruncated_truncated`, `Proof/Refinement.lean:5873`, which already exists for
the positive path). Concretely, a lemma `negativelyCacheable resp = true → resp.header.tc
= 0` (currently the gate makes this hold definitionally) consumed by a server-layer
refinement step, rather than every consumer assuming `htc` as a free hypothesis.
