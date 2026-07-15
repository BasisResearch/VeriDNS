# 025: `IoResumeSound.ioResumeLoop_sound` — terminal soundness theorem is orphan deadweight (coverage-gap)

## Classification

**coverage-gap** (negative deadweight probe, proof-only; no behavioral mutation).

## Mutation

`M-IoResumeSound-orphan-conclusion-break` — gutted the entire conclusion of
`VeriDNS.Proof.IoResumeSound.ioResumeLoop_sound`
(`VeriDNS/Proof/IoResumeSound.lean:2810`, conclusion at lines 2863-2878) and truncated the
~3,600-line proof body:

```diff
-      ∃ slist v coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v coutM
-        ∧ (modelSlistOf state.resources.slist).Subperm slist
-        ∧ (αResp resp).rcode = v.rcode
-        ∧ (αResp resp).answer = αSection state.cnameChain ++ v.answer
-        ∧ CacheRefines (αCache cout) coutM
-        ∧ WorldModels net ns ra ednsBuf now w'
-        ∧ CacheWf cout state.now
-        ... (13-conjunct verdict/refinement/invariant block) ...
-        ∧ cout.records.size ≤ DnsCache.capacity := by
-  intro n
-  induction n using Nat.strongRecOn with
-  ... (~3,600 lines of proof) ...
+      True := by
+  intros
+  trivial
```

`git diff --stat`: `VeriDNS/Proof/IoResumeSound.lean | 3623 +------- (3 insertions, 3620 deletions)`

## Build result

```
lake build
...
⚠ [277/279] Built VeriDNS.Proof.IoResumeSound (2.5s)   -- unused-variable lints only
✔ [278/279] Built VeriDNS (574ms)
Build completed successfully (279 jobs).
```

**GREEN.** Not a single file outside `Proof/IoResumeSound.lean` regressed — and nothing inside
it either, because the theorem is the last declaration in the file and nothing else names it.
Cross-repo check: every code reference to `ioResumeLoop_sound` resolves to the *distinct*
`VeriDNS.Proof.NameTree.ioResumeLoop_sound` (`VeriDNS/Proof/NameTree.lean:1633`, the one bound
by `rfc_proves` at `VeriDNS/RFC/ProofLinks.lean:59`); all other mentions of the IoResumeSound
theorem are prose comments (`AnswerScrubAlpha.lean`, `DeliveredAuthentic.lean`,
`RRsetComplete.lean`, `Refinement.lean:9505`, `FreeIO.lean:632`). Its sole importer is the
aggregator `VeriDNS.lean:81`, which imports the module but never uses the theorem.

## Runtime reproduction (mutated binary vs unbound)

Proof-only mutation, so behavior is unchanged — confirmed after
`lake build veri-dns` + `restart-verid.sh`:

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 host.example.test A +short
10.53.0.101
$ ip netns exec attacker dig @10.53.0.3 -p 5301 host.example.test A +short
10.53.0.101
$ ip netns exec attacker dig @10.53.0.2 -p 5300 www.example.test A +short
example.test.
10.53.0.100
```

`observable = false`. The signal is purely the dependency graph.

## Why this matters

`IoResumeSound.ioResumeLoop_sound` is the terminal *constructive* network-discharge soundness
theorem — the one whose ~3,600-line proof actually walks the IO resume loop and produces a
`HasVerdictAt` witness plus cache-refinement/invariant conjuncts. This probe shows it
contributes to **no applied guarantee**: you can replace its entire conclusion with `True` and
every `rfc_proves` theorem and every other `Proof/*.lean` file still builds.

Moreover its premise set covers zero real client traffic:

- `q.rd = false` (`IoResumeSound.lean:2844`) — but the client gate
  `performsRequestedOperation` (`VeriDNS/Impl/Server.lean:98-99`) REFUSES any query with
  `rd != 1` (`queryProblem`, `Server.lean:104`), so every query the server actually resolves
  carries `rd = 1`.
- `q.qtype ≠ QType.star` (`:2846`) and `q.qclass = RRClass.in` (`:2848`) further narrow it.

The load-bearing name at the IO level is instead
`VeriDNS.Proof.NameTree.ioResumeLoop_sound` (`rfc_proves`, ProofLinks:59), which rests on the
**assumed** `NetworkConsistent` oracle — i.e. the guarantee that is actually wired into the
RFC-proof surface is the unverified-at-M=IO one, while the fully constructive theorem hangs
off the side, consumed by nobody and instantiable by no real query.

## Recommendation

Either (a) compose `IoResumeSound.ioResumeLoop_sound` into the capstone chain (e.g. have the
`rfc_proves` obligation or `DeliveredAuthentic`/`AnswerScrubAlpha` capstones consume its
`HasVerdictAt` verdict), fixing the `rd`/`qtype`/`qclass` premises so a gated client query can
satisfy them; or (b) mark it explicitly as scaffolding. As it stands, a regression that
falsifies its statement (or deletes it) is invisible to `lake build`.

## Restoration

`git checkout -- .` + `lake build` (green) + `restart-verid.sh`; baseline re-verified with the
same digs.
