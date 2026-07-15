# 014 — Case-fold spec is not load-bearing across [A..Z]: a surgical W under-fold survives a coordinated multi-file proof repair (settles CONFIRMED-001)

- **Severity:** low-medium (spec-provenance / bad-spec; not an exploitable poisoning). **Class:** bad-spec.
- **Settles the open question in finding 001.** 001 left it undecided whether the *spec* forbids conflating/splitting distinct letters, or whether the prior naive-over-collapse catch was merely (i) a brittle proof script + (ii) incidental `rfl`-checked concrete traces. This mutation was designed to route around both: it under-folds a **single** uppercase letter **W (87)** — grep of `Spec/NetworkTraces.lean` confirms **no trace name contains W** — and it carries the minimal, in-bounds proof-script repair for the two impl-relative mirror laws. Result: **`lake build` is fully GREEN with every `rfc_proves` intact.** The RFC-anchored spec therefore does **not** pin the fold across `[A..Z]`; it samples only `A=a` plus the non-alphabetic bytes. Verification is **not** load-bearing here.

## The mutation (coordinated, minimal)
```
Impl/DomainName.lean:109
-  if 65 ≤ b && b ≤ 90 then b + 32 else b
+  if 65 ≤ b && b ≤ 90 && b != 87 then b + 32 else b     -- W(87) no longer folds to w(119)

Spec/NetworkModel.lean:24  (model mirror foldByte)
-  cond (Nat.ble 65 x.toNat && Nat.ble x.toNat 90) (x + 32) x
+  cond (Nat.ble 65 x.toNat && Nat.ble x.toNat 90 && !(x.toNat == 87)) (x + 32) x
```
Two impl-relative **mirror laws** repaired in lockstep (statement + a few tactic lines only — NOT re-architected):
- `Proof/NameTree.lean:377` `foldCaseByte_toNat`: RHS guard `if 65≤b≤90` → `if 65≤b≤90 ∧ b≠87`, plus the two `if_pos`/`if_neg` discharges updated to carry the `b != 87` bit.
- `Proof/Refinement.lean:61` `foldByte_eq` (model-fold = impl-fold): **statement unchanged** (both sides gained the identical guard, so equality still holds); only the closing `simp only [...]` needed three extra normalization lemmas (`Bool.not_eq_true'`, `bne_iff_ne`, `← UInt8.toNat_inj`, `UInt8.toNat 87 = 87`) to reconcile the `!(·==87)` vs `·!=87` spellings.
- `Proof/DomainName.lean:650` `foldCaseByte_nonalphabetic_exact`: **needed no change** — W is alphabetic, so it lies outside this prop's non-alphabetic domain (this is exactly why the prop cannot see the bug).

## Build result
`lake build` → **Build completed successfully (279 jobs).** No `rfc_proves` failed. In particular the RFC-anchored generated props survived unchanged at STATEMENT level:
- `namespace_compare_example` (`Spec/DomainName.lean:42`) — pins only `compare 65 97 = true` (A=a). W(87) is not sampled. ✓ green
- `namespace_compare_caseinsensitive` (`:48`) — one-sided tautology over `nameEqCI := foldNameCase a == foldNameCase b`; holds for **any** fold. ✓ green
- `namespace_nonalphabetic_match_exactly` (`:38`) — quantifies only over non-alphabetic bytes; W is alphabetic. ✓ green
- `foldByte`'s own `rfc_proves VeriDNS.Spec.Net.foldByte [1034][378:396]` — the RFC-text embed is unaffected by the definition's actual content. ✓ green

No theorem **statement** became false. The only breakage was tactic-level (`foldByte_eq`'s `simp` and the two mirror-law discharges), and those are impl-relative mirrors, not RFC obligations — exactly the "brittle, repairable" category. This upgrades 001's verdict from "caught by brittle script + incidental traces" to **"survives a coordinated multi-file proof repair" → bad-spec.**

## Observable divergence vs unbound (race-free continuous capture)
Rig: veri-dns @10.53.0.2:5300 (netns verid), unbound @10.53.0.3:5301 (netns unbound), same nsd hierarchy; leaf `example.test` @10.53.0.12.

Single continuous `tcpdump` in the verid netns across a warm→repeat→case-flip sequence isolates exactly which client queries reach upstream:
```
[A] warm  www.example.test  -> Out 10.53.0.2 > 10.53.0.12.53:  A? www.example.test
[B] again www.example.test  -> Out 10.53.0.2 > 10.53.0.12.53:  A? example.test   (CNAME target)
[C] WWW.example.test        -> Out 10.53.0.2 > 10.53.0.12.53:  A? WWW.example.test   <-- FRESH FETCH
[D] WWW.example.test again  -> (no upstream; WWW now cached under its own fold)
```
Query **[C]** issued a brand-new `A? WWW.example.test` upstream query although `www.example.test` had just been cached — a spurious **cache MISS** because `foldNameCase("WWW") = "WWW" ≠ "www" = foldNameCase("www")` under the mutant, so `Cache.lean`'s `nameEqCI` lookups (`Impl/Cache.lean:64/79/88/156/296`) fail to match. Correct behavior ([D]) shows the resolver *does* cache — only the **cross-case** lookup broke.

Reference resolver (unbound), same warm-then-uppercase sequence: **zero** upstream queries to nsd on the uppercase `WWW` — it serves it from the warmed `www` cache entry (RFC 1034 §3.1 / RFC 4343 case-insensitivity). So veri-dns and unbound **diverge**: mutant veri-dns treats `WWW` and `www` as distinct names, unbound does not.

(End-to-end the *answer* still resolves on both, because nsd echoes the query's case in the answer owner and the extra fetch succeeds — so the damage here is a correctness/efficiency divergence — duplicated egress + split cache — rather than an answer substitution. A poisoning variant is not implied: the mutant makes matching *stricter*, not looser.)

## The claim under test (RFC)
RFC 1034 §3.1 / RFC 4343: labels compare case-insensitively — the fold must equate upper/lower forms of the **same** letter across the **whole** `[A..Z]` range, not merely at the `A=a` sample point. The generated props sample `A=a` and the non-alphabetic complement, leaving `B..Z` (here W) unconstrained.

## Why this matters / suggested fix
The "RFC-words-to-code" chain for case-insensitivity bottoms out in the *trusted definition* of `foldByte`/`foldCaseByte` plus a hand-written mirror law that merely restates that definition. No RFC-anchored obligation forces the fold to case-fold every letter in `[A..Z]`. Fix as suggested in 001: add a spec obligation pinning the fold pointwise over the full range, e.g. `∀ b, foldByte b = (if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b + 32 else b)` discharged by `decide`/`native_decide`, or a two-sided law `foldByte a = foldByte b ↔ (a = b ∨ {a,b} is an upper/lower pair)`. Until then the `namespace_compare_*` props are decorative for any letter other than A.

## Reproduction
1. Apply the two `def` edits above + the three proof repairs (`NameTree.lean:377`, `Refinement.lean:61`); `lake build` → green (279 jobs).
2. `lake build veri-dns` + `review/env/restart-verid.sh`.
3. In one continuous `ip netns exec verid tcpdump -ni any -tt "udp and port 53"`: dig `www.example.test` (warm), then dig `WWW.example.test` from the attacker ns; observe the fresh `A? WWW.example.test` egress. Repeat against unbound @10.53.0.3:5301 → no egress on the uppercase query.
