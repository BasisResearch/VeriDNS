# 001 — The RFC-generated case-fold props are decorative; the fold is pinned by a hand-written law instead

- **Severity:** low (spec-provenance observation, NOT a bug); **class:** decorative-generated-spec.
- **EXPLOITABILITY CLAIM RETRACTED.** The loop's surgical J–K over-collapse mutation was caught **semantically** by `foldCaseByte_toNat` (`Proof/NameTree.lean:377`), a load-bearing law that hardcodes the exact ASCII fold (`(foldCaseByte b).toNat = if 65≤b≤90 then b+32 else b`) and feeds the on-path congruence proofs (used at :392/:447/:501). So **an over-collapsing fold does NOT slip through** — the case-insensitivity property is genuinely enforced. The original "not load-bearing / high severity" headline was wrong.
- **What remains true (the modest, honest point):** the three *RFC-generated* props (`namespace_compare_caseinsensitive` is one-sided; `_example` pins only `A=a`; `_nonalphabetic_match_exactly` covers only non-letters) are **decorative** — they do not by themselves force the fold to keep distinct letters distinct. The real pinning is done by the *hand-written* `foldCaseByte_toNat`, which just restates the definition and is not derived from RFC prose. So for this property, the advertised "from the words of the RFC to the theorem" chain is carried by a hand lemma, not the generator. That is a provenance caveat, not a defect.
- **On/off-path:** ON-PATH; correctly enforced.
- **Status:** RETRACTED as a bug; retained as a spec-provenance note. The generated `namespace_compare_*` props are demonstrably one-sided (below). Empirically: the *identity* fold (case-sensitive) IS caught — by the real `A=a` example theorem (`namespace_compare_example`, a genuine semantic catch). A *naive over-collapse* (all letters→'a') is also caught, but **only by a brittle proof script + incidental concrete traces, not a semantic obligation** (see "Empirical nuance"). Whether the *spec* forbids conflating distinct letters is being settled by a **surgical over-collapse + minimal proof-script repair** in the integrated `bug-hunt.mjs` loop.

## Empirical nuance (from the mutation run)
- IDENTITY fold → `lake build` FAILS at `Proof/DomainName.lean:646` — `decide` rejects `foldCaseByte 65 == foldCaseByte 97` (the `A=a` example). This is a **real** semantic catch: under-folding is genuinely forbidden by the spec.
- NAIVE over-collapse (`if alphabeticByte b then 97 else b`) → `lake build` FAILS, but only because (i) `foldCaseByte_nonalphabetic_exact`'s tactic `rw [hc.1]; simp` (`Proof/DomainName.lean:655`) structurally assumes the fold's `if` has just the 65–90 branch — the theorem *statement* stays true, only the script breaks; and (ii) seven `rfl`-checked concrete server-failover traces in `Spec/NetworkTraces.lean` exercise specific names whose `nameEq` result changes. Neither is a principled obligation that distinct letters stay distinct. A surgical mutation that avoids those concrete names, plus a one-line repair of the brittle script, tests the real question — that is what the loop now runs.

## The claim under test
RFC 1035 §3.1 (embedded at `Spec/DomainName.lean:23-25`): *"Name servers and resolvers must compare labels in a case-insensitive manner (i.e., A=a) … Non-alphabetic codes must match exactly."* The intent is that the fold equates **only** the upper/lower forms of the **same** letter (A=a) and keeps **different** letters distinct (A≠B).

## The spec, and why it does not pin the fold
The generator produces three `Prop`s (`Spec/DomainName.lean:38-49`), proven about the implementation in `Proof/DomainName.lean`:

```lean
-- :631  proven for the runtime comparison
theorem nameEqCI_conforms :
    namespace_compare_caseinsensitive ByteArray nameEqCI foldNameCase := by
  intro a b h; show nameEqCI a b = true; unfold nameEqCI; rw [h]; …   -- TAUTOLOGY
```

`nameEqCI a b` is *defined* as `foldNameCase a == foldNameCase b` (`Impl/DomainName.lean:118`). So `foldNameCase a = foldNameCase b → nameEqCI a b = true` is true **by definition, for any fold whatsoever** — the proof never inspects `foldCaseByte`. The remaining two props constrain the fold only weakly:
- `foldCaseByte_example_conforms` (`:643`): just `foldCaseByte 65 == foldCaseByte 97` (A folds like a).
- `foldCaseByte_nonalphabetic_exact` (`:650`): only for **non-alphabetic** bytes.

And every downstream case theorem (`nodeAtName_congrCI` `Proof/NameTree.lean:600`, the cache case-invariance lemmas) is **invariance-under-the-fold** — of the form "lookup/tree is invariant under `nameEqCI`" — which holds for *any* fold, correct or not.

## The mutation that slips through
```lean
-- Impl/DomainName.lean:108  (and mirror Spec/NetworkModel.lean:23 foldByte)
def foldCaseByte (b : UInt8) : UInt8 :=
  if alphabeticByte b then 97 else b        -- collapse ALL letters to 'a'
```
- `nameEqCI_conforms` — still a tautology. ✓ green
- `foldCaseByte_example_conforms` — `foldCaseByte 65 = 97 = foldCaseByte 97`. ✓ green
- `foldCaseByte_nonalphabetic_exact` — unchanged for non-alphabetic bytes. ✓ green
- all invariance/congruence theorems — hold for the new fold. ✓ green

So `lake build` stays **fully green**, yet the resolver now treats any two equal-length names that agree on non-letter positions as identical.

## Observable effect (produced by the mutant)
Prime `example.com` (7 letters) via a normal resolution, then query `eeeeeee.com` (7 letters): under the collapsed fold both names fold-equal, so the cache lookup returns **example.com's A record for `eeeeeee.com`**, where a correct resolver returns NXDOMAIN. This is a cache-collision / answer-substitution bug that a battle-tested resolver (unbound) does not exhibit — reproduced side-by-side in the mutation run.

## Why this matters for the trust verdict
The "machine-checked from the words of the RFC to the running code" chain for case-insensitivity is **not** load-bearing: it bottoms out in the *trusted definition* of `foldByte`/`foldCaseByte`. `rfc_proves` merely embeds the RFC text next to the definition; it does not prove the definition equals the ASCII case fold, and no theorem forces the fold to distinguish distinct letters. A reviewer must read and trust `foldCaseByte` by eye — the proofs add nothing here.

## Suggested fix
Add a spec obligation that pins the fold pointwise to the ASCII case map — e.g. `∀ b, foldByte b = (if 65≤b≤90 then b+32 else b)` proven by `decide`/`native_decide`, or a two-sided law `∀ a b, foldByte a = foldByte b ↔ (a = b ∨ {a,b} is an upper/lower pair)`. Without a definitional pin, the generated `namespace_compare_*` props are decorative for this property.
