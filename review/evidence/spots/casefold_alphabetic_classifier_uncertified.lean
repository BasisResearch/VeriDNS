import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName

open VeriDNS.Spec
open VeriDNS.Impl.DomainName

/-! SPOT (round 10, thread a — a DISTINCT sub-finding, not the bundle-vacuity).

    Of the three generated case-fold props, only ONE has real teeth:
      namespace_nonalphabetic_match_exactly (Spec/DomainName.lean:38)
        := ∀ a b, alphabetic a = false → alphabetic b = false → compare a b = (a == b)
    It is the sole prop forcing the comparator to be EXACT on some bytes. But the
    "alphabetic" classifier is a PARAMETER, discharged (Proof/DomainName.lean:650)
    by instantiating it with the impl's `alphabeticByte` (Impl/DomainName.lean:111).

    TWO facts make that instantiation load-bearing yet unguarded:
      1. `alphabeticByte` is certified by NO theorem to actually identify letters.
         Nothing pins alphabeticByte 53 = false ('5' is a non-letter). It is the
         proof's own free choice of where the exact-match obligation applies.
      2. `alphabeticByte` is executable-path DEAD CODE: grep shows it is used only
         here (the prop instantiation) and in one unused `open` list; `foldCaseByte`
         and `nameEqCI` do NOT reference it (foldCaseByte inlines `65 ≤ b && b ≤ 90`).
         So a maintainer can co-adjust it with zero runtime consequence and zero
         other-theorem breakage.

    CONSEQUENCE: the only teeth-bearing prop's domain is impl-declared. Widen the
    classifier and the prop's teeth vanish. Below: with `alphaAll := fun _ => true`,
    `namespace_nonalphabetic_match_exactly` holds VACUOUSLY for the WORST possible
    comparator (constant-true — accepts every response question in the RFC 5452
    acceptResponse gate). The other two props (example, caseinsensitive) do NOT
    save us across the board — but the point stands: the exact-match teeth are
    nullified purely by the classifier parameter, which no theorem constrains. -/

def alphaAll : UInt8 → Bool := fun _ => true

-- The teeth-bearing prop is VACUOUS under a widened classifier: it holds for ANY
-- comparator whatsoever, including the constant-true anti-spoof-bypass comparator.
theorem nonalpha_vacuous_under_widened_classifier (cmp : UInt8 → UInt8 → Bool) :
    namespace_nonalphabetic_match_exactly cmp alphaAll := by
  intro a b ha hb
  -- ha : alphaAll a = false, i.e. true = false — impossible.
  simp only [alphaAll] at ha
  exact absurd ha (by decide)

-- Concretely: the always-true comparator (which makes questionMatches accept every
-- response, a total RFC 5452 anti-spoof bypass) satisfies the widened prop.
theorem constant_true_passes_widened :
    namespace_nonalphabetic_match_exactly (fun _ _ => true) alphaAll :=
  nonalpha_vacuous_under_widened_classifier _

-- And nothing in the spec layer pins the classifier to the truth. This restates the
-- gap: `alphabeticByte` is the proof's free choice, checked against no obligation.
-- (There is no `namespace_*` prop asserting alphabetic 53 = false, etc.)

/-! WEAPONIZABLE MUTANT: co-mutate the two independent defs (Impl/DomainName.lean):
      foldCaseByte : add `if b == 90 then b else …`  (drop 'Z'=90 from folding)
      alphabeticByte : leave as-is (still classifies 90 alphabetic)
    Then 'Z'(90) and 'z'(122) miss in cache/questionMatches. All three props stay
    green: example checks only 65↔97; caseinsensitive is tautological (fold is its
    own parameter); nonalpha EXEMPTS 90 because alphabeticByte 90 = true. No prop,
    and no other theorem, references the dropped byte.

    SEMANTIC-CATCH vs BRITTLENESS distinguisher: the ONLY artifact whose STATEMENT
    goes false under this mutation is `foldCaseByte_toNat` (NameTree.lean:377) — a
    verbatim `unfold`-proven mirror of foldCaseByte. That is proof BRITTLENESS: edit
    it in lockstep (narrow its `if` to match) and the build is green with an
    observable wire divergence. A GENUINE semantic catch would be an RFC-published
    theorem (rfc_proves) over questionMatches/nameEqCI whose truth pins the fold on
    'Z'; grep for such a theorem returns none — the spec layer stops at A=a. -/
