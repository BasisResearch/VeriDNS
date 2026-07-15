import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName

open VeriDNS.Spec
open VeriDNS.Impl.DomainName

/-! SPOT (round 10, thread a — DEEPER than the underfold spots).

    Prior spots (casefold_underfold_all_props, casefold_letter_collision) show a
    SAME-CLASS defect: under-fold a letter → two names miss in cache. Consequence
    = availability (cache miss), not a security gate.

    This SPOT weaponises a CROSS-CLASS OVER-fold: fold a NON-letter (digit '5'=53)
    onto a letter's fold-image ('e'=101, the image of 'E'=69). RFC 1035 §3.1 says
    "Non-alphabetic codes must match exactly" — a digit must compare equal only to
    itself. We show the THREE generated RFC-spec props (Spec/DomainName.lean:38-49)
    do NOT forbid the cross-class collision, and the comparator then declares
    '5' == 'E' == 'e'. Because nameEqCI (built on foldCaseByte) is the SAME predicate
    the RFC 5452 acceptResponse anti-spoof gate uses (questionMatches → nameEqCI,
    Impl/Server.lean:36-44), this over-fold WIDENS the set of response question-names
    that pass acceptance.

    WHY the "non-alphabetic match exactly" prop is BLIND to it: the prop quantifies
    over pairs (a,b) that are BOTH non-alphabetic. The collision is '5'(non-alpha)
    vs 'E'(ALPHA), so the offending pair is never in the prop's domain. Among two
    non-alphabetic bytes the fold is still injective (101 = 'e' is alphabetic, hence
    not a second argument), so the prop still holds — vacuously safe, semantically
    broken.

    WEAPONIZABLE MUTANT (foldCaseByte, Impl/DomainName.lean:108): change
        if 65 ≤ b && b ≤ 90 then b + 32 else b
    to
        if b == 53 then 101 else if 65 ≤ b && b ≤ 90 then b + 32 else b
    and repair the proof-internal mirror foldCaseByte_toNat (NameTree.lean:377) in
    LOCKSTEP (add the `b==53` arm to its `if`). Prediction: green build; observable
    on the wire as a widened acceptResponse question-match.

    SEMANTIC-CATCH vs BRITTLENESS distinguisher: the KB CONTROL
    (M-foldCaseByte-crossclass-collision-CONTROL) left foldCaseByte_toNat UNREPAIRED,
    so its statement went false — that is a MIRROR LEMMA breaking (proof brittleness),
    NOT a semantic spec obligation firing. The genuine test is the LOCKSTEP repair:
    if no RFC-published theorem over questionMatches/acceptResponse pins nameEqCI to
    reject cross-class pairs, the lockstep mutant is fully green with an observable
    anti-spoof weakening. This file proves the spec-layer half (all three props are
    blind); the mutant + lockstep repair is the impl half. -/

def foldXclass (b : UInt8) : UInt8 :=
  if b == 53 then 101 else if 65 ≤ b && b ≤ 90 then b + 32 else b
def cmpXclass (a b : UInt8) : Bool := foldXclass a == foldXclass b

-- (1) A=a example still holds.
theorem xclass_passes_example : namespace_compare_example cmpXclass := by
  show (foldXclass 65 == foldXclass 97) = true
  decide

-- (2) case-insensitive prop holds (fold is the impl's own parameter — vacuous pin).
theorem xclass_passes_caseinsensitive :
    namespace_compare_caseinsensitive UInt8 cmpXclass foldXclass := by
  intro a b h
  show (foldXclass a == foldXclass b) = true
  rw [h]; simp

-- (3) "non-alphabetic codes must match exactly" — STILL HOLDS despite the leak,
--     because the collision partner 'E'(69) is alphabetic and never quantified.
theorem xclass_passes_nonalpha :
    namespace_nonalphabetic_match_exactly cmpXclass alphabeticByte := by
  intro a b ha hb
  show (foldXclass a == foldXclass b) = (a == b)
  have letterOff : ∀ c, alphabeticByte c = false → (65 ≤ c && c ≤ 90) = false := by
    intro c hc
    unfold alphabeticByte at hc
    rw [Bool.or_eq_false_iff] at hc
    exact hc.1
  have ea : foldXclass a = (if a == 53 then 101 else a) := by
    unfold foldXclass; rw [letterOff a ha]; simp
  have eb : foldXclass b = (if b == 53 then 101 else b) := by
    unfold foldXclass; rw [letterOff b hb]; simp
  -- a non-alphabetic ⇒ a ≠ 101 (101='e' is alphabetic); same for b.
  have aNe101 : (a == 101) = false := by
    by_contra h; simp only [Bool.not_eq_false] at h
    have : a = 101 := by simpa using h
    subst this; simp [alphabeticByte] at ha
  have bNe101 : (b == 101) = false := by
    by_contra h; simp only [Bool.not_eq_false] at h
    have : b = 101 := by simpa using h
    subst this; simp [alphabeticByte] at hb
  rw [ea, eb]
  by_cases ha53 : a == 53 <;> by_cases hb53 : b == 53
  · have e1 : a = 53 := by simpa using ha53
    have e2 : b = 53 := by simpa using hb53
    subst e1; subst e2; decide
  · have hbf : (b == 53) = false := by
      cases hbeq : (b == 53) with
      | false => rfl
      | true => exact absurd hbeq hb53
    have e1 : a = 53 := by simpa using ha53
    subst e1
    simp only [if_pos ha53, if_neg hb53]
    have l : ((101 : UInt8) == b) = false := by rw [BEq.comm]; exact bNe101
    have r : ((53 : UInt8) == b) = false := by rw [BEq.comm]; exact hbf
    rw [l, r]
  · have haf : (a == 53) = false := by
      cases haeq : (a == 53) with
      | false => rfl
      | true => exact absurd haeq ha53
    have e2 : b = 53 := by simpa using hb53
    subst e2
    simp only [if_neg ha53, if_pos hb53]
    have l : (a == (101 : UInt8)) = false := aNe101
    have r : (a == (53 : UInt8)) = false := haf
    rw [l, r]
  · simp only [if_neg ha53, if_neg hb53]

-- OBSERVABLE WRONGNESS: '5'(53) and 'E'(69) compare EQUAL under the over-fold.
theorem xclass_collides_digit_letter : cmpXclass 53 69 = true := by decide
theorem xclass_collides_digit_lower : cmpXclass 53 101 = true := by decide

-- Contrast: the REAL impl keeps them distinct (non-alphabetic matches exactly).
theorem realimpl_digit_letter_distinct :
    (foldCaseByte 53 == foldCaseByte 69) = false := by decide
