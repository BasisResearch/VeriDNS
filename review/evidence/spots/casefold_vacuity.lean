import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName

open VeriDNS.Spec
open VeriDNS.Impl.DomainName

/-! SPOT: does the generated `namespace_compare_caseinsensitive` spec force any
    actual case folding?  The real impl proves it as `nameEqCI_conforms`
    (Proof/DomainName.lean:631).  Claim: the spec is vacuous w.r.t. folding —
    an EXACT-equality comparator with the IDENTITY "fold" satisfies it. -/

-- NONSENSE #1: exact byte-equality (NO case folding at all) with identity fold
-- satisfies the "case-insensitive" compare spec.  If this proves, the spec does
-- not force case-insensitivity — it is a tautology about `compare = beq-of-fold`.
theorem nonsense_exact_is_caseinsensitive :
    namespace_compare_caseinsensitive UInt8 (fun a b => a == b) (fun x => x) := by
  intro a b h
  simp only at h
  subst h
  simp

-- NONSENSE #2: the example only pins the single point A=a (65 vs 97).
-- A fold that folds ONLY 'A' (leaving B..Z unfolded) still satisfies the example.
def foldOnlyA (b : UInt8) : UInt8 := if b == 65 then 97 else b

theorem nonsense_foldOnlyA_passes_example :
    namespace_compare_example (fun a b => foldOnlyA a == foldOnlyA b) := by
  show (foldOnlyA 65 == foldOnlyA 97) = true
  decide

-- NONSENSE #3: foldOnlyA still satisfies the non-alphabetic exact-match spec,
-- because alphabeticByte classifies B..Z as alphabetic and excludes them.
theorem nonsense_foldOnlyA_passes_nonalpha :
    namespace_nonalphabetic_match_exactly
      (fun a b => foldOnlyA a == foldOnlyA b) alphabeticByte := by
  intro a b ha hb
  show (foldOnlyA a == foldOnlyA b) = (a == b)
  have fix : ∀ (c : UInt8), alphabeticByte c = false → foldOnlyA c = c := by
    intro c hc
    unfold alphabeticByte at hc
    unfold foldOnlyA
    rw [Bool.or_eq_false_iff] at hc
    -- non-alphabetic ⇒ not in [65,90] ⇒ c ≠ 65
    have : (c == 65) = false := by
      rcases hc with ⟨h1, _⟩
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have : c = 65 := by simpa using hcon
      subst this
      simp at h1
    rw [this]; rfl
  rw [fix a ha, fix b hb]

-- SENSIBLE: a REAL case-fold spec would pin the WHOLE letter range, not one point.
-- The true impl satisfies this; foldOnlyA would NOT.
theorem sensible_full_range_realimpl :
    ∀ b : UInt8, 65 ≤ b → b ≤ 90 → foldCaseByte b = b + 32 := by
  intro b h1 h2
  unfold foldCaseByte
  simp only [h1, h2, decide_true, Bool.and_self, if_true]

-- And foldOnlyA FAILS the same real spec (witness B = 66):  foldOnlyA 66 = 66 ≠ 98.
theorem foldOnlyA_fails_full_range :
    ¬ (∀ b : UInt8, 65 ≤ b → b ≤ 90 → foldOnlyA b = b + 32) := by
  intro h
  have := h 66 (by decide) (by decide)
  simp [foldOnlyA] at this
