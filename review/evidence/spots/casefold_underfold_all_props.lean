import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName

open VeriDNS.Spec
open VeriDNS.Impl.DomainName

/-! SPOT (round 2, thread a): Do the THREE generated RFC props jointly pin the
    case fold beyond the single A=a point?  Claim: NO.  A comparator that folds
    ONLY 'A' (leaving B..Z, i.e. every other letter, unfolded) satisfies ALL
    THREE generated props simultaneously — yet is observably wrong: it treats
    "Box" and "box" as different names (cache miss / no CI match).

    The three generated props (Spec/DomainName.lean):
      - namespace_compare_example            (pins A=a only)
      - namespace_nonalphabetic_match_exactly (constrains only NON-letters)
      - namespace_compare_caseinsensitive     (fold is an impl-chosen PARAMETER)

    If the bundle below all prove for `foldOnlyA`, then the RFC-linked SPEC layer
    places ZERO constraint on folding B..Z; the only thing catching an under-fold
    is the proof-internal restatement `foldCaseByte_toNat` (Proof/NameTree.lean:377),
    which is proven by `unfold foldCaseByte` — a tautological mirror of the def a
    maintainer would edit in lockstep. -/

def foldOnlyA (b : UInt8) : UInt8 := if b == 65 then 97 else b
def cmpOnlyA (a b : UInt8) : Bool := foldOnlyA a == foldOnlyA b

-- (1) passes the A=a example
theorem underfold_passes_example :
    namespace_compare_example cmpOnlyA := by
  show (foldOnlyA 65 == foldOnlyA 97) = true
  decide

-- (2) passes the case-insensitive prop (fold is the impl's own parameter, so
--     compare = beq-of-fold satisfies it trivially — the prop pins NOTHING).
theorem underfold_passes_caseinsensitive :
    namespace_compare_caseinsensitive UInt8 cmpOnlyA foldOnlyA := by
  intro a b h
  show (foldOnlyA a == foldOnlyA b) = true
  rw [h]; simp

-- (3) passes the non-alphabetic exact-match prop (only NON-letters constrained;
--     B..Z are classified alphabetic and thus excluded from the obligation).
theorem underfold_passes_nonalpha :
    namespace_nonalphabetic_match_exactly cmpOnlyA alphabeticByte := by
  intro a b ha hb
  show (foldOnlyA a == foldOnlyA b) = (a == b)
  have fix : ∀ c : UInt8, alphabeticByte c = false → foldOnlyA c = c := by
    intro c hc
    unfold alphabeticByte at hc
    unfold foldOnlyA
    rw [Bool.or_eq_false_iff] at hc
    have : (c == 65) = false := by
      rcases hc with ⟨h1, _⟩
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have : c = 65 := by simpa using hcon
      subst this; simp at h1
    rw [this]; rfl
  rw [fix a ha, fix b hb]

-- OBSERVABLE WRONGNESS: cmpOnlyA declares 'B' (66) and 'b' (98) UNEQUAL.
-- A correct case-insensitive comparator MUST return true here (RFC 1035 A=a).
theorem underfold_is_observably_wrong :
    cmpOnlyA 66 98 = false := by decide

-- Contrast: the REAL impl comparator folds the whole range.
theorem realimpl_folds_B :
    (foldCaseByte 66 == foldCaseByte 98) = true := by decide
