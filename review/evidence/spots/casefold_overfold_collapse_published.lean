import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName

open VeriDNS.Spec
open VeriDNS.Impl.DomainName

/-! SPOT (round 6, thread a — OVER-fold / total-collapse direction).

    Prior spots (casefold_vacuity, casefold_underfold_all_props) attacked UNDER-
    folding (a fold that leaves B..Z alone).  This spot attacks the OPPOSITE
    failure — a fold that COLLAPSES everything — and sharpens which theorems are
    actually RFC-PUBLISHED.

    The ONLY two RFC-1035-§3.1 case-fold obligations wired into the RFC ledger
    (RFC/ProofLinks.lean:29-30, both [1035][478:530]) are:
      - nameEqCI_conforms          := namespace_compare_caseinsensitive .. nameEqCI foldNameCase
      - foldCaseByte_example_conforms := namespace_compare_example (beq-of foldCaseByte)
    `foldCaseByte_nonalphabetic_exact` (Proof/DomainName.lean:650) is PROVEN but
    appears in NO `rfc_proves`/`check_rfc` line — it is not part of the published
    RFC surface (grep-verified).

    Claim: the CONSTANT fold `fun _ => 0` — which makes nameEqCI return `true` for
    EVERY pair of names (total collapse; RFC 5452 questionMatches would then accept
    a response for ANY query name) — satisfies BOTH published obligations.  Only the
    UNPUBLISHED nonalpha prop rejects it. -/

def foldConst0 (_ : UInt8) : UInt8 := 0
def cmpConst0 (a b : UInt8) : Bool := foldConst0 a == foldConst0 b

-- NONSENSE #1: the published "case-insensitive" obligation passes for the
-- collapsing fold.  (compare is beq-of-fold, so this holds for ANY fold — the
-- published theorem constrains the fold not at all.)
theorem nonsense_collapse_passes_caseinsensitive :
    namespace_compare_caseinsensitive UInt8 cmpConst0 foldConst0 := by
  intro a b h
  show (foldConst0 a == foldConst0 b) = true
  rfl

-- NONSENSE #2: the published A=a example passes for the collapsing fold.
theorem nonsense_collapse_passes_example :
    namespace_compare_example cmpConst0 := by
  show (foldConst0 65 == foldConst0 97) = true
  decide

-- OBSERVABLE CATASTROPHE: under this fold, two totally different names compare
-- EQUAL.  'B'(66) vs 'q'(113) — no case relationship whatsoever — matches.
theorem nonsense_collapse_matches_unrelated :
    cmpConst0 66 113 = true := by decide

-- The ONLY thing that rejects the collapse is the UNPUBLISHED nonalpha prop:
-- two distinct non-letters (0 and 1) must compare unequal, but the collapse says
-- equal.  So this obligation is false for foldConst0 — and it is not rfc_proves-linked.
theorem collapse_fails_unpublished_nonalpha :
    ¬ namespace_nonalphabetic_match_exactly cmpConst0 alphabeticByte := by
  intro h
  have := h 0 1 (by decide) (by decide)
  simp only [cmpConst0, foldConst0] at this
  exact absurd this (by decide)

-- SENSIBLE: the real impl comparator does NOT collapse unrelated bytes.
theorem sensible_realimpl_rejects_unrelated :
    (foldCaseByte 66 == foldCaseByte 113) = false := by decide

-- SENSIBLE: the published caseinsensitive obligation genuinely holds for the real
-- fold — but note the proof is definitional (compare = beq-of-fold), the same
-- tautology shape as nonsense_collapse_passes_caseinsensitive above.
theorem sensible_realimpl_conforms :
    namespace_compare_caseinsensitive ByteArray nameEqCI foldNameCase := by
  intro a b h
  show nameEqCI a b = true
  unfold nameEqCI
  rw [h]
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp
