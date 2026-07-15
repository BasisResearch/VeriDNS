import VeriDNS.Spec.DomainName
import VeriDNS.Proof.DomainName

/-
SPOT round 9 — thread (a): do the generated case-fold props pin the fold
beyond the single A=a point?

We reuse the ACTUAL spec predicates from VeriDNS.Spec:
  namespace_compare_example              (pins compare 65 97 = true)
  namespace_compare_caseinsensitive      (fold a = fold b -> compare a b = true)
  namespace_nonalphabetic_match_exactly  (non-alpha a,b -> compare a b = (a==b))

NONSENSE fold: `badFold` behaves like the real fold on [65,90] but ALSO
collapses byte 66 ('B') to 97 ('a').  So 'A','B','a' all fold together and the
name "Bat" case-insensitively "matches" "aat" -- a catastrophic letter<->letter
over-fold that widens the RFC 5452 questionMatches anti-spoof gate.

If all three generated props still prove for badFold, the spec layer does NOT
constrain letter<->letter over-folding: the props pin only A=a plus non-alpha
identity.  (The only laws that WOULD catch badFold -- foldCaseByte_toNat and
foldByte_eq -- are proof-internal restatements of the impl, co-mutable.)
-/

open VeriDNS.Spec
open VeriDNS.Impl.DomainName (alphabeticByte)

def badFold (b : UInt8) : UInt8 :=
  if b == 66 then 97 else if 65 ≤ b && b ≤ 90 then b + 32 else b

def badCompare (a b : UInt8) : Bool := badFold a == badFold b

-- SANITY: badFold really collapses 'A'(65),'B'(66),'a'(97) to the same image,
-- so it is genuinely a case-sensitivity-widening (spoofing-grade) mutant.
example : badFold 65 = badFold 66 ∧ badFold 66 = badFold 97 := by decide
-- and 'B' and 'a' compare equal even though they are different letters:
example : badCompare 66 97 = true := by decide

-- PROP 1 (A=a example point) — still holds for the bad fold.
theorem bad_compare_example : namespace_compare_example badCompare := by
  show (badFold 65 == badFold 97) = true
  decide

-- PROP 2 (non-alphabetic bytes match exactly) — still holds: badFold only
-- perturbs byte 66, which IS alphabetic, so the non-alpha domain is untouched.
theorem bad_nonalpha_exact :
    namespace_nonalphabetic_match_exactly badCompare alphabeticByte := by
  intro a b ha hb
  show (badFold a == badFold b) = (a == b)
  have fix : ∀ (c : UInt8), alphabeticByte c = false → badFold c = c := by
    intro c hc
    unfold alphabeticByte at hc
    unfold badFold
    rw [Bool.or_eq_false_iff] at hc
    -- c is non-alpha, so c ≠ 66 and not in [65,90]
    have h1 : (c == 66) = false := by
      by_contra h; rw [Bool.not_eq_false] at h
      have : c = 66 := by simpa using h
      rw [this] at hc; simp at hc
    rw [h1]; simp only [Bool.false_eq_true, if_false]
    rw [hc.1]; simp
  rw [fix a ha, fix b hb]

-- PROP 3 (case-insensitivity) — this one is self-referential (compare IS
-- fold-then-eq), so it is a tautology for ANY fold.
theorem bad_caseinsensitive :
    namespace_compare_caseinsensitive UInt8 badCompare badFold := by
  intro a b h
  show (badFold a == badFold b) = true
  rw [h]; simp

#print axioms bad_compare_example
#print axioms bad_nonalpha_exact
#print axioms bad_caseinsensitive
