import VeriDNS.Impl.DomainName
import VeriDNS.Spec.DomainName

open VeriDNS.Spec
open VeriDNS.Impl.DomainName

/-! SPOT (round 4, NEW): the three generated RFC 1035 §3.1 case-fold props leave a
    CROSS-CLASS collision hole that survives the *real* `alphabeticByte` instantiation.

    `namespace_nonalphabetic_match_exactly compare alphabetic` requires
    `compare a b = (a==b)` ONLY when BOTH `a` and `b` are non-alphabetic.  A fold that
    maps a NON-letter into the fold-image of a LETTER makes a (non-letter, letter)
    MIXED pair collide — excluded by the premise.  Prop #2 (`caseinsensitive`) is a
    tautology (compare := beq-of-fold).  Prop #1 (`example`) pins only A=a.  So the
    collision is invisible to ALL THREE props under the exact `alphabeticByte` the real
    proof (`foldCaseByte_nonalphabetic_exact`, Proof/DomainName.lean:650) uses.

    Mutant `surgicalFold` = real uppercase fold PLUS folding digit '5'(0x35=53) to
    0x75=117 (= real fold of 'U').  Then `nameEqCI "5" "U" = true`. -/

def surgicalFold (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32          -- real A..Z -> a..z fold (keeps A=a)
  else if b == 53 then 117 else b          -- extra: digit '5' collides with fold('U')

def surgicalName (n : ByteArray) : ByteArray := ⟨n.data.map surgicalFold⟩
def surgicalEqCI (a b : ByteArray) : Bool := surgicalName a == surgicalName b

-- OBSERVABLE BUG: digit '5' and letter 'U' compare EQUAL under the mutant fold.
theorem BUG_digit5_collides_with_U :
    surgicalEqCI (ByteArray.mk #[53]) (ByteArray.mk #[85]) = true := by
  native_decide

-- RFC prop #1 (A=a example) — still holds.
theorem mutant_passes_example :
    namespace_compare_example (fun a b => surgicalFold a == surgicalFold b) := by
  show (surgicalFold 65 == surgicalFold 97) = true
  native_decide

-- RFC prop #3 (non-alphabetic exact match) — TRUE under the REAL `alphabeticByte`
-- (finite check over UInt8×UInt8).  The '5'~'U' collision is a MIXED-class pair,
-- excluded by the premise, so the STATEMENT genuinely holds — not script brittleness.
theorem mutant_passes_nonalpha_REAL_alpha :
    namespace_nonalphabetic_match_exactly
      (fun a b => surgicalFold a == surgicalFold b) alphabeticByte := by
  intro a b ha hb
  show (surgicalFold a == surgicalFold b) = (a == b)
  -- On non-alphabetic bytes, surgicalFold reduces to `if c==53 then 117 else c`.
  have hfold : ∀ c : UInt8, alphabeticByte c = false →
      surgicalFold c = (if c == 53 then 117 else c) := by
    intro c hc
    unfold alphabeticByte at hc
    rw [Bool.or_eq_false_iff] at hc
    unfold surgicalFold
    rw [hc.1]; rfl
  -- A non-alphabetic byte is never 117 ('u' is alphabetic).
  have hne117 : ∀ c : UInt8, alphabeticByte c = false → c ≠ 117 := by
    intro c hc h; subst h; simp [alphabeticByte] at hc
  rw [hfold a ha, hfold b hb]
  by_cases ha53 : a = 53 <;> by_cases hb53 : b = 53
  · subst ha53; subst hb53; decide
  · subst ha53
    have hbe : (b == 53) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hb53 h
    have hbn : (117 == b) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h => (hne117 b hb) h.symm
    have hab : ((53 : UInt8) == b) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h => hb53 h.symm
    simp [hbe, hbn, hab]
  · subst hb53
    have hae : (a == 53) = false := by rw [beq_eq_false_iff_ne]; exact fun h => ha53 h
    have han : (a == 117) = false := by
      rw [beq_eq_false_iff_ne]; exact hne117 a ha
    have hab : (a == (53 : UInt8)) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h => ha53 h
    simp [hae, han, hab]
  · have hae : (a == 53) = false := by rw [beq_eq_false_iff_ne]; exact fun h => ha53 h
    have hbe : (b == 53) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hb53 h
    simp [hae, hbe]

-- RFC prop #2 (case-insensitive) — holds tautologically (compare = beq of fold).
theorem mutant_passes_caseinsensitive :
    namespace_compare_caseinsensitive ByteArray surgicalEqCI surgicalName := by
  intro a b h
  show surgicalEqCI a b = true
  unfold surgicalEqCI; rw [h]
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp

/-! CONTROL: the CORRECT fold has NO such collision — sanity that the props are not
    trivially true of everything (the SENSIBLE direction). -/
theorem control_realfold_no_5U_collision :
    nameEqCI (ByteArray.mk #[53]) (ByteArray.mk #[85]) = false := by
  native_decide

/-! Distinguisher: `BUG_digit5_collides_with_U` proves (observable defect) while all
    three `mutant_passes_*` are TRUE statements under the exact real instantiation.
    Replacing `foldCaseByte` by `surgicalFold` and re-proving
    `foldCaseByte_nonalphabetic_exact` (statement stays true, `native_decide` closes it)
    builds green with a live name collision — semantic, not a repaired tactic script. -/
