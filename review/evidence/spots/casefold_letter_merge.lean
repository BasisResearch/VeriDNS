-- SPOT: does the RFC-spec case-fold layer catch a LETTER-LETTER MERGE mutant?
-- Mutant: fold that behaves exactly like the real foldCaseByte EXCEPT it also
-- collapses 'c' (99) onto 'b' (98). This is NOT under-folding (uppercase still
-- folds) and NOT a cross-class collision (no non-letter maps into a letter's
-- image); it merges two DISTINCT lowercase letters, so nameEqCI would report
-- "bat" == "cat".  If all three RFC-spec props still hold, the spec layer does
-- not pin the fold as an injection on letters.

def alphabeticByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

-- honest fold
def foldReal (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

-- MUTANT fold: additionally sends 'c'(99) -> 'b'(98)
def foldMut (b : UInt8) : UInt8 :=
  if b == 99 then 98 else (if 65 ≤ b && b ≤ 90 then b + 32 else b)

-- The three RFC-spec props (verbatim shapes from Spec/DomainName.lean)
def prop_nonalphabetic_match_exactly : (UInt8 → UInt8 → Bool) → (UInt8 → Bool) → Prop :=
  fun compare alphabetic =>
  ∀ (a b : UInt8), alphabetic a = Bool.false → alphabetic b = Bool.false → compare a b = (a == b)

def prop_compare_example : (UInt8 → UInt8 → Bool) → Prop :=
  fun compare => compare 65 97 = Bool.true

def prop_compare_caseinsensitive : (α : Type) → (α → α → Bool) → (α → α) → Prop :=
  fun α compare foldCase => ∀ (a b : α), foldCase a = foldCase b → compare a b = Bool.true

-- Comparator built from the MUTANT fold, exactly as foldCaseByte_example_conforms does
def cmpMut : UInt8 → UInt8 → Bool := fun a b => foldMut a == foldMut b

-- SENSIBLE: the A=a example still passes with the mutant.
theorem sensible_example : prop_compare_example cmpMut := by
  show (foldMut 65 == foldMut 97) = true
  decide

-- SENSIBLE: caseinsensitive is tautological for ANY comparator of the form (f a == f b).
theorem sensible_caseinsensitive : prop_compare_caseinsensitive UInt8 cmpMut foldMut := by
  intro a b h
  show (foldMut a == foldMut b) = true
  simp [h]

-- The mutant preserves non-alphabetic bytes (99 is alphabetic, so exempt).
theorem mut_fixes_nonalpha : ∀ (c : UInt8), alphabeticByte c = false → foldMut c = c := by
  intro c hc
  unfold alphabeticByte at hc
  rw [Bool.or_eq_false_iff] at hc
  have hup : (65 ≤ c && c ≤ 90) = false := hc.1
  have hlo : (97 ≤ c && c ≤ 122) = false := hc.2
  have hne : (c == 99) = false := by
    by_cases h : c = 99
    · subst h; simp at hlo
    · simpa using h
  unfold foldMut
  simp only [hne, hup, Bool.false_eq_true, if_false, ite_false]

-- SENSIBLE: nonalphabetic-exact still passes with the mutant.
theorem sensible_nonalpha : prop_nonalphabetic_match_exactly cmpMut alphabeticByte := by
  intro a b ha hb
  show (foldMut a == foldMut b) = (a == b)
  rw [mut_fixes_nonalpha a ha, mut_fixes_nonalpha b hb]

-- NONSENSE that SHOULD be false for an honest fold but the spec props do NOT rule out:
-- the mutant equates two DISTINCT lowercase letters 'b'(98) and 'c'(99).
theorem nonsense_letters_collapse : cmpMut 98 99 = true := by decide

-- And the honest fold correctly keeps them apart (control):
def cmpReal : UInt8 → UInt8 → Bool := fun a b => foldReal a == foldReal b
theorem control_real_keeps_apart : cmpReal 98 99 = false := by decide
