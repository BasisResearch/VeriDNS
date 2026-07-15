/-! SPOT (round 8, NEW — thread c-adjacent: the ACTUALLY-APPLIED, RFC-PUBLISHED
    delivered-answer guarantee).

    The soundness/completeness pair that actually holds at M=IO and is rfc_proves-
    published is:
      * `NameTree.resolveWithIO_sound`     (NameTree.lean:1747)  → conclusion `ShimSound`
      * `NameTree.resolveWithIO_complete`  (NameTreeComplete.lean:3074, ProofLinks:102)
                                                                 → conclusion `ShimComplete`
    with
      ShimSound     rc := (∀ f, rc.1 = .ok f → SectionAgrees T f.answer) ∧ CacheAgrees T rc.2
      ShimComplete  rc := (∀ f, rc.1 = .ok f → f.header.tc = 0 → ∀ k, AnswersFromTree …) ∧ …
      SectionAgrees T rrs := ∀ b ∈ rrs, RRAgrees T b          -- NameTree.lean:34
      AnswersFromTree … := SectionAgrees … ∧ (match treeResolve … | .answer rrs => … contains rrs …)

    TWO STRUCTURAL VACUITIES, both invisible to the published theorems:

    (1) `SectionAgrees` is a ∀ over the delivered RRs, hence DOWNWARD-CLOSED and VACUOUS
        on the empty section.  A resolver that drops answer RRs (or delivers none) is
        `resolveWithIO_sound`-conformant for free — soundness never forces DELIVERY.

    (2) The completeness half is GATED on `f.header.tc = 0`.  For ANY delivered `f` with
        `f.header.tc ≠ 0`, `ShimComplete` waives the entire `AnswersFromTree` obligation.
        So a resolver that stamps `tc := 1` on the client reply satisfies BOTH published
        theorems while delivering a truncated / empty / partial answer — for a tree `T`
        that actually holds the full RRset.  (This is the theorem-level shadow of the
        confirmed TC=1 delivery + no-upstream-TCP impl-bug, but here it is a SPEC gap:
        the completeness statement does not constrain the tc bit itself, so the impl is
        free to assert truncation and escape.)

    WEAPONIZED MUTANT:  in `finalizeForClient` / `finalizeAnswer` force the delivered
    header's `tc := 1` (and/or drop all but the first answer RR).  Expected: both
    `resolveWithIO_sound` and `resolveWithIO_complete` STILL build green — SectionAgrees
    is vacuous on the shrunk section and ShimComplete's `tc = 0` antecedent is never met.
    DISTINGUISH semantic-catch from brittleness:  a completeness theorem that genuinely
    pinned delivery would fail here (goal `AnswersFromTree` for the rich-tree case is now
    unprovable) — if instead the build stays green with NO proof edit, the guarantee was
    vacuous, not merely brittle.

    Below: an abstract skeleton mirroring the exact logical shape (SectionAgrees as a ∀,
    completeness under a tc=0 guard), proving the pair holds for an EMPTY, tc=1 delivery
    over a tree with a nonempty answer — the NONSENSE that a real oracle must reject. -/

-- Abstract stand-ins.
variable {RR Tree : Type}

/-- `SectionAgrees` skeleton: a ∀ over delivered RRs (NameTree.lean:34). -/
def SectionAgrees (inTree : Tree → RR → Prop) (T : Tree) (rrs : List RR) : Prop :=
  ∀ r ∈ rrs, inTree T r

/-- Downward-closed: vacuous on the empty section. -/
theorem sectionAgrees_nil (inTree : Tree → RR → Prop) (T : Tree) :
    SectionAgrees inTree T [] := by
  intro r hr; simp at hr

/-- `ShimSound` skeleton: the SOLE delivered-answer obligation of resolveWithIO_sound. -/
def ShimSound (inTree : Tree → RR → Prop) (T : Tree) (tc : Nat) (answer : List RR) : Prop :=
  SectionAgrees inTree T answer

/-- `ShimComplete` skeleton: completeness GATED on `tc = 0` (ShimComplete, tc=0 antecedent). -/
def ShimComplete (contains : Tree → List RR → Prop) (T : Tree) (tc : Nat)
    (answer : List RR) : Prop :=
  tc = 0 → contains T answer

/-- (SENSIBLE) An honest untruncated delivery that contains the tree's RRset satisfies
    both — proves. -/
theorem honest_both
    (inTree : Tree → RR → Prop) (contains : Tree → List RR → Prop)
    (T : Tree) (answer : List RR)
    (hsound : SectionAgrees inTree T answer)
    (hcomplete : contains T answer) :
    ShimSound inTree T 0 answer ∧ ShimComplete contains T 0 answer :=
  ⟨hsound, fun _ => hcomplete⟩

/-- (NONSENSE — proves, exposing the vacuity) A resolver that delivers an EMPTY answer
    with `tc = 1` satisfies BOTH published guarantees, for an ARBITRARY tree `T` and an
    ARBITRARY `contains` predicate — even one that DEMANDS a nonempty RRset for the empty
    delivery.  The soundness half is vacuous (empty ∀); the completeness half is waived by
    `tc ≠ 0`.  A real correctness oracle must NOT admit an empty, truncated answer for a
    query whose tree holds data. -/
theorem empty_truncated_passes_both
    (inTree : Tree → RR → Prop) (contains : Tree → List RR → Prop)
    (T : Tree) :
    ShimSound inTree T 1 [] ∧ ShimComplete contains T 1 [] := by
  refine ⟨sectionAgrees_nil inTree T, ?_⟩
  intro h; exact absurd h (by decide)
