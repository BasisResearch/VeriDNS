/-! SPOT (round 7, NEW, thread c-deepened): the RFC-PUBLISHED, actually-APPLIED
    soundness capstone `resolveWithIO_sound` (Proof/NameTree.lean:1747,
    rfc_proves [1034][1849:1976]) concludes only `SatisfiesM (ShimSound T)`, and

        ShimSound T rc := (∀ f, rc.1 = .ok f → SectionAgrees T f.answer)
                          ∧ CacheAgrees T rc.2                 (NameTree.lean:1585)
        SectionAgrees T rrs := ∀ b ∈ rrs, RRAgrees T b          (:34)
        RRAgrees T bytes := ∃ rr, parseRaw bytes = some rr ∧ RRInTree T rr   (:30)
        RRInTree T rr := ∃ n, nodeAtName T rr.name = some n ∧
                             ∃ rr' ∈ n.resourceSet, sameData rr' rr           (:21)

    CRITICAL STRUCTURAL FACT: `SectionAgrees` / `RRInTree` take NO query argument.
    Each delivered answer RR is validated against the tree AT ITS OWN OWNER
    (`rr.name`), never against the client's QNAME/SNAME.  The RFC 1034 §5.3.3
    algorithm the theorem is published against (step 1 "see if the ANSWER is in
    local information", step 4a "if the response ANSWERS THE QUESTION ... return it
    to the client") demands query-RELEVANCE.  `ShimSound` does not: it is a pure
    ANTI-FABRICATION property (served RR exists somewhere in ground truth), NOT an
    ANTI-MISDIRECTION property (served RR answers *this* query).

    Consequence: a resolver that, for a query for name Q, delivers a REAL, in-tree
    A record whose owner is a DIFFERENT name X (e.g. an attacker-chosen host that
    genuinely exists in the tree/cache) satisfies `SectionAgrees` and therefore the
    published `resolveWithIO_sound`.  The client is misdirected with authentic-but-
    irrelevant data; the soundness theorem cannot see it.

    NOTE this is DISTINCT from the known impl-level scope-gap on `answersQueryB`
    (owner-agnostic classification): here the gap is in the CONCLUSION of the
    rfc-published soundness THEOREM itself — even a perfectly relevance-checking
    `answersQueryB` would leave `ShimSound` unable to certify relevance, and a
    misdirecting mutant leaves the theorem STATEMENT true (semantic, not brittle). -/

-- Faithful schematic of SectionAgrees/RRInTree: membership of a record in the tree
-- keyed on the record's OWN owner, with NO query parameter anywhere.
-- `Owner` = name, `InTreeAt o` = "the tree holds this record's data at owner o".
variable (Owner : Type) [DecidableEq Owner]

-- The real `SectionAgrees T ans` unfolds to exactly this shape for a single RR:
def sectionAgreesRR (InTree : Owner → Prop) (ownerOf : α → Owner) (rr : α) : Prop :=
  InTree (ownerOf rr)

-- NONSENSE: with the tree holding records at BOTH names q and x, delivering the
-- record owned by x in response to a query for q passes `sectionAgreesRR` — the
-- predicate never receives q, so it cannot object.
theorem misdirection_passes_sectionAgrees
    (q x : Owner) (InTree : Owner → Prop)
    (htree_q : InTree q) (htree_x : InTree x)   -- both names really in the tree
    (rrForX : Owner) (hown : rrForX = x) :       -- delivered RR owned by x, not q
    sectionAgreesRR Owner InTree id rrForX := by
  simp only [sectionAgreesRR, hown]; exact htree_x

-- The query `q` is a FREE variable above and appears NOWHERE in the goal: proof of
-- soundness for the wrong-owner answer does not even mention it.  This is the
-- structural vacuity — `SectionAgrees`'s type has no slot for the query.
theorem sectionAgrees_is_query_independent
    (InTree : Owner → Prop) (ownerOf : α → Owner) (rr : α)
    (q₁ q₂ : Owner) :   -- two DIFFERENT queries
    sectionAgreesRR Owner InTree ownerOf rr
      ↔ sectionAgreesRR Owner InTree ownerOf rr := Iff.rfl  -- identical: q irrelevant

/-- CONTRAST — a NON-vacuous delivered-answer soundness must thread the query name
    and require each answer owner to be REACHABLE from it (owner = qname, or a
    CNAME chain to it: the real `Reaches` relation, NameTree.lean:48).  Under that
    spec the wrong-owner record FAILS to certify. -/
def relevantSectionAgreesRR (InTree : Owner → Prop) (Reaches : Owner → Owner → Prop)
    (ownerOf : α → Owner) (q : Owner) (rr : α) : Prop :=
  InTree (ownerOf rr) ∧ Reaches q (ownerOf rr)

theorem relevance_aware_spec_REJECTS_misdirection :
    ¬ (∀ (O : Type) (InTree : O → Prop) (Reaches : O → O → Prop)
         (q x : O), InTree x →
         -- query q, delivered record owned by x, with x NOT reachable from q:
         (¬ Reaches q x) →
         relevantSectionAgreesRR O InTree Reaches id q x) := by
  intro h
  have := h Bool (fun _ => True) (fun a b => a = b) true false trivial (by decide)
  exact absurd this.2 (by decide)

/-- SENSIBLE: when the delivered record's owner IS the query name, BOTH the weak
    (`sectionAgreesRR`) and the relevance-aware spec accept it — the weak spec is
    not false, merely too coarse. -/
theorem sensible_relevant_answer_conforms
    (q : Owner) (InTree : Owner → Prop) (Reaches : Owner → Owner → Prop)
    (htree : InTree q) (hrefl : Reaches q q) :
    relevantSectionAgreesRR Owner InTree Reaches id q q := ⟨htree, hrefl⟩

/-! ── REAL-def anchors (verified with `lake env lean` against the built oleans) ──
    #check (SectionAgrees : Node ResourceRecord → Array ByteArray → Prop)
      ⇒ elaborates: the real conclusion type has NO query/qname/SNAME slot.
    example (T) : SectionAgrees T #[] := by intro b hb; simp at hb
      ⇒ proves: the empty answer is "sound" for every tree (soundness has no lower
        bound; misdirection = swapping in a wrong-owner in-tree record keeps the
        STATEMENT true, so a mutant that misdirects is NOT caught and the pass is
        semantic, not proof-script brittleness). -/

/-! ── The COMPLETENESS capstone does not close the gap either ──
    `resolveWithIO_complete` (rfc_proves [1034], ProofLinks:102) concludes
    `AnswersFromTree T qname qtype fuel resp` (NameTree.lean:121).  Its `.answer`
    arm is:
        SectionAgrees T resp.answer
        ∧ rcode = noError
        ∧ ∀ rr ∈ (treeResolve … qname), ∃ b ∈ resp.answer, sameData …   (LOWER bound)
    There is NO upper bound `∀ b ∈ resp.answer, b ∈ treeResolve-result` in the
    `.answer` case.  So a response that contains the correct qname records PLUS an
    EXTRA real-in-tree record owned by an unrelated/attacker name X satisfies BOTH
    `resolveWithIO_sound` (SectionAgrees) AND `resolveWithIO_complete`
    (AnswersFromTree).  The only artifact that strips wrong-owner answer records is
    the impl `scrubAnswerB` (CNAME-reachability, Impl/AnswerScrub.lean), which is
    composed into NEITHER published capstone. -/
