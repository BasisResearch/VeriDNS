/-! SPOT (round 7, NEW): the two RFC-PUBLISHED, APPLIED capstones over the executed
    `resolveWithIO` — `resolveWithIO_sound` (NameTree.lean:1747, ShimSound, ProofLinks
    :60 [1034][1849:1976]) and `resolveWithIO_complete` (NameTreeComplete.lean:3074,
    ShimComplete, ProofLinks :101-102/:103 [1034][1849:1976]+[2181][195:202]) — JOINTLY
    fail to force any DNS data to be delivered.  A resolver that answers every query
    with an EMPTY answer section flagged tc=1 satisfies BOTH.

    GREP FACTS (source, no proof needed):
      * ShimSound (NameTree.lean:1585-1587):
          (∀ f, rc.1 = .ok f → SectionAgrees T f.answer) ∧ CacheAgrees T rc.2
        SectionAgrees (NameTree.lean:34) = ∀ b ∈ rrs.toList, RRAgrees T b  — a pure
        SUBSET/soundness property, VACUOUSLY true when f.answer = #[].
      * ShimComplete (NameTreeComplete.lean:2712-2717):
          (∀ f, rc.1 = .ok f → f.header.tc = 0 → ∀ k, AnswersFromTree T qn qt k f)
          ∧ CacheAgrees ∧ LookupComplete ∧ OneExpiryPerKey ∧ NegativesFaithful
        The ONLY delivered-answer obligation, AnswersFromTree (NameTree.lean:121-136,
        which DOES force treeResolve's `.answer rrs` records into resp.answer), is gated
        behind `f.header.tc = 0`.  With tc=1 the implication is vacuous.
        The remaining conjuncts are all about the OUTPUT CACHE rc.2, not the delivered f.
      * Every non-tc-gated completeness clause in ResponseConsistent (NameTree.lean:78-119)
        is separately gated on the answer being NON-empty: `rcodeFaithful` (:92, answer.size>0),
        `answerShape`/`answersFaithful` (:95/:99, tc=0 ∧ answer.size>0/HasType),
        `AnswerComplete` (:37-46, "answer already HasType qtype"), `nodataDeserved` (:115, tc=0).
        None fires on an empty answer.

    CONSEQUENCE: mutate `cacheResponse` (Resolver.lean:220) to
        answer := #[]     (drop the RRset)
        header := { … with tc := 1 }   (flag truncation)
    — and likewise `negativeResponse`/the network `.answer` deliveries.  The delivered
    response carries no records; the resolver is observably catastrophic (serves NO data
    for any name).  Yet ShimSound is vacuous (SectionAgrees #[]) and ShimComplete is
    vacuous (tc=1 kills AnswersFromTree; cache conjuncts untouched since a drop-only mutant
    need not corrupt the cache).  BOTH published capstones stay TRUE.

    This is a SPEC weakness (a truncation escape hatch) distinct from the CONFIRMED
    impl-bug "upstream TC=1 delivered to client": here the *published soundness AND
    completeness theorems themselves* place no obligation on a truncated/empty delivery,
    so a resolver that truncates EVERYTHING is certified sound+complete.

    The schematic below reproduces the exact logical shape.
      (SENSIBLE) at tc=0 the completeness obligation genuinely forces the tree records
                 into the answer — proves only for a resolver that delivers them.
      (NONSENSE) at tc=1 with an empty answer, BOTH the subset-soundness and the
                 completeness obligations hold — a no-data resolver is certified.
                 Its provability IS the weakness. -/

-- Abstract stand-ins for the record / tree types.
variable {RR : Type}

/-- SectionAgrees: every delivered record is in the tree (subset / soundness only). -/
def SectionAgrees (inTree : RR → Prop) (answer : List RR) : Prop :=
  ∀ r, r ∈ answer → inTree r

/-- The completeness obligation actually forcing delivery: every tree record for the
    query is present in the answer.  (AnswersFromTree's `.answer rrs` branch.) -/
def DeliversAll (treeRecords : List RR) (answer : List RR) : Prop :=
  ∀ r, r ∈ treeRecords → r ∈ answer

/-- ShimSound's delivered-answer clause. -/
def ShimSoundAnswer (inTree : RR → Prop) (answer : List RR) : Prop :=
  SectionAgrees inTree answer

/-- ShimComplete's delivered-answer clause: gated on tc = 0. -/
def ShimCompleteAnswer (treeRecords : List RR) (tc : Nat) (answer : List RR) : Prop :=
  tc = 0 → DeliversAll treeRecords answer

/-- (SENSIBLE) At tc=0, ShimComplete genuinely forces every tree record into the answer.
    A resolver that delivers exactly the tree records satisfies both clauses. -/
theorem honest_delivers
    (inTree : RR → Prop) (treeRecords : List RR)
    (hsub : ∀ r, r ∈ treeRecords → inTree r) :
    ShimSoundAnswer inTree treeRecords
    ∧ ShimCompleteAnswer treeRecords 0 treeRecords :=
  ⟨fun r hr => hsub r hr, fun _ r hr => hr⟩

/-- (NONSENSE) A resolver whose answer is EMPTY and whose header flags tc=1 satisfies
    BOTH the published soundness AND completeness delivered-answer clauses — for an
    ARBITRARY non-empty tree.  A real correctness pair must NOT certify a no-data
    resolver.  It proves; the provability is the vacuity. -/
theorem nodata_resolver_certified
    (inTree : RR → Prop) (treeRecords : List RR) :
    ShimSoundAnswer inTree ([] : List RR)          -- soundness: subset of anything
    ∧ ShimCompleteAnswer treeRecords 1 ([] : List RR) := by  -- completeness: tc=1 ⇒ vacuous
  refine ⟨?_, ?_⟩
  · intro r hr; exact absurd hr (by simp)
  · intro htc; exact absurd htc (by decide)

/-- Sharpest form: for a FIXED tree with a real record `good`, the SAME published
    delivered-answer predicates are satisfied by a resolver returning NOTHING (empty,
    tc=1).  Delivery is therefore not pinned by the published capstones. -/
theorem completeness_does_not_pin_delivery
    (inTree : RR → Prop) (good : RR) (hgood : inTree good) :
    (ShimSoundAnswer inTree [good] ∧ ShimCompleteAnswer [good] 0 [good])   -- honest
    ∧ (ShimSoundAnswer inTree [] ∧ ShimCompleteAnswer [good] 1 []) := by   -- no-data, tc=1
  refine ⟨⟨fun r hr => ?_, fun _ r hr => hr⟩, ⟨fun r hr => absurd hr (by simp), ?_⟩⟩
  · rcases List.mem_singleton.mp hr with rfl; exact hgood
  · intro htc; exact absurd htc (by decide)
