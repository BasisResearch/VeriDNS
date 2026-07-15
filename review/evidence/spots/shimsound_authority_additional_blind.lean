import VeriDNS.Proof.NameTree

/-! SPOT (round 9, NEW — sharpens the authority-leak from the model layer up to the
    PUBLISHED + APPLIED IO-facing soundness conclusion).

    Prior work (`respagree_ignores_authority_flags.lean`) showed the MODEL verdict
    relation `RespAgree` (Refinement.lean) equates responses differing in authority/
    additional/aa/ra/tc.  But `RespAgree` feeds `HasVerdict`/`resolveWithIO_simulates`,
    which is ORPHANED (never applied, not rfc_proves-published).

    This SPOT targets the OTHER, load-bearing conclusion:

        ShimSound (NameTree.lean:1587):
            ShimSound T (rc) := (∀ f, rc.1 = .ok f → SectionAgrees T f.answer)
                                 ∧ CacheAgrees T rc.2

        resolveWithIO_sound (NameTree.lean:1747)  concludes  SatisfiesM (ShimSound T) …
        ioResumeLoop_sound   (NameTree.lean:1633)  concludes  SatisfiesM (ShimSound T) …
        Both are rfc_proves-PUBLISHED  (ProofLinks.lean:59-60, [1034][1849:1976])
        and APPLIED (resolveWithIO_sound uses ioResumeLoop_sound at :1763).

    `ShimSound` has exactly TWO conjuncts.  Neither mentions `f.authority` or
    `f.additional`.  So the delivered reply's authority + additional sections are
    UNCONSTRAINED by the published IO soundness — even though `replyForResolution`
    forwards the upstream response's AUTHORITY/ADDITIONAL to the client verbatim
    (confirmed leak: "Cache-miss path leaks upstream AUTHORITY (NS)+ADDITIONAL (glue)
    to the client unscrubbed").

    Note this is a STRICTLY STRONGER blindness than the RespAgree one: the oracle
    premise `NetworkConsistent`/`ResponseConsistent` (NameTree.lean:1577/78-90) DOES
    constrain all three sections of the *upstream* resp — but that guarantee is
    DROPPED on the way out: only `SectionAgrees T f.answer` survives into ShimSound,
    so the client-facing reply keeps no authority/additional obligation. -/

open VeriDNS.Spec
open VeriDNS.Impl.Cache
open VeriDNS.Proof.NameTree

/-- An empty ground-truth tree: a root node with no records and no children. -/
def emptyTree : Node ResourceRecord := Node.mk (ByteArray.mk #[]) #[] #[]

/-- SENSIBLE (baseline): ShimSound genuinely projects the answer section — this is
    the *real* content of the theorem and it proves, so the property is not empty. -/
theorem sensible_answer_is_constrained
    (f : Format) (c : DnsCache)
    (h : ShimSound emptyTree (.ok f, c)) :
    SectionAgrees emptyTree f.answer :=
  h.1 f rfl

/-- NONSENSE: a delivered reply carrying an ARBITRARY attacker-controlled authority
    AND additional section (with an empty answer) satisfies the PUBLISHED soundness
    conclusion `ShimSound` against the empty tree.  `authPoison`/`addPoison` are free.
    A soundness statement that actually protected the client MUST NOT admit this —
    yet it proves, because ShimSound never reads `.authority`/`.additional`. -/
theorem nonsense_forged_authority_is_sound
    (authPoison addPoison : Array ByteArray) :
    ShimSound emptyTree
      (.ok { header := default, question := #[], answer := #[],
             authority := authPoison, additional := addPoison }, DnsCache.empty) := by
  refine ⟨?_, cacheAgrees_empty _⟩
  intro f hf
  cases hf
  -- SectionAgrees over the empty answer section is vacuous, regardless of authority.
  intro b hb
  simp at hb
