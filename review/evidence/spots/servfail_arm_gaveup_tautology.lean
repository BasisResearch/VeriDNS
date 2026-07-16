import VeriDNS.Proof.WorldNetwork

/-! SPOT (round 1, new-capstone audit): the SERVFAIL ("error") arm of the NEW
    per-datagram capstones
      `ResolveWithIOSound.serveDatagram_verdict_sound`  (:3553)
      `ResolveWithIOSound.serveDatagram_total`          (:3826)
      `ServeTcp.serveTcpDatagram_verdict_sound`         (:34)
      `ServeTcp.serveTcpDatagram_total`                 (:272)
    claims the emitted SERVFAIL is "justified": it produces

      ∃ slist v, HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] []
                   (αCache cache) slist qm v (αCache cache)
                 ∧ v.rcode = RCode.servFail ∧ v.answer = []

    The claim is a TAUTOLOGY.  `Spec.Net.Resolves.gaveUp` (NetworkSemantics.lean:1660)
    is an UNCONDITIONAL constructor — for every net, ns, cache, slist and query it
    derives the empty SERVFAIL response.  So the arm is derivable with zero
    hypotheses, in particular WITHOUT the run hypothesis `hrun`, without the world
    models, and without any property of the implementation.

    SENSIBLE (should prove):  the arm as the capstone states it.
    NONSENSE (should NOT prove, but does): the very same arm for an ARBITRARY
    response the resolver never computed, and for every query/cache/network at
    once — i.e. an always-SERVFAIL resolver discharges it identically. -/

open VeriDNS.Spec.Net
open VeriDNS.Proof.Refinement (HasVerdictAt)

namespace Spot.ServfailArm

/-- NONSENSE #1 — the exact shape of the capstones' `hV` obligation, proven for
    EVERY network, state, cache, slist and query, with no implementation, no run,
    no `WorldModels`, and no `net.WF`.  This is the whole justification the
    capstone offers for its error arm. -/
theorem servfail_arm_holds_universally
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : Time) (c : Cache) (qm : Query) :
    ∃ slist v, HasVerdictAt net ns ra ednsBuf rttOf now [] [] c slist qm v c
      ∧ v.rcode = RCode.servFail ∧ v.answer = [] :=
  ⟨[], _, VeriDNS.Proof.WorldNetwork.gaveUp_hasVerdictAt net ns ra ednsBuf rttOf c [] qm
    { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }
    rfl rfl, rfl, rfl⟩

/-- NONSENSE #2 — the arm is discharged for a NON-EMPTY slist too, so the
    "vacuous only over an empty slist" reading is too charitable: even a resolver
    holding a full, live, cooperative SLIST is entitled to SERVFAIL and the
    capstone still calls it model-justified. -/
theorem servfail_arm_holds_with_live_slist
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : Time) (c : Cache) (qm : Query) (slist : List String) :
    ∃ v, HasVerdictAt net ns ra ednsBuf rttOf now [] [] c slist qm v c
      ∧ v.rcode = RCode.servFail ∧ v.answer = [] :=
  ⟨_, VeriDNS.Proof.WorldNetwork.gaveUp_hasVerdictAt net ns ra ednsBuf rttOf c slist qm
    { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }
    rfl rfl, rfl, rfl⟩

/-- NONSENSE #3 — the four-way `by_cases` on the error STRING inside
    `serveDatagram_verdict_sound` (:3671-3691, `loopDetected`/`exhausted`/`gaveUp`)
    is decoration: `gaveUp` alone covers every message, so no error message the
    implementation can emit is ever unjustifiable.  Stated as: for EVERY msg. -/
theorem every_error_message_is_justified
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : Time) (c : Cache) (qm : Query) :
    ∀ _msg : String, ∃ slist v, HasVerdictAt net ns ra ednsBuf rttOf now [] [] c slist qm v c
      ∧ v.rcode = RCode.servFail ∧ v.answer = [] :=
  fun _ => servfail_arm_holds_universally net ns ra ednsBuf rttOf now c qm

/-- SENSIBLE, and NOT provable from this material — the property the arm pretends
    to have: a SERVFAIL is justified only when the model could not have produced a
    non-SERVFAIL verdict.  Stated as a would-be lemma; there is no proof, because
    `gaveUp` makes both verdicts simultaneously derivable for the same inputs.
    The witness below shows the model is genuinely ambiguous: NXDOMAIN-and-SERVFAIL
    both hold at once for the same (net, ns, cache, slist, query). -/
theorem model_is_ambiguous_servfail_never_excludes_success
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : Time) (c : Cache) (qm : Query) (slist : List String)
    (v : Response)
    (hgood : HasVerdictAt net ns ra ednsBuf rttOf now [] [] c slist qm v c) :
    ∃ vbad, HasVerdictAt net ns ra ednsBuf rttOf now [] [] c slist qm vbad c
      ∧ vbad.rcode = RCode.servFail := by
  refine ⟨_, VeriDNS.Proof.WorldNetwork.gaveUp_hasVerdictAt net ns ra ednsBuf rttOf c slist qm
    { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }
    rfl rfl, rfl⟩

end Spot.ServfailArm
