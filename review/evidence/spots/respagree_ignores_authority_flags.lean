import VeriDNS.Proof.Refinement

/-! SPOT (round 7, NEW — spans confirmed impl-bugs into a single spec-weakness):

    `RespAgree` (Proof/Refinement.lean:3314) is the agreement relation sitting at
    the TOP of every model-soundness conclusion:
        HasVerdict/HasVerdictAt (Refinement.lean:3333/3349) := ∃ … Resolves … ∧ RespAgree v resp
        resolveWithIO_simulates (Refinement.lean:9700) concludes HasVerdict
        NameTree.resolveWithIO_sound / ioResumeLoop_sound conclude via the same shape
        IoResumeSound.ioResumeLoop_sound (:2810) concludes HasVerdictAt

    But `Net.Response` (Spec/NetworkModel.lean:137) has SEVEN fields
        aa, rcode, answer, authority, additional, ra, tc
    and RespAgree constrains ONLY TWO of them:
        def RespAgree a b := a.rcode = b.rcode ∧ a.answer.Perm b.answer
    So the entire verified soundness chain is BLIND to the impl's delivered
        • authority section        (→ confirmed leak bug: replyForResolution passes
                                     upstream AUTHORITY/ADDITIONAL to the client unscrubbed)
        • additional section       (same leak; glue exfiltration)
        • aa bit / ra bit
        • tc bit                   (→ confirmed bug: upstream TC=1 truncated response
                                     delivered to client, no TCP fallback)

    If the two theorems below both prove, then no model-agreement conclusion can
    tell a clean answer from one carrying attacker-injected authority/additional
    records, a forged aa bit, or a spuriously-set TC flag — the soundness statement
    is satisfied identically. -/

open VeriDNS.Spec.Net
open VeriDNS.Proof.Refinement

-- SENSIBLE: identical responses agree (sanity — the relation is not empty).
theorem sensible_refl (r : Response) : RespAgree r r := RespAgree.refl r

/-- NONSENSE: a clean `good` and a `poison` that shares only rcode+answer but
    carries an ARBITRARY attacker authority/additional payload, flips aa, ra, and
    sets tc, are RespAgree-equal.  `authPoison`/`addPoison` are free (attacker
    controlled).  A real observable-verdict oracle must NOT equate these. -/
theorem nonsense_poison_authority_agrees
    (rc : RCode) (ans authPoison addPoison : List RR) :
    RespAgree
      { aa := true,  rcode := rc, answer := ans, authority := [],        additional := [],
        ra := true,  tc := false }
      { aa := false, rcode := rc, answer := ans, authority := authPoison, additional := addPoison,
        ra := false, tc := true } := by
  constructor
  · rfl
  · exact List.Perm.refl ans

/-- Sharpest form: a response that TRUNCATED the delivery (tc := true) while
    injecting foreign authority RRs still "agrees" with the honest zero-authority
    reply — so the confirmed TC-delivery and authority-leak bugs both live in the
    exact fields RespAgree drops.  Distinguishing a real semantic catch from
    proof-script brittleness: these theorems need ZERO invariant lemmas; RespAgree
    literally does not project those fields, so a mutant that garbles
    resp.authority/additional/tc in replyForResolution changes no soundness STATEMENT
    and needs no proof repair. -/
theorem nonsense_truncated_leak_agrees
    (rc : RCode) (ans foreign : List RR) :
    RespAgree
      { aa := true, rcode := rc, answer := ans, authority := [],      additional := [], tc := false }
      { aa := true, rcode := rc, answer := ans, authority := foreign, additional := foreign, tc := true } :=
  ⟨rfl, List.Perm.refl ans⟩
