import VeriDNS.Spec.NetworkSemantics
import VeriDNS.Spec.AnswerAuthenticity

/-!
# Threading answer authenticity through the model's soundness

`Spec/AnswerAuthenticity.lean` proves the scrub keeps only owner-authentic records; the model's
`resolves_answer_authoritative` proves every record a `Resolves` derivation delivers is either
RFC-grounded (`AuthAnswer` / `GroundedServed`) or one of the bounded RFC 5452 threat-model
admissions (`TrustedReplyAnswer` / `TrustedReferralCache` / `TrustedCnameCache` /
`TrustedReplyCache` — an accepts-passing datagram from an off-path attacker who won the id+port
race). The poison-conduit is precisely a `TrustedReplyAnswer` record with a
*foreign owner* being delivered to the client.

`Resolves` is exactly the soundness relation `HasVerdict`/`ioResumeLoop_sound` establish
(`HasVerdict = ∃ …, Resolves … resp ∧ RespAgree v resp`, `Refinement.lean:3131`). Threading the
scrub through it (`resolves_delivered_grounded_and_authentic`) shows the *scrubbed* client
delivery is simultaneously **grounded** AND **owner-authentic** — so even a `TrustedReplyAnswer`
spoof can only ever place a record whose owner is on the genuine CNAME chain from the query name,
never `victim-bank.com`. That is the poison-conduit ruled out *through* soundness, not beside it.
-/

namespace VeriDNS.Spec.Net

/-- **The delivered answer is grounded and owner-authentic — threaded through model soundness.**
    For any `Resolves` derivation (the relation `ioResumeLoop_sound` produces via `HasVerdict`),
    every record surviving the client-delivery scrub is (a) RFC-grounded or a bounded RFC 5452
    trusted-reply admission — `resolves_answer_authoritative` — AND (b) owned by a name genuinely
    `CnameReachable` from the query name — `scrubAnswer_authentic`. -/
theorem resolves_delivered_grounded_and_authentic
    {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ r ∈ scrubAnswer q.qname resp.answer,
      (AuthAnswer net r ∨ GroundedServed net c r ∨ TrustedReplyAnswer ra ednsBuf r
        ∨ TrustedReferralCache ra ednsBuf r ∨ TrustedCnameCache ra ednsBuf r
        ∨ TrustedReplyCache ra ednsBuf r)
      ∧ (∃ n, CnameReachable q.qname resp.answer n ∧ nameEq r.owner n = true) := by
  intro r hr
  exact ⟨resolves_answer_authoritative h r (scrubAnswer_subset hr),
         scrubAnswer_authentic q.qname resp.answer r hr⟩

/-- **The poison-conduit is ruled out through soundness.** No record whose owner is not genuinely
    `CnameReachable` from the query name can be delivered to the client — even though the model
    *admits* `TrustedReplyAnswer` spoof records (an accepts-passing off-path reply). The scrub
    intersects the RFC 5452 residual with owner-authenticity, killing the injection vector. -/
theorem resolves_delivered_no_foreign
    {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (_h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp)
    {r : RR} (hr : r ∈ scrubAnswer q.qname resp.answer)
    (hforeign : ∀ n, CnameReachable q.qname resp.answer n → nameEq r.owner n = false) : False :=
  scrubAnswer_no_foreign hr hforeign

end VeriDNS.Spec.Net
