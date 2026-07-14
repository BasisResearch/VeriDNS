import VeriDNS.Spec.NetworkSemantics
import VeriDNS.Spec.AnswerAuthenticity




namespace VeriDNS.Spec.Net

theorem resolves_delivered_grounded_and_authentic
    {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ r ∈ scrubAnswer q.qname resp.answer,
      (∃ r₀ ∈ resp.answer,
        r.rdata = r₀.rdata ∧ r.ttl = r₀.ttl ∧ r.cls = r₀.cls ∧ nameEq r.owner r₀.owner = true
        ∧ (AuthAnswer net r₀ ∨ GroundedServed net c r₀ ∨ TrustedReplyAnswer ra ednsBuf r₀
          ∨ TrustedReferralCache ra ednsBuf r₀ ∨ TrustedCnameCache ra ednsBuf r₀
          ∨ TrustedReplyCache ra ednsBuf r₀))
      ∧ (∃ n, CnameReachable q.qname resp.answer n ∧ nameEq r.owner n = true) := by
  intro r hr
  obtain ⟨r₀, hr₀, hrd, httl, hcls, hown⟩ := scrubAnswer_data hr
  exact ⟨⟨r₀, hr₀, hrd, httl, hcls, hown, resolves_answer_authoritative h r₀ hr₀⟩,
         scrubAnswer_authentic q.qname resp.answer r hr⟩

theorem resolves_delivered_no_foreign
    {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (_h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp)
    {r : RR} (hr : r ∈ scrubAnswer q.qname resp.answer)
    (hforeign : ∀ n, CnameReachable q.qname resp.answer n → nameEq r.owner n = false) : False :=
  scrubAnswer_no_foreign hr hforeign

end VeriDNS.Spec.Net
