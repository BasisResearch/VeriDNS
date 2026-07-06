import VeriDNS.Impl.AnswerScrub

/-!
# Executable client-answer scrub — authenticity

Wire-level counterpart of `Spec/AnswerAuthenticity.lean`. `scrubAnswerB_no_foreign` proves the
implemented scrub cannot emit a record whose owner is not genuinely CNAME-reachable from the
queried name — the executable form of "the poison-conduit is ruled out". Mirrors the
`bailiwickRaws_owner_inBailiwick` pattern (`Impl/Resolver.lean`).
-/

namespace VeriDNS.Impl.Resolver

open VeriDNS.Spec VeriDNS.Impl

variable {RR : Type} [RRParse RR]

/-- Wire-level entitlement: the least set of owner names containing `qname` and closed under a
    CNAME (type 5) record present in `answer` whose owner is already reachable (case-insensitively). -/
inductive CnameReachableB (qname : ByteArray) (answer : Array ByteArray) : ByteArray → Prop where
  | root : CnameReachableB qname answer qname
  | step (bytes : ByteArray) (hmem : bytes ∈ answer) (rr : RR)
      (hpr : RRParse.parseRaw (RR := RR) bytes = some rr)
      (hcn : (RRParse.rrType rr == (5 : BitVec 16)) = true)
      (n : ByteArray) (hn : CnameReachableB qname answer n)
      (hmatch : DomainName.nameEqCI (RRParse.rrName rr) n = true) :
      CnameReachableB qname answer (RRParse.rrRdata rr)

theorem reachIterB_sound (qname : ByteArray) (answer : Array ByteArray) :
    ∀ (k : Nat) (reach : Array ByteArray),
      (∀ m ∈ reach, CnameReachableB (RR := RR) qname answer m) →
      ∀ n ∈ reachIterB (RR := RR) answer k reach, CnameReachableB (RR := RR) qname answer n := by
  intro k
  induction k with
  | zero => intro reach hreach n hn; exact hreach n hn
  | succ k ih =>
    intro reach hreach n hn
    apply ih (reachStepB (RR := RR) answer reach) _ n hn
    intro m hm
    unfold reachStepB at hm
    rw [Array.mem_append] at hm
    rcases hm with hm | hm
    · exact hreach m hm
    · rw [Array.mem_filterMap] at hm
      obtain ⟨bytes, hbytes, hrt⟩ := hm
      unfold reachTarget? at hrt
      cases hpr : RRParse.parseRaw (RR := RR) bytes with
      | none => rw [hpr] at hrt; simp at hrt
      | some rr =>
        rw [hpr] at hrt
        simp only at hrt
        by_cases hg : (RRParse.rrType rr == (5 : BitVec 16)
            && nameMemB (RRParse.rrName rr) reach) = true
        · rw [if_pos hg] at hrt
          simp only [Bool.and_eq_true] at hg
          obtain ⟨hty, hnm⟩ := hg
          unfold nameMemB at hnm
          rw [Array.any_eq_true] at hnm
          obtain ⟨i, hlt, hoeq⟩ := hnm
          have hm' : RRParse.rrRdata rr = m := by simpa using hrt
          rw [← hm']
          exact CnameReachableB.step bytes hbytes rr hpr hty reach[i]
            (hreach reach[i] (Array.getElem_mem hlt)) (by simpa using hoeq)
        · rw [if_neg hg] at hrt; simp at hrt

theorem reachableNamesB_sound (qname : ByteArray) (answer : Array ByteArray) :
    ∀ n ∈ reachableNamesB (RR := RR) qname answer, CnameReachableB (RR := RR) qname answer n := by
  apply reachIterB_sound
  intro m hm
  rw [Array.mem_singleton] at hm; subst hm
  exact CnameReachableB.root

/-- The scrub only drops records. -/
theorem scrubAnswerB_subset {qname : ByteArray} {answer : Array ByteArray} {bytes : ByteArray}
    (h : bytes ∈ scrubAnswerB (RR := RR) qname answer) : bytes ∈ answer :=
  (Array.mem_filter.mp h).1

/-- **Every surviving record is entitled.** Any record the scrub keeps parses to an rr whose owner
    is genuinely `CnameReachableB` from the query name. -/
theorem scrubAnswerB_authentic {qname : ByteArray} {answer : Array ByteArray} {bytes : ByteArray}
    (h : bytes ∈ scrubAnswerB (RR := RR) qname answer) :
    ∃ (rr : RR) (n : ByteArray), RRParse.parseRaw (RR := RR) bytes = some rr
      ∧ CnameReachableB (RR := RR) qname answer n
      ∧ DomainName.nameEqCI (RRParse.rrName rr) n = true := by
  have hfil := Array.mem_filter.mp h
  have hpred := hfil.2
  unfold scrubAnswerB at h
  cases hpr : RRParse.parseRaw (RR := RR) bytes with
  | none => rw [hpr] at hpred; simp at hpred
  | some rr =>
    rw [hpr] at hpred
    simp only at hpred
    unfold nameMemB at hpred
    rw [Array.any_eq_true] at hpred
    obtain ⟨i, hlt, hneq⟩ := hpred
    refine ⟨rr, (reachableNamesB (RR := RR) qname answer)[i], rfl,
      reachableNamesB_sound (RR := RR) qname answer _ (Array.getElem_mem hlt), ?_⟩
    simpa using hneq

/-- **The poison-conduit is ruled out by the implementation.** A record whose owner is not
    `CnameReachableB` from the query name — not the query name, and not reachable through a CNAME
    chain genuinely present in the answer — cannot be delivered to the client. -/
theorem scrubAnswerB_excludes_foreign {qname : ByteArray} {answer : Array ByteArray}
    {bytes : ByteArray} {rr : RR}
    (hpr : RRParse.parseRaw (RR := RR) bytes = some rr)
    (hforeign : ∀ n, CnameReachableB (RR := RR) qname answer n →
      DomainName.nameEqCI (RRParse.rrName rr) n = false)
    (hin : bytes ∈ scrubAnswerB (RR := RR) qname answer) : False := by
  obtain ⟨rr', n, hpr', hreach, hneq⟩ := scrubAnswerB_authentic (RR := RR) hin
  rw [hpr] at hpr'
  cases hpr'
  rw [hforeign n hreach] at hneq
  simp at hneq

end VeriDNS.Impl.Resolver
