import VeriDNS.Impl.AnswerScrub



namespace VeriDNS.Impl.Resolver

open VeriDNS.Spec VeriDNS.Impl

variable {RR : Type} [RRParse RR]

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

theorem scrubAnswerB_mem {qname : ByteArray} {answer : Array ByteArray} {bytes' : ByteArray}
    (h : bytes' ∈ scrubAnswerB (RR := RR) qname answer) :
    ∃ bytes ∈ answer, ∃ rr, RRParse.parseRaw (RR := RR) bytes = some rr
      ∧ ∃ m ∈ reachableNamesB (RR := RR) qname answer,
        DomainName.nameEqCI (RRParse.rrName rr) m = true
        ∧ bytes' = setOwnerB (RR := RR) rr bytes m := by
  unfold scrubAnswerB at h
  rw [Array.mem_filterMap] at h
  obtain ⟨bytes, hbytes, hmap⟩ := h
  cases hpr : RRParse.parseRaw (RR := RR) bytes with
  | none => rw [hpr] at hmap; simp at hmap
  | some rr =>
    rw [hpr] at hmap
    simp only at hmap
    cases hf : (reachableNamesB (RR := RR) qname answer).find?
        (fun m => DomainName.nameEqCI (RRParse.rrName (RR := RR) rr) m) with
    | none => rw [hf] at hmap; simp at hmap
    | some m =>
      rw [hf] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      exact ⟨bytes, hbytes, rr, hpr, m, Array.mem_of_find?_eq_some hf,
        Array.find?_some hf, hmap.symm⟩

theorem scrubAnswerB_authentic {qname : ByteArray} {answer : Array ByteArray} {bytes' : ByteArray}
    (h : bytes' ∈ scrubAnswerB (RR := RR) qname answer) :
    ∃ bytes ∈ answer, ∃ (rr : RR) (n : ByteArray),
      RRParse.parseRaw (RR := RR) bytes = some rr
      ∧ CnameReachableB (RR := RR) qname answer n
      ∧ DomainName.nameEqCI (RRParse.rrName rr) n = true
      ∧ bytes' = setOwnerB (RR := RR) rr bytes n := by
  obtain ⟨bytes, hb, rr, hpr, m, hm, hci, heq⟩ := scrubAnswerB_mem h
  exact ⟨bytes, hb, rr, m, hpr, reachableNamesB_sound (RR := RR) qname answer m hm, hci, heq⟩

theorem scrubAnswerB_excludes_foreign {qname : ByteArray} {answer : Array ByteArray}
    {bytes' : ByteArray}
    (hforeign : ∀ (bytes : ByteArray) (rr : RR), bytes ∈ answer →
      RRParse.parseRaw (RR := RR) bytes = some rr →
      ∀ n, CnameReachableB (RR := RR) qname answer n →
        DomainName.nameEqCI (RRParse.rrName rr) n = false)
    (hin : bytes' ∈ scrubAnswerB (RR := RR) qname answer) : False := by
  obtain ⟨bytes, hb, rr, n, hpr, hreach, hneq, -⟩ := scrubAnswerB_authentic (RR := RR) hin
  rw [hforeign bytes rr hb hpr n hreach] at hneq
  simp at hneq

end VeriDNS.Impl.Resolver
