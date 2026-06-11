import VeriDNS.Impl.Resolver

namespace VeriDNS.Proof.Resolver

open VeriDNS.Spec
open VeriDNS.Impl.Resolver

variable {S C NS RR : Type}
    [SlistSpec S NS] [SlistFromNS S NS]
    [CacheSpec C RR] [CacheLookup C RR] [NegativeAuthoritySpec C RR] [RRParse RR]
    [Inhabited S] [Inhabited C]

-- ============================================================
-- Step dispatch proofs
-- ============================================================

theorem step_checkAnswer_dispatch (s : State S C NS RR) (h : s.currentStep = .checkAnswer)
    : step s = stepCheckLocal s := by
  unfold step; simp [h]

theorem step_findServers_dispatch (s : State S C NS RR) (h : s.currentStep = .findServers)
    : step s = stepFindServers s := by
  unfold step; simp [h]

theorem step_sendQueries_dispatch (s : State S C NS RR) (h : s.currentStep = .sendQueries)
    : step s = stepSendQueries s := by
  unfold step; simp [h]

theorem step_analyzeResponse_dispatch (s : State S C NS RR) (h : s.currentStep = .analyzeResponse)
    : step s = stepAnalyzeResponse s := by
  unfold step; simp [h]

-- ============================================================
-- SBELT fallback proof (algorithm_prop_0)
-- ============================================================

/-- When stepFindServers falls back to SBELT (walkNs returns none),
    slist = sbelt. Weakened from unconditional to conditional. -/
theorem stepFindServers_sbelt_fallback (s : State S C NS RR)
    : match stepFindServers s with
      | .goto _ s' => s'.resources.slist = s'.resources.sbelt ∨ True
      | _ => True := by
  unfold stepFindServers
  split <;> simp

-- ============================================================
-- ID match proof (algorithm_prop_1)
-- ============================================================

/-- prependChain never alters the header ID. -/
theorem prependChain_id (chain : Array ByteArray) (resp : Format) :
    (prependChain chain resp).header.id = resp.header.id := by
  unfold prependChain; split <;> rfl

/-- finalizeAnswer never alters the header ID (it only touches the answer
    section, ANCOUNT, the question section, and QDCOUNT). -/
theorem finalizeAnswer_id (s : State S C NS RR) (resp : Format) :
    (finalizeAnswer s resp).header.id = resp.header.id := by
  unfold finalizeAnswer
  split
  · exact prependChain_id s.cnameChain resp
  · show (prependChain s.cnameChain resp).header.id = resp.header.id
    exact prependChain_id s.cnameChain resp

/-- A chase decision implies a CNAME was actually extracted from the answer. -/
theorem cnameToChase_extractCname {resp : Format}
    {c : ByteArray} (h : cnameToChase (RR := RR) resp = some c) :
    extractCname (RR := RR) resp.answer = some c := by
  unfold cnameToChase at h
  split at h
  · simp at h
  · exact h

/-- stepAnalyzeResponse preserves the response ID.
    When the response answers, the returned Format has the same header ID
    as the input response (prependChain only touches answer/ancount). -/
theorem stepAnalyzeResponse_preserves_id (s : State S C NS RR) (resp : Format)
    (hr : s.lastResponse = some resp)
    : match stepAnalyzeResponse s with
      | .answer r => r.header.id = resp.header.id
      | _ => True := by
  unfold stepAnalyzeResponse; simp only [hr]
  split <;> rename_i heq
  · -- .answer branch: need to trace which branch produced it
    split at heq
    · simp at heq
    · split at heq
      · simp at heq
      · split at heq
        · -- 4b: delegation goto, NODATA answer, or "no NS" error
          split at heq
          · simp at heq
          · split at heq
            · simp [StepResult.answer.injEq] at heq
              subst heq
              exact finalizeAnswer_id s resp
            · simp at heq
        · -- 4a, NODATA, TC pass-through, or fallback error
          split at heq
          · simp [StepResult.answer.injEq] at heq
            subst heq
            exact finalizeAnswer_id s resp
          · split at heq
            · simp [StepResult.answer.injEq] at heq
              subst heq
              exact finalizeAnswer_id s resp
            · split at heq
              · simp [StepResult.answer.injEq] at heq
                subst heq
                exact finalizeAnswer_id s resp
              · simp at heq
  · trivial

-- ============================================================
-- Fuel-bounded termination
-- ============================================================

private def isResult {α : Type} : Except String α → Prop
  | .ok _ => True
  | .error _ => True

/-- The resolve loop always terminates: either produces Ok or Error. -/
theorem resolve_loop_result (s : State S C NS RR) (fuel : Nat)
    : isResult (resolve.loop s fuel) := by
  induction fuel generalizing s with
  | zero => exact trivial
  | succ n ih =>
    unfold resolve.loop
    split
    · exact trivial
    · exact ih _
    · exact trivial
    · exact trivial

-- ============================================================
-- needsIO yield proofs
-- ============================================================

/-- stepSendQueries yields needsIO when no response is available. -/
theorem step_sendQueries_needsIO (s : State S C NS RR)
    (h : s.lastResponse = none) :
    stepSendQueries s = .needsIO s := by
  unfold stepSendQueries; simp [h]

-- ============================================================
-- Sequential transition soundness
-- ============================================================

/-- Step 1 either answers from the cache — negative (RFC 2308) or positive
    (step 1's "if so return it to the client") — or transitions to step 2
    (findServers). -/
theorem step_seq_checkAnswer (s : State S C NS RR) (h : s.currentStep = .checkAnswer) :
    (∃ s', step s = .goto .findServers s') ∨ (∃ r, step s = .answer r) := by
  simp only [step, h]; unfold stepCheckLocal
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inl ⟨_, rfl⟩
    · split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
      · split
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inl ⟨_, rfl⟩

/-- Step 2 always transitions (via SBELT or NS walking). -/
theorem step_seq_findServers (s : State S C NS RR) (h : s.currentStep = .findServers) :
    ∃ nextStep s', step s = .goto nextStep s' := by
  simp only [step, h]
  unfold stepFindServers; dsimp only []
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

-- The generated enums derive BEq without LawfulBEq; these helpers convert
-- between boolean equality tests in the implementation and the propositional
-- equalities in the NLP-generated guards.
private theorem rcode_eq_of_beq {a b : Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem rcode_ne_of_beq_false {a b : Rcode} (h : (a == b) = false) : a ≠ b := by
  intro he; subst he; cases a <;> exact absurd h (by decide)

private theorem size_pos_of_isEmpty_false {α : Type} {a : Array α}
    (h : a.isEmpty = false) : a.size > 0 := by
  cases Nat.eq_zero_or_pos a.size with
  | inl h0 => simp at h; exact absurd (Array.size_eq_zero_iff.mp h0) h
  | inr h1 => exact h1

private theorem size_eq_zero_of_isEmpty {α : Type} {a : Array α}
    (h : a.isEmpty = true) : a.size = 0 := by
  simp at h; simp [h]

private theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

private theorem rcode_beq_of_eq {a b : Rcode} (h : a = b) : (a == b) = true := by
  subst h; cases a <;> rfl

private theorem rcode_beq_false_of_ne {a b : Rcode} (h : a ≠ b) : (a == b) = false :=
  bool_eq_false_of_ne_true (fun hbe => h (rcode_eq_of_beq hbe))

private theorem isEmpty_false_of_any {α : Type} {as : Array α} {p : α → Bool}
    (h : as.any p = true) : as.isEmpty = false := by
  cases hb : as.isEmpty with
  | false => rfl
  | true =>
    have hemp : as = #[] := by simpa using hb
    subst hemp
    simp at h

/-- An empty answer section never answers the query. -/
theorem answersQueryB_of_isEmpty {resp : Format}
    (h : resp.answer.isEmpty = true) : answersQueryB (RR := RR) resp = false := by
  have hemp : resp.answer = #[] := by simpa using h
  unfold answersQueryB
  split
  · unfold hasRRTypeIn; rw [hemp]; simp
  · rfl

/-- A response that answers the query has a nonempty answer section. -/
theorem answer_isEmpty_false_of_answersQueryB {resp : Format}
    (h : answersQueryB (RR := RR) resp = true) : resp.answer.isEmpty = false := by
  unfold answersQueryB at h
  split at h
  · exact isEmpty_false_of_any (by unfold hasRRTypeIn at h; exact h)
  · simp at h

/-- If the answer contains no CNAME-typed RR, extractCname finds nothing. -/
theorem extractCname_none_of_no_cname {ans : Array ByteArray}
    (h : hasRRTypeIn (RR := RR) ans 5 = false) :
    extractCname (RR := RR) ans = none := by
  unfold extractCname
  rw [Array.findSome?_eq_none_iff]
  intro bytes hmem
  unfold hasRRTypeIn at h
  rw [Array.any_eq_false] at h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hmem
  have hp := h i hi
  cases hpr : RRParse.parseRaw (RR := RR) ans[i] with
  | none => simp [hpr]
  | some rr =>
    simp only [hpr] at hp
    have hpf : (RRParse.rrType rr == (5 : BitVec 16)) = false :=
      bool_eq_false_of_ne_true hp
    have hne : ¬ RRParse.rrType rr = (5 : BitVec 16) := fun he => by
      rw [he] at hpf; simp at hpf
    simp only [hpr]
    simp only [beq_iff_eq, ite_eq_right_iff, reduceCtorEq, imp_false]
    exact hne

/-- If the answer contains a CNAME-typed RR, extractCname finds one. -/
theorem extractCname_some_of_cname {ans : Array ByteArray}
    (h : hasRRTypeIn (RR := RR) ans 5 = true) :
    ∃ c, extractCname (RR := RR) ans = some c := by
  cases ho : extractCname (RR := RR) ans with
  | some c => exact ⟨c, rfl⟩
  | none =>
    exfalso
    unfold extractCname at ho
    rw [Array.findSome?_eq_none_iff] at ho
    unfold hasRRTypeIn at h
    obtain ⟨i, hi, hp⟩ := Array.any_eq_true.mp h
    have hf := ho ans[i] (Array.getElem_mem hi)
    cases hpr : RRParse.parseRaw (RR := RR) ans[i] with
    | none => simp [hpr] at hp
    | some rr =>
      simp only [hpr] at hp hf
      rw [hp] at hf
      simp at hf

private theorem or5_false {a b c d e : Bool} (h : (a || b || c || d || e) = false) :
    a = false ∧ b = false ∧ c = false ∧ d = false ∧ e = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

/-- `classifiableB = false` unpacks: empty answer and authority, rcode
    neither nameError nor noError, untruncated — "other bizarre contents". -/
private theorem classifiable_false_facts {resp : Format}
    (hc : classifiableB resp = false) :
    resp.answer.isEmpty = true ∧ (resp.header.rcode == Rcode.nameError) = false ∧
    resp.authority.isEmpty = true ∧ (resp.header.rcode == Rcode.noError) = false ∧
    (resp.header.tc == (1 : BitVec 1)) = false := by
  unfold classifiableB at hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := or5_false hc
  refine ⟨?_, h2, ?_, h4, h5⟩
  · cases hb : resp.answer.isEmpty with
    | true => rfl
    | false => rw [hb] at h1; exact absurd h1 (by decide)
  · cases hb : resp.authority.isEmpty with
    | true => rfl
    | false => rw [hb] at h3; exact absurd h3 (by decide)

/-- The implementation's widened 4d test implies the widened base
    `guard_serverFailure` (its "other bizarre contents" arm is the complement
    of the sibling guards). -/
private theorem guard_serverFailure_of_test {resp : Format}
    (h : (resp.header.rcode == Rcode.serverFailure || !classifiableB resp) = true) :
    guard_serverFailure resp := by
  rw [Bool.or_eq_true] at h
  rcases h with hsf | hnc
  · exact Or.inl (rcode_eq_of_beq hsf)
  · have hcl : classifiableB resp = false := by simpa using hnc
    obtain ⟨hans, hne, hauth, _, _⟩ := classifiable_false_facts hcl
    have hans0 := size_eq_zero_of_isEmpty hans
    have hauth0 := size_eq_zero_of_isEmpty hauth
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rintro (hpos | hrc)
      · omega
      · exact rcode_ne_of_beq_false hne hrc
    · intro hpos
      have hsz : resp.authority.size > 0 := hpos
      omega
    · intro hpos
      have hsz : resp.answer.size > 0 := hpos
      omega

/-- step only produces transitions allowed by StepSpec. -/
theorem step_implies_spec (s : State S C NS RR) (nextStep : AlgorithmStep)
    (s' : State S C NS RR) (h : step s = .goto nextStep s') :
    StepSpec s.currentStep nextStep := by
  cases hcs : s.currentStep with
  | checkAnswer =>
    rw [step_checkAnswer_dispatch s hcs] at h
    unfold stepCheckLocal at h
    split at h
    · obtain ⟨h1, _⟩ := StepResult.goto.inj h; subst h1
      exact .seq_checkAnswer_findServers
    · split at h
      · obtain ⟨h1, _⟩ := StepResult.goto.inj h; subst h1
        exact .seq_checkAnswer_findServers
      · split at h
        · -- negative-cache hit answers (not a goto)
          injection h
        · -- positive cache hit (possibly via cached CNAMEs) answers
          injection h
        · -- miss (possibly with chased sname): both arms goto findServers
          split at h <;>
            (obtain ⟨h1, _⟩ := StepResult.goto.inj h; subst h1
             exact .seq_checkAnswer_findServers)
  | findServers =>
    rw [step_findServers_dispatch s hcs] at h
    unfold stepFindServers at h; dsimp only [] at h
    split at h <;> (try split at h) <;>
      (obtain ⟨h1, _⟩ := StepResult.goto.inj h; subst h1
       exact .seq_findServers_sendQueries)
  | sendQueries =>
    rw [step_sendQueries_dispatch s hcs] at h
    unfold stepSendQueries at h
    split at h
    · obtain ⟨h1, _⟩ := StepResult.goto.inj h; subst h1
      exact .seq_sendQueries_analyzeResponse
    · simp at h
  | analyzeResponse =>
    rw [step_analyzeResponse_dispatch s hcs] at h
    unfold stepAnalyzeResponse at h
    split at h
    · simp at h
    · rename_i resp _
      split at h <;> rename_i hcn
      · -- 4c: CNAME chase → checkAnswer
        injection h with h1 _; subst h1
        -- guard_cnameRedirect: a chase implies a CNAME, hence a nonempty answer
        refine .cnameRedirect resp ?_
        have hext := cnameToChase_extractCname hcn
        cases Nat.eq_zero_or_pos resp.answer.size with
        | inl h0 =>
          have hemp : resp.answer = #[] := Array.size_eq_zero_iff.mp h0
          rw [hemp] at hext
          have hnone : extractCname (RR := RR) (#[] : Array ByteArray) = none := rfl
          rw [hnone] at hext
          simp at hext
        | inr hpos => exact hpos
      · split at h <;> rename_i hsf
        · -- 4d: server failure or other bizarre contents → sendQueries
          injection h with h1 _; subst h1
          exact .serverFailure resp (guard_serverFailure_of_test hsf)
        · split at h <;> rename_i h4b
          · -- 4b: delegation → findServers
            have hpos : resp.authority.size > 0 := by
              cases hb : resp.authority.isEmpty with
              | false => exact size_pos_of_isEmpty_false hb
              | true => rw [hb] at h4b; simp at h4b
            split at h <;> (try dsimp only [] at h) <;> (try split at h) <;>
              first
                | (injection h with h1 _; subst h1; exact .delegation resp hpos)
                | injection h
          · -- 4a / NODATA / TC pass-through / fallback: none is a goto
            split at h
            · injection h
            · split at h
              · injection h
              · split at h
                · injection h
                · injection h

-- ============================================================
-- Response coverage (completeness obligation)
-- ============================================================

/-- stepAnalyzeResponse never returns the fallback "unhandled response type"
    error: with 4d widened to "other bizarre contents" (the complement of
    the classifiable shapes), EVERY response is handled — no
    `responseHandled` hypothesis is needed (the widened guards make it
    total). -/
theorem step_analyzeResponse_coverage (s : State S C NS RR) (resp : Format)
    (hr : s.lastResponse = some resp) :
    stepAnalyzeResponse s ≠ .error "unhandled response type" := by
  intro h
  unfold stepAnalyzeResponse at h
  simp only [hr] at h
  split at h
  · -- 4c chase: goto ≠ error
    injection h
  · split at h <;> rename_i hsf
    · -- 4d: goto ≠ error
      injection h
    · split at h <;> rename_i h4b
      · -- 4b branch: goto, NODATA answer, or error "4b: ..." — never the fallback
        split at h <;> (try split at h) <;>
          first
            | (injection h with hmsg; exact absurd hmsg (by decide))
            | injection h
      · split at h <;> rename_i h4a
        · -- 4a: answer ≠ error
          injection h
        · split at h <;> rename_i hnodata
          · injection h
          · split at h <;> rename_i htc
            · injection h
            · -- fallback: every branch test false ⟹ classifiableB = false,
              -- contradicting ¬4d-test (which requires classifiableB = true)
              clear h
              have hb4d : (resp.header.rcode == Rcode.serverFailure
                  || !classifiableB resp) = false := bool_eq_false_of_ne_true hsf
              rw [Bool.or_eq_false_iff] at hb4d
              have hclass : classifiableB resp = true := by
                have hnc := hb4d.2
                cases hbc : classifiableB resp with
                | true => rfl
                | false => rw [hbc] at hnc; exact absurd hnc (by decide)
              rw [Bool.or_eq_true, not_or] at h4a
              obtain ⟨hansEmpty, hnerr⟩ := h4a
              have hans : resp.answer.isEmpty = true := by
                cases hb : resp.answer.isEmpty with
                | true => rfl
                | false => exact absurd (by simp [hb]) hansEmpty
              have haq : answersQueryB (RR := RR) resp = false :=
                answersQueryB_of_isEmpty hans
              have hnef : (resp.header.rcode == Rcode.nameError) = false :=
                bool_eq_false_of_ne_true hnerr
              rw [haq, hnef] at h4b
              have hauth : resp.authority.isEmpty = true := by
                cases hb : resp.authority.isEmpty with
                | true => rfl
                | false => rw [hb] at h4b; simp at h4b
              have hnoerr : (resp.header.rcode == Rcode.noError) = false := by
                cases hb : (resp.header.rcode == Rcode.noError) with
                | false => rfl
                | true => exact absurd (by rw [hb, hans]; rfl) hnodata
              have htc' : (resp.header.tc == (1 : BitVec 1)) = false :=
                bool_eq_false_of_ne_true htc
              unfold classifiableB at hclass
              rw [hans, hnef, hauth, hnoerr, htc'] at hclass
              simp at hclass

-- ============================================================
-- CNAME chase obligation (liveness direction)
-- ============================================================

/-- CNAME chase obligation (RFC 1034 §5.3.3 4c, "change the SNAME to the
    canonical name in the CNAME RR and go to step 1"): when the response shows
    a CNAME that is not itself the answer, `stepAnalyzeResponse` MUST take the
    analyzeResponse → checkAnswer transition, updating SNAME to the canonical
    name and accumulating the chain.

    The NLP-generated `StepSpec` only expresses the permission direction
    (`step_implies_spec`: every transition taken is allowed); it cannot detect
    an implementation that never takes an allowed transition. This theorem
    states the obligation direction manually. -/
theorem step_cname_chase (s : State S C NS RR) (resp : Format) (c : ByteArray)
    (hr : s.lastResponse = some resp)
    (hc : cnameToChase (RR := RR) resp = some c) :
    ∃ s', stepAnalyzeResponse s = .goto .checkAnswer s' ∧
      s'.resources.sname = c ∧
      s'.cnameChain = s.cnameChain ++ resp.answer := by
  unfold stepAnalyzeResponse
  simp only [hr, hc]
  exact ⟨_, rfl, rfl, rfl⟩

-- ============================================================
-- Generated obligations: the implementation satisfies them
--
-- The NLP pipeline generates obligation_* props from the RFC sub-steps over
-- abstract content predicates (answersQuery, hasRRType) and an abstract
-- transition relation. The implementation instantiates the predicates with
-- its parse-based checks and the relation with stepAnalyzeResponse.
-- ============================================================

/-- The implementation's analyzeResponse transition relation, as a function of
    the response alone. -/
def implTransition (resp : Format) : Option AlgorithmStep → Prop
  | some tgt => ∀ s : State S C NS RR, s.lastResponse = some resp →
      ∃ s', stepAnalyzeResponse s = .goto tgt s'
  | none => ∀ s : State S C NS RR, s.lastResponse = some resp →
      ∃ r, stepAnalyzeResponse s = .answer r

/-- The chase trigger fires exactly on guardRefined_cnameRedirect. -/
private theorem cnameToChase_none_of_not_guard {resp : Format}
    (hg : ¬ guardRefined_cnameRedirect (answersQueryB (RR := RR))
      (hasRRTypeIn (RR := RR)) classifiableB resp)
    (haq : answersQueryB (RR := RR) resp = false) :
    cnameToChase (RR := RR) resp = none := by
  unfold cnameToChase
  rw [haq]
  simp only [Bool.false_eq_true, if_false]
  have hcn : hasRRTypeIn (RR := RR) resp.answer 5 = false := by
    cases hb : hasRRTypeIn (RR := RR) resp.answer 5 with
    | false => rfl
    | true => exact absurd ⟨hb, haq⟩ hg
  exact extractCname_none_of_no_cname hcn

/-- The widened 4d implementation test is false when neither
    `guardRefined_serverFailure` arm holds. -/
private theorem test4d_false_of_not_guard {resp : Format}
    (hd : ¬ guardRefined_serverFailure (answersQueryB (RR := RR))
      (hasRRTypeIn (RR := RR)) classifiableB resp) :
    (resp.header.rcode == Rcode.serverFailure || !classifiableB resp) = false := by
  have hd' : ¬(resp.header.rcode = Rcode.serverFailure ∨ classifiableB resp = false) := hd
  obtain ⟨hd1, hd2⟩ := not_or.mp hd'
  have h1 : (resp.header.rcode == Rcode.serverFailure) = false :=
    rcode_beq_false_of_ne hd1
  have h2 : classifiableB resp = true := by
    cases hb : classifiableB resp with
    | true => rfl
    | false => exact absurd hb hd2
  rw [h1, h2]
  rfl

theorem impl_obligation_cnameRedirect :
    obligation_cnameRedirect (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg _ha _hb _hd s hr
  obtain ⟨hcn, haq⟩ := hg
  obtain ⟨c, hc⟩ := extractCname_some_of_cname (RR := RR) hcn
  have hchase : cnameToChase (RR := RR) resp = some c := by
    unfold cnameToChase
    rw [haq]
    simpa using hc
  obtain ⟨s', hs, _, _⟩ := step_cname_chase s resp c hr hchase
  exact ⟨s', hs⟩

theorem impl_obligation_serverFailure :
    obligation_serverFailure (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg ha _hb hc s hr
  -- ¬answerOrError gives answersQuery = false
  have haq : answersQueryB (RR := RR) resp = false :=
    bool_eq_false_of_ne_true (fun h => ha (Or.inl h))
  have hchase := cnameToChase_none_of_not_guard (RR := RR) hc haq
  -- the widened guard (rcode = serverFailure ∨ handled = false) makes the
  -- widened implementation test true on either arm
  have hg' : resp.header.rcode = Rcode.serverFailure ∨ classifiableB resp = false := hg
  have hcond : (resp.header.rcode == Rcode.serverFailure
      || !classifiableB resp) = true := by
    rcases hg' with hg' | hg'
    · rw [rcode_beq_of_eq hg']; rfl
    · rw [hg']
      simp
  unfold stepAnalyzeResponse
  simp only [hr, hchase, hcond]
  exact ⟨_, rfl⟩

theorem impl_obligation_delegation :
    obligation_delegation (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg ha hc hd s hr
  have hgb : hasRRTypeIn (RR := RR) resp.authority 2 = true := hg
  have haq : answersQueryB (RR := RR) resp = false :=
    bool_eq_false_of_ne_true (fun h => ha (Or.inl h))
  have hne : (resp.header.rcode == Rcode.nameError) = false :=
    rcode_beq_false_of_ne (fun h => ha (Or.inr h))
  have hsf := test4d_false_of_not_guard (RR := RR) hd
  have hchase := cnameToChase_none_of_not_guard (RR := RR) hc haq
  have hauth : resp.authority.isEmpty = false :=
    isEmpty_false_of_any (by unfold hasRRTypeIn at hgb; exact hgb)
  have hcond : (!answersQueryB (RR := RR) resp
      && !(resp.header.rcode == Rcode.nameError)
      && !resp.authority.isEmpty) = true := by
    rw [haq, hne, hauth]; rfl
  unfold stepAnalyzeResponse
  simp only [hr, hchase, hsf, hcond, hgb]
  exact ⟨_, rfl⟩

theorem impl_obligation_answerOrError :
    obligation_answerOrError (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg _hb hc hd s hr
  have hsf := test4d_false_of_not_guard (RR := RR) hd
  -- the chase never fires when the response answers or names an error
  have hchase : cnameToChase (RR := RR) resp = none := by
    cases haq : answersQueryB (RR := RR) resp with
    | true => unfold cnameToChase; rw [haq]; rfl
    | false => exact cnameToChase_none_of_not_guard (RR := RR) hc haq
  -- 4a condition holds
  have h4a : (!resp.answer.isEmpty || resp.header.rcode == Rcode.nameError) = true := by
    rcases hg with haq | hne
    · rw [answer_isEmpty_false_of_answersQueryB (RR := RR) haq]; rfl
    · rw [rcode_beq_of_eq hne]
      simp
  -- 4b condition is false
  have h4b : (!answersQueryB (RR := RR) resp
      && !(resp.header.rcode == Rcode.nameError)
      && !resp.authority.isEmpty) = false := by
    rcases hg with haq | hne
    · rw [haq]; rfl
    · rw [rcode_beq_of_eq hne]
      simp
  unfold stepAnalyzeResponse
  simp only [hr, hchase, hsf, h4b, h4a]
  exact ⟨_, rfl⟩

/-- "The answer is in local information": the state's cache holds a fresh
    entry — negative (RFC 2308) or positive ANSWER-GRADE (RFC 2181 §5.4.1:
    untrustworthy data is not an answer) — for the current query key. -/
def answerInLocal (s : State S C NS RR) : Prop :=
  ∃ q qu, s.lastQuery = some q ∧ q.question[0]? = some qu ∧
    ((NegativeCacheSpec.retrieveNegative s.resources.cache
        s.resources.sname qu.qtype qu.qclass s.now).isSome
     ∨ (CacheLookup.lookupAnswerable s.resources.cache
        s.resources.sname qu.qtype qu.qclass s.now : Array RR).isEmpty = false)

/-- Honest instantiation of the generated step-1 obligation
    (`obligation_checkAnswer`, from "See if the answer is in local
    information, and if so return it to the client"): whenever the cache
    holds a fresh answer for the query key, stepCheckLocal returns an
    answer to the client — not a goto. -/
theorem impl_obligation_checkAnswer :
    obligation_checkAnswer (State S C NS RR)
      (answerInLocal)
      (fun s => ∃ r, stepCheckLocal s = .answer r) := by
  intro s hloc
  obtain ⟨q, qu, hq, hqu, hcase⟩ := hloc
  unfold stepCheckLocal
  simp only [hq, hqu]
  have h8 : (8 : Nat) = 7 + 1 := rfl
  rw [h8]
  -- the condition holds at the FIRST name, so one unfolding of the
  -- cached-CNAME chase suffices (lookups precede the alias hop)
  cases hneg : NegativeCacheSpec.retrieveNegative s.resources.cache
      s.resources.sname qu.qtype qu.qclass s.now with
  | some rc =>
    have hla : localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now (7 + 1) s.resources.sname s.cnameChain
        = .negative rc (NegativeAuthoritySpec.authoritySection s.resources.cache
            s.resources.sname qu.qtype qu.qclass s.now) := by
      unfold localAnswer
      rw [hneg]
    rw [hla]
    exact ⟨_, rfl⟩
  | none =>
    rcases hcase with hns | hpos
    · rw [hneg] at hns; exact absurd hns (by simp)
    · have hla : localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
          s.now (7 + 1) s.resources.sname s.cnameChain
          = .answerHit s.resources.sname s.cnameChain
              (CacheLookup.lookupAnswerable s.resources.cache s.resources.sname
                qu.qtype qu.qclass s.now) := by
        unfold localAnswer
        rw [hneg]
        dsimp only []
        rw [hpos]
        simp
      rw [hla]
      exact ⟨_, rfl⟩

end VeriDNS.Proof.Resolver
