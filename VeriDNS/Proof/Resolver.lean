import VeriDNS.Impl.Resolver

namespace VeriDNS.Proof.Resolver

open VeriDNS.Spec
open VeriDNS.Impl.Resolver

variable {S C NS RR : Type}
    [SlistSpec S NS] [SlistFromNameSpec S NS]
    [CacheSpec C RR] [TrustworthinessSpec C RR] [NegativeAuthoritySpec C RR] [RRParse RR]
    [Inhabited S] [Inhabited C]

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

def nsSearchFails (s : State S C NS RR) : Prop :=
  stepFindServers.walkNs (C := C) (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = none ∧
  (!SlistFromNameSpec.searchFails (NS := NS) s.resources.slist
      && decide (0 < SlistFromNameSpec.matchCount (NS := NS) s.resources.slist)) = false

def findServersState (s : State S C NS RR) : State S C NS RR :=
  match stepFindServers s with
  | .goto _ s' => s'
  | _ => s

theorem impl_algorithm_sbelt_fallback :
    algorithm_prop_0 (State S C NS RR) S C NS RR
      nsSearchFails
      (fun s => (findServersState s).resources) := by
  intro s hfail
  obtain ⟨hwalk, hcloser⟩ := hfail
  unfold findServersState stepFindServers
  simp only [hwalk, hcloser]
  rfl

theorem prependChain_id (chain : Array ByteArray) (resp : Format) :
    (prependChain chain resp).header.id = resp.header.id := by
  unfold prependChain; split <;> rfl

theorem finalizeAnswer_id (s : State S C NS RR) (resp : Format) :
    (finalizeAnswer s resp).header.id = resp.header.id := by
  unfold finalizeAnswer
  split
  · exact prependChain_id s.cnameChain resp
  · show (prependChain s.cnameChain resp).header.id = resp.header.id
    exact prependChain_id s.cnameChain resp

theorem cnameToChase_extractCname {resp : Format}
    {c : ByteArray} (h : cnameToChase (RR := RR) resp = some c) :
    extractCname (RR := RR) resp.answer = some c := by
  unfold cnameToChase at h
  split at h
  · simp at h
  · exact h

theorem stepAnalyzeResponse_preserves_id (s : State S C NS RR) (resp : Format)
    (hr : s.lastResponse = some resp)
    : match stepAnalyzeResponse s with
      | .answer r _ => r.header.id = resp.header.id
      | _ => True := by
  unfold stepAnalyzeResponse; simp only [hr]
  split <;> rename_i heq
  ·
    split at heq
    · split at heq
      · simp [StepResult.answer.injEq] at heq
        obtain ⟨heq, -⟩ := heq
        subst heq
        exact finalizeAnswer_id s resp
      · split at heq <;> simp at heq
    · split at heq
      · simp at heq
      · split at heq
        ·
          split at heq
          · simp at heq
          · split at heq
            · simp [StepResult.answer.injEq] at heq
              obtain ⟨heq, -⟩ := heq
              subst heq
              exact finalizeAnswer_id s resp
            · simp at heq
        ·
          split at heq
          · simp [StepResult.answer.injEq] at heq
            obtain ⟨heq, -⟩ := heq
            subst heq
            exact finalizeAnswer_id s resp
          · split at heq
            · simp [StepResult.answer.injEq] at heq
              obtain ⟨heq, -⟩ := heq
              subst heq
              exact finalizeAnswer_id s resp
            · split at heq
              · simp [StepResult.answer.injEq] at heq
                obtain ⟨heq, -⟩ := heq
                subst heq
                exact finalizeAnswer_id s resp
              · split at heq
                · simp [StepResult.answer.injEq] at heq
                  obtain ⟨heq, -⟩ := heq
                  subst heq
                  exact finalizeAnswer_id s resp
                · simp at heq
  · trivial

theorem step_needsIO_inversion (s s' : State S C NS RR)
    (h : step s = .needsIO s') :
    s' = s ∧ s.currentStep = .sendQueries ∧ s.lastResponse = none := by
  cases hcs : s.currentStep with
  | checkAnswer =>
    rw [step_checkAnswer_dispatch s hcs] at h
    unfold stepCheckLocal at h
    split at h <;> (try split at h) <;> (try split at h) <;>
      first | injection h | (split at h <;> injection h)
  | findServers =>
    rw [step_findServers_dispatch s hcs] at h
    unfold stepFindServers at h
    dsimp only [] at h
    split at h <;> (try split at h) <;> injection h
  | sendQueries =>
    rw [step_sendQueries_dispatch s hcs] at h
    unfold stepSendQueries at h
    split at h <;> rename_i hr
    · injection h
    · injection h with hs
      exact ⟨hs.symm, rfl, hr⟩
  | analyzeResponse =>
    rw [step_analyzeResponse_dispatch s hcs] at h
    unfold stepAnalyzeResponse at h
    split at h
    · injection h
    · split at h
      · simp only [] at h; split at h <;> (try split at h) <;> injection h
      · split at h
        · injection h
        · split at h
          · split at h <;> (try split at h) <;> injection h
          · split at h
            · injection h
            · split at h
              · injection h
              · split at h
                · injection h
                · split at h <;> injection h

theorem resolve_loop_paused (fuel : Nat) (s s' : State S C NS RR)
    (h : resolve.loop s fuel = .ok (.paused s')) :
    s'.currentStep = .sendQueries ∧ s'.lastResponse = none := by
  induction fuel generalizing s with
  | zero => exact absurd h (by simp [resolve.loop])
  | succ n ih =>
    unfold resolve.loop at h
    split at h <;> rename_i hstep
    · exact absurd (Except.ok.inj h) (by simp)
    · exact ih _ h
    · rename_i s₀
      obtain ⟨heq, hcs, hr⟩ := step_needsIO_inversion _ _ hstep
      have hps := Except.ok.inj h
      injection hps with hs
      rw [← hs, heq]
      exact ⟨hcs, hr⟩
    · exact absurd h (by simp)

theorem step_sendQueries_needsIO (s : State S C NS RR)
    (h : s.lastResponse = none) :
    stepSendQueries s = .needsIO s := by
  unfold stepSendQueries; simp [h]

theorem step_seq_checkAnswer (s : State S C NS RR) (h : s.currentStep = .checkAnswer) :
    (∃ s', step s = .goto .findServers s') ∨ (∃ r st, step s = .answer r st)
      ∨ step s = .error "cname chain too long" := by
  simp only [step, h]; unfold stepCheckLocal
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inl ⟨_, rfl⟩
    · split
      · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      · split
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inr rfl)

theorem step_seq_findServers (s : State S C NS RR) (h : s.currentStep = .findServers) :
    ∃ nextStep s', step s = .goto nextStep s' := by
  simp only [step, h]
  unfold stepFindServers; dsimp only []
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

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

theorem answersQueryB_of_isEmpty {resp : Format}
    (h : resp.answer.isEmpty = true) : answersQueryB (RR := RR) resp = false := by
  have hemp : resp.answer = #[] := by simpa using h
  unfold answersQueryB
  split
  · unfold hasRRTypeIn; rw [hemp]; simp
  · rfl

theorem answer_isEmpty_false_of_answersQueryB {resp : Format}
    (h : answersQueryB (RR := RR) resp = true) : resp.answer.isEmpty = false := by
  unfold answersQueryB at h
  split at h
  · exact isEmpty_false_of_any (by unfold hasRRTypeIn at h; exact h)
  · simp at h

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
        ·
          injection h
        ·
          injection h
        ·
          split at h <;>
            (obtain ⟨h1, _⟩ := StepResult.goto.inj h; subst h1
             exact .seq_checkAnswer_findServers)
        ·
          injection h
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
      ·
        simp only [] at h
        split at h
        · injection h
        split at h
        · injection h
        injection h with h1 _; subst h1

        refine .cname resp ?_
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
        ·
          injection h with h1 _; subst h1
          exact .serverFailure resp (guard_serverFailure_of_test hsf)
        · split at h <;> rename_i h4b
          ·
            have hpos : resp.authority.size > 0 := by
              cases hb : resp.authority.isEmpty with
              | false => exact size_pos_of_isEmpty_false hb
              | true => rw [hb] at h4b; simp at h4b
            split at h <;> (try dsimp only [] at h) <;> (try split at h) <;>
              first
                | (injection h with h1 _; subst h1; exact .delegation resp hpos)
                | injection h
          ·
            split at h
            · dsimp only [] at h; injection h
            · split at h
              · injection h
              · split at h
                · injection h
                · split at h
                  · injection h
                  · injection h

theorem step_analyzeResponse_coverage (s : State S C NS RR) (resp : Format)
    (hr : s.lastResponse = some resp) :
    stepAnalyzeResponse s ≠ .error "unhandled response type" := by
  intro h
  unfold stepAnalyzeResponse at h
  simp only [hr] at h
  split at h
  ·
    split at h
    · injection h
    · split at h
      · injection h with hmsg; exact absurd hmsg (by decide)
      · injection h
  · split at h <;> rename_i hsf
    ·
      injection h
    · split at h <;> rename_i h4b
      ·
        split at h <;> (try split at h) <;>
          first
            | (injection h with hmsg; exact absurd hmsg (by decide))
            | injection h
      · split at h <;> rename_i haqB
        ·
          simp at h
        · split at h <;> rename_i h4a
          ·
            injection h
          · split at h <;> rename_i hnodata
            · injection h
            · split at h <;> rename_i htc
              · injection h
              ·

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
                rw [haq, hnef, hans] at h4b
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

theorem step_cname_chase (s : State S C NS RR) (resp : Format) (c : ByteArray)
    (hr : s.lastResponse = some resp)
    (hc : cnameToChase (RR := RR) resp = some c)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v c)) = false) :
    ∃ s', stepAnalyzeResponse s = .goto .checkAnswer s' ∧
      s'.resources.sname = c ∧
      s'.cnameChain = prependCnameLink (RR := RR) s.cnameChain resp.answer := by
  unfold stepAnalyzeResponse
  simp only [hr, hc, htc, hnrev, Bool.false_eq_true, if_false]
  exact ⟨_, rfl, rfl, rfl⟩

/-- **The state does not put `resp`'s CNAME chase in a loop** — the network-hop companion of
    `localAnswer`'s cache-hop guard. If `resp` carries a CNAME (`cnameToChase = some c`), its canonical
    name `c` has not already been visited in this chase (the original query name plus every prior
    target, `cnameChaseVisited`). Vacuously true for non-CNAME responses. RFC 1034 §3.6.2: a resolver
    detects CNAME loops rather than following them forever, so `stepAnalyzeResponse` transitions to
    `checkAnswer` exactly for loop-free states (and fails a genuine loop). -/
def cnameChaseLoopFree (s : State S C NS RR) (resp : Format) : Prop :=
  ∀ c, cnameToChase (RR := RR) resp = some c →
    ((cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v c)) = false

/-- **`resp`'s CNAME chase is not truncation-blocked.** If `resp` carries a chaseable CNAME
    (`cnameToChase = some c`), it is not truncated (tc=0). A truncated (tc=1) payload is possibly
    incomplete (RFC 1035 §4.1.1), so the impl DELIVERS it (`.answer (finalizeAnswer s resp)`) rather
    than chasing a CNAME read out of partial data — the chase transition to `checkAnswer` only fires
    for untruncated responses. Vacuously true for non-CNAME responses. -/
def cnameChaseUntruncated (resp : Format) : Prop :=
  ∀ c, cnameToChase (RR := RR) resp = some c → (resp.header.tc == 1) = false

def implTransition (resp : Format) : Option AlgorithmStep → Prop
  | some tgt => ∀ s : State S C NS RR, s.lastResponse = some resp →
      cnameChaseLoopFree (S := S) (C := C) (NS := NS) (RR := RR) s resp →
      cnameChaseUntruncated (RR := RR) resp →
      ∃ s', stepAnalyzeResponse s = .goto tgt s'
  | none => ∀ s : State S C NS RR, s.lastResponse = some resp →
      ∃ r st, stepAnalyzeResponse s = .answer r st

private theorem cnameToChase_none_of_not_guard {resp : Format}
    (hg : ¬ guardRefined_cname (answersQueryB (RR := RR))
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

theorem impl_obligation_cname :
    obligation_cname (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg _ha _hb _hd s hr hlf htc
  obtain ⟨hcn, haq⟩ := hg
  obtain ⟨c, hc⟩ := extractCname_some_of_cname (RR := RR) hcn
  have hchase : cnameToChase (RR := RR) resp = some c := by
    unfold cnameToChase
    rw [haq]
    simpa using hc
  obtain ⟨s', hs, _, _⟩ := step_cname_chase s resp c hr hchase (htc c hchase) (hlf c hchase)
  exact ⟨s', hs⟩

theorem impl_obligation_serverFailure :
    obligation_serverFailure (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg ha _hb hc s hr _hlf _htc

  have haq : answersQueryB (RR := RR) resp = false :=
    bool_eq_false_of_ne_true (fun h => ha (Or.inl h))
  have hchase := cnameToChase_none_of_not_guard (RR := RR) hc haq

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
  intro resp hg ha hc hd s hr _hlf _htc
  unfold guardRefined_delegation at hg
  obtain ⟨hgb, hans, haa, hrc, hsoa⟩ := hg
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
      && resp.answer.isEmpty
      && !resp.authority.isEmpty) = true := by
    rw [haq, hne, hans, hauth]; rfl
  unfold stepAnalyzeResponse
  simp only [hr, hchase, hsf, hcond, hgb, haa, hrc, hsoa, Bool.not_false,
    Bool.and_true, Bool.true_and, Bool.and_self, if_true]
  exact ⟨_, rfl⟩

theorem impl_obligation_answerOrNameError :
    obligation_answerOrNameError (answersQueryB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg _hb hc hd s hr
  have hsf := test4d_false_of_not_guard (RR := RR) hd

  have hchase : cnameToChase (RR := RR) resp = none := by
    cases haq : answersQueryB (RR := RR) resp with
    | true => unfold cnameToChase; rw [haq]; rfl
    | false => exact cnameToChase_none_of_not_guard (RR := RR) hc haq

  have h4a : (!resp.answer.isEmpty || resp.header.rcode == Rcode.nameError) = true := by
    rcases hg with haq | hne
    · rw [answer_isEmpty_false_of_answersQueryB (RR := RR) haq]; rfl
    · rw [rcode_beq_of_eq hne]
      simp

  have h4b : (!answersQueryB (RR := RR) resp
      && !(resp.header.rcode == Rcode.nameError)
      && resp.answer.isEmpty
      && !resp.authority.isEmpty) = false := by
    rcases hg with haq | hne
    · rw [haq]; rfl
    · rw [rcode_beq_of_eq hne]
      simp
  unfold stepAnalyzeResponse
  simp only [hr, hchase, hsf, h4b, h4a]

  cases haq : answersQueryB (RR := RR) resp with
  | true => simp only [haq, if_true]; exact ⟨_, _, rfl⟩
  | false => simp only [haq, Bool.false_eq_true, if_false]; exact ⟨_, _, rfl⟩

def answerInLocal (s : State S C NS RR) : Prop :=
  ∃ q qu, s.lastQuery = some q ∧ q.question[0]? = some qu ∧
    ((NegativeCacheSpec.retrieveNegative s.resources.cache
        s.resources.sname qu.qtype qu.qclass s.now).isSome
     ∨ (TrustworthinessSpec.answers s.resources.cache
        s.resources.sname qu.qtype qu.qclass s.now : Array RR).isEmpty = false)

theorem impl_obligation_checkAnswer :
    obligation_checkAnswer (State S C NS RR)
      (answerInLocal)
      (fun s => ∃ r st, stepCheckLocal s = .answer r st) := by
  intro s hloc
  obtain ⟨q, qu, hq, hqu, hcase⟩ := hloc
  unfold stepCheckLocal
  simp only [hq, hqu]
  have h8 : (8 : Nat) = 7 + 1 := rfl
  rw [h8]

  cases hneg : NegativeCacheSpec.retrieveNegative s.resources.cache
      s.resources.sname qu.qtype qu.qclass s.now with
  | some rc =>
    have hla : localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now (7 + 1) s.resources.sname s.cnameChain
        (cnameChaseVisited (RR := RR) qu.qname s.cnameChain)
        = .negative rc (NegativeAuthoritySpec.authoritySection s.resources.cache
            s.resources.sname qu.qtype qu.qclass s.now) s.cnameChain := by
      unfold localAnswer
      rw [hneg]
    rw [hla]
    exact ⟨_, _, rfl⟩
  | none =>
    rcases hcase with hns | hpos
    · rw [hneg] at hns; exact absurd hns (by simp)
    · have hla : localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
          s.now (7 + 1) s.resources.sname s.cnameChain
          (cnameChaseVisited (RR := RR) qu.qname s.cnameChain)
          = .answerHit s.resources.sname s.cnameChain
              (TrustworthinessSpec.answers s.resources.cache s.resources.sname
                qu.qtype qu.qclass s.now) := by
        unfold localAnswer
        rw [hneg]
        dsimp only []
        rw [hpos]
        simp
      rw [hla]
      exact ⟨_, _, rfl⟩

private theorem optRcode_eq_of_beq {a : Option Rcode}
    (h : (a == some Rcode.nameError) = true) : a = some Rcode.nameError := by
  cases a with
  | none => exact absurd h (by decide)
  | some rc => cases rc <;> first | rfl | exact absurd h (by decide)

theorem localAnswer_nameError_semantics (qtype qclass : BitVec 16)
    (now : UInt32) (fuel : Nat) (chain visited : Array ByteArray) :
    rcode_nameError_semantics (C × ByteArray)
      (fun p => !(NegativeCacheSpec.retrieveNegative p.1 p.2 qtype qclass now
        == some Rcode.nameError))
      (fun p => localAnswer (RR := RR) p.1 qtype qclass now (fuel + 1) p.2 chain visited
        = .negative Rcode.nameError
            (NegativeAuthoritySpec.authoritySection p.1 p.2 qtype qclass now) chain) := by
  intro p h
  have hb : (NegativeCacheSpec.retrieveNegative p.1 p.2 qtype qclass now
      == some Rcode.nameError) = true := by
    simpa using h
  have heq := optRcode_eq_of_beq hb
  unfold localAnswer
  rw [heq]

theorem resolve_loop_star (fuel : Nat) (s s' : State S C NS RR)
    (h : resolve.loop s fuel = .ok (.paused s')) :
    StepSpecStar s.currentStep s'.currentStep := by
  induction fuel generalizing s with
  | zero => exact absurd h (by simp [resolve.loop])
  | succ n ih =>
    unfold resolve.loop at h
    split at h <;> rename_i hstep
    · exact absurd (Except.ok.inj h) (by simp)
    · rename_i nextStep s₀
      exact .trans _ _ _ (step_implies_spec s nextStep s₀ hstep) (ih _ h)
    · rename_i s₀
      obtain ⟨heq, _, _⟩ := step_needsIO_inversion _ _ hstep
      have hps := Except.ok.inj h
      injection hps with hs
      rw [← hs, heq]
      exact .refl _
    · exact absurd h (by simp)

theorem resolve_loop_done (fuel : Nat) (s : State S C NS RR) (r : Format)
    (stF : State S C NS RR)
    (h : resolve.loop s fuel = .ok (.done r stF)) :
    ∃ s₀ : State S C NS RR,
      StepSpecStar s.currentStep s₀.currentStep ∧ step s₀ = .answer r stF := by
  induction fuel generalizing s with
  | zero => exact absurd h (by simp [resolve.loop])
  | succ n ih =>
    unfold resolve.loop at h
    split at h <;> rename_i hstep
    · rename_i resp st'
      have hd : ResolveYield.done (S := S) (C := C) (NS := NS) (RR := RR) resp st'
          = .done r stF := Except.ok.inj h
      injection hd with hresp hst
      exact ⟨s, .refl _, hresp ▸ hst ▸ hstep⟩
    · rename_i nextStep s₀
      obtain ⟨s₁, hstar, hans⟩ := ih _ h
      exact ⟨s₁, .trans _ _ _ (step_implies_spec s nextStep s₀ hstep) hstar, hans⟩
    · exact absurd (Except.ok.inj h) (by simp)
    · exact absurd h (by simp)

end VeriDNS.Proof.Resolver
