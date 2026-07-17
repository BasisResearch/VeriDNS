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

/-- The glue set `stepFindServers` derives from a candidate NS name set by reading
    each name's cached A records out of `s.resources.cache`.  This mirrors the local
    `let glue := …` inside `stepFindServers` exactly, so a hypothesis phrased over
    `rootCutGlue` is a hypothesis about the real implementation branch. -/
def rootCutGlue (s : State S C NS RR) (nsNames : Array ByteArray)
    : Array (ByteArray × BitVec 32) :=
  let aType : BitVec 16 := BitVec.ofNat 16 1
  let inClass : BitVec 16 := BitVec.ofNat 16 1
  nsNames.flatMap fun nsName =>
    let aRRs : Array RR := CacheSpec.lookupTopCred s.resources.cache nsName aType inClass s.now
    aRRs.filterMap fun rr =>
      let rd := RRParse.rrRdata rr
      if rd.size == 4 then
        let addr : BitVec 32 :=
          (rd.data[0]!.toBitVec.setWidth 32 <<< 24) |||
          (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
          (rd.data[2]!.toBitVec.setWidth 32 <<< 8) |||
          rd.data[3]!.toBitVec.setWidth 32
        some (nsName, addr)
      else none

/-- **Finding 015 — root-cut SBELT fallback, as a theorem.**

    RFC 1034 §5.3.3: when the resolver's cache offers an NS RRset for a zone but no
    usable addresses (all names are glueless), it must fall back to SBELT rather than
    query the (address-less) NS set.  The pathological instance that finding 015 hit is
    the *root cut* (`mc = 0`): an address-less root NS RRset shadowed SBELT, leaving the
    resolver with an unqueryable SLIST that made it re-derive the same address-less set
    every `.findServers` visit — a permanent SERVFAIL loop and a remote-DoS vector.

    This theorem pins the fix behaviourally: at the root cut (`walkNs = some (nsNames, 0)`,
    search not yet closer, glue empty), `stepFindServers` installs `s.resources.sbelt`
    as the new SLIST verbatim.  So the next SLIST is exactly SBELT — no longer the
    address-less set — and forward progress is restored whenever SBELT is non-empty
    (see `stepFindServers_rootCut_sbelt_progress`).  A regression that dropped the
    `mc == 0` guard, or that installed the address-less `setUpAddresses` set here,
    would break this equation and fail to compile. -/
theorem stepFindServers_rootCut_sbelt_fallback (s : State S C NS RR)
    {nsNames : Array ByteArray}
    (hwalk : stepFindServers.walkNs (C := C) (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = some (nsNames, 0))
    (hcloser : (!SlistFromNameSpec.searchFails (NS := NS) s.resources.slist
        && decide (0 < SlistFromNameSpec.matchCount (NS := NS) s.resources.slist)) = false)
    (hglue : rootCutGlue (S := S) (C := C) (NS := NS) (RR := RR) s nsNames = #[]) :
    stepFindServers s
      = .goto .sendQueries
          { s with resources := { s.resources with slist := s.resources.sbelt } } := by
  unfold stepFindServers
  dsimp only []
  rw [hwalk]
  dsimp only []
  -- `currentCloser 0` is exactly `hcloser`, with `walkMc = 0 < mc` decided.
  have hcc : (!SlistFromNameSpec.searchFails (NS := NS) s.resources.slist
      && (0 < SlistFromNameSpec.matchCount (NS := NS) s.resources.slist)) = false := by
    simpa using hcloser
  simp only [hcc, Bool.decide_and, if_false]
  -- Now the two branches on `glue.isEmpty && mc == 0`; `mc = 0` and glue = #[] pick the first.
  have hge : (rootCutGlue (S := S) (C := C) (NS := NS) (RR := RR) s nsNames).isEmpty = true := by
    rw [hglue]; rfl
  show (if (rootCutGlue (S := S) (C := C) (NS := NS) (RR := RR) s nsNames).isEmpty
        && ((0 : Nat) == 0) then _ else _) = _
  rw [hge]
  simp

/-- **Forward-progress corollary of the root-cut SBELT fallback.**

    The behavioural crux of finding 015: after the fallback installs SBELT, the resolver's
    SLIST is *queryable* (its search does not fail) whenever SBELT itself is non-empty —
    i.e. carries at least one belt server (RFC 1034 §5.3.3, the SBELT invariant that the
    resolver always keeps root servers around).  Because `.sendQueries` then transmits to a
    real belt server instead of re-deriving the same address-less NS set, the resolver
    escapes the SERVFAIL loop.  `searchFails (NS := NS) slist = false` is precisely the
    negation of the "SLIST search failed" condition the `.findServers` re-entry tests, so
    a non-search-failing SLIST is the concrete no-starvation witness. -/
theorem stepFindServers_rootCut_sbelt_progress (s : State S C NS RR)
    {nsNames : Array ByteArray}
    (hwalk : stepFindServers.walkNs (C := C) (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = some (nsNames, 0))
    (hcloser : (!SlistFromNameSpec.searchFails (NS := NS) s.resources.slist
        && decide (0 < SlistFromNameSpec.matchCount (NS := NS) s.resources.slist)) = false)
    (hglue : rootCutGlue (S := S) (C := C) (NS := NS) (RR := RR) s nsNames = #[])
    (hbelt : SlistFromNameSpec.searchFails (NS := NS) s.resources.sbelt = false) :
    ∃ s', stepFindServers s = .goto .sendQueries s'
      ∧ SlistFromNameSpec.searchFails (NS := NS) s'.resources.slist = false := by
  refine ⟨_, stepFindServers_rootCut_sbelt_fallback s hwalk hcloser hglue, ?_⟩
  -- The installed SLIST *is* SBELT, so its search does not fail.
  exact hbelt

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
    ∃ qu, resp.question[0]? = some qu
      ∧ extractCname (RR := RR) qu.qname resp.answer = some c := by
  unfold cnameToChase at h
  split at h
  · simp at h
  · split at h
    next qu hq => exact ⟨qu, hq, h⟩
    next => simp at h

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
    split at h <;> (try split at h) <;> (try split at h) <;> injection h
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
  split <;> (try split) <;> (try split) <;> exact ⟨_, _, rfl⟩

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

theorem extractCname_none_of_no_cname {sname : ByteArray} {ans : Array ByteArray}
    (h : hasRRTypeIn (RR := RR) ans 5 = false) :
    extractCname (RR := RR) sname ans = none := by
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
    simp only [hpr, hpf, Bool.false_and, Bool.false_eq_true, if_false]

theorem hasRRTypeIn_of_extractCname_some {sname : ByteArray} {ans : Array ByteArray}
    {c : ByteArray} (h : extractCname (RR := RR) sname ans = some c) :
    hasRRTypeIn (RR := RR) ans 5 = true := by
  unfold extractCname at h
  obtain ⟨bytes, hmem, hb⟩ := Array.exists_of_findSome?_eq_some h
  unfold hasRRTypeIn
  rw [Array.any_eq_true]
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hmem
  refine ⟨i, hi, ?_⟩
  cases hpr : RRParse.parseRaw (RR := RR) ans[i] with
  | none => rw [hpr] at hb; simp at hb
  | some rr =>
    simp only [hpr] at hb
    split at hb
    next hcond => exact (Bool.and_eq_true _ _ |>.mp hcond).1
    next => simp at hb

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

private theorem guard_serverFailure_of_test {resp : Format} (entitled : Format → Bool)
    (h : (resp.header.rcode == Rcode.serverFailure || !classifiableB resp) = true) :
    guard_serverFailure entitled resp := by
  rw [Bool.or_eq_true] at h
  rcases h with hsf | hnc
  · exact Or.inl (rcode_eq_of_beq hsf)
  · have hcl : classifiableB resp = false := by simpa using hnc
    obtain ⟨hans, hne, hauth, _, _⟩ := classifiable_false_facts hcl
    have hans0 := size_eq_zero_of_isEmpty hans
    have hauth0 := size_eq_zero_of_isEmpty hauth
    refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
    · rintro (hpos | hrc)
      · omega
      · exact rcode_ne_of_beq_false hne hrc
    · intro hpos
      have hsz : resp.authority.size > 0 := hpos
      omega
    · intro hpos
      have hsz : resp.answer.size > 0 := hpos
      omega

private theorem guard_serverFailure_of_lame {resp : Format} (entitled : Format → Bool)
    (hnoerr : (resp.header.rcode == Rcode.noError) = false)
    (hne : (resp.header.rcode == Rcode.nameError) = false) :
    guard_serverFailure entitled resp :=
  Or.inr (Or.inr (Or.inl ⟨rcode_ne_of_beq_false hnoerr, rcode_ne_of_beq_false hne⟩))

/-- RFC 1034 §4.3.2.d: an empty-answer response that is not an NXDOMAIN is
    "bizarre contents" and justifies a retry — the DIRECTION-row strengthening. -/
private theorem guard_serverFailure_of_bizarre {resp : Format} (entitled : Format → Bool)
    (hemp : resp.answer.isEmpty = true)
    (hne : (resp.header.rcode == Rcode.nameError) = false) :
    guard_serverFailure entitled resp :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨hemp, rcode_ne_of_beq_false hne⟩)))

/-- **Off-owner strengthening (2026-07-15, findings 036 / off-owner-A).**  A
    response with no ENTITLED answer record that is not delivered by the guarded
    NXDOMAIN arm (`nameError && answer.isEmpty`) is *foreign* — either a non-empty
    off-owner answer, or a contradictory non-empty `nameError`.  It scrubs to
    empty at delivery, so it is bizarre contents and justifies a retry — never an
    accepted-then-scrubbed spurious NODATA. -/
private theorem guard_serverFailure_of_offowner {resp : Format} {entitled : Format → Bool}
    (hent : entitled resp = false)
    (hguard : (resp.header.rcode == Rcode.nameError && resp.answer.isEmpty) = false) :
    guard_serverFailure entitled resp := by
  unfold guard_serverFailure
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hent, ?_⟩)))
  by_cases hne : (resp.header.rcode == Rcode.nameError) = true
  · -- rcode = nameError: the guard being false forces a non-empty answer.
    right
    rw [hne, Bool.true_and] at hguard
    have hne0 : resp.answer.isEmpty = false := by simpa using hguard
    exact size_pos_of_isEmpty_false hne0
  · left
    exact rcode_ne_of_beq_false (by simpa using hne)

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
    split at h <;> (try split at h) <;> (try split at h) <;>
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
        obtain ⟨qu, _, hext⟩ := cnameToChase_extractCname hcn
        cases Nat.eq_zero_or_pos resp.answer.size with
        | inl h0 =>
          have hemp : resp.answer = #[] := Array.size_eq_zero_iff.mp h0
          rw [hemp] at hext
          have hnone : extractCname (RR := RR) qu.qname (#[] : Array ByteArray) = none := rfl
          rw [hnone] at hext
          simp at hext
        | inr hpos => exact hpos
      · split at h <;> rename_i hsf
        ·
          injection h with h1 _; subst h1
          exact .serverFailure (entitledAnswerB (RR := RR)) resp
            (guard_serverFailure_of_test _ hsf)
        · split at h <;> rename_i h4b
          ·
            have hpos : resp.authority.size > 0 := by
              cases hb : resp.authority.isEmpty with
              | false => exact size_pos_of_isEmpty_false hb
              | true => rw [hb] at h4b; simp at h4b
            have h4b' := h4b
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at h4b'
            obtain ⟨⟨⟨haq, hne⟩, hans⟩, hauth⟩ := h4b'
            split at h
            · dsimp only [] at h
              injection h with h1 _; subst h1
              exact .delegation resp hpos
            · split at h <;> rename_i hnodata
              · injection h
              ·
                -- B.3: empty-answer, non-referral, no valid SOA negative proof.
                -- RFC 1034 §4.3.2.d bizarre contents ⇒ retry (serverFailure edge).
                injection h with h1 _; subst h1
                exact .serverFailure (entitledAnswerB (RR := RR)) resp
                  (guard_serverFailure_of_bizarre _ hans hne)
          ·
            -- answer tail: entitled / nameError / SOA-nodata / tc ⇒ `.answer`
            -- (goto impossible, `injection h`); the final else is the retry.
            split at h <;> rename_i hent
            · dsimp only [] at h; injection h
            · split at h <;> rename_i hne
              · injection h
              · split at h <;> rename_i hsoa
                · injection h
                · split at h <;> rename_i htc
                  · injection h
                  · -- else: not entitled, not NXDOMAIN, no SOA proof, not truncated.
                    -- Either an empty NOERROR without SOA (041/045) or a NON-EMPTY
                    -- FOREIGN answer (036 / off-owner-A): a response carrying no
                    -- entitled answer that is not an NXDOMAIN is bizarre contents
                    -- ⇒ retry (findings 036 / off-owner-A).
                    injection h with h1 _; subst h1
                    exact .serverFailure (entitledAnswerB (RR := RR)) resp
                      (guard_serverFailure_of_offowner (bool_eq_false_of_ne_true hent)
                        (bool_eq_false_of_ne_true hne))

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
      · -- The answer tail: every arm is `.answer` or `.goto .sendQueries` —
        -- the "unhandled response type" error branch was DELETED (a foreign
        -- answer now retries), so this error string is unreachable here.
        split at h <;> rename_i haqB
        ·
          simp at h
        · split at h <;> rename_i h4a
          ·
            injection h
          · split at h <;> rename_i hnodata
            · injection h
            · split at h <;> rename_i htc
              · injection h
              · injection h

theorem step_cname_chase (s : State S C NS RR) (resp : Format) (c : ByteArray)
    (hr : s.lastResponse = some resp)
    (hc : cnameToChase (RR := RR) resp = some c)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v c)) = false) :
    ∃ s', stepAnalyzeResponse s = .goto .checkAnswer s' ∧
      s'.resources.sname = c ∧
      s'.cnameChain = prependCnameLink (RR := RR) s.cnameChain resp := by
  unfold stepAnalyzeResponse
  simp only [hr, hc, htc, hnrev, Bool.false_eq_true, if_false]
  exact ⟨_, rfl, rfl, rfl⟩

def cnameChaseLoopFree (s : State S C NS RR) (resp : Format) : Prop :=
  ∀ c, cnameToChase (RR := RR) resp = some c →
    ((cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v c)) = false

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
    (hg : ¬ guardRefined_cname (entitledAnswerB (RR := RR))
      (hasRRTypeIn (RR := RR)) classifiableB (cnameToChase (RR := RR)) resp) :
    cnameToChase (RR := RR) resp = none := by
  cases hb : cnameToChase (RR := RR) resp with
  | none => rfl
  | some c =>
    exfalso
    -- `cnameToChase = some` already forces `answersQueryB = false` (its guard),
    -- hence `entitledAnswerB = false` (entitled refines answersQuery).
    have haqb : answersQueryB (RR := RR) resp = false := by
      by_contra h
      have : answersQueryB (RR := RR) resp = true := by
        cases hh : answersQueryB (RR := RR) resp with
        | true => rfl
        | false => exact absurd hh h
      unfold cnameToChase at hb; rw [this] at hb; simp at hb
    have hent : entitledAnswerB (RR := RR) resp = false := by
      by_contra h
      have ht : entitledAnswerB (RR := RR) resp = true := by
        cases hh : entitledAnswerB (RR := RR) resp with
        | true => rfl
        | false => exact absurd hh h
      rw [answersQueryB_of_entitled (RR := RR) resp ht] at haqb; simp at haqb
    obtain ⟨qu, _, hext⟩ := cnameToChase_extractCname (RR := RR) hb
    exact hg ⟨hasRRTypeIn_of_extractCname_some (RR := RR) hext, hent, by rw [hb]; rfl⟩

private theorem test4d_false_of_not_guard {resp : Format}
    (hd : ¬ guardRefined_serverFailure (entitledAnswerB (RR := RR))
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
    obligation_cname (entitledAnswerB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB (cnameToChase (RR := RR))
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg _ha _hb _hd s hr hlf htc
  obtain ⟨_hcn, _haq, hsome⟩ := hg
  obtain ⟨c, hchase⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨s', hs, _, _⟩ := step_cname_chase s resp c hr hchase (htc c hchase) (hlf c hchase)
  exact ⟨s', hs⟩

theorem impl_obligation_serverFailure :
    obligation_serverFailure (entitledAnswerB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB (cnameToChase (RR := RR))
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg ha _hb hc s hr _hlf _htc

  have hchase := cnameToChase_none_of_not_guard (RR := RR) hc

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
    obligation_delegation (entitledAnswerB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB (cnameToChase (RR := RR))
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg ha hc hd s hr _hlf _htc
  unfold guardRefined_delegation at hg
  obtain ⟨hgb, hans, haa, hrc, hsoa⟩ := hg
  -- an empty answer (from the delegation guard) is never a type-matching answer
  have haq : answersQueryB (RR := RR) resp = false :=
    answersQueryB_of_isEmpty hans
  have hne : (resp.header.rcode == Rcode.nameError) = false :=
    rcode_beq_false_of_ne (fun h => ha (Or.inr ⟨h, hans⟩))
  have hsf := test4d_false_of_not_guard (RR := RR) hd
  have hchase := cnameToChase_none_of_not_guard (RR := RR) hc
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

/-- The answer-acceptance obligation instantiated with the ENTITLED-answer
    predicate `entitledAnswerB` (the 2026-07-15 off-owner tightening, findings
    036 / off-owner-A): a response answers the query only when it carries a
    record of the query type whose owner is on the CNAME chain rooted at the
    query name.  A purely-foreign answer (type-matching but off-owner) is NOT an
    answer — it scrubs to empty at delivery — so it is not accepted here. -/
theorem impl_obligation_answerOrNameError :
    obligation_answerOrNameError (entitledAnswerB (RR := RR)) (hasRRTypeIn (RR := RR))
      classifiableB (cnameToChase (RR := RR))
      (implTransition (S := S) (C := C) (NS := NS) (RR := RR)) := by
  intro resp hg _hb hc hd s hr
  have hsf := test4d_false_of_not_guard (RR := RR) hd

  -- The deliver guard now carries `answer.isEmpty` on the NXDOMAIN arm: a
  -- `nameError` that carries ANY answer record is contradictory and is retried,
  -- not delivered (findings 036 / off-owner-A).
  have hent_nameError : entitledAnswerB (RR := RR) resp = true
      ∨ ((resp.header.rcode == Rcode.nameError) = true ∧ resp.answer.isEmpty = true) := by
    rcases hg with hent | ⟨hne, hemp⟩
    · exact Or.inl hent
    · exact Or.inr ⟨rcode_beq_of_eq hne, hemp⟩

  have hchase : cnameToChase (RR := RR) resp = none :=
    cnameToChase_none_of_not_guard (RR := RR) hc

  -- The empty-answer B-block cannot fire: an entitled answer is non-empty; an
  -- NXDOMAIN fails the `¬nameError` conjunct.
  have h4b : (!answersQueryB (RR := RR) resp
      && !(resp.header.rcode == Rcode.nameError)
      && resp.answer.isEmpty
      && !resp.authority.isEmpty) = false := by
    rcases hent_nameError with hent | ⟨hne, _⟩
    · rw [answersQueryB_of_entitled (RR := RR) resp hent]; rfl
    · rw [hne]; simp
  unfold stepAnalyzeResponse
  simp only [hr, hchase, h4b]

  rcases hent_nameError with hent | ⟨hne, hemp⟩
  · rw [if_neg (by simp [hsf])]
    rw [if_neg (by simp)]
    simp only [hent, if_true]; exact ⟨_, _, rfl⟩
  · -- NXDOMAIN with no answer: entitled is false (empty answer), so the guarded
    -- nameError arm (`nameError && answer.isEmpty`) delivers.
    have hent : entitledAnswerB (RR := RR) resp = false := by
      cases hb : entitledAnswerB (RR := RR) resp with
      | false => rfl
      | true =>
        have := answersQueryB_of_entitled (RR := RR) resp hb
        rw [answersQueryB_of_isEmpty (RR := RR) hemp] at this; simp at this
    rw [if_neg (by simp [hsf])]
    rw [if_neg (by simp)]
    simp only [hent, Bool.false_eq_true, if_false, hne, hemp, Bool.and_true, if_true]
    exact ⟨_, _, rfl⟩

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



def fuelRank : AlgorithmStep → Option Format → Nat
  | .sendQueries, none => 1
  | .findServers, none => 2
  | .checkAnswer, none => 3
  | .analyzeResponse, _ => 4
  | .sendQueries, some _ => 5
  | .findServers, some _ => 6
  | .checkAnswer, some _ => 7

theorem fuelRank_pos (cs : AlgorithmStep) (lr : Option Format) : 1 ≤ fuelRank cs lr := by
  cases cs <;> cases lr <;> simp [fuelRank]

theorem fuelRank_le_seven (cs : AlgorithmStep) (lr : Option Format) : fuelRank cs lr ≤ 7 := by
  cases cs <;> cases lr <;> simp [fuelRank]

theorem stepCheckLocal_goto_resp (s : State S C NS RR) (next : AlgorithmStep)
    (s' : State S C NS RR) (h : stepCheckLocal s = .goto next s') :
    next = .findServers ∧ s'.lastResponse = s.lastResponse := by
  unfold stepCheckLocal at h
  split at h
  · obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2; exact ⟨rfl, rfl⟩
  · split at h
    · obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2; exact ⟨rfl, rfl⟩
    · split at h
      · injection h
      · injection h
      · split at h <;>
          (obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2; exact ⟨rfl, rfl⟩)
      · injection h

theorem stepFindServers_goto_resp (s : State S C NS RR) (next : AlgorithmStep)
    (s' : State S C NS RR) (h : stepFindServers s = .goto next s') :
    next = .sendQueries ∧ s'.lastResponse = s.lastResponse := by
  unfold stepFindServers at h; dsimp only [] at h
  split at h <;> (try split at h) <;> (try split at h) <;>
    (obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2; exact ⟨rfl, rfl⟩)

theorem stepSendQueries_goto_resp (s : State S C NS RR) (next : AlgorithmStep)
    (s' : State S C NS RR) (h : stepSendQueries s = .goto next s') :
    next = .analyzeResponse ∧ s' = s ∧ ∃ resp, s.lastResponse = some resp := by
  unfold stepSendQueries at h
  split at h
  · rename_i resp hr
    obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2
    exact ⟨rfl, rfl, resp, hr⟩
  · injection h

theorem stepAnalyzeResponse_goto_resp (s : State S C NS RR) (next : AlgorithmStep)
    (s' : State S C NS RR) (h : stepAnalyzeResponse s = .goto next s') :
    next ≠ .analyzeResponse ∧ s'.lastResponse = none := by
  unfold stepAnalyzeResponse at h
  split at h
  · injection h
  · split at h
    ·
      simp only [] at h
      split at h
      · injection h
      split at h
      · injection h
      obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2
      exact ⟨nofun, rfl⟩
    · split at h
      ·
        obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2
        exact ⟨nofun, rfl⟩
      · split at h
        · split at h
          ·
            dsimp only [] at h
            obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2
            exact ⟨nofun, rfl⟩
          · split at h
            · injection h
            ·
              obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2
              exact ⟨nofun, rfl⟩
        · split at h
          · dsimp only [] at h; injection h
          · split at h
            · injection h
            · split at h
              · injection h
              · split at h
                · injection h
                · obtain ⟨h1, h2⟩ := StepResult.goto.inj h; subst h1 h2
                  exact ⟨nofun, rfl⟩

theorem step_goto_fuelRank (s : State S C NS RR) (next : AlgorithmStep)
    (s' : State S C NS RR) (h : step s = .goto next s') :
    fuelRank next s'.lastResponse < fuelRank s.currentStep s.lastResponse := by
  cases hcs : s.currentStep with
  | checkAnswer =>
    rw [step_checkAnswer_dispatch s hcs] at h
    obtain ⟨h1, h2⟩ := stepCheckLocal_goto_resp s next s' h
    subst h1; rw [h2]
    cases s.lastResponse <;> simp [fuelRank]
  | findServers =>
    rw [step_findServers_dispatch s hcs] at h
    obtain ⟨h1, h2⟩ := stepFindServers_goto_resp s next s' h
    subst h1; rw [h2]
    cases s.lastResponse <;> simp [fuelRank]
  | sendQueries =>
    rw [step_sendQueries_dispatch s hcs] at h
    obtain ⟨h1, h2, resp, hr⟩ := stepSendQueries_goto_resp s next s' h
    subst h1 h2; rw [hr]
    simp [fuelRank]
  | analyzeResponse =>
    rw [step_analyzeResponse_dispatch s hcs] at h
    obtain ⟨h1, h2⟩ := stepAnalyzeResponse_goto_resp s next s' h
    rw [h2]
    cases next <;> first | exact absurd rfl h1 | (cases s.lastResponse <;> simp [fuelRank])

theorem step_error_ne_maxIterations (s : State S C NS RR) (msg : String)
    (h : step s = .error msg) : msg ≠ "resolver: max iterations" := by
  cases hcs : s.currentStep with
  | checkAnswer =>
    rw [step_checkAnswer_dispatch s hcs] at h
    unfold stepCheckLocal at h
    split at h
    · injection h
    · split at h
      · injection h
      · split at h
        · injection h
        · injection h
        · split at h <;> injection h
        · injection h with hmsg; subst hmsg; decide
  | findServers =>
    rw [step_findServers_dispatch s hcs] at h
    unfold stepFindServers at h; dsimp only [] at h
    split at h <;> (try split at h) <;> (try split at h) <;> injection h
  | sendQueries =>
    rw [step_sendQueries_dispatch s hcs] at h
    unfold stepSendQueries at h
    split at h <;> injection h
  | analyzeResponse =>
    rw [step_analyzeResponse_dispatch s hcs] at h
    unfold stepAnalyzeResponse at h
    split at h
    · injection h with hmsg; subst hmsg; decide
    · split at h
      · simp only [] at h
        split at h
        · injection h
        split at h
        · injection h with hmsg; subst hmsg; decide
        injection h
      · split at h
        · injection h
        · split at h
          · split at h
            · dsimp only [] at h; injection h
            · split at h <;> injection h
          · split at h
            · dsimp only [] at h; injection h
            · split at h
              · injection h
              · split at h
                · injection h
                · split at h
                  · injection h
                  · injection h

theorem loop_ne_maxIterations (n : Nat) (s : State S C NS RR)
    (h : fuelRank s.currentStep s.lastResponse ≤ n) :
    resolve.loop s n ≠ .error "resolver: max iterations" := by
  induction n generalizing s with
  | zero =>
    intro _
    have := fuelRank_pos s.currentStep s.lastResponse
    omega
  | succ n ih =>
    unfold resolve.loop
    split <;> rename_i hstep
    · nofun
    · rename_i nextStep s₀
      exact ih _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
        (step_goto_fuelRank s nextStep s₀ hstep) h))
    · nofun
    · rename_i msg
      intro hc
      injection hc with hmsg
      exact step_error_ne_maxIterations s msg hstep hmsg

theorem resolve_ne_maxIterations (query : Format) (sbelt : S) (fuel : Nat) (now : UInt32)
    (initCache : C) (hfuel : 3 ≤ fuel) :
    resolve (NS := NS) (RR := RR) query sbelt fuel now initCache
      ≠ .error "resolver: max iterations" := by
  unfold resolve
  exact loop_ne_maxIterations fuel (initFromQuery query sbelt now initCache)
    (Nat.le_trans (by simp [initFromQuery, fuelRank]) hfuel)

theorem resume_ne_maxIterations (s : State S C NS RR) (resp : Format) (fuel : Nat)
    (hfuel : 7 ≤ fuel) :
    resume s resp fuel ≠ .error "resolver: max iterations" := by
  unfold resume
  exact loop_ne_maxIterations fuel _ (Nat.le_trans (fuelRank_le_seven _ _) hfuel)

end VeriDNS.Proof.Resolver
