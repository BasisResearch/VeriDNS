import VeriDNS.Spec.Resilience

open VeriDNS.Spec

/-! SPOT (round 4, NEW): the RFC 5452 §9.1 "response query NAME must match the
    request" obligation is SELF-REFERENTIAL and therefore blind to whether the
    implementation actually compares owner names.

    `accept_match_obligation` (Proof/Server.lean:261) instantiates
    `querymatchingrules_match_obligation` with
        accepted r      := (acceptExchanged …).isSome && (acceptResponse …).isSome
        queryName r     := questionMatches resp.question sent.question
    and `acceptResponse` accepts iff `id-match && questionMatches …`.  So the
    "name matched" WITNESS the RFC obligation demands is the SAME `questionMatches`
    already inside the acceptance gate.  The obligation `accepted r → queryName r`
    is then a tautology REGARDLESS of what `questionMatches`/`nameEqCI` computes.

    This is DISTINCT from the known mutant M-acceptResponse-questionMatches-drop
    (which *removes* questionMatches from the gate and IS caught).  Here we keep
    questionMatches in the gate but let it SKIP the name comparison — the gate and
    the witness move in lockstep, so nothing is caught. -/

/-- Faithful abstraction of `accept_match_obligation`'s shape: `accepted` is the
    conjunction of every per-attribute gate, and `queryName`/`queryClassAndType`
    are one of those very gates (`qm`).  The obligation holds for ANY `qm` — in
    particular a `qm` that ignores the owner name entirely. -/
theorem obligation_holds_for_ANY_questionMatches
    (ρ : Type) (src dst dport idM qm : ρ → Bool) :
    querymatchingrules_match_obligation ρ
      (fun r => src r && dst r && dport r && idM r && qm r)  -- accepted
      src dst dport idM
      qm            -- queryName      := questionMatches  (the self-reference)
      qm := by      -- queryClassAndType := questionMatches
  intro r hacc
  simp only [Bool.and_eq_true] at hacc
  obtain ⟨⟨⟨⟨hs, hd⟩, hp⟩, hi⟩, hq⟩ := hacc
  exact ⟨⟨⟨⟨⟨hs, hd⟩, hp⟩, hi⟩, hq⟩, hq⟩

/-- NONSENSE instantiation: `qm := fun _ => true` models a `questionMatches` that
    NEVER checks the owner name (accepts a response whose question is a DIFFERENT
    name).  RFC 5452 §9.1 says the name MUST match — yet the obligation still proves. -/
theorem name_blind_gate_still_conforms
    (ρ : Type) (src dst dport idM : ρ → Bool) :
    querymatchingrules_match_obligation ρ
      (fun r => src r && dst r && dport r && idM r && (fun _ => true) r)
      src dst dport idM (fun _ => true) (fun _ => true) :=
  obligation_holds_for_ANY_questionMatches ρ src dst dport idM (fun _ => true)

/-! CONTRAST — a NON-vacuous spec states `queryName` as an INDEPENDENT predicate
    (real byte/name equality of the two question owner names), NOT reusing the
    acceptance component.  Then a name-blind gate FAILS to conform, which is the
    genuine semantic catch. -/
theorem independent_namematch_is_NOT_vacuous :
    ¬ (∀ (ρ : Type) (src dst dport idM realNameEq : ρ → Bool),
        querymatchingrules_match_obligation ρ
          (fun r => src r && dst r && dport r && idM r && (fun _ => true) r)  -- name-BLIND accept
          src dst dport idM realNameEq (fun _ => true)) := by  -- but demand REAL name eq
  intro h
  -- ρ := Unit, all gates true except realNameEq := false: accepted holds, name-eq fails.
  have := h Unit (fun _ => true) (fun _ => true) (fun _ => true) (fun _ => true)
              (fun _ => false) ()
  simp at this
