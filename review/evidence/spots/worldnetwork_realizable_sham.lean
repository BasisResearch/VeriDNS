/-! SPOT (round 5, NEW, thread d-deepened): the WorldNetwork "realizability"
    theorem `answer_model_realizable` (Proof/WorldNetwork.lean:330) is cited — by
    the docstrings at Refinement.lean:9690-9698 and WorldNetwork.lean:324-329 — as
    evidence that the network disjunct of `resolveWithIO_simulates` is
    "realizable, not merely assumed."  It is not.

    STRUCTURAL FACTS (from source, no SPOT needed):
      * `resolveWithIO_simulates` (Refinement.lean:9700) fixes `net ns` as
        ∀-BOUND PARAMETERS; its network disjunct demands `HasVerdict net ns … v`
        for THAT given net.
      * `answer_model_realizable` (WorldNetwork.lean:330,342-343) concludes
        `HasVerdict (answerNet addr q.qname A q.qclass) allUp … v` — a network and
        NetState of its OWN construction, built FROM the delivered answer `A`.
      * The two never unify (`answerNet …` is not the arbitrary `net`), and
        `resolveWithIO_simulates` is APPLIED NOWHERE (grep: only docstrings), so
        the realizability lemma is never composed into it.

    The schematic below reproduces the exact logical gap: "for every answer there
    EXISTS a model network that justifies it" is a tautology (pick the network that
    parrots the answer) and is strictly weaker than soundness ("the answer agrees
    with the GIVEN network"). A poisoned answer is equally "realizable." -/

-- Abstract stand-ins.  `Net` = model network, `Resp` = delivered response.
variable (Net Resp : Type)

/-- Faithful shape of `answer_model_realizable`: it hands back a network it BUILDS
    from the response (`fabricate`), for which agreement holds by construction. -/
theorem realizable_shape
    (HasVerdict : Net → Resp → Prop)
    (fabricate : Resp → Net)
    (fab_ok : ∀ v, HasVerdict (fabricate v) v) :
    ∀ v : Resp, ∃ net : Net, HasVerdict net v :=
  fun v => ⟨fabricate v, fab_ok v⟩

/-- Weaponization: `HasVerdict net v := True` models "some fabricated authority
    can be made to answer `v`."  Then EVERY response — including an attacker's
    poisoned one — is "realizable."  Realizability certifies nothing about the
    resolver's honesty. -/
theorem poison_is_equally_realizable
    (fabricate : Resp → Net) :
    ∀ v : Resp, ∃ net : Net, (fun (_ : Net) (_ : Resp) => True) net v :=
  realizable_shape Net Resp (fun _ _ => True) fabricate (fun _ => trivial)

/-- The gap that matters: soundness needs agreement with a FIXED, independently
    given `net0` (the network the query was actually issued against), NOT a net
    chosen after seeing the answer.  `realizable_shape` does NOT yield this — you
    cannot extract `HasVerdict net0 v` for an arbitrary pre-fixed `net0`.
    Concrete refutation with `Net := Bool`, `Resp := Unit`. -/
theorem fixed_net_soundness_is_strictly_stronger :
    ¬ (∀ (N R : Type) (H : N → R → Prop) (fab : R → N),
         (∀ v, H (fab v) v) →                 -- realizability premise (holds)
         ∀ (net0 : N) (v : R), H net0 v) := by  -- claimed fixed-net soundness (must fail)
  intro h
  -- H net _ := (net = true); fab _ := true satisfies realizability;
  -- yet H false () is `false = true`, which is absurd.
  have hbad := h Bool Unit (fun net _ => net = true) (fun _ => true) (fun _ => rfl) false ()
  exact absurd hbad (by decide)
