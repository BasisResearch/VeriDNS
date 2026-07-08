/-! SPOT (round 3, thread d): the network-resolution disjunct of
    `Refinement.resolveWithIO_simulates` (Refinement.lean:9700) is the theorem's
    own conclusion, verbatim.

    Source shape (paraphrased):
      houtcome : A ∨ B ∨ C ∨ (∃ resp cout, RUN = ... ∧ HasVerdict ... (αResp resp))
      conclusion :         (∃ resp cout, RUN = ... ∧ HasVerdict ... (αResp resp))
      proof of 4th arm (9752-9753):  obtain ... := hnet;  exact ⟨resp,cout,hrun,hverdict⟩

    So the network case is a pure pass-through: the model-agreement fact
    `HasVerdict` for a network-obtained response is ASSUMED, never derived. The
    schematic below reproduces the exact logical structure and shows it proves
    for ANY predicates — including a `Concl` that is false of the real resolver.
    That is the definition of a vacuous (over-premised) disjunct: it can never
    fail to be dischargeable because it demands its own goal as input. -/

-- Abstract stand-ins: A,B,C are the three cache-hit disjuncts (really discharged
-- by sub-lemmas); `Concl` is the network conclusion `∃ resp cout, RUN ∧ HasVerdict`.
variable (A B C Concl : Prop)

-- The theorem's exact skeleton.  Note the 4th disjunct IS `Concl`.
theorem simulate_skeleton
    (hA : A → Concl) (hB : B → Concl) (hC : C → Concl)
    (houtcome : A ∨ B ∨ C ∨ Concl) : Concl := by
  rcases houtcome with h | h | h | h
  · exact hA h
  · exact hB h
  · exact hC h
  · exact h            -- the network arm: `exact hnet`, no model reasoning at all

/-- Weaponization witness: instantiate `Concl` as an OBSERVABLY FALSE statement
    (`False`). The skeleton still proves, given the (unsatisfiable-in-reality)
    premise. The point: `resolveWithIO_simulates` places NO independent constraint
    on the network path — feed it a `HasVerdict` for a poisoned/spoofed `resp` and
    it will certify that poisoned resp as model-justified. The theorem cannot tell
    a sound resolver from one whose network arm returns attacker data. -/
theorem simulate_certifies_anything :
    (True → False) → (True → False) → (True → False) →
    (True ∨ True ∨ True ∨ False) → False :=
  simulate_skeleton True True True False

/-- Contrast — how a NON-vacuous forward simulation must be shaped: the network
    conclusion has to be *derived* from an operational-run hypothesis plus network
    invariants, NOT handed in as the goal. This shape is NOT what 9700 proves. -/
theorem sensible_simulate_shape_requires_derivation
    (Run NetInv : Prop) (Concl2 : Prop)
    (derive : Run → NetInv → Concl2)
    (hrun : Run) (hinv : NetInv) : Concl2 :=
  derive hrun hinv
