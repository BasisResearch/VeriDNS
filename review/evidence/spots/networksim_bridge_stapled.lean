/-! SPOT (round 7, NEW, threads c+d joined): `NetworkSim.networkAnswer_simulates`
    (Proof/NetworkSim.lean:34) is the ONE named theorem the docstrings advertise as
    the "end-to-end" discharge of the network arm — "the network disjunct of
    `resolveWithIO_simulates`, discharged by construction rather than assumed"
    (NetworkSim.lean:17-19; echoed at WorldNetwork.lean:327-329 and
    Refinement.lean:9690-9698).  It is neither end-to-end nor a discharge.

    STRUCTURAL FACTS (from source; no SPOT needed, recorded for the record):

    (1) ITS BODY IS A STAPLE, NOT A COMPOSITION.  The proof term (NetworkSim.lean:56-58)
        is literally `⟨hrun, WorldNetwork.answer_model_realizable …⟩` — the impl-run
        fact `hrun` is taken as a HYPOTHESIS and pasted next to the self-fabricated
        model verdict.  No lemma relates the two; the resolver run and the model
        network are independent conjuncts.

    (2) THE `hrun` PREMISE IS NEVER DISCHARGED BY ITS CITED PRODUCER FOR A REAL RUN.
        `hrun` (NetworkSim.lean:40-41) demands the run return the cache UNCHANGED:
            Prog.run K (resolveWithIO … cache …) w = some ((.ok respImpl, cache), w')
        but the cited producer `run_resolveWithIO_networkAnswer` (FreeIO.lean:344-356)
        returns output cache
            (cacheUnlessTruncated state.cache resp (bailiwickRaws …) …).boundExpiryClasses
        i.e. the cache WITH the freshly cached answer inserted.  For any answer that
        actually gets cached (the normal case) that ≠ input `cache`, so the producer
        does NOT satisfy `hrun`.  The "supplied by run_resolveWithIO_networkAnswer"
        claim (NetworkSim.lean:10-12) does not type-check for cache-mutating runs.

    (3) THE MODEL VERDICT IS FABRICATED FROM THE ANSWER (inherited from
        answer_model_realizable): the conclusion is
            HasVerdict (answerNet addr q.qname (αResp respImpl).answer q.qclass) …
        a network BUILT from the delivered answer, over `Cache.empty` and `addr::rest`
        — NOT the ∀-fixed `net ns slist cache` of resolveWithIO_simulates' disjunct 4.
        So it can never be unified with that disjunct, and indeed
        `networkAnswer_simulates` is APPLIED NOWHERE (grep: only its own defn) and is
        NOT rfc_proves-published.  Terminal.

    (4) THE PREMISES EXCLUDE THE CONFIRMED ATTACKS.  `howner` (NetworkSim.lean:42)
        requires EVERY delivered answer RR to be owned by q.qname:
            ∀ r ∈ (αResp respImpl).answer, nameEq r.owner q.qname = true
        But CONFIRMED live differentials show the impl delivers records with
        owner ≠ q.qname (CNAME-target foreign-owner injection; bailiwick leniency;
        occluded-child).  For exactly those runs `howner` is FALSE and this theorem
        says NOTHING.  So the advertised "every positive answer the running resolver
        can deliver is justified by a constructible model authority"
        (WorldNetwork.lean:327-328) is false as stated — it covers only the
        already-owner-matched (honest) subset.

    The schematic below reproduces the exact logical shape and shows it proves for
    ANY respImpl — poisoned included — precisely because the model side is fabricated
    and the impl side is an unrelated conjunct. -/

variable (Query Resp Net Cache World : Type)

/-- Faithful skeleton of `networkAnswer_simulates`:
      * `run` = the impl run predicate (hrun), abstract;
      * `fabricate : Resp → Net` = answerNet built from the delivered answer;
      * `HasVerdict` holds by construction on the fabricated net (answer_model_realizable);
      * `howner` = the owner-match side condition. -/
theorem networkAnswer_skeleton
    (run : Resp → Prop)
    (HasVerdict : Net → Resp → Prop)
    (fabricate : Resp → Net)
    (howner : Resp → Prop)
    -- the SOLE model fact available: agreement holds on the SELF-BUILT net (vacuous).
    (realizable : ∀ resp, howner resp → HasVerdict (fabricate resp) resp)
    -- inputs, exactly as `networkAnswer_simulates` receives them:
    (respImpl : Resp) (hrun : run respImpl) (howner_resp : howner respImpl) :
    run respImpl ∧ HasVerdict (fabricate respImpl) respImpl :=
  ⟨hrun, realizable respImpl howner_resp⟩   -- ← NetworkSim.lean:56-58, verbatim shape

-- SENSIBLE property that a REAL end-to-end discharge SHOULD satisfy but this theorem
-- does NOT: agreement against an ARBITRARY caller-given `net` (the `net ns` fixed by
-- resolveWithIO_simulates), not one fabricated from the answer.  There is no term of
-- type `∀ net, HasVerdict net respImpl` derivable from the skeleton — which is exactly
-- why the bridge can never feed disjunct 4 of resolveWithIO_simulates.

/-- NONSENSE check (should PROVE, exposing vacuity): a POISONED response whose owner
    does NOT match still passes whenever we can fabricate its net — i.e. the theorem's
    guarantee is empty exactly where howner fails to hold, and full-strength only where
    the answer is already honest.  Here we show the honest branch proves for a
    completely arbitrary/poisoned respImpl as long as howner is granted, because the
    net is parroted. -/
theorem poisoned_answer_equally_realizable
    (HasVerdict : Net → Resp → Prop) (fabricate : Resp → Net) (howner : Resp → Prop)
    (realizable : ∀ resp, howner resp → HasVerdict (fabricate resp) resp)
    (poisoned : Resp) (howner_poisoned : howner poisoned) :
    HasVerdict (fabricate poisoned) poisoned :=
  realizable poisoned howner_poisoned
