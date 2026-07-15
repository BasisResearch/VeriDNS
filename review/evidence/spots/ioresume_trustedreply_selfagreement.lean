/-! SPOT (round 6, NEW — threads b+c joined): the ONE oracle-free network-agreement
    theorem `IoResumeSound.ioResumeLoop_sound` (Proof/IoResumeSound.lean:2810)
    discharges its network ANSWER / CNAME arms through the poison-admitting model
    constructor `Resolves.trustedReply` (Spec/NetworkSemantics.lean:1444), via the
    bridges `trustedReply_hasVerdictAt` (Refinement.lean:9516) and
    `WorldNetwork.serverAnswer_hasVerdictAt` (WorldNetwork.lean:157) — the LATTER also
    routes through `trustedReply` even in the "honest server" case (WorldNetwork.lean
    :147-153,176).  Applied at IoResumeSound.lean:3542/3561/3582/3598/3745/3793/… .

    GREP FACTS (source, no proof needed):
      * `trustedReply_hasVerdictAt` (Refinement.lean:9516-9532) takes the delivered
        verdict `v : Response` and the accepted datagram `reply : Datagram` as FREE
        parameters.  Its ONLY content premises are `htrans` (link reachability),
        `hacc : accepts (queryDatagram …) reply = true` (RFC-5452 id+question+source
        match — a gate the impl ALREADY passes), `hnr`/`htc`, and
        `hbridge : RespAgree v { reply.msg with aa := false }`.  There is NO
        `serverAt net addr = some srv` and NO `ServerAnswers` premise: the verdict is
        NOT tied to any honest server's data in `net`.
      * Consequently the answer-arm conclusion clause of ioResumeLoop_sound
        (IoResumeSound.lean:2866)
            (αResp resp).answer = αSection state.cnameChain ++ v.answer
        is satisfied by choosing `v := αResp resp` (the impl's OWN produced response);
        it constrains `resp` to equal itself, not to be the correct DNS data.
      * The heavy driver even `rcases`es an explicit honest/spoof disjunction
        (IoResumeSound.lean:3543 `⟨srv,…,hfind,hans,…⟩ | hspoof`) and discharges BOTH
        sides with a trustedReply-family bridge — the honest `hfind/hans` facts are
        collected (feeding `positive_answer_covered`, which only witnesses a
        covering-TYPE record, never its rdata) but the OUTPUT verdict is re-derived
        from the impl's own accepted `reply`.

    CONSEQUENCE: the theorem advertised as the constructive, NetworkConsistent-free
    network discharge proves, on the answer/cname arms, SELF-AGREEMENT (impl output =
    model verdict re-derived from that same output).  An impl that serves an
    attacker-forged in-bailiwick answer produces `resp` whose answer is the forgery,
    and `trustedReply` fabricates a matching model verdict — so the STATEMENT stays
    true.  This is strictly weaker than "the delivered answer is the true DNS data."

    The schematic below reproduces the exact logical shape and shows:
      (SENSIBLE)  the honest answer has a model verdict — proves.
      (NONSENSE)  an arbitrary attacker response ALSO has a model verdict, with no
                  tie to the honest network — proves too (it should NOT, if HasVerdict
                  were a real correctness oracle).  Its provability IS the vacuity. -/

-- Abstract stand-ins (implicit type parameters throughout).
variable {Net Server Resp Datagram Query : Type}

/-- Faithful two-constructor shape of the model `Resolves` relation: an HONEST arm
    that requires the network to actually contain a server answering `q` with `resp`,
    and a TRUSTED-REPLY arm that requires only that `reply` passed the accept gate —
    the delivered verdict `resp` is otherwise free. -/
inductive Resolves
    (net : Net) (q : Query)
    (serverAt : Net → Option Server)
    (serverAnswers : Server → Query → Resp → Prop)
    (accepts : Datagram → Bool) : Resp → Prop where
  | answer (srv : Server) (resp : Resp)
      (hfind : serverAt net = some srv)
      (hans  : serverAnswers srv q resp) :
      Resolves net q serverAt serverAnswers accepts resp
  | trustedReply (reply : Datagram) (resp : Resp)     -- ← verdict `resp` is FREE
      (hacc : accepts reply = true) :
      Resolves net q serverAt serverAnswers accepts resp

/-- `HasVerdict`: the soundness conclusion — the impl's delivered response agrees
    with SOME model derivation over the given `net`. -/
def HasVerdict
    (net : Net) (q : Query)
    (serverAt : Net → Option Server)
    (serverAnswers : Server → Query → Resp → Prop)
    (accepts : Datagram → Bool)
    (delivered : Resp) : Prop :=
  Resolves net q serverAt serverAnswers accepts delivered

/-- (SENSIBLE) An honestly-served answer has a model verdict. -/
theorem honest_hasVerdict
    (net : Net) (q : Query)
    (serverAt : Net → Option Server)
    (serverAnswers : Server → Query → Resp → Prop)
    (accepts : Datagram → Bool)
    (srv : Server) (resp : Resp)
    (hfind : serverAt net = some srv) (hans : serverAnswers srv q resp) :
    HasVerdict
      net q serverAt serverAnswers accepts resp :=
  Resolves.answer srv resp hfind hans

/-- (NONSENSE) An ARBITRARY attacker-chosen response `poison` — with NO relation to
    any server in `net` — ALSO has a model verdict, as long as SOME accepts-passing
    datagram exists (the impl always has one: the reply it accepted).  A real
    correctness oracle must NOT admit this.  It proves, mirroring
    `trustedReply_hasVerdictAt`: the verdict parameter is free. -/
theorem poison_hasVerdict
    (net : Net) (q : Query)
    (serverAt : Net → Option Server)
    (serverAnswers : Server → Query → Resp → Prop)
    (accepts : Datagram → Bool)
    (poison : Resp)                       -- attacker-controlled, unrelated to net
    (reply : Datagram) (hacc : accepts reply = true) :
    HasVerdict
      net q serverAt serverAnswers accepts poison :=
  Resolves.trustedReply reply poison hacc

/-- Sharpest statement of the vacuity: for a FIXED net whose only server answers the
    single honest response `good`, the SAME `HasVerdict` predicate is *also* satisfied
    by a different response `bad ≠ good`.  Verdict agreement therefore cannot
    distinguish the honest answer from a forgery. -/
theorem verdict_does_not_pin_answer
    (net : Net) (q : Query)
    (serverAt : Net → Option Server)
    (serverAnswers : Server → Query → Resp → Prop)
    (accepts : Datagram → Bool)
    (good bad : Resp)
    (reply : Datagram) (hacc : accepts reply = true) :
    HasVerdict net q serverAt serverAnswers accepts good
    ∧ HasVerdict net q serverAt serverAnswers accepts bad :=
  ⟨Resolves.trustedReply reply good hacc, Resolves.trustedReply reply bad hacc⟩
