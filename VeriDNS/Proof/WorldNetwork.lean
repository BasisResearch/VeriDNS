import VeriDNS.Proof.Refinement

/-!
# `World ↔ Network` abstraction — discharging the network `answer` disjunct concretely

`resolveWithIO_simulates` (`Proof/Refinement.lean`) takes the network outcome as an oracle premise:
a `HasVerdict` for the network sub-run. This file *constructs* that premise for the principal
positive-answer mode, so the network disjunct is no longer merely assumed.

Two layers:

* `serverAnswer_hasVerdict` — the **transport bridge**. Given an authoritative model server that
  `ServerAnswers` the query (and reachability + the response fits the UDP cap), the model's
  `Transit` / `OnWire` / `accepts` obligations are *discharged by construction*
  (`Transit.deliver`, `OnWire.fromServer`, `accepts_reply`) — they are no longer hypotheses. So a
  reachable authoritative answer is always a `HasVerdict`.

* `answer_model_realizable` — the **`World → Network` construction**. For *any* well-formed positive
  answer `v` (rcode `noError`, every answer RR owned by the query name and matching the query type/
  class), there is a concrete model `Network` whose single authoritative server produces exactly that
  answer, so `HasVerdict … v` holds. I.e. every positive answer the running resolver can deliver is
  justified by a constructible model authority — the network disjunct is realizable, not assumed.

`RespAgree` compares only the observable verdict (rcode + answer section), so the model server's
`authority`/`additional` (SOA hints, glue) need not match the impl's — exactly the right granularity.
-/

namespace VeriDNS.Proof.WorldNetwork

open VeriDNS.Spec (RRType RRClass)
open VeriDNS.Spec.Net
open VeriDNS.Proof.Refinement

/-- **Transport bridge.** A reachable authoritative server that `ServerAnswers` the query, with a
    response that fits the UDP cap and is answer-shaped (not a referral, untruncated, terminal),
    yields a `HasVerdict`: the model's transport obligations (`Transit`/`OnWire`/`accepts`) are
    discharged by the honest-delivery constructors rather than assumed. -/
theorem serverAnswer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (resp : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr resp)
    (hreachA : linkReach net ns resolverAddr addr = true)
    (hreachR : linkReach net ns resolverAddr resolverAddr = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q resp = (resp, false))
    (hnr : resp.isReferral = false)
    (hnc : cnameRR resp.answer = none ∨ q.qtype.covers RRType.cname = true
            ∨ (∃ rr ∈ resp.answer, q.qtype.covers rr.rdata.rtype = true))
    (htc : resp.tc = false)
    (v : Response) (hbridge : RespAgree v { resp with aa := false }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  refine answer_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q srv tr resp id srcPort c
    hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id resolverAddr addr srcPort ednsBuf q) resp)
    (Transit.deliver addr resolverAddr _ hreachA hreachR)
    (accepts_reply id resolverAddr addr srcPort ednsBuf q resp)
    ?_ hnr hnc htc v hbridge

  rw [hfit]
  exact OnWire.fromServer

/-- **Transport bridge for the `refer` branch** (the referral analogue of `serverAnswer_hasVerdict`).
    A reachable server that `ServerAnswers` the query with a *referral* response (in-bailiwick, descending
    below the server's bailiwick, with glue) yields a `HasVerdict`, GIVEN the recursive sub-resolution as a
    `HasVerdict` over the post-absorb cache at any SLIST `gl` that is a permutation of the cache-re-derived
    referral addresses (`hgl` — the keystone correspondence). The model's transport obligations
    (`Transit`/`OnWire`/`accepts`) are discharged by the honest-delivery constructors, and the Perm-form
    `refer` rule admits `gl`/`hgl` directly (no order reroute). This is the reusable core of the driver's
    `.continue` referral case: the impl absorbs the referral into a new state `st`, re-derives its SLIST from
    that cache, and recurses — and that recursion's verdict is exactly the model `refer` rule's verdict. -/
theorem serverRefer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (hreachA : linkReach net ns resolverAddr addr = true)
    (hreachR : linkReach net ns resolverAddr resolverAddr = true)
    (href : ref.isReferral = true)
    (hbail : ref.inBailiwick q.qname = true)
    (hdesc : ref.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : ref.descendsBelow frontier = true)
    (hglue : glueAddresses ref ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (gl : List String)
    (hgl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut ref)) ref).referralSlist now' q.qname (q.qname.length + 1)).Subperm gl)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref)) ref)
        gl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  refine refer_hasVerdict_perm net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref id srcPort c
    hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref)
    (Transit.deliver addr resolverAddr _ hreachA hreachR)
    (accepts_reply id resolverAddr addr srcPort ednsBuf q ref)
    ?_ href hbail hdesc frontier hdescF hglue hfresh hmono v gl hgl hrec

  exact OnWire.fromServer

/-- **Transport bridge for the `referForget` (eviction) branch** — the referral analogue where the
    recursion runs over a cache `cf` that `CacheRefines` the post-absorb cache (the resolver evicted cached
    answers to honour its capacity bound before recursing). Identical to `serverRefer_hasVerdict` but threads
    `cf`/`hcf` through `referForget_hasVerdict_hv`. This is the driver's `.continue` referral case *with*
    `boundStateCache` eviction: `cf = αCache(boundStateCache …)`, `hcf` from `cacheRefines_boundStateCache_absorb`. -/
theorem serverReferForget_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (hreachA : linkReach net ns resolverAddr addr = true)
    (hreachR : linkReach net ns resolverAddr resolverAddr = true)
    (href : ref.isReferral = true)
    (hbail : ref.inBailiwick q.qname = true)
    (hdesc : ref.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : ref.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (gl : List String)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut ref)) ref))
    (hgl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm gl
            ∨ (glueAddresses ref).Subperm gl)
    (cf : Cache)
    (hcf : WriteRefines now' cf cf0)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf gl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  refine referForget_hasVerdict_hv net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref id srcPort c
    hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref)
    (Transit.deliver addr resolverAddr _ hreachA hreachR)
    (accepts_reply id resolverAddr addr srcPort ednsBuf q ref)
    ?_ href hbail hdesc frontier hdescF hfresh hmono v gl cf0 hcf0 hgl cf hcf hrec
  exact OnWire.fromServer

/-- **Transport bridge, cout-exporting form (`HasVerdictAt`).** Same honest-delivery premises as
    `serverAnswer_hasVerdict`, but the model derivation is routed through `Resolves.trustedReply`
    instead of `Resolves.answer`, pinning the OUTPUT CACHE to the input `c`. Rationale: the
    executable resolver's terminal answer/negative delivery does NOT write its cache (the
    `stepAnalyzeResponse` `.answer` leaves return the state verbatim; only chase/referral hops
    write), whereas `Resolves.answer`'s output cache is the full-message absorb — a write the impl
    never performs, so the driver's impl↔model output-cache tie (`CacheRefines (αCache cout) coutM`)
    is only realizable against the cout-faithful `trustedReply` rule. The honest transport facts
    (`Transit.deliver`/`accepts_reply` from reachability) are constructed exactly as in
    `serverAnswer_hasVerdict`; only the rule attribution of the (observably identical) verdict
    changes. -/
theorem serverAnswer_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (resp : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hreachA : linkReach net ns resolverAddr addr = true)
    (hreachR : linkReach net ns resolverAddr resolverAddr = true)
    (hnr : resp.isReferral = false)
    (htc : resp.tc = false)
    (v : Response) (hbridge : RespAgree v { resp with aa := false })

    (cf0 : Cache)
    (hcf0 : WriteRefines now cf0 (c.absorb now q.qname { resp with authority := [], additional := [] })
            ∨ cf0 = c)
    (cf : Cache) (hcf : WriteRefines now cf cf0) :
    VeriDNS.Proof.Refinement.HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c
      (addr :: rest) q v cf :=
  ⟨_, _, _, _,
   Resolves.trustedReply addr addr rest q id srcPort c
     (replyDatagram (queryDatagram id resolverAddr addr srcPort ednsBuf q) resp)
     hmiss hnmiss
     (Transit.deliver addr resolverAddr _ hreachA hreachR)
     (accepts_reply id resolverAddr addr srcPort ednsBuf q resp)
     hnr htc cf0 hcf0 cf hcf, hbridge⟩

/-- **Transport bridge for the `referForget` branch, cout-exporting form.** Identical premises to
    `serverReferForget_hasVerdict`, with the recursion supplied (and the conclusion delivered) as a
    `HasVerdictAt`: the referral hop returns the recursion's output cache unchanged, so `coutM`
    threads through verbatim. -/
theorem serverReferForget_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (hreachA : linkReach net ns resolverAddr addr = true)
    (hreachR : linkReach net ns resolverAddr resolverAddr = true)
    (href : ref.isReferral = true)
    (hbail : ref.inBailiwick q.qname = true)
    (hdesc : ref.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : ref.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (gl : List String)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut ref)) ref))
    (hgl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm gl
            ∨ (glueAddresses ref).Subperm gl)
    (cf : Cache)
    (hcf : WriteRefines now' cf cf0) (coutM : Cache)
    (hrec : VeriDNS.Proof.Refinement.HasVerdictAt net ns resolverAddr ednsBuf rttOf now' nseen
      (frontier :: seen) cf gl q v coutM) :
    VeriDNS.Proof.Refinement.HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c
      (addr :: rest) q v coutM := by
  obtain ⟨ftr, rpath, tEnd, final, hres, hbridge⟩ := hrec
  refine ⟨_, _, _, _,
    Resolves.referForget addr rest q srv tr ref ftr rpath tEnd final id srcPort c coutM
      hmiss hnmiss hfind hans
      (replyDatagram (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref)
      (Transit.deliver addr resolverAddr _ hreachA hreachR)
      (accepts_reply id resolverAddr addr srcPort ednsBuf q ref)
      ?_ href hbail frontier hdesc hdescF hfresh hmono gl cf0 hcf0 hgl cf hcf hres,
    hbridge⟩
  exact OnWire.fromServer

/-- The authoritative zone realizing answer `A`: apex = the query name, records = `A`, no
    delegations. -/
def answerZone (apex : Name) (records : List RR) (qcls : RRClass) : Zone :=
  { apex := apex, records := records, delegations := [], cls := qcls }

/-- The authoritative model server realizing answer `A` for class `qcls`, reachable at `addr`. -/
def answerServer (addr : String) (apex : Name) (records : List RR) (qcls : RRClass) : Server :=
  { name := apex, zones := [answerZone apex records qcls], cache := [], addr := addr,
    recursionAvailable := false, rtt := 0 }

/-- A one-server network hosting `answerServer`. -/
def answerNet (addr : String) (apex : Name) (records : List RR) (qcls : RRClass) : Network :=
  ⟨[answerServer addr apex records qcls]⟩

/-- The all-servers-up network state. -/
def allUp : NetState := { status := fun _ => Status.up }

/-- The built network serves its single server at `addr`. -/
theorem answerNet_serverAt (addr : String) (apex : Name) (records : List RR) (qcls : RRClass) :
    serverAt (answerNet addr apex records qcls) addr = some (answerServer addr apex records qcls) := by
  simp only [serverAt, answerNet, answerServer, List.find?, beq_self_eq_true]

/-- The built server is reachable from the resolver in the all-up state. -/
theorem answerNet_reachA (addr : String) (apex : Name) (records : List RR) (qcls : RRClass)
    (resolverAddr : String) :
    linkReach (answerNet addr apex records qcls) allUp resolverAddr addr = true := by
  have hup : (Status.up == Status.up) = true := rfl
  simp only [linkReach, reachOf, answerNet, answerServer, allUp, NetState.isUp, List.any_cons,
    List.any_nil, Bool.or_false, beq_self_eq_true, Bool.true_and, hup, Bool.or_true]

/-- The resolver address is always reachable from itself. -/
theorem reach_self (net : Network) (ns : NetState) (resolverAddr : String) :
    linkReach net ns resolverAddr resolverAddr = true := by
  simp only [linkReach, beq_self_eq_true, Bool.true_or]

/-- `recordsAt` of the answer zone returns exactly `A` when every RR is owned by the query name. -/
theorem recordsAt_answerZone (apex : Name) (A : List RR) (qcls : RRClass)
    (howner : ∀ r ∈ A, nameEq r.owner apex = true) :
    recordsAt (answerZone apex A qcls) apex = A := by
  simp only [recordsAt, answerZone]
  exact List.filter_eq_self.mpr (fun r hr => howner r hr)

/-- The answer zone has no delegations. -/
theorem bestDeleg_answerZone (apex : Name) (A : List RR) (qcls : RRClass) (qname : Name) :
    bestDeleg (answerZone apex A qcls) qname = none := by
  simp only [bestDeleg, answerZone, List.filter_nil, List.foldl_nil]

/-- The built server's best zone for its own apex is the answer zone. -/
theorem bestZone_answerServer (addr : String) (apex : Name) (A : List RR) (qcls : RRClass) :
    bestZone (answerServer addr apex A qcls) apex qcls = some (answerZone apex A qcls) := by
  have hcc : (qcls == qcls) = true := by cases qcls <;> rfl
  simp only [bestZone, answerServer, answerZone, isAncestor_refl, hcc, Bool.and_true,
    List.filter_cons, List.filter_nil, if_pos, List.foldl_cons, List.foldl_nil]

/-- The model response the built authoritative server produces for `q` (the `ServerAnswers.answer`
    constructor's output, named so it can be referenced). -/
def answerRespOf (addr : String) (now : Time) (q : Query) (A : List RR) : Response :=
  { aa := true, rcode := RCode.noError,
    ra := (answerServer addr q.qname A q.qclass).recursionAvailable,
    answer := (recordsAt (answerZone q.qname A q.qclass) q.qname).filter
                (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass),
    authority := [],
    additional := additionalFrom ((answerZone q.qname A q.qclass).records
                    ++ freshServerCache (answerServer addr q.qname A q.qclass) now)
                    ((recordsAt (answerZone q.qname A q.qclass) q.qname).filter
                      (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass)) }

/-- The built authoritative server `ServerAnswers` the query with `answerRespOf` — the model-side
    realizability of any well-formed positive answer. -/
theorem answerServer_answers
    (addr : String) (now : Time) (q : Query) (A : List RR)
    (howner : ∀ r ∈ A, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ A, (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true)
    (hnc : cnameRR A = none ∨ q.qtype.covers RRType.cname = true)
    (hA : A ≠ []) :
    ServerAnswers (answerServer addr q.qname A q.qclass) now [] true q
      [Step.findZone q.qname, Step.matchNode q.qname, Step.copyAnswer, Step.addAdditional]
      (answerRespOf addr now q A) := by
  have hrec : recordsAt (answerZone q.qname A q.qclass) q.qname = A :=
    recordsAt_answerZone q.qname A q.qclass howner
  have hnc' : cnameRR (recordsAt (answerZone q.qname A q.qclass) q.qname) = none
      ∨ q.qtype.covers RRType.cname = true := by rw [hrec]; exact hnc
  have hfilt : (recordsAt (answerZone q.qname A q.qclass) q.qname).filter
      (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass) ≠ [] := by
    rw [hrec, List.filter_eq_self.mpr (fun r hr => hmatch r hr)]; exact hA
  exact ServerAnswers.answer q (answerZone q.qname A q.qclass)
    (recordsAt (answerZone q.qname A q.qclass) q.qname)
    (bestZone_answerServer addr q.qname A q.qclass)
    (bestDeleg_answerZone q.qname A q.qclass q.qname) rfl hnc' hfilt

/-- `answerRespOf`'s answer section is exactly `A` (filter is a no-op under `hmatch`). -/
theorem answerRespOf_answer (addr : String) (now : Time) (q : Query) (A : List RR)
    (howner : ∀ r ∈ A, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ A, (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true) :
    (answerRespOf addr now q A).answer = A := by
  simp only [answerRespOf, recordsAt_answerZone q.qname A q.qclass howner]
  exact List.filter_eq_self.mpr (fun r hr => hmatch r hr)

/-- **`World → Network` construction (the network `answer` disjunct, discharged by construction).**
    For *any* well-formed positive answer `v` (rcode `noError`; every answer RR owned by the query
    name and matching the query type/class; non-empty; fits the UDP cap), there is a concrete model
    network — a single authoritative server at `addr` — whose run yields `HasVerdict … v`. So every
    positive answer the running resolver can deliver is justified by a constructible model authority;
    the network disjunct of `resolveWithIO_simulates` is *realizable*, not merely assumed. -/
theorem answer_model_realizable
    (resolverAddr addr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (rest : List String) (q : Query) (id srcPort : Nat)
    (A : List RR) (v : Response)
    (howner : ∀ r ∈ A, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ A, (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true)
    (hnc : cnameRR A = none ∨ q.qtype.covers RRType.cname = true)
    (hA : A ≠ [])
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q (answerRespOf addr now q A)
        = (answerRespOf addr now q A, false))
    (hrc : v.rcode = RCode.noError) (hva : v.answer = A) :
    HasVerdict (answerNet addr q.qname A q.qclass) allUp resolverAddr ednsBuf rttOf now nseen seen
      Cache.empty (addr :: rest) q v := by
  have hrespA : (answerRespOf addr now q A).answer = A := answerRespOf_answer addr now q A howner hmatch
  have hAe : A.isEmpty = false := by cases A with | nil => exact absurd rfl hA | cons => rfl
  have hnr : (answerRespOf addr now q A).isReferral = false := by
    simp only [Response.isReferral, hrespA, hAe, Bool.false_and]
  refine serverAnswer_hasVerdict (answerNet addr q.qname A q.qclass) allUp resolverAddr ednsBuf rttOf
    addr rest q (answerServer addr q.qname A q.qclass) _ (answerRespOf addr now q A) id srcPort
    Cache.empty rfl rfl (answerNet_serverAt addr q.qname A q.qclass)
    (answerServer_answers addr now q A howner hmatch hnc hA)
    (answerNet_reachA addr q.qname A q.qclass resolverAddr) (reach_self _ allUp _)
    hfit hnr (by rw [hrespA]; rcases hnc with h | h; exacts [Or.inl h, Or.inr (Or.inl h)]) rfl v ?_
  exact RespAgree.of_eq hrc (hva.trans hrespA.symm)

/-- An empty answer zone is not an empty-non-terminal at its own apex (no descendants). -/
theorem isEmptyNonTerminal_empty (apex : Name) (qcls : RRClass) :
    isEmptyNonTerminal (answerZone apex [] qcls) apex = false := by
  simp [isEmptyNonTerminal, answerZone]

/-- An empty answer zone synthesises no wildcard. -/
theorem wildcardSynth_empty (apex : Name) (qcls : RRClass) (qt : QType) :
    wildcardSynth (answerZone apex [] qcls) apex qt qcls = none := by
  unfold wildcardSynth
  split
  · rfl
  · rw [Option.map_eq_none_iff]
    apply List.findSome?_eq_none_iff.mpr
    intro k _
    simp [recordsAt, answerZone]

/-- The NXDOMAIN output of the empty answer zone carries an empty authority (no SOA). -/
theorem nxdomainAuthority_empty (apex : Name) (qcls : RRClass) :
    nxdomainAuthority (answerZone apex [] qcls) = [] := by
  simp [nxdomainAuthority, answerZone, soaOf]

/-- The model response the empty authoritative server produces for `q`: an authoritative NXDOMAIN
    (empty answer, empty authority). -/
def nxdomainRespOf (addr : String) (q : Query) : Response :=
  { aa := true, rcode := RCode.nameError,
    ra := (answerServer addr q.qname [] q.qclass).recursionAvailable,
    answer := [], authority := nxdomainAuthority (answerZone q.qname [] q.qclass),
    additional := [] }

/-- The built (empty) authoritative server `ServerAnswers` the query with an authoritative NXDOMAIN —
    the model-side realizability of a name-error response. -/
theorem nxdomainServer_answers (addr : String) (now : Time) (q : Query) :
    ServerAnswers (answerServer addr q.qname [] q.qclass) now [] true q
      [Step.findZone q.qname, Step.nameError] (nxdomainRespOf addr q) :=
  ServerAnswers.nameError q (answerZone q.qname [] q.qclass)
    (bestZone_answerServer addr q.qname [] q.qclass)
    (bestDeleg_answerZone q.qname [] q.qclass q.qname)
    (recordsAt_answerZone q.qname [] q.qclass (by intro r hr; exact absurd hr (by simp)))
    (wildcardSynth_empty q.qname q.qclass q.qtype)
    (isEmptyNonTerminal_empty q.qname q.qclass)

/-- **`World → Network` construction for NXDOMAIN** (the network name-error branch, discharged by
    construction). For any name-error response `v` (rcode `nameError`, empty answer; fits the cap),
    there is a concrete one-server model network whose authoritative NXDOMAIN run is `HasVerdict … v`.
    The companion of `answer_model_realizable` for the name-error mode. -/
theorem nxdomain_model_realizable
    (resolverAddr addr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (rest : List String) (q : Query) (id srcPort : Nat) (v : Response)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q (nxdomainRespOf addr q)
        = (nxdomainRespOf addr q, false))
    (hrc : v.rcode = RCode.nameError) (hva : v.answer = []) :
    HasVerdict (answerNet addr q.qname [] q.qclass) allUp resolverAddr ednsBuf rttOf now nseen seen
      Cache.empty (addr :: rest) q v := by
  have hnr : (nxdomainRespOf addr q).isReferral = false := by
    simp [Response.isReferral, nxdomainRespOf]
  refine serverAnswer_hasVerdict (answerNet addr q.qname [] q.qclass) allUp resolverAddr ednsBuf rttOf
    addr rest q (answerServer addr q.qname [] q.qclass) _ (nxdomainRespOf addr q) id srcPort
    Cache.empty rfl rfl (answerNet_serverAt addr q.qname [] q.qclass)
    (nxdomainServer_answers addr now q)
    (answerNet_reachA addr q.qname [] q.qclass resolverAddr) (reach_self _ allUp _)
    hfit hnr (Or.inl rfl) rfl v ?_
  exact RespAgree.of_eq hrc hva

/-! ### NODATA branch (the name exists as an empty-non-terminal, but has no records of the type) -/

/-- A child name is a strict descendant of its parent: not equal (the model `nameEq` is structural,
    so the lengths differ). -/
theorem nameEq_child_false (x : ByteArray) (qname : Name) : nameEq (x :: qname) qname = false := by
  by_contra h; rw [Bool.not_eq_false] at h; have := nameEq_length h; simp at this

theorem nameEq_child_false' (x : ByteArray) (qname : Name) : nameEq qname (x :: qname) = false := by
  by_contra h; rw [Bool.not_eq_false] at h; have := nameEq_length h; simp at this

/-- A child name is in the bailiwick of (a descendant of) its parent. -/
theorem isAncestor_child (x : ByteArray) (qname : Name) : isAncestor qname (x :: qname) = true := by
  have h2 : (x :: qname).drop ((x :: qname).length - qname.length) = qname := by
    simp [List.length_cons]
  unfold isAncestor; rw [h2]; simp [List.length_cons, nameEq_refl]

/-- One ENT (empty-non-terminal) record: an A record at a child `x.qname`, so `qname` itself has no
    records but is "known" (has a descendant). -/
def entRR (qname : Name) (qcls : RRClass) : RR :=
  { owner := L "x" :: qname, ttl := 0, rdata := RData.a ⟨0, 0, 0, 0⟩, cls := qcls }

/-- The query name has no records in the ENT zone (the only record is at a child). -/
theorem recordsAt_entZone (qname : Name) (qcls : RRClass) :
    recordsAt (answerZone qname [entRR qname qcls] qcls) qname = [] := by
  simp [recordsAt, answerZone, entRR, nameEq_child_false]

/-- The query name is an empty-non-terminal in the ENT zone (it has the child as a descendant). -/
theorem isEmptyNonTerminal_ent (qname : Name) (qcls : RRClass) :
    isEmptyNonTerminal (answerZone qname [entRR qname qcls] qcls) qname = true := by
  simp [isEmptyNonTerminal, answerZone, entRR, isAncestor_child, nameEq_child_false']

/-- The ENT zone is "known" at the query name (has a descendant), so no wildcard is synthesised. -/
theorem wildcardSynth_ent (qname : Name) (qcls : RRClass) (qt : QType) :
    wildcardSynth (answerZone qname [entRR qname qcls] qcls) qname qt qcls = none := by
  unfold wildcardSynth
  rw [if_pos]
  simp [nameKnown, answerZone, entRR, isAncestor_child]

/-- The NODATA output of the ENT zone carries an empty authority (no SOA at the apex). -/
theorem noDataAuthority_ent (qname : Name) (qcls : RRClass) :
    noDataAuthority (answerZone qname [entRR qname qcls] qcls) = [] := by
  have hsoa : soaOf (answerZone qname [entRR qname qcls] qcls) = none := by
    show (List.find? _ [entRR qname qcls]) = none
    rw [List.find?_cons]
    simp only [entRR, RData.rtype, show (RRType.a == RRType.soa) = false from rfl, Bool.false_and,
      List.find?_nil]
  unfold noDataAuthority
  rw [hsoa]
  simp [answerZone]

/-- The model response the ENT server produces: an authoritative NODATA (empty answer, empty
    authority for our minimal zone). -/
def noDataRespOf (addr : String) (q : Query) : Response :=
  { aa := true, rcode := RCode.noError,
    ra := (answerServer addr q.qname [entRR q.qname q.qclass] q.qclass).recursionAvailable,
    answer := [], authority := noDataAuthority (answerZone q.qname [entRR q.qname q.qclass] q.qclass),
    additional := [] }

/-- The built ENT authoritative server `ServerAnswers` the query with an authoritative NODATA. -/
theorem noDataServer_answers (addr : String) (now : Time) (q : Query) :
    ServerAnswers (answerServer addr q.qname [entRR q.qname q.qclass] q.qclass) now [] true q
      [Step.findZone q.qname, Step.noData] (noDataRespOf addr q) :=
  ServerAnswers.noData q (answerZone q.qname [entRR q.qname q.qclass] q.qclass) []
    (bestZone_answerServer addr q.qname [entRR q.qname q.qclass] q.qclass)
    (bestDeleg_answerZone q.qname [entRR q.qname q.qclass] q.qclass q.qname)
    (recordsAt_entZone q.qname q.qclass)
    (Or.inl rfl)
    (by simp)
    (wildcardSynth_ent q.qname q.qclass q.qtype)
    (Or.inr (isEmptyNonTerminal_ent q.qname q.qclass))

/-- **`World → Network` construction for NODATA** (the no-records-of-type branch, discharged by
    construction). For any NODATA response `v` (rcode `noError`, empty answer; fits the cap), there is
    a concrete one-server model network whose authoritative NODATA run is `HasVerdict … v`. -/
theorem nodata_model_realizable
    (resolverAddr addr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (rest : List String) (q : Query) (id srcPort : Nat) (v : Response)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q (noDataRespOf addr q)
        = (noDataRespOf addr q, false))
    (hrc : v.rcode = RCode.noError) (hva : v.answer = []) :
    HasVerdict (answerNet addr q.qname [entRR q.qname q.qclass] q.qclass) allUp resolverAddr ednsBuf
      rttOf now nseen seen Cache.empty (addr :: rest) q v := by
  have hnr : (noDataRespOf addr q).isReferral = false := by simp [Response.isReferral, noDataRespOf]
  refine serverAnswer_hasVerdict (answerNet addr q.qname [entRR q.qname q.qclass] q.qclass) allUp
    resolverAddr ednsBuf rttOf addr rest q (answerServer addr q.qname [entRR q.qname q.qclass] q.qclass)
    _ (noDataRespOf addr q) id srcPort Cache.empty rfl rfl
    (answerNet_serverAt addr q.qname [entRR q.qname q.qclass] q.qclass)
    (noDataServer_answers addr now q)
    (answerNet_reachA addr q.qname [entRR q.qname q.qclass] q.qclass resolverAddr) (reach_self _ allUp _)
    hfit hnr (Or.inl rfl) rfl v ?_
  exact RespAgree.of_eq hrc hva

/-- **Exhausted (SERVFAIL) terminal realizability.** The fourth and last *purely terminal* (non-
    recursive) model verdict shape, completing the set alongside `answer`/`nxdomain`/`nodata`. When
    the resolver's SLIST is empty there is no server left to query, and RFC 1034 §5.3.3 has it return
    SERVFAIL with empty sections — the model's `Resolves.exhausted` base case. Unlike the other three
    this needs no constructed network: `Resolves.exhausted` holds for *any* `net`/`ns` from the
    empty-slist state, so any impl verdict that abstracts to a SERVFAIL with empty answer is justified
    by the model directly. The remaining model constructors (`timeout`, `skipMissing`, `rejectSpoof`,
    `gluelessNs`) all carry recursive premises and belong to the loop-induction frontier (C3). -/
theorem exhausted_model_realizable
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (q : Query)
    (v : Response) (hrc : v.rcode = RCode.servFail) (hva : v.answer = []) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c [] q v :=
  ⟨[], [], now, c, _, Resolves.exhausted c q, RespAgree.of_eq hrc hva⟩

end VeriDNS.Proof.WorldNetwork
