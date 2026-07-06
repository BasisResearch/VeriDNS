import VeriDNS.Proof.FreeIO
import VeriDNS.Proof.WorldNetwork
import VeriDNS.Proof.AnswerTerminal

/-!
# Network answer: impl run ⟷ model verdict, end to end

`networkAnswer_simulates` joins the two sides of the network `answer` path:

* the **impl side** — `Proof/FreeIO.run_resolveWithIO_networkAnswer` runs the *actual* executable
  resolver over a concrete `World` oracle and returns a finalized response (transport discharged
  concretely, not axiomatically);

* the **model side** — `Proof/WorldNetwork.answer_model_realizable` exhibits a concrete authoritative
  `Network` whose run is a `Net.Resolves` derivation observably agreeing with that response.

Their conjunction is the end-to-end statement for the principal network mode: *the running resolver,
on a network answer, produces a verdict that the model justifies* — the network disjunct of
`resolveWithIO_simulates`, discharged by construction rather than assumed.
-/

namespace VeriDNS.Proof.NetworkSim

open VeriDNS.Spec (RRType RRClass)
open VeriDNS.Spec.Net
open VeriDNS.Proof.Refinement VeriDNS.Proof.FreeIO

/-- **End-to-end network answer.** Given the FreeIO run of the real resolver yielding `respImpl`
    (`hrun`, supplied by `run_resolveWithIO_networkAnswer`) and that the answer is well-formed
    (owned by the query name, type/class-matching, non-empty, fits the UDP cap, `noError`), the run's
    abstracted verdict `αResp respImpl` is justified by a constructed authoritative model network
    (`HasVerdict`). This composes the executable I/O round with the model realizability — the
    network `answer` mode of the forward simulation, end to end. -/
theorem networkAnswer_simulates
    (query : VeriDNS.Spec.Format) (sbelt : VeriDNS.Impl.SList.DnsSList)
    (cache : VeriDNS.Impl.Cache.DnsCache) (nowImpl : UInt32) (fuel depth : Nat) (budget : UInt32)
    (w : World) (respImpl : VeriDNS.Spec.Format)
    (resolverAddr addr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (rest : List String) (q : Query)
    (hrun : ∃ K w', Prog.run K (VeriDNS.Impl.Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache nowImpl fuel depth budget) w = some ((Except.ok respImpl, cache), w'))
    (howner : ∀ r ∈ (αResp respImpl).answer, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ (αResp respImpl).answer,
        (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true)
    (hnc : cnameRR (αResp respImpl).answer = none ∨ q.qtype.covers RRType.cname = true)
    (hA : (αResp respImpl).answer ≠ [])
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q
        (WorldNetwork.answerRespOf addr now q (αResp respImpl).answer)
          = (WorldNetwork.answerRespOf addr now q (αResp respImpl).answer, false))
    (hrc : (αResp respImpl).rcode = RCode.noError) :
    (∃ K w', Prog.run K (VeriDNS.Impl.Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache nowImpl fuel depth budget) w = some ((Except.ok respImpl, cache), w'))
    ∧ HasVerdict (WorldNetwork.answerNet addr q.qname (αResp respImpl).answer q.qclass)
        WorldNetwork.allUp
        resolverAddr ednsBuf rttOf now nseen seen Cache.empty (addr :: rest) q (αResp respImpl) :=
  ⟨hrun,
   WorldNetwork.answer_model_realizable resolverAddr addr ednsBuf rttOf rest q 0 0
     (αResp respImpl).answer (αResp respImpl) howner hmatch hnc hA hfit hrc rfl⟩

/-- **End-to-end network NXDOMAIN** (the name-error companion of `networkAnswer_simulates`). Given
    the FreeIO run yielding `respImpl` (`hrun`, from `run_ioResumeLoop_nxdomain` lifted to
    `resolveWithIO`) and that it is a name-error (rcode `nameError`, empty answer, fits the cap), the
    run's abstracted verdict is justified by a constructed authoritative-NXDOMAIN model network. -/
theorem networkNxdomain_simulates
    (query : VeriDNS.Spec.Format) (sbelt : VeriDNS.Impl.SList.DnsSList)
    (cache : VeriDNS.Impl.Cache.DnsCache) (nowImpl : UInt32) (fuel depth : Nat) (budget : UInt32)
    (w : World) (respImpl : VeriDNS.Spec.Format)
    (resolverAddr addr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (rest : List String) (q : Query)
    (hrun : ∃ K w', Prog.run K (VeriDNS.Impl.Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache nowImpl fuel depth budget) w = some ((Except.ok respImpl, cache), w'))
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q (WorldNetwork.nxdomainRespOf addr q)
        = (WorldNetwork.nxdomainRespOf addr q, false))
    (hrc : (αResp respImpl).rcode = RCode.nameError)
    (hva : (αResp respImpl).answer = []) :
    (∃ K w', Prog.run K (VeriDNS.Impl.Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache nowImpl fuel depth budget) w = some ((Except.ok respImpl, cache), w'))
    ∧ HasVerdict (WorldNetwork.answerNet addr q.qname [] q.qclass) WorldNetwork.allUp
        resolverAddr ednsBuf rttOf now nseen seen Cache.empty (addr :: rest) q (αResp respImpl) :=
  ⟨hrun,
   WorldNetwork.nxdomain_model_realizable resolverAddr addr ednsBuf rttOf rest q 0 0
     (αResp respImpl) hfit hrc hva⟩

/-! ### C1 — the `WorldModels` environment-consistency relation (GAP 1, Option 3)

  The forward-simulation totality (`resolveWithIO_total`, the recursive frontier) needs one legitimate
  assumption: the World oracle the resolver runs against simulates a faithful execution of the model
  network — *you cannot prove the network, you assume it behaves per the model*. The user-chosen
  Option 3 makes that assumption **adversary-inclusive**: replies may be lost, partitioned, or off-path
  spoofed; the model's `Transit`/`accepts`/bailiwick machinery then bounds what the adversary achieves.
  This is the C1 foundation the `ioResumeLoop` induction instantiates per hop; the per-branch
  `*_hasVerdict`/`*_hasVerdict_hv` wrappers and the terminal realizabilities consume its output. -/

/-- **Environment consistency (Option 3 — full transport incl. adversary).** For every reply the
    resolver *accepts* (oracle yields `d` for the id-stamped query `q` sent to byte-address `ab`, and
    the receive pipeline `acceptExchanged → decode → sanitizeTtlsCap → acceptResponse` produces `resp`,
    with `q` abstracting to model query `qm`): there is a model datagram `reply` *delivered* to the
    resolver (`Transit … (some reply)` — origin network-reachable), passing the RFC 5452 anti-spoof
    `accepts` gate and observably agreeing with the processed response; and `reply` is **either** an
    honest answer from the queried server (`serverAt`+`ServerAnswers`+`OnWire`) **or** an off-path
    injection from a different origin (`origin ≠ byteAddrToModel ab`) — the spoofing the bailiwick
    filters defend against. The address bridge `byteAddrToModel` lines up the oracle's byte key with the
    model's `String` server address; `αQuery`/`αResp` bridge the wire query/response to the model. -/
def WorldModels (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat)
    (now : Time) (w : World) : Prop :=
  ∀ (q : VeriDNS.Spec.Format) (id : UInt16) (ab : ByteArray)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format) (qm : Query),
    w.oracle (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Server.withRandomId q id)) ab = some d →
    VeriDNS.Impl.Server.acceptExchanged ab d = some bytes →
    VeriDNS.Impl.Message.decode bytes = .ok resp0 →
    VeriDNS.Impl.Server.sanitizeTtlsCap resp0 = some resp₀ →
    VeriDNS.Impl.Server.acceptResponse (VeriDNS.Impl.Server.withRandomId q id) resp₀ = some resp →
    αQuery q = some qm →

    ( (∃ srv tr ref, serverAt net (byteAddrToModel ab) = some srv ∧
          ServerAnswers srv now [] true qm tr ref ∧
          RespAgree (αResp resp) ref ∧
          linkReach net ns resolverAddr (byteAddrToModel ab) = true ∧

          truncateToCap (negotiatedUdp ednsBuf) qm ref = (ref, false) ∧

          (αResp resp).isReferral = ref.isReferral ∧
          (VeriDNS.Spec.Net.cnameRR (αResp resp).answer = none
            ↔ VeriDNS.Spec.Net.cnameRR ref.answer = none) ∧

          (∀ cn, VeriDNS.Spec.Net.cnameRR (αResp resp).answer = some cn →
            ∃ cn', VeriDNS.Spec.Net.cnameRR ref.answer = some cn' ∧ cn'.rdata = cn.rdata) ∧

          (∀ b ∈ resp.answer.toList, ∃ rr,
            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧

          (∀ b ∈ resp.authority.toList, ∃ rr,
            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧

          (∀ sname : ByteArray, VeriDNS.Impl.Server.respInBailiwick sname resp = true →
            VeriDNS.Impl.Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
              resp.authority sname = (VeriDNS.Spec.Net.referralCut ref).length) ∧

          (∀ b ∈ resp.authority.toList, ∀ rr,
            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
            (rr.type == (2 : BitVec 16)) = true →
            ∃ na, αName rr.rdata = some na
              ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
              ∧ (∀ x ∈ na, x.size ≤ 63)) ∧

          (VeriDNS.Impl.Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority).toList.Nodup ∧

          αSection resp.authority = ref.authority ∧
          αSection resp.additional = ref.additional ∧

          ((resp.header.aa == 1) = ref.aa) ∧

          (∀ b ∈ resp.additional.toList, ∃ rr,
            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧

          ((resp.header.tc == 1) = ref.tc))

      ∨ (∃ (origin : String) (reply : Datagram) (srcPort : Nat),
          origin ≠ byteAddrToModel ab ∧
          Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply) ∧
          accepts (queryDatagram id.toNat resolverAddr (byteAddrToModel ab) srcPort ednsBuf qm) reply
            = true ∧
          RespAgree (αResp resp) reply.msg ∧
          (αResp resp).isReferral = reply.msg.isReferral ∧
          reply.msg.tc = false ∧
          (∀ b ∈ resp.answer.toList, ∃ rr,
            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
          (∀ b ∈ resp.authority.toList, ∃ rr,
            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
          (reply.msg.isReferral = true →
            αSection resp.authority = reply.msg.authority ∧
            αSection resp.additional = reply.msg.additional ∧
            ((resp.header.aa == 1) = reply.msg.aa) ∧
            reply.msg.inBailiwick qm.qname = true ∧
            (∀ b ∈ resp.additional.toList, ∃ rr,
              VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
            (∀ sname : ByteArray, VeriDNS.Impl.Server.respInBailiwick sname resp = true →
              VeriDNS.Impl.Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname
                = (VeriDNS.Spec.Net.referralCut reply.msg).length) ∧

            (∀ b ∈ resp.authority.toList, ∀ rr,
              VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
              (rr.type == (2 : BitVec 16)) = true →
              ∃ na, αName rr.rdata = some na
                ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
                ∧ (∀ x ∈ na, x.size ≤ 63)) ∧

            ((resp.header.tc == 1) = reply.msg.tc))) )

/-! ### C3 branch classifiers — mapping impl classification to model verdicts

  The `ioResumeLoop` induction, at each accepted reply, classifies it exactly as the impl's
  `analyzeResponse` does (answer / referral / cname / retry) and applies the matching model verdict.
  These lemmas are the per-branch maps; the fuel induction (the remaining piece) threads the
  induction-hypothesis `HasVerdict` through them. -/

/-- C3 part (i): wire construction for an honest reply. Given a server's response `honest` and that
    both the server address and the resolver are network-reachable, the reply datagram
    `replyDatagram (queryDatagram …) honest` is delivered (`Transit.deliver`), passes the resolver's
    anti-spoof `accepts` gate (`accepts_reply`), and is on-wire (`OnWire.fromServer`). Shared by every
    honest branch classifier. -/
theorem honest_wire_premises (net : Network) (ns : NetState) (ra : String)
    (addr : String) (id sp ednsBuf : Nat) (qm : Query) (honest : Response)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true) :
    Transit (linkReach net ns ra) addr ra (replyDatagram (queryDatagram id ra addr sp ednsBuf qm) honest)
        (some (replyDatagram (queryDatagram id ra addr sp ednsBuf qm) honest))
      ∧ accepts (queryDatagram id ra addr sp ednsBuf qm)
          (replyDatagram (queryDatagram id ra addr sp ednsBuf qm) honest) = true
      ∧ OnWire (queryDatagram id ra addr sp ednsBuf qm) honest
          (replyDatagram (queryDatagram id ra addr sp ednsBuf qm) honest) :=
  ⟨Transit.deliver _ _ _ hreachS hreachR, accepts_reply _ _ _ _ _ _ _, OnWire.fromServer⟩

/-- **C3 answer-branch classifier (part ii).** Given the honest witnesses
    (`serverAt`+`ServerAnswers`+reachability) plus the classification facts the impl's `analyzeResponse`
    establishes for an answer (the server reply `ref` fits the UDP cap, is not a referral, satisfies the
    CNAME side-condition, untruncated) and a cache miss, the verdict `v` agreeing with `ref` is
    model-justified via `Net.Resolves.answer` (through `answer_hasVerdict`). Builds the wire form with
    `honest_wire_premises`; `hfit` collapses the `truncateToCap` to `ref`. The first concrete C3 branch
    map — the others (refer/cname/retry) follow the same shape with their wrappers. -/
theorem answer_classifier (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id sp : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hnr : ref.isReferral = false)
    (hnc : cnameRR ref.answer = none ∨ q.qtype.covers RRType.cname = true
            ∨ (∃ rr ∈ ref.answer, q.qtype.covers rr.rdata.rtype = true))
    (htc : ref.tc = false)
    (v : Response) (hbridge : RespAgree v { ref with aa := false }) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ht, ha, hw⟩ := honest_wire_premises net ns ra addr id sp ednsBuf q ref hreachS hreachR
  exact answer_hasVerdict net ns ra ednsBuf rttOf addr rest q srv tr ref id sp c hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id ra addr sp ednsBuf q) ref) ht ha
    (by rw [show (truncateToCap (negotiatedUdp ednsBuf) q ref).1 = ref from by rw [hfit]]; exact hw)
    hnr hnc htc v hbridge

/-- **C3 referral-branch classifier (the bug's branch, part ii).** Same shape as `answer_classifier`,
    composing `honest_wire_premises` with `refer_hasVerdict_hv`: given the honest witnesses, the referral
    classification facts (`isReferral`, in-bailiwick, descends-below the server's zone, non-empty glue,
    fresh address, monotone clock), and the recursive sub-resolution's `HasVerdict` (the induction
    hypothesis from the descended cache + glue SLIST), the verdict is justified via `Net.Resolves.refer`.
    Referral uses the *untruncated* `ref` on-wire (no `truncateToCap`), so this is simpler than the
    answer branch. This is the branch whose missing totality hid the original referral cache-poisoning
    bug — now a checked refinement. -/
theorem referral_classifier (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id sp : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (href : ref.isReferral = true)
    (hbail : ref.inBailiwick q.qname = true)
    (hdesc : ref.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : ref.descendsBelow frontier = true)
    (hglue : glueAddresses ref ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String)
    (hsl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref)) ref).referralSlist now' q.qname (q.qname.length + 1)).Subperm sl)
    (hrec : HasVerdict net ns ra ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref)) ref)
        sl q v) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ht, ha, hw⟩ := honest_wire_premises net ns ra addr id sp ednsBuf q ref hreachS hreachR
  exact refer_hasVerdict_hv net ns ra ednsBuf rttOf addr rest q srv tr ref id sp c hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id ra addr sp ednsBuf q) ref) ht ha hw href hbail hdesc frontier hdescF hglue hfresh hmono v sl hsl hrec

/-- HasVerdict-threading form of the *verdict-transforming* `answerCname` branch: the outer verdict `v`
    prepends the CNAME RR `cn` to the recursive sub-resolution's verdict (`v.answer = cn :: vsub.answer`,
    same rcode). Destructures the IH's `HasVerdict`, applies `Net.Resolves.answerCname`, and rebuilds the
    `RespAgree` by transitivity through the prepend. Unlike the output-preserving branches this can't use
    a uniform `*_hv` wrapper — the verdict changes — so it threads the sub-response explicitly. -/
theorem answerCname_hasVerdict_hv (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (resp : Response)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr resp)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns ra) addr ra reply (some reply))
    (hacc : accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id ra addr srcPort ednsBuf q)
        (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
    (hcn : cnameRR reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname { reply.msg with authority := [], additional := [] }))
    (cf : VeriDNS.Spec.Net.Cache) (hcf : VeriDNS.Spec.Net.WriteRefines now' cf cf0)
    (vsub v : Response) (hrc : v.rcode = vsub.rcode) (hva : v.answer = cn :: vsub.answer)
    (hrec : HasVerdict net ns ra ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } vsub) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨tr', sp', tEnd', cout', resp', hres, hag⟩ := hrec
  refine ⟨_, _, _, _, _, Resolves.answerCname addr rest q srv tr resp cn target id srcPort c nsl
    tr' sp' tEnd' cout' resp' hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono
    htc cf0 hcf0 cf hcf hres, ?_⟩
  exact ⟨hrc.trans hag.1, by rw [hva]; exact List.Perm.cons cn hag.2⟩

/-- **C3 cname-branch classifier (the verdict-transforming branch).** Composes `honest_wire_premises`
    with `answerCname_hasVerdict_hv`: given the honest witnesses, the cname classification facts (`ref`
    fits the cap, carries a CNAME the qtype doesn't cover, targeting `target`, untruncated, fresh) and
    the recursive resolution of the CNAME target (the induction hypothesis `vsub`), the outer verdict
    `v = cn :: vsub` is justified via `Net.Resolves.answerCname`. Completes the per-branch classifier
    set (answer/referral/cname honest + the retry wrappers + exhausted). -/
theorem cname_classifier (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (cn : RR) (target : Name) (id sp : Nat) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hcn : cnameRR ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname { ref with authority := [], additional := [] }))
    (cf : VeriDNS.Spec.Net.Cache) (hcf : VeriDNS.Spec.Net.WriteRefines now' cf cf0)
    (vsub v : Response) (hrc : v.rcode = vsub.rcode) (hva : v.answer = cn :: vsub.answer)
    (hrec : HasVerdict net ns ra ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } vsub) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ht, ha, hw⟩ := honest_wire_premises net ns ra addr id sp ednsBuf q ref hreachS hreachR
  exact answerCname_hasVerdict_hv net ns ra ednsBuf rttOf addr rest q srv tr ref cn target id sp c nsl
    hmiss hnmiss hfind hans (replyDatagram (queryDatagram id ra addr sp ednsBuf q) ref) ht ha
    (by rw [show (truncateToCap (negotiatedUdp ednsBuf) q ref).1 = ref from by rw [hfit]]; exact hw)
    hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf vsub v hrc hva hrec

/-- **C3 cname-branch classifier, bridge form** (the `cnameToChase=some` driver terminal's assembly point).
    Same honest witnesses as `cname_classifier`, but takes the recursion as a `Resolves` on the absorbed cache
    and the answer agreement as a `RespAgree` bridge directly (Perm-tolerant), routing through the non-`_hv`
    `answerCname_hasVerdict`. The driver feeds `hrec` = the chased target's cache-hit `Resolves`
    (`Resolves.cacheHit` on `c.absorb …`) and `hbridge` = `respAgree_cname_finished_bridge` (the impl's
    delivered CNAME answer ~ `cn :: final.answer`). This closes the honest CNAME-chase terminal end-to-end. -/
theorem cname_classifier_bridge (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (cn : RR) (target : Name) (id sp : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hcn : cnameRR ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname { ref with authority := [], additional := [] }))
    (cf : VeriDNS.Spec.Net.Cache) (hcf : VeriDNS.Spec.Net.WriteRefines now' cf cf0)
    (hrec : Resolves net ns ra ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ht, ha, hw⟩ := honest_wire_premises net ns ra addr id sp ednsBuf q ref hreachS hreachR
  exact answerCname_hasVerdict net ns ra ednsBuf rttOf addr rest q srv tr ref cn target id sp c nsl
    ftr rpath tEnd cout final hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id ra addr sp ednsBuf q) ref) ht ha
    (by rw [show (truncateToCap (negotiatedUdp ednsBuf) q ref).1 = ref from by rw [hfit]]; exact hw)
    hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec v hbridge

/-- **CNAME-chase base terminal refines (the assembled `cnameToChase=some`, `cnameChain=#[]` case).** With the
    honest WorldModels witnesses, the model CNAME (`hcn`/`htgt`), the chased target's cache-hit recursion
    (`hrec`), and the impl's delivered answer `out = finalizeAnswer st (cacheResponse qf rrs)` (single-link
    chain `st.cnameChain = #[cnBytes]`, served set `Perm`-matching `final.answer`), the impl's CNAME-chase
    terminal yields a `HasVerdict` for `αResp out` — the branch refines `answerCname`. Composes
    `cname_classifier_bridge` (the network + recursion assembly) with `respAgree_cname_finished_bridge` (the
    `v`-agreement). The driver instantiates `hrec := Resolves.cacheHit (c.absorb …) …` and discharges `hperm`
    via `localAnswer_answerHit_modelHit_perm`. -/
theorem cnameChase_base_refines (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (cn : RR) (target : Name) (id sp : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (st : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (qf : VeriDNS.Spec.Format) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (cnBytes : ByteArray) (rrCn : VeriDNS.Spec.ResourceRecord)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hcn : cnameRR ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname { ref with authority := [], additional := [] }))
    (cf : VeriDNS.Spec.Net.Cache) (hcf : VeriDNS.Spec.Net.WriteRefines now' cf cf0)
    (hrec : Resolves net ns ra ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (hstchain : st.cnameChain = #[cnBytes])
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) cnBytes = some rrCn)
    (har : αRR rrCn = some cn)
    (hperm : (αSection (VeriDNS.Impl.Resolver.cacheResponse qf rrs).answer).Perm final.answer)
    (hfinrc : final.rcode = VeriDNS.Spec.Net.RCode.noError) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q
      (αResp (VeriDNS.Impl.Resolver.finalizeAnswer st (VeriDNS.Impl.Resolver.cacheResponse qf rrs))) :=
  cname_classifier_bridge net ns ra ednsBuf rttOf addr rest q srv tr ref cn target id sp c nsl
    ftr rpath tEnd cout final hmiss hnmiss hfind hans hreachS hreachR hfit hcn hqt htgt hfresh hmono htc
    cf0 hcf0 cf hcf hrec
    (αResp (VeriDNS.Impl.Resolver.finalizeAnswer st (VeriDNS.Impl.Resolver.cacheResponse qf rrs)))
    (Refinement.respAgree_cname_finished_bridge st qf rrs cnBytes rrCn cn final hstchain hp har hperm hfinrc)

/-- **Part-(b) consumer bridge: the model answer's CNAME points at the impl-chased target.** Combines the
    WorldModels honest disjunct's `cnameRR`-some conjunct (`hcnsome`) with the impl-side CNAME target fact
    (`cnameRR (αResp resp).answer = some cn0`, `cn0.rdata = RData.cname target'` — produced by
    `cnameRR_some_of_extractCname` from `cnameToChase respA = some target`): the server's model answer `ref`
    carries a CNAME with the SAME target rdata. Discharges `cname_classifier`'s `hcn`/`htgt` for the honest
    CNAME-chase (`cnameToChase=some`) driver terminal. -/
theorem cnameRR_ref_target
    (resp : VeriDNS.Spec.Format) (ref : Response) (target' : Name) (cn0 : RR)
    (hcn0 : cnameRR (αResp resp).answer = some cn0)
    (htgt0 : cn0.rdata = RData.cname target')
    (hcnsome : ∀ cn, cnameRR (αResp resp).answer = some cn →
        ∃ cn', cnameRR ref.answer = some cn' ∧ cn'.rdata = cn.rdata) :
    ∃ cn', cnameRR ref.answer = some cn' ∧ cn'.rdata = RData.cname target' := by
  obtain ⟨cn', hcn', hrd⟩ := hcnsome cn0 hcn0
  exact ⟨cn', hcn', by rw [hrd, htgt0]⟩

/-- The `ServerAnswers.answer` output's answer set provably satisfies the well-formedness the answer
    realizability *assumed* (`howner`/`hmatch`): every record is owned by the query name (`nameEq`) and
    type/class-matches. The answer is `(recordsAt z qname).filter (covers ∧ cls)` and `recordsAt`
    filters by owner, so both fall out by `List.mem_filter`. A C3 integration step: it turns the
    realizability's assumed premises into theorems derivable from the model derivation's structure, part
    of discharging the network oracle premise rather than assuming it. -/
theorem answer_records_match (z : Zone) (qname : Name) (qt : QType) (qcls : RRClass) (r : RR)
    (h : r ∈ (recordsAt z qname).filter (fun r => qt.covers r.rdata.rtype && r.cls == qcls)) :
    nameEq r.owner qname = true ∧ qt.covers r.rdata.rtype = true ∧ (r.cls == qcls) = true := by
  rw [List.mem_filter] at h
  obtain ⟨hrec, hp⟩ := h
  rw [recordsAt, List.mem_filter] at hrec
  rw [Bool.and_eq_true] at hp
  exact ⟨hrec.2, hp.1, hp.2⟩

/-- A response with empty authority is not a referral. The `ServerAnswers.answer`/`wildcard` cases emit
    `authority := []`, so `answer_classifier`'s `hnr : ref.isReferral = false` is *derivable* from the
    model derivation rather than assumed — another classification fact discharged for the C3 integration
    (the answer-branch totality from `WorldModels`, no oracle premise). -/
theorem isReferral_of_authority_nil (r : Response) (h : r.authority = []) : r.isReferral = false := by
  simp [Response.isReferral, h]

/-- A response with a non-empty answer section is never a referral (`isReferral` requires an *empty*
    answer). So in the answer-branch classifier, `hnr : ref.isReferral = false` is derivable directly
    from `ref.answer ≠ []` (which `RespAgree` carries from the impl's non-empty answer) — no need to case
    the `ServerAnswers` derivation. A clean bridge for the answer-path integration of the C3 fuel
    induction. -/
theorem isReferral_of_answer_nonempty (r : Response) (h : r.answer ≠ []) : r.isReferral = false := by
  unfold Response.isReferral
  have : r.answer.isEmpty = false := by
    cases hr : r.answer with
    | nil => exact absurd hr h
    | cons _ _ => rfl
  simp [this]

/-- Every `ServerAnswers` reply is untruncated (`tc = false`): authoritative servers in the model build
    full responses; only the resolver's UDP-cap `truncateToCap` ever sets `tc`. Gives the answer/cname
    classifiers their `htc` premise directly from the model derivation (the CNAME case inherits `tc` from
    the recursive reply; all others emit `tc = false`). Another classification fact discharged for the
    C3 answer-path integration. -/
theorem serverAnswers_tc_false {s : Server} {now : Time} {seen : List Name} {o : Bool} {q : Query}
    {tr : List Step} {resp : Response} (h : ServerAnswers s now seen o q tr resp) :
    resp.tc = false := by
  induction h with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih => exact ih
  | _ => rfl

/-- Filtering a record list cannot introduce a CNAME: if there is no CNAME in `l`, there is none in
    `l.filter p`. Bridges the `ServerAnswers.answer` case's `hnc` (about the unfiltered `recordsAt`) to
    the classifier's `hnc` (about the filtered answer section `recordsAt.filter (covers ∧ cls)`). -/
theorem cnameRR_filter_none {l : List RR} {p : RR → Bool} (h : cnameRR l = none) :
    cnameRR (l.filter p) = none := by
  unfold cnameRR at h ⊢
  rw [List.find?_eq_none] at h ⊢
  intro r hr
  exact h r (List.mem_filter.mp hr).1

/-! ### `MatchMaxEquiv` — the cache-substitution relation for the forward-simulation capstone (GAP 1, B)

  The `(depth, fuel)` soundness induction for `resolveWithIO_total` produces, at each recursive hop, a
  `HasVerdict` over the **impl's** actual cache `αCache state''.cache`, but the model's `refer`/`cname`
  constructors demand the recursive cache be exactly the **model's** `c.absorb …`. These two caches are
  NOT equal: the impl `storeChecked` skips redundant writes (`betterExists`) and replaces same-key
  records, while the model `Cache.insert` is pure-prepend with the §5.4.1 max gate applied at *read*
  time. They agree only on what they *serve*. `MatchMaxEquiv` is the equivalence under which `Resolves`
  is a congruence in its cache argument: it pins the per-key rank-maximal matching records (`topServed`)
  and the three negative/CNAME read predicates — exactly the four channels through which the cache ever
  influences a `Resolves` derivation. It is deliberately at the `topServed` (not `served`/`hit`) level
  because only `topServed`-equality is stable under `absorb` (see `Cache.topServed`). -/
def MatchMaxEquiv (c c' : VeriDNS.Spec.Net.Cache) : Prop :=
  (∀ now q, (c.topServed now q).Perm (c'.topServed now q))
  ∧ (∀ now q, c.negHit now q = c'.negHit now q)
  ∧ (∀ now q, c.negHitNx now q = c'.negHitNx now q)

theorem MatchMaxEquiv.refl (c : VeriDNS.Spec.Net.Cache) : MatchMaxEquiv c c :=
  ⟨fun _ _ => List.Perm.refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem MatchMaxEquiv.symm {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c') :
    MatchMaxEquiv c' c :=
  ⟨fun n q => (h.1 n q).symm, fun n q => (h.2.1 n q).symm, fun n q => (h.2.2 n q).symm⟩

theorem MatchMaxEquiv.trans {c c' c'' : VeriDNS.Spec.Net.Cache}
    (h : MatchMaxEquiv c c') (h' : MatchMaxEquiv c' c'') : MatchMaxEquiv c c'' :=
  ⟨fun n q => (h.1 n q).trans (h'.1 n q), fun n q => (h.2.1 n q).trans (h'.2.1 n q),
   fun n q => (h.2.2 n q).trans (h'.2.2 n q)⟩

/-- **Model-level one-expiry-per-key** (the model image of the impl's `OneExpiryPerKey`): all positive entries
    sharing a `(owner, type, class)` key have the same expiry (`insertedAt + ttl`). The invariant that makes the
    expiry-class eviction `filterPos qf` a WHOLE-KEY drop — so it preserves `MatchMaxEquiv` (a key's `topServed` is
    either fully kept or fully dropped, never reshuffled). -/
def ModelOneExpiry (c : VeriDNS.Spec.Net.Cache) : Prop :=
  ∀ e₁ ∈ c.pos, ∀ e₂ ∈ c.pos, e₁.sameKey e₂.rr = true →
    e₁.insertedAt + e₁.rr.ttl = e₂.insertedAt + e₂.rr.ttl

/-- A `MatchMaxEquiv` is in particular a `CacheRefines` (`topServed` `Perm` ⟹ `Subperm`; negatives equal). Lets the
    existing `MatchMaxEquiv`-based `StateModels` compose with refinement. -/
theorem MatchMaxEquiv.cacheRefines {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c') :
    VeriDNS.Spec.Net.CacheRefines c c' :=
  ⟨fun n q => (h.1 n q).subperm, h.2.1, h.2.2⟩

theorem ModelOneExpiry.filterPos {c : VeriDNS.Spec.Net.Cache} (h : ModelOneExpiry c)
    (qf : VeriDNS.Spec.Net.CacheRR → Bool) : ModelOneExpiry (c.filterPos qf) := by
  intro e₁ he₁ e₂ he₂ hk
  exact h e₁ (List.mem_filter.mp he₁).1 e₂ (List.mem_filter.mp he₂).1 hk

/-- **`topServed` of the expiry-filtered cache is the `topServed` filtered.** When `qf` is constant on each cache
    KEY (which the expiry-class eviction is, by `ModelOneExpiry`: same key ⟹ same expiry ⟹ same `qf`), the filter
    drops whole keys, so the per-key `maxRank` is never reshuffled — hence
    `(c.filterPos qf).topServed = (c.topServed).filter qf`. -/
theorem filterPos_topServed {c : VeriDNS.Spec.Net.Cache} (qf : VeriDNS.Spec.Net.CacheRR → Bool)
    (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (hqf : ∀ e₁ ∈ c.pos, ∀ e₂ ∈ c.pos, e₁.sameKey e₂.rr = true → qf e₁ = qf e₂) :
    (c.filterPos qf).topServed now q = (c.topServed now q).filter qf := by
  unfold VeriDNS.Spec.Net.Cache.topServed
  rw [VeriDNS.Spec.Net.Cache.filterPos_matching]
  simp only [List.filter_filter]
  apply List.filter_congr
  intro e he
  have hmem : ∀ x ∈ c.matching now q, x ∈ c.pos := fun x hx => (List.mem_filter.mp hx).1
  by_cases hqe : qf e = true
  ·
    have hall : ((c.matching now q).filter qf).all
          (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
        = (c.matching now q).all
          (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank) := by
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      constructor
      · intro hf x hx
        by_cases hqx : qf x = true
        · exact hf x (List.mem_filter.mpr ⟨hx, hqx⟩)
        · by_cases hsk : x.sameKey e.rr = true
          · exact absurd (hqf x (hmem x hx) e (hmem e he) hsk) (by rw [hqe]; simpa using hqx)
          · simp [hsk]
      · intro hf x hx
        exact hf x (List.mem_filter.mp hx).1
    rw [hqe, Bool.and_true, Bool.true_and, hall]
  · simp only [Bool.not_eq_true] at hqe
    rw [hqe, Bool.and_false, Bool.false_and]

/-- **`MatchMaxEquiv` is preserved by the expiry-class eviction `filterPos qf`** when `qf` is key-constant on both
    caches (the expiry-class eviction, by `ModelOneExpiry`). `topServed` filters identically on both (per
    `filterPos_topServed`) and `Perm` survives the filter; the negative cache is untouched. This is the bridge
    that closes the over-capacity refer capstone: `αCache(boundExpiry impl) = (αCache impl).filterPos qf`, so the
    model refer rule's `(absorb).filterPos qf` recursive cache stays `MatchMaxEquiv` to the impl's evicted cache. -/
theorem MatchMaxEquiv.filterPos {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (qf : VeriDNS.Spec.Net.CacheRR → Bool)
    (hqf : ∀ e₁ ∈ c.pos, ∀ e₂ ∈ c.pos, e₁.sameKey e₂.rr = true → qf e₁ = qf e₂)
    (hqf' : ∀ e₁ ∈ c'.pos, ∀ e₂ ∈ c'.pos, e₁.sameKey e₂.rr = true → qf e₁ = qf e₂) :
    MatchMaxEquiv (c.filterPos qf) (c'.filterPos qf) := by
  refine ⟨fun now q => ?_, fun now q => ?_, fun now q => ?_⟩
  · rw [filterPos_topServed qf now q hqf, filterPos_topServed qf now q hqf']
    exact (h.1 now q).filter qf
  · rw [VeriDNS.Spec.Net.Cache.filterPos_negHit, VeriDNS.Spec.Net.Cache.filterPos_negHit]
    exact h.2.1 now q
  · rw [VeriDNS.Spec.Net.Cache.filterPos_negHitNx, VeriDNS.Spec.Net.Cache.filterPos_negHitNx]
    exact h.2.2 now q

/-- `MatchMaxEquiv` determines `served` up to `Perm` (per-key max records, post-usability). -/
theorem MatchMaxEquiv.served {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (c.served now q).Perm (c'.served now q) := by
  rw [c.served_eq_topServed_filter, c'.served_eq_topServed_filter]
  exact (h.1 now q).filter _

/-- **`flatMap` congruence up to pointwise `Perm`** (no Mathlib here, so proved from core). If `f a ~ g a` for
    each `a ∈ l`, then `l.flatMap f ~ l.flatMap g`. Combined with `List.Perm.flatMap_right` (Perm of the list,
    same `f`) this gives the full two-sided `flatMap` Perm congruence the SLIST re-derivation needs. -/
theorem perm_flatMap_congr {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a t ih =>
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- **`MatchMaxEquiv` determines the cached NS hosts at a cut up to `Perm`.** `Cache.nsHostsAt` is a
    `filterMap` over `topServed` — exactly the component `MatchMaxEquiv` pins — so the `gluelessNs`
    rule's cache-provenance anchor `hns : nsHost ∈ c.nsHostsAt now zone` transfers under cache
    substitution by `Perm`-preserves-membership. -/
theorem MatchMaxEquiv.nsHostsAt {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (nm : VeriDNS.Spec.Net.Name) :
    (c.nsHostsAt now nm).Perm (c'.nsHostsAt now nm) := by
  unfold VeriDNS.Spec.Net.Cache.nsHostsAt
  exact (h.1 now _).filterMap _

/-- **`MatchMaxEquiv` determines the cache-re-derived referral SLIST up to `Perm`.** `Cache.referralSlist` is
    built entirely from `served` (NS hosts via `nsHostsAt`, glue addresses via `glueAddrsAt`), both `filterMap`s
    of `served`, combined with `flatMap` — all `Perm`-stable. So two `MatchMaxEquiv`-equivalent caches re-derive
    `Perm`-equal SLISTs. This is the lift that turns the impl-vs-`αCache` correspondence into the impl-vs-model
    keystone: `modelSlistOf(impl) .Perm referralSlist(αCache impl) .Perm referralSlist(c)`. -/
theorem MatchMaxEquiv.referralSlist {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (nm : VeriDNS.Spec.Net.Name) (fuel : Nat) :
    (c.referralSlist now nm fuel).Perm (c'.referralSlist now nm fuel) := by
  induction fuel generalizing nm with
  | zero =>
    unfold VeriDNS.Spec.Net.Cache.referralSlist
    exact List.Perm.refl _
  | succ fuel ih =>
    have hns : (c.nsHostsAt now nm).Perm (c'.nsHostsAt now nm) := by
      unfold VeriDNS.Spec.Net.Cache.nsHostsAt
      exact (h.1 now _).filterMap _
    by_cases he : c.nsHostsAt now nm = []
    · have he' : c'.nsHostsAt now nm = [] := by
        rcases hc' : c'.nsHostsAt now nm with _ | ⟨b, s⟩
        · rfl
        · exfalso; have := hns.length_eq; rw [he, hc'] at this; simp at this
      have hb : (c.nsHostsAt now nm).isEmpty = true := by rw [he]; rfl
      have hb' : (c'.nsHostsAt now nm).isEmpty = true := by rw [he']; rfl
      unfold VeriDNS.Spec.Net.Cache.referralSlist
      rw [if_pos hb, if_pos hb']
      cases nm with
      | nil => exact List.Perm.refl _
      | cons l parent => exact ih parent
    · have he' : c'.nsHostsAt now nm ≠ [] := by
        intro hc'
        exact he (by
          rcases hc : c.nsHostsAt now nm with _ | ⟨a, t⟩
          · rfl
          · exfalso; have := hns.length_eq; rw [hc, hc'] at this; simp at this)
      have hbn : ¬((c.nsHostsAt now nm).isEmpty = true) := fun hh => he (List.isEmpty_iff.mp hh)
      have hbn' : ¬((c'.nsHostsAt now nm).isEmpty = true) := fun hh => he' (List.isEmpty_iff.mp hh)
      unfold VeriDNS.Spec.Net.Cache.referralSlist
      rw [if_neg hbn, if_neg hbn']
      exact (List.Perm.flatMap_right _ hns).trans
        (perm_flatMap_congr _ _ _ (fun a _ => by
          unfold VeriDNS.Spec.Net.Cache.glueAddrsAt
          exact (h.1 now _).filterMap _))

/-- `MatchMaxEquiv` determines `hit` up to `Perm` — the positive-cache read predicate
    `cacheHit`/`answer`/`refer`/… consult (DNS RRset order is RFC-unspecified). -/
theorem MatchMaxEquiv.hit {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (c.hit now q).Perm (c'.hit now q) := by
  unfold VeriDNS.Spec.Net.Cache.hit
  rw [c.served_eq_topServed_filter, c'.served_eq_topServed_filter]
  exact ((h.1 now q).filter _).map _

/-- `MatchMaxEquiv` determines `cnameServed` up to `Perm` — so the `Phase 0a` membership premise
    `cn ∈ cnameServed` transfers under cache substitution by `Perm`-preserves-membership. -/
theorem MatchMaxEquiv.cnameServed {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (qname : VeriDNS.Spec.Net.Name) (qcls : RRClass) :
    (c.cnameServed now qname qcls).Perm (c'.cnameServed now qname qcls) := by
  unfold VeriDNS.Spec.Net.Cache.cnameServed
  exact (h.served now _).filterMap _

/-- **The CNAME-chase cache-hit Perm bridge** (part (c) capstone). The impl's `.answerHit` served set
    abstracts to a `Perm` of the MODEL cache's `Cache.hit` (`mc`, related to the impl cache `αCache cache` by
    `MatchMaxEquiv` — the invariant `matchMaxEquiv_absorb_step` threads across the CNAME-reply absorb).
    Composes `localAnswer_answerHit_hit` (served set = `αCache`-hit, under cache well-formedness) with
    `MatchMaxEquiv.hit` (`αCache`-hit ~ `mc`-hit). Feeds `cacheHit_hasVerdict`'s `RespAgree`: the chased
    target's verdict (`answerCname`'s recursive `hrec`) agrees with the impl's served answer up to `Perm`. -/
theorem localAnswer_answerHit_modelHit_perm
    (cache : VeriDNS.Impl.Cache.DnsCache) (mc : VeriDNS.Spec.Net.Cache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname0 : ByteArray) (chain0 visited0 : Array ByteArray)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (h : VeriDNS.Impl.Resolver.localAnswer (C := VeriDNS.Impl.Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache qt qc now fuel sname0 chain0 visited0 = .answerHit sname chain rrs)
    (hqn : αName sname = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
        e.rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ cache.records, e.credibility = VeriDNS.Spec.Trustworthiness.authoritativeSection
            ∨ e.credibility = VeriDNS.Spec.Trustworthiness.authoritySection
            ∨ e.credibility = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hmm : MatchMaxEquiv (αCache cache) mc) :
    (rrs.toList.filterMap αRR).Perm (mc.hit (αTime now) q) := by
  rw [Refinement.localAnswer_answerHit_hit cache qt qc now fuel sname0 chain0 visited0 sname chain rrs q t h
      hqn ht hqq hqc hcanN hvN hwf hcanon hused]
  exact MatchMaxEquiv.hit hmm (αTime now) q

/-! ### `absorb` prepends a cache-independent prefix — the backbone of `MatchMaxEquiv` `absorb`-stability

  `Cache.absorb` (and each of its three `foldl`-of-`insert` section passes) only ever *prepends* new
  entries to `pos`; the prepended list depends on `(now, bw, resp)` but **not** on the cache it is
  applied to. Hence `matching (c.absorb …) = M ++ matching c` with a cache-independent `M`. This is what
  reduces `absorb`-stability of `topServed`-equality to the purely list-combinatorial fact that
  `topOf (M ++ L)` depends on `L` only through `topOf L` (records strictly below a key's max never
  re-enter the max when the same `M` is prepended to both sides). -/

open VeriDNS.Spec (RRType) in
/-- A `foldl` of `Cache.insert` prepends a cache-independent list `N` to `pos`. -/
theorem foldl_insert_pos (now : VeriDNS.Spec.Net.Time) (cred : VeriDNS.Spec.Net.Cred) :
    ∀ (l : List VeriDNS.Spec.Net.RR), ∃ N, ∀ (c : VeriDNS.Spec.Net.Cache),
      (l.foldl (fun a r => a.insert now cred r) c).pos = N ++ c.pos := by
  intro l
  induction l with
  | nil => exact ⟨[], fun c => rfl⟩
  | cons r rs ih =>
    obtain ⟨Nrs, hrs⟩ := ih
    refine ⟨Nrs ++ (if VeriDNS.Spec.Net.cacheable r then
      [(⟨r, now, cred⟩ : VeriDNS.Spec.Net.CacheRR)] else []), fun c => ?_⟩
    simp only [List.foldl_cons]
    rw [hrs (c.insert now cred r)]
    unfold VeriDNS.Spec.Net.Cache.insert
    by_cases hc : VeriDNS.Spec.Net.cacheable r
    · simp only [hc, if_true]; simp
    · simp only [hc]; simp

/-- The per-record contribution of a model `Cache.insert` fold: the singleton prepended `CacheRR` for a
    cacheable record, `[]` otherwise. The model-side analogue of `Refinement.pushOf`. -/
def modelPushOf (now : VeriDNS.Spec.Net.Time) (cred : VeriDNS.Spec.Net.Cred)
    (r : VeriDNS.Spec.Net.RR) : List VeriDNS.Spec.Net.CacheRR :=
  if VeriDNS.Spec.Net.cacheable r then [⟨r, now, cred⟩] else []

/-- **The CONCRETE model insert-fold** (the model-side mirror of `foldl_storeChecked_concrete`). Folding
    `Cache.insert now cred` over `l` prepends, in reverse, exactly the cacheable records:
    `(l.foldl insert c).pos = l.reverse.flatMap (modelPushOf now cred) ++ c.pos`. This pins the model
    `absorb`'s inserted `N` concretely (per section), so the bridge's `extra ~ N` Perm is a comparison of two
    explicit `flatMap`s — the impl's `pushOf` list vs the model's `modelPushOf` list. (The `reverse` is washed
    out by the `Perm`, which `topServed` uses; insert prepends, the impl `store` appends.) -/
theorem foldl_insert_concrete (now : VeriDNS.Spec.Net.Time) (cred : VeriDNS.Spec.Net.Cred)
    (l : List VeriDNS.Spec.Net.RR) (c : VeriDNS.Spec.Net.Cache) :
    (l.foldl (fun a r => a.insert now cred r) c).pos
      = (l.reverse.flatMap (modelPushOf now cred)) ++ c.pos := by
  induction l generalizing c with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih (c.insert now cred r), List.reverse_cons, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    congr 1
    unfold VeriDNS.Spec.Net.Cache.insert modelPushOf
    by_cases hc : VeriDNS.Spec.Net.cacheable r
    · simp only [hc, if_true]; rfl
    · simp only [hc, if_false]; rfl

/-- **The per-raw write-path correspondence (the atom of `extra ~ N`).** For a raw that parses (`hpr`) and
    abstracts (`hαr`), under the no-overflow `hno` (from the TTL cap), the impl's abstracted per-raw push
    equals the model's per-record insert contribution: `(pushOf cred now b).filterMap αCacheRR = modelPushOf
    now.toNat (αCred cred) r`. Both sides yield `[⟨r, now.toNat, αCred cred⟩]` for a cacheable record and `[]`
    for `ttl=0` — the cacheability gates agree by `cacheable_corr`, the record/cred/expiry by `αCacheRR_push`.
    Lifting this over the (bailiwick-filtered) section list gives the per-section `extra ~ N`. -/
theorem pushOf_filterMap_eq_modelPushOf {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    {r : VeriDNS.Spec.Net.RR} (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hαr : αRR rr = some r)
    (hno : (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    (pushOf cred now b).filterMap αCacheRR = modelPushOf now.toNat (αCred cred) r := by
  unfold modelPushOf
  rw [cacheable_corr hαr]
  by_cases htt : (rr.ttl == 0) = true
  · rw [pushOf_zero cred now hpr htt]
    simp only [List.filterMap_nil, htt, Bool.not_true, Bool.false_eq_true, if_false]
  · have htf : (rr.ttl == 0) = false := by simpa using htt
    rw [pushOf_pos cred now hpr htf, List.filterMap_cons, αCacheRR_push rr r now cred hαr hno]
    simp only [List.filterMap_nil, htf, Bool.not_false, if_true]

/-- **The section lift (the per-raw atom over a whole list).** The impl's abstracted section write equals a
    `modelPushOf` `flatMap` over the abstracted section:
    `(l.flatMap (pushOf cred now)).filterMap αCacheRR = (l.filterMap (parseRaw · >>= αRR)).flatMap (modelPushOf
    now.toNat (αCred cred))`. Note `l.filterMap (parseRaw · >>= αRR)` is exactly `αSection l` (its definition).
    Crucially this needs only the no-overflow `hno` (per parsing raw, from the TTL cap) — NOT full `WfRR`
    abstractability: a raw that fails to abstract contributes `[]` on BOTH sides (impl: `αCacheRR` returns
    `none` so `filterMap` drops it; model: `filterMap (·>>=αRR)` drops it). So the impl referral section write,
    abstracted, IS the model `modelPushOf` fold over the abstracted (and — via `αSection_bailiwickRaws_eq` —
    bailiwick-filtered) section; the model `N` is the same list up to the `reverse` that `Perm` absorbs. -/
theorem flatMap_pushOf_filterMap_eq (l : List ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hno : ∀ b ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    (l.flatMap (pushOf cred now)).filterMap αCacheRR
      = (l.filterMap (fun b => (VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b).bind αRR)).flatMap
          (modelPushOf now.toNat (αCred cred)) := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih (fun x hx => hno x (List.mem_cons_of_mem _ hx)),
      List.filterMap_cons]
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [pushOf_none cred now hpr]; simp [hpr]
    | some rr =>
      simp only [hpr, Option.bind_some]
      cases hαr : αRR rr with
      | none =>
        have hz : (pushOf cred now b).filterMap αCacheRR = [] := by
          by_cases htt : (rr.ttl == 0) = true
          · rw [pushOf_zero cred now hpr htt]; rfl
          · have htf : (rr.ttl == 0) = false := by simpa using htt
            rw [pushOf_pos cred now hpr htf, List.filterMap_cons]
            simp only [αCacheRR, hαr, Option.map_none, List.filterMap_nil]
        rw [hz]; simp
      | some r =>
        rw [pushOf_filterMap_eq_modelPushOf cred now hpr hαr (hno b (by simp) rr hpr)]
        simp [List.flatMap_cons]

/-- **The per-section `extra ~ N` (one referral section).** The impl's abstracted bailiwick-filtered section
    write permutes the model `absorb`'s inserted records for that section: `((bailiwickRaws cut sec).flatMap
    (pushOf cred now)).filterMap αCacheRR ~ ((αSection sec).filter (isAncestor bwN)).reverse.flatMap (modelPushOf
    now.toNat (αCred cred))`. Assembles the section lift (`flatMap_pushOf_filterMap_eq`, identifying
    `filterMap (·>>=αRR) = αSection`), the bailiwick filter (`αSection_bailiwickRaws_eq`), and the `reverse`
    `Perm` (`List.flatMap` respects `l.reverse ~ l`). Needs only `αName cut = some bwN` and the per-raw
    no-overflow `hno` — the cred (`αCred`), cacheability, abstraction, and bailiwick all already discharged in
    the atoms. Two of these (authority + additional) `Perm`-append to the full refer `extra ~ N`. -/
theorem section_extra_perm (sec : Array ByteArray) (cut : ByteArray) (bwN : VeriDNS.Spec.Net.Name)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (hcut : αName cut = some bwN)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut sec)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut sec),
        RRCanonMappable e) :
    (((VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut sec)).toList.flatMap
        (pushOf cred now)).filterMap αCacheRR).Perm
      ((VeriDNS.Spec.Net.normalizeTTL
          ((αSection sec).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap
        (modelPushOf now.toNat (αCred cred))) := by
  rw [flatMap_pushOf_filterMap_eq _ cred now hno]
  have hb : (VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut sec)).toList.filterMap
      (fun b => (VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b).bind αRR)
      = VeriDNS.Spec.Net.normalizeTTL
          ((αSection sec).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner)) := by
    have hαs : (VeriDNS.Impl.Cache.normRaws
          (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut sec)).toList.filterMap
        (fun b => (VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b).bind αRR)
        = αSection (VeriDNS.Impl.Cache.normRaws
          (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut sec)) := by
      unfold αSection
      congr 1
      funext b
      cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
    rw [hαs, αSection_normRaws _ hcanmap, αSection_bailiwickRaws_eq cut bwN sec hcut]
  rw [hb]
  exact (List.reverse_perm _).symm.flatMap_right _

/-- **The full refer-hop `extra ~ N` (both sections).** The impl's complete referral write — authority
    (`credAuthority aa`) then additional (`credAdditional`), bailiwick-filtered to `cut`, abstracted —
    permutes the model `absorb`'s inserted records. Combines two `section_extra_perm`s with `List.Perm.append`,
    using `αCred (credAuthority aa) = αCred credAdditional = Cred.additional` under `aa = false` (the
    `isReferral` discipline). The LHS is exactly `two_section_αCache_pos`'s `extra` (minus `(αCache c).pos`)
    and the RHS is `absorb_referral_pos`'s `N` (minus `c.pos`), so this is the `hposperm` that
    `topServed_bridge_of_pos_perm` consumes — the refer-hop write-path Perm, complete and axiom-clean. -/
theorem refer_extra_perm (authority additional : Array ByteArray) (cut : ByteArray)
    (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (aa : Bool) (haa : aa = false)
    (hcut : αName cut = some bwN)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hnoD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmapA : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut authority), RRCanonMappable e)
    (hcanmapD : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut additional), RRCanonMappable e) :
    (((VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut authority)).toList.flatMap
          (pushOf (VeriDNS.Impl.Resolver.credAuthority aa) now)).filterMap αCacheRR
      ++ ((VeriDNS.Impl.Cache.normRaws
          (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut additional)).toList.flatMap
          (pushOf VeriDNS.Impl.Resolver.credAdditional now)).filterMap αCacheRR).Perm
    ((VeriDNS.Spec.Net.normalizeTTL
          ((αSection authority).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap
          (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)
      ++ (VeriDNS.Spec.Net.normalizeTTL
          ((αSection additional).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap
          (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) := by
  have hcA : αCred (VeriDNS.Impl.Resolver.credAuthority aa) = VeriDNS.Spec.Net.Cred.additional := by
    rw [αCred_credAuthority]; simp [haa]
  have hpA := section_extra_perm authority cut bwN (VeriDNS.Impl.Resolver.credAuthority aa) now hcut hnoA hcanmapA
  rw [hcA] at hpA
  have hpD := section_extra_perm additional cut bwN VeriDNS.Impl.Resolver.credAdditional now hcut hnoD hcanmapD
  rw [αCred_credAdditional] at hpD
  exact hpA.append hpD

/-- **The refer-case `absorb` collapses to two same-credibility section folds.** When the response is a
    referral (`isReferral`: empty answer, `aa = false`, NS-but-no-SOA in authority), `Cache.absorb` reduces
    to inserting the bailiwick-filtered authority then additional sections, BOTH at `Cred.additional`: the
    answer fold is over `[]` (no answer to copy), `authCred` collapses to `additional` (`aa = false`), and the
    SOA-filter on authority is vacuous (`isReferral` forbids SOA). This is what makes the impl refer branch —
    which caches *only* authority+additional (never the answer) at `credAuthority`/`credAdditional`
    (= `additionalAuthoritative`, `αCred`-image `additional`) — refine the model: the "model absorbs the
    answer the impl drops" mismatch provably cannot arise, because a referral has no answer. -/
theorem absorb_referral_eq (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response)
    (href : resp.isReferral = true) :
    c.absorb now bw resp
      = (VeriDNS.Spec.Net.normalizeTTL
            (resp.authority.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner))).foldl
            (fun a r => a.insert now VeriDNS.Spec.Net.Cred.additional r)
          ((VeriDNS.Spec.Net.normalizeTTL
              (resp.additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner))).foldl
            (fun a r => a.insert now VeriDNS.Spec.Net.Cred.additional r) c) := by
  unfold VeriDNS.Spec.Net.Response.isReferral at href
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at href
  obtain ⟨⟨⟨⟨hempty, haa⟩, hrc⟩, hns⟩, hsoa⟩ := href
  have hans : resp.answer = [] := List.isEmpty_iff.mp hempty
  have hauth : resp.authority.filter (fun r => r.rdata.rtype != RRType.soa) = resp.authority := by
    apply List.filter_eq_self.mpr
    intro r hr
    have hne : (r.rdata.rtype == RRType.soa) = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact absurd (List.any_eq_true.mpr ⟨r, hr, hc⟩) (by rw [hsoa]; simp)
    show (r.rdata.rtype != RRType.soa) = true
    rw [show (r.rdata.rtype != RRType.soa) = !(r.rdata.rtype == RRType.soa) from rfl, hne,
      Bool.not_false]
  unfold VeriDNS.Spec.Net.Cache.absorb
  simp only [haa, hans, hauth, List.filter_nil, VeriDNS.Spec.Net.normalizeTTL, List.map_nil,
    List.foldl_nil, Bool.false_eq_true, if_false, ite_false, reduceIte]

/-- **The model `absorb`'s positive records `N`, concretely, for a referral.** Composing `absorb_referral_eq`
    (two same-cred section folds) with `foldl_insert_concrete` (each fold = reverse-`flatMap modelPushOf`):
    `(c.absorb now bw resp).pos = authority-N ++ additional-N ++ c.pos`, where each section-`N` is
    `(section.filter (isAncestor bw)).reverse.flatMap (modelPushOf now Cred.additional)`. This is the model
    side of the refer-hop `extra ~ N` (the `N` of `absorb_pos_append`, specialized to the referral case); each
    `section-N` is exactly the RHS of `section_extra_perm` (with `αCred cred = additional`, since `aa = false`
    under `isReferral`). Two `List.Perm.append`s of `section_extra_perm` then give the full `extra ~ N`. -/
theorem absorb_referral_pos (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response) (href : resp.isReferral = true) :
    (c.absorb now bw resp).pos
      = ((VeriDNS.Spec.Net.normalizeTTL
            (resp.authority.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner))).reverse.flatMap
            (modelPushOf now VeriDNS.Spec.Net.Cred.additional))
        ++ ((VeriDNS.Spec.Net.normalizeTTL
            (resp.additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner))).reverse.flatMap
            (modelPushOf now VeriDNS.Spec.Net.Cred.additional))
        ++ c.pos := by
  rw [absorb_referral_eq c now bw resp href, foldl_insert_concrete, foldl_insert_concrete,
    List.append_assoc]

/-- **The model `absorb`'s positive records `N`, concretely, for an ANSWER-ONLY response** (the answerCname
    hop, after the model restriction: a CNAME chase absorbs only the answer at bailiwick `q.qname`). With the
    authority/additional sections empty, `absorb` collapses to the single answer fold at `ansCred = if aa then
    authoritative else glue`: `(c.absorb now bw { resp with authority := [], additional := [] }).pos =
    (resp.answer.filter (isAncestor bw)).reverse.flatMap (modelPushOf now ansCred) ++ c.pos`. This is the model
    side of the answerCname-hop `extra ~ N`; the impl side is one `cacheRRs_αCache_pos` over
    `bailiwickRaws sname resp.answer` at `credAnswer aa` (`αCred (credAnswer aa) = ansCred`). -/
theorem absorb_answerOnly_pos (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response) :
    (c.absorb now bw { resp with authority := [], additional := [] }).pos
      = ((VeriDNS.Spec.Net.normalizeTTL
            (resp.answer.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner))).reverse.flatMap
            (modelPushOf now (if resp.aa then VeriDNS.Spec.Net.Cred.authoritative
                                          else VeriDNS.Spec.Net.Cred.glue)))
        ++ c.pos := by
  unfold VeriDNS.Spec.Net.Cache.absorb
  simp only [List.filter_nil, VeriDNS.Spec.Net.normalizeTTL, List.map_nil, List.foldl_nil]
  rw [foldl_insert_concrete]

/-- **A zero-TTL record is never fresh (the wash-out of the `cacheable` mismatch).** The model `Cache.insert`
    drops non-cacheable (`ttl = 0`) records (`cacheable r = 0 < r.ttl`), but the impl `store` pushes every
    bailiwick record unconditionally — so `extra` (impl pushes) carries `ttl=0` records that the model's `N`
    omits, and a naive `extra ~ N` is FALSE. It doesn't matter: a `ttl=0` cache entry has `fresh nowT =
    (nowT < insertedAt + 0) = (nowT < insertedAt)`, which is `false` for any read time `nowT ≥ insertedAt`
    (cache clock monotone). So these records are filtered out by `Cache.matching`'s freshness gate and never
    reach `topServed`. The bridge's `extra ~ N` is therefore required only AFTER the fresh filter, where the
    `ttl=0` surplus vanishes — this lemma is the fact that licenses dropping them. -/
theorem not_fresh_of_ttl_zero (e : VeriDNS.Spec.Net.CacheRR) (nowT : VeriDNS.Spec.Net.Time)
    (h0 : e.rr.ttl = 0) (hle : e.insertedAt ≤ nowT) :
    e.fresh nowT = false := by
  unfold VeriDNS.Spec.Net.CacheRR.fresh
  rw [h0, Nat.add_zero, Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  exact Nat.not_lt.mpr hle

open VeriDNS.Spec (RRType) in
/-- `Cache.absorb` prepends a cache-independent list `N` to `pos` (composing the three section folds). -/
theorem absorb_pos_append (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) :
    ∃ N, ∀ (c : VeriDNS.Spec.Net.Cache), (c.absorb now bw resp).pos = N ++ c.pos := by
  obtain ⟨N1, h1⟩ := foldl_insert_pos now VeriDNS.Spec.Net.Cred.additional
    (VeriDNS.Spec.Net.normalizeTTL
      (resp.additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner)))
  obtain ⟨N2, h2⟩ := foldl_insert_pos now
    (if resp.aa then VeriDNS.Spec.Net.Cred.authority else VeriDNS.Spec.Net.Cred.additional)
    (VeriDNS.Spec.Net.normalizeTTL ((resp.authority.filter (fun r => r.rdata.rtype != RRType.soa)).filter
      (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner)))
  obtain ⟨N3, h3⟩ := foldl_insert_pos now
    (if resp.aa then VeriDNS.Spec.Net.Cred.authoritative else VeriDNS.Spec.Net.Cred.glue)
    (VeriDNS.Spec.Net.normalizeTTL
      (resp.answer.filter (fun r => VeriDNS.Spec.Net.isAncestor bw r.owner)))
  refine ⟨N3 ++ N2 ++ N1, fun c => ?_⟩
  unfold VeriDNS.Spec.Net.Cache.absorb
  simp only
  rw [h3, h2, h1]
  simp [List.append_assoc]

/-- `matching` of an absorbed cache is a cache-independent prefix `M` followed by the original
    `matching` (filter distributes over the `absorb`-prepended `pos`). -/
theorem matching_absorb_append (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    ∃ M, ∀ (c : VeriDNS.Spec.Net.Cache),
      (c.absorb now bw resp).matching now' q = M ++ c.matching now' q := by
  obtain ⟨N, hN⟩ := absorb_pos_append now bw resp
  refine ⟨N.filter (fun e => e.fresh now' && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
                          && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)), fun c => ?_⟩
  unfold VeriDNS.Spec.Net.Cache.matching
  rw [hN c, List.filter_append]

/-! ### The combinatorial core: `topOf` and the max-achieved lemma

  `topOf L` is the per-key rank-maximal sublist of `L` (`Cache.topServed = topOf ∘ matching`). The crux
  of `absorb`-stability is that `topOf (M ++ L)` depends on `L` only through `topOf L`, which rests on
  the **max-achieved** lemma: every record in `L` is dominated, at its key, by a record that lies in
  `topOf L`. That in turn needs `CacheRR.sameKey` to be an equivalence on the record key (reflexive,
  transitive), bottoming out in `==`-reflexivity on the `RRType`/`RRClass` enums. -/

/-- `(a == b) = true → a = b` on `RRType` (the 62-constructor enum is `deriving BEq` but not
    `LawfulBEq`, so this is by exhaustive case split, off-diagonal by `decide`). -/
theorem rrtype_eq_of_beq : ∀ {a b : RRType}, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- `(a == b) = true → a = b` on `RRClass`. -/
theorem rrclass_eq_of_beq : ∀ {a b : RRClass}, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **NS-predicate correspondence.** For an abstracting record (`αRR rr = some r`), the impl's wire NS test
    (`rr.type == 2`) agrees as a Bool with the model's NS test (`r.rdata.rtype == ns`). The per-record core of
    the `referralCutRaw`↔`referralCut` cut-name alignment: both `findSome?`/`find?` over the authority section
    select on equivalent NS predicates, so they pick corresponding records. -/
theorem nsPred_corr {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (h : αRR rr = some r) :
    (rr.type == (2 : BitVec 16)) = (r.rdata.rtype == RRType.ns) := by
  have hrt : αType rr.type = some r.rdata.rtype := αRR_rtype rr r h
  have h2 : αType (2 : BitVec 16) = some RRType.ns := by rfl
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro he
    have hty : rr.type = 2 := eq_of_beq he
    rw [hty, h2] at hrt
    have : r.rdata.rtype = RRType.ns := (Option.some.inj hrt).symm
    rw [this]; decide
  · intro he
    have hns : r.rdata.rtype = RRType.ns := rrtype_eq_of_beq he
    rw [hns] at hrt
    have hty : rr.type = 2 := αType_injective hrt h2
    rw [hty]; decide

/-- **The `referralCutRaw`↔`referralCut` cut-name alignment (keystone of the refer-branch bailiwick).** Under
    the decode-validity invariant — every authority raw parses and fully abstracts (`hwf`) — and the presence
    of at least one NS record (`hns`, guaranteed by `isReferral`), the impl's `findSome?` (first NS owner
    *bytes*) and the model's `find?` over `αSection` (first NS *record*) select the SAME record `r`: the model
    `find?` returns `some r`, and `αName` of the impl's extracted cut bytes is `some r.owner`. Hence the impl
    cut abstracts to exactly the model `referralCut` — the two bailiwick filters coincide. The `αSection`
    `filterMap` cannot desync `find?` from `findSome?` because `hwf` forbids any drop. -/
theorem referralCut_align (l : List ByteArray)
    (hwf : ∀ b ∈ l, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
            ∧ (αRR rr).isSome = true)
    (hns : ∃ b ∈ l, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
            ∧ (rr.type == (2 : BitVec 16)) = true) :
    ∃ r, (l.filterMap (fun b => match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
            | some rr => αRR rr | none => none)).find? (fun r => r.rdata.rtype == RRType.ns) = some r
        ∧ αName (match l.findSome? (fun b =>
              match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
              | some rr => if rr.type == (2 : BitVec 16) then some rr.name else none | none => none) with
            | some o => o | none => ByteArray.empty) = some r.owner := by
  induction l with
  | nil => obtain ⟨b, hb, _⟩ := hns; exact absurd hb (by simp)
  | cons b t ih =>
    obtain ⟨rr, hpr, hsome⟩ := hwf b (by simp)
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
    by_cases hty : (rr.type == (2 : BitVec 16)) = true
    · have hp : (r.rdata.rtype == RRType.ns) = true := by rw [← nsPred_corr hr]; exact hty
      refine ⟨r, ?_, ?_⟩
      · simp only [List.filterMap_cons, hpr, hr, List.find?_cons, hp]
      · simp only [List.findSome?_cons, hpr, hty, if_true]
        exact (αRR_fields rr r hr).1
    · have hpf : (r.rdata.rtype == RRType.ns) = false := by
        rw [← nsPred_corr hr]; exact Bool.eq_false_iff.mpr hty
      have htf : (rr.type == (2 : BitVec 16)) = false := Bool.eq_false_iff.mpr hty
      have hnst : ∃ b ∈ t, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
              ∧ (rr.type == (2 : BitVec 16)) = true := by
        obtain ⟨b', hb', rr', hpr', hty'⟩ := hns
        rcases List.mem_cons.mp hb' with rfl | hbt
        · rw [hpr] at hpr'; obtain rfl := Option.some.inj hpr'; exact absurd hty' hty
        · exact ⟨b', hbt, rr', hpr', hty'⟩
      obtain ⟨r', hfind', himpl'⟩ := ih (fun x hx => hwf x (by simp [hx])) hnst
      refine ⟨r', ?_, ?_⟩
      · simp only [List.filterMap_cons, hpr, hr, List.find?_cons, hpf]; exact hfind'
      · simp only [List.findSome?_cons, hpr, htf, if_false]; exact himpl'

/-- `CacheRR.sameKey` is reflexive (a record shares its own key). -/
theorem cacheRR_sameKey_refl (e : VeriDNS.Spec.Net.CacheRR) : e.sameKey e.rr = true := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey
  simp [VeriDNS.Spec.Net.nameEq_refl, rrtype_beq_self, rrclass_beq_self]

/-- `CacheRR.sameKey` is transitive through the record key. -/
theorem cacheRR_sameKey_trans {e1 e2 : VeriDNS.Spec.Net.CacheRR} {r : VeriDNS.Spec.Net.RR}
    (h1 : e1.sameKey e2.rr = true) (h2 : e2.sameKey r = true) : e1.sameKey r = true := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at h1 h2 ⊢
  simp only [Bool.and_eq_true] at h1 h2 ⊢
  obtain ⟨⟨hn1, ht1⟩, hc1⟩ := h1
  obtain ⟨⟨hn2, ht2⟩, hc2⟩ := h2
  exact ⟨⟨VeriDNS.Spec.Net.nameEq_trans hn1 hn2, by rw [rrtype_eq_of_beq ht1]; exact ht2⟩,
         by rw [rrclass_eq_of_beq hc1]; exact hc2⟩

/-- The per-key rank-maximal sublist of a `CacheRR` list (`Cache.topServed = topOf ∘ matching`). -/
def topOf (L : List VeriDNS.Spec.Net.CacheRR) : List VeriDNS.Spec.Net.CacheRR :=
  L.filter (fun e => L.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))

theorem topServed_eq_topOf (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (q : VeriDNS.Spec.Net.Query) : c.topServed now q = topOf (c.matching now q) := rfl

theorem ble_self (n : Nat) : Nat.ble n n = true := Nat.ble_eq.mpr (Nat.le_refl _)

/-- A non-empty `CacheRR` list has a rank-maximal element. -/
theorem list_has_max_rank : ∀ (L : List VeriDNS.Spec.Net.CacheRR), L ≠ [] →
    ∃ em ∈ L, ∀ x ∈ L, Nat.ble x.cred.rank em.cred.rank = true := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _
    cases rest with
    | nil => exact ⟨a, by simp, by intro x hx; rw [List.mem_singleton.mp hx]; exact ble_self _⟩
    | cons b rs =>
      obtain ⟨em', hem', hmax'⟩ := ih (by simp)
      by_cases hcmp : Nat.ble em'.cred.rank a.cred.rank = true
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ble_self _
        · exact Nat.ble_eq.mpr (Nat.le_trans (Nat.ble_eq.mp (hmax' x hx')) (Nat.ble_eq.mp hcmp))
      · refine ⟨em', List.mem_cons_of_mem _ hem', ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.ble_eq.mpr (Nat.le_of_not_le (fun h => hcmp (Nat.ble_eq.mpr h)))
        · exact hmax' x hx'

/-- **Max-achieved.** Every record of `L` is dominated, at its key, by a record lying in `topOf L`.
    This is what makes a key's max *rank* (hence the result of a future `absorb`) a function of `topOf L`
    alone — the structural fact behind `MatchMaxEquiv` `absorb`-stability. -/
theorem exists_dom_in_topOf (L : List VeriDNS.Spec.Net.CacheRR) (e2 : VeriDNS.Spec.Net.CacheRR)
    (he2 : e2 ∈ L) :
    ∃ em ∈ topOf L, em.sameKey e2.rr = true ∧ Nat.ble e2.cred.rank em.cred.rank = true := by
  have he2cls : e2 ∈ L.filter (fun e => e.sameKey e2.rr) :=
    List.mem_filter.mpr ⟨he2, cacheRR_sameKey_refl e2⟩
  obtain ⟨em, hemcls, hmax⟩ := list_has_max_rank (L.filter (fun e => e.sameKey e2.rr))
    (by intro h; rw [h] at he2cls; simp at he2cls)
  have heml : em ∈ L := (List.mem_filter.mp hemcls).1
  have hemkey : em.sameKey e2.rr = true := (List.mem_filter.mp hemcls).2
  refine ⟨em, ?_, hemkey, hmax e2 he2cls⟩
  rw [topOf, List.mem_filter]
  refine ⟨heml, ?_⟩
  rw [List.all_eq_true]
  intro x hx
  rw [Bool.or_eq_true]
  by_cases hk : x.sameKey em.rr = true
  · right
    exact hmax x (List.mem_filter.mpr ⟨hx, cacheRR_sameKey_trans hk hemkey⟩)
  · left
    simp only [Bool.not_eq_true] at hk
    simp [hk]

/-! ### The `topOf` congruence and `topServed` `absorb`-stability

  With the max-achieved lemma in hand, dominating all of `L` at a key equals dominating all of `topOf L`
  (`all_eq_topOf_all`), and hence `topOf (M ++ L)` is a function of `L` only through `topOf L`
  (`topOf_append_congr`). Composed with `matching_absorb_append` this yields the keystone:
  `topServed`-equality is preserved by `absorb` (`topServed_absorb_congr`) — the positive-cache half of
  `MatchMaxEquiv` `absorb`-stability, the piece that two prior turns proved was *not* available at the
  `hit`/`served` level. -/

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Dominating all of `L` at `e`'s key = dominating all of `topOf L` at `e`'s key (a key's maximum
    rank is witnessed inside `topOf L`). The bridge that makes `topOf (M ++ ·)` factor through `topOf`. -/
theorem all_eq_topOf_all (L : List VeriDNS.Spec.Net.CacheRR) (e : VeriDNS.Spec.Net.CacheRR) :
    L.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
      = (topOf L).all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank) := by
  apply bool_ext
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro hL e2 he2
    exact hL e2 (List.mem_filter.mp (by rw [← topOf]; exact he2)).1
  · intro hT e2 he2
    rw [Bool.or_eq_true]
    by_cases hk : e2.sameKey e.rr = true
    · right
      obtain ⟨em, hem, hemk, hle⟩ := exists_dom_in_topOf L e2 he2
      have hgg := hT em hem
      rw [Bool.or_eq_true] at hgg
      have hemke : em.sameKey e.rr = true := cacheRR_sameKey_trans hemk hk
      rcases hgg with hgg | hgg
      · exact absurd (hemke ▸ hgg) (by decide)
      · exact Nat.ble_eq.mpr (Nat.le_trans (Nat.ble_eq.mp hle) (Nat.ble_eq.mp hgg))
    · left; simp only [Bool.not_eq_true] at hk; simp [hk]

/-- `topOf (M ++ X)` decomposes into an `M`-part (whose `X`-domination factors through `topOf X`) and a
    `(topOf X)`-part. The structural identity behind the congruence. -/
theorem topOf_append_key (M X : List VeriDNS.Spec.Net.CacheRR) :
    topOf (M ++ X)
      = M.filter (fun e => M.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
            && (topOf X).all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
        ++ (topOf X).filter (fun e =>
            M.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) := by
  rw [topOf]
  have hall : ∀ e : VeriDNS.Spec.Net.CacheRR,
      (M ++ X).all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
        = (M.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
           && X.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) := by
    intro e; rw [List.all_append]
  rw [List.filter_congr (fun e _ => hall e), List.filter_append]
  congr 1
  · apply List.filter_congr; intro e _; rw [all_eq_topOf_all X e]
  · rw [topOf, List.filter_filter]

/-- **The `topOf` congruence.** `topOf (M ++ L)` depends on `L` only through `topOf L`. -/
theorem topOf_append_congr {M L L' : List VeriDNS.Spec.Net.CacheRR} (h : topOf L = topOf L') :
    topOf (M ++ L) = topOf (M ++ L') := by
  rw [topOf_append_key, topOf_append_key, h]

/-! ### `Perm`-foundations for the order-robust `MatchMaxEquiv` (the (B)(3) ordering fix)

  `αCache` preserves the impl's `Array` push order while the model `absorb`/`insert` prepend, so the
  impl-store and model-absorb caches are *reverse-ordered* — `topServed`-as-LIST equality cannot bridge
  them. DNS RRset order is RFC-unspecified, so the faithful fix is to make `MatchMaxEquiv` (and
  `RespAgree`) compare answers up to `List.Perm`. These are the keystones that let the committed
  list-equality forms of (B)(1)/(B)(2) port to permutation: `topOf` is `Perm`-congruent (`topOf_perm`)
  and the `topOf (M ++ ·)` congruence holds up to `Perm` (`topOf_append_perm`) — because the per-key-max
  predicate is membership-only (hence `Perm`-invariant, `perm_all`) and `topOf`/`filter` commute with
  `Perm`. -/

/-- **`foldl` of a left-commutative operation is `Perm`-invariant** (the reusable keystone for any
    canonical/order-invariant *single-element* selector — the `addressOf`/`cnameAt` canonicalization that
    Phase 0 of the `resolveWithIO_total` plan needs, since this Lean toolchain lacks Mathlib's
    `List.Perm` fold/sort lemmas). A min-by-key pick is exactly such a `foldl`. -/
theorem perm_foldl_eq {α β : Type} {f : β → α → β}
    (lcomm : ∀ b x y, f (f b x) y = f (f b y) x)
    {l1 l2 : List α} (h : l1.Perm l2) (acc : β) : l1.foldl f acc = l2.foldl f acc := by
  induction h generalizing acc with
  | nil => rfl
  | cons x h ih => exact ih (f acc x)
  | swap x y l => simp only [List.foldl_cons]; rw [lcomm acc x y]
  | trans h1 h2 ih1 ih2 => exact (ih1 acc).trans (ih2 acc)

/-- `List.all` is `Perm`-invariant (it quantifies over membership only). -/
theorem perm_all {α : Type} {L L' : List α} (f : α → Bool) (h : L.Perm L') : L.all f = L'.all f := by
  apply bool_ext
  rw [List.all_eq_true, List.all_eq_true]
  exact ⟨fun hL x hx => hL x (h.mem_iff.mpr hx), fun hL x hx => hL x (h.mem_iff.mp hx)⟩

/-- **General self-referential-filter `Perm`-congruence**: filtering a list by a predicate `fun e => L.all
    (g e)` that scans the WHOLE list is `Perm`-congruent. Generalises `topOf_perm` (its `g` is the per-key
    max-rank test) to ANY per-key argmax — in particular the `(rank, insertedAt)`-lex test the warm-cache
    read-side dedup needs (`Cache.topServed` keeping the freshest highest-cred RRset per key). Composed with
    `Net.dedup_perm`, this gives the `Perm`-stability of `dedup (matching.filter (per-key lex-argmax))`, so the
    existing bridge lemmas (which produce `topServed`-`Perm`) still feed `MatchMaxEquiv` after the dedup wrap. -/
theorem filter_self_perm {α : Type} {L L' : List α} (g : α → α → Bool) (h : L.Perm L') :
    (L.filter (fun e => L.all (g e))).Perm (L'.filter (fun e => L'.all (g e))) := by
  have hc : L.filter (fun e => L.all (g e)) = L.filter (fun e => L'.all (g e)) := by
    apply List.filter_congr
    intro e _
    rw [perm_all (g e) h]
  rw [hc]
  exact h.filter _

/-- **`topOf` is `Perm`-congruent**: permuting the input permutes the per-key-max sublist. The keystone
    that ports `topServed`-equality reasoning to `topServed`-permutation. -/
theorem topOf_perm {L L' : List VeriDNS.Spec.Net.CacheRR} (h : L.Perm L') :
    (topOf L).Perm (topOf L') := by
  unfold topOf
  have hcongr : L.filter (fun e => L.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
      = L.filter (fun e => L'.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) := by
    apply List.filter_congr; intro e _; rw [perm_all _ h]
  rw [hcongr]
  exact h.filter _

/-- The `topOf (M ++ ·)` congruence up to `Perm` (the `Perm` analogue of `topOf_append_congr`): if the
    `topOf`s of the tails are `Perm`-equivalent, so are the `topOf`s of `M`-prefixed lists. The form the
    `Perm`-based `MatchMaxEquiv` `absorb`-stability will consume. -/
theorem topOf_append_perm {M L L' : List VeriDNS.Spec.Net.CacheRR} (h : (topOf L).Perm (topOf L')) :
    (topOf (M ++ L)).Perm (topOf (M ++ L')) := by
  rw [topOf_append_key, topOf_append_key]
  refine List.Perm.append ?_ (h.filter _)
  have : M.filter (fun e => M.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
            && (topOf L).all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
       = M.filter (fun e => M.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)
            && (topOf L').all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) := by
    apply List.filter_congr; intro e _; rw [perm_all _ h]
  rw [this]

/-- **`topServed` is `absorb`-stable** — the positive-cache component of `MatchMaxEquiv` `absorb`-
    stability. Equal `topServed` before `absorb` ⟹ equal `topServed` after (the `absorb`-prepended
    prefix `M` from `matching_absorb_append` is shared, and `topOf (M ++ ·)` factors through `topOf`). -/
theorem topServed_absorb_congr (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    {c c' : VeriDNS.Spec.Net.Cache} (h : (c.topServed now' q).Perm (c'.topServed now' q)) :
    ((c.absorb now bw resp).topServed now' q).Perm ((c'.absorb now bw resp).topServed now' q) := by
  obtain ⟨M, hM⟩ := matching_absorb_append now bw resp now' q
  rw [topServed_eq_topOf, topServed_eq_topOf, hM c, hM c'] at *
  exact topOf_append_perm h

/-! ### Full `MatchMaxEquiv` `absorb`/`absorbNeg`-stability

  Composing `topServed_absorb_congr` (positive side) with the negative/CNAME read predicates:
  `absorb` leaves `neg` untouched (`absorb_neg`) so `negHit`/`negHitNx` are stable, and prepends a
  cache-independent prefix to `pos` so `cnameAt` is stable (`cnameAt_absorb_congr`); `absorbNeg` leaves
  `pos` untouched (`absorbNeg_pos`) so `topServed`/`cnameAt` are stable, and prepends a cache-independent
  prefix to `neg` so `negHit`/`negHitNx` are congruent. Hence `MatchMaxEquiv` is preserved by both cache
  mutations the recursive `Resolves` constructors thread — the `absorb`-stability that two prior turns
  identified as the crux of the cache-substitution congruence, now complete. -/

theorem negHit_absorb (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (c : VeriDNS.Spec.Net.Cache)
    (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (c.absorb now bw resp).negHit now' q = c.negHit now' q := by
  unfold VeriDNS.Spec.Net.Cache.negHit; rw [VeriDNS.Spec.Net.absorb_neg]

theorem negHitNx_absorb (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (c : VeriDNS.Spec.Net.Cache)
    (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (c.absorb now bw resp).negHitNx now' q = c.negHitNx now' q := by
  unfold VeriDNS.Spec.Net.Cache.negHitNx; rw [VeriDNS.Spec.Net.absorb_neg]

/-- `cnameAt` is `absorb`-stable: `absorb` prepends a cache-independent prefix `N` to `pos`, so the
    CNAME `head?` either comes from `N` (shared) or falls through to the original `cnameAt`. -/
theorem cnameAt_absorb_congr (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (now' : VeriDNS.Spec.Net.Time) (n : VeriDNS.Spec.Net.Name)
    (cls : RRClass) {c c' : VeriDNS.Spec.Net.Cache}
    (h : c.cnameAt now' n cls = c'.cnameAt now' n cls) :
    (c.absorb now bw resp).cnameAt now' n cls = (c'.absorb now bw resp).cnameAt now' n cls := by
  obtain ⟨N, hN⟩ := absorb_pos_append now bw resp
  unfold VeriDNS.Spec.Net.Cache.cnameAt at h ⊢
  rw [hN c, hN c', List.filter_append, List.filter_append]
  cases hNf : N.filter (fun e => e.fresh now' && VeriDNS.Spec.Net.nameEq e.rr.owner n
      && e.rr.rdata.rtype == RRType.cname && e.rr.cls == cls) with
  | nil => simp only [List.nil_append]; exact h
  | cons x xs => simp only [List.cons_append, List.head?_cons, Option.map_some]

/-- `absorbNeg` prepends a cache-independent prefix to `neg`. -/
theorem absorbNeg_neg_append (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (resp : VeriDNS.Spec.Net.Response) :
    ∃ pre, ∀ (c : VeriDNS.Spec.Net.Cache), (c.absorbNeg now q resp).neg = pre ++ c.neg := by
  unfold VeriDNS.Spec.Net.Cache.absorbNeg
  cases VeriDNS.Spec.Net.soaNegTtl resp with
  | none => exact ⟨[], fun c => rfl⟩
  | some ttl =>
    by_cases h1 : (resp.rcode == VeriDNS.Spec.Net.RCode.nameError) = true
    · refine ⟨[⟨q.qname, none, now, ttl⟩], fun c => ?_⟩; simp [h1]
    · by_cases h2 : (resp.rcode == VeriDNS.Spec.Net.RCode.noError && resp.answer.isEmpty) = true
      · refine ⟨[⟨q.qname, some q.qtype, now, ttl⟩], fun c => ?_⟩; simp [h1, h2]
      · refine ⟨[], fun c => ?_⟩; simp [h1, h2]

theorem topServed_absorbNeg (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (resp : VeriDNS.Spec.Net.Response) (c : VeriDNS.Spec.Net.Cache)
    (now' : VeriDNS.Spec.Net.Time) (q' : VeriDNS.Spec.Net.Query) :
    (c.absorbNeg now q resp).topServed now' q' = c.topServed now' q' := by
  unfold VeriDNS.Spec.Net.Cache.topServed VeriDNS.Spec.Net.Cache.matching
  rw [VeriDNS.Spec.Net.absorbNeg_pos]

theorem cnameAt_absorbNeg (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (resp : VeriDNS.Spec.Net.Response) (c : VeriDNS.Spec.Net.Cache)
    (now' : VeriDNS.Spec.Net.Time) (n : VeriDNS.Spec.Net.Name) (cls : RRClass) :
    (c.absorbNeg now q resp).cnameAt now' n cls = c.cnameAt now' n cls := by
  unfold VeriDNS.Spec.Net.Cache.cnameAt; rw [VeriDNS.Spec.Net.absorbNeg_pos]

/-- **`MatchMaxEquiv` is preserved by `absorb`.** -/
theorem MatchMaxEquiv.absorb {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response) :
    MatchMaxEquiv (c.absorb now bw resp) (c'.absorb now bw resp) := by
  refine ⟨fun now' q => ?_, fun now' q => ?_, fun now' q => ?_⟩
  · exact topServed_absorb_congr now bw resp now' q (h.1 now' q)
  · rw [negHit_absorb, negHit_absorb]; exact h.2.1 now' q
  · rw [negHitNx_absorb, negHitNx_absorb]; exact h.2.2 now' q

/-- **`MatchMaxEquiv` is preserved by `absorbNeg`.** Together with `MatchMaxEquiv.absorb`, the relation
    is stable under every cache mutation a `Resolves` derivation threads — the hypothesis the
    cache-substitution congruence's recursive cases require. -/
theorem MatchMaxEquiv.absorbNeg {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) (resp : VeriDNS.Spec.Net.Response) :
    MatchMaxEquiv (c.absorbNeg now q resp) (c'.absorbNeg now q resp) := by
  obtain ⟨pre, hpre⟩ := absorbNeg_neg_append now q resp
  refine ⟨fun now' q' => ?_, fun now' q' => ?_, fun now' q' => ?_⟩
  · rw [topServed_absorbNeg, topServed_absorbNeg]; exact h.1 now' q'
  · unfold VeriDNS.Spec.Net.Cache.negHit
    rw [hpre c, hpre c', List.any_append, List.any_append]
    have hh := h.2.1 now' q'; unfold VeriDNS.Spec.Net.Cache.negHit at hh; rw [hh]
  · unfold VeriDNS.Spec.Net.Cache.negHitNx
    rw [hpre c, hpre c', List.any_append, List.any_append]
    have hh := h.2.2 now' q'; unfold VeriDNS.Spec.Net.Cache.negHitNx at hh; rw [hh]

/-! ### (B)(2) — `Resolves`/`HasVerdict` is a congruence in its cache argument

  The cache enters a `Resolves` derivation only through the four read predicates `MatchMaxEquiv` pins
  (`hit`/`served`, `negHit`, `negHitNx`, `cnameAt`) and is threaded forward only by `absorb`/`absorbNeg`
  (under which `MatchMaxEquiv` is stable). Hence replacing the cache by any `MatchMaxEquiv`-equivalent
  one yields a derivation with the **same response** (and a `MatchMaxEquiv`-equivalent output cache, which
  `gluelessNs`'s continuation after the NS-address sub-resolution needs). This is what lets the `resolveWithIO_total` induction
  hand the model's `c.absorb …` cache a `HasVerdict` obtained over the impl's actual cache. -/

/-! ### Phase 0 (capstone plan) — `addressOf` is order-invariant

  The model `Spec.Net.addressOf` now picks the minimum-32-bit-key A-record (not the order-sensitive
  *first*). `addressOf_perm` proves it is invariant under answer permutation — exactly what lets
  `gluelessNs` keep `nsAddr` fixed when the cache-substitution congruence permutes `nsResp`. The
  injective key + left-commutative min step (`Spec.Net.ipKey`/`ipMinOpt`) make the `perm_foldl_eq`
  keystone applicable. -/

open VeriDNS.Spec.Net in
theorem ipKey_inj {a b : VeriDNS.Spec.Net.IPv4} (h : ipKey a = ipKey b) : a = b := by
  obtain ⟨a0,a1,a2,a3⟩ := a; obtain ⟨b0,b1,b2,b3⟩ := b
  simp only [ipKey] at h
  have := a0.toNat_lt; have := a1.toNat_lt; have := a2.toNat_lt; have := a3.toNat_lt
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have k0 : a0.toNat = b0.toNat := by omega
  have k1 : a1.toNat = b1.toNat := by omega
  have k2 : a2.toNat = b2.toNat := by omega
  have k3 : a3.toNat = b3.toNat := by omega
  rw [UInt8.toNat_inj.mp k0, UInt8.toNat_inj.mp k1, UInt8.toNat_inj.mp k2, UInt8.toNat_inj.mp k3]

open VeriDNS.Spec.Net in
theorem ipMinOpt_lcomm (acc : Option VeriDNS.Spec.Net.IPv4) (x y : VeriDNS.Spec.Net.IPv4) :
    ipMinOpt (ipMinOpt acc x) y = ipMinOpt (ipMinOpt acc y) x := by
  cases acc with
  | none =>
    simp only [ipMinOpt]
    by_cases hxy : ipKey x < ipKey y <;> by_cases hyx : ipKey y < ipKey x <;>
      simp only [hxy, hyx, if_true, if_false]
    · omega
    · have : x = y := ipKey_inj (by omega); rw [this]
  | some b =>
    simp only [ipMinOpt]
    by_cases hxb : ipKey x < ipKey b <;> by_cases hyb : ipKey y < ipKey b <;>
      by_cases hxy : ipKey x < ipKey y <;> by_cases hyx : ipKey y < ipKey x <;>
      simp only [hxb, hyb, hxy, hyx, if_true, if_false] <;>
      first
        | rfl
        | (have he : x = y := ipKey_inj (by omega); subst he; rfl)
        | (exfalso; omega)

/-- **`addressOf` is permutation-invariant** — it depends on the answer only as a multiset, so the
    `gluelessNs` learned address survives the cache-substitution congruence's answer permutation. -/
theorem addressOf_perm {a b : VeriDNS.Spec.Net.Response} (h : a.answer.Perm b.answer) :
    VeriDNS.Spec.Net.addressOf a = VeriDNS.Spec.Net.addressOf b := by
  unfold VeriDNS.Spec.Net.addressOf
  rw [perm_foldl_eq ipMinOpt_lcomm (h.filterMap _)]

theorem negTrace_congr {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query} :
    c.negTrace now q = c'.negTrace now q := by
  unfold VeriDNS.Spec.Net.Cache.negTrace; rw [h.2.2 now q]

theorem negResponse_congr {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query} :
    c.negResponse now q = c'.negResponse now q := by
  unfold VeriDNS.Spec.Net.Cache.negResponse; rw [h.2.2 now q]

/-- **Inserting a non-usable record preserves an empty `served`.** A record at a credibility tier with
    `usable = false` (`Cred.additional` — referral glue and a non-authoritative referral's authority) never
    enters `served` (the `usable` filter drops it) and never disqualifies an existing usable max-rank entry
    (additional's rank is ≤ every tier's), so an already-empty `served` stays empty. The per-insert step of
    `absorb_hit_nil` (RFC 2181 §5.4.1: glue is non-answerable). -/
theorem served_insert_nonusable_nil (c : Cache) (now : Time) (q : Query) (cred : Cred) (r : RR)
    (huse : cred.usable = false) (h : c.served now q = []) :
    (c.insert now cred r).served now q = [] := by
  unfold Cache.insert
  by_cases hc : cacheable r
  · simp only [hc, if_true]
    have hsub : ∀ e ∈ c.matching now q,
        e ∈ ({c with pos := (⟨r, now, cred⟩ : CacheRR) :: c.pos}).matching now q := by
      intro e he
      unfold Cache.matching at he ⊢
      rw [List.mem_filter] at he ⊢
      exact ⟨List.mem_cons_of_mem _ he.1, he.2⟩
    rw [Cache.served, List.filter_eq_nil_iff]
    intro e he
    have hmem : e = (⟨r, now, cred⟩ : CacheRR) ∨ e ∈ c.matching now q := by
      unfold Cache.matching at he
      rw [List.mem_filter, List.mem_cons] at he
      rcases he.1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_filter.mpr ⟨h1, he.2⟩)
    rcases hmem with rfl | hem
    · simp only [huse, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
    · rw [Cache.served, List.filter_eq_nil_iff] at h
      have hne := h e hem
      intro hcontra
      apply hne
      rw [Bool.and_eq_true] at hcontra ⊢
      refine ⟨hcontra.1, ?_⟩
      rw [List.all_eq_true] at hcontra ⊢
      intro e2 he2
      exact hcontra.2 e2 (hsub e2 he2)
  · simp only [hc, if_false]; exact h

/-- Folding non-usable inserts (one `absorb` tier) preserves an empty `served`. -/
theorem served_foldl_insert_nonusable_nil (now : Time) (q : Query) (cred : Cred)
    (huse : cred.usable = false) :
    ∀ (rs : List RR) (c : Cache), c.served now q = [] →
      (rs.foldl (fun a r => a.insert now cred r) c).served now q = [] := by
  intro rs
  induction rs with
  | nil => intro c h; exact h
  | cons r rest ih => intro c h; exact ih _ (served_insert_nonusable_nil c now q cred r huse h)

/-- **A referral `absorb` preserves an empty `hit`.** A referral (`aa = false`, empty answer) writes only
    its authority and additional sections, both at the non-usable `additional` tier — so nothing enters
    `served`, and an absent positive cache hit stays absent. This is what lets the driver's `.continue`
    referral case re-invoke the `(depth,fuel)` IH with `c.hit = []` still discharged over the post-absorb
    cache (the model time is unchanged across the hop, so it is the *same* `now`). -/
theorem absorb_hit_nil (c : Cache) (now : Time) (bw : Name) (q : Query) (resp : Response)
    (h : c.hit now q = []) (hans : resp.answer = []) (haa : resp.aa = false) :
    (c.absorb now bw resp).hit now q = [] := by
  have hserved : c.served now q = [] := by
    unfold Cache.hit at h; exact List.map_eq_nil_iff.mp h
  unfold Cache.absorb Cache.hit
  simp only [hans, haa, if_false, List.filter_nil, List.foldl_nil, List.map_eq_nil_iff]
  apply served_foldl_insert_nonusable_nil now q Cred.additional rfl
  apply served_foldl_insert_nonusable_nil now q Cred.additional rfl
  exact hserved

/-- `insert` leaves the negative cache untouched (it only prepends to `.pos`). -/
theorem insert_neg (c : Cache) (now : Time) (cred : Cred) (r : RR) :
    (c.insert now cred r).neg = c.neg := by
  unfold Cache.insert; by_cases hc : cacheable r <;> simp [hc]

/-- Folding inserts leaves the negative cache untouched. -/
theorem foldl_insert_neg (now : Time) (cred : Cred) :
    ∀ (rs : List RR) (c : Cache), ((rs.foldl (fun a r => a.insert now cred r) c).neg = c.neg) := by
  intro rs
  induction rs with
  | nil => intro c; rfl
  | cons r rest ih => intro c; rw [List.foldl_cons, ih, insert_neg]

/-- **`absorb` leaves the negative cache untouched** — it only writes positive records. So a referral (or any)
    `absorb` preserves `negHit`/`negHitNx`; combined with `absorb_hit_nil` this discharges BOTH the IH's cache
    preconditions (`hit = []`, `negHit = false`) for the driver's `.continue` referral recursion. -/
theorem absorb_neg (c : Cache) (now : Time) (bw : Name) (resp : Response) :
    (c.absorb now bw resp).neg = c.neg := by
  unfold Cache.absorb
  simp only [foldl_insert_neg]

theorem absorb_negHit_eq (c : Cache) (now : Time) (bw : Name) (q : Query) (resp : Response) :
    (c.absorb now bw resp).negHit now q = c.negHit now q := by
  unfold Cache.negHit; rw [absorb_neg]

/-- An empty `hit` is preserved (`Perm` with `[]` forces `[]`). The `hmiss` discharge for the network
    branches. -/
theorem MatchMaxEquiv.hit_nil {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query} (hm : c.hit now q = []) :
    c'.hit now q = [] := by
  have hp := h.hit now q; rw [hm] at hp; exact (List.perm_nil.mp hp.symm)

/-- **Cache-substitution congruence for `Resolves`.** A `MatchMaxEquiv`-equivalent cache yields the same
    derivation outcome (same trace/path/end-time/response) with a `MatchMaxEquiv`-equivalent output cache.
    By induction on the derivation: cache reads discharged by the four `MatchMaxEquiv` components,
    recursive `absorb`/`absorbNeg` steps by `MatchMaxEquiv.absorb`/`.absorbNeg`. -/
theorem resolves_cache_congr {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState}
    {ra : String} {eb : Nat} {rtt : String → Nat} {now : VeriDNS.Spec.Net.Time}
    {nseen : List VeriDNS.Spec.Net.Name} {seen : List Name} {c : VeriDNS.Spec.Net.Cache}
    {slist : List String} {q : VeriDNS.Spec.Net.Query} {tr : List VeriDNS.Spec.Net.Step}
    {rp : List String} {tEnd : VeriDNS.Spec.Net.Time} {cout : VeriDNS.Spec.Net.Cache}
    {final : VeriDNS.Spec.Net.Response}
    (hr : VeriDNS.Spec.Net.Resolves net ns ra eb rtt now nseen seen c slist q tr rp tEnd cout final) :
    ∀ c', MatchMaxEquiv c c' →
      ∃ cout' final', VeriDNS.Spec.Net.Resolves net ns ra eb rtt now nseen seen c' slist q tr rp tEnd cout' final'
        ∧ RespAgree final final' ∧ MatchMaxEquiv cout cout' := by
  induction hr with
  | cacheHit c slist q here hhit hne =>
    intro cc hmm
    have hp : here.Perm (cc.hit _ _) := hhit ▸ MatchMaxEquiv.hit hmm _ _
    exact ⟨cc, _, Resolves.cacheHit cc slist q (cc.hit _ _) rfl (hp.length_eq ▸ hne), ⟨rfl, hp⟩, hmm⟩
  | exhausted c q =>
    intro cc hmm
    exact ⟨cc, _, Resolves.exhausted cc q, RespAgree.refl _, hmm⟩
  | negHit c slist q hneg =>
    intro cc hmm
    rw [negTrace_congr hmm, negResponse_congr hmm]
    exact ⟨cc, _, Resolves.negHit cc slist q ((hmm.2.1 _ _).symm.trans hneg), RespAgree.refl _, hmm⟩
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
    intro cc hmm
    refine ⟨_, _, Resolves.answer addr rest q srv tr resp id srcPort cc
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      hfind hans reply htrans hacc hwire hnr hnc htc,
      ?_, (hmm.absorb _ _ _).absorbNeg _ _ _⟩
    exact RespAgree.refl _
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>
    intro cc hmm

    rcases hcf0 with hw | rfl
    · exact ⟨cf, _, Resolves.trustedReply addr origin rest q id srcPort cc reply
        (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) htrans hacc hnr htc
        cf0 (Or.inl (hw.trans_perm
          (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).1
          (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).2.1
          (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).2.2))
        cf hcf,
        RespAgree.refl _, MatchMaxEquiv.refl _⟩
    · exact ⟨cf, _, Resolves.trustedReply addr origin rest q id srcPort cc reply
        (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) htrans hacc hnr htc
        cc (Or.inr rfl) cf (hcf.trans_perm hmm.1 hmm.2.1 hmm.2.2),
        RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | refer addr rest q srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ (hmm.absorb _ _ reply.msg)

    exact ⟨cout', f', Resolves.refer addr rest q srv tr ref ftr rpath tEnd f' id srcPort cc cout'
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono
      sl (((MatchMaxEquiv.referralSlist (hmm.absorb _ _ reply.msg) _ _ _).symm.subperm).trans hsl) hres, hrag, hmout⟩
  | referForget addr rest q srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec _ih =>
    intro cc hmm

    exact ⟨cout, final, Resolves.referForget addr rest q srv tr ref ftr rpath tEnd final id srcPort cc cout
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono
      sl cf0 (hcf0.trans_perm (hmm.absorb _ _ reply.msg).1 (hmm.absorb _ _ reply.msg).2.1
        (hmm.absorb _ _ reply.msg).2.2)
      hsl cf hcf hrec, RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | trustedReferral addr origin rest q frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec _ih =>
    intro cc hmm

    exact ⟨cout, final, Resolves.trustedReferral addr origin rest q frontier ftr rpath tEnd final id srcPort cc cout
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      reply htrans hacc href hbail hcut hdesc hfresh hmono
      sl cf0 (hcf0.trans_perm (hmm.absorb _ _ reply.msg).1 (hmm.absorb _ _ reply.msg).2.1
        (hmm.absorb _ _ reply.msg).2.2)
      hsl cf hcf hrec, RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec _ih =>
    intro cc hmm

    exact ⟨cout, _, Resolves.answerCname addr rest q srv tr resp cn target id srcPort cc nsl ftr rpath tEnd cout final
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc
      cf0 (hcf0.trans_perm (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).1
        (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).2.1
        (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).2.2)
      cf hcf hrec,
      RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec _ih =>
    intro cc hmm
    exact ⟨cout, _, Resolves.trustedCname addr origin rest q cn target id srcPort cc nsl ftr rpath tEnd cout final
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      reply htrans hacc hcn hqt htgt hfresh hmono htc
      cf0 (hcf0.trans_perm (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).1
        (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).2.1
        (hmm.absorb _ q.qname { reply.msg with authority := [], additional := [] }).2.2)
      cf hcf hrec,
      RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec _ih =>
    intro cc hmm

    exact ⟨cout, _, Resolves.cacheCname slist q cn target cc nsl ftr rpath tEnd cout final
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      ((MatchMaxEquiv.cnameServed hmm _ _ _).mem_iff.mp hcn) hqt htgt hfresh
      cf (hcf.trans_perm hmm.1 hmm.2.1 hmm.2.2) hrec,
      RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.timeout addr rest q ftr rpath tEnd f' cc cout' d hdrop hmono hres, hrag, hmout⟩
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.skipMissing addr rest q ftr rpath tEnd f' cc cout' hfind hres, hrag, hmout⟩
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs _ihRec =>
    intro cc hmm

    obtain ⟨c2', nsResp', hns', hragNs, hm2⟩ := ihNs _ hmm
    exact ⟨cout, _, Resolves.gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp'
      slist2 ftr rpath tEnd final cc c2' cout
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      hanc cprov hns hmono1 hns'
      ((addressOf_perm hragNs.2).symm.trans hnsaddr) hmem
      c2f (hc2f.trans_perm hm2.1 hm2.2.1 hm2.2.2) hrec,
      RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | rejectSpoof addr rest q ftr rpath tEnd final c cout id srcPort reply hreject hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.rejectSpoof addr rest q ftr rpath tEnd f' cc cout' id srcPort reply hreject hres, hrag, hmout⟩
  | badResponse addr rest q ftr rpath tEnd final c cout id srcPort reply htrans hacc hbad hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.badResponse addr rest q ftr rpath tEnd f' cc cout' id srcPort reply htrans hacc hbad hres, hrag, hmout⟩
  | unfollowableReferral addr rest q srv tr ref id srcPort ftr rpath tEnd final c cout reply
      hmiss hnmiss hfind hans htrans hacc href hunfollow hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.unfollowableReferral addr rest q srv tr ref id srcPort ftr rpath tEnd f' cc cout' reply
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      hfind hans htrans hacc href hunfollow hres, hrag, hmout⟩
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.chooseServer slist slist' q ftr rpath tEnd f' cc cout' hperm hres, hrag, hmout⟩

/-- **Cache-substitution congruence for `HasVerdict`** (the form the totality induction consumes): a
    `MatchMaxEquiv`-equivalent cache preserves the verdict. -/
theorem hasVerdict_cache_congr {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState}
    {ra : String} {eb : Nat} {rtt : String → Nat} {now : VeriDNS.Spec.Net.Time}
    {nseen : List VeriDNS.Spec.Net.Name} {seen : List Name} {c c' : VeriDNS.Spec.Net.Cache}
    {slist : List String} {q : VeriDNS.Spec.Net.Query} {v : VeriDNS.Spec.Net.Response}
    (h : HasVerdict net ns ra eb rtt now nseen seen c slist q v) (hmm : MatchMaxEquiv c c') :
    HasVerdict net ns ra eb rtt now nseen seen c' slist q v := by
  obtain ⟨tr, sp, tEnd, cout, resp, hres, hag⟩ := h
  obtain ⟨cout', resp', hres', hrag, _⟩ := resolves_cache_congr hres c' hmm
  exact ⟨tr, sp, tEnd, cout', resp', hres', RespAgree.trans hag hrag⟩

/-! ### (B)(3) groundwork — the model atomic-write (`insert`) congruence

  `MatchMaxEquiv.absorb` covers `absorb` (a fold of `insert`s) wholesale, but the per-hop establishment
  `MatchMaxEquiv (αCache (impl storeChecked-fold)) ((αCache c).absorb …)` is proven *record by record*,
  pairing each impl `storeChecked` write with a model `insert`. These are the model-`insert` templates for
  that pairing: `insert` prepends a cache-independent prefix to `matching` (`matching_insert_append`), so
  `topServed`-equality is `insert`-stable (`topServed_insert_congr`). The remaining (B)(3) crux is the
  impl side — `topServed (αCache (DnsCache.storeChecked c rr cred now)) = topServed ((αCache c).insert …)`
  — the write-path analogue of the proven read-path `lookupAnswerable_αRR_eq_hit`. -/

theorem matching_insert_append (now : VeriDNS.Spec.Net.Time) (cred : VeriDNS.Spec.Net.Cred)
    (r : VeriDNS.Spec.Net.RR) (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    ∃ M, ∀ (c : VeriDNS.Spec.Net.Cache),
      (c.insert now cred r).matching now' q = M ++ c.matching now' q := by
  unfold VeriDNS.Spec.Net.Cache.insert
  by_cases hc : VeriDNS.Spec.Net.cacheable r
  · simp only [hc, if_true]
    refine ⟨([(⟨r, now, cred⟩ : VeriDNS.Spec.Net.CacheRR)].filter
        (fun e => e.fresh now' && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
              && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass))), fun c => ?_⟩
    unfold VeriDNS.Spec.Net.Cache.matching
    rw [List.filter_cons]
    by_cases hm : (CacheRR.fresh ⟨r, now, cred⟩ now' && VeriDNS.Spec.Net.nameEq r.owner q.qname
        && q.qtype.covers r.rtype && (r.cls == q.qclass)) = true
    · simp [hm]
    · simp [hm]
  · simp only [hc]; exact ⟨[], fun c => rfl⟩

theorem topServed_insert_congr (now : VeriDNS.Spec.Net.Time) (cred : VeriDNS.Spec.Net.Cred)
    (r : VeriDNS.Spec.Net.RR) (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    {c c' : VeriDNS.Spec.Net.Cache} (h : c.topServed now' q = c'.topServed now' q) :
    (c.insert now cred r).topServed now' q = (c'.insert now cred r).topServed now' q := by
  obtain ⟨M, hM⟩ := matching_insert_append now cred r now' q
  rw [topServed_eq_topOf, topServed_eq_topOf, hM c, hM c'] at *
  exact topOf_append_congr h

/-! ### Phase 3 — `αCache` of the impl fresh-push lands as a record-append (the `topServed`-bridge shape)

  Under freshness (`store_fresh_records`), the impl referral write appends records to `c.records`. `αCache`
  carries that append through `filterMap` (`αCache_pos_of_records_append`), and `matching` carries it through
  `filter` (`matching_αCache_records_append`). So `matching (αCache impl-fold) = matching (αCache c) ++ (new
  records, matched)` — the same *multiset* as the model `absorb`'s `M ++ matching c` (only the append side
  differs), which `topOf_perm` turns into the `topServed`-`Perm` clause of the bridge. -/

theorem αCache_pos_of_records_append {c c' : VeriDNS.Impl.Cache.DnsCache}
    {extra : Array VeriDNS.Impl.Cache.CacheEntry} (h : c'.records = c.records ++ extra) :
    (αCache c').pos = (αCache c).pos ++ extra.toList.filterMap αCacheRR := by
  unfold αCache
  simp only [h, Array.toList_append, List.filterMap_append]

theorem matching_αCache_records_append {c c' : VeriDNS.Impl.Cache.DnsCache}
    {extra : Array VeriDNS.Impl.Cache.CacheEntry} (h : c'.records = c.records ++ extra)
    (nowT : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (αCache c').matching nowT q
      = (αCache c).matching nowT q
        ++ (extra.toList.filterMap αCacheRR).filter (fun e => e.fresh nowT
              && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
              && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)) := by
  unfold VeriDNS.Spec.Net.Cache.matching
  rw [αCache_pos_of_records_append h, List.filter_append]

/-- `topOf` of `L ++ A` and `B ++ L` are `Perm`-equal when `A ~ B` (append commutes; `topOf` is
    `Perm`-congruent). The shape that joins the impl `matching_c ++ extra'` to the model `M ++ matching_c`. -/
theorem topOf_appendL_perm_appendR {L A B : List VeriDNS.Spec.Net.CacheRR} (h : A.Perm B) :
    (topOf (L ++ A)).Perm (topOf (B ++ L)) :=
  topOf_perm ((List.Perm.append_left L h).trans List.perm_append_comm)

/-- **The `topServed` clause of the Phase-3 bridge, reduced to the matched-record correspondence.** Given
    the impl fresh-push (`c''.records = c.records ++ extra`), the model `absorb`'s matching-append
    (`hM`, from `matching_absorb_append`), and that the impl's pushed-and-matched records permute the
    model's added matching `M` (`hcorr` — the `bailiwickRaws`↔`isAncestor bw` + `αRR` correspondence, the
    one genuine remaining piece), the served per-key-max sets agree up to `Perm`. With
    `store_negatives`/`absorb_neg` (the negHit/negHitNx clauses) this is the whole bridge
    `MatchMaxEquiv (αCache c'') ((αCache c).absorb …)`. -/
theorem topServed_bridge_clause {c c'' : VeriDNS.Impl.Cache.DnsCache}
    {extra : Array VeriDNS.Impl.Cache.CacheEntry} (hrec : c''.records = c.records ++ extra)
    (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response)
    (nowT : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) (M : List VeriDNS.Spec.Net.CacheRR)
    (hM : ((αCache c).absorb now bw resp).matching nowT q = M ++ (αCache c).matching nowT q)
    (hcorr : ((extra.toList.filterMap αCacheRR).filter (fun e => e.fresh nowT
                && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname && q.qtype.covers e.rr.rtype
                && (e.rr.cls == q.qclass))).Perm M) :
    ((αCache c'').topServed nowT q).Perm (((αCache c).absorb now bw resp).topServed nowT q) := by
  rw [topServed_eq_topOf, topServed_eq_topOf, matching_αCache_records_append hrec, hM]
  exact topOf_appendL_perm_appendR hcorr

/-- **The `topServed` bridge reduced to the query-independent positive-records correspondence.** Given the
    impl fresh-push (`hrec`), the model `absorb`'s pos-append (`hN`, from `absorb_pos_append`), and that the
    abstracted impl-pushed records permute the model's absorbed positive records (`hposperm` — note: NO query
    filter, NO freshness/owner/type predicate — purely `(extra.filterMap αCacheRR) ~ N`), the served
    per-key-max sets agree up to `Perm` *for every query simultaneously*. The per-query matching filter drops
    out via `List.Perm.filter`. This is the final shape `hcorr` must establish: a single positive-records
    `Perm`, dischargeable per-section by `αSection_bailiwickRaws_eq` (bailiwick filter) + `αCred_cred*` (cred)
    + `αCacheRR_rr`/`_cred` (abstraction), independent of the read query. -/
theorem topServed_bridge_of_pos_perm {c c'' : VeriDNS.Impl.Cache.DnsCache}
    {extra : Array VeriDNS.Impl.Cache.CacheEntry}
    (hrec : c''.records = c.records ++ extra)
    (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response)
    (nowT : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) {N : List VeriDNS.Spec.Net.CacheRR}
    (hN : ((αCache c).absorb now bw resp).pos = N ++ (αCache c).pos)
    (hposperm : (extra.toList.filterMap αCacheRR).Perm N) :
    ((αCache c'').topServed nowT q).Perm (((αCache c).absorb now bw resp).topServed nowT q) := by
  have hM : ((αCache c).absorb now bw resp).matching nowT q
      = (N.filter (fun e => e.fresh nowT && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
            && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)))
        ++ (αCache c).matching nowT q := by
    unfold VeriDNS.Spec.Net.Cache.matching
    rw [hN, List.filter_append]
  exact topServed_bridge_clause hrec now bw resp nowT q _ hM
    (hposperm.filter (fun e => e.fresh nowT && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
            && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)))

/-- **The `topServed` bridge at the POS level (consumes the refer-hop write-path lemmas directly).** Given the
    impl cache's abstracted pos as a base-append `cI.pos = cBase.pos ++ X` (from `two_section_αCache_pos`), the
    model's as a base-prepend `cM.pos = N ++ cBase.pos` (from `absorb_referral_pos`), and `X ~ N` (from
    `refer_extra_perm`), the served per-key-max sets agree up to `Perm` for every query. Unlike
    `topServed_bridge_of_pos_perm` (which derives the pos from a records-level `hrec`), this takes the abstract
    `αCache.pos` equations the refer-hop lemmas actually produce. The append/prepend mismatch (impl `store`
    appends newest-last, model `insert` prepends newest-first) is absorbed by `topOf_appendL_perm_appendR`. -/
theorem topServed_bridge_pos (cBase cI cM : VeriDNS.Spec.Net.Cache)
    (X N : List VeriDNS.Spec.Net.CacheRR) (nowT : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (hI : cI.pos = cBase.pos ++ X) (hM : cM.pos = N ++ cBase.pos) (hXN : X.Perm N) :
    (cI.topServed nowT q).Perm (cM.topServed nowT q) := by
  rw [topServed_eq_topOf, topServed_eq_topOf]
  have hmI : cI.matching nowT q
      = cBase.matching nowT q
        ++ X.filter (fun e => e.fresh nowT && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
              && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)) := by
    unfold VeriDNS.Spec.Net.Cache.matching; rw [hI, List.filter_append]
  have hmM : cM.matching nowT q
      = N.filter (fun e => e.fresh nowT && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
              && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass))
        ++ cBase.matching nowT q := by
    unfold VeriDNS.Spec.Net.Cache.matching; rw [hM, List.filter_append]
  rw [hmI, hmM]
  exact topOf_appendL_perm_appendR (hXN.filter _)
/-- **The refer-hop `MatchMaxEquiv` (the cache half of the refer-branch forward simulation).** The impl's
    two referral writes (authority `credAuthority aa`, additional `credAdditional`, bailiwick-filtered to
    `cut`, via `cacheUnlessTruncated`), abstracted, are `MatchMaxEquiv` to the model `absorb`. All three
    clauses discharged: the `topServed` `Perm` via `topServed_bridge_pos` (`two_section_αCache_pos` ++
    `absorb_referral_pos` ++ `refer_extra_perm`), and the negHit/negHitNx eqs via `cacheUnlessTruncated_negatives`
    + `absorb_neg` (a referral write touches only positives). Hypotheses: `aa=false` + `isReferral` (the refer
    discipline), `htc` (untruncated), `hcut` (cut abstracts to `bwN`), the per-section fresh-push `h1`/`h2`
    (from the freshness invariant), and the per-raw no-overflow `hnoA`/`hnoD` (TTL cap). These are exactly the
    side-conditions the `StateModels` refer-branch step supplies; THIS is the refer-hop cache-preservation
    obligation, proved axiom-clean. -/
theorem refer_hop_MatchMaxEquiv (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray)
    (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (aa : Bool) (haa : aa = false)
    (hcut : αName cut = some bwN) (htc : (resp.header.tc == 1) = false)
    (href : (αResp resp).isReferral = true)
    (h1 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr (VeriDNS.Impl.Resolver.credAuthority aa) now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAuthority aa⟩)
    (h2 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr VeriDNS.Impl.Resolver.credAdditional now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hnoD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmapA : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority), RRCanonMappable e)
    (hcanmapD : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional), RRCanonMappable e) :
    MatchMaxEquiv
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
            (VeriDNS.Impl.Resolver.credAuthority aa) now)
          resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
            VeriDNS.Impl.Resolver.credAdditional now))
      ((αCache c).absorb now.toNat bwN (αResp resp)) := by
  have hI := two_section_αCache_pos c resp
    (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
    (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
    (VeriDNS.Impl.Resolver.credAuthority aa) VeriDNS.Impl.Resolver.credAdditional now htc h1 h2
  have hM := absorb_referral_pos (αCache c) now.toNat bwN (αResp resp) href
  have hXN := refer_extra_perm resp.authority resp.additional cut bwN now aa haa hcut hnoA hnoD hcanmapA hcanmapD
  have hαr : (αResp resp).authority = αSection resp.authority := rfl
  have hαr2 : (αResp resp).additional = αSection resp.additional := rfl
  rw [hαr, hαr2] at hM
  rw [List.append_assoc] at hI
  have hneg : (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
            (VeriDNS.Impl.Resolver.credAuthority aa) now)
          resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
            VeriDNS.Impl.Resolver.credAdditional now).negatives = c.negatives := by
    rw [cacheUnlessTruncated_negatives, cacheUnlessTruncated_negatives]
  refine ⟨fun nowT q => ?_, fun nowT q => ?_, fun nowT q => ?_⟩
  · exact topServed_bridge_pos (αCache c) _ _ _ _ nowT q hI hM hXN
  · show VeriDNS.Spec.Net.Cache.negHit _ nowT q = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHit
    rw [hneg, VeriDNS.Spec.Net.absorb_neg]
  · show VeriDNS.Spec.Net.Cache.negHitNx _ nowT q = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHitNx
    rw [hneg, VeriDNS.Spec.Net.absorb_neg]
/-- **The answerCname-hop `MatchMaxEquiv` (the CNAME-chase cache refinement).** The impl's single CNAME
    write (`cacheUnlessTruncated cache resp (bailiwickRaws sname resp.answer) (credAnswer aa)`), abstracted,
    is `MatchMaxEquiv` to the model `absorb` over the answer-only response at bailiwick `bwN` (= `αName
    sname`). Simpler than the refer hop — ONE section, NO `aa=false`/`isReferral` (the cred is `aa`-dependent
    on both sides: `αCred (credAnswer aa) = if aa then authoritative else glue = ansCred`). topServed `Perm`
    via `topServed_bridge_pos` (`cacheRRs_αCache_pos` ++ `absorb_answerOnly_pos` ++ `section_extra_perm`),
    negHit/negHitNx via `cacheRRs_negatives` + `absorb_neg`. With the model restricted to answer-only
    (the resolved answerCname gap), the model caches exactly the impl's CNAME write — the hop refines. -/
theorem answerCname_hop_MatchMaxEquiv (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format) (sname : ByteArray)
    (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (hcut : αName sname = some bwN)
    (htc : (resp.header.tc == 1) = false)
    (h1 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)⟩)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer), RRCanonMappable e) :
    MatchMaxEquiv
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)
          (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now))
      ((αCache c).absorb now.toNat bwN { αResp resp with authority := [], additional := [] }) := by
  have hI := cacheRRs_αCache_pos (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer))
    (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now c h1
  rw [cacheUnlessTruncated_untruncated _ _ _ _ _ htc]
  have hM := absorb_answerOnly_pos (αCache c) now.toNat bwN (αResp resp)
  have hsec := section_extra_perm resp.answer sname bwN (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now hcut hnoA hcanmap
  rw [αCred_credAnswer] at hsec
  refine ⟨fun nowT q' => ?_, fun nowT q' => ?_, fun nowT q' => ?_⟩
  · refine topServed_bridge_pos (αCache c) _ _ _ _ nowT q' hI ?_ hsec
    show ((αCache c).absorb now.toNat bwN { αResp resp with authority := [], additional := [] }).pos = _
    rw [hM]; rfl
  · show VeriDNS.Spec.Net.Cache.negHit _ nowT q' = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHit
    rw [cacheRRs_negatives, VeriDNS.Spec.Net.absorb_neg]
  · show VeriDNS.Spec.Net.Cache.negHitNx _ nowT q' = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHitNx
    rw [cacheRRs_negatives, VeriDNS.Spec.Net.absorb_neg]

/-! ### Phase 4 (capstone plan) — the `StateModels` state↔model invariant (keystone)

  The `(depth,fuel)` totality induction threads a model configuration `(c, q, now, deadline, …)` alongside
  the executable resolver `state` and the `World` oracle `w`. `StateModels` is the invariant relating them:
  the model cache `c` is `MatchMaxEquiv` to the abstracted impl cache (so the Phase-3 bridge is exactly the
  preservation obligation at a cache-changing hop), the query name + clock + deadline correspond, and the
  oracle simulates `net` (`WorldModels`). (Core fields; the query type/class bridge — `Qtype`/`Qclass` are
  inductive, related to the model `QType`/`RRClass` via `…toCode` + `αQType`/`αClass` — and the slist
  correspondence are refinements added as the induction's branches consume them.) -/
def StateModels (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState) (ra : String)
    (ednsBuf : Nat) (rttOf : String → Nat) (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (state : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (c : VeriDNS.Spec.Net.Cache) (w : World) : Prop :=
  MatchMaxEquiv (αCache state.resources.cache) c
  ∧ αName state.resources.sname = some q.qname
  ∧ αTime state.now = now
  ∧ WorldModels net ns ra ednsBuf now w

/-- **`StateModels` can be re-pointed at the impl cache's OWN abstraction** (`MatchMaxEquiv` becomes refl; the
    `sname`/`now`/`WorldModels` parts don't mention the model cache). Lets the IH on the post-eviction state run
    against `αCache state.cache` directly — the model cache the `referForget` recursive step needs (with `hcf`
    relating it to `c.absorb` by `CacheRefines`). -/
theorem StateModels_swap_to_αCache
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : World}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w) :
    StateModels net ns ra ednsBuf rttOf now q state (αCache state.resources.cache) w :=
  ⟨MatchMaxEquiv.refl _, old.2⟩

/-- **Cache canonicity invariant** — the `keystone_at_cut` cache hypotheses, packaged as one predicate over the
    impl cache. Every stored record (a) abstracts (`αCacheRR` is `some`) with a sane TTL/expiry window around
    `now`, (b) has a canonical owner name (the literal `labelsToWireFormatGo` of its abstraction, ≤63-byte
    labels), and (c) sits in one of the four credibility tiers the impl writes. These hold for any cache the impl
    builds (records parsed from canonical wire by `Message.decode`, stored at `credAuthority`/`credAdditional`/
    `credAnswer`), and are exactly what the keystone `hgl` discharge needs — but they are **NOT yet part of
    `StateModels`**. Closing the refer `.continue` (235) case requires strengthening `StateModels` with this
    conjunct and proving its preservation across `absorb` (`storeChecked` of canonical wire records) and the
    other hops. Surfaced 2026-06-29: a hypothesis the keystone assumes that the invariant didn't yet carry. -/
def CacheWf (c : VeriDNS.Impl.Cache.DnsCache) (now : UInt32) : Prop :=
  (∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
      ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
  ∧ (∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
      e.rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
  ∧ (∀ e ∈ c.records, e.credibility = VeriDNS.Spec.Trustworthiness.authoritativeSection
      ∨ e.credibility = VeriDNS.Spec.Trustworthiness.authoritySection
      ∨ e.credibility = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
      ∨ e.credibility = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)

/-- **`CacheWf` is monotone under record removal.** Each clause is a `∀ e ∈ records`, so a sub-cache (fewer
    records) keeps the invariant. The frame for every record-FILTERING cache op (sweep, eviction). -/
theorem CacheWf_mono {c c' : VeriDNS.Impl.Cache.DnsCache} {now : UInt32}
    (hsub : ∀ e ∈ c'.records, e ∈ c.records) (h : CacheWf c now) : CacheWf c' now :=
  ⟨fun e he => h.1 e (hsub e he), fun e he => h.2.1 e (hsub e he), fun e he => h.2.2 e (hsub e he)⟩

/-- The empty cache is well-formed (no records to constrain). -/
theorem CacheWf_empty (now : UInt32) : CacheWf VeriDNS.Impl.Cache.DnsCache.empty now :=
  ⟨fun _ he => absurd he (by simp [VeriDNS.Impl.Cache.DnsCache.empty]),
   fun _ he => absurd he (by simp [VeriDNS.Impl.Cache.DnsCache.empty]),
   fun _ he => absurd he (by simp [VeriDNS.Impl.Cache.DnsCache.empty])⟩

/-- Impl-level same-key test between a cache entry and an incoming record — the exact key shape
    `storeChecked`'s `betterExists` gate and `store`'s replacement filter use (case-insensitive owner,
    `==` type and class). -/
def entKeyB (e : VeriDNS.Impl.Cache.CacheEntry) (rr : VeriDNS.Spec.ResourceRecord) : Bool :=
  VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class

/-- `entKeyB` chains through a middle entry (CI name equality is transitive; type/class `==` is equality). -/
theorem entKeyB_trans {e f : VeriDNS.Impl.Cache.CacheEntry} {rr : VeriDNS.Spec.ResourceRecord}
    (h1 : entKeyB e f.rr = true) (h2 : entKeyB f rr = true) : entKeyB e rr = true := by
  unfold entKeyB at h1 h2 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  exact ⟨⟨VeriDNS.Proof.NameTree.nameEqCI_trans h1.1.1 h2.1.1, h1.1.2.trans h2.1.2⟩,
    h1.2.trans h2.2⟩

/-- The parse-then-`storeChecked` fold step, NAMED so `List.foldl` rewriting keeps the application
    syntactic (an anonymous lambda gets beta-reduced by `rw`, hiding the step from equation rewriting). -/
def warmStep (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (c : VeriDNS.Impl.Cache.DnsCache) (bytes : ByteArray) : VeriDNS.Impl.Cache.DnsCache :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
  | some rr => c.storeChecked rr cred now
  | none => c

theorem warm_step_none (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (c : VeriDNS.Impl.Cache.DnsCache) {b : ByteArray}
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = none) :
    warmStep cred now c b = c := by
  unfold warmStep
  rw [hpr]

theorem warm_step_some (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (c : VeriDNS.Impl.Cache.DnsCache) {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    warmStep cred now c b = c.storeChecked rr cred now := by
  unfold warmStep
  rw [hpr]

/-- **Warm-fold decomposition of a `storeChecked` fold** (the impl side of the warm-cache write bridge,
    with NO fresh-push hypothesis). Folding `parse-then-storeChecked` at a fixed `cred` over raws `l`
    decomposes the result's records as `survivors ++ pushed`:
    * the survivors are a `filter Q` of the input records;
    * the pushed entries `P` are a `Sublist` of the would-be fresh pushes `l.flatMap (pushOf cred now)`
      (each `storeChecked` either skips — RFC 2181 §5.4.1 — or replaces-and-pushes — §5.2);
    * (INV-B, *blocker protection*) every input record that is fresh at `now` and STRICTLY more
      trustworthy than `cred` survives, and no pushed record shares its key — such a record makes
      `betterExists` true for any same-key incoming record, forcing a skip; inductively it is never
      dropped (drops happen only at same-key stores);
    * (INV-D, *drop reason*) every dropped input record shares its key with some FINAL pushed record —
      a drop happens only at a same-key store, and the last same-key store survives to the end. -/theorem warm_foldl_decomp (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (c : VeriDNS.Impl.Cache.DnsCache),
      ∃ (Q : VeriDNS.Impl.Cache.CacheEntry → Bool) (P : List VeriDNS.Impl.Cache.CacheEntry),
        (l.foldl (warmStep cred now) c).records.toList
          = c.records.toList.filter Q ++ P
        ∧ P.Sublist (l.flatMap (pushOf cred now))
        ∧ (∀ e ∈ c.records.toList, (decide (e.expiry > now)) = true →
              e.credibility.toCode < cred.toCode →
              Q e = true ∧ ∀ p ∈ P, entKeyB e p.rr = false)
        ∧ (∀ e ∈ c.records.toList, Q e = false → ∃ p ∈ P, entKeyB e p.rr = true) := by
  intro l
  induction l with
  | nil =>
    intro c
    refine ⟨fun _ => true, [],
      by rw [List.foldl_nil, List.append_nil, List.filter_eq_self.mpr (fun _ _ => rfl)],
      by simp, fun e _ _ _ => ⟨rfl, by simp⟩, fun e _ hq => absurd hq (by simp)⟩
  | cons b rest ih =>
    intro c
    rw [List.foldl_cons]
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none =>
      rw [warm_step_none cred now c hpr]
      obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := ih c
      refine ⟨Q, P, hdec, ?_, hB, hD⟩
      rw [List.flatMap_cons, pushOf_none cred now hpr, List.nil_append]
      exact hsub
    | some rr =>
      rw [warm_step_some cred now c hpr]
      by_cases hz : (rr.ttl == 0) = true
      ·
        have hstep : c.storeChecked rr cred now = c := by
          unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
          exact if_pos hz
        rw [hstep]
        obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := ih c
        refine ⟨Q, P, hdec, ?_, hB, hD⟩
        rw [List.flatMap_cons, pushOf_zero cred now hpr hz, List.nil_append]
        exact hsub
      · by_cases hb : (c.records.any fun e =>
            VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type
              && e.rr.class == rr.class
              && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
              && decide (e.credibility.toCode < cred.toCode)) = true
        ·
          have hstep : c.storeChecked rr cred now = c := by
            unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
            rw [if_neg hz]
            exact if_pos hb
          rw [hstep]
          obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := ih c
          refine ⟨Q, P, hdec, ?_, hB, hD⟩
          rw [List.flatMap_cons]
          exact (List.nil_sublist _).append hsub
        ·
          have hstep : c.storeChecked rr cred now = c.store rr now cred := by
            unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
            rw [if_neg hz]
            exact if_neg hb
          rw [hstep]
          have hrec : (c.store rr now cred).records
              = (c.records.filter fun e => !(entKeyB e rr
                  && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
                ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := rfl
          obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := ih (c.store rr now cred)
          have hlist : (c.store rr now cred).records.toList
              = c.records.toList.filter (fun e => !(entKeyB e rr
                  && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata)))
                ++ [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩] := by
            rw [hrec, Array.toList_push, Array.toList_filter]

          have hkeyfree : ∀ e ∈ c.records.toList, (decide (e.expiry > now)) = true →
              e.credibility.toCode < cred.toCode → entKeyB e rr = false := by
            intro e he hfr hbet
            by_contra hk
            rw [Bool.not_eq_false] at hk
            apply hb
            obtain ⟨i, hi, hei⟩ := Array.getElem_of_mem (Array.mem_def.mpr he)
            rw [Array.any_eq_true]
            refine ⟨i, hi, ?_⟩
            rw [hei]
            have hk' := hk
            unfold entKeyB at hk'
            rw [hk', hfr]
            simp [hbet]
          refine ⟨fun e => Q e && !(entKeyB e rr
              && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata)),
            List.filter Q [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩] ++ P, ?_, ?_, ?_, ?_⟩
          ·
            rw [hdec, hlist, List.filter_append, List.filter_filter, List.append_assoc]
          ·
            rw [List.flatMap_cons, pushOf_pos cred now hpr (by simpa using hz)]
            exact List.Sublist.append List.filter_sublist hsub
          ·
            intro e he hfr hbet
            have hek := hkeyfree e he hfr hbet
            have hkeep : (!(entKeyB e rr
                && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))) = true := by
              rw [hek]; rfl
            have hmem1 : e ∈ (c.store rr now cred).records.toList := by
              rw [hlist]
              exact List.mem_append_left _ (List.mem_filter.mpr ⟨he, hkeep⟩)
            obtain ⟨hQ, hPfree⟩ := hB e hmem1 hfr hbet
            refine ⟨?_, ?_⟩
            · show (Q e && !(entKeyB e rr
                  && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))) = true
              rw [hkeep, hQ]
              rfl
            · intro p hp
              rcases List.mem_append.mp hp with hp | hp
              · have hpz : p = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :=
                  List.mem_singleton.mp (List.mem_filter.mp hp).1
                rw [hpz]
                exact hek
              · exact hPfree p hp
          ·
            intro e he hq
            have hq2 : (Q e && !(entKeyB e rr
                && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))) = false := hq
            rcases Bool.and_eq_false_iff.mp hq2 with hQ | hkeep
            ·
              by_cases hkeep : (!(entKeyB e rr
                  && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))) = true
              · have hmem1 : e ∈ (c.store rr now cred).records.toList := by
                  rw [hlist]
                  exact List.mem_append_left _ (List.mem_filter.mpr ⟨he, hkeep⟩)
                obtain ⟨p, hp, hpk⟩ := hD e hmem1 hQ
                exact ⟨p, List.mem_append_right _ hp, hpk⟩
              ·
                have hek : entKeyB e rr = true := by
                  rw [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at hkeep
                  exact hkeep.1
                by_cases hQz : Q ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = true
                · refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩, List.mem_append_left _ ?_, hek⟩
                  exact List.mem_filter.mpr
                    ⟨List.mem_singleton_self (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :
                      VeriDNS.Impl.Cache.CacheEntry), hQz⟩
                · have hmemz : (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :
                      VeriDNS.Impl.Cache.CacheEntry) ∈ (c.store rr now cred).records.toList := by
                    rw [hlist]
                    exact List.mem_append_right _ (List.mem_singleton_self _)
                  obtain ⟨p, hp, hpk⟩ := hD _ hmemz (by simpa using hQz)
                  exact ⟨p, List.mem_append_right _ hp, entKeyB_trans hek hpk⟩

            ·
              have hek : entKeyB e rr = true := by
                rw [Bool.not_eq_false', Bool.and_eq_true] at hkeep
                exact hkeep.1
              by_cases hQz : Q ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = true
              · refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩, List.mem_append_left _ ?_, hek⟩
                exact List.mem_filter.mpr
                  ⟨List.mem_singleton_self (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :
                    VeriDNS.Impl.Cache.CacheEntry), hQz⟩
              · have hmemz : (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :
                    VeriDNS.Impl.Cache.CacheEntry) ∈ (c.store rr now cred).records.toList := by
                  rw [hlist]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
                obtain ⟨p, hp, hpk⟩ := hD _ hmemz (by simpa using hQz)
                exact ⟨p, List.mem_append_right _ hp, entKeyB_trans hek hpk⟩
/-- `entKeyB` is symmetric (CI name equality is symmetric; `==` on type/class is equality). -/
theorem entKeyB_symm {e f : VeriDNS.Impl.Cache.CacheEntry} (h : entKeyB e f.rr = true) :
    entKeyB f e.rr = true := by
  unfold entKeyB at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨⟨VeriDNS.Proof.NameTree.nameEqCI_symm h.1.1, h.1.2.symm⟩, h.2.symm⟩

/-- Membership inversion for the fresh-push list: each would-be pushed entry comes from a parsed,
    `ttl ≠ 0` raw of the section, with the canonical `⟨rr, now+ttl, false, cred⟩` shape. -/
theorem mem_flatMap_pushOf {l : List ByteArray} {cred : VeriDNS.Spec.Trustworthiness} {now : UInt32}
    {p : VeriDNS.Impl.Cache.CacheEntry} (hp : p ∈ l.flatMap (pushOf cred now)) :
    ∃ b ∈ l, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
      ∧ (rr.ttl == 0) = false
      ∧ p = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := by
  rw [List.mem_flatMap] at hp
  obtain ⟨b, hb, hpin⟩ := hp
  refine ⟨b, hb, ?_⟩
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [pushOf_none cred now hpr] at hpin; exact absurd hpin (by simp)
  | some rr =>
    by_cases hz : (rr.ttl == 0) = true
    · rw [pushOf_zero cred now hpr hz] at hpin; exact absurd hpin (by simp)
    · rw [pushOf_pos cred now hpr (by simpa using hz)] at hpin
      exact ⟨rr, rfl, by simpa using hz, List.mem_singleton.mp hpin⟩

/-- Every record the model `absorb` inserts (via `modelPushOf`) carries the fold's credibility and
    `insertedAt = now` — for a referral (`aa = false`) that is `Cred.additional`, the MINIMAL rank. -/
theorem mem_modelPushOf {now : VeriDNS.Spec.Net.Time} {cred : VeriDNS.Spec.Net.Cred}
    {r : VeriDNS.Spec.Net.RR} {x : VeriDNS.Spec.Net.CacheRR} (hx : x ∈ modelPushOf now cred r) :
    x.cred = cred ∧ x.insertedAt = now := by
  unfold modelPushOf at hx
  split at hx
  · rw [List.mem_singleton.mp hx]; exact ⟨rfl, rfl⟩
  · exact absurd hx (by simp)

/-- The minimal-rank gate is free: `Cred.additional` (referral-write tier) ranks below everything, so a
    same-key `additional` record can never evict another record from `topServed`. -/
theorem ble_additional_rank (c : VeriDNS.Spec.Net.Cred) :
    Nat.ble (VeriDNS.Spec.Net.Cred.additional.rank) c.rank = true := by
  rw [Nat.ble_eq]
  exact Nat.zero_le _

/-- Assemble the `topServed` max-rank gate from per-element rank bounds. -/
theorem topGate_of_ranks {m : List VeriDNS.Spec.Net.CacheRR} {a : VeriDNS.Spec.Net.CacheRR}
    (h : ∀ x ∈ m, x.sameKey a.rr = true → Nat.ble x.cred.rank a.cred.rank = true) :
    (m.all fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true := by
  rw [List.all_eq_true]
  intro x hx
  by_cases hk : x.sameKey a.rr = true
  · rw [hk, h x hx hk]; rfl
  · rw [Bool.not_eq_true] at hk; rw [hk]; rfl

/-- **Model-`sameKey` transfers to the impl key** on abstracting, canonically-named entries — the
    bridge the warm-write provenance argument uses to feed model-level same-key facts into the fold
    invariants (INV-B/INV-D). Owner names via `nameEqCI_of_αName_canonical`; type/class via
    `αType_injective`/`αClass_inj` (the wire codes abstracting to equal model types/classes are equal). -/
theorem entKeyB_of_sameKey {e f : VeriDNS.Impl.Cache.CacheEntry} {x a : VeriDNS.Spec.Net.CacheRR}
    (hx : αCacheRR e = some x) (ha : αCacheRR f = some a)
    (hcanE : e.rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo x.rr.owner)
    (hvE : ∀ lb ∈ x.rr.owner, lb.size ≤ 63)
    (hcanF : f.rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner)
    (hvF : ∀ lb ∈ a.rr.owner, lb.size ≤ 63)
    (hk : x.sameKey a.rr = true) : entKeyB e f.rr = true := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨⟨hnm, hty⟩, hcl⟩ := hk
  unfold entKeyB
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hxe := αRR_rtype e.rr x.rr (αCacheRR_rr hx)
  have hfa := αRR_rtype f.rr a.rr (αCacheRR_rr ha)
  have hty0 : (x.rr.rdata.rtype == a.rr.rdata.rtype) = true := hty
  have htyeq : x.rr.rdata.rtype = a.rr.rdata.rtype := eq_of_αType_beq hxe hfa hty0
  have hclE := (αRR_fields e.rr x.rr (αCacheRR_rr hx)).2.2
  have hclF := (αRR_fields f.rr a.rr (αCacheRR_rr ha)).2.2
  have hcleq : x.rr.cls = a.rr.cls := eq_of_αClass_beq hclE hclF hcl
  refine ⟨⟨nameEqCI_of_αName_canonical hnm hcanE hcanF hvE hvF, ?_⟩, ?_⟩
  · exact αType_injective (hxe.trans (congrArg some htyeq)) hfa
  · exact αClass_inj (hclE.trans (congrArg some hcleq)) hclF

/-- **The refer-hop `WriteRefines` — the WARM-CACHE write-path bridge** (supersedes `refer_hop_MatchMaxEquiv`
    for the driver: no fresh-push `h1`/`h2` hypotheses, so it holds for ARBITRARY warm caches). The impl's two
    referral writes (`storeChecked` fold: skip when a strictly-better same-key record is fresh — RFC 2181
    §5.4.1 — else REPLACE the stale same-key RRset and push — §5.2), abstracted, `WriteRefines` the model's
    accumulate-`absorb`:
    (i) *read-soundness from `now`*: at read times ≥ `now`, under `OneExpiryPerKey` every same-key class is
        all-fresh or all-expired, so a skipped record is exactly one the absorb-cache also masks (its blocker
        is fresh whenever the class is), and a replacing push serves a sub-multiset of the absorb's
        (survivors ⊆ base, the pushed entry is in the absorb's added records, and the replaced-away entries
        are either expired at `now` or rank-dominated by the push);
    (ii) *all-time provenance*: any record the written cache ever serves, the absorb-cache serves at the same
        time or at `now` (whatever masked it in the absorb is either also present impl-side — contradiction
        with being served — or expired by `now`);
    (iii)–(iv) negatives untouched by positive writes on both sides.
    The remaining warm-cache obligation of the refer capstone, isolated here. -/
theorem refer_write_WriteRefines (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (cut : ByteArray) (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (aa : Bool) (haa : aa = false)
    (hcut : αName cut = some bwN) (htc : (resp.header.tc == 1) = false)
    (href : (αResp resp).isReferral = true)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hvalA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hvalD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hnoD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmapA : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority), RRCanonMappable e)
    (hcanmapD : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional), RRCanonMappable e) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
            (VeriDNS.Impl.Resolver.credAuthority aa) now)
          resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
            VeriDNS.Impl.Resolver.credAdditional now))
      ((αCache c).absorb now.toNat bwN (αResp resp)) := by
  subst haa

  have himpl : VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
          (VeriDNS.Impl.Resolver.credAuthority false) now)
        resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
          VeriDNS.Impl.Resolver.credAdditional now
      = (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
          ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl
            (warmStep VeriDNS.Impl.Resolver.credAdditional now) c) := by
    rw [cacheUnlessTruncated_untruncated _ _ _ _ _ htc, cacheUnlessTruncated_untruncated _ _ _ _ _ htc,
      show VeriDNS.Impl.Resolver.credAuthority false = VeriDNS.Impl.Resolver.credAdditional from rfl,
      ← cacheRRs_append, ← Array.toList_append]
    unfold VeriDNS.Impl.Resolver.cacheRRs warmStep
    rw [← Array.foldl_toList]
    congr 1
    funext acc bytes
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes <;> rfl

  obtain ⟨Q, P, hdec, hsub, hB, hD⟩ :=
    warm_foldl_decomp VeriDNS.Impl.Resolver.credAdditional now
      ((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
        ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList) c

  have hpos := absorb_referral_pos (αCache c) now.toNat bwN (αResp resp) href

  have hposI : (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).pos
      = (c.records.toList.filter Q).filterMap αCacheRR ++ P.filterMap αCacheRR := by
    show (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c).records.toList.filterMap αCacheRR = _
    rw [hdec, List.filterMap_append]

  have hextra : (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList.flatMap (pushOf VeriDNS.Impl.Resolver.credAdditional now)).filterMap αCacheRR
      ++ ((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList.flatMap (pushOf VeriDNS.Impl.Resolver.credAdditional now)).filterMap αCacheRR).Perm
      (((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).authority.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) ++ ((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional))) :=
    refer_extra_perm resp.authority resp.additional cut bwN now false rfl hcut hnoA hnoD hcanmapA hcanmapD
  have hPsub : (P.filterMap αCacheRR).Sublist
      (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList.flatMap (pushOf VeriDNS.Impl.Resolver.credAdditional now)).filterMap αCacheRR
        ++ ((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList.flatMap (pushOf VeriDNS.Impl.Resolver.credAdditional now)).filterMap αCacheRR) := by
    have h1 := hsub.filterMap αCacheRR
    rw [List.flatMap_append, List.filterMap_append] at h1
    exact h1
  have hPmem : ∀ x ∈ P.filterMap αCacheRR, x ∈ ((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).authority.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) ++ ((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) :=
    fun x hx => hextra.mem_iff.mp (hPsub.subset hx)
  have hPcount : ∀ x : VeriDNS.Spec.Net.CacheRR,
      (P.filterMap αCacheRR).count x ≤ (((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).authority.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) ++ ((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional))).count x :=
    fun x => Nat.le_trans (hPsub.count_le x) (Nat.le_of_eq (hextra.count_eq x))

  have hNadd : ∀ x, x ∈ ((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).authority.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) ++ ((VeriDNS.Spec.Net.normalizeTTL ((αResp resp).additional.filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap (modelPushOf now.toNat VeriDNS.Spec.Net.Cred.additional)) → x.cred = VeriDNS.Spec.Net.Cred.additional := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨r, _, hxr⟩ := List.mem_flatMap.mp hx
      exact (mem_modelPushOf hxr).1
    · obtain ⟨r, _, hxr⟩ := List.mem_flatMap.mp hx
      exact (mem_modelPushOf hxr).1

  have hstale_add : ∀ e ∈ c.records.toList, (decide (e.expiry > now)) = true → Q e = false →
      e.credibility = VeriDNS.Spec.Trustworthiness.additionalAuthoritative := by
    intro e he hfr hQe
    by_cases hbet : e.credibility.toCode < (VeriDNS.Impl.Resolver.credAdditional).toCode
    · have h1 := (hB e he hfr hbet).1
      rw [hQe] at h1
      exact absurd h1 (by decide)
    · revert hbet
      cases e.credibility <;> intro hbet <;> first | rfl | exact absurd (by decide) hbet
  have hkeyed_add : ∀ e ∈ c.records.toList, (decide (e.expiry > now)) = true →
      ∀ p ∈ P, entKeyB e p.rr = true →
      e.credibility = VeriDNS.Spec.Trustworthiness.additionalAuthoritative := by
    intro e he hfr p hpP hk
    by_cases hbet : e.credibility.toCode < (VeriDNS.Impl.Resolver.credAdditional).toCode
    · have h1 := (hB e he hfr hbet).2 p hpP
      rw [hk] at h1
      exact absurd h1 (by decide)
    · revert hbet
      cases e.credibility <;> intro hbet <;> first | rfl | exact absurd (by decide) hbet

  have hfresh_toNat : ∀ (e : VeriDNS.Impl.Cache.CacheEntry) (x : VeriDNS.Spec.Net.CacheRR) (n : Nat),
      e ∈ c.records → αCacheRR e = some x → x.fresh n = true → n < e.expiry.toNat := by
    intro e x n he hx hf
    have hexp := αCacheRR_expiry hx (hwf.1 e he).2.1
    unfold VeriDNS.Spec.Net.CacheRR.fresh at hf
    rw [Nat.blt_eq] at hf
    exact Nat.lt_of_lt_of_eq hf hexp
  have hdecide_fresh : ∀ (e : VeriDNS.Impl.Cache.CacheEntry), now.toNat < e.expiry.toNat →
      (decide (e.expiry > now)) = true := by
    intro e h
    rw [decide_eq_true_eq]
    exact UInt32.lt_iff_toNat_lt.mpr h

  have hPfacts : ∀ p ∈ P, ∃ rr, p = (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩ : VeriDNS.Impl.Cache.CacheEntry)
      ∧ (rr.ttl == 0) = false ∧ (αRR rr).isSome = true
      ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat
      ∧ ∃ na, αName rr.name = some na
          ∧ rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo na ∧ (∀ lb ∈ na, lb.size ≤ 63) := by
    intro p hpP
    obtain ⟨b, hbL, rr, hpr, hz, hpe⟩ := mem_flatMap_pushOf (hsub.subset hpP)
    have hval_no : (αRR rr).isSome = true
        ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat := by
      rcases List.mem_append.mp hbL with hb | hb
      · exact ⟨hvalA b hb rr hpr, hnoA b hb rr hpr⟩
      · exact ⟨hvalD b hb rr hpr, hnoD b hb rr hpr⟩
    obtain ⟨na, hna, hcanon, h63⟩ := parseRaw_name_canonical hpr
    exact ⟨rr, hpe, hz, hval_no.1, hval_no.2, na, hna, hcanon, h63⟩

  have hneg : (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
          (VeriDNS.Impl.Resolver.credAuthority false) now)
        resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
          VeriDNS.Impl.Resolver.credAdditional now).negatives = c.negatives := by
    rw [cacheUnlessTruncated_negatives, cacheUnlessTruncated_negatives]
  refine ⟨?_, ?_, fun nowT q => ?_, fun nowT q => ?_⟩
  ·
    intro n hn q
    rw [himpl, List.subperm_ext_iff]
    intro a ha
    have ha2 : a ∈ (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q ∧
        ((αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q).all
          (fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true := by
      have h := ha
      unfold VeriDNS.Spec.Net.Cache.topServed at h
      exact List.mem_filter.mp h
    obtain ⟨hmIa, hgateIa⟩ := ha2
    have hm2 : a ∈ (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).pos ∧
        (a.fresh n && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
          && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)) = true := by
      have h := hmIa
      unfold VeriDNS.Spec.Net.Cache.matching at h
      exact List.mem_filter.mp h
    obtain ⟨hposa, hpreda⟩ := hm2

    have hgateM : ∀ x ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).matching n q,
        x.sameKey a.rr = true → Nat.ble x.cred.rank a.cred.rank = true := by
      intro x hx hkx
      have hx2 : x ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).pos ∧
          (x.fresh n && VeriDNS.Spec.Net.nameEq x.rr.owner q.qname
            && q.qtype.covers x.rr.rtype && (x.rr.cls == q.qclass)) = true := by
        have h := hx
        unfold VeriDNS.Spec.Net.Cache.matching at h
        exact List.mem_filter.mp h
      obtain ⟨hxpos, hxpred⟩ := hx2
      rw [hpos] at hxpos
      rcases List.mem_append.mp hxpos with hxN | hxbase
      · rw [hNadd x hxN]
        exact ble_additional_rank _
      · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
        have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
        by_cases hQx : Q ex = true
        ·
          have hxI : x ∈ (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q := by
            unfold VeriDNS.Spec.Net.Cache.matching
            refine List.mem_filter.mpr ⟨?_, hxpred⟩
            rw [hposI]
            exact List.mem_append_left _
              (List.mem_filterMap.mpr ⟨ex, List.mem_filter.mpr ⟨hexL, hQx⟩, hexα⟩)
          have hall := List.all_eq_true.mp hgateIa x hxI
          rw [hkx] at hall
          simpa using hall
        ·
          have hxfr : x.fresh n = true := by
            have h := hxpred
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
            exact h.1.1.1
          have hfr32 : (decide (ex.expiry > now)) = true :=
            hdecide_fresh ex (Nat.lt_of_le_of_lt hn (hfresh_toNat ex x n hexR hexα hxfr))
          rw [αCacheRR_cred hexα, hstale_add ex hexL hfr32 (by simpa using hQx)]
          exact ble_additional_rank _

    have hcount_pos : List.count a (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).pos
        ≤ List.count a ((αCache c).absorb now.toNat bwN (αResp resp)).pos := by
      rw [hposI, hpos, List.count_append, List.count_append, List.count_append]
      have h1 : List.count a ((c.records.toList.filter Q).filterMap αCacheRR)
          ≤ List.count a ((αCache c).pos) :=
        ((List.filter_sublist).filterMap αCacheRR).count_le a
      have h2 := hPcount a
      rw [List.count_append] at h2
      omega
    have hc1 : List.count a ((αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).topServed n q)
        = List.count a ((αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q) := by
      unfold VeriDNS.Spec.Net.Cache.topServed
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) => ((αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q).all
        (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) hgateIa
    have hc2 : List.count a ((αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q)
        = List.count a (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).pos := by
      unfold VeriDNS.Spec.Net.Cache.matching
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) => e.fresh n && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)) hpreda
    have hc3 : List.count a (((αCache c).absorb now.toNat bwN (αResp resp)).matching n q) = List.count a ((αCache c).absorb now.toNat bwN (αResp resp)).pos := by
      unfold VeriDNS.Spec.Net.Cache.matching
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) => e.fresh n && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)) hpreda
    have hc4 : List.count a (((αCache c).absorb now.toNat bwN (αResp resp)).topServed n q)
        = List.count a (((αCache c).absorb now.toNat bwN (αResp resp)).matching n q) := by
      unfold VeriDNS.Spec.Net.Cache.topServed
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) => (((αCache c).absorb now.toNat bwN (αResp resp)).matching n q).all
        (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
        (topGate_of_ranks hgateM)
    rw [hc1, hc2, hc4, hc3]
    exact hcount_pos
  ·
    intro n q a ha
    rw [himpl] at ha
    have ha2 : a ∈ (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q ∧
        ((αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q).all
          (fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true := by
      have h := ha
      unfold VeriDNS.Spec.Net.Cache.topServed at h
      exact List.mem_filter.mp h
    obtain ⟨hmIa, hgateIa⟩ := ha2
    have hm2 : a ∈ (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).pos ∧
        (a.fresh n && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
          && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)) = true := by
      have h := hmIa
      unfold VeriDNS.Spec.Net.Cache.matching at h
      exact List.mem_filter.mp h
    obtain ⟨hposa, hpreda⟩ := hm2
    have hpreda' : ((a.fresh n = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
        ∧ q.qtype.covers a.rr.rtype = true) ∧ (a.rr.cls == q.qclass) = true := by
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpreda
      exact hpreda

    have hmkTop : ∀ t : Nat, a ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).pos → a.fresh t = true →
        (∀ x ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).matching t q, x.sameKey a.rr = true →
          Nat.ble x.cred.rank a.cred.rank = true) →
        a ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).topServed t q := by
      intro t hpos' hfr hg
      have hma : a ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).matching t q := by
        unfold VeriDNS.Spec.Net.Cache.matching
        refine List.mem_filter.mpr ⟨hpos', ?_⟩
        show (a.fresh t && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
          && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)) = true
        rw [hfr, hpreda'.1.1.2, hpreda'.1.2, hpreda'.2]
        rfl
      unfold VeriDNS.Spec.Net.Cache.topServed
      exact List.mem_filter.mpr ⟨hma, topGate_of_ranks hg⟩

    have hmatchM : ∀ (t : Nat) (x : VeriDNS.Spec.Net.CacheRR), x ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).matching t q →
        x ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).pos ∧ x.fresh t = true := by
      intro t x hx
      have hx2 : x ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).pos ∧
          (x.fresh t && VeriDNS.Spec.Net.nameEq x.rr.owner q.qname
            && q.qtype.covers x.rr.rtype && (x.rr.cls == q.qclass)) = true := by
        have h := hx
        unfold VeriDNS.Spec.Net.Cache.matching at h
        exact List.mem_filter.mp h
      refine ⟨hx2.1, ?_⟩
      have h := hx2.2
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact h.1.1.1
    rw [hposI] at hposa
    rcases List.mem_append.mp hposa with haS | haP
    ·
      obtain ⟨ea, heaF, heaα⟩ := List.mem_filterMap.mp haS
      have heaL : ea ∈ c.records.toList := (List.mem_filter.mp heaF).1
      have heaQ : Q ea = true := (List.mem_filter.mp heaF).2
      have heaR : ea ∈ c.records := Array.mem_def.mpr heaL
      have haBase : a ∈ (αCache c).pos := List.mem_filterMap.mpr ⟨ea, heaL, heaα⟩
      have haM : a ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).pos := by
        rw [hpos]
        exact List.mem_append_right _ haBase
      by_cases hkp : ∃ p ∈ P, entKeyB ea p.rr = true
      ·
        obtain ⟨p, hpP, hkey⟩ := hkp
        obtain ⟨rr, hpe, hz, hval, hno, na, hna, hcanon, h63⟩ := hPfacts p hpP
        subst hpe
        have hne0 : rr.ttl ≠ 0 := by
          intro h0
          rw [h0] at hz
          exact absurd hz (by decide)
        have httl : 0 < rr.ttl.toNat :=
          Nat.pos_of_ne_zero (fun h0 => hne0 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)))

        have hoe2 : VeriDNS.Proof.NameTree.OneExpiryPerKey (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c) := by
          rw [← himpl]
          exact VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated
            (VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hoe _ _ _ _) _ _ _ _
        have hmemEA : ea ∈ (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c).records := by
          rw [Array.mem_def, hdec]
          exact List.mem_append_left _ heaF
        have hmemP : (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩ : VeriDNS.Impl.Cache.CacheEntry) ∈ (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c).records := by
          rw [Array.mem_def, hdec]
          exact List.mem_append_right _ hpP
        have hsk : VeriDNS.Proof.NameTree.SameKey ea.rr rr := by
          have hk := hkey
          unfold entKeyB at hk
          rw [Bool.and_eq_true, Bool.and_eq_true] at hk
          exact ⟨hk.1.1, eq_of_beq hk.1.2, eq_of_beq hk.2⟩
        have hexpEq : ea.expiry = now + rr.ttl.toNat.toUInt32 :=
          hoe2 ea hmemEA (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩ : VeriDNS.Impl.Cache.CacheEntry) hmemP hsk
        have h1 : now.toNat < ea.expiry.toNat := by
          rw [hexpEq, hno]
          omega
        have hfr32 : (decide (ea.expiry > now)) = true := hdecide_fresh ea h1
        have hfrnowA : a.fresh now.toNat = true := by
          have hie := αCacheRR_expiry heaα (hwf.1 ea heaR).2.1
          unfold VeriDNS.Spec.Net.CacheRR.fresh
          rw [Nat.blt_eq]
          exact Nat.lt_of_lt_of_eq h1 hie.symm
        refine ⟨now.toNat, hmkTop now.toNat haM hfrnowA ?_⟩
        intro x hx hkx
        obtain ⟨hxpos, hxfr⟩ := hmatchM now.toNat x hx
        rw [hpos] at hxpos
        rcases List.mem_append.mp hxpos with hxN | hxbase
        · rw [hNadd x hxN]
          exact ble_additional_rank _
        · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
          have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
          have hfr32x : (decide (ex.expiry > now)) = true :=
            hdecide_fresh ex (hfresh_toNat ex x now.toNat hexR hexα hxfr)
          have hekxa : entKeyB ex ea.rr = true :=
            entKeyB_of_sameKey hexα heaα
              (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
              (hwf.2.1 ea heaR a heaα).1 (hwf.2.1 ea heaR a heaα).2 hkx
          have hekxp : entKeyB ex rr = true := entKeyB_trans hekxa hkey
          rw [αCacheRR_cred hexα, hkeyed_add ex hexL hfr32x _ hpP hekxp]
          exact ble_additional_rank _
      ·
        refine ⟨n, hmkTop n haM hpreda'.1.1.1 ?_⟩
        intro x hx hkx
        obtain ⟨hxpos, hxfr⟩ := hmatchM n x hx
        rw [hpos] at hxpos
        rcases List.mem_append.mp hxpos with hxN | hxbase
        · rw [hNadd x hxN]
          exact ble_additional_rank _
        · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
          have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
          by_cases hQx : Q ex = true
          · have hxI : x ∈ (αCache (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c)).matching n q := by
              unfold VeriDNS.Spec.Net.Cache.matching
              refine List.mem_filter.mpr ⟨?_, ?_⟩
              · rw [hposI]
                exact List.mem_append_left _
                  (List.mem_filterMap.mpr ⟨ex, List.mem_filter.mpr ⟨hexL, hQx⟩, hexα⟩)
              · have h := hx
                unfold VeriDNS.Spec.Net.Cache.matching at h
                exact (List.mem_filter.mp h).2
            have hall := List.all_eq_true.mp hgateIa x hxI
            rw [hkx] at hall
            simpa using hall
          · obtain ⟨p', hp', hk'⟩ := hD ex hexL (by simpa using hQx)
            have hekxa : entKeyB ex ea.rr = true :=
              entKeyB_of_sameKey hexα heaα
                (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
                (hwf.2.1 ea heaR a heaα).1 (hwf.2.1 ea heaR a heaα).2 hkx
            exact absurd ⟨p', hp', entKeyB_trans (entKeyB_symm hekxa) hk'⟩ hkp
    ·
      obtain ⟨p, hpP, hpa⟩ := List.mem_filterMap.mp haP
      obtain ⟨rr, hpe, hz, hval, hno, na, hna, hcanon, h63⟩ := hPfacts p hpP
      subst hpe
      have hne0 : rr.ttl ≠ 0 := by
        intro h0
        rw [h0] at hz
        exact absurd hz (by decide)
      have httl : 0 < rr.ttl.toNat :=
        Nat.pos_of_ne_zero (fun h0 => hne0 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)))
      have hfrnow : a.fresh now.toNat = true := by
        have hle : (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.ttl.toNat ≤ (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩ : VeriDNS.Impl.Cache.CacheEntry).expiry.toNat := by
          show rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
          rw [hno]
          omega
        have hie := αCacheRR_expiry hpa hle
        have hie2 : (now + rr.ttl.toNat.toUInt32).toNat = a.insertedAt + a.rr.ttl := hie.symm
        unfold VeriDNS.Spec.Net.CacheRR.fresh
        rw [Nat.blt_eq]
        rw [hno] at hie2
        exact Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right httl) hie2
      have haN := hPmem a haP
      have haM : a ∈ ((αCache c).absorb now.toNat bwN (αResp resp)).pos := by
        rw [hpos]
        exact List.mem_append_left _ haN

      have hownEq : na = a.rr.owner := by
        have hf := (αRR_fields rr a.rr (αCacheRR_rr hpa)).1
        exact Option.some.inj (hna.symm.trans hf)
      have hcanonP : (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner := by
        show rr.name = _
        rw [hcanon, hownEq]
      have h63P : ∀ lb ∈ a.rr.owner, lb.size ≤ 63 := by
        rw [← hownEq]
        exact h63
      refine ⟨now.toNat, hmkTop now.toNat haM hfrnow ?_⟩
      intro x hx hkx
      obtain ⟨hxpos, hxfr⟩ := hmatchM now.toNat x hx
      rw [hpos] at hxpos
      rcases List.mem_append.mp hxpos with hxN | hxbase
      · rw [hNadd x hxN]
        exact ble_additional_rank _
      · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
        have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
        have hfr32x : (decide (ex.expiry > now)) = true :=
          hdecide_fresh ex (hfresh_toNat ex x now.toNat hexR hexα hxfr)
        have hekxp : entKeyB ex rr = true :=
          entKeyB_of_sameKey hexα hpa
            (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
            hcanonP h63P hkx
        rw [αCacheRR_cred hexα, hkeyed_add ex hexL hfr32x _ hpP hekxp]
        exact ble_additional_rank _
  · show VeriDNS.Spec.Net.Cache.negHit _ nowT q = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHit
    rw [hneg, VeriDNS.Spec.Net.absorb_neg]
  · show VeriDNS.Spec.Net.Cache.negHitNx _ nowT q = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHitNx
    rw [hneg, VeriDNS.Spec.Net.absorb_neg]

/-- **Driver-facing form of the warm-write bridge, retargeted onto the model reply and model cache.**
    Composes `refer_write_WriteRefines` with (a) `absorb_resp_congr` — the strengthened `WorldModels`
    section/aa conjuncts pin `αResp resp`'s absorb-relevant fields to `ref`'s, and a referral's answer
    sections are both empty — and (b) `WriteRefines.trans_perm` over `hmme.absorb` (retargeting the base
    cache `αCache c → cm` through the `StateModels` correspondence). This is exactly the `hcf0` obligation
    of `Resolves.referForget` for the honest referral arms of the `ioResumeLoop_sound` driver. -/
theorem refer_write_WriteRefines_ref (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (cut : ByteArray) (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (aa : Bool) (haa : aa = false)
    (hcut : αName cut = some bwN) (htc : (resp.header.tc == 1) = false)
    (href : (αResp resp).isReferral = true)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hvalA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hvalD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hnoD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmapA : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority), RRCanonMappable e)
    (hcanmapD : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional), RRCanonMappable e)
    (ref : VeriDNS.Spec.Net.Response) (cm : VeriDNS.Spec.Net.Cache)
    (hrefIs : ref.isReferral = true)
    (hauthEq : αSection resp.authority = ref.authority)
    (haddEq : αSection resp.additional = ref.additional)
    (haaEq : (resp.header.aa == 1) = ref.aa)
    (hmme : MatchMaxEquiv (αCache c) cm) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
            (VeriDNS.Impl.Resolver.credAuthority aa) now)
          resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
            VeriDNS.Impl.Resolver.credAdditional now))
      (cm.absorb now.toNat bwN ref) := by
  have h0 := refer_write_WriteRefines c resp cut bwN now aa haa hcut htc href hwf hoe hvalA hvalD hnoA hnoD hcanmapA hcanmapD
  have hcongr : (αCache c).absorb now.toNat bwN (αResp resp) = (αCache c).absorb now.toNat bwN ref :=
    VeriDNS.Spec.Net.absorb_resp_congr _ _ _ haaEq
      ((VeriDNS.Spec.Net.Response.isReferral_answer_nil href).trans
        (VeriDNS.Spec.Net.Response.isReferral_answer_nil hrefIs).symm)
      hauthEq haddEq
  rw [hcongr] at h0
  have hmabs := hmme.absorb now.toNat bwN ref
  exact h0.trans_perm hmabs.1 hmabs.2.1 hmabs.2.2

/-- **`ModelOneExpiry (αCache c)` descends from the impl `OneExpiryPerKey c`** (+ `CacheWf`). A model `sameKey`
    match between two abstracted entries reflects an impl `SameKey` (owner via `nameEqCI_of_αName_canonical` +
    `CacheWf` canonicity; type/class via `αType_injective`/`αClass_inj`), so the impl one-expiry-per-key gives equal
    impl expiry, which `αCacheRR_expiry` lifts to equal model expiry. The invariant `MatchMaxEquiv.filterPos` needs. -/
theorem ModelOneExpiry_αCache (c : VeriDNS.Impl.Cache.DnsCache) (now : UInt32)
    (hwf : CacheWf c now) (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c) :
    ModelOneExpiry (αCache c) := by
  intro ce₁ hce₁ ce₂ hce₂ hk
  simp only [αCache, List.mem_filterMap] at hce₁ hce₂
  obtain ⟨e₁, he₁, hα₁⟩ := hce₁
  obtain ⟨e₂, he₂, hα₂⟩ := hce₂
  have he₁' : e₁ ∈ c.records := by simpa using he₁
  have he₂' : e₂ ∈ c.records := by simpa using he₂
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at hk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨⟨hkn, hkt⟩, hkc⟩ := hk
  have hf₁ := αRR_fields e₁.rr ce₁.rr (αCacheRR_rr hα₁)
  have hf₂ := αRR_fields e₂.rr ce₂.rr (αCacheRR_rr hα₂)
  have hrt₁ := αRR_rtype e₁.rr ce₁.rr (αCacheRR_rr hα₁)
  have hrt₂ := αRR_rtype e₂.rr ce₂.rr (αCacheRR_rr hα₂)
  have hcan₁ := hwf.2.1 e₁ he₁' ce₁ hα₁
  have hcan₂ := hwf.2.1 e₂ he₂' ce₂ hα₂
  have hsk : VeriDNS.Proof.NameTree.SameKey e₁.rr e₂.rr := by
    refine ⟨nameEqCI_of_αName_canonical hkn hcan₁.1 hcan₂.1 hcan₁.2 hcan₂.2, ?_, ?_⟩
    · have ht : ce₁.rr.rdata.rtype = ce₂.rr.rdata.rtype := rrtype_eq_of_beq hkt
      exact αType_injective hrt₁ (by rw [ht]; exact hrt₂)
    · have hc : ce₁.rr.cls = ce₂.rr.cls := rrclass_eq_of_beq hkc
      exact αClass_inj hf₁.2.2 (by rw [hc]; exact hf₂.2.2)
  have hexp := hoe e₁ he₁' e₂ he₂' hsk
  rw [αCacheRR_expiry hα₁ (hwf.1 e₁ he₁').2.1, αCacheRR_expiry hα₂ (hwf.1 e₂ he₂').2.1, hexp]

/-- **`boundExpiryClasses` (capacity eviction) preserves `CacheWf`.** Eviction only removes records
    (`evictClasses` is a `filter` by expiry — `evictClasses_filter_form`), so the per-record invariant survives.
    Together with the (harder) `absorb`/`storeChecked` preservation this would thread `CacheWf` through the
    `boundStateCache` wrap on a referral `.continue`. -/
theorem CacheWf_boundExpiryClasses (c : VeriDNS.Impl.Cache.DnsCache) (now : UInt32)
    (h : CacheWf c now) : CacheWf c.boundExpiryClasses now := by
  refine CacheWf_mono (c := c) ?_ h
  intro e he
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp] at he
  exact (Array.mem_filter.mp he).1

/-- **`storeChecked` preserves `CacheWf`** given the freshly-stored record is canonical. `storeChecked` either
    leaves the cache (`ttl = 0` or a strictly-better entry already present) or `store`s, which keeps a SUBSET of
    the old records (a dedup `filter`) and pushes ONE new entry `⟨rr, now+ttl, false, cred⟩`. Old records keep
    the invariant (subset); the new one needs the per-record hypotheses — which the `absorb` caller discharges
    from the wire parse: `αCacheRR` is `some` and the owner is canonical (`parseRaw_name_canonical`), the
    expiry window is sane (no TTL overflow), and `cred` is one of the four impl tiers. The decomposition point
    of `CacheWf`'s `absorb` preservation. -/
theorem CacheWf_storeChecked (c : VeriDNS.Impl.Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheWf c now)
    (hwfNew : (αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome
        ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
        ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
    (hcanonNew : ∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = some a →
        rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hcredNew : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative) :
    CacheWf (c.storeChecked rr cred now) now := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := rfl
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩
    · rw [hrec, Array.mem_push] at he
      rcases he with he | rfl
      · exact h.1 e (Array.mem_filter.mp he).1
      · exact hwfNew
    · rw [hrec, Array.mem_push] at he
      rcases he with he | rfl
      · exact h.2.1 e (Array.mem_filter.mp he).1
      · exact hcanonNew
    · rw [hrec, Array.mem_push] at he
      rcases he with he | rfl
      · exact h.2.2 e (Array.mem_filter.mp he).1
      · exact hcredNew

/-- **`CacheWf` preserved by a `storeChecked` fold** (the list core of the `absorb` preservation). Folding
    `parse-then-storeChecked` over a list of raws keeps `CacheWf`, given each raw that parses yields a canonical
    record (the per-raw hyp the `absorb` caller discharges from `parseRaw_name_canonical`) and the uniform `cred`
    is one of the four tiers. Each step applies `CacheWf_storeChecked`. -/
theorem CacheWf_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative) :
    ∀ (l : List ByteArray) (cache : VeriDNS.Impl.Cache.DnsCache), CacheWf cache now →
      (∀ bytes ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome
            ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
            ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
          ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = some a →
              rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))) →
      CacheWf (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) now := by
  intro l
  induction l with
  | nil => intro cache hc _; exact hc
  | cons b bs ih =>
    intro cache hc hraw
    rw [List.foldl_cons]
    apply ih
    · cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => simp only [hp]; exact hc
      | some rr =>
        simp only [hp]
        obtain ⟨hwf, hcanon⟩ := hraw b (List.mem_cons_self ..) rr hp
        exact CacheWf_storeChecked cache rr cred now hc hwf hcanon hcred
    · intro bytes hb rr hp; exact hraw bytes (List.mem_cons_of_mem _ hb) rr hp

/-- **`CacheWf` preserved by `cacheRRs`** (one referral section write). `cacheRRs` is the `acceptRrset`
    (=`storeChecked`) fold over the raws; bridges to `CacheWf_foldl_storeChecked` via `Array.foldl_toList`. -/
theorem CacheWf_cacheRRs (cache : VeriDNS.Impl.Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheWf cache now)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome
            ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
            ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
          ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = some a →
              rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))) :
    CacheWf (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) now := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheWf_foldl_storeChecked cred now hcred raws.toList cache h hraw

/-- **`CacheWf` preserved by `cacheUnlessTruncated`** — either the cache is untouched (truncated reply) or it is
    a `cacheRRs` write. One half of a referral `absorb` (the other is the same with the additional section). -/
theorem CacheWf_cacheUnlessTruncated (cache : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheWf cache now)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hraw : ∀ bytes ∈ (VeriDNS.Impl.Cache.normRaws raws).toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome
            ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
            ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
          ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = some a →
              rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))) :
    CacheWf (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) now := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]; exact CacheWf_cacheRRs cache _ cred now h hcred hraw

/-- **Every cacheable raw's key is REPRESENTED in the warm-fold result at tier ≤ `cred`'s code**
    (the skip-blocker invariant the general-cred write bridge needs). For each parsed, `ttl ≠ 0` raw of
    the fold list, the final cache holds SOME same-key entry at least as trustworthy as the fold tier:
    either the raw's push (or a later same-key push, both at exactly `cred`) survives, or the push was
    skipped because a strictly-better same-key record was live (RFC 2181 §5.4.1's `betterExists`) — and
    that blocker, being fresh at `now` and strictly better, is protected by `warm_foldl_decomp`'s INV-B
    for the rest of the fold. This is what replaces `refer_write_WriteRefines`'s minimal-rank shortcut
    (`ble_additional_rank`) when the write tier is NOT minimal (the CNAME answer write can be
    `authoritativeSection`): a model-inserted record's key always has a written-cache witness whose
    model rank is ≥ the write tier's, so the `topServed` gate transfers. -/
theorem warm_foldl_key_covered (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (c : VeriDNS.Impl.Cache.DnsCache),
      (∀ b ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) →
      ∀ b ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (rr.ttl == 0) = false →
      ∃ e ∈ (l.foldl (warmStep cred now) c).records.toList,
        entKeyB e rr = true ∧ e.credibility.toCode ≤ cred.toCode := by
  intro l
  induction l with
  | nil => intro c _ b hb; exact absurd hb (by simp)
  | cons b0 rest ih =>
    intro c hno b hb rr hpr hz
    rw [List.foldl_cons]
    have hnoR : ∀ b' ∈ rest, ∀ rr',
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr' →
        (now + rr'.ttl.toNat.toUInt32).toNat = now.toNat + rr'.ttl.toNat :=
      fun b' hb' rr' hpr' => hno b' (List.mem_cons_of_mem _ hb') rr' hpr'
    rcases List.mem_cons.mp hb with rfl | hbR
    ·
      rw [warm_step_some cred now c hpr]
      have hne0 : rr.ttl ≠ 0 := by
        intro h0; rw [h0] at hz; exact absurd hz (by decide)
      have httl : 0 < rr.ttl.toNat :=
        Nat.pos_of_ne_zero (fun h0 => hne0 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)))
      have hexpNat : (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat :=
        hno b (List.mem_cons_self ..) rr hpr
      by_cases hbb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type
            && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      ·
        have hstep : c.storeChecked rr cred now = c := by
          unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
          rw [if_neg (show ¬((rr.ttl == 0) = true) by rw [hz]; simp)]
          exact if_pos hbb
        rw [hstep]
        rw [Array.any_eq_true] at hbb
        obtain ⟨i, hi, hpred⟩ := hbb
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred
        obtain ⟨⟨⟨⟨hknm, hkty⟩, hkcl⟩, hlive⟩, hbet⟩ := hpred
        have heL : c.records[i] ∈ c.records.toList := by
          rw [← Array.getElem_toList]
          exact List.getElem_mem _
        have hkey : entKeyB c.records[i] rr = true := by
          unfold entKeyB
          rw [hknm, hkty, hkcl]
          rfl
        have hfr : (decide (c.records[i].expiry > now)) = true := by
          rcases Bool.or_eq_true_iff.mp hlive with h | h
          · exact h
          · have hexpEq : c.records[i].expiry = now + rr.ttl.toNat.toUInt32 := eq_of_beq h
            rw [decide_eq_true_eq]
            apply UInt32.lt_iff_toNat_lt.mpr
            rw [hexpEq, hexpNat]
            omega
        have hbet' : c.records[i].credibility.toCode < cred.toCode := of_decide_eq_true hbet
        obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := warm_foldl_decomp cred now rest c
        have hQ := (hB c.records[i] heL hfr hbet').1
        refine ⟨c.records[i], ?_, hkey, Nat.le_of_lt hbet'⟩
        rw [hdec]
        exact List.mem_append_left _ (List.mem_filter.mpr ⟨heL, hQ⟩)
      ·
        have hstep : c.storeChecked rr cred now = c.store rr now cred := by
          unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
          rw [if_neg (show ¬((rr.ttl == 0) = true) by rw [hz]; simp)]
          exact if_neg hbb
        rw [hstep]
        have hmemz : (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :
            VeriDNS.Impl.Cache.CacheEntry) ∈ (c.store rr now cred).records.toList := by
          show _ ∈ ((c.records.filter _).push _).toList
          rw [Array.toList_push]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hkeyz : entKeyB (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :
            VeriDNS.Impl.Cache.CacheEntry) rr = true := by
          unfold entKeyB
          rw [VeriDNS.Proof.NameTree.nameEqCI_refl]
          simp
        obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := warm_foldl_decomp cred now rest (c.store rr now cred)
        by_cases hQz : Q ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = true
        · refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩, ?_, hkeyz, Nat.le_refl _⟩
          rw [hdec]
          exact List.mem_append_left _ (List.mem_filter.mpr ⟨hmemz, hQz⟩)
        · obtain ⟨p, hpP, hpk⟩ := hD _ hmemz (by simpa using hQz)
          obtain ⟨b', hb', rr', hpr', hz', hpe⟩ := mem_flatMap_pushOf (hsub.subset hpP)
          have hpcred : p.credibility = cred := by rw [hpe]
          refine ⟨p, ?_, ?_, by rw [hpcred]; exact Nat.le_refl _⟩
          · rw [hdec]
            exact List.mem_append_right _ hpP
          · exact entKeyB_trans (entKeyB_symm hpk) hkeyz
    ·
      exact ih (warmStep cred now c b0) hnoR b hbR rr hpr hz

/-- **The written-cache representative gate** (the general-cred replacement for the referral proof's
    per-case `ble_additional_rank` closings). If `a` (abstraction of `ent`) passes the written cache's
    `topServed` max-rank gate at read time `n` — fresh, matching `q` — then EVERY same-key entry `e` of
    the written cache bounds its model rank by `a`'s: `e` abstracts (CacheWf), is fresh at `n` (same-key
    entries share `ent`'s expiry by `OneExpiryPerKey`), matches `q` (the key determines owner/type/class
    up to the abstraction), so the gate `hgateIa` applies to it. Instantiated at the `warm_foldl_key_covered`
    witness (rank ≥ write tier) and at pushed entries (rank = write tier), this transfers the model
    absorb-side rank comparisons into the impl gate. -/
theorem written_rep_rank_le (W : VeriDNS.Impl.Cache.DnsCache) (now : UInt32) (n : Nat)
    (q : VeriDNS.Spec.Net.Query)
    (hwfW : CacheWf W now) (hoeW : VeriDNS.Proof.NameTree.OneExpiryPerKey W)
    {a : VeriDNS.Spec.Net.CacheRR} {ent : VeriDNS.Impl.Cache.CacheEntry}
    (hentR : ent ∈ W.records) (hentα : αCacheRR ent = some a)
    (hgateIa : ((αCache W).matching n q).all
        (fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true)
    (hafr : a.fresh n = true)
    (hname : VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
    (hcov : q.qtype.covers a.rr.rtype = true)
    (hcls : (a.rr.cls == q.qclass) = true)
    {e : VeriDNS.Impl.Cache.CacheEntry} (heW : e ∈ W.records) (hk : entKeyB e ent.rr = true) :
    Nat.ble (αCred e.credibility).rank a.cred.rank = true := by
  obtain ⟨xe, hxe⟩ := Option.isSome_iff_exists.mp (hwfW.1 e heW).1
  have hskM : xe.sameKey a.rr = true := αRR_sameKey e ent xe a hxe hentα hk

  have hSK : VeriDNS.Proof.NameTree.SameKey e.rr ent.rr := by
    have hk' := hk
    unfold entKeyB at hk'
    rw [Bool.and_eq_true, Bool.and_eq_true] at hk'
    exact ⟨hk'.1.1, eq_of_beq hk'.1.2, eq_of_beq hk'.2⟩
  have hexpEq : e.expiry = ent.expiry := hoeW e heW ent hentR hSK
  have hentExp : a.insertedAt + a.rr.ttl = ent.expiry.toNat :=
    αCacheRR_expiry hentα (hwfW.1 ent hentR).2.1
  have hnlt : n < ent.expiry.toNat := by
    unfold VeriDNS.Spec.Net.CacheRR.fresh at hafr
    rw [Nat.blt_eq] at hafr
    rw [← hentExp]
    exact hafr
  have hxefr : xe.fresh n = true := by
    unfold VeriDNS.Spec.Net.CacheRR.fresh
    rw [Nat.blt_eq, αCacheRR_expiry hxe (hwfW.1 e heW).2.1, hexpEq]
    exact hnlt

  have hskM' := hskM
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at hskM'
  rw [Bool.and_eq_true, Bool.and_eq_true] at hskM'
  obtain ⟨⟨hnm, hty⟩, hcl⟩ := hskM'
  have hxeM : xe ∈ (αCache W).matching n q := by
    unfold VeriDNS.Spec.Net.Cache.matching
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · exact List.mem_filterMap.mpr ⟨e, Array.mem_def.mp heW, hxe⟩
    · show (xe.fresh n && VeriDNS.Spec.Net.nameEq xe.rr.owner q.qname
        && q.qtype.covers xe.rr.rtype && (xe.rr.cls == q.qclass)) = true
      rw [hxefr, VeriDNS.Spec.Net.nameEq_trans hnm hname, rrtype_eq_of_beq hty,
        rrclass_eq_of_beq hcl, hcov, hcls]
      rfl
  have hall := List.all_eq_true.mp hgateIa xe hxeM
  rw [hskM] at hall
  rw [← αCacheRR_cred hxe]
  simpa using hall

/-- **The GENERAL single-section warm-write `WriteRefines`** (the `cred`-generic core of
    `refer_write_WriteRefines`, freed from the referral's minimal-rank shortcut). One impl
    `cacheUnlessTruncated` write of `raws` at an arbitrary resolver tier `cred` (any of the four used
    tiers) refines any model cache `M` whose positives decompose as `N ++ (αCache c).pos` with `N` a
    permutation of the abstracted would-be pushes, all at `αCred cred` — the shape every `absorb`
    produces for a single section. Where the referral proof closed rank obligations with
    `ble_additional_rank` (its tier is the MINIMUM), this proof uses:
    * `warm_foldl_key_covered` — every model-inserted record's key has a written-cache witness at
      tier-code ≤ `cred` (the push survives, a later same-key push survives, or the skip's
      strictly-better blocker survives);
    * `written_rep_rank_le` — any same-key written-cache entry's model rank is bounded by a served
      record's rank (through the impl `topServed` gate, freshness transferred by `OneExpiryPerKey`);
    * `αCred_order_used` — the impl `toCode` order and model `Cred.rank` order agree (reversed) on the
      four used tiers, converting the fold's `betterExists`/INV-B code comparisons into rank bounds.
    A key-repushed survivor at strictly lower rank than `cred` additionally yields a CONTRADICTION with
    its own gate (the pushed same-key entry outranks it), replacing the referral's vacuous sub-case. -/
theorem single_cred_write_WriteRefines (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (M : VeriDNS.Spec.Net.Cache) (N : List VeriDNS.Spec.Net.CacheRR)
    (htc : (resp.header.tc == 1) = false)
    (hcredU : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws raws).toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws raws).toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hMpos : M.pos = N ++ (αCache c).pos)
    (hNperm : (((VeriDNS.Impl.Cache.normRaws raws).toList.flatMap (pushOf cred now)).filterMap αCacheRR).Perm N)
    (hNcred : ∀ x ∈ N, x.cred = αCred cred)
    (hMnegHit : ∀ nT q, M.negHit nT q = (αCache c).negHit nT q)
    (hMnegHitNx : ∀ nT q, M.negHitNx nT q = (αCache c).negHitNx nT q) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now)) M := by

  have himpl : VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c resp raws cred now = (VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c := by
    rw [cacheUnlessTruncated_untruncated _ _ _ _ _ htc]
    unfold VeriDNS.Impl.Resolver.cacheRRs warmStep
    rw [← Array.foldl_toList]
    congr 1
    funext acc bytes
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes <;> rfl

  obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := warm_foldl_decomp cred now (VeriDNS.Impl.Cache.normRaws raws).toList c

  have hposI : (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).pos
      = (c.records.toList.filter Q).filterMap αCacheRR ++ P.filterMap αCacheRR := by
    show ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records.toList.filterMap αCacheRR = _
    rw [hdec, List.filterMap_append]
  have hPsub : (P.filterMap αCacheRR).Sublist
      (((VeriDNS.Impl.Cache.normRaws raws).toList.flatMap (pushOf cred now)).filterMap αCacheRR) :=
    hsub.filterMap αCacheRR
  have hPmem : ∀ x ∈ P.filterMap αCacheRR, x ∈ N :=
    fun x hx => hNperm.mem_iff.mp (hPsub.subset hx)
  have hPcount : ∀ x : VeriDNS.Spec.Net.CacheRR, (P.filterMap αCacheRR).count x ≤ N.count x :=
    fun x => Nat.le_trans (hPsub.count_le x) (Nat.le_of_eq (hNperm.count_eq x))

  have hrawWf : ∀ bytes ∈ (VeriDNS.Impl.Cache.normRaws raws).toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
      ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome
          ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
          ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
        ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = some a →
            rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner
              ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63)) := by
    intro bytes hby rr hpr
    have hv := hval bytes hby rr hpr
    have hn := hno bytes hby rr hpr
    refine ⟨⟨?_, by omega, by omega⟩, ?_⟩
    · show ((αRR rr).map _).isSome = true
      cases hαr : αRR rr with
      | none => rw [hαr] at hv; exact absurd hv (by simp)
      | some r => rfl
    · intro a ha
      obtain ⟨na, hna, hcan, h63⟩ := parseRaw_name_canonical hpr
      have hown : αName rr.name = some a.rr.owner := (αRR_fields rr a.rr (αCacheRR_rr ha)).1
      have hnaEq : na = a.rr.owner := Option.some.inj (hna.symm.trans hown)
      rw [← hnaEq]
      exact ⟨hcan, h63⟩
  have hwfW : CacheWf ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c) now := by
    rw [← himpl]
    exact CacheWf_cacheUnlessTruncated c resp raws cred now hwf hcredU hrawWf
  have hoeW : VeriDNS.Proof.NameTree.OneExpiryPerKey ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c) := by
    rw [← himpl]
    exact VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hoe resp raws cred now

  have hfresh_toNat : ∀ (e : VeriDNS.Impl.Cache.CacheEntry) (x : VeriDNS.Spec.Net.CacheRR) (n : Nat),
      e ∈ c.records → αCacheRR e = some x → x.fresh n = true → n < e.expiry.toNat := by
    intro e x n he hx hf
    have hexp := αCacheRR_expiry hx (hwf.1 e he).2.1
    unfold VeriDNS.Spec.Net.CacheRR.fresh at hf
    rw [Nat.blt_eq] at hf
    exact Nat.lt_of_lt_of_eq hf hexp
  have hdecide_fresh : ∀ (e : VeriDNS.Impl.Cache.CacheEntry), now.toNat < e.expiry.toNat →
      (decide (e.expiry > now)) = true := by
    intro e h
    rw [decide_eq_true_eq]
    exact UInt32.lt_iff_toNat_lt.mpr h

  have hstale_ge : ∀ e ∈ c.records.toList, (decide (e.expiry > now)) = true → Q e = false →
      cred.toCode ≤ e.credibility.toCode := by
    intro e he hfr hQe
    by_cases hbet : e.credibility.toCode < cred.toCode
    · have h1 := (hB e he hfr hbet).1
      rw [hQe] at h1
      exact absurd h1 (by decide)
    · omega
  have hkeyed_ge : ∀ e ∈ c.records.toList, (decide (e.expiry > now)) = true →
      ∀ p ∈ P, entKeyB e p.rr = true → cred.toCode ≤ e.credibility.toCode := by
    intro e he hfr p hpP hk
    by_cases hbet : e.credibility.toCode < cred.toCode
    · have h1 := (hB e he hfr hbet).2 p hpP
      rw [hk] at h1
      exact absurd h1 (by decide)
    · omega

  have hPfacts : ∀ p ∈ P, ∃ rr, p = (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry)
      ∧ (rr.ttl == 0) = false ∧ (αRR rr).isSome = true
      ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat
      ∧ ∃ na, αName rr.name = some na
          ∧ rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo na ∧ (∀ lb ∈ na, lb.size ≤ 63) := by
    intro p hpP
    obtain ⟨b, hbL, rr, hpr, hz, hpe⟩ := mem_flatMap_pushOf (hsub.subset hpP)
    obtain ⟨na, hna, hcanon, h63⟩ := parseRaw_name_canonical hpr
    exact ⟨rr, hpe, hz, hval b hbL rr hpr, hno b hbL rr hpr, na, hna, hcanon, h63⟩

  have hneg : (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c resp raws cred now).negatives = c.negatives :=
    cacheUnlessTruncated_negatives c resp raws cred now
  refine ⟨?_, ?_, fun nowT q => ?_, fun nowT q => ?_⟩
  ·
    intro n hn q
    rw [himpl, List.subperm_ext_iff]
    intro a ha
    have ha2 : a ∈ (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q ∧
        ((αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q).all
          (fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true := by
      have h := ha
      unfold VeriDNS.Spec.Net.Cache.topServed at h
      exact List.mem_filter.mp h
    obtain ⟨hmIa, hgateIa⟩ := ha2
    have hm2 : a ∈ (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).pos ∧
        (a.fresh n && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
          && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)) = true := by
      have h := hmIa
      unfold VeriDNS.Spec.Net.Cache.matching at h
      exact List.mem_filter.mp h
    obtain ⟨hposa, hpreda⟩ := hm2
    have hpreda' : ((a.fresh n = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
        ∧ q.qtype.covers a.rr.rtype = true) ∧ (a.rr.cls == q.qclass) = true := by
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpreda
      exact hpreda
    obtain ⟨ent, hentR, hentα⟩ := mem_αCache_pos _ a hposa
    have hrep : ∀ e ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records, entKeyB e ent.rr = true →
        Nat.ble (αCred e.credibility).rank a.cred.rank = true :=
      fun e heW hk => written_rep_rank_le _ now n q hwfW hoeW hentR hentα hgateIa
        hpreda'.1.1.1 hpreda'.1.1.2 hpreda'.1.2 hpreda'.2 heW hk

    have hgateM : ∀ x ∈ M.matching n q, x.sameKey a.rr = true →
        Nat.ble x.cred.rank a.cred.rank = true := by
      intro x hx hkx
      have hx2 : x ∈ M.pos ∧ (x.fresh n && VeriDNS.Spec.Net.nameEq x.rr.owner q.qname
          && q.qtype.covers x.rr.rtype && (x.rr.cls == q.qclass)) = true := by
        have h := hx
        unfold VeriDNS.Spec.Net.Cache.matching at h
        exact List.mem_filter.mp h
      obtain ⟨hxpos, hxpred⟩ := hx2
      rw [hMpos] at hxpos
      rcases List.mem_append.mp hxpos with hxN | hxbase
      ·
        have hxE : x ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.flatMap (pushOf cred now)).filterMap αCacheRR :=
          hNperm.mem_iff.mpr hxN
        obtain ⟨pe, hpeL, hpeα⟩ := List.mem_filterMap.mp hxE
        obtain ⟨braw, hbrawL, rrx, hprx, hzx, hpee⟩ := mem_flatMap_pushOf hpeL
        subst hpee
        obtain ⟨na, hna, hcanon, h63⟩ := parseRaw_name_canonical hprx
        have hown : αName rrx.name = some x.rr.owner := (αRR_fields rrx x.rr (αCacheRR_rr hpeα)).1
        have hnaEq : na = x.rr.owner := Option.some.inj (hna.symm.trans hown)
        have hcanPe : (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name
            = VeriDNS.Impl.DomainName.labelsToWireFormatGo x.rr.owner := by
          show rrx.name = _
          rw [hcanon, hnaEq]
        have h63Pe : ∀ lb ∈ x.rr.owner, lb.size ≤ 63 := by
          rw [← hnaEq]; exact h63
        have hkPeEnt : entKeyB (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry) ent.rr = true :=
          entKeyB_of_sameKey hpeα hentα hcanPe h63Pe
            (hwfW.2.1 ent hentR a hentα).1 (hwfW.2.1 ent hentR a hentα).2 hkx
        obtain ⟨e, heL, hek, hle⟩ := warm_foldl_key_covered cred now (VeriDNS.Impl.Cache.normRaws raws).toList c hno braw hbrawL rrx hprx hzx
        have heW : e ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records := Array.mem_def.mpr heL
        have hkE : entKeyB e ent.rr = true :=
          entKeyB_trans (show entKeyB e (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).rr = true from hek) hkPeEnt
        have hrk := hrep e heW hkE
        have hup : (αCred cred).rank ≤ (αCred e.credibility).rank :=
          (αCred_order_used e.credibility cred (hwfW.2.2 e heW) hcredU).mp hle
        rw [hNcred x hxN]
        exact Nat.ble_eq.mpr (Nat.le_trans hup (Nat.ble_eq.mp hrk))
      · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
        have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
        by_cases hQx : Q ex = true
        ·
          have hxI : x ∈ (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q := by
            unfold VeriDNS.Spec.Net.Cache.matching
            refine List.mem_filter.mpr ⟨?_, hxpred⟩
            rw [hposI]
            exact List.mem_append_left _
              (List.mem_filterMap.mpr ⟨ex, List.mem_filter.mpr ⟨hexL, hQx⟩, hexα⟩)
          have hall := List.all_eq_true.mp hgateIa x hxI
          rw [hkx] at hall
          simpa using hall
        ·
          have hxfr : x.fresh n = true := by
            have h := hxpred
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
            exact h.1.1.1
          have hfr32 : (decide (ex.expiry > now)) = true :=
            hdecide_fresh ex (Nat.lt_of_le_of_lt hn (hfresh_toNat ex x n hexR hexα hxfr))
          have hgeCode : cred.toCode ≤ ex.credibility.toCode :=
            hstale_ge ex hexL hfr32 (by simpa using hQx)
          obtain ⟨p, hpP, hkp⟩ := hD ex hexL (by simpa using hQx)
          have hpW : p ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records :=
            Array.mem_def.mpr (by rw [hdec]; exact List.mem_append_right _ hpP)
          have hkxEnt : entKeyB ex ent.rr = true :=
            entKeyB_of_sameKey hexα hentα
              (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
              (hwfW.2.1 ent hentR a hentα).1 (hwfW.2.1 ent hentR a hentα).2 hkx
          have hkPEnt : entKeyB p ent.rr = true := entKeyB_trans (entKeyB_symm hkp) hkxEnt
          have hrkp := hrep p hpW hkPEnt
          obtain ⟨rrp, hpe, -, -, -, -⟩ := hPfacts p hpP
          have hpcred : p.credibility = cred := by rw [hpe]
          rw [hpcred] at hrkp
          have hdown : (αCred ex.credibility).rank ≤ (αCred cred).rank :=
            (αCred_order_used cred ex.credibility hcredU (hwf.2.2 ex hexR)).mp hgeCode
          rw [αCacheRR_cred hexα]
          exact Nat.ble_eq.mpr (Nat.le_trans hdown (Nat.ble_eq.mp hrkp))

    have hcount_pos : List.count a (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).pos
        ≤ List.count a M.pos := by
      rw [hposI, hMpos, List.count_append, List.count_append]
      have h1 : List.count a ((c.records.toList.filter Q).filterMap αCacheRR)
          ≤ List.count a ((αCache c).pos) :=
        ((List.filter_sublist).filterMap αCacheRR).count_le a
      have h2 := hPcount a
      omega
    have hc1 : List.count a ((αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).topServed n q)
        = List.count a ((αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q) := by
      unfold VeriDNS.Spec.Net.Cache.topServed
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) =>
        ((αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q).all
          (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) hgateIa
    have hc2 : List.count a ((αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q)
        = List.count a (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).pos := by
      unfold VeriDNS.Spec.Net.Cache.matching
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) =>
        e.fresh n && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
          && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)) hpreda
    have hc3 : List.count a (M.matching n q) = List.count a M.pos := by
      unfold VeriDNS.Spec.Net.Cache.matching
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) =>
        e.fresh n && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
          && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)) hpreda
    have hc4 : List.count a (M.topServed n q) = List.count a (M.matching n q) := by
      unfold VeriDNS.Spec.Net.Cache.topServed
      exact List.count_filter (p := fun (e : VeriDNS.Spec.Net.CacheRR) =>
        (M.matching n q).all
          (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
        (topGate_of_ranks hgateM)
    rw [hc1, hc2, hc4, hc3]
    exact hcount_pos
  ·
    intro n q a ha
    rw [himpl] at ha
    have ha2 : a ∈ (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q ∧
        ((αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q).all
          (fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true := by
      have h := ha
      unfold VeriDNS.Spec.Net.Cache.topServed at h
      exact List.mem_filter.mp h
    obtain ⟨hmIa, hgateIa⟩ := ha2
    have hm2 : a ∈ (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).pos ∧
        (a.fresh n && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
          && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)) = true := by
      have h := hmIa
      unfold VeriDNS.Spec.Net.Cache.matching at h
      exact List.mem_filter.mp h
    obtain ⟨hposa, hpreda⟩ := hm2
    have hpreda' : ((a.fresh n = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
        ∧ q.qtype.covers a.rr.rtype = true) ∧ (a.rr.cls == q.qclass) = true := by
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpreda
      exact hpreda
    obtain ⟨ent, hentR, hentα⟩ := mem_αCache_pos _ a hposa
    have hrep : ∀ e ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records, entKeyB e ent.rr = true →
        Nat.ble (αCred e.credibility).rank a.cred.rank = true :=
      fun e heW hk => written_rep_rank_le _ now n q hwfW hoeW hentR hentα hgateIa
        hpreda'.1.1.1 hpreda'.1.1.2 hpreda'.1.2 hpreda'.2 heW hk

    have hmkTop : ∀ t : Nat, a ∈ M.pos → a.fresh t = true →
        (∀ x ∈ M.matching t q, x.sameKey a.rr = true →
          Nat.ble x.cred.rank a.cred.rank = true) →
        a ∈ M.topServed t q := by
      intro t hpos' hfr hg
      have hma : a ∈ M.matching t q := by
        unfold VeriDNS.Spec.Net.Cache.matching
        refine List.mem_filter.mpr ⟨hpos', ?_⟩
        show (a.fresh t && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
          && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)) = true
        rw [hfr, hpreda'.1.1.2, hpreda'.1.2, hpreda'.2]
        rfl
      unfold VeriDNS.Spec.Net.Cache.topServed
      exact List.mem_filter.mpr ⟨hma, topGate_of_ranks hg⟩

    have hmatchM : ∀ (t : Nat) (x : VeriDNS.Spec.Net.CacheRR), x ∈ M.matching t q →
        x ∈ M.pos ∧ x.fresh t = true := by
      intro t x hx
      have hx2 : x ∈ M.pos ∧
          (x.fresh t && VeriDNS.Spec.Net.nameEq x.rr.owner q.qname
            && q.qtype.covers x.rr.rtype && (x.rr.cls == q.qclass)) = true := by
        have h := hx
        unfold VeriDNS.Spec.Net.Cache.matching at h
        exact List.mem_filter.mp h
      refine ⟨hx2.1, ?_⟩
      have h := hx2.2
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact h.1.1.1

    have hgateN : ∀ x ∈ N, x.sameKey a.rr = true → Nat.ble x.cred.rank a.cred.rank = true := by
      intro x hxN hkx
      have hxE : x ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.flatMap (pushOf cred now)).filterMap αCacheRR :=
        hNperm.mem_iff.mpr hxN
      obtain ⟨pe, hpeL, hpeα⟩ := List.mem_filterMap.mp hxE
      obtain ⟨braw, hbrawL, rrx, hprx, hzx, hpee⟩ := mem_flatMap_pushOf hpeL
      subst hpee
      obtain ⟨na, hna, hcanon, h63⟩ := parseRaw_name_canonical hprx
      have hown : αName rrx.name = some x.rr.owner := (αRR_fields rrx x.rr (αCacheRR_rr hpeα)).1
      have hnaEq : na = x.rr.owner := Option.some.inj (hna.symm.trans hown)
      have hcanPe : (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name
          = VeriDNS.Impl.DomainName.labelsToWireFormatGo x.rr.owner := by
        show rrx.name = _
        rw [hcanon, hnaEq]
      have h63Pe : ∀ lb ∈ x.rr.owner, lb.size ≤ 63 := by
        rw [← hnaEq]; exact h63
      have hkPeEnt : entKeyB (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry) ent.rr = true :=
        entKeyB_of_sameKey hpeα hentα hcanPe h63Pe
          (hwfW.2.1 ent hentR a hentα).1 (hwfW.2.1 ent hentR a hentα).2 hkx
      obtain ⟨e, heL, hek, hle⟩ := warm_foldl_key_covered cred now (VeriDNS.Impl.Cache.normRaws raws).toList c hno braw hbrawL rrx hprx hzx
      have heW : e ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records := Array.mem_def.mpr heL
      have hkE : entKeyB e ent.rr = true :=
        entKeyB_trans (show entKeyB e (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).rr = true from hek) hkPeEnt
      have hrk := hrep e heW hkE
      have hup : (αCred cred).rank ≤ (αCred e.credibility).rank :=
        (αCred_order_used e.credibility cred (hwfW.2.2 e heW) hcredU).mp hle
      rw [hNcred x hxN]
      exact Nat.ble_eq.mpr (Nat.le_trans hup (Nat.ble_eq.mp hrk))
    rw [hposI] at hposa
    rcases List.mem_append.mp hposa with haS | haP
    ·
      obtain ⟨ea, heaF, heaα⟩ := List.mem_filterMap.mp haS
      have heaL : ea ∈ c.records.toList := (List.mem_filter.mp heaF).1
      have heaQ : Q ea = true := (List.mem_filter.mp heaF).2
      have heaR : ea ∈ c.records := Array.mem_def.mpr heaL
      have haBase : a ∈ (αCache c).pos := List.mem_filterMap.mpr ⟨ea, heaL, heaα⟩
      have haM : a ∈ M.pos := by
        rw [hMpos]
        exact List.mem_append_right _ haBase
      by_cases hkp : ∃ p ∈ P, entKeyB ea p.rr = true
      ·
        obtain ⟨p, hpP, hkey⟩ := hkp
        obtain ⟨rrp, hpe, hz, hvalp, hnop, na, hna, hcanon, h63⟩ := hPfacts p hpP
        subst hpe
        have hne0 : rrp.ttl ≠ 0 := by
          intro h0
          rw [h0] at hz
          exact absurd hz (by decide)
        have httl : 0 < rrp.ttl.toNat :=
          Nat.pos_of_ne_zero (fun h0 => hne0 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)))
        have hpW : (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry)
            ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records :=
          Array.mem_def.mpr (by rw [hdec]; exact List.mem_append_right _ hpP)
        have heaW : ea ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records :=
          Array.mem_def.mpr (by rw [hdec]; exact List.mem_append_left _ heaF)
        have hsk : VeriDNS.Proof.NameTree.SameKey ea.rr rrp := by
          have hk := hkey
          unfold entKeyB at hk
          rw [Bool.and_eq_true, Bool.and_eq_true] at hk
          exact ⟨hk.1.1, eq_of_beq hk.1.2, eq_of_beq hk.2⟩
        have hexpEq : ea.expiry = now + rrp.ttl.toNat.toUInt32 :=
          hoeW ea heaW (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry) hpW hsk
        have h1 : now.toNat < ea.expiry.toNat := by
          rw [hexpEq, hnop]
          omega
        have hfrnowA : a.fresh now.toNat = true := by
          have hie := αCacheRR_expiry heaα (hwf.1 ea heaR).2.1
          unfold VeriDNS.Spec.Net.CacheRR.fresh
          rw [Nat.blt_eq]
          exact Nat.lt_of_lt_of_eq h1 hie.symm
        have hacred : a.cred = αCred ea.credibility := αCacheRR_cred heaα
        by_cases hrk : (αCred cred).rank ≤ (αCred ea.credibility).rank
        · refine ⟨now.toNat, hmkTop now.toNat haM hfrnowA ?_⟩
          intro x hx hkx
          obtain ⟨hxpos, hxfr⟩ := hmatchM now.toNat x hx
          rw [hMpos] at hxpos
          rcases List.mem_append.mp hxpos with hxN | hxbase
          · rw [hNcred x hxN, hacred]
            exact Nat.ble_eq.mpr hrk
          · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
            have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
            have hfr32x : (decide (ex.expiry > now)) = true :=
              hdecide_fresh ex (hfresh_toNat ex x now.toNat hexR hexα hxfr)
            have hekxa : entKeyB ex ea.rr = true :=
              entKeyB_of_sameKey hexα heaα
                (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
                (hwf.2.1 ea heaR a heaα).1 (hwf.2.1 ea heaR a heaα).2 hkx
            have hekxp : entKeyB ex rrp = true := entKeyB_trans hekxa hkey
            have hgeX : cred.toCode ≤ ex.credibility.toCode :=
              hkeyed_ge ex hexL hfr32x _ hpP hekxp
            have hdownX : (αCred ex.credibility).rank ≤ (αCred cred).rank :=
              (αCred_order_used cred ex.credibility hcredU (hwf.2.2 ex hexR)).mp hgeX
            rw [αCacheRR_cred hexα, hacred]
            exact Nat.ble_eq.mpr (Nat.le_trans hdownX hrk)
        ·
          exfalso
          have hself : a.sameKey a.rr = true := by
            unfold VeriDNS.Spec.Net.CacheRR.sameKey
            rw [VeriDNS.Spec.Net.nameEq_refl, rrtype_beq_self, rrclass_beq_self]
            rfl
          have hkEaEnt : entKeyB ea ent.rr = true :=
            entKeyB_of_sameKey heaα hentα
              (hwf.2.1 ea heaR a heaα).1 (hwf.2.1 ea heaR a heaα).2
              (hwfW.2.1 ent hentR a hentα).1 (hwfW.2.1 ent hentR a hentα).2 hself
          have hkPEnt : entKeyB (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry) ent.rr = true :=
            entKeyB_trans (entKeyB_symm hkey) hkEaEnt
          have hrkp := hrep _ hpW hkPEnt
          apply hrk
          have h2 := Nat.ble_eq.mp hrkp
          rwa [hacred] at h2
      ·
        refine ⟨n, hmkTop n haM hpreda'.1.1.1 ?_⟩
        intro x hx hkx
        obtain ⟨hxpos, hxfr⟩ := hmatchM n x hx
        rw [hMpos] at hxpos
        rcases List.mem_append.mp hxpos with hxN | hxbase
        · exact hgateN x hxN hkx
        · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
          have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
          by_cases hQx : Q ex = true
          · have hxI : x ∈ (αCache ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c)).matching n q := by
              unfold VeriDNS.Spec.Net.Cache.matching
              refine List.mem_filter.mpr ⟨?_, ?_⟩
              · rw [hposI]
                exact List.mem_append_left _
                  (List.mem_filterMap.mpr ⟨ex, List.mem_filter.mpr ⟨hexL, hQx⟩, hexα⟩)
              · have h := hx
                unfold VeriDNS.Spec.Net.Cache.matching at h
                exact (List.mem_filter.mp h).2
            have hall := List.all_eq_true.mp hgateIa x hxI
            rw [hkx] at hall
            simpa using hall
          · obtain ⟨p', hp', hk'⟩ := hD ex hexL (by simpa using hQx)
            have hekxa : entKeyB ex ea.rr = true :=
              entKeyB_of_sameKey hexα heaα
                (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
                (hwf.2.1 ea heaR a heaα).1 (hwf.2.1 ea heaR a heaα).2 hkx
            exact absurd ⟨p', hp', entKeyB_trans (entKeyB_symm hekxa) hk'⟩ hkp
    ·
      obtain ⟨p, hpP, hpa⟩ := List.mem_filterMap.mp haP
      obtain ⟨rrp, hpe, hz, hvalp, hnop, na, hna, hcanon, h63⟩ := hPfacts p hpP
      subst hpe
      have hne0 : rrp.ttl ≠ 0 := by
        intro h0
        rw [h0] at hz
        exact absurd hz (by decide)
      have httl : 0 < rrp.ttl.toNat :=
        Nat.pos_of_ne_zero (fun h0 => hne0 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)))
      have hfrnow : a.fresh now.toNat = true := by
        have hle : (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.ttl.toNat
            ≤ (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).expiry.toNat := by
          show rrp.ttl.toNat ≤ (now + rrp.ttl.toNat.toUInt32).toNat
          rw [hnop]
          omega
        have hie := αCacheRR_expiry hpa hle
        have hie2 : (now + rrp.ttl.toNat.toUInt32).toNat = a.insertedAt + a.rr.ttl := hie.symm
        unfold VeriDNS.Spec.Net.CacheRR.fresh
        rw [Nat.blt_eq]
        rw [hnop] at hie2
        exact Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right httl) hie2
      have haN : a ∈ N := hPmem a (List.mem_filterMap.mpr ⟨_, hpP, hpa⟩)
      have haM : a ∈ M.pos := by
        rw [hMpos]
        exact List.mem_append_left _ haN
      have hacred : a.cred = αCred cred := αCacheRR_cred hpa

      have hownEq : na = a.rr.owner := by
        have hf := (αRR_fields rrp a.rr (αCacheRR_rr hpa)).1
        exact Option.some.inj (hna.symm.trans hf)
      have hcanonP : (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name
          = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner := by
        show rrp.name = _
        rw [hcanon, hownEq]
      have h63P : ∀ lb ∈ a.rr.owner, lb.size ≤ 63 := by
        rw [← hownEq]
        exact h63
      refine ⟨now.toNat, hmkTop now.toNat haM hfrnow ?_⟩
      intro x hx hkx
      obtain ⟨hxpos, hxfr⟩ := hmatchM now.toNat x hx
      rw [hMpos] at hxpos
      rcases List.mem_append.mp hxpos with hxN | hxbase
      · rw [hNcred x hxN, hacred]
        exact Nat.ble_eq.mpr (Nat.le_refl _)
      · obtain ⟨ex, hexR, hexα⟩ := mem_αCache_pos c x hxbase
        have hexL : ex ∈ c.records.toList := Array.mem_def.mp hexR
        have hfr32x : (decide (ex.expiry > now)) = true :=
          hdecide_fresh ex (hfresh_toNat ex x now.toNat hexR hexα hxfr)
        have hekxp : entKeyB ex rrp = true :=
          entKeyB_of_sameKey hexα hpa
            (hwf.2.1 ex hexR x hexα).1 (hwf.2.1 ex hexR x hexα).2
            hcanonP h63P hkx
        have hgeX : cred.toCode ≤ ex.credibility.toCode :=
          hkeyed_ge ex hexL hfr32x _ hpP hekxp
        have hdownX : (αCred ex.credibility).rank ≤ (αCred cred).rank :=
          (αCred_order_used cred ex.credibility hcredU (hwf.2.2 ex hexR)).mp hgeX
        rw [αCacheRR_cred hexα, hacred]
        exact Nat.ble_eq.mpr hdownX
  · show VeriDNS.Spec.Net.Cache.negHit _ nowT q = _
    rw [hMnegHit nowT q]
    unfold αCache VeriDNS.Spec.Net.Cache.negHit
    rw [hneg]
  · show VeriDNS.Spec.Net.Cache.negHitNx _ nowT q = _
    rw [hMnegHitNx nowT q]
    unfold αCache VeriDNS.Spec.Net.Cache.negHitNx
    rw [hneg]

/-- **The CNAME-hop `WriteRefines` — the WARM-CACHE write-path bridge for the chase's answer write**
    (the CNAME analogue of `refer_write_WriteRefines`; supersedes `answerCname_hop_MatchMaxEquiv` for the
    driver: no fresh-push `h1` hypothesis, so it holds for ARBITRARY warm caches). The impl's single CNAME
    write — the ANSWER section, bailiwick-filtered to the queried name `sname`, at `credAnswer aa` —
    abstracted, `WriteRefines` the model's answer-only accumulate-`absorb` at `bwN = αName sname`.
    Instantiates `single_cred_write_WriteRefines` at `credAnswer (resp.header.aa == 1)`: the model side
    is `absorb_answerOnly_pos` (`N` at `ansCred = if aa then authoritative else glue = αCred (credAnswer
    aa)`), the `extra ~ N` value correspondence is `section_extra_perm`, and — unlike the referral, whose
    tier is rank-MINIMAL — the rank obligations go through the general covered-key/representative-gate
    argument (an authoritative answer write can outrank warm records; the write's own pushes then defeat
    them in BOTH caches). This is the `hcf0` obligation of `Resolves.cacheCname`'s network arms. -/
theorem cname_write_WriteRefines (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (sname : ByteArray) (bwN : VeriDNS.Spec.Net.Name) (now : UInt32)
    (hcut : αName sname = some bwN) (htc : (resp.header.tc == 1) = false)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer), RRCanonMappable e) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)
        (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now))
      ((αCache c).absorb now.toNat bwN { αResp resp with authority := [], additional := [] }) := by
  have hsec := section_extra_perm resp.answer sname bwN
    (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now hcut hno hcanmap
  rw [αCred_credAnswer] at hsec
  have hMpos : ((αCache c).absorb now.toNat bwN { αResp resp with authority := [], additional := [] }).pos
      = ((VeriDNS.Spec.Net.normalizeTTL ((αSection resp.answer).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner))).reverse.flatMap
          (modelPushOf now.toNat
            (if (resp.header.aa == 1) then VeriDNS.Spec.Net.Cred.authoritative else VeriDNS.Spec.Net.Cred.glue)))
        ++ (αCache c).pos :=
    absorb_answerOnly_pos (αCache c) now.toNat bwN (αResp resp)
  refine single_cred_write_WriteRefines c resp _ _ now _ _
    htc (cred_used_credAnswer _) hwf hoe hval hno hMpos hsec ?_ ?_ ?_
  · intro x hx
    obtain ⟨r, -, hxr⟩ := List.mem_flatMap.mp hx
    rw [αCred_credAnswer]
    exact (mem_modelPushOf hxr).1
  · intro nT q'
    show VeriDNS.Spec.Net.Cache.negHit _ nT q' = _
    unfold VeriDNS.Spec.Net.Cache.negHit
    rw [VeriDNS.Spec.Net.absorb_neg]
  · intro nT q'
    show VeriDNS.Spec.Net.Cache.negHitNx _ nT q' = _
    unfold VeriDNS.Spec.Net.Cache.negHitNx
    rw [VeriDNS.Spec.Net.absorb_neg]

/-- **Driver-facing form of the CNAME warm-write bridge, retargeted onto the model reply and model cache**
    (the CNAME analogue of `refer_write_WriteRefines_ref`). Composes `cname_write_WriteRefines` with (a)
    `absorb_resp_congr` — the `WorldModels` answer/aa conjuncts pin `αResp resp`'s absorb-relevant fields
    to `ref`'s, and both sides' authority/additional sections are literally `[]` — and (b)
    `WriteRefines.trans_perm` over `hmme.absorb` (retargeting the base cache `αCache c → cm` through the
    `StateModels` correspondence). This is exactly the `hcf0` obligation of `Resolves.cacheCname` for the
    honest CNAME-chase arms of the `ioResumeLoop_sound` driver. -/
theorem cname_write_WriteRefines_ref (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (sname : ByteArray) (bwN : VeriDNS.Spec.Net.Name) (now : UInt32)
    (hcut : αName sname = some bwN) (htc : (resp.header.tc == 1) = false)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer), RRCanonMappable e)
    (ref : VeriDNS.Spec.Net.Response) (cm : VeriDNS.Spec.Net.Cache)
    (hansEq : αSection resp.answer = ref.answer)
    (haaEq : (resp.header.aa == 1) = ref.aa)
    (hmme : MatchMaxEquiv (αCache c) cm) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)
        (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now))
      (cm.absorb now.toNat bwN { ref with authority := [], additional := [] }) := by
  have h0 := cname_write_WriteRefines c resp sname bwN now hcut htc hwf hoe hval hno hcanmap
  have hcongr : (αCache c).absorb now.toNat bwN { αResp resp with authority := [], additional := [] }
      = (αCache c).absorb now.toNat bwN { ref with authority := [], additional := [] } :=
    VeriDNS.Spec.Net.absorb_resp_congr _ _ _ haaEq hansEq rfl rfl
  rw [hcongr] at h0
  have hmabs := hmme.absorb now.toNat bwN { ref with authority := [], additional := [] }
  exact h0.trans_perm hmabs.1 hmabs.2.1 hmabs.2.2

/-- **Retry-family `StateModels` preservation.** The `markQueried` state update (deprioritise the just-
    queried server) only mutates the SLIST, which `StateModels` does not read — cache, query name, clock,
    `WorldModels`, and deadline are all unchanged — so the invariant is preserved by defeq. This covers the
    `timeout`/`rejectSpoof`/`badResponse`/`unfollowableReferral`/`skipMissing` branches of the totality
    induction (they recurse on the same cache, taking the model clock `now' := now`). -/
theorem StateModels_markQueried (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (ra : String) (ednsBuf : Nat) (rttOf : String → Nat) (now : VeriDNS.Spec.Net.Time)
    (q : VeriDNS.Spec.Net.Query)
    (state : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (c : VeriDNS.Spec.Net.Cache) (w : World) (nm : ByteArray)
    (h : StateModels net ns ra ednsBuf rttOf now q state c w) :
    StateModels net ns ra ednsBuf rttOf now q
      { state with resources := { state.resources with
          slist := state.resources.slist.markQueried nm } } c w := h

/-- **Cache-changing `StateModels` preservation (the `MatchMaxEquiv` cache clause).** At a `refer`/
    `answerCname` hop the impl absorbs the referral into `state''.cache` and the model threads `c.absorb`.
    The Phase-3 bridge gives `MatchMaxEquiv (αCache state''.cache) ((αCache state.cache).absorb …)`; the old
    invariant gives `MatchMaxEquiv (αCache state.cache) c`, so `MatchMaxEquiv.absorb` + `trans` yield
    `MatchMaxEquiv (αCache state''.cache) (c.absorb …)` — the new invariant's cache clause. This is where
    the entire Phase-1/2/3 subsystem (`MatchMaxEquiv` `Perm`-stability + the write-path bridge) discharges
    the totality induction's hardest preservation step. -/
theorem matchMaxEquiv_absorb_step {c1 c2 c : VeriDNS.Spec.Net.Cache} {now : VeriDNS.Spec.Net.Time}
    {bw : VeriDNS.Spec.Net.Name} {resp : VeriDNS.Spec.Net.Response}
    (hbridge : MatchMaxEquiv c1 (c2.absorb now bw resp)) (hold : MatchMaxEquiv c2 c) :
    MatchMaxEquiv c1 (c.absorb now bw resp) :=
  hbridge.trans (hold.absorb now bw resp)

/-- The `absorbNeg` companion of `matchMaxEquiv_absorb_step` (the `answer` terminal threads
    `(c.absorb …).absorbNeg …`). -/
theorem matchMaxEquiv_absorbNeg_step {c1 c2 c : VeriDNS.Spec.Net.Cache} {now : VeriDNS.Spec.Net.Time}
    {q : VeriDNS.Spec.Net.Query} {resp : VeriDNS.Spec.Net.Response}
    (hbridge : MatchMaxEquiv c1 (c2.absorbNeg now q resp)) (hold : MatchMaxEquiv c2 c) :
    MatchMaxEquiv c1 (c.absorbNeg now q resp) :=
  hbridge.trans (hold.absorbNeg now q resp)

/-- **Full cache-changing `StateModels` preservation.** Given the old invariant, the Phase-3 bridge for
    the absorbed impl cache, and that the impl `refer`/`answerCname` step leaves the query name and clock
    unchanged (`hsname`/`hnow` — `afterResume`'s referral branch only descends the cache + glue SLIST), the
    invariant transfers to the new state with the model cache `c.absorb …`. The cache clause is
    `matchMaxEquiv_absorb_step`; name/time rewrite by the equalities; `WorldModels`/deadline are unchanged.
    This is the whole `StateModels` preservation for the hard branches, reduced to the bridge the induction
    will produce from `cacheRRs_records_append` + `topServed_bridge_clause`. -/
theorem StateModels_absorb_preserve
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state stateB : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : World} {bw : VeriDNS.Spec.Net.Name} {resp : VeriDNS.Spec.Net.Response}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hbridge : MatchMaxEquiv (αCache stateB.resources.cache)
        ((αCache state.resources.cache).absorb now bw resp))
    (hsname : stateB.resources.sname = state.resources.sname)
    (hnow : stateB.now = state.now) :
    StateModels net ns ra ednsBuf rttOf now q stateB (c.absorb now bw resp) w :=
  ⟨matchMaxEquiv_absorb_step hbridge old.1, hsname ▸ old.2.1, hnow ▸ old.2.2.1, old.2.2.2⟩

/-- **Refer-hop `StateModels` preservation.** Threads `refer_hop_MatchMaxEquiv` (the refer-branch cache
    refinement) through `StateModels_absorb_preserve`: a refer step takes the impl `state` → `stateB` (cache =
    the two `cacheUnlessTruncated` referral writes; sname + clock unchanged) and the model `c` → `c.absorb now
    bwN (αResp resp)`, preserving the whole `StateModels` invariant (cache `MatchMaxEquiv`, query name, clock,
    `WorldModels`). The time aligns via `αTime state.now = now` (`αTime = .toNat`), so the impl-side absorb at
    `state.now.toNat` IS the model absorb at `now`. Side-conditions (`aa=false`+`isReferral`, `htc`, `hcut`,
    fresh-push `h1`/`h2`, no-overflow `hnoA`/`hnoD`) are the refer-branch classifier outputs — now total since
    the dirty-referral fix. This is the per-hop preservation the `(depth,fuel)` induction invokes for refer. -/
theorem StateModels_refer_preserve
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state stateB : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : VeriDNS.Proof.FreeIO.World} {bwN : VeriDNS.Spec.Net.Name} {cut : ByteArray}
    {resp : VeriDNS.Spec.Format} {aa : Bool}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w)
    (haa : aa = false) (hcut : αName cut = some bwN) (htc : (resp.header.tc == 1) = false)
    (href : (αResp resp).isReferral = true)
    (h1 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr (VeriDNS.Impl.Resolver.credAuthority aa) state.now).records = acc.records.push ⟨rr, state.now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAuthority aa⟩)
    (h2 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr VeriDNS.Impl.Resolver.credAdditional state.now).records = acc.records.push ⟨rr, state.now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional⟩)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat)
    (hnoD : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat)
    (hcanmapA : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority), RRCanonMappable e)
    (hcanmapD : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional), RRCanonMappable e)
    (hcache : stateB.resources.cache =
      VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          state.resources.cache resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
            (VeriDNS.Impl.Resolver.credAuthority aa) state.now)
          resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
            VeriDNS.Impl.Resolver.credAdditional state.now)
    (hsname : stateB.resources.sname = state.resources.sname)
    (hnowB : stateB.now = state.now) :
    StateModels net ns ra ednsBuf rttOf now q stateB (c.absorb now bwN (αResp resp)) w := by
  have hnow_eq : now = state.now.toNat := old.2.2.1.symm
  have hbridge : MatchMaxEquiv (αCache stateB.resources.cache)
      ((αCache state.resources.cache).absorb now bwN (αResp resp)) := by
    rw [hcache, hnow_eq]
    exact refer_hop_MatchMaxEquiv state.resources.cache resp cut bwN state.now aa haa hcut htc href h1 h2 hnoA hnoD hcanmapA hcanmapD
  exact StateModels_absorb_preserve old hbridge hsname hnowB

/-- **Frame preservation for cache-invariant hops.** Any impl step that leaves the cache, query name, and
    clock unchanged (timeout/skipMissing/badResponse/rejectSpoof/markQueried — they touch only the SLIST or
    `lastResponse`/`seen`, none of which `StateModels` reads) preserves `StateModels` against an UNCHANGED
    model cache `c` (the matching model rules — `timeout`, `skipMissing`, `badResponse`, `rejectSpoof` —
    recurse with the same `c`). The cache-writing analogue is `StateModels_refer_preserve`. -/
theorem StateModels_frame
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state stateB : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : VeriDNS.Proof.FreeIO.World}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hcache : stateB.resources.cache = state.resources.cache)
    (hsname : stateB.resources.sname = state.resources.sname)
    (hnow : stateB.now = state.now) :
    StateModels net ns ra ednsBuf rttOf now q stateB c w :=
  ⟨hcache ▸ old.1, hsname ▸ old.2.1, hnow ▸ old.2.2.1, old.2.2.2⟩

/-- **answerCname-hop `StateModels` preservation (the query-RENAMING variant).** Unlike the refer hop, a
    CNAME chase renames `sname → target` and the query `q → { q with qname := target }`. So `StateModels` is
    re-established at the NEW query: the cache `MatchMaxEquiv` carries via `matchMaxEquiv_absorb_step` (model
    `c → c.absorb now bwN (answer-only)`), the query-name clause becomes `αName stateB.sname = some target`
    (= the new `qname`), clock + `WorldModels` unchanged. Pairs `answerCname_hop_MatchMaxEquiv` (the bridge,
    `bwN = αName sname = q.qname`) with the cname-chase state transition. -/
theorem StateModels_answerCname_preserve
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state stateB : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : VeriDNS.Proof.FreeIO.World} {bwN : VeriDNS.Spec.Net.Name}
    {resp : VeriDNS.Spec.Format} {target : VeriDNS.Spec.Net.Name}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hbridge : MatchMaxEquiv (αCache stateB.resources.cache)
        ((αCache state.resources.cache).absorb now bwN { αResp resp with authority := [], additional := [] }))
    (hsnameNew : αName stateB.resources.sname = some target)
    (hnow : stateB.now = state.now) :
    StateModels net ns ra ednsBuf rttOf now { q with qname := target } stateB
      (c.absorb now bwN { αResp resp with authority := [], additional := [] }) w := by
  refine ⟨matchMaxEquiv_absorb_step hbridge old.1, hsnameNew, hnow ▸ old.2.2.1, old.2.2.2⟩

/-- **cacheCname / cache-hit-rename `StateModels` preservation** (no cache write, query RENAMED). A cached
    CNAME chase (`cacheCname`) reads the CNAME from the cache and renames `sname → target` WITHOUT a network
    write — so the cache `MatchMaxEquiv` carries unchanged (`hcache`), and only the query-name clause updates
    (`αName stateB.sname = some target`). The read-only analogue of `StateModels_answerCname_preserve`. -/
theorem StateModels_cacheCname_preserve
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state stateB : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : VeriDNS.Proof.FreeIO.World} {target : VeriDNS.Spec.Net.Name}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hcache : stateB.resources.cache = state.resources.cache)
    (hsnameNew : αName stateB.resources.sname = some target)
    (hnow : stateB.now = state.now) :
    StateModels net ns ra ednsBuf rttOf now { q with qname := target } stateB c w :=
  ⟨hcache ▸ old.1, hsnameNew, hnow ▸ old.2.2.1, old.2.2.2⟩

/-- **Entry `StateModels` for the network induction.** The initial `initFromQuery` state models the abstract
    cache `αCache initCache` (cache unchanged ⟹ `MatchMaxEquiv.refl`), the abstracted query name
    (`αName sname = some qm.qname` via `hqn`), the clock, and the `WorldModels` oracle. This is the BASE of
    the `(depth,fuel)` induction's `StateModels` invariant; `StateModels_frame` then carries it across the
    pre-pause steps (checkAnswer→sendQueries, which touch neither cache nor sname) to the paused state the
    loop receives — so the loop starts with `StateModels` established. -/
theorem StateModels_initFromQuery
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {q : VeriDNS.Spec.Format} {sbelt : VeriDNS.Impl.SList.DnsSList} {now : UInt32}
    {initCache : VeriDNS.Impl.Cache.DnsCache} {qu : VeriDNS.Spec.Question} {qm : VeriDNS.Spec.Net.Query}
    {w : VeriDNS.Proof.FreeIO.World}
    (hqu : q.question[0]? = some qu) (hqn : αName qu.qname = some qm.qname)
    (hw : WorldModels net ns ra ednsBuf (αTime now) w) :
    StateModels net ns ra ednsBuf rttOf (αTime now) qm
      (VeriDNS.Impl.Resolver.initFromQuery (S := VeriDNS.Impl.SList.DnsSList)
        (C := VeriDNS.Impl.Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
        (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache) (αCache initCache) w :=
  ⟨by rw [initFromQuery_cache]; exact MatchMaxEquiv.refl _,
   by rw [initFromQuery_sname q sbelt now initCache qu hqu]; exact hqn,
   by rw [initFromQuery_now],
   hw⟩

/-- **Driver-facing referral keystone from cache invariants.** Packages `refer_continue_keystone` (ascent) and
    `keystone_at_cut`+`referralSlist_base` (base case: `sname` itself has cached NS): from just the `walkNs`
    result, `sname`'s canonicity, the ≤127-label bound, and `CacheWf`/`CacheNsCanon`/`CacheNsDistinct` of the
    cache, it discharges every walk-node/cut canonicity + fuel hypothesis and yields the SLIST Subperm. -/
theorem refer_continue_keystone_wf (cache : VeriDNS.Impl.Cache.DnsCache) (sname : ByteArray)
    (qname : VeriDNS.Spec.Net.Name) (sname_lab : Array ByteArray) (nsNames : Array ByteArray) (mc : Nat) (now : UInt32)
    (hwalk : VeriDNS.Impl.Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) sname cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 128 = some (nsNames, mc))
    (hsna : VeriDNS.Impl.DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hsnCanon : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qname)
    (hlab : sname_lab.toList = qname)
    (hqlen : qname.length ≤ 127)
    (hCWwf : CacheWf cache now)
    (hNsCanon : CacheNsCanon cache)
    (hNsDistinct : CacheNsDistinct cache) :
    ((αCache cache).referralSlist (αTime now) qname (qname.length + 1)).Subperm
      (modelSlistOf (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList)
        (NS := VeriDNS.Spec.SlistEntry) nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now nsNames) mc)) := by
  have hqn : αName sname = some qname := by simp only [αName, hsna]; rw [hlab]
  have hsvN : ∀ x ∈ qname, x.size ≤ 63 := by
    intro x hx
    rw [← hlab] at hx
    obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp hx
    rw [Array.length_toList] at hi
    rw [← hei, Array.getElem_toList]
    exact (hsnav i hi).2
  have hlabsz : sname_lab.size = qname.length := by rw [← hlab, Array.length_toList]

  have honeOf : ∀ node : ByteArray,
      (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = false →
      ∃ rr ∈ (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none := by
    intro node hne
    have hsz : 0 < (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).size := by
      rcases Nat.eq_zero_or_pos (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).size with h | h
      · rw [Array.isEmpty, h] at hne; simp at hne
      · exact h
    have hmem : (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now)[0] ∈
        cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now := Array.getElem_mem hsz
    have hmemL : (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now)[0] ∈
        (cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList := by
      simpa using hmem
    refine ⟨_, hmemL, ?_⟩
    have htype := mem_lookupTopCred_rrType cache node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now _ hmem
    rw [if_pos htype]
    obtain ⟨na, hna, _, _⟩ := hrdcanon_of_CacheNsCanon cache node now hNsCanon _ hmemL htype
    rw [hna]; simp
  have hhostOf : ∀ node : ByteArray,
      ∀ n ∈ ((cache.lookupTopCred node (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).toList,
        ∃ qn, αName n = some qn ∧ n = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63) := by
    intro node n hn
    rw [Array.toList_filterMap, List.mem_filterMap] at hn
    obtain ⟨rr, hrr, hcond⟩ := hn
    split at hcond
    · next htype =>
      rw [Option.some.injEq] at hcond
      subst hcond
      obtain ⟨qn, h1, h2, h3, -⟩ := hrdcanon_of_CacheNsCanon cache node now hNsCanon rr hrr htype
      exact ⟨qn, h1, h2, h3⟩
    · simp at hcond
  rcases walkNs_some_inversion cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 128 sname nsNames mc hwalk with
    hbase | ⟨cut, inter, hchain, hempties, hcutne⟩
  ·
    have hb := walkNs_base sname cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 127 hbase
    rw [show (128 : Nat) = 127 + 1 from rfl, hb] at hwalk
    have heq := Option.some.inj hwalk
    rw [Prod.mk.injEq] at heq
    obtain ⟨hnn, hmm⟩ := heq
    subst hnn; subst hmm
    have hA := keystone_at_cut cache sname now 0
      ⟨qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩ hqn rfl hsnCanon hsvN
      hCWwf.1 hCWwf.2.1 hCWwf.2.2
      (hnd_of_CacheNsDistinct cache sname now hNsDistinct)
      (hhostOf sname)
    have hcutNe : ((αCache cache).nsHostsAt (αTime now) qname).isEmpty = false :=
      nsHostsAt_nonempty_of_lookupTopCred cache sname now
        ⟨qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩ hqn rfl hsnCanon hsvN
        hCWwf.1 hCWwf.2.1 hCWwf.2.2 (honeOf sname hbase)
    rw [referralSlist_base (αCache cache) (αTime now) qname qname.length hcutNe, ← hA]
    exact (nsGlueByteFlat_sublist_fold _ _ _).subperm
  ·
    have hcc := chain_canonical (inter ++ [cut]) sname sname_lab hsna hsnav (by rw [hlab]; exact hsnCanon) hchain
    obtain ⟨cutNa, hcutNa, hcut_canN, hcut_vN⟩ := hcc cut (by simp)
    have hlen := parentDomainWire_chain_length (inter ++ [cut]) sname sname_lab hsna hsnav hchain
    simp only [List.length_append, List.length_cons, List.length_nil, hlabsz] at hlen
    have hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = VeriDNS.Impl.DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63) := by
      intro m hm
      rcases List.mem_cons.mp hm with hms | hmi
      · rw [hms]; exact hcc sname (by simp)
      · exact hcc m (by simp [hmi])
    have hres := refer_continue_keystone cache sname cut sname_lab cutNa inter nsNames mc now (qname.length + 1)
      hwalk hchain hempties hcutne (by omega) hsna hsnav hcutNa hcut_canN hcut_vN
      hCWwf.1 hCWwf.2.1 hCWwf.2.2
      (hnd_of_CacheNsDistinct cache cut now hNsDistinct)
      (hhostOf cut)
      hcanonNode (honeOf cut hcutne) (by omega)
    rw [hlab] at hres
    exact hres

end VeriDNS.Proof.NetworkSim
