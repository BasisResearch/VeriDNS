import VeriDNS.Proof.Refinement







namespace VeriDNS.Proof.WorldNetwork

open VeriDNS.Spec (RRType RRClass)
open VeriDNS.Spec.Net
open VeriDNS.Proof.Refinement

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
    (hnc : cnameRR q.qname resp.answer = none ∨ q.qtype.covers RRType.cname = true
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
    (hcf0 : WriteRefines now cf0 (c.absorb now q.qname (resp.answerOwned q.qname))
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
    Resolves.referForget addr rest q q srv tr ref ftr rpath tEnd final id srcPort c coutM
      hmiss hnmiss (ProbeQuery.refl q) hfind hans
      (replyDatagram (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref)
      (Transit.deliver addr resolverAddr _ hreachA hreachR)
      (accepts_reply id resolverAddr addr srcPort ednsBuf q ref)
      ?_ href hbail frontier hdesc hdescF hfresh hmono gl cf0 hcf0 hgl cf hcf hres,
    hbridge⟩
  exact OnWire.fromServer

def answerZone (apex : Name) (records : List RR) (qcls : RRClass) : Zone :=
  { apex := apex, records := records, delegations := [], cls := qcls }

def answerServer (addr : String) (apex : Name) (records : List RR) (qcls : RRClass) : Server :=
  { name := apex, zones := [answerZone apex records qcls], cache := [], addr := addr,
    recursionAvailable := false, rtt := 0 }

def answerNet (addr : String) (apex : Name) (records : List RR) (qcls : RRClass) : Network :=
  ⟨[answerServer addr apex records qcls]⟩

def allUp : NetState := { status := fun _ => Status.up }

theorem answerNet_serverAt (addr : String) (apex : Name) (records : List RR) (qcls : RRClass) :
    serverAt (answerNet addr apex records qcls) addr = some (answerServer addr apex records qcls) := by
  simp only [serverAt, answerNet, answerServer, List.find?, beq_self_eq_true]

theorem answerNet_reachA (addr : String) (apex : Name) (records : List RR) (qcls : RRClass)
    (resolverAddr : String) :
    linkReach (answerNet addr apex records qcls) allUp resolverAddr addr = true := by
  have hup : (Status.up == Status.up) = true := rfl
  simp only [linkReach, reachOf, answerNet, answerServer, allUp, NetState.isUp, List.any_cons,
    List.any_nil, Bool.or_false, beq_self_eq_true, Bool.true_and, hup, Bool.or_true]

theorem reach_self (net : Network) (ns : NetState) (resolverAddr : String) :
    linkReach net ns resolverAddr resolverAddr = true := by
  simp only [linkReach, beq_self_eq_true, Bool.true_or]

theorem recordsAt_answerZone (apex : Name) (A : List RR) (qcls : RRClass)
    (howner : ∀ r ∈ A, nameEq r.owner apex = true) :
    recordsAt (answerZone apex A qcls) apex = A := by
  simp only [recordsAt, answerZone]
  exact List.filter_eq_self.mpr (fun r hr => howner r hr)

theorem bestDeleg_answerZone (apex : Name) (A : List RR) (qcls : RRClass) (qname : Name) :
    bestDeleg (answerZone apex A qcls) qname = none := by
  simp only [bestDeleg, answerZone, List.filter_nil, List.foldl_nil]

theorem bestZone_answerServer (addr : String) (apex : Name) (A : List RR) (qcls : RRClass) :
    bestZone (answerServer addr apex A qcls) apex qcls = some (answerZone apex A qcls) := by
  have hcc : (qcls == qcls) = true := by cases qcls <;> rfl
  simp only [bestZone, answerServer, answerZone, isAncestor_refl, hcc, Bool.and_true,
    List.filter_cons, List.filter_nil, if_pos, List.foldl_cons, List.foldl_nil]

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

theorem answerServer_answers
    (addr : String) (now : Time) (q : Query) (A : List RR)
    (howner : ∀ r ∈ A, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ A, (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true)
    (hnc : cnameRR q.qname A = none ∨ q.qtype.covers RRType.cname = true)
    (hA : A ≠ []) :
    ServerAnswers (answerServer addr q.qname A q.qclass) now [] true q
      [Step.findZone q.qname, Step.matchNode q.qname, Step.copyAnswer, Step.addAdditional]
      (answerRespOf addr now q A) := by
  have hrec : recordsAt (answerZone q.qname A q.qclass) q.qname = A :=
    recordsAt_answerZone q.qname A q.qclass howner
  have hnc' : cnameRR q.qname (recordsAt (answerZone q.qname A q.qclass) q.qname) = none
      ∨ q.qtype.covers RRType.cname = true := by rw [hrec]; exact hnc
  have hfilt : (recordsAt (answerZone q.qname A q.qclass) q.qname).filter
      (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass) ≠ [] := by
    rw [hrec, List.filter_eq_self.mpr (fun r hr => hmatch r hr)]; exact hA
  exact ServerAnswers.answer q (answerZone q.qname A q.qclass)
    (recordsAt (answerZone q.qname A q.qclass) q.qname)
    (bestZone_answerServer addr q.qname A q.qclass)
    (bestDeleg_answerZone q.qname A q.qclass q.qname) rfl hnc' hfilt

theorem answerRespOf_answer (addr : String) (now : Time) (q : Query) (A : List RR)
    (howner : ∀ r ∈ A, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ A, (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true) :
    (answerRespOf addr now q A).answer = A := by
  simp only [answerRespOf, recordsAt_answerZone q.qname A q.qclass howner]
  exact List.filter_eq_self.mpr (fun r hr => hmatch r hr)

theorem answer_model_realizable
    (resolverAddr addr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (rest : List String) (q : Query) (id srcPort : Nat)
    (A : List RR) (v : Response)
    (howner : ∀ r ∈ A, nameEq r.owner q.qname = true)
    (hmatch : ∀ r ∈ A, (q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = true)
    (hnc : cnameRR q.qname A = none ∨ q.qtype.covers RRType.cname = true)
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

theorem isEmptyNonTerminal_empty (apex : Name) (qcls : RRClass) :
    isEmptyNonTerminal (answerZone apex [] qcls) apex = false := by
  simp [isEmptyNonTerminal, answerZone]

theorem wildcardSynth_empty (apex : Name) (qcls : RRClass) (qt : QType) :
    wildcardSynth (answerZone apex [] qcls) apex qt qcls = none := by
  unfold wildcardSynth
  split
  · rfl
  · rw [Option.map_eq_none_iff]
    apply List.findSome?_eq_none_iff.mpr
    intro k _
    simp [recordsAt, answerZone]

theorem nxdomainAuthority_empty (apex : Name) (qcls : RRClass) :
    nxdomainAuthority (answerZone apex [] qcls) = [] := by
  simp [nxdomainAuthority, answerZone, soaOf]

def nxdomainRespOf (addr : String) (q : Query) : Response :=
  { aa := true, rcode := RCode.nameError,
    ra := (answerServer addr q.qname [] q.qclass).recursionAvailable,
    answer := [], authority := nxdomainAuthority (answerZone q.qname [] q.qclass),
    additional := [] }

theorem nxdomainServer_answers (addr : String) (now : Time) (q : Query) :
    ServerAnswers (answerServer addr q.qname [] q.qclass) now [] true q
      [Step.findZone q.qname, Step.nameError] (nxdomainRespOf addr q) :=
  ServerAnswers.nameError q (answerZone q.qname [] q.qclass)
    (bestZone_answerServer addr q.qname [] q.qclass)
    (bestDeleg_answerZone q.qname [] q.qclass q.qname)
    (recordsAt_answerZone q.qname [] q.qclass (by intro r hr; exact absurd hr (by simp)))
    (wildcardSynth_empty q.qname q.qclass q.qtype)
    (isEmptyNonTerminal_empty q.qname q.qclass)

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


theorem nameEq_child_false (x : ByteArray) (qname : Name) : nameEq (x :: qname) qname = false := by
  by_contra h; rw [Bool.not_eq_false] at h; have := nameEq_length h; simp at this

theorem nameEq_child_false' (x : ByteArray) (qname : Name) : nameEq qname (x :: qname) = false := by
  by_contra h; rw [Bool.not_eq_false] at h; have := nameEq_length h; simp at this

theorem isAncestor_child (x : ByteArray) (qname : Name) : isAncestor qname (x :: qname) = true := by
  have h2 : (x :: qname).drop ((x :: qname).length - qname.length) = qname := by
    simp [List.length_cons]
  unfold isAncestor; rw [h2]; simp [List.length_cons, nameEq_refl]

def entRR (qname : Name) (qcls : RRClass) : RR :=
  { owner := L "x" :: qname, ttl := 0, rdata := RData.a ⟨0, 0, 0, 0⟩, cls := qcls }

theorem recordsAt_entZone (qname : Name) (qcls : RRClass) :
    recordsAt (answerZone qname [entRR qname qcls] qcls) qname = [] := by
  simp [recordsAt, answerZone, entRR, nameEq_child_false]

theorem isEmptyNonTerminal_ent (qname : Name) (qcls : RRClass) :
    isEmptyNonTerminal (answerZone qname [entRR qname qcls] qcls) qname = true := by
  simp [isEmptyNonTerminal, answerZone, entRR, isAncestor_child, nameEq_child_false']

theorem wildcardSynth_ent (qname : Name) (qcls : RRClass) (qt : QType) :
    wildcardSynth (answerZone qname [entRR qname qcls] qcls) qname qt qcls = none := by
  unfold wildcardSynth
  rw [if_pos]
  simp [nameKnown, answerZone, entRR, isAncestor_child]

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

def noDataRespOf (addr : String) (q : Query) : Response :=
  { aa := true, rcode := RCode.noError,
    ra := (answerServer addr q.qname [entRR q.qname q.qclass] q.qclass).recursionAvailable,
    answer := [], authority := noDataAuthority (answerZone q.qname [entRR q.qname q.qclass] q.qclass),
    additional := [] }

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

theorem exhausted_model_realizable
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (q : Query)
    (v : Response) (hrc : v.rcode = RCode.servFail) (hva : v.answer = []) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c [] q v :=
  ⟨[], [], now, c, _, Resolves.exhausted c q, RespAgree.of_eq hrc hva⟩

theorem exhausted_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (q : Query)
    (v : Response) (hrc : v.rcode = RCode.servFail) (hva : v.answer = []) :
    VeriDNS.Proof.Refinement.HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen
      c [] q v c :=
  ⟨[], [], now, _, Resolves.exhausted c q, RespAgree.of_eq hrc hva⟩

theorem gaveUp_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (slist : List String)
    (q : Query) (hw : VeriDNS.Spec.Net.GaveUpWitness now c slist q)
    (v : Response) (hrc : v.rcode = RCode.servFail) (hva : v.answer = []) :
    VeriDNS.Proof.Refinement.HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen
      c slist q v c :=
  ⟨[], [], now, _, Resolves.gaveUp c slist q hw, RespAgree.of_eq hrc hva⟩

theorem loopDetected_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (slist : List String)
    (q : Query) (v : Response) (hrc : v.rcode = RCode.servFail) (hva : v.answer = []) :
    VeriDNS.Proof.Refinement.HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen
      c slist q v c :=
  ⟨[], [], now, _, Resolves.loopDetected c slist q, RespAgree.of_eq hrc hva⟩

end VeriDNS.Proof.WorldNetwork
