import VeriDNS.Proof.CooperativeNetwork




/-!
# NODATA terminal adequacy dual

The positive adequacy capstones (`resolveWithIO_flatAuthoritative_answer_adequate`) and the
NXDOMAIN dual (`resolveWithIO_flatAuthoritative_nxdomain_adequate`) prove that a cooperative
network which answers cleanly (or with a name error) drives the resolver to a *definite*
terminal.  This file supplies the missing **NODATA** dual: when the authoritative leaf returns
`noError` with an empty answer section and a (non-referral) SOA authority — i.e. the tree lookup
resolves to `.nodata` — the resolver still reaches a definite terminal and delivers the negative
(NODATA) reply, rather than silently looping.

This closes the rcode-scope adequacy gap for the NODATA case: the resolver's liveness no longer
depends on the upstream answering with records.  RFC 2308 §2.2 (NODATA responses).
-/

namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message


/-- The model resolver classifies a NODATA reply (`noError`, empty answer, non-referral SOA
authority) as a terminal negative answer. -/
theorem stepAnalyzeResponse_nodata {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hans : Resolver.answersQueryB (RR := RR) resp = false)
    (hae : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hnoNs : Resolver.hasRRTypeIn (RR := RR) resp.authority 2 = false)
    (hsoa : Resolver.hasSoaAuthorityFor (RR := RR) (Resolver.echoedQname resp) resp.authority = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    Resolver.stepAnalyzeResponse s = .answer (Resolver.finalizeAnswer s resp) s := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname]
  rw [if_neg (by simp [hsf, hcls]),
    if_pos (by simp [hans, hnerr, hae, hauth]),
    if_neg (by intro h; rw [hnoNs] at h; simp at h),
    if_pos (by simp [hrc, hae, hsoa])]


/-- `afterResume` reaches the finished NODATA terminal. -/
theorem afterResume_nodata
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hae : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = false)
    (hsoa : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.echoedQname resp) resp.authority = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    Server.afterResume state entryName resp
      = .finished (.ok (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp))
          (Server.boundStateCache (Server.roundTouches state resp)
            { state with lastResponse := some resp, currentStep := .analyzeResponse }).resources.cache := by
  have hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB resp) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hsa : Resolver.stepAnalyzeResponse
      { state with lastResponse := some resp, currentStep := .analyzeResponse }
      = .answer (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp)
          { state with lastResponse := some resp, currentStep := .analyzeResponse } := by
    apply stepAnalyzeResponse_nodata <;> first | rfl | assumption
  unfold Server.afterResume
  rw [hdrop, Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]


/-- One IO round that receives a NODATA reply from a non-probe leaf query delivers the NODATA
terminal.  Structural twin of `run_ioResumeLoop_nxdomain`. -/
theorem run_ioResumeLoop_nodata
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (_hglueless : state.resources.slist.addressTargets[0]? = none)
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀
        = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hae : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = false)
    (hsoa : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.echoedQname resp) resp.authority = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),
          (Server.boundStateCache
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            ({ ({ state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } })
                with lastResponse := some resp, currentStep := .analyzeResponse }
                : Resolver.State DnsSList DnsCache SlistEntry
                    VeriDNS.Spec.ResourceRecord)).resources.cache), w') := by
  apply Exists.intro 6; apply Exists.intro
  rw [Server.ioResumeLoop]
  refine run_now_bind _ w ?_
  rw [if_neg hdl]
  simp only [hbest, hbuild]
  refine run_log_bind _ _ w ?_
  refine run_randomId_bind _ _ ?_
  refine run_randomId_bind _ _ ?_
  rw [if_neg (show ¬ (Server.blockedEgress ipAddr = true) by simp [hegress])]
  refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
  rw [hsani]
  dsimp only
  rw [haccResp]
  refine run_log_bind _ _ _ ?_
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  have hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false := by
    cases hrcc : resp.header.rcode <;>
      first | rfl | (rw [hrcc] at hrc; exact absurd hrc (by decide))
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
    if_neg (by simp [hprobe]), if_neg (by simp [hprobe])]
  rw [afterResume_nodata
      { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } }
      entry.name resp hsendq hcname hsf hcls hnerr hans hae hauth hnoNs hsoa hrc]
  exact run_pure _ _ _


/-- The honest-oracle NODATA round delivers the NODATA terminal.  Twin of
`honestNxdomainRound_delivers`. -/
theorem honestNodataRound_delivers
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (resp0 resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr)
        = some (honestDatagram (Server.ipv4ToAddr ipAddr) (VeriDNS.Impl.Message.encode resp0)))
    (hrt : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0)
    (hid : resp0.header.id
        = (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))).header.id)
    (hqm : Server.questionMatches resp0.question
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))).question = true)
    (hqr : resp0.header.qr = 1)
    (hop : resp0.header.opcode = VeriDNS.Spec.Opcode.query)
    (hsanEq : Server.capTtls (Edns.stripOpt resp0) = resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hae : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = false)
    (hsoa : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.echoedQname resp) resp.authority = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w
      (.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),
          (Server.boundStateCache
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            ({ ({ state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } })
                with lastResponse := some resp, currentStep := .analyzeResponse }
                : Resolver.State DnsSList DnsCache SlistEntry
                    VeriDNS.Spec.ResourceRecord)).resources.cache) := by
  have hb := honestReply_accepted
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp0
    (Server.ipv4ToAddr ipAddr) hrt hid hqm hqr hop
  exact run_ioResumeLoop_nodata sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (honestDatagram (Server.ipv4ToAddr ipAddr) (VeriDNS.Impl.Message.encode resp0))
    (VeriDNS.Impl.Message.encode resp0) resp0 resp resp
    hsendq hdl hbest hglueless hegress hbuild hprobe horacle hb.1 hrt
    (by rw [hb.2.2.1, hsanEq]) (by rw [← hsanEq]; exact hb.2.2.2)
    htc hunfollow hcname hsf hcls hnerr hans hae hauth hnoNs hsoa hrc


/-- The tree-server classification of a NODATA leaf reply. -/
theorem treeRespond_nodata_classified
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (slist : DnsSList) (sname : ByteArray)
    (qu : VeriDNS.Spec.Question)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nodata)
    (hae : query.answer = #[])
    (hne : negAuth.isEmpty = false)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hsoaNeg : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord) qu.qname negAuth = true)
    (htc : (query.header.tc == 1) = false)
    (hrc : (query.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    ((treeRespond T negAuth query).header.tc == 1) = false
    ∧ Server.unfollowableDelegationB slist sname (treeRespond T negAuth query) = false
    ∧ Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) (treeRespond T negAuth query) = none
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
    ∧ Resolver.classifiableB (treeRespond T negAuth query) = true
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.nameError) = false
    ∧ Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) (treeRespond T negAuth query)
        = false
    ∧ (treeRespond T negAuth query).answer.isEmpty = true
    ∧ (treeRespond T negAuth query).authority.isEmpty = false
    ∧ Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord)
        (treeRespond T negAuth query).authority 2 = false
    ∧ Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname (treeRespond T negAuth query))
        (treeRespond T negAuth query).authority = true
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.noError) = true := by
  have hred := treeRespond_nodata_eq T negAuth query qu hq hlk
  have htcR : (treeRespond T negAuth query).header.tc = query.header.tc := by rw [hred]
  have hrcR : (treeRespond T negAuth query).header.rcode = query.header.rcode := by rw [hred]
  have haeR : (treeRespond T negAuth query).answer = #[] := by rw [hred]; exact hae
  have hauR : (treeRespond T negAuth query).authority = negAuth := by rw [hred]
  have hans := answersQueryB_of_emptyAnswer (RR := VeriDNS.Spec.ResourceRecord) _ haeR
  have hcname := cnameToChase_of_emptyAnswer (RR := VeriDNS.Spec.ResourceRecord) _ haeR
  have hnoNsR : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord)
      (treeRespond T negAuth query).authority 2 = false := by rw [hauR]; exact hnoNs
  have hqnR : Resolver.echoedQname (treeRespond T negAuth query) = qu.qname := by
    unfold Resolver.echoedQname
    rw [treeRespond_question, hq]; rfl
  have hsoaR : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.echoedQname (treeRespond T negAuth query))
      (treeRespond T negAuth query).authority = true := by
    rw [hqnR, hauR]; exact hsoaNeg
  have hrcEq : query.header.rcode = VeriDNS.Spec.Rcode.noError := by
    cases h : query.header.rcode <;> rw [h] at hrc <;>
      first | rfl | exact absurd hrc (by decide)
  have hsf : ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.serverFailure)
      = false := by rw [hrcR, hrcEq]; decide
  have hnerr : ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.nameError)
      = false := by rw [hrcR, hrcEq]; decide
  have haeIs : (treeRespond T negAuth query).answer.isEmpty = true := by
    rw [haeR]; rfl
  have hauIs : (treeRespond T negAuth query).authority.isEmpty = false := by
    rw [hauR]; exact hne
  have hrcNo : ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.noError)
      = true := by rw [hrcR]; exact hrc
  have hcls : Resolver.classifiableB (treeRespond T negAuth query) = true := by
    unfold Resolver.classifiableB; rw [hrcNo]; simp
  refine ⟨by rw [htcR]; exact htc, ?_, hcname, hsf, hcls, hnerr, hans,
    haeIs, hauIs, hnoNsR, hsoaR, hrcNo⟩
  · -- unfollowableDelegationB = false since delegationShapedB is false (no NS authority)
    have hshape : Server.delegationShapedB (treeRespond T negAuth query) = false := by
      unfold Server.delegationShapedB; rw [hnoNsR]; simp
    unfold Server.unfollowableDelegationB Server.bogusDelegationB
    rw [hshape]; simp


/-- The leaf NODATA round delivers, packaged from the tree responder facts.  Twin of
`flatAuthoritative_nxdomainRound_delivers`. -/
theorem flatAuthoritative_nodataRound_delivers
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question)
    (hcoop : CooperativeNetwork (treeRespond T negAuth) w)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hresp0Eq : resp0 = treeRespond T negAuth sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hrt : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0)
    (hopt : ∀ b ∈ resp0.additional, Edns.isOptRR b = false)
    (harc : resp0.header.arcount = BitVec.ofNat 16 resp0.additional.size)
    (ha : ∀ b ∈ resp0.answer, Server.capTtlRR b = b)
    (hn : ∀ b ∈ resp0.authority, Server.capTtlRR b = b)
    (hd : ∀ b ∈ resp0.additional, Server.capTtlRR b = b)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nodata)
    (hae : sent.answer = #[])
    (hne : negAuth.isEmpty = false)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hsoaNeg : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord) qu.qname negAuth = true)
    (htc : (sent.header.tc == 1) = false)
    (hrc : (sent.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w
      (.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp0, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp0),
          (Server.boundStateCache
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp0)
            ({ ({ state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } })
                with lastResponse := some resp0, currentStep := .analyzeResponse }
                : Resolver.State DnsSList DnsCache SlistEntry
                    VeriDNS.Spec.ResourceRecord)).resources.cache) := by
  subst hsentEq hresp0Eq
  have hwire := oracle_supplies_round (treeRespond T negAuth)
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (Server.ipv4ToAddr ipAddr) w hcoop hsent
    (treeRespond_header_id T negAuth _) (treeRespond_question T negAuth _) qu hq
  have hsanEq : Server.capTtls (Edns.stripOpt
      (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))))
      = treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) := by
    rw [Edns.stripOpt_eq_self _ hopt harc]; exact capTtls_eq_self _ ha hn hd
  have hcls := treeRespond_nodata_classified T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (state.resources.slist.markQueried entry.name) state.resources.sname
    qu hq hlk hae hne hnoNs hsoaNeg htc hrc
  exact honestNodataRound_delivers sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    hsendq hdl hbest hglueless hegress hbuild hprobe
    hwire.1 hrt hwire.2.1 hwire.2.2
    (treeRespond_qr_opcode T negAuth _ qu hq).1
    (by rw [(treeRespond_qr_opcode T negAuth _ qu hq).2,
        (withSecrets_qr_opcode subQuery₀ _ _).2,
        buildSubQuery_opcode state revealed subQuery₀ hbuild])
    hsanEq
    hcls.1 hcls.2.1 hcls.2.2.1 hcls.2.2.2.1 hcls.2.2.2.2.1 hcls.2.2.2.2.2.1
    hcls.2.2.2.2.2.2.1 hcls.2.2.2.2.2.2.2.1 hcls.2.2.2.2.2.2.2.2.1
    hcls.2.2.2.2.2.2.2.2.2.1 hcls.2.2.2.2.2.2.2.2.2.2.1 hcls.2.2.2.2.2.2.2.2.2.2.2


/-- **NODATA adequacy dual.**  A cooperative flat-authoritative network whose leaf lookup is
`.nodata` drives the resolver to the definite NODATA terminal.  This is the error-rcode dual of
`resolveWithIO_flatAuthoritative_answer_adequate` for the NODATA (RFC 2308 §2.2) case: the
resolver delivers, it does not loop.  Note the `hrc` gate is on the *outgoing* sub-query
(`sent`), which the honest server echoes; no gate on the *reply* rcode is needed — the NODATA
reply's `noError` is derived from the leaf lookup.  The SOA-gated classifier (Classify row)
requires the negative proof be present: `hsoaNeg` supplies the RFC 2308 §2.2 fact that `negAuth`
carries an SOA owned by an ancestor of the query name; the honest server places it verbatim in
the reply's authority section, so `hasSoaAuthorityFor` holds on the received response. -/
theorem resolveWithIO_flatAuthoritative_nodata_adequate
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel' depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question)
    (hcoop : CooperativeNetwork (treeRespond T negAuth) w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hresp0Eq : resp0 = treeRespond T negAuth sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ now + budget))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state (Server.seedRevealed state) = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname (Server.seedRevealed state) = false)
    (hcanon : CanonicalName state.resources.sname)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nodata)
    (hne : negAuth.isEmpty = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hsoaNeg : Resolver.hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord) qu.qname negAuth = true)
    (hnclean : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (htc : (sent.header.tc == 1) = false)
    (hrc : (sent.header.rcode == VeriDNS.Spec.Rcode.noError) = true) :
    ∃ (K : Nat) (w' : World), Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now (fuel' + 1) depth budget) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp0, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp0),
          (Server.boundStateCache
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp0)
            ({ ({ state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } })
                with lastResponse := some resp0, currentStep := .analyzeResponse }
                : Resolver.State DnsSList DnsCache SlistEntry
                    VeriDNS.Spec.ResourceRecord)).resources.cache), w') := by
  subst hresp0Eq
  have hsent := buildSubQuery_withSecrets_roundtrips state (Server.seedRevealed state)
    subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild hprobe hcanon
  rw [← hsentEq] at hsent
  have hneq := treeRespond_nodata_eq T negAuth sent qu hq hlk
  have hadd := treeRespond_additional_empty T negAuth sent qu hq
  have haeq : sent.answer = #[] := by
    have h := (buildSubQuery_withSecrets_sections state (Server.seedRevealed state)
      subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild).1
    rw [← hsentEq] at h; exact h
  have hrt := treeRespond_nodata_roundtrips T negAuth sent qu hsent hq hlk hnsz hcanNeg
  have hopt : ∀ b ∈ (treeRespond T negAuth sent).additional, Edns.isOptRR b = false := by
    rw [hadd.1]; intro b hb; simp at hb
  have harc : (treeRespond T negAuth sent).header.arcount
      = BitVec.ofNat 16 (treeRespond T negAuth sent).additional.size := by
    rw [hadd.1, hadd.2]; rfl
  have ha : ∀ b ∈ (treeRespond T negAuth sent).answer, Server.capTtlRR b = b := by
    have hans : (treeRespond T negAuth sent).answer = #[] := by rw [hneq]; exact haeq
    rw [hans]; intro b hb; simp at hb
  have hn : ∀ b ∈ (treeRespond T negAuth sent).authority, Server.capTtlRR b = b := by
    have hauth : (treeRespond T negAuth sent).authority = negAuth := by rw [hneq]
    rw [hauth]; exact hnclean
  have hd : ∀ b ∈ (treeRespond T negAuth sent).additional, Server.capTtlRR b = b := by
    rw [hadd.1]; intro b hb; simp at hb
  exact resolveWithIO_delivers query sbelt cache now (fuel' + 1) depth budget w state _ hpause
    (flatAuthoritative_nodataRound_delivers T negAuth sbelt state (now + budget) depth fuel'
      (Server.seedRevealed state) w entry ipAddr subQuery₀ sent (treeRespond T negAuth sent) qu
      hcoop hsentEq rfl hsendq hdl hbest hglueless hegress hbuild hprobe
      hsent hrt hopt harc ha hn hd hq hlk haeq hne hnoNs hsoaNeg htc hrc)


end VeriDNS.Proof.Adequacy
