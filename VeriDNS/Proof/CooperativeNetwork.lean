import VeriDNS.Proof.Adequacy
import VeriDNS.Proof.DeliveredWire
import VeriDNS.Proof.QnameMin





namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message

def honestDatagram (addr payload : ByteArray) : VeriDNS.Spec.Exchanged ByteArray :=
  { payload := payload, source := addr, destination := addr, localAddr := addr }

theorem acceptExchanged_honestDatagram (addr payload : ByteArray) :
    Server.acceptExchanged addr (honestDatagram addr payload) = some payload := by
  unfold Server.acceptExchanged Server.datagramMatches honestDatagram
  simp only [byteArray_beq_refl, Bool.and_self, if_pos]



theorem honestReply_accepted
    (sent resp0 : VeriDNS.Spec.Format) (addr : ByteArray)
    (hrt : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0)
    (hid : resp0.header.id = sent.header.id)
    (hq : Server.questionMatches resp0.question sent.question = true)
    (hqr : resp0.header.qr = 1)
    (hop : resp0.header.opcode = VeriDNS.Spec.Opcode.query) :
    Server.acceptExchanged addr (honestDatagram addr (VeriDNS.Impl.Message.encode resp0))
        = some (VeriDNS.Impl.Message.encode resp0)
    ∧ VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0
    ∧ Server.sanitizeTtlsCap resp0 = some (Server.capTtls (Edns.stripOpt resp0))
    ∧ Server.acceptResponse sent (Server.capTtls (Edns.stripOpt resp0))
        = some (Server.capTtls (Edns.stripOpt resp0)) := by
  refine ⟨acceptExchanged_honestDatagram addr _, hrt, rfl, ?_⟩
  have hidC : (Server.capTtls (Edns.stripOpt resp0)).header.id = sent.header.id := by
    rw [(capTtls_frame (Edns.stripOpt resp0)).1, Edns.stripOpt_header_id]; exact hid
  have hqC : (Server.capTtls (Edns.stripOpt resp0)).question = resp0.question := by
    rw [(capTtls_frame (Edns.stripOpt resp0)).2.1, Edns.stripOpt_question]
  have hqrC : (Server.capTtls (Edns.stripOpt resp0)).header.qr = 1 := by
    rw [(capTtls_frame (Edns.stripOpt resp0)).1, Edns.stripOpt_header_qr]; exact hqr
  have hopC : (Server.capTtls (Edns.stripOpt resp0)).header.opcode
      = VeriDNS.Spec.Opcode.query := by
    rw [(capTtls_frame (Edns.stripOpt resp0)).1, Edns.stripOpt_header_opcode]; exact hop
  have hopRefl : (VeriDNS.Spec.Opcode.query == VeriDNS.Spec.Opcode.query) = true := rfl
  unfold Server.acceptResponse
  rw [if_pos (by rw [hidC, hqC, hqrC, hopC, hq, hopRefl]; simp)]


theorem honestAnswerRound_delivers
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (resp0 resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
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
    (hans : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w
      (.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),
          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundLru
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            state.now)) := by
  have hb := honestReply_accepted
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp0
    (Server.ipv4ToAddr ipAddr) hrt hid hqm hqr hop
  exact run_ioResumeLoop_answer sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (honestDatagram (Server.ipv4ToAddr ipAddr) (VeriDNS.Impl.Message.encode resp0))
    (VeriDNS.Impl.Message.encode resp0) resp0 resp resp
    hsendq hdl hbest hegress hbuild hprobe horacle hb.1 hrt
    (by rw [hb.2.2.1, hsanEq]) (by rw [← hsanEq]; exact hb.2.2.2)
    htc hunfollow hcname hsf hcls hans hfe


theorem honestNxdomainRound_delivers
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (resp0 resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
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
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hemp : resp.answer.isEmpty = true) :
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
  exact run_ioResumeLoop_nxdomain sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (honestDatagram (Server.ipv4ToAddr ipAddr) (VeriDNS.Impl.Message.encode resp0))
    (VeriDNS.Impl.Message.encode resp0) resp0 resp resp
    hsendq hdl hbest hegress hbuild hprobe horacle hb.1 hrt
    (by rw [hb.2.2.1, hsanEq]) (by rw [← hsanEq]; exact hb.2.2.2)
    htc hunfollow hcname hsf hcls hnerr hans hemp


theorem honestReferralNode
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (resp0 resp : VeriDNS.Spec.Format)
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hpdeny : (Resolver.probeRoundB state.resources.sname revealed
        && Server.strictDenialB resp) = false)
    (hpconsume : (Resolver.probeRoundB state.resources.sname revealed
        && !Server.probePassableB resp) = false)
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
    (hcont : Server.afterResume { state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } } entry.name resp = .continue st)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false)
    (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock + w.tick w.exchCtr →
        w'.exchCtr = w.exchCtr + 1 → w'.tick = w.tick → w'.idCtr = w.idCtr + 2 →
        DescentChain sbelt deadline depth out st fuel'
          (Server.revealedAfterContinue state.resources.sname revealed st) w') :
    DescentChain sbelt deadline depth out state (fuel' + 1) revealed w := by
  have hb := honestReply_accepted
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp0
    (Server.ipv4ToAddr ipAddr) hrt hid hqm hqr hop
  exact DescentChain.referral hdl hbest hegress hbuild hpdeny hpconsume
    horacle hb.1 hrt
    (by rw [hb.2.2.1, hsanEq]) (by rw [← hsanEq]; exact hb.2.2.2) htc hunfollow hcont hfe hnext


theorem honestProbeConsumeNode
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (resp0 resp : VeriDNS.Spec.Format)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
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
    (hdeny : Server.strictDenialB resp = false)
    (hpass : Server.probePassableB resp = false)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false)
    (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock + w.tick w.exchCtr →
        w'.exchCtr = w.exchCtr + 1 → w'.tick = w.tick → w'.idCtr = w.idCtr + 2 →
        DescentChain sbelt deadline depth out
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } fuel'
          (Resolver.bumpRevealed state.resources.sname revealed) w') :
    DescentChain sbelt deadline depth out state (fuel' + 1) revealed w := by
  have hb := honestReply_accepted
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp0
    (Server.ipv4ToAddr ipAddr) hrt hid hqm hqr hop
  exact DescentChain.probe hdl hbest hegress hbuild hprobe
    horacle hb.1 hrt
    (by rw [hb.2.2.1, hsanEq]) (by rw [← hsanEq]; exact hb.2.2.2) htc hunfollow hdeny hpass hfe hnext



def mkHonestOracle (respond : VeriDNS.Spec.Format → VeriDNS.Spec.Format) :
    ByteArray → ByteArray → Option (VeriDNS.Spec.Exchanged ByteArray) :=
  fun qbytes addr =>
    match VeriDNS.Impl.Message.decode qbytes with
    | .error _ => none
    | .ok query => some (honestDatagram addr (VeriDNS.Impl.Message.encode (respond query)))

def CooperativeNetwork (respond : VeriDNS.Spec.Format → VeriDNS.Spec.Format) (w : World) : Prop :=
  w.oracle = mkHonestOracle respond

theorem questionMatches_self (qs : Array VeriDNS.Spec.Question) (q : VeriDNS.Spec.Question)
    (h : qs[0]? = some q) : Server.questionMatches qs qs = true := by
  simp only [Server.questionMatches, h, byteArray_beq_refl, beq_self_eq_true, Bool.and_self]

theorem oracle_supplies_round
    (respond : VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (sent : VeriDNS.Spec.Format) (addr : ByteArray) (w : World)
    (hcoop : CooperativeNetwork respond w)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hidP : (respond sent).header.id = sent.header.id)
    (hqP : (respond sent).question = sent.question)
    (q : VeriDNS.Spec.Question) (hne : sent.question[0]? = some q) :
    w.oracle (VeriDNS.Impl.Message.encode sent) addr
        = some (honestDatagram addr (VeriDNS.Impl.Message.encode (respond sent)))
    ∧ (respond sent).header.id = sent.header.id
    ∧ Server.questionMatches (respond sent).question sent.question = true := by
  refine ⟨?_, hidP, ?_⟩
  · rw [hcoop]; simp only [mkHonestOracle, hsent]
  · rw [hqP]; exact questionMatches_self sent.question q hne




def treeRespond {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) : VeriDNS.Spec.Format :=
  match query.question[0]? with
  | none => query
  | some qu =>
    match VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype with
    | .answer rrs =>
      { query with
          header := { query.header with qr := 1, aa := 1, ancount := BitVec.ofNat 16 rrs.size, arcount := 0 },
          answer := rrs.map VeriDNS.Spec.RRParse.rrBytes,
          additional := #[] }
    | .redirect rr _ =>
      { query with
          header := { query.header with qr := 1, aa := 1, ancount := 1, arcount := 0 },
          answer := #[VeriDNS.Spec.RRParse.rrBytes rr],
          additional := #[] }
    | .nodata =>
      { query with
          header := { query.header with qr := 1, aa := 1, nscount := BitVec.ofNat 16 negAuth.size, arcount := 0 }
          authority := negAuth,
          additional := #[] }
    | .nameError =>
      { query with
          header := { query.header with qr := 1, aa := 1, rcode := VeriDNS.Spec.Rcode.nameError, nscount := BitVec.ofNat 16 negAuth.size, arcount := 0 }
          authority := negAuth,
          additional := #[] }

theorem treeRespond_header_id {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format) :
    (treeRespond T negAuth query).header.id = query.header.id := by
  unfold treeRespond
  split
  · rfl
  · split <;> rfl

theorem treeRespond_question {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format) :
    (treeRespond T negAuth query).question = query.question := by
  unfold treeRespond
  split
  · rfl
  · split <;> rfl

/-- The honest tree responder emits a *response*: QR=1 and the OPCODE echoed
    from the query (the two shape conjuncts of the finding-030 accept gate). -/
theorem treeRespond_qr_opcode {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (hq : query.question[0]? = some qu) :
    (treeRespond T negAuth query).header.qr = 1
    ∧ (treeRespond T negAuth query).header.opcode = query.header.opcode := by
  unfold treeRespond
  simp only [hq]
  split <;> exact ⟨rfl, rfl⟩

/-- `withSecrets` only touches the transaction id and the question casing:
    QR and OPCODE pass through. -/
theorem withSecrets_qr_opcode (q : VeriDNS.Spec.Format) (rid cid : UInt16) :
    (Server.withSecrets q rid cid).header.qr = q.header.qr
    ∧ (Server.withSecrets q rid cid).header.opcode = q.header.opcode :=
  ⟨rfl, rfl⟩

/-- Every sub-query the resolver builds carries the standard QUERY opcode
    (RFC 1035 §4.1.1: the resolver originates standard queries). -/
theorem buildSubQuery_opcode
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀) :
    subQuery₀.header.opcode = VeriDNS.Spec.Opcode.query := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · split at hbuild
    · exact absurd hbuild (by simp)
    · rw [← Option.some.inj hbuild]

theorem treeRespond_additional_empty {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (hq : query.question[0]? = some qu) :
    (treeRespond T negAuth query).additional = #[]
    ∧ (treeRespond T negAuth query).header.arcount = 0 := by
  unfold treeRespond
  simp only [hq]
  split <;> exact ⟨rfl, rfl⟩



theorem capTtls_eq_self (resp : VeriDNS.Spec.Format)
    (ha : ∀ b ∈ resp.answer, Server.capTtlRR b = b)
    (hn : ∀ b ∈ resp.authority, Server.capTtlRR b = b)
    (hd : ∀ b ∈ resp.additional, Server.capTtlRR b = b) :
    Server.capTtls resp = resp := by
  unfold Server.capTtls
  rw [(Array.map_congr_left ha).trans (Array.map_id _),
      (Array.map_congr_left hn).trans (Array.map_id _),
      (Array.map_congr_left hd).trans (Array.map_id _)]

theorem sanitizeTtlsCap_eq_self (resp : VeriDNS.Spec.Format)
    (hopt : ∀ b ∈ resp.additional, Edns.isOptRR b = false)
    (harc : resp.header.arcount = BitVec.ofNat 16 resp.additional.size)
    (ha : ∀ b ∈ resp.answer, Server.capTtlRR b = b)
    (hn : ∀ b ∈ resp.authority, Server.capTtlRR b = b)
    (hd : ∀ b ∈ resp.additional, Server.capTtlRR b = b) :
    Server.sanitizeTtlsCap resp = some resp := by
  unfold Server.sanitizeTtlsCap
  rw [Edns.stripOpt_eq_self resp hopt harc, capTtls_eq_self resp ha hn hd]





theorem lookupAt_answer {RR : Type} [VeriDNS.Spec.RRParse RR]
    (n : VeriDNS.Spec.Node RR) (qtype : BitVec 16) (rrs : Array RR)
    (h : VeriDNS.Impl.NameTree.lookupAt n qtype = .answer rrs) :
    0 < rrs.size ∧ ∀ rr ∈ rrs, (VeriDNS.Spec.RRParse.rrType rr == qtype) = true := by
  unfold VeriDNS.Impl.NameTree.lookupAt at h
  simp only at h
  split at h
  · rename_i hsz
    rw [VeriDNS.Impl.NameTree.Outcome.answer.injEq] at h
    subst h
    exact ⟨hsz, fun rr hrr => (Array.mem_filter.mp hrr).2⟩
  · split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)

theorem treeLookup_answer {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (qname : ByteArray) (qtype : BitVec 16) (rrs : Array RR)
    (h : VeriDNS.Impl.NameTree.treeLookup T qname qtype = .answer rrs) :
    0 < rrs.size ∧ ∀ rr ∈ rrs, (VeriDNS.Spec.RRParse.rrType rr == qtype) = true := by
  unfold VeriDNS.Impl.NameTree.treeLookup at h
  split at h
  · exact absurd h (by simp)
  · exact lookupAt_answer _ qtype rrs h

theorem treeRespond_answer_eq {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rrs : Array RR)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs) :
    treeRespond T negAuth query =
      { query with
          header := { query.header with qr := 1, aa := 1, ancount := BitVec.ofNat 16 rrs.size, arcount := 0 },
          answer := rrs.map VeriDNS.Spec.RRParse.rrBytes,
          additional := #[] } := by
  unfold treeRespond
  simp only [hq, hlk]

theorem treeRespond_answersQuery {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rrs : Array RR) (rr : RR)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hmem : rr ∈ rrs)
    (hrt : VeriDNS.Spec.RRParse.parseRaw (VeriDNS.Spec.RRParse.rrBytes rr) = some rr) :
    Resolver.answersQueryB (RR := RR) (treeRespond T negAuth query) = true := by
  have htype : (VeriDNS.Spec.RRParse.rrType rr == qu.qtype) = true :=
    (treeLookup_answer T qu.qname qu.qtype rrs hlk).2 rr hmem
  rw [treeRespond_answer_eq T negAuth query qu rrs hq hlk]
  unfold Resolver.answersQueryB
  simp only [hq, Resolver.hasRRTypeIn, Array.any_eq_true]
  have hb := Array.mem_map_of_mem (f := VeriDNS.Spec.RRParse.rrBytes) hmem
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem hb
  exact ⟨i, hi, by rw [hget, hrt]; exact htype⟩

/-- An honest tree answer is ENTITLED: its records are owned at the query name
    (a well-formed authoritative node stores its own name), so their owner is the
    root of the CNAME chain (`reachableNamesB` always contains `qname`).  This is
    the honest-side witness of the 2026-07-15 off-owner acceptance tightening. -/
theorem treeRespond_entitledAnswerB {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rrs : Array RR) (rr : RR)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hmem : rr ∈ rrs)
    (hrt : VeriDNS.Spec.RRParse.parseRaw (VeriDNS.Spec.RRParse.rrBytes rr) = some rr)
    (hown : VeriDNS.Impl.DomainName.nameEqCI (VeriDNS.Spec.RRParse.rrName rr) qu.qname = true) :
    Resolver.entitledAnswerB (RR := RR) (treeRespond T negAuth query) = true := by
  have htype : (VeriDNS.Spec.RRParse.rrType rr == qu.qtype) = true :=
    (treeLookup_answer T qu.qname qu.qtype rrs hlk).2 rr hmem
  rw [treeRespond_answer_eq T negAuth query qu rrs hq hlk]
  unfold Resolver.entitledAnswerB
  simp only [hq]
  rw [Array.any_eq_true]
  have hb := Array.mem_map_of_mem (f := VeriDNS.Spec.RRParse.rrBytes) hmem
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem hb
  refine ⟨i, hi, ?_⟩
  rw [hget, hrt]
  rw [Bool.and_eq_true]
  refine ⟨htype, ?_⟩
  unfold Resolver.nameMemB
  rw [Array.any_eq_true']
  exact ⟨qu.qname, Resolver.qname_mem_reachableNamesB _ _, hown⟩

theorem cnameToChase_of_answers {RR : Type} [VeriDNS.Spec.RRParse RR] (resp : VeriDNS.Spec.Format)
    (hans : Resolver.answersQueryB (RR := RR) resp = true) :
    Resolver.cnameToChase (RR := RR) resp = none := by
  simp only [Resolver.cnameToChase, hans, if_true]

theorem unfollowableDelegationB_of_answers (slist : DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hans : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    Server.unfollowableDelegationB slist sname resp = false := by
  have haq : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true :=
    Resolver.answersQueryB_of_entitled (RR := VeriDNS.Spec.ResourceRecord) resp hans
  simp only [Server.unfollowableDelegationB, Server.bogusDelegationB, Server.delegationShapedB,
    haq, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_self]

theorem treeRespond_answer_classifiableB {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rrs : Array RR)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs) :
    Resolver.classifiableB (treeRespond T negAuth query) = true := by
  have hsz : 0 < rrs.size := (treeLookup_answer T qu.qname qu.qtype rrs hlk).1
  have hne : (rrs.map VeriDNS.Spec.RRParse.rrBytes).isEmpty = false := by
    simp only [Array.isEmpty_eq_false_iff_exists_mem]
    exact ⟨_, Array.mem_map_of_mem (Array.getElem_mem hsz)⟩
  rw [treeRespond_answer_eq T negAuth query qu rrs hq hlk]
  simp only [Resolver.classifiableB, hne, Bool.not_false, Bool.true_or]

theorem treeRespond_answer_classified
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (slist : DnsSList) (sname : ByteArray)
    (qu : VeriDNS.Spec.Question) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (rr : VeriDNS.Spec.ResourceRecord)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hmem : rr ∈ rrs)
    (hrt : VeriDNS.Spec.RRParse.parseRaw (VeriDNS.Spec.RRParse.rrBytes rr) = some rr)
    (hown : VeriDNS.Impl.DomainName.nameEqCI (VeriDNS.Spec.RRParse.rrName rr) qu.qname = true)
    (htc : (query.header.tc == 1) = false)
    (hsf : (query.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hfe : (query.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ((treeRespond T negAuth query).header.tc == 1) = false
    ∧ Server.unfollowableDelegationB slist sname (treeRespond T negAuth query) = false
    ∧ Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) (treeRespond T negAuth query) = none
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
    ∧ Resolver.classifiableB (treeRespond T negAuth query) = true
    ∧ Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) (treeRespond T negAuth query)
        = true
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.formatError) = false := by
  have hent := treeRespond_entitledAnswerB T negAuth query qu rrs rr hq hlk hmem hrt hown
  have hans := treeRespond_answersQuery T negAuth query qu rrs rr hq hlk hmem hrt
  have hhdr : (treeRespond T negAuth query).header.tc = query.header.tc
      ∧ (treeRespond T negAuth query).header.rcode = query.header.rcode := by
    rw [treeRespond_answer_eq T negAuth query qu rrs hq hlk]; exact ⟨rfl, rfl⟩
  exact ⟨by rw [hhdr.1]; exact htc,
    unfollowableDelegationB_of_answers slist sname _ hent,
    cnameToChase_of_answers _ hans,
    by rw [hhdr.2]; exact hsf,
    treeRespond_answer_classifiableB T negAuth query qu rrs hq hlk, hent,
    by rw [hhdr.2]; exact hfe⟩



theorem treeRespond_nameError_eq {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nameError) :
    treeRespond T negAuth query =
      { query with
          header := { query.header with qr := 1, aa := 1, rcode := VeriDNS.Spec.Rcode.nameError, nscount := BitVec.ofNat 16 negAuth.size, arcount := 0 },
          authority := negAuth,
          additional := #[] } := by
  unfold treeRespond
  simp only [hq, hlk]

theorem answersQueryB_of_emptyAnswer {RR : Type} [VeriDNS.Spec.RRParse RR]
    (resp : VeriDNS.Spec.Format) (hae : resp.answer = #[]) :
    Resolver.answersQueryB (RR := RR) resp = false := by
  unfold Resolver.answersQueryB Resolver.hasRRTypeIn
  rw [hae]
  simp only [Array.any_empty]
  split <;> rfl

theorem cnameToChase_of_emptyAnswer {RR : Type} [VeriDNS.Spec.RRParse RR]
    (resp : VeriDNS.Spec.Format) (hae : resp.answer = #[]) :
    Resolver.cnameToChase (RR := RR) resp = none := by
  unfold Resolver.cnameToChase
  rw [answersQueryB_of_emptyAnswer resp hae]
  simp only [Bool.false_eq_true, if_false]
  split
  · rw [hae]; rfl
  · rfl

theorem treeRespond_nxdomain_classified
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (slist : DnsSList) (sname : ByteArray)
    (qu : VeriDNS.Spec.Question)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nameError)
    (hae : query.answer = #[])
    (htc : (query.header.tc == 1) = false) :
    ((treeRespond T negAuth query).header.tc == 1) = false
    ∧ Server.unfollowableDelegationB slist sname (treeRespond T negAuth query) = false
    ∧ Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) (treeRespond T negAuth query) = none
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
    ∧ Resolver.classifiableB (treeRespond T negAuth query) = true
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.nameError) = true
    ∧ Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) (treeRespond T negAuth query)
        = false
    ∧ (treeRespond T negAuth query).answer.isEmpty = true := by
  have hred := treeRespond_nameError_eq T negAuth query qu hq hlk
  have htcR : (treeRespond T negAuth query).header.tc = query.header.tc := by rw [hred]
  have hrcR : (treeRespond T negAuth query).header.rcode = VeriDNS.Spec.Rcode.nameError := by
    rw [hred]
  have haeR : (treeRespond T negAuth query).answer = #[] := by rw [hred]; exact hae
  have hans := answersQueryB_of_emptyAnswer (RR := VeriDNS.Spec.ResourceRecord) _ haeR
  have hrn : (VeriDNS.Spec.Rcode.nameError == VeriDNS.Spec.Rcode.nameError) = true := by decide
  refine ⟨by rw [htcR]; exact htc, ?_, cnameToChase_of_emptyAnswer _ haeR,
    by rw [hrcR]; decide, ?_, by rw [hrcR]; decide, hans, by rw [haeR]; rfl⟩
  · simp only [Server.unfollowableDelegationB, Server.bogusDelegationB, Server.delegationShapedB,
      hrcR, hrn, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_self]
  · simp only [Resolver.classifiableB, hrcR, hrn, Bool.or_true, Bool.true_or]



theorem treeRespond_nodata_eq {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (negAuth : Array ByteArray) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nodata) :
    treeRespond T negAuth query =
      { query with
          header := { query.header with qr := 1, aa := 1, nscount := BitVec.ofNat 16 negAuth.size, arcount := 0 },
          authority := negAuth,
          additional := #[] } := by
  unfold treeRespond
  simp only [hq, hlk]

theorem treeRespond_answer_probeConsumed
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (slist : DnsSList) (sname : ByteArray)
    (qu : VeriDNS.Spec.Question) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hauth : query.authority = #[])
    (hrcNo : query.header.rcode = VeriDNS.Spec.Rcode.noError)
    (htc : (query.header.tc == 1) = false) :
    ((treeRespond T negAuth query).header.tc == 1) = false
    ∧ Server.unfollowableDelegationB slist sname (treeRespond T negAuth query) = false
    ∧ Server.strictDenialB (treeRespond T negAuth query) = false
    ∧ Server.probePassableB (treeRespond T negAuth query) = false := by
  have hred := treeRespond_answer_eq T negAuth query qu rrs hq hlk
  have htcR : (treeRespond T negAuth query).header.tc = query.header.tc := by rw [hred]
  have hrcR : (treeRespond T negAuth query).header.rcode = query.header.rcode := by rw [hred]
  have hauthR : (treeRespond T negAuth query).authority = #[] := by rw [hred]; exact hauth
  have hsz : 0 < rrs.size := (treeLookup_answer T qu.qname qu.qtype rrs hlk).1
  have hne : (treeRespond T negAuth query).answer.isEmpty = false := by
    have : (treeRespond T negAuth query).answer = rrs.map VeriDNS.Spec.RRParse.rrBytes := by
      rw [hred]
    rw [this]
    simp only [Array.isEmpty_eq_false_iff_exists_mem]
    exact ⟨_, Array.mem_map_of_mem (Array.getElem_mem hsz)⟩
  have hcls : Resolver.classifiableB (treeRespond T negAuth query) = true :=
    treeRespond_answer_classifiableB T negAuth query qu rrs hq hlk
  have hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord)
      (treeRespond T negAuth query).authority 2 = false := by
    unfold Resolver.hasRRTypeIn
    rw [hauthR]
    simp only [Array.any_empty]
  have hnn : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by decide
  refine ⟨by rw [htcR]; exact htc, ?_, ?_, ?_⟩
  · simp only [Server.unfollowableDelegationB, Server.bogusDelegationB, Server.delegationShapedB,
      hnoNs, Bool.false_and, Bool.or_self]
  · simp only [Server.strictDenialB, hrcR, hrcNo, hnn, Bool.false_and, Bool.and_false]
  · simp only [Server.probePassableB, Server.referralShapedB, Server.retryShapedB,
      hne, hrcR, hrcNo, hnsf, hcls, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.or_self]

theorem treeRespond_nodata_probeConsumed
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (slist : DnsSList) (sname : ByteArray)
    (qu : VeriDNS.Spec.Question)
    (hq : query.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nodata)
    (hae : query.answer = #[])
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hrcNo : query.header.rcode = VeriDNS.Spec.Rcode.noError)
    (htc : (query.header.tc == 1) = false) :
    ((treeRespond T negAuth query).header.tc == 1) = false
    ∧ Server.unfollowableDelegationB slist sname (treeRespond T negAuth query) = false
    ∧ Server.strictDenialB (treeRespond T negAuth query) = false
    ∧ Server.probePassableB (treeRespond T negAuth query) = false
    ∧ ((treeRespond T negAuth query).header.rcode == VeriDNS.Spec.Rcode.formatError) = false := by
  have hred := treeRespond_nodata_eq T negAuth query qu hq hlk
  have htcR : (treeRespond T negAuth query).header.tc = query.header.tc := by rw [hred]
  have hrcR : (treeRespond T negAuth query).header.rcode = query.header.rcode := by rw [hred]
  have hauthR : (treeRespond T negAuth query).authority = negAuth := by rw [hred]
  have haeR : (treeRespond T negAuth query).answer = #[] := by rw [hred]; exact hae
  have hnoNsR : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord)
      (treeRespond T negAuth query).authority 2 = false := by rw [hauthR]; exact hnoNs
  have hcls : Resolver.classifiableB (treeRespond T negAuth query) = true := by
    simp only [Resolver.classifiableB, hrcR, hrcNo,
      show (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.noError) = true by decide,
      Bool.or_true, Bool.true_or]
  have hnn : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by decide
  refine ⟨by rw [htcR]; exact htc, ?_, ?_, ?_, by rw [hrcR, hrcNo]; decide⟩
  · simp only [Server.unfollowableDelegationB, Server.bogusDelegationB, Server.delegationShapedB,
      hnoNsR, Bool.false_and, Bool.or_self]
  · simp only [Server.strictDenialB, hrcR, hrcNo, hnn, Bool.false_and, Bool.and_false]
  · simp only [Server.probePassableB, Server.referralShapedB, Server.retryShapedB,
      hnoNsR, hrcR, hrcNo, hnsf, hcls, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.or_self]



theorem flatAuthoritative_answerRound_delivers
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (rr : VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetwork (treeRespond T negAuth) w)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hresp0Eq : resp0 = treeRespond T negAuth sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
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
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hmem : rr ∈ rrs)
    (hrtRR : VeriDNS.Spec.RRParse.parseRaw (VeriDNS.Spec.RRParse.rrBytes rr) = some rr)
    (hown : VeriDNS.Impl.DomainName.nameEqCI (VeriDNS.Spec.RRParse.rrName rr) qu.qname = true)
    (htc : (sent.header.tc == 1) = false)
    (hsf : (sent.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hfe : (sent.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w
      (.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp0, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp0),
          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp0
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp0) resp0.answer)
            (Resolver.credAnswer (resp0.header.aa == 1)) state.now).boundLru
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp0)
            state.now)) := by
  subst hsentEq hresp0Eq
  have hwire := oracle_supplies_round (treeRespond T negAuth)
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (Server.ipv4ToAddr ipAddr) w hcoop hsent
    (treeRespond_header_id T negAuth _) (treeRespond_question T negAuth _) qu hq
  have hsanEq : Server.capTtls (Edns.stripOpt
      (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))))
      = treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) := by
    rw [Edns.stripOpt_eq_self _ hopt harc]; exact capTtls_eq_self _ ha hn hd
  have hcls := treeRespond_answer_classified T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (state.resources.slist.markQueried entry.name) state.resources.sname
    qu rrs rr hq hlk hmem hrtRR hown htc hsf hfe
  exact honestAnswerRound_delivers sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    hsendq hdl hbest hegress hbuild hprobe
    hwire.1 hrt hwire.2.1 hwire.2.2
    (treeRespond_qr_opcode T negAuth _ qu hq).1
    (by rw [(treeRespond_qr_opcode T negAuth _ qu hq).2,
        (withSecrets_qr_opcode subQuery₀ _ _).2,
        buildSubQuery_opcode state revealed subQuery₀ hbuild])
    hsanEq
    hcls.1 hcls.2.1 hcls.2.2.1 hcls.2.2.2.1 hcls.2.2.2.2.1 hcls.2.2.2.2.2.1
    hcls.2.2.2.2.2.2

theorem flatAuthoritative_nxdomainRound_delivers
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
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nameError)
    (hae : sent.answer = #[])
    (htc : (sent.header.tc == 1) = false) :
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
  have hcls := treeRespond_nxdomain_classified T negAuth
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (state.resources.slist.markQueried entry.name) state.resources.sname
    qu hq hlk hae htc
  exact honestNxdomainRound_delivers sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    (treeRespond T negAuth (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
    hsendq hdl hbest hegress hbuild hprobe
    hwire.1 hrt hwire.2.1 hwire.2.2
    (treeRespond_qr_opcode T negAuth _ qu hq).1
    (by rw [(treeRespond_qr_opcode T negAuth _ qu hq).2,
        (withSecrets_qr_opcode subQuery₀ _ _).2,
        buildSubQuery_opcode state revealed subQuery₀ hbuild])
    hsanEq
    hcls.1 hcls.2.1 hcls.2.2.1 hcls.2.2.2.1 hcls.2.2.2.2.1 hcls.2.2.2.2.2.1 hcls.2.2.2.2.2.2.1
    hcls.2.2.2.2.2.2.2



theorem canonicalRR_optRRBytes (size : Nat) :
    CanonicalRR (Edns.optRRBytes size) := by
  refine ⟨#[], Edns.optType, BitVec.ofNat 16 size, 0, ByteArray.empty,
    (fun i h => absurd h (by simp)), by decide, ?_, ?_⟩
  · exact CanonicalRdata.other (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · show Edns.optRRBytes size
      = rrWire #[] Edns.optType (BitVec.ofNat 16 size) 0 ByteArray.empty
    unfold Edns.optRRBytes Edns.optRR
    rw [VeriDNS.Impl.ResourceRecord.encode, rrWire_encoder]
    rfl

theorem questionFromLabels_of_canonicalName {q : VeriDNS.Spec.Question}
    (h : CanonicalName q.qname) : QuestionFromLabels q := by
  obtain ⟨ls, hv, hle, heq⟩ := h
  exact ⟨ls, hv, hle, heq.symm⟩

theorem validRRBytes_singleton {b : ByteArray} (h : CanonicalRR b) :
    ValidRRBytes #[b] :=
  canonicalSection_validRRBytes (fun x hx => by
    rw [Array.mem_singleton.mp hx]; exact h)

theorem buildSubQuery_withSecrets_roundtrips
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format) (rid cid : UInt16)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
    (hcanon : CanonicalName state.resources.sname) :
    Impl.Message.decode (Impl.Message.encode (Server.withSecrets subQuery₀ rid cid))
      = .ok (Server.withSecrets subQuery₀ rid cid) := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i origQuery hlq
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu hqu
      injection hbuild with hb
      have hqf : subQuery₀.question
          = #[Resolver.subQuestion state.resources.sname revealed qu] := by rw [← hb]
      have haf : subQuery₀.answer = (#[] : Array ByteArray) := by rw [← hb]
      have hnf : subQuery₀.authority = (#[] : Array ByteArray) := by rw [← hb]
      have hdf : subQuery₀.additional
          = if state.noEdns then #[] else #[Edns.optRRBytes Edns.advertisedUdpSize] := by
        rw [← hb]
      have hqd : subQuery₀.header.qdcount = BitVec.ofNat 16 1 := by rw [← hb]
      have hac : subQuery₀.header.ancount = 0 := by rw [← hb]
      have hnc : subQuery₀.header.nscount = 0 := by rw [← hb]
      have hrc : subQuery₀.header.arcount
          = if state.noEdns then 0 else 1 := by rw [← hb]
      have wq : (Server.withSecrets subQuery₀ rid cid).question
          = subQuery₀.question.map
              (fun q => { q with qname := DomainName.randomizeCase cid q.qname }) := rfl
      have wa : (Server.withSecrets subQuery₀ rid cid).answer = subQuery₀.answer := rfl
      have wn : (Server.withSecrets subQuery₀ rid cid).authority = subQuery₀.authority := rfl
      have wd : (Server.withSecrets subQuery₀ rid cid).additional = subQuery₀.additional := rfl
      have wqd : (Server.withSecrets subQuery₀ rid cid).header.qdcount
          = subQuery₀.header.qdcount := rfl
      have wac : (Server.withSecrets subQuery₀ rid cid).header.ancount
          = subQuery₀.header.ancount := rfl
      have wnc : (Server.withSecrets subQuery₀ rid cid).header.nscount
          = subQuery₀.header.nscount := rfl
      have wrc : (Server.withSecrets subQuery₀ rid cid).header.arcount
          = subQuery₀.header.arcount := rfl
      have hsubq : Resolver.subQuestion state.resources.sname revealed qu
          = { qname := state.resources.sname, qtype := qu.qtype, qclass := qu.qclass } := by
        rw [Resolver.subQuestion, if_neg (by rw [hprobe]; simp)]
      apply decode_encode
      · show (Server.withSecrets subQuery₀ rid cid).header.qdcount.toNat
          = (Server.withSecrets subQuery₀ rid cid).question.size
        rw [wqd, hqd, wq, hqf]
        simp
      · show (Server.withSecrets subQuery₀ rid cid).header.ancount.toNat
          = (Server.withSecrets subQuery₀ rid cid).answer.size
        rw [wac, hac, wa, haf]; decide
      · show (Server.withSecrets subQuery₀ rid cid).header.nscount.toNat
          = (Server.withSecrets subQuery₀ rid cid).authority.size
        rw [wnc, hnc, wn, hnf]; decide
      · show (Server.withSecrets subQuery₀ rid cid).header.arcount.toNat
          = (Server.withSecrets subQuery₀ rid cid).additional.size
        rw [wrc, hrc, wd, hdf]
        cases hne : state.noEdns
        · rw [if_neg (by exact Bool.false_ne_true), if_neg (by exact Bool.false_ne_true)]
          decide
        · rw [if_pos rfl, if_pos rfl]
          decide
      ·
        show ValidQuestions (Server.withSecrets subQuery₀ rid cid).question
        rw [wq, hqf, hsubq, Array.map_singleton]
        refine validQuestionsOfForall (fun i => ?_)
        apply questionFromLabels_of_canonicalName
        have hi : (i : Nat) < 1 := i.isLt
        simp only [Fin.getElem_fin, Array.getElem_singleton hi]
        exact canonicalName_randomizeCase cid hcanon
      · show ValidRRBytes (Server.withSecrets subQuery₀ rid cid).answer
        rw [wa, haf]; exact canonicalSection_validRRBytes canonicalSection_empty
      · show ValidRRBytes (Server.withSecrets subQuery₀ rid cid).authority
        rw [wn, hnf]; exact canonicalSection_validRRBytes canonicalSection_empty
      · show ValidRRBytes (Server.withSecrets subQuery₀ rid cid).additional
        rw [wd, hdf]
        cases hne : state.noEdns
        · rw [if_neg (by exact Bool.false_ne_true)]
          exact validRRBytes_singleton (canonicalRR_optRRBytes _)
        · rw [if_pos rfl]
          exact canonicalSection_validRRBytes canonicalSection_empty

theorem buildSubQuery_withSecrets_sections
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format) (rid cid : UInt16)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀) :
    (Server.withSecrets subQuery₀ rid cid).answer = #[]
    ∧ (Server.withSecrets subQuery₀ rid cid).authority = #[] := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i origQuery hlq
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu hqu
      injection hbuild with hb
      exact ⟨by show subQuery₀.answer = #[]; rw [← hb], by show subQuery₀.authority = #[]; rw [← hb]⟩

theorem probeRoundB_false_of_fullReveal (sname : ByteArray) (revealed : Nat)
    (h : DomainName.labelCount sname ≤ revealed) :
    Resolver.probeRoundB sname revealed = false := by
  unfold Resolver.probeRoundB
  have hlt : ¬ (revealed < DomainName.labelCount sname) := by omega
  simp [hlt]

theorem buildSubQuery_withSecrets_question
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format) (rid cid : UInt16)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false) :
    (Server.withSecrets subQuery₀ rid cid).question[0]?
      = some { qname := DomainName.randomizeCase cid state.resources.sname,
               qtype := qu.qtype, qclass := qu.qclass } := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i origQuery hlq'
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu' hqu'
      rw [hlq] at hlq'
      injection hlq' with hoq
      subst hoq
      rw [hqu] at hqu'
      injection hqu' with hqe
      subst hqe
      injection hbuild with hb
      have hqf : subQuery₀.question
          = #[Resolver.subQuestion state.resources.sname revealed qu] := by rw [← hb]
      have hsubq : Resolver.subQuestion state.resources.sname revealed qu
          = { qname := state.resources.sname, qtype := qu.qtype, qclass := qu.qclass } := by
        rw [Resolver.subQuestion, if_neg (by rw [hprobe]; simp)]
      have wq : (Server.withSecrets subQuery₀ rid cid).question
          = subQuery₀.question.map
              (fun qx => { qx with qname := DomainName.randomizeCase cid qx.qname }) := rfl
      rw [wq, hqf, hsubq, Array.map_singleton]
      rfl

theorem buildSubQuery_withSecrets_header
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format) (rid cid : UInt16)
    (q : VeriDNS.Spec.Format)
    (hlq : state.lastQuery = some q)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀) :
    (Server.withSecrets subQuery₀ rid cid).header.tc = q.header.tc
    ∧ (Server.withSecrets subQuery₀ rid cid).header.rcode = q.header.rcode := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i origQuery hlq'
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu' hqu'
      rw [hlq] at hlq'
      injection hlq' with hoq
      subst hoq
      injection hbuild with hb
      constructor
      · show (Server.withSecrets subQuery₀ rid cid).header.tc = q.header.tc
        rw [← hb]; rfl
      · show (Server.withSecrets subQuery₀ rid cid).header.rcode = q.header.rcode
        rw [← hb]; rfl

theorem buildSubQuery_withSecrets_question_probe
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format) (rid cid : UInt16)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true) :
    (Server.withSecrets subQuery₀ rid cid).question[0]?
      = some { qname := DomainName.randomizeCase cid
                 (DomainName.minimisedName state.resources.sname revealed),
               qtype := BitVec.ofNat 16 1, qclass := qu.qclass } := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i origQuery hlq'
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu' hqu'
      rw [hlq] at hlq'
      injection hlq' with hoq
      subst hoq
      rw [hqu] at hqu'
      injection hqu' with hqe
      subst hqe
      injection hbuild with hb
      have hqf : subQuery₀.question
          = #[Resolver.subQuestion state.resources.sname revealed qu] := by rw [← hb]
      have hsubq : Resolver.subQuestion state.resources.sname revealed qu
          = { qname := DomainName.minimisedName state.resources.sname revealed,
              qtype := BitVec.ofNat 16 1, qclass := qu.qclass } := by
        rw [Resolver.subQuestion, if_pos hprobe]
      have wq : (Server.withSecrets subQuery₀ rid cid).question
          = subQuery₀.question.map
              (fun qx => { qx with qname := DomainName.randomizeCase cid qx.qname }) := rfl
      rw [wq, hqf, hsubq, Array.map_singleton]
      rfl

theorem buildSubQuery_withSecrets_roundtrips_probe
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (revealed : Nat) (subQuery₀ : VeriDNS.Spec.Format) (rid cid : UInt16)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (hcanon : CanonicalName state.resources.sname) :
    Impl.Message.decode (Impl.Message.encode (Server.withSecrets subQuery₀ rid cid))
      = .ok (Server.withSecrets subQuery₀ rid cid) := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i origQuery hlq
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu hqu
      injection hbuild with hb
      have hqf : subQuery₀.question
          = #[Resolver.subQuestion state.resources.sname revealed qu] := by rw [← hb]
      have haf : subQuery₀.answer = (#[] : Array ByteArray) := by rw [← hb]
      have hnf : subQuery₀.authority = (#[] : Array ByteArray) := by rw [← hb]
      have hdf : subQuery₀.additional
          = if state.noEdns then #[] else #[Edns.optRRBytes Edns.advertisedUdpSize] := by
        rw [← hb]
      have hqd : subQuery₀.header.qdcount = BitVec.ofNat 16 1 := by rw [← hb]
      have hac : subQuery₀.header.ancount = 0 := by rw [← hb]
      have hnc : subQuery₀.header.nscount = 0 := by rw [← hb]
      have hrc : subQuery₀.header.arcount
          = if state.noEdns then 0 else 1 := by rw [← hb]
      have wq : (Server.withSecrets subQuery₀ rid cid).question
          = subQuery₀.question.map
              (fun q => { q with qname := DomainName.randomizeCase cid q.qname }) := rfl
      have wa : (Server.withSecrets subQuery₀ rid cid).answer = subQuery₀.answer := rfl
      have wn : (Server.withSecrets subQuery₀ rid cid).authority = subQuery₀.authority := rfl
      have wd : (Server.withSecrets subQuery₀ rid cid).additional = subQuery₀.additional := rfl
      have wqd : (Server.withSecrets subQuery₀ rid cid).header.qdcount
          = subQuery₀.header.qdcount := rfl
      have wac : (Server.withSecrets subQuery₀ rid cid).header.ancount
          = subQuery₀.header.ancount := rfl
      have wnc : (Server.withSecrets subQuery₀ rid cid).header.nscount
          = subQuery₀.header.nscount := rfl
      have wrc : (Server.withSecrets subQuery₀ rid cid).header.arcount
          = subQuery₀.header.arcount := rfl
      have hsubq : Resolver.subQuestion state.resources.sname revealed qu
          = { qname := DomainName.minimisedName state.resources.sname revealed,
              qtype := BitVec.ofNat 16 1, qclass := qu.qclass } := by
        rw [Resolver.subQuestion, if_pos hprobe]
      apply decode_encode
      · show (Server.withSecrets subQuery₀ rid cid).header.qdcount.toNat
          = (Server.withSecrets subQuery₀ rid cid).question.size
        rw [wqd, hqd, wq, hqf]
        simp
      · show (Server.withSecrets subQuery₀ rid cid).header.ancount.toNat
          = (Server.withSecrets subQuery₀ rid cid).answer.size
        rw [wac, hac, wa, haf]; decide
      · show (Server.withSecrets subQuery₀ rid cid).header.nscount.toNat
          = (Server.withSecrets subQuery₀ rid cid).authority.size
        rw [wnc, hnc, wn, hnf]; decide
      · show (Server.withSecrets subQuery₀ rid cid).header.arcount.toNat
          = (Server.withSecrets subQuery₀ rid cid).additional.size
        rw [wrc, hrc, wd, hdf]
        cases hne : state.noEdns
        · rw [if_neg (by exact Bool.false_ne_true), if_neg (by exact Bool.false_ne_true)]
          decide
        · rw [if_pos rfl, if_pos rfl]
          decide
      ·
        show ValidQuestions (Server.withSecrets subQuery₀ rid cid).question
        rw [wq, hqf, hsubq, Array.map_singleton]
        refine validQuestionsOfForall (fun i => ?_)
        apply questionFromLabels_of_canonicalName
        have hi : (i : Nat) < 1 := i.isLt
        simp only [Fin.getElem_fin, Array.getElem_singleton hi]
        exact canonicalName_randomizeCase cid
          (VeriDNS.Proof.QnameMin.minimisedName_canonical hcanon revealed)
      · show ValidRRBytes (Server.withSecrets subQuery₀ rid cid).answer
        rw [wa, haf]; exact canonicalSection_validRRBytes canonicalSection_empty
      · show ValidRRBytes (Server.withSecrets subQuery₀ rid cid).authority
        rw [wn, hnf]; exact canonicalSection_validRRBytes canonicalSection_empty
      · show ValidRRBytes (Server.withSecrets subQuery₀ rid cid).additional
        rw [wd, hdf]
        cases hne : state.noEdns
        · rw [if_neg (by exact Bool.false_ne_true)]
          exact validRRBytes_singleton (canonicalRR_optRRBytes _)
        · rw [if_pos rfl]
          exact canonicalSection_validRRBytes canonicalSection_empty



def WfTreeRR (rr : VeriDNS.Spec.ResourceRecord) : Prop :=
  RRWireCanon rr ∧ rr.ttl.toNat ≤ 604800

theorem capTtlRR_rrBytes {rr : VeriDNS.Spec.ResourceRecord} (h : WfTreeRR rr) :
    Server.capTtlRR (RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr)
      = RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr := by
  obtain ⟨hcanon, httl⟩ := h
  have hf : (rr.ttl >>> 31 == 1) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    have ht : (rr.ttl >>> 31).toNat = 1 := by rw [he]; rfl
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at ht
    omega
  have hc : ¬ (604800 < rr.ttl.toNat) := by omega
  unfold Server.capTtlRR
  rw [parseRaw_rrBytes hcanon]
  simp only [hf, hc, Bool.false_eq_true, if_false]

theorem treeRespond_answer_roundtrips
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sent : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hsent : Impl.Message.decode (Impl.Message.encode sent) = .ok sent)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwf : ∀ rr ∈ rrs.toList, RRWireCanon rr) :
    Impl.Message.decode (Impl.Message.encode (treeRespond T negAuth sent))
      = .ok (treeRespond T negAuth sent) := by
  obtain ⟨hqd, han, hns, har, hvqf, hcaA, hcaN, hcaD⟩ := decode_ok_wire_facts hsent
  rw [treeRespond_answer_eq T negAuth sent qu rrs hq hlk]
  apply decode_encode
  · exact hqd
  · show (BitVec.ofNat 16 rrs.size).toNat = (rrs.map _).size
    have h216 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [Array.size_map, BitVec.toNat_ofNat, h216, Nat.mod_eq_of_lt hsz]
  · exact hns
  · rfl
  · exact validQuestionsOfForall hvqf
  · exact canonicalSection_validRRBytes (canonicalSection_map_rrBytes hwf)
  · exact canonicalSection_validRRBytes hcaN
  · exact canonicalSection_validRRBytes canonicalSection_empty

theorem treeRespond_nxdomain_roundtrips
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sent : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hsent : Impl.Message.decode (Impl.Message.encode sent) = .ok sent)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nameError)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth) :
    Impl.Message.decode (Impl.Message.encode (treeRespond T negAuth sent))
      = .ok (treeRespond T negAuth sent) := by
  obtain ⟨hqd, han, hns, har, hvqf, hcaA, hcaN, hcaD⟩ := decode_ok_wire_facts hsent
  rw [treeRespond_nameError_eq T negAuth sent qu hq hlk]
  apply decode_encode
  · exact hqd
  · exact han
  · show (BitVec.ofNat 16 negAuth.size).toNat = negAuth.size
    have h216 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [BitVec.toNat_ofNat, h216, Nat.mod_eq_of_lt hnsz]
  · rfl
  · exact validQuestionsOfForall hvqf
  · exact canonicalSection_validRRBytes hcaA
  · exact canonicalSection_validRRBytes hcanNeg
  · exact canonicalSection_validRRBytes canonicalSection_empty

theorem treeRespond_nodata_roundtrips
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sent : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hsent : Impl.Message.decode (Impl.Message.encode sent) = .ok sent)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nodata)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth) :
    Impl.Message.decode (Impl.Message.encode (treeRespond T negAuth sent))
      = .ok (treeRespond T negAuth sent) := by
  obtain ⟨hqd, han, hns, har, hvqf, hcaA, hcaN, hcaD⟩ := decode_ok_wire_facts hsent
  rw [treeRespond_nodata_eq T negAuth sent qu hq hlk]
  apply decode_encode
  · exact hqd
  · exact han
  · show (BitVec.ofNat 16 negAuth.size).toNat = negAuth.size
    have h216 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [BitVec.toNat_ofNat, h216, Nat.mod_eq_of_lt hnsz]
  · rfl
  · exact validQuestionsOfForall hvqf
  · exact canonicalSection_validRRBytes hcaA
  · exact canonicalSection_validRRBytes hcanNeg
  · exact canonicalSection_validRRBytes canonicalSection_empty



theorem resolveWithIO_flatAuthoritative_answer_adequate
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel' depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetwork (treeRespond T negAuth) w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hresp0Eq : resp0 = treeRespond T negAuth sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ now + budget))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state (Server.seedRevealed state) = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname (Server.seedRevealed state) = false)
    (hcanon : CanonicalName state.resources.sname)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr)
    (hown : ∀ rr ∈ rrs.toList,
        VeriDNS.Impl.DomainName.nameEqCI (VeriDNS.Spec.RRParse.rrName rr) qu.qname = true)
    (htc : (sent.header.tc == 1) = false)
    (hsf : (sent.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hfe : (sent.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ (K : Nat) (w' : World), Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now (fuel' + 1) depth budget) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp0, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp0),
          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp0
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp0) resp0.answer)
            (Resolver.credAnswer (resp0.header.aa == 1)) state.now).boundLru
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp0)
            state.now)), w') := by
  subst hresp0Eq
  have hsent := buildSubQuery_withSecrets_roundtrips state (Server.seedRevealed state)
    subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild hprobe hcanon
  rw [← hsentEq] at hsent
  have haeq := treeRespond_answer_eq T negAuth sent qu rrs hq hlk
  have hadd := treeRespond_additional_empty T negAuth sent qu hq
  have hsecAuth : sent.authority = #[] := by
    have h := (buildSubQuery_withSecrets_sections state (Server.seedRevealed state)
      subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild).2
    rw [← hsentEq] at h; exact h
  have hpos := (treeLookup_answer T qu.qname qu.qtype rrs hlk).1
  have hmem : rrs[0] ∈ rrs := Array.getElem_mem hpos
  have hrt := treeRespond_answer_roundtrips T negAuth sent qu rrs hsent hq hlk hsz
    (fun rr h => (hwfRR rr h).1)
  have hopt : ∀ b ∈ (treeRespond T negAuth sent).additional, Edns.isOptRR b = false := by
    rw [hadd.1]; intro b hb; simp at hb
  have harc : (treeRespond T negAuth sent).header.arcount
      = BitVec.ofNat 16 (treeRespond T negAuth sent).additional.size := by
    rw [hadd.1, hadd.2]; rfl
  have ha : ∀ b ∈ (treeRespond T negAuth sent).answer, Server.capTtlRR b = b := by
    have hans : (treeRespond T negAuth sent).answer = rrs.map RRParse.rrBytes := by rw [haeq]
    rw [hans]; intro b hb
    rw [Array.mem_map] at hb; obtain ⟨rr, hrr, rfl⟩ := hb
    exact capTtlRR_rrBytes (hwfRR rr (Array.mem_def.mp hrr))
  have hn : ∀ b ∈ (treeRespond T negAuth sent).authority, Server.capTtlRR b = b := by
    have hauth : (treeRespond T negAuth sent).authority = #[] := by rw [haeq]; exact hsecAuth
    rw [hauth]; intro b hb; simp at hb
  have hd : ∀ b ∈ (treeRespond T negAuth sent).additional, Server.capTtlRR b = b := by
    rw [hadd.1]; intro b hb; simp at hb
  have hrtRR := parseRaw_rrBytes (hwfRR rrs[0] (Array.mem_def.mp hmem)).1
  exact resolveWithIO_delivers query sbelt cache now (fuel' + 1) depth budget w state _ hpause
    (flatAuthoritative_answerRound_delivers T negAuth sbelt state (now + budget) depth fuel'
      (Server.seedRevealed state) w entry ipAddr subQuery₀ sent (treeRespond T negAuth sent) qu rrs rrs[0]
      hcoop hsentEq rfl hsendq hdl hbest hegress hbuild hprobe
      hsent hrt hopt harc ha hn hd hq hlk hmem hrtRR (hown rrs[0] (Array.mem_def.mp hmem)) htc hsf hfe)

theorem resolveWithIO_flatAuthoritative_nxdomain_adequate
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
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state (Server.seedRevealed state) = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname (Server.seedRevealed state) = false)
    (hcanon : CanonicalName state.resources.sname)
    (hq : sent.question[0]? = some qu)
    (hlk : VeriDNS.Impl.NameTree.treeLookup T qu.qname qu.qtype = .nameError)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnclean : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (htc : (sent.header.tc == 1) = false) :
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
  have hneq := treeRespond_nameError_eq T negAuth sent qu hq hlk
  have hadd := treeRespond_additional_empty T negAuth sent qu hq
  have hae : sent.answer = #[] := by
    have h := (buildSubQuery_withSecrets_sections state (Server.seedRevealed state)
      subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild).1
    rw [← hsentEq] at h; exact h
  have hrt := treeRespond_nxdomain_roundtrips T negAuth sent qu hsent hq hlk hnsz hcanNeg
  have hopt : ∀ b ∈ (treeRespond T negAuth sent).additional, Edns.isOptRR b = false := by
    rw [hadd.1]; intro b hb; simp at hb
  have harc : (treeRespond T negAuth sent).header.arcount
      = BitVec.ofNat 16 (treeRespond T negAuth sent).additional.size := by
    rw [hadd.1, hadd.2]; rfl
  have ha : ∀ b ∈ (treeRespond T negAuth sent).answer, Server.capTtlRR b = b := by
    have hans : (treeRespond T negAuth sent).answer = #[] := by rw [hneq]; exact hae
    rw [hans]; intro b hb; simp at hb
  have hn : ∀ b ∈ (treeRespond T negAuth sent).authority, Server.capTtlRR b = b := by
    have hauth : (treeRespond T negAuth sent).authority = negAuth := by rw [hneq]
    rw [hauth]; exact hnclean
  have hd : ∀ b ∈ (treeRespond T negAuth sent).additional, Server.capTtlRR b = b := by
    rw [hadd.1]; intro b hb; simp at hb
  exact resolveWithIO_delivers query sbelt cache now (fuel' + 1) depth budget w state _ hpause
    (flatAuthoritative_nxdomainRound_delivers T negAuth sbelt state (now + budget) depth fuel'
      (Server.seedRevealed state) w entry ipAddr subQuery₀ sent (treeRespond T negAuth sent) qu
      hcoop hsentEq rfl hsendq hdl hbest hegress hbuild hprobe
      hsent hrt hopt harc ha hn hd hq hlk hae htc)



inductive InZone {RR : Type} (rr : RR) : VeriDNS.Spec.Node RR → Prop where
  | atHere {n : VeriDNS.Spec.Node RR} : rr ∈ n.resourceSet → InZone rr n
  | atChild {n c : VeriDNS.Spec.Node RR} : c ∈ n.children → InZone rr c → InZone rr n

def WfTree (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) : Prop :=
  ∀ rr, InZone rr T → WfTreeRR rr

theorem findChild_mem {RR : Type} (root c : VeriDNS.Spec.Node RR) (lab : ByteArray)
    (h : VeriDNS.Impl.NameTree.findChild root lab = some c) : c ∈ root.children :=
  Array.mem_of_find?_eq_some h

theorem nodeAt_inTree {RR : Type} (root n : VeriDNS.Spec.Node RR) (path : List ByteArray)
    (h : VeriDNS.Impl.NameTree.nodeAt root path = some n) :
    ∀ rr ∈ n.resourceSet, InZone rr root := by
  induction path generalizing root with
  | nil =>
    simp only [VeriDNS.Impl.NameTree.nodeAt] at h
    injection h with h; subst h
    exact fun rr hrr => InZone.atHere hrr
  | cons l rest ih =>
    simp only [VeriDNS.Impl.NameTree.nodeAt] at h
    split at h
    · rename_i c hc
      intro rr hrr
      exact InZone.atChild (findChild_mem root c l hc) (ih c h rr hrr)
    · exact absurd h (by simp)

theorem nodeAtName_inTree {RR : Type} (T n : VeriDNS.Spec.Node RR) (qname : ByteArray)
    (h : VeriDNS.Impl.NameTree.nodeAtName T qname = some n) :
    ∀ rr ∈ n.resourceSet, InZone rr T := by
  unfold VeriDNS.Impl.NameTree.nodeAtName at h
  split at h
  · exact nodeAt_inTree T n _ h
  · exact absurd h (by simp)

theorem lookupAt_answer_mem {RR : Type} [VeriDNS.Spec.RRParse RR]
    (n : VeriDNS.Spec.Node RR) (qtype : BitVec 16) (rrs : Array RR)
    (h : VeriDNS.Impl.NameTree.lookupAt n qtype = .answer rrs) :
    ∀ rr ∈ rrs, rr ∈ n.resourceSet := by
  unfold VeriDNS.Impl.NameTree.lookupAt at h
  simp only at h
  split at h
  · rw [VeriDNS.Impl.NameTree.Outcome.answer.injEq] at h
    subst h
    exact fun rr hrr => (Array.mem_filter.mp hrr).1
  · split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)

theorem treeLookup_answer_node {RR : Type} [VeriDNS.Spec.RRParse RR]
    (T : VeriDNS.Spec.Node RR) (qname : ByteArray) (qtype : BitVec 16) (rrs : Array RR)
    (h : VeriDNS.Impl.NameTree.treeLookup T qname qtype = .answer rrs) :
    ∃ n, VeriDNS.Impl.NameTree.nodeAtName T qname = some n
      ∧ VeriDNS.Impl.NameTree.lookupAt n qtype = .answer rrs := by
  unfold VeriDNS.Impl.NameTree.treeLookup at h
  split at h
  · exact absurd h (by simp)
  · rename_i n hn; exact ⟨n, hn, h⟩

theorem treeLookup_answer_wfTree
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (qname : ByteArray) (qtype : BitVec 16)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hwf : WfTree T)
    (h : VeriDNS.Impl.NameTree.treeLookup T qname qtype = .answer rrs) :
    ∀ rr ∈ rrs.toList, WfTreeRR rr := by
  obtain ⟨n, hn, hla⟩ := treeLookup_answer_node T qname qtype rrs h
  intro rr hrr
  exact hwf rr (nodeAtName_inTree T n qname hn rr
    (lookupAt_answer_mem n qtype rrs hla rr (Array.mem_def.mpr hrr)))




theorem hasRRTypeIn_nonempty {RR : Type} [VeriDNS.Spec.RRParse RR]
    (rrs : Array ByteArray) (code : BitVec 16)
    (h : Resolver.hasRRTypeIn (RR := RR) rrs code = true) : rrs.isEmpty = false := by
  unfold Resolver.hasRRTypeIn at h
  rw [Array.any_eq_true] at h
  obtain ⟨x, hx, _⟩ := h
  exact Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨rrs[x], Array.getElem_mem hx⟩

def referralReply (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray) :
    VeriDNS.Spec.Format :=
  { query with
      header := { query.header with qr := 1, aa := 0, rcode := VeriDNS.Spec.Rcode.noError, ancount := 0, nscount := BitVec.ofNat 16 nsAuth.size, arcount := BitVec.ofNat 16 glue.size },
      answer := #[],
      authority := nsAuth,
      additional := glue }

theorem referralReply_header_id (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray) :
    (referralReply query nsAuth glue).header.id = query.header.id := rfl

theorem referralReply_question (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray) :
    (referralReply query nsAuth glue).question = query.question := rfl

theorem referralReply_continues
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false) :
    ∃ st, Server.afterResume state entryName (referralReply query nsAuth glue) = .continue st := by
  have hansE : (referralReply query nsAuth glue).answer = #[] := rfl
  have hauthE : (referralReply query nsAuth glue).authority = nsAuth := rfl
  have hrcR : (referralReply query nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  have haaR : (referralReply query nsAuth glue).header.aa = 0 := rfl
  have hnoerr : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.noError) = true := by decide
  have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by decide
  have hnne : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  have hcls : Resolver.classifiableB (referralReply query nsAuth glue) = true := by
    simp only [Resolver.classifiableB, hrcR, hnoerr, Bool.or_true, Bool.true_or]
  refine VeriDNS.Proof.Refinement.afterResume_referral_continues state entryName _ hstep
    (cnameToChase_of_emptyAnswer _ hansE) ?_ (answersQueryB_of_emptyAnswer _ hansE)
    (by rw [hrcR]; exact hnne) (by rw [hansE]; rfl) ?_ ?_ (by rw [haaR]; rfl)
    (by rw [hrcR]; exact hnoerr) ?_
  · rw [hrcR, hcls]; simp only [hnsf, Bool.not_true, Bool.or_false]
  · rw [hauthE]; exact hasRRTypeIn_nonempty nsAuth 2 hns
  · rw [hauthE]; exact hns
  · rw [hauthE]; exact hsoa

theorem referralReply_continue_struct
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false) :
    ∃ st, Server.afterResume state entryName (referralReply query nsAuth glue) = .continue st
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries := by
  have hansE : (referralReply query nsAuth glue).answer = #[] := rfl
  have hauthE : (referralReply query nsAuth glue).authority = nsAuth := rfl
  have hrcR : (referralReply query nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  have haaR : (referralReply query nsAuth glue).header.aa = 0 := rfl
  have hnoerr : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.noError) = true := by decide
  have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by decide
  have hnne : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  have hcls : Resolver.classifiableB (referralReply query nsAuth glue) = true := by
    simp only [Resolver.classifiableB, hrcR, hnoerr, Bool.or_true, Bool.true_or]
  obtain ⟨st, hc, _, hsn, hnw, hcc, hcs⟩ :=
    VeriDNS.Proof.Refinement.afterResume_referral_continue_struct state entryName _ hstep
      (cnameToChase_of_emptyAnswer _ hansE)
      (by rw [hrcR, hcls]; simp only [hnsf, Bool.not_true, Bool.or_false])
      (answersQueryB_of_emptyAnswer _ hansE)
      (by rw [hrcR]; exact hnne) (by rw [hansE]; rfl)
      (by rw [hauthE]; exact hasRRTypeIn_nonempty nsAuth 2 hns)
      (by rw [hauthE]; exact hns) (by rw [haaR]; rfl)
      (by rw [hrcR]; exact hnoerr) (by rw [hauthE]; exact hsoa)
  exact ⟨st, hc, hsn, hnw, hcc, hcs⟩

theorem referralReply_continue_sendFacts
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (revealed : Nat)
    (hstep : state.currentStep = .sendQueries)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hcanon : CanonicalName state.resources.sname) :
    ∃ st, Server.afterResume state entryName (referralReply query nsAuth glue) = .continue st
      ∧ st.currentStep = .sendQueries
      ∧ CanonicalName st.resources.sname
      ∧ ∃ sq, Resolver.buildSubQuery st revealed = some sq := by
  have hansE : (referralReply query nsAuth glue).answer = #[] := rfl
  have hauthE : (referralReply query nsAuth glue).authority = nsAuth := rfl
  have hrcR : (referralReply query nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  have haaR : (referralReply query nsAuth glue).header.aa = 0 := rfl
  have hnoerr : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.noError) = true := by decide
  have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by decide
  have hnne : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  have hcls : Resolver.classifiableB (referralReply query nsAuth glue) = true := by
    simp only [Resolver.classifiableB, hrcR, hnoerr, Bool.or_true, Bool.true_or]
  obtain ⟨st, hc, _, hsn, _, _, hcs, hlqst, _, _⟩ :=
    VeriDNS.Proof.Refinement.afterResume_referral_continue_cases state entryName _ hstep
      (cnameToChase_of_emptyAnswer _ hansE)
      (by rw [hrcR, hcls]; simp only [hnsf, Bool.not_true, Bool.or_false])
      (answersQueryB_of_emptyAnswer _ hansE)
      (by rw [hrcR]; exact hnne) (by rw [hansE]; rfl)
      (by rw [hauthE]; exact hasRRTypeIn_nonempty nsAuth 2 hns)
      (by rw [hauthE]; exact hns) (by rw [haaR]; rfl)
      (by rw [hrcR]; exact hnoerr) (by rw [hauthE]; exact hsoa)
  refine ⟨st, hc, hcs, by rw [hsn]; exact hcanon, ?_⟩
  have hbq : (Resolver.buildSubQuery st revealed).isSome = true := by
    simp only [Resolver.buildSubQuery, hlqst, hlq, hqu, Option.isSome_some]
  exact Option.isSome_iff_exists.mp hbq

theorem referralReply_delegationShaped
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true) :
    Server.delegationShapedB (referralReply query nsAuth glue) = true := by
  have hansE : (referralReply query nsAuth glue).answer = #[] := rfl
  have hauthE : (referralReply query nsAuth glue).authority = nsAuth := rfl
  have hrcR : (referralReply query nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  have hnne : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  unfold Server.delegationShapedB
  rw [hauthE, hns, answersQueryB_of_emptyAnswer _ hansE, cnameToChase_of_emptyAnswer _ hansE, hrcR]
  simp only [hnne, Bool.not_false, Option.isNone_none, Bool.and_true]

theorem referralReply_strictDenial_false
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray) :
    Server.strictDenialB (referralReply query nsAuth glue) = false := by
  have hrcR : (referralReply query nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  unfold Server.strictDenialB
  rw [hrcR]
  simp only [show (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false by decide,
    Bool.and_false, Bool.false_and]

theorem referralReply_probePassable
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false) :
    Server.probePassableB (referralReply query nsAuth glue) = true := by
  have hansE : (referralReply query nsAuth glue).answer = #[] := rfl
  have hauthE : (referralReply query nsAuth glue).authority = nsAuth := rfl
  have hrcR : (referralReply query nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  have haaE : (referralReply query nsAuth glue).header.aa = 0 := rfl
  unfold Server.probePassableB Server.referralShapedB
  rw [hauthE, hns, hsoa, answersQueryB_of_emptyAnswer _ hansE,
    cnameToChase_of_emptyAnswer _ hansE, hrcR, haaE, hansE,
    hasRRTypeIn_nonempty (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 hns]
  simp
  exact Or.inl (by decide)

theorem referralReply_unfollowable_false
    (query : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (slist : DnsSList) (sname : ByteArray)
    (hcloser : Server.delegationCloserB slist sname (referralReply query nsAuth glue) = true)
    (hbai : Server.respInBailiwick sname (referralReply query nsAuth glue) = true) :
    Server.unfollowableDelegationB slist sname (referralReply query nsAuth glue) = false := by
  unfold Server.unfollowableDelegationB Server.bogusDelegationB
  rw [hcloser, hbai]
  simp



theorem flatDelegating_referralNode
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (qu : VeriDNS.Spec.Question)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr)
        = some (honestDatagram (Server.ipv4ToAddr ipAddr)
            (VeriDNS.Impl.Message.encode (referralReply sent nsAuth glue))))
    (hrt : VeriDNS.Impl.Message.decode
        (VeriDNS.Impl.Message.encode (referralReply sent nsAuth glue))
        = .ok (referralReply sent nsAuth glue))
    (hopt : ∀ b ∈ glue, Edns.isOptRR b = false)
    (hn : ∀ b ∈ nsAuth, Server.capTtlRR b = b)
    (hd : ∀ b ∈ glue, Server.capTtlRR b = b)
    (hq : sent.question[0]? = some qu)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false)
    (htc : ((referralReply sent nsAuth glue).header.tc == 1) = false)
    (hcloser : Server.delegationCloserB (state.resources.slist.markQueried entry.name)
        state.resources.sname (referralReply sent nsAuth glue) = true)
    (hbai : Server.respInBailiwick state.resources.sname
        (referralReply sent nsAuth glue) = true)
    (hnext : ∀ st, Server.afterResume { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } } entry.name
          (referralReply sent nsAuth glue) = .continue st →
        ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
          w'.ids = w.ids → w'.clock = w.clock + w.tick w.exchCtr →
        w'.exchCtr = w.exchCtr + 1 → w'.tick = w.tick → w'.idCtr = w.idCtr + 2 →
          DescentChain sbelt deadline depth out st fuel'
            (Server.revealedAfterContinue state.resources.sname revealed st) w') :
    DescentChain sbelt deadline depth out state (fuel' + 1) revealed w := by
  subst hsentEq
  obtain ⟨st, hcont⟩ := referralReply_continues
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) nsAuth glue
    { state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } } entry.name hsendq hns hsoa
  have hsanEq : Server.capTtls (Edns.stripOpt
      (referralReply (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) nsAuth glue))
      = referralReply (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) nsAuth glue := by
    rw [Edns.stripOpt_eq_self _ hopt rfl, capTtls_eq_self _ (by simp [referralReply]) hn hd]
  exact honestReferralNode sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    (referralReply (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) nsAuth glue)
    (referralReply (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) nsAuth glue)
    st out hdl hbest hegress hbuild
    (by rw [referralReply_strictDenial_false, Bool.and_false])
    (by rw [referralReply_probePassable _ nsAuth glue hns hsoa, Bool.not_true, Bool.and_false])
    horacle hrt
    (referralReply_header_id _ nsAuth glue)
    (by rw [referralReply_question]; exact questionMatches_self _ qu hq)
    rfl (buildSubQuery_opcode state revealed subQuery₀ hbuild)
    hsanEq htc
    (referralReply_unfollowable_false _ nsAuth glue _ _ hcloser hbai)
    hcont rfl (hnext st hcont)




def mkHonestOracleAddr (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format) :
    ByteArray → ByteArray → Option (VeriDNS.Spec.Exchanged ByteArray) :=
  fun qbytes addr =>
    match VeriDNS.Impl.Message.decode qbytes with
    | .error _ => none
    | .ok query => some (honestDatagram addr (VeriDNS.Impl.Message.encode (respond addr query)))

def CooperativeNetworkAddr (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (w : World) : Prop :=
  w.oracle = mkHonestOracleAddr respond

theorem CooperativeNetworkAddr_of_oracle_eq
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format) (w w' : World)
    (hcoop : CooperativeNetworkAddr respond w) (hoe : w'.oracle = w.oracle) :
    CooperativeNetworkAddr respond w' := by
  unfold CooperativeNetworkAddr at hcoop ⊢
  rw [hoe, hcoop]

theorem mkHonestOracle_eq_addr (respond : VeriDNS.Spec.Format → VeriDNS.Spec.Format) :
    mkHonestOracle respond = mkHonestOracleAddr (fun _ q => respond q) := rfl

theorem oracle_supplies_roundAddr
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (sent : VeriDNS.Spec.Format) (addr : ByteArray) (w : World)
    (hcoop : CooperativeNetworkAddr respond w)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hidP : (respond addr sent).header.id = sent.header.id)
    (hqP : (respond addr sent).question = sent.question)
    (q : VeriDNS.Spec.Question) (hne : sent.question[0]? = some q) :
    w.oracle (VeriDNS.Impl.Message.encode sent) addr
        = some (honestDatagram addr (VeriDNS.Impl.Message.encode (respond addr sent)))
    ∧ (respond addr sent).header.id = sent.header.id
    ∧ Server.questionMatches (respond addr sent).question sent.question = true := by
  refine ⟨?_, hidP, ?_⟩
  · rw [hcoop]; simp only [mkHonestOracleAddr, hsent]
  · rw [hqP]; exact questionMatches_self sent.question q hne

theorem delegatingReferralRound_node
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (qu : VeriDNS.Spec.Question)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hcoop : CooperativeNetworkAddr respond w)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hrespEq : respond (Server.ipv4ToAddr ipAddr) sent = referralReply sent nsAuth glue)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hrt : VeriDNS.Impl.Message.decode
        (VeriDNS.Impl.Message.encode (referralReply sent nsAuth glue))
        = .ok (referralReply sent nsAuth glue))
    (hopt : ∀ b ∈ glue, Edns.isOptRR b = false)
    (hn : ∀ b ∈ nsAuth, Server.capTtlRR b = b)
    (hd : ∀ b ∈ glue, Server.capTtlRR b = b)
    (hq : sent.question[0]? = some qu)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false)
    (htc : ((referralReply sent nsAuth glue).header.tc == 1) = false)
    (hcloser : Server.delegationCloserB (state.resources.slist.markQueried entry.name)
        state.resources.sname (referralReply sent nsAuth glue) = true)
    (hbai : Server.respInBailiwick state.resources.sname
        (referralReply sent nsAuth glue) = true)
    (hnext : ∀ st, Server.afterResume { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } } entry.name
          (referralReply sent nsAuth glue) = .continue st →
        ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
          w'.ids = w.ids → w'.clock = w.clock + w.tick w.exchCtr →
        w'.exchCtr = w.exchCtr + 1 → w'.tick = w.tick → w'.idCtr = w.idCtr + 2 →
          DescentChain sbelt deadline depth out st fuel'
            (Server.revealedAfterContinue state.resources.sname revealed st) w') :
    DescentChain sbelt deadline depth out state (fuel' + 1) revealed w := by
  have hwire := oracle_supplies_roundAddr respond sent (Server.ipv4ToAddr ipAddr) w hcoop hsent
    (by rw [hrespEq]; exact referralReply_header_id sent nsAuth glue)
    (by rw [hrespEq]; exact referralReply_question sent nsAuth glue) qu hq
  have horacle : w.oracle (VeriDNS.Impl.Message.encode
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
      (Server.ipv4ToAddr ipAddr)
      = some (honestDatagram (Server.ipv4ToAddr ipAddr)
          (VeriDNS.Impl.Message.encode (referralReply sent nsAuth glue))) := by
    rw [← hsentEq, ← hrespEq]; exact hwire.1
  exact flatDelegating_referralNode sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    sent nsAuth glue qu out hsentEq hsendq hdl hbest hegress hbuild horacle hrt hopt hn hd hq
    hns hsoa htc hcloser hbai hnext

theorem delegatingAnswerRound_delivers
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 resp : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hcoop : CooperativeNetworkAddr respond w)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hrespEq : respond (Server.ipv4ToAddr ipAddr) sent = resp0)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
    (hrt : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0)
    (hidP : resp0.header.id = sent.header.id)
    (hqP : resp0.question = sent.question)
    (hqrP : resp0.header.qr = 1)
    (hopP : resp0.header.opcode = sent.header.opcode)
    (hq : sent.question[0]? = some qu)
    (hsanEq : Server.capTtls (Edns.stripOpt resp0) = resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w
      (.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),
          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundLru
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            state.now)) := by
  subst hsentEq
  have hwire := oracle_supplies_roundAddr respond
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (Server.ipv4ToAddr ipAddr) w hcoop hsent
    (by rw [hrespEq]; exact hidP) (by rw [hrespEq]; exact hqP) qu hq
  exact honestAnswerRound_delivers sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    resp0 resp hsendq hdl hbest hegress hbuild hprobe
    (by rw [← hrespEq]; exact hwire.1) hrt (by rw [← hrespEq]; exact hwire.2.1)
    (by rw [← hrespEq]; exact hwire.2.2) hqrP
    (by rw [hopP]; exact buildSubQuery_opcode state revealed subQuery₀ hbuild) hsanEq htc hunfollow hcname hsf hcls hans hfe

theorem delegatingNxdomainRound_delivers
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 resp : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hcoop : CooperativeNetworkAddr respond w)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hrespEq : respond (Server.ipv4ToAddr ipAddr) sent = resp0)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
    (hrt : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0)
    (hidP : resp0.header.id = sent.header.id)
    (hqP : resp0.question = sent.question)
    (hqrP : resp0.header.qr = 1)
    (hopP : resp0.header.opcode = sent.header.opcode)
    (hq : sent.question[0]? = some qu)
    (hsanEq : Server.capTtls (Edns.stripOpt resp0) = resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hemp : resp.answer.isEmpty = true) :
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
  subst hsentEq
  have hwire := oracle_supplies_roundAddr respond
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (Server.ipv4ToAddr ipAddr) w hcoop hsent
    (by rw [hrespEq]; exact hidP) (by rw [hrespEq]; exact hqP) qu hq
  exact honestNxdomainRound_delivers sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    resp0 resp hsendq hdl hbest hegress hbuild hprobe
    (by rw [← hrespEq]; exact hwire.1) hrt (by rw [← hrespEq]; exact hwire.2.1)
    (by rw [← hrespEq]; exact hwire.2.2) hqrP
    (by rw [hopP]; exact buildSubQuery_opcode state revealed subQuery₀ hbuild) hsanEq htc hunfollow hcname hsf hcls hnerr hans hemp

theorem delegatingProbeConsumeRound_node
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent resp0 resp : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hcoop : CooperativeNetworkAddr respond w)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hrespEq : respond (Server.ipv4ToAddr ipAddr) sent = resp0)
    (hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (hrt : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode resp0) = .ok resp0)
    (hidP : resp0.header.id = sent.header.id)
    (hqP : resp0.question = sent.question)
    (hqrP : resp0.header.qr = 1)
    (hopP : resp0.header.opcode = sent.header.opcode)
    (hq : sent.question[0]? = some qu)
    (hsanEq : Server.capTtls (Edns.stripOpt resp0) = resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hdeny : Server.strictDenialB resp = false)
    (hpass : Server.probePassableB resp = false)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false)
    (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock + w.tick w.exchCtr →
        w'.exchCtr = w.exchCtr + 1 → w'.tick = w.tick → w'.idCtr = w.idCtr + 2 →
        DescentChain sbelt deadline depth out
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } fuel'
          (Resolver.bumpRevealed state.resources.sname revealed) w') :
    DescentChain sbelt deadline depth out state (fuel' + 1) revealed w := by
  subst hsentEq
  have hwire := oracle_supplies_roundAddr respond
    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (Server.ipv4ToAddr ipAddr) w hcoop hsent
    (by rw [hrespEq]; exact hidP) (by rw [hrespEq]; exact hqP) qu hq
  exact honestProbeConsumeNode sbelt state deadline depth fuel' revealed w entry ipAddr subQuery₀
    resp0 resp out hdl hbest hegress hbuild hprobe
    (by rw [← hrespEq]; exact hwire.1) hrt (by rw [← hrespEq]; exact hwire.2.1)
    (by rw [← hrespEq]; exact hwire.2.2) hqrP
    (by rw [hopP]; exact buildSubQuery_opcode state revealed subQuery₀ hbuild) hsanEq htc hunfollow hdeny hpass hfe hnext




theorem pickBest_isSome_of_acc (acc : Option (SlistEntry × BitVec 32)) (e : SlistEntry)
    (h : acc.isSome = true) : (DnsSList.pickBest acc e).isSome = true := by
  unfold DnsSList.pickBest
  split
  · exact h
  · split
    · rfl
    · split <;> rfl

theorem pickBest_isSome_of_addr (acc : Option (SlistEntry × BitVec 32)) (e : SlistEntry)
    (addr : BitVec 32) (h : e.address = some addr) : (DnsSList.pickBest acc e).isSome = true := by
  unfold DnsSList.pickBest
  rw [h]
  cases acc with
  | none => rfl
  | some p =>
    show (if e.transmissionCount < p.1.transmissionCount then some (e, addr)
      else some (p.1, p.2)).isSome = true
    split <;> rfl

theorem foldl_pickBest_isSome_of_acc : ∀ (l : List SlistEntry)
    (acc : Option (SlistEntry × BitVec 32)), acc.isSome = true →
    (l.foldl DnsSList.pickBest acc).isSome = true := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons e rest ih => intro acc h; exact ih _ (pickBest_isSome_of_acc acc e h)

theorem foldl_pickBest_isSome_of_mem : ∀ (l : List SlistEntry)
    (acc : Option (SlistEntry × BitVec 32)) (e : SlistEntry) (addr : BitVec 32),
    e ∈ l → e.address = some addr → (l.foldl DnsSList.pickBest acc).isSome = true := by
  intro l
  induction l with
  | nil => intro acc e addr hmem _; simp at hmem
  | cons hd rest ih =>
    intro acc e addr hmem haddr
    rcases List.mem_cons.mp hmem with heq | hrest
    · subst heq
      exact foldl_pickBest_isSome_of_acc rest (DnsSList.pickBest acc e)
        (pickBest_isSome_of_addr acc e addr haddr)
    · exact ih (DnsSList.pickBest acc hd) e addr hrest haddr

theorem bestWithAddress_isSome_of_mem (s : DnsSList) (e : SlistEntry) (addr : BitVec 32)
    (hmem : e ∈ s.servers) (haddr : e.address = some addr) :
    s.bestWithAddress.isSome = true := by
  unfold DnsSList.bestWithAddress
  rw [← Array.foldl_toList]
  exact foldl_pickBest_isSome_of_mem s.servers.toList none e addr (Array.mem_def.mp hmem) haddr

theorem foldl_pickBest_mem : ∀ (l : List SlistEntry)
    (acc : Option (SlistEntry × BitVec 32)) (e : SlistEntry) (a : BitVec 32),
    l.foldl DnsSList.pickBest acc = some (e, a) →
    acc = some (e, a) ∨ (e ∈ l ∧ e.address = some a) := by
  intro l
  induction l with
  | nil => intro acc e a h; exact Or.inl h
  | cons hd rest ih =>
    intro acc e a h
    rcases ih (DnsSList.pickBest acc hd) e a h with hstep | ⟨hmem, haddr⟩
    · unfold DnsSList.pickBest at hstep
      cases hhd : hd.address with
      | none => rw [hhd] at hstep; exact Or.inl hstep
      | some addr =>
        rw [hhd] at hstep
        cases acc with
        | none =>
          simp only [] at hstep
          have hp := Option.some.inj hstep
          rw [Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact Or.inr ⟨List.mem_cons_self, hhd⟩
        | some p =>
          simp only [] at hstep
          split at hstep
          · have hp := Option.some.inj hstep
            rw [Prod.mk.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact Or.inr ⟨List.mem_cons_self, hhd⟩
          · have hp := Option.some.inj hstep
            rw [Prod.mk.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact Or.inl rfl
    · exact Or.inr ⟨List.mem_cons_of_mem _ hmem, haddr⟩

theorem bestWithAddress_mem (s : DnsSList) (e : SlistEntry) (a : BitVec 32)
    (h : s.bestWithAddress = some (e, a)) : e ∈ s.servers ∧ e.address = some a := by
  unfold DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  rcases foldl_pickBest_mem s.servers.toList none e a h with hnil | ⟨hmem, haddr⟩
  · simp at hnil
  · exact ⟨Array.mem_def.mpr hmem, haddr⟩

theorem mem_fromNsWithGlueAll_addr_glue
    (names : Array ByteArray) (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (e : SlistEntry) (a : BitVec 32)
    (hmem : e ∈ (DnsSList.fromNsWithGlueAll names glue mc).servers)
    (haddr : e.address = some a) : ∃ gn, (gn, a) ∈ glue := by
  unfold DnsSList.fromNsWithGlueAll at hmem
  rw [Array.mem_flatMap] at hmem
  obtain ⟨n, _hn, he⟩ := hmem
  simp only [] at he
  split at he
  ·
    rw [Array.mem_singleton] at he
    subst he
    simp at haddr
  ·
    rw [Array.mem_map] at he
    obtain ⟨ga, hga, rfl⟩ := he
    have hga' : ga = a := by simpa using haddr
    subst hga'
    rw [Array.mem_filterMap] at hga
    obtain ⟨⟨gn, gv⟩, hgmem, hgif⟩ := hga
    refine ⟨gn, ?_⟩
    by_cases hc : (VeriDNS.Impl.DomainName.foldNameCase gn
        == VeriDNS.Impl.DomainName.foldNameCase n) = true
    · rw [if_pos hc] at hgif
      have : gv = ga := by simpa using hgif
      subst this
      exact hgmem
    · rw [if_neg hc] at hgif
      exact absurd hgif (by simp)

theorem bestWithAddress_isSome_of_glueMatch
    (names : Array ByteArray) (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (n gn : ByteArray) (ga : BitVec 32)
    (hn : n ∈ names) (hg : (gn, ga) ∈ glue)
    (hmatch : (VeriDNS.Impl.DomainName.foldNameCase gn
        == VeriDNS.Impl.DomainName.foldNameCase n) = true) :
    (DnsSList.fromNsWithGlueAll names glue mc).bestWithAddress.isSome = true := by
  have hmemServer : (⟨n, some ga, 0⟩ : SlistEntry)
      ∈ (DnsSList.fromNsWithGlueAll names glue mc).servers := by
    unfold DnsSList.fromNsWithGlueAll
    simp only [Array.mem_flatMap]
    refine ⟨n, hn, ?_⟩
    have hga : ga ∈ glue.filterMap
        (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
          == VeriDNS.Impl.DomainName.foldNameCase n then some x.2 else none) := by
      rw [Array.mem_filterMap]
      exact ⟨(gn, ga), hg, by simp only [hmatch, if_true]⟩
    split
    · rename_i hc
      rw [Array.isEmpty_iff] at hc
      rw [hc] at hga
      simp at hga
    · exact Array.mem_map.mpr ⟨ga, hga, rfl⟩
  exact bestWithAddress_isSome_of_mem _ _ ga hmemServer rfl

theorem bestWithAddress_glueMatch_resolves
    (names : Array ByteArray) (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (n gn0 : ByteArray) (ga0 : BitVec 32)
    (hn : n ∈ names) (hg : (gn0, ga0) ∈ glue)
    (hmatch : (VeriDNS.Impl.DomainName.foldNameCase gn0
        == VeriDNS.Impl.DomainName.foldNameCase n) = true) :
    ∃ (entry : SlistEntry) (ga : BitVec 32) (gn : ByteArray),
      (DnsSList.fromNsWithGlueAll names glue mc).bestWithAddress = some (entry, ga)
      ∧ (gn, ga) ∈ glue := by
  have hsome := bestWithAddress_isSome_of_glueMatch names glue mc n gn0 ga0 hn hg hmatch
  obtain ⟨⟨entry, ga⟩, hbest⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hmem, haddr⟩ := bestWithAddress_mem _ entry ga hbest
  obtain ⟨gn, hgn⟩ := mem_fromNsWithGlueAll_addr_glue names glue mc entry ga hmem haddr
  exact ⟨entry, ga, gn, hbest, hgn⟩

theorem addressTargets_empty_of_allGlued
    (names : Array ByteArray) (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (hall : ∀ n ∈ names, ∃ gn ga, (gn, ga) ∈ glue
        ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
            == VeriDNS.Impl.DomainName.foldNameCase n) = true) :
    (DnsSList.fromNsWithGlueAll names glue mc).addressTargets = #[] := by
  unfold DnsSList.addressTargets DnsSList.fromNsWithGlueAll
  rw [Array.filterMap_eq_empty_iff]
  intro e he
  simp only [Array.mem_flatMap] at he
  obtain ⟨n, hn, hemem⟩ := he
  obtain ⟨gn, ga, hg, hmatch⟩ := hall n hn
  have hga : ga ∈ glue.filterMap
      (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
        == VeriDNS.Impl.DomainName.foldNameCase n then some x.2 else none) := by
    rw [Array.mem_filterMap]
    exact ⟨(gn, ga), hg, by simp only [hmatch, if_true]⟩
  have hne : (glue.filterMap
      (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
        == VeriDNS.Impl.DomainName.foldNameCase n then some x.2 else none)).isEmpty = false :=
    Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨ga, hga⟩
  rw [hne, if_neg (by simp)] at hemem
  obtain ⟨a, _, rfl⟩ := Array.mem_map.mp hemem
  rfl

theorem mem_reGlue_of_served
    (cache : DnsCache) (now : UInt32) (nsNames : Array ByteArray)
    (nsName : ByteArray) (rr : VeriDNS.Spec.ResourceRecord)
    (hn : nsName ∈ nsNames)
    (hserved : rr ∈ cache.lookupTopCred nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4)
        = true) :
    ∃ ga, (nsName, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        cache now nsNames := by
  unfold VeriDNS.Proof.Refinement.reGlue
  exact ⟨_, Array.mem_flatMap.mpr ⟨nsName, hn,
    Array.mem_filterMap.mpr ⟨rr, hserved, if_pos hsize⟩⟩⟩

theorem lookupTopCred_serves_glue (c : DnsCache) (nsName : ByteArray) (now : UInt32)
    (e : CacheEntry) (he : e ∈ c.records)
    (hlive : liveEntry e nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now = true)
    (hrank : c.maxRankForKey e now = true)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) e.rr).size == 4)
        = true) :
    ∃ rr, rr ∈ c.lookupTopCred nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true := by
  refine ⟨{ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }, ?_, hsize⟩
  rw [DnsCache.lookupTopCred, Array.mem_filterMap]
  exact ⟨e, he, by rw [hlive, hrank]; rfl⟩

theorem storeChecked_pushed_live_maxrank
    (c : DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (hnz : (rr.ttl == 0) = false)
    (hfresh : now + rr.ttl.toNat.toUInt32 > now)
    (hnb : (c.records.any fun e =>
        DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
          && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
          && e.credibility.toCode < cred.toCode) = false) :
    ∃ e ∈ (c.storeChecked rr cred now).records,
      liveEntry e rr.name rr.type rr.class now = true ∧
      (c.storeChecked rr cred now).maxRankForKey e now = true := by
  obtain ⟨e0, hmem, hrr, hexp, hcred⟩ := VeriDNS.Proof.Cache.mem_storeChecked_pushed c rr cred now hnz hnb
  have hSC : c.storeChecked rr cred now = c.store rr now cred := by
    unfold DnsCache.storeChecked
    simp only [hnz, hnb, Bool.false_eq_true, if_false]
  refine ⟨e0, hmem, ?_, ?_⟩
  ·
    unfold liveEntry CacheEntry.fresh
    rw [hrr, hexp]
    simp only [VeriDNS.Impl.Cache.nameEqCI_refl, beq_self_eq_true, Bool.and_true, Bool.true_and,
      decide_eq_true_eq]
    exact hfresh
  ·
    unfold DnsCache.maxRankForKey
    rw [Array.all_eq_true_iff_forall_mem]
    intro e2 he2
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hrival : (e2.fresh now && sameRRKey e2 e0) = true
    · right
      simp only [Bool.and_eq_true] at hrival
      obtain ⟨hfr, hsk⟩ := hrival
      rw [sameRRKey, hrr] at hsk
      simp only [Bool.and_eq_true] at hsk
      obtain ⟨⟨hnm, htp⟩, hcl⟩ := hsk
      have he2c : e2 ∈ c.records ∨ e2 = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
        rw [hSC] at he2
        unfold DnsCache.store at he2
        rcases Array.mem_push.mp he2 with hf | hp
        · exact Or.inl (Array.mem_filter.mp hf).1
        · exact Or.inr hp
      rcases he2c with hinc | hpush
      ·
        have hP : (DomainName.nameEqCI e2.rr.name rr.name && e2.rr.type == rr.type
            && e2.rr.class == rr.class
            && (e2.expiry > now || e2.expiry == now + rr.ttl.toNat.toUInt32)
            && e2.credibility.toCode < cred.toCode) = false := by
          by_contra h
          rw [Bool.not_eq_false] at h
          have hany : (c.records.any fun e =>
              DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
                && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
                && e.credibility.toCode < cred.toCode) = true := by
            rw [Array.any_eq_true]
            obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hinc
            exact ⟨i, hi, h⟩
          rw [hany] at hnb; exact absurd hnb (by decide)
        have hexpfr : (e2.expiry > now || e2.expiry == now + rr.ttl.toNat.toUInt32) = true := by
          rw [CacheEntry.fresh] at hfr; rw [hfr, Bool.true_or]
        rw [hnm, htp, hcl, hexpfr] at hP
        simp only [Bool.and_true, Bool.true_and] at hP
        rw [hcred, decide_eq_true_eq]
        exact Nat.le_of_not_lt (of_decide_eq_false hP)
      ·
        rw [hcred, hpush, decide_eq_true_eq]
        exact Nat.le_refl _
    · left
      simp only [Bool.not_eq_true] at hrival
      exact hrival



theorem mem_store_inv (c : DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : Trustworthiness) (e : CacheEntry)
    (he : e ∈ (c.store rr now cred).records) :
    e ∈ c.records ∨ e = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  unfold DnsCache.store at he
  rcases Array.mem_push.mp he with hf | hp
  · exact Or.inl (Array.mem_filter.mp hf).1
  · exact Or.inr hp

theorem mem_storeChecked_inv (c : DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) (e : CacheEntry)
    (he : e ∈ (c.storeChecked rr cred now).records) :
    e ∈ c.records ∨ e = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  simp only [DnsCache.storeChecked] at he
  split at he
  · exact Or.inl he
  · split at he
    · exact Or.inl he
    · exact mem_store_inv c rr now cred e he

theorem mem_cacheRRs_inv (c : DnsCache) (raws : Array ByteArray) (cred : Trustworthiness)
    (now : UInt32) :
    ∀ e ∈ (Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now).records,
      e ∈ c.records ∨ ∃ b ∈ raws, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ e = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  unfold Resolver.cacheRRs
  refine Array.foldl_induction
    (motive := fun _ (acc : DnsCache) => ∀ e ∈ acc.records,
      e ∈ c.records ∨ ∃ b ∈ raws, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ e = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩)
    (fun e he => Or.inl he) ?_
  intro i acc ih e he
  cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raws[i] with
  | none =>
    simp only [hp] at he
    exact ih e he
  | some rr =>
    simp only [hp] at he
    rcases mem_storeChecked_inv acc rr cred now e he with hin | hpush
    · exact ih e hin
    · exact Or.inr ⟨raws[i], Array.getElem_mem i.isLt, rr, hp, hpush⟩

theorem mem_lookupTopCred_inv (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred name qt qc now) :
    ∃ e ∈ c.records, liveEntry e name qt qc now = true
      ∧ rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  rw [DnsCache.lookupTopCred, Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    rw [Option.some.injEq] at hsome
    exact ⟨e, he, hcond.1, hsome.symm⟩
  · exact absurd hsome (by simp)

theorem cacheRRs_singleton (c : DnsCache) (b : ByteArray) (cred : Trustworthiness) (now : UInt32) :
    Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c #[b] cred now
      = match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
        | some rr => c.storeChecked rr cred now
        | none => c := by
  unfold Resolver.cacheRRs
  rw [← Array.foldl_toList]
  simp only [List.foldl_cons, List.foldl_nil]
  cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl

theorem referralWrite_nsKey_facts
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32) (sname : ByteArray)
    (nsRaw : ByteArray) (nsrr : VeriDNS.Spec.ResourceRecord)
    (htc : (resp.header.tc == 1) = false)
    (hauthN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) authRaws
        = #[nsRaw])
    (hpns : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsrr)
    (hnsName : DomainName.nameEqCI nsrr.name sname = true)
    (hnsType : nsrr.type = BitVec.ofNat 16 2)
    (hnsClass : nsrr.class = BitVec.ofNat 16 1)
    (hnz : (nsrr.ttl == 0) = false)
    (hfresh : now + nsrr.ttl.toNat.toUInt32 > now)
    (haddT : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 2) = false)
    (hnone : ∀ e ∈ c.records,
        (DomainName.nameEqCI e.rr.name sname
          && e.rr.type == BitVec.ofNat 16 2 && e.rr.class == BitVec.ofNat 16 1) = false) :
    ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
        resp addRaws credD now).lookupTopCred
          sname (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = false
    ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr
        ∈ ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
            resp addRaws credD now).lookupTopCred
              sname (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
            (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
                == BitVec.ofNat 16 2
              then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
              else none)
    ∧ ∀ n ∈ ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
            resp addRaws credD now).lookupTopCred
              sname (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
            (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
                == BitVec.ofNat 16 2
              then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
              else none),
        n = VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr := by
  have hw : Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
      resp addRaws credD now
      = Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (c.storeChecked nsrr credA now)
          (VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws)
          credD now := by
    unfold Resolver.cacheUnlessTruncated
    simp only [htc, Bool.false_eq_true, if_false]
    rw [hauthN, cacheRRs_singleton, hpns]
  rw [hw]
  have hnb : (c.records.any fun e =>
      DomainName.nameEqCI e.rr.name nsrr.name && e.rr.type == nsrr.type && e.rr.class == nsrr.class
        && (e.expiry > now || e.expiry == now + nsrr.ttl.toNat.toUInt32)
        && e.credibility.toCode < credA.toCode) = false := by
    by_contra hx
    rw [Bool.not_eq_false, Array.any_eq_true] at hx
    obtain ⟨i, hi, hP⟩ := hx
    simp only [Bool.and_eq_true] at hP
    obtain ⟨⟨⟨⟨hnm, htp⟩, hcl⟩, _⟩, _⟩ := hP
    have h2 : (c.records[i].rr.type == BitVec.ofNat 16 2) = true := by
      rw [← hnsType]; exact htp
    have h1 : (c.records[i].rr.class == BitVec.ofNat 16 1) = true := by
      rw [← hnsClass]; exact hcl
    have hnm' : DomainName.nameEqCI c.records[i].rr.name sname = true :=
      VeriDNS.Proof.NameTree.nameEqCI_trans hnm hnsName
    have hcontra := hnone c.records[i] (Array.getElem_mem hi)
    rw [hnm', h2, h1] at hcontra
    exact absurd hcontra (by decide)
  obtain ⟨e0, he0, hrr0, hexp0, hcred0⟩ :=
    VeriDNS.Proof.Cache.mem_storeChecked_pushed c nsrr credA now hnz hnb
  have hlive0 : liveEntry e0 sname (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now = true := by
    unfold liveEntry CacheEntry.fresh
    rw [hrr0, hexp0, hnsType, hnsClass]
    simp only [hnsName, beq_self_eq_true, Bool.and_true, Bool.true_and, decide_eq_true_eq]
    exact hfresh
  have hkeep : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws,
      ∀ rr', VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr' →
      (DomainName.nameEqCI e0.rr.name rr'.name && e0.rr.type == rr'.type
        && e0.rr.class == rr'.class
        && (e0.expiry != now + rr'.ttl.toNat.toUInt32
            || rdataEqCI rr'.type e0.rr.rdata rr'.rdata)) = false := by
    intro b hb rr' hp'
    have h2 : (e0.rr.type == rr'.type) = false := by
      rw [hrr0, hnsType, beq_eq_false_iff_ne]
      exact fun h => (beq_eq_false_iff_ne.mp (haddT b hb rr' hp')) h.symm
    simp only [h2, Bool.and_false, Bool.false_and]
  have he0post : e0 ∈ (Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      (c.storeChecked nsrr credA now)
      (VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws)
      credD now).records :=
    VeriDNS.Proof.Cache.mem_cacheRRs_preserve _ _ credD now e0 he0 hkeep
  have hrank0 : (Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      (c.storeChecked nsrr credA now)
      (VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws)
      credD now).maxRankForKey e0 now = true := by
    unfold DnsCache.maxRankForKey
    rw [Array.all_eq_true_iff_forall_mem]
    intro e2 he2
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hrival : (e2.fresh now && sameRRKey e2 e0) = true
    · right
      simp only [Bool.and_eq_true] at hrival
      obtain ⟨_hfr, hsk⟩ := hrival
      rw [sameRRKey, hrr0] at hsk
      simp only [Bool.and_eq_true] at hsk
      obtain ⟨⟨hnm, htp⟩, hcl⟩ := hsk
      rcases mem_cacheRRs_inv _ _ credD now e2 he2 with h1 | ⟨b, hb, rr', hp', hpush⟩
      · rcases mem_storeChecked_inv c nsrr credA now e2 h1 with hc | hpush
        ·
          have h2t : (e2.rr.type == BitVec.ofNat 16 2) = true := by rw [← hnsType]; exact htp
          have h2c : (e2.rr.class == BitVec.ofNat 16 1) = true := by rw [← hnsClass]; exact hcl
          have hnm' : DomainName.nameEqCI e2.rr.name sname = true :=
            VeriDNS.Proof.NameTree.nameEqCI_trans hnm hnsName
          have hcontra := hnone e2 hc
          rw [hnm', h2t, h2c] at hcontra
          exact absurd hcontra (by decide)
        ·
          rw [hcred0, hpush, decide_eq_true_eq]
          exact Nat.le_refl _
      ·
        have h2t : (e2.rr.type == BitVec.ofNat 16 2) = true := by rw [← hnsType]; exact htp
        have herr : e2.rr = rr' := by rw [hpush]
        rw [herr, haddT b hb rr' hp'] at h2t
        exact absurd h2t (by decide)
    · left
      simp only [Bool.not_eq_true] at hrival
      exact hrival
  refine ⟨VeriDNS.Proof.Cache.lookupTopCred_ne_of_mem _ sname _ _ now e0 he0post hlive0 hrank0,
    ?_, ?_⟩
  · rw [Array.mem_filterMap]
    refine ⟨{ e0.rr with ttl := BitVec.ofNat 32 (e0.expiry - now).toNat }, ?_, ?_⟩
    · rw [DnsCache.lookupTopCred, Array.mem_filterMap]
      exact ⟨e0, he0post, by rw [hlive0, hrank0]; rfl⟩
    · have ht : VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord)
          ({ e0.rr with ttl := BitVec.ofNat 32 (e0.expiry - now).toNat }) = BitVec.ofNat 16 2 := by
        show e0.rr.type = BitVec.ofNat 16 2
        rw [hrr0, hnsType]
      rw [ht, if_pos (by decide)]
      show some e0.rr.rdata = some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr)
      rw [hrr0]
      rfl
  · intro n hn
    rw [Array.mem_filterMap] at hn
    obtain ⟨rr, hrrmem, hsome⟩ := hn
    have hval : n = VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr := by
      split at hsome
      · rw [Option.some.injEq] at hsome; exact hsome.symm
      · exact absurd hsome (by simp)
    obtain ⟨e, he, hlv, hreq⟩ := mem_lookupTopCred_inv _ sname _ _ now rr hrrmem
    unfold liveEntry at hlv
    simp only [Bool.and_eq_true] at hlv
    obtain ⟨⟨⟨hnm, htp⟩, hcl⟩, _hfr⟩ := hlv
    rcases mem_cacheRRs_inv _ _ credD now e he with h1 | ⟨b, hb, rr', hp', hpush⟩
    · rcases mem_storeChecked_inv c nsrr credA now e h1 with hc | hpush
      ·
        have hcontra := hnone e hc
        rw [hnm, htp, hcl] at hcontra
        exact absurd hcontra (by decide)
      ·
        have herr : e.rr = nsrr := by rw [hpush]
        rw [hval, hreq]
        show ({ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
            : VeriDNS.Spec.ResourceRecord).rdata
          = VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr
        rw [herr]
        rfl
    ·
      have herr : e.rr = rr' := by rw [hpush]
      rw [herr, haddT b hb rr' hp'] at htp
      exact absurd htp (by decide)



theorem liveEntry_touchEntry (ks : Array RRKey) (now' now : UInt32) (e : CacheEntry)
    (name : ByteArray) (qt qc : BitVec 16) :
    liveEntry (touchEntry ks now' e) name qt qc now = liveEntry e name qt qc now := by
  unfold touchEntry; split <;> rfl

theorem maxRankForKey_touchKeys (c : DnsCache) (ks : Array RRKey) (now' now : UInt32)
    (e : CacheEntry) :
    (c.touchKeys ks now').maxRankForKey (touchEntry ks now' e) now = c.maxRankForKey e now := by
  unfold DnsCache.maxRankForKey
  rw [touchKeys_records, Array.all_map]
  congr 1
  funext e2
  simp only [Function.comp]
  rcases touchEntry_cases ks now' e with he | he
    <;> rcases touchEntry_cases ks now' e2 with h2 | h2 <;> rw [he, h2] <;> rfl

theorem lookupTopCred_touchKeys (c : DnsCache) (ks : Array RRKey) (name : ByteArray)
    (qt qc : BitVec 16) (now' now : UInt32) :
    (c.touchKeys ks now').lookupTopCred name qt qc now = c.lookupTopCred name qt qc now := by
  unfold DnsCache.lookupTopCred
  rw [touchKeys_records, Array.filterMap_map]
  congr 1
  funext e2
  simp only [Function.comp, liveEntry_touchEntry, maxRankForKey_touchKeys, touchEntry_rr,
    touchEntry_expiry]

theorem lookupTopCred_boundLru_serves_glue (c : DnsCache) (touches : Array RRKey)
    (nsName : ByteArray) (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (hcap : c.records.size ≤ DnsCache.capacity)
    (hserved : rr ∈ c.lookupTopCred nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4)
        = true) :
    ∃ rr', rr' ∈ (c.boundLru touches now).lookupTopCred nsName (BitVec.ofNat 16 1)
        (BitVec.ofNat 16 1) now
      ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr').size == 4)
        = true := by
  refine ⟨rr, ?_, hsize⟩
  unfold DnsCache.boundLru
  rw [VeriDNS.Proof.Cache.boundLruKeys_noop _ (by rw [touchKeys_records, Array.size_map]; exact hcap),
      lookupTopCred_touchKeys]
  exact hserved




def NoBetterGlue (c : DnsCache) (grr : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness)
    (now : UInt32) : Prop :=
  ∀ e2 ∈ c.records, e2.fresh now = true → DomainName.nameEqCI e2.rr.name grr.name = true →
    (e2.rr.type == grr.type) = true → (e2.rr.class == grr.class) = true →
    cred.toCode ≤ e2.credibility.toCode

def ServesGlue (c : DnsCache) (grr : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness)
    (now : UInt32) : Prop :=
  ∃ e ∈ c.records, DomainName.nameEqCI e.rr.name grr.name = true ∧ (e.rr.type == grr.type) = true
    ∧ (e.rr.class == grr.class) = true ∧ e.fresh now = true ∧ e.credibility = cred
    ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) e.rr).size == 4) = true

theorem noBetterGlue_storeChecked (c : DnsCache) (rr grr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32)
    (h : NoBetterGlue c grr cred now) :
    NoBetterGlue (c.storeChecked rr cred now) grr cred now := by
  intro e2 he2 hfr hnm htp hcl
  simp only [DnsCache.storeChecked] at he2
  split at he2
  · exact h e2 he2 hfr hnm htp hcl
  · split at he2
    · exact h e2 he2 hfr hnm htp hcl
    · unfold DnsCache.store at he2
      rcases Array.mem_push.mp he2 with hf | hp
      · exact h e2 (Array.mem_filter.mp hf).1 hfr hnm htp hcl
      ·
        rw [hp]; exact Nat.le_refl _

theorem servesGlue_storeChecked_preserve (c : DnsCache) (rr grr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32)
    (hgood : DomainName.nameEqCI rr.name grr.name = true → (rr.type == grr.type) = true →
        (rr.class == grr.class) = true →
        (now + rr.ttl.toNat.toUInt32 > now)
          ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true)
    (h : ServesGlue c grr cred now) :
    ServesGlue (c.storeChecked rr cred now) grr cred now := by
  obtain ⟨e, he, hnm, htp, hcl, hfr, hcred, hsz⟩ := h
  simp only [DnsCache.storeChecked]
  split
  · exact ⟨e, he, hnm, htp, hcl, hfr, hcred, hsz⟩
  · split
    · exact ⟨e, he, hnm, htp, hcl, hfr, hcred, hsz⟩
    · by_cases hkill : (DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type
          && e.rr.class == rr.class
          && (e.expiry != now + rr.ttl.toNat.toUInt32 || rdataEqCI rr.type e.rr.rdata rr.rdata)) = true
      ·
        simp only [Bool.and_eq_true] at hkill
        obtain ⟨⟨⟨hkn, hkt⟩, hkc⟩, _⟩ := hkill
        have hrn : DomainName.nameEqCI rr.name grr.name = true :=
          VeriDNS.Proof.NameTree.nameEqCI_trans (VeriDNS.Proof.NameTree.nameEqCI_symm hkn) hnm
        have hrt : (rr.type == grr.type) = true := by
          rw [beq_iff_eq] at hkt htp ⊢; rw [← hkt]; exact htp
        have hrc : (rr.class == grr.class) = true := by
          rw [beq_iff_eq] at hkc hcl ⊢; rw [← hkc]; exact hcl
        obtain ⟨hgfr, hgsz⟩ := hgood hrn hrt hrc
        refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩,
          Array.mem_push.mpr (Or.inr rfl), hrn, hrt, hrc, ?_, rfl, hgsz⟩
        simp only [CacheEntry.fresh, decide_eq_true_eq]; exact hgfr
      ·
        refine ⟨e, ?_, hnm, htp, hcl, hfr, hcred, hsz⟩
        unfold DnsCache.store
        refine Array.mem_push.mpr (Or.inl (Array.mem_filter.mpr ⟨he, ?_⟩))
        rw [Bool.not_eq_true] at hkill; rw [hkill]; rfl

theorem noBetterGlue_betterExists_false (c : DnsCache) (grr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32)
    (hfresh : now + grr.ttl.toNat.toUInt32 > now)
    (hnb : NoBetterGlue c grr cred now) :
    (c.records.any fun e =>
        DomainName.nameEqCI e.rr.name grr.name && e.rr.type == grr.type && e.rr.class == grr.class
          && (e.expiry > now || e.expiry == now + grr.ttl.toNat.toUInt32)
          && e.credibility.toCode < cred.toCode) = false := by
  rw [Bool.eq_false_iff, Ne, Array.any_eq_true]
  rintro ⟨i, hi, hp⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨hnm, htp⟩, hcl⟩, hexp⟩, hlt⟩ := hp
  have hfr : c.records[i].fresh now = true := by
    simp only [CacheEntry.fresh, decide_eq_true_eq]
    rw [Bool.or_eq_true] at hexp
    rcases hexp with h | h
    · exact of_decide_eq_true h
    · rw [beq_iff_eq] at h; rw [h]; exact hfresh
  exact absurd (hnb c.records[i] (Array.getElem_mem hi) hfr hnm htp hcl) (Nat.not_le.mpr hlt)


theorem lookupTopCred_cacheRRs_serves_glue
    (c : DnsCache) (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32)
    (grr : VeriDNS.Spec.ResourceRecord) (b : ByteArray)
    (hb : b ∈ raws)
    (hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some grr)
    (hnz : (grr.ttl == 0) = false)
    (htype : grr.type = BitVec.ofNat 16 1)
    (hclass : grr.class = BitVec.ofNat 16 1)
    (hfresh : now + grr.ttl.toNat.toUInt32 > now)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr).size == 4) = true)
    (hnb0 : NoBetterGlue c grr cred now)
    (hexp : ∀ b' ∈ raws, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b'
        = some rr → DomainName.nameEqCI rr.name grr.name = true → (rr.type == grr.type) = true →
        (rr.class == grr.class) = true →
        (now + rr.ttl.toNat.toUInt32 > now)
          ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true) :
    ∃ rr', rr' ∈ (Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now).lookupTopCred
        grr.name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr').size == 4) = true := by
  obtain ⟨idx, hidx, hib⟩ := Array.getElem_of_mem hb
  have hfold : NoBetterGlue (Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now) grr cred now
      ∧ (idx < raws.size → ServesGlue (Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now) grr cred now) := by
    unfold Resolver.cacheRRs
    refine Array.foldl_induction
      (motive := fun j acc => NoBetterGlue acc grr cred now ∧ (idx < j → ServesGlue acc grr cred now))
      ⟨hnb0, fun h => absurd h (Nat.not_lt_zero _)⟩ ?_
    rintro i acc ⟨hNB, hSv⟩
    cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raws[i] with
    | none =>
      refine ⟨hNB, fun hlt => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      · exact hSv hlt'
      · exfalso
        have hib' : raws[i] = b := by subst heq; exact hib
        have hpi : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raws[i]
            = some grr := by rw [hib']; exact hpb
        rw [hp] at hpi; simp at hpi
    | some rr =>
      refine ⟨noBetterGlue_storeChecked acc rr grr cred now hNB, fun hlt => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      ·
        exact servesGlue_storeChecked_preserve acc rr grr cred now
          (fun hn ht hc => hexp raws[i] (Array.getElem_mem i.isLt) rr hp hn ht hc) (hSv hlt')
      ·
        have hib' : raws[i] = b := by subst heq; exact hib
        have hpi : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raws[i]
            = some grr := by rw [hib']; exact hpb
        rw [hp] at hpi
        have hrg : rr = grr := Option.some.inj hpi
        subst hrg
        obtain ⟨e0, hmem, hrreq, hexpeq, hcredeq⟩ :=
          VeriDNS.Proof.Cache.mem_storeChecked_pushed acc rr cred now hnz
            (noBetterGlue_betterExists_false acc rr cred now hfresh hNB)
        refine ⟨e0, hmem, ?_, ?_, ?_, ?_, hcredeq, ?_⟩
        · rw [hrreq]; exact VeriDNS.Impl.Cache.nameEqCI_refl _
        · rw [hrreq]; exact beq_self_eq_true _
        · rw [hrreq]; exact beq_self_eq_true _
        · simp only [CacheEntry.fresh, decide_eq_true_eq, hexpeq]; exact hfresh
        · rw [hrreq]; exact hsize
  obtain ⟨hNBfin, hSvfin⟩ := hfold
  generalize hcf : Resolver.cacheRRs (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now = cf at hNBfin hSvfin ⊢
  obtain ⟨e, he, hnm, htp, hcl, hfr, hcred, hsz⟩ := hSvfin hidx
  have hlive : liveEntry e grr.name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now = true := by
    unfold liveEntry
    rw [hnm, hfr]
    have h1 : (e.rr.type == BitVec.ofNat 16 1) = true := by rw [beq_iff_eq] at htp ⊢; rw [htp, htype]
    have h2 : (e.rr.class == BitVec.ofNat 16 1) = true := by rw [beq_iff_eq] at hcl ⊢; rw [hcl, hclass]
    rw [h1, h2]; rfl
  have hrank : cf.maxRankForKey e now = true := by
    unfold DnsCache.maxRankForKey
    rw [Array.all_eq_true_iff_forall_mem]
    intro e2 he2
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hriv : (e2.fresh now && sameRRKey e2 e) = true
    · right
      simp only [Bool.and_eq_true] at hriv
      obtain ⟨hf2, hsk⟩ := hriv
      rw [sameRRKey, Bool.and_eq_true, Bool.and_eq_true] at hsk
      obtain ⟨⟨hnm2, htp2⟩, hcl2⟩ := hsk
      have hn2 : DomainName.nameEqCI e2.rr.name grr.name = true :=
        VeriDNS.Proof.NameTree.nameEqCI_trans hnm2 hnm
      have ht2 : (e2.rr.type == grr.type) = true := by
        rw [beq_iff_eq] at htp2 htp ⊢; rw [htp2, htp]
      have hc2 : (e2.rr.class == grr.class) = true := by
        rw [beq_iff_eq] at hcl2 hcl ⊢; rw [hcl2, hcl]
      rw [decide_eq_true_eq, hcred]
      exact hNBfin e2 he2 hf2 hn2 ht2 hc2
    · left; rwa [Bool.not_eq_true] at hriv
  exact lookupTopCred_serves_glue cf grr.name now e he hlive hrank hsz

theorem lookupTopCred_cacheUnlessTruncated_serves_glue
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (raws : Array ByteArray) (cred : Trustworthiness)
    (now : UInt32) (grr : VeriDNS.Spec.ResourceRecord) (b : ByteArray)
    (htc : (resp.header.tc == 1) = false)
    (hb : b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws)
    (hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some grr)
    (hnz : (grr.ttl == 0) = false)
    (htype : grr.type = BitVec.ofNat 16 1) (hclass : grr.class = BitVec.ofNat 16 1)
    (hfresh : now + grr.ttl.toNat.toUInt32 > now)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr).size == 4) = true)
    (hnb0 : NoBetterGlue c grr cred now)
    (hexp : ∀ b' ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
        DomainName.nameEqCI rr.name grr.name = true → (rr.type == grr.type) = true →
        (rr.class == grr.class) = true →
        (now + rr.ttl.toNat.toUInt32 > now)
          ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true) :
    ∃ rr', rr' ∈ (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now).lookupTopCred grr.name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr').size == 4) = true := by
  unfold Resolver.cacheUnlessTruncated
  simp only [htc, Bool.false_eq_true, if_false]
  exact lookupTopCred_cacheRRs_serves_glue c _ cred now grr b hb hpb hnz htype hclass hfresh hsize
    hnb0 hexp

theorem lookupTopCred_nameEqCI (c : DnsCache) (n1 n2 : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (h : DomainName.nameEqCI n1 n2 = true) :
    c.lookupTopCred n1 qt qc now = c.lookupTopCred n2 qt qc now := by
  unfold DnsCache.lookupTopCred
  congr 1
  funext e
  have hname : DomainName.nameEqCI e.rr.name n1 = DomainName.nameEqCI e.rr.name n2 := by
    cases h1 : DomainName.nameEqCI e.rr.name n1 <;> cases h2 : DomainName.nameEqCI e.rr.name n2 <;>
      first
        | rfl
        | (rw [VeriDNS.Proof.NameTree.nameEqCI_trans h1 h] at h2; exact absurd h2 (by decide))
        | (rw [VeriDNS.Proof.NameTree.nameEqCI_trans h2
              (VeriDNS.Proof.NameTree.nameEqCI_symm h)] at h1; exact absurd h1 (by decide))
  simp only [liveEntry, hname]

theorem reGlue_of_referral_glue
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (raws : Array ByteArray) (cred : Trustworthiness)
    (now : UInt32) (touches : Array RRKey) (nsNames : Array ByteArray)
    (grr : VeriDNS.Spec.ResourceRecord) (b : ByteArray) (nsName : ByteArray)
    (hnsMem : nsName ∈ nsNames)
    (hkey : DomainName.nameEqCI grr.name nsName = true)
    (htc : (resp.header.tc == 1) = false)
    (hb : b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws)
    (hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some grr)
    (hnz : (grr.ttl == 0) = false)
    (htype : grr.type = BitVec.ofNat 16 1) (hclass : grr.class = BitVec.ofNat 16 1)
    (hfresh : now + grr.ttl.toNat.toUInt32 > now)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr).size == 4) = true)
    (hnb0 : NoBetterGlue c grr cred now)
    (hexp : ∀ b' ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
        DomainName.nameEqCI rr.name grr.name = true → (rr.type == grr.type) = true →
        (rr.class == grr.class) = true →
        (now + rr.ttl.toNat.toUInt32 > now)
          ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true)
    (hcap : (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now).records.size ≤ DnsCache.capacity) :
    ∃ ga, (nsName, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        ((Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp raws cred now).boundLru touches now) now nsNames := by
  obtain ⟨rr0, hrr0, hsz0⟩ := lookupTopCred_cacheUnlessTruncated_serves_glue c resp raws cred now grr b
    htc hb hpb hnz htype hclass hfresh hsize hnb0 hexp
  have hkeyName : (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c resp raws cred now).lookupTopCred grr.name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      = (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp raws cred now).lookupTopCred nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now :=
    lookupTopCred_nameEqCI _ _ _ _ _ _ hkey
  rw [hkeyName] at hrr0
  obtain ⟨rr1, hrr1, hsz1⟩ := lookupTopCred_boundLru_serves_glue _ touches nsName now rr0 hcap hrr0 hsz0
  exact mem_reGlue_of_served _ now nsNames nsName rr1 hnsMem hrr1 hsz1

theorem reGlue_preBoundLru_of_referral_glue
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (raws : Array ByteArray) (cred : Trustworthiness)
    (now : UInt32) (nsNames : Array ByteArray)
    (grr : VeriDNS.Spec.ResourceRecord) (b : ByteArray) (nsName : ByteArray)
    (hnsMem : nsName ∈ nsNames)
    (hkey : DomainName.nameEqCI grr.name nsName = true)
    (htc : (resp.header.tc == 1) = false)
    (hb : b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws)
    (hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some grr)
    (hnz : (grr.ttl == 0) = false)
    (htype : grr.type = BitVec.ofNat 16 1) (hclass : grr.class = BitVec.ofNat 16 1)
    (hfresh : now + grr.ttl.toNat.toUInt32 > now)
    (hsize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr).size == 4) = true)
    (hnb0 : NoBetterGlue c grr cred now)
    (hexp : ∀ b' ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
        DomainName.nameEqCI rr.name grr.name = true → (rr.type == grr.type) = true →
        (rr.class == grr.class) = true →
        (now + rr.ttl.toNat.toUInt32 > now)
          ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true) :
    ∃ ga, (nsName, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp raws cred now) now nsNames := by
  obtain ⟨rr0, hrr0, hsz0⟩ := lookupTopCred_cacheUnlessTruncated_serves_glue c resp raws cred now grr b
    htc hb hpb hnz htype hclass hfresh hsize hnb0 hexp
  have hkeyName : (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c resp raws cred now).lookupTopCred grr.name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      = (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          c resp raws cred now).lookupTopCred nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now :=
    lookupTopCred_nameEqCI _ _ _ _ _ _ hkey
  rw [hkeyName] at hrr0
  exact mem_reGlue_of_served _ now nsNames nsName rr0 hnsMem hrr0 hsz0

theorem bestWithAddress_reGlue_resolves
    (cache : DnsCache) (now : UInt32) (nsNames : Array ByteArray) (mc : Nat)
    (nsName : ByteArray) (ga0 : BitVec 32)
    (hn : nsName ∈ nsNames)
    (hg : (nsName, ga0) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        cache now nsNames) :
    ∃ (entry : SlistEntry) (ga : BitVec 32) (gn : ByteArray),
      (DnsSList.fromNsWithGlueAll nsNames
          (VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
            cache now nsNames) mc).bestWithAddress = some (entry, ga)
      ∧ (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
          cache now nsNames :=
  bestWithAddress_glueMatch_resolves nsNames
    (VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now nsNames) mc
    nsName nsName ga0 hn hg (VeriDNS.Impl.Cache.byteArray_beq_refl _)

theorem branch2_childSlist_resolves
    (sl : DnsSList) (cache : DnsCache) (now : UInt32) (nsNames : Array ByteArray) (mc : Nat)
    (nsName : ByteArray) (ga0 : BitVec 32)
    (hsl : sl = DnsSList.fromNsWithGlueAll nsNames
        (VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now nsNames) mc)
    (hnsMem : nsName ∈ nsNames)
    (hg : (nsName, ga0) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        cache now nsNames)
    (hall : ∀ n ∈ nsNames, ∃ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue
        (RR := VeriDNS.Spec.ResourceRecord) cache now nsNames
        ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
            == VeriDNS.Impl.DomainName.foldNameCase n) = true) :
    (∃ (entry : SlistEntry) (ga : BitVec 32), sl.bestWithAddress = some (entry, ga))
      ∧ sl.addressTargets[0]? = none := by
  subst hsl
  refine ⟨?_, ?_⟩
  · obtain ⟨entry, ga, _, hbest, _⟩ :=
      bestWithAddress_reGlue_resolves cache now nsNames mc nsName ga0 hnsMem hg
    exact ⟨entry, ga, hbest⟩
  · rw [addressTargets_empty_of_allGlued nsNames _ mc hall]; rfl

theorem cooperativeReferral_continue_terminalFacts
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (nsNames : Array ByteArray) (mc : Nat) (postCache : DnsCache)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (revealed : Nat)
    (nsName : ByteArray) (ga0 : BitVec 32)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hpc : postCache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
        postCache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := DnsSList) (NS := SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false)
    (hnb : ((VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames).isEmpty
        && (mc == 0)) = false)
    (hnsMem : nsName ∈ nsNames)
    (hg : (nsName, ga0) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        postCache state.now nsNames)
    (hall : ∀ n ∈ nsNames, ∃ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue
        (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames
        ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
            == VeriDNS.Impl.DomainName.foldNameCase n) = true)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hcanon : CanonicalName state.resources.sname) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.currentStep = .sendQueries
      ∧ CanonicalName st.resources.sname
      ∧ (∃ sq, Resolver.buildSubQuery st revealed = some sq)
      ∧ (∃ entry ga, st.resources.slist.bestWithAddress = some (entry, ga))
      ∧ st.resources.slist.addressTargets[0]? = none := by
  subst hpc
  obtain ⟨st, hcont, hsl, hsn, _hnw, _hcc, hcs, hlqst⟩ :=
    VeriDNS.Proof.Refinement.afterResume_referral_continue_slist state entryName resp nsNames mc
      hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa hwalk hclose hnb
  refine ⟨st, hcont, hcs, by rw [hsn]; exact hcanon, ?_, ?_, ?_⟩
  · have hbq : (Resolver.buildSubQuery st revealed).isSome = true := by
      simp only [Resolver.buildSubQuery, hlqst, hlq, hqu, Option.isSome_some]
    exact Option.isSome_iff_exists.mp hbq
  · exact (branch2_childSlist_resolves st.resources.slist _ state.now nsNames mc nsName ga0
      hsl hnsMem hg hall).1
  · exact (branch2_childSlist_resolves st.resources.slist _ state.now nsNames mc nsName ga0
      hsl hnsMem hg hall).2

theorem cooperativeReferral_continue_terminalFacts_exact
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (nsNames : Array ByteArray) (mc : Nat) (postCache : DnsCache)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (revealed : Nat)
    (nsName : ByteArray) (ga0 : BitVec 32)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hpc : postCache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
        postCache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := DnsSList) (NS := SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false)
    (hnb : ((VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames).isEmpty
        && (mc == 0)) = false)
    (hnsMem : nsName ∈ nsNames)
    (hg : (nsName, ga0) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        postCache state.now nsNames)
    (hall : ∀ n ∈ nsNames, ∃ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue
        (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames
        ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
            == VeriDNS.Impl.DomainName.foldNameCase n) = true)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hcanon : CanonicalName state.resources.sname) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.currentStep = .sendQueries
      ∧ CanonicalName st.resources.sname
      ∧ st.resources.sname = state.resources.sname
      ∧ st.lastQuery = state.lastQuery
      ∧ st.cnameChain = state.cnameChain
      ∧ (∃ sq, Resolver.buildSubQuery st revealed = some sq)
      ∧ (∃ entry ga gn, st.resources.slist.bestWithAddress = some (entry, ga)
           ∧ (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
                postCache state.now nsNames)
      ∧ st.resources.slist.addressTargets[0]? = none := by
  subst hpc
  obtain ⟨st, hcont, hsl, hsn, _hnw, hcc, hcs, hlqst⟩ :=
    VeriDNS.Proof.Refinement.afterResume_referral_continue_slist state entryName resp nsNames mc
      hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa hwalk hclose hnb
  refine ⟨st, hcont, hcs, by rw [hsn]; exact hcanon, hsn, hlqst, hcc, ?_, ?_, ?_⟩
  · have hbq : (Resolver.buildSubQuery st revealed).isSome = true := by
      simp only [Resolver.buildSubQuery, hlqst, hlq, hqu, Option.isSome_some]
    exact Option.isSome_iff_exists.mp hbq
  · rw [hsl]
    obtain ⟨entry, ga, gn, hbest, hgmem⟩ :=
      bestWithAddress_reGlue_resolves _ state.now nsNames mc nsName ga0 hnsMem hg
    exact ⟨entry, ga, gn, hbest, hgmem⟩
  · exact (branch2_childSlist_resolves st.resources.slist _ state.now nsNames mc nsName ga0
      hsl hnsMem hg hall).2

theorem finalizeAnswer_answer {S C NS RR : Type} [VeriDNS.Spec.SlistSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] (s : Resolver.State S C NS RR)
    (resp : VeriDNS.Spec.Format) (hchain : s.cnameChain = #[]) :
    (Resolver.finalizeAnswer s resp).answer = resp.answer := by
  unfold Resolver.finalizeAnswer Resolver.prependChain
  rw [hchain]
  cases s.lastQuery <;> rfl

theorem finalizeAnswer_question {S C NS RR : Type} [VeriDNS.Spec.SlistSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] (s : Resolver.State S C NS RR)
    (resp q : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q) :
    (Resolver.finalizeAnswer s resp).question = q.question := by
  unfold Resolver.finalizeAnswer
  rw [hlq]





theorem depth1Delegation_chain
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (childT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (childNeg : Array ByteArray)
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel'' revealed : Nat) (w : World)
    (entry : SlistEntry) (rootIp : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (sent : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (nsNames : Array ByteArray) (mc : Nat) (postCache : DnsCache)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (nsName : ByteArray) (ga0 : BitVec 32)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetworkAddr respond w)
    (hroot : respond (Server.ipv4ToAddr rootIp) sent = referralReply sent nsAuth glue)
    (hchild : ∀ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue
        (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames →
      ∀ q', respond (Server.ipv4ToAddr ga) q' = treeRespond childT childNeg q')
    (hegressGlue : ∀ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue
        (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames →
      Server.blockedEgress ga = false)
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hdl₂ : ¬ (w.clock + w.tick w.exchCtr ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, rootIp))
    (hegress : Server.blockedEgress rootIp = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hrev : DomainName.labelCount state.resources.sname ≤ revealed)
    (hcanon : CanonicalName state.resources.sname)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hqtc : (q.header.tc == 1) = false)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hqfe : (q.header.rcode == VeriDNS.Spec.Rcode.formatError) = false)
    (hchain0 : state.cnameChain = #[])
    (hrt : VeriDNS.Impl.Message.decode
        (VeriDNS.Impl.Message.encode (referralReply sent nsAuth glue))
        = .ok (referralReply sent nsAuth glue))
    (hoptG : ∀ b ∈ glue, Edns.isOptRR b = false)
    (hnA : ∀ b ∈ nsAuth, Server.capTtlRR b = b)
    (hdG : ∀ b ∈ glue, Server.capTtlRR b = b)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false)
    (hcloser : Server.delegationCloserB (state.resources.slist.markQueried entry.name)
        state.resources.sname (referralReply sent nsAuth glue) = true)
    (hbai : Server.respInBailiwick state.resources.sname
        (referralReply sent nsAuth glue) = true)
    (hpc : postCache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache
            (referralReply sent nsAuth glue)
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply sent nsAuth glue).authority)
              (referralReply sent nsAuth glue).authority)
            (Resolver.credAuthority ((referralReply sent nsAuth glue).header.aa == 1)) state.now)
          (referralReply sent nsAuth glue)
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply sent nsAuth glue).authority)
            (referralReply sent nsAuth glue).additional)
          Resolver.credAdditional state.now)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
        state.resources.sname postCache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128
        = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := DnsSList) (NS := SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) (referralReply sent nsAuth glue).authority) (referralReply sent nsAuth glue).authority))
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply sent nsAuth glue).authority)
            (referralReply sent nsAuth glue).additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
            (referralReply sent nsAuth glue).authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) (referralReply sent nsAuth glue).authority) (referralReply sent nsAuth glue).authority))
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
                (referralReply sent nsAuth glue).authority)
              (referralReply sent nsAuth glue).additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
              (referralReply sent nsAuth glue).authority state.resources.sname)))) = false)
    (hnb : ((VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord) postCache
        state.now nsNames).isEmpty && (mc == 0)) = false)
    (hnsMem : nsName ∈ nsNames)
    (hg : (nsName, ga0) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        postCache state.now nsNames)
    (hall : ∀ n ∈ nsNames, ∃ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue
        (RR := VeriDNS.Spec.ResourceRecord) postCache state.now nsNames
        ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
            == VeriDNS.Impl.DomainName.foldNameCase n) = true)
    (hlk : VeriDNS.Impl.NameTree.treeLookup childT
        (DomainName.randomizeCase (w.ids (w.idCtr + 3)) state.resources.sname) qu.qtype
        = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr)
    (hown : ∀ rr ∈ rrs.toList, VeriDNS.Impl.DomainName.nameEqCI
        (VeriDNS.Spec.RRParse.rrName rr)
        (DomainName.randomizeCase (w.ids (w.idCtr + 3)) state.resources.sname) = true) :
    ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      DescentChain sbelt deadline depth (.ok resp, cout) state (fuel'' + 2) revealed w
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question := by
  have hprobe : Resolver.probeRoundB state.resources.sname revealed = false :=
    probeRoundB_false_of_fullReveal state.resources.sname revealed hrev
  have hsent : VeriDNS.Impl.Message.decode (VeriDNS.Impl.Message.encode sent) = .ok sent := by
    rw [hsentEq]
    exact buildSubQuery_withSecrets_roundtrips state revealed subQuery₀
      (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild hprobe hcanon
  have hq1 : sent.question[0]?
      = some { qname := DomainName.randomizeCase (w.ids (w.idCtr + 1)) state.resources.sname,
               qtype := qu.qtype, qclass := qu.qclass } := by
    rw [hsentEq]
    exact buildSubQuery_withSecrets_question state revealed subQuery₀
      (w.ids w.idCtr) (w.ids (w.idCtr + 1)) q qu hlq hqu hbuild hprobe
  have hhdr₁ := buildSubQuery_withSecrets_header state revealed subQuery₀
      (w.ids w.idCtr) (w.ids (w.idCtr + 1)) q hlq hbuild
  have htcR : ((referralReply sent nsAuth glue).header.tc == 1) = false := by
    have hpass : (referralReply sent nsAuth glue).header.tc = sent.header.tc := rfl
    rw [hpass, hsentEq, hhdr₁.1]
    exact hqtc
  have hansE : (referralReply sent nsAuth glue).answer = #[] := rfl
  have hauthE : (referralReply sent nsAuth glue).authority = nsAuth := rfl
  have hrcR : (referralReply sent nsAuth glue).header.rcode = VeriDNS.Spec.Rcode.noError := rfl
  have haaR : (referralReply sent nsAuth glue).header.aa = 0 := rfl
  have hnoerr : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.noError) = true := by decide
  have hnsf : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.serverFailure) = false := by decide
  have hnne : (VeriDNS.Spec.Rcode.noError == VeriDNS.Spec.Rcode.nameError) = false := by decide
  have hclsR : Resolver.classifiableB (referralReply sent nsAuth glue) = true := by
    simp only [Resolver.classifiableB, hrcR, hnoerr, Bool.or_true, Bool.true_or]
  obtain ⟨st, hcont, hsendq₂, hcanon₂, hsnP, hlqP, hccP, _hbq,
      ⟨entry₂, ga, gn, hbest₂, hgmem⟩, _hglueless₂⟩ :=
    cooperativeReferral_continue_terminalFacts_exact
      { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } }
      entry.name (referralReply sent nsAuth glue) nsNames mc postCache q qu revealed nsName ga0
      hsendq
      (cnameToChase_of_emptyAnswer _ hansE)
      (by rw [hrcR, hclsR]; simp only [hnsf, Bool.not_true, Bool.or_false])
      (answersQueryB_of_emptyAnswer _ hansE)
      (by rw [hrcR]; exact hnne)
      (by rw [hansE]; rfl)
      (by rw [hauthE]; exact hasRRTypeIn_nonempty nsAuth 2 hns)
      (by rw [hauthE]; exact hns)
      (by rw [haaR]; rfl)
      (by rw [hrcR]; exact hnoerr)
      (by rw [hauthE]; exact hsoa)
      hpc hwalk hclose hnb hnsMem hg hall hlq hqu hcanon
  have hsn : st.resources.sname = state.resources.sname := hsnP
  have hlqst : st.lastQuery = some q := hlqP.trans hlq
  have hrevEq : Server.revealedAfterContinue state.resources.sname revealed st
      = max revealed (Server.seedRevealed st) := by
    unfold Server.revealedAfterContinue
    rw [hsn, VeriDNS.Impl.Cache.byteArray_beq_refl]
    simp
  have hprobe₂ : Resolver.probeRoundB st.resources.sname
      (Server.revealedAfterContinue state.resources.sname revealed st) = false := by
    rw [hrevEq, hsn]
    exact probeRoundB_false_of_fullReveal _ _ (Nat.le_trans hrev (Nat.le_max_left _ _))
  have hbq₂ : (Resolver.buildSubQuery st
      (Server.revealedAfterContinue state.resources.sname revealed st)).isSome = true := by
    simp only [Resolver.buildSubQuery, hlqst, hqu, Option.isSome_some]
  obtain ⟨subQuery₂, hbuild₂⟩ := Option.isSome_iff_exists.mp hbq₂
  have hsent₂ := buildSubQuery_withSecrets_roundtrips st
    (Server.revealedAfterContinue state.resources.sname revealed st) subQuery₂
    (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)) hbuild₂ hprobe₂ hcanon₂
  have hq₂ := buildSubQuery_withSecrets_question st
    (Server.revealedAfterContinue state.resources.sname revealed st) subQuery₂
    (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)) q qu hlqst hqu hbuild₂ hprobe₂
  have hhdr₂ := buildSubQuery_withSecrets_header st
    (Server.revealedAfterContinue state.resources.sname revealed st) subQuery₂
    (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)) q hlqst hbuild₂
  have hlk₂ : VeriDNS.Impl.NameTree.treeLookup childT
      (DomainName.randomizeCase (w.ids (w.idCtr + 3)) st.resources.sname) qu.qtype
      = .answer rrs := by rw [hsn]; exact hlk
  have htcS₂ : ((Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2))
      (w.ids (w.idCtr + 3))).header.tc == 1) = false := by
    rw [hhdr₂.1]; exact hqtc
  have hsfS₂ : ((Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2))
      (w.ids (w.idCtr + 3))).header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false := by
    rw [hhdr₂.2]; exact hqsf
  have hfeS₂ : ((Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2))
      (w.ids (w.idCtr + 3))).header.rcode == VeriDNS.Spec.Rcode.formatError) = false := by
    rw [hhdr₂.2]; exact hqfe
  have hpos := (treeLookup_answer childT _ qu.qtype rrs hlk₂).1
  have hmem : rrs[0] ∈ rrs := Array.getElem_mem hpos
  have hrtRR := parseRaw_rrBytes (hwfRR rrs[0] (Array.mem_def.mp hmem)).1
  obtain ⟨htcT, hunfT, hcnameT, hsfT, hclsT, hansT, hfeT⟩ :=
    treeRespond_answer_classified childT childNeg
      (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))
      (st.resources.slist.markQueried entry₂.name) st.resources.sname
      { qname := DomainName.randomizeCase (w.ids (w.idCtr + 3)) st.resources.sname,
        qtype := qu.qtype, qclass := qu.qclass } rrs rrs[0]
      hq₂ hlk₂ hmem hrtRR
      (by rw [hsn]; exact hown rrs[0] (Array.mem_def.mp hmem)) htcS₂ hsfS₂ hfeS₂
  have haeq₂ := treeRespond_answer_eq childT childNeg
      (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))
      { qname := DomainName.randomizeCase (w.ids (w.idCtr + 3)) st.resources.sname,
        qtype := qu.qtype, qclass := qu.qclass } rrs hq₂ hlk₂
  have hadd₂ := treeRespond_additional_empty childT childNeg
      (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))
      { qname := DomainName.randomizeCase (w.ids (w.idCtr + 3)) st.resources.sname,
        qtype := qu.qtype, qclass := qu.qclass } hq₂
  have hsecAuth₂ : (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2))
      (w.ids (w.idCtr + 3))).authority = #[] :=
    (buildSubQuery_withSecrets_sections st
      (Server.revealedAfterContinue state.resources.sname revealed st) subQuery₂
      (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)) hbuild₂).2
  have hrt₂ := treeRespond_answer_roundtrips childT childNeg
      (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))
      { qname := DomainName.randomizeCase (w.ids (w.idCtr + 3)) st.resources.sname,
        qtype := qu.qtype, qclass := qu.qclass } rrs hsent₂ hq₂ hlk₂ hsz
      (fun rr h => (hwfRR rr h).1)
  have hopt₂ : ∀ b ∈ (treeRespond childT childNeg (Server.withSecrets subQuery₂
      (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).additional, Edns.isOptRR b = false := by
    rw [hadd₂.1]; intro b hb; simp at hb
  have harc₂ : (treeRespond childT childNeg (Server.withSecrets subQuery₂
      (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).header.arcount
      = BitVec.ofNat 16 (treeRespond childT childNeg (Server.withSecrets subQuery₂
          (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).additional.size := by
    rw [hadd₂.1, hadd₂.2]; rfl
  have ha₂ : ∀ b ∈ (treeRespond childT childNeg (Server.withSecrets subQuery₂
      (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).answer, Server.capTtlRR b = b := by
    have hansA : (treeRespond childT childNeg (Server.withSecrets subQuery₂
        (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).answer
        = rrs.map RRParse.rrBytes := by rw [haeq₂]
    rw [hansA]; intro b hb
    rw [Array.mem_map] at hb; obtain ⟨rr, hrr, rfl⟩ := hb
    exact capTtlRR_rrBytes (hwfRR rr (Array.mem_def.mp hrr))
  have hn₂ : ∀ b ∈ (treeRespond childT childNeg (Server.withSecrets subQuery₂
      (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).authority, Server.capTtlRR b = b := by
    have hauthA : (treeRespond childT childNeg (Server.withSecrets subQuery₂
        (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).authority = #[] := by
      rw [haeq₂]; exact hsecAuth₂
    rw [hauthA]; intro b hb; simp at hb
  have hd₂ : ∀ b ∈ (treeRespond childT childNeg (Server.withSecrets subQuery₂
      (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))).additional, Server.capTtlRR b = b := by
    rw [hadd₂.1]; intro b hb; simp at hb
  have hsanEq₂ : Server.capTtls (Edns.stripOpt (treeRespond childT childNeg
      (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))))
      = treeRespond childT childNeg
          (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3))) := by
    rw [Edns.stripOpt_eq_self _ hopt₂ harc₂, capTtls_eq_self _ ha₂ hn₂ hd₂]
  obtain ⟨resp, cout, hterm, hansOut, hquesOut⟩ :
      ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      (∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock + w.tick w.exchCtr →
        w'.exchCtr = w.exchCtr + 1 → w'.tick = w.tick → w'.idCtr = w.idCtr + 2 →
        Delivers sbelt st deadline depth (fuel'' + 1)
          (Server.revealedAfterContinue state.resources.sname revealed st) w' (.ok resp, cout))
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question :=
    ⟨_, _, fun w' ho _hto hids hclk hectr htick hctr =>
      delegatingAnswerRound_delivers respond sbelt st deadline depth fuel''
        (Server.revealedAfterContinue state.resources.sname revealed st) w'
        entry₂ ga subQuery₂
        (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3)))
        (treeRespond childT childNeg
          (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3))))
        (treeRespond childT childNeg
          (Server.withSecrets subQuery₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 3))))
        { qname := DomainName.randomizeCase (w.ids (w.idCtr + 3)) st.resources.sname,
          qtype := qu.qtype, qclass := qu.qclass }
        (CooperativeNetworkAddr_of_oracle_eq respond w w' hcoop ho)
        (by rw [hids, hctr])
        (hchild gn ga hgmem _)
        hsent₂ hsendq₂ (by rw [hclk]; exact hdl₂) hbest₂
        (hegressGlue gn ga hgmem) hbuild₂ hprobe₂ hrt₂
        (treeRespond_header_id childT childNeg _) (treeRespond_question childT childNeg _)
        (treeRespond_qr_opcode childT childNeg _ _ hq₂).1
        (treeRespond_qr_opcode childT childNeg _ _ hq₂).2
        hq₂ hsanEq₂ htcT hunfT hcnameT hsfT hclsT hansT hfeT,
      (finalizeAnswer_answer _ _ (hccP.trans hchain0)).trans (by rw [haeq₂]),
      finalizeAnswer_question _ _ q hlqst⟩
  refine ⟨resp, cout, ?_, hansOut, hquesOut⟩
  refine delegatingReferralRound_node respond sbelt state deadline depth (fuel'' + 1) revealed w
    entry rootIp subQuery₀ sent nsAuth glue
    { qname := DomainName.randomizeCase (w.ids (w.idCtr + 1)) state.resources.sname,
      qtype := qu.qtype, qclass := qu.qclass } (.ok resp, cout)
    hcoop hsentEq hroot hsent hsendq hdl hbest hegress hbuild hrt hoptG hnA hdG hq1
    hns hsoa htcR hcloser hbai ?_
  intro st' hcont' w' ho hto hids hclk hectr htick hctr
  have hst : st = st' := by
    have h := hcont.symm.trans hcont'
    injection h
  subst hst
  exact DescentChain.terminal (hterm w' ho hto hids hclk hectr htick hctr)

theorem referral_continue_bestWithAddress
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (resp : VeriDNS.Spec.Format) (sname n gn : ByteArray) (ga : BitVec 32)
    (hst : st.resources.slist
      = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname))
    (hn : n ∈ Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
    (hg : (gn, ga) ∈ Resolver.extractGlueRecords (Resolver.bailiwickRaws
            (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
    (hmatch : (VeriDNS.Impl.DomainName.foldNameCase gn
        == VeriDNS.Impl.DomainName.foldNameCase n) = true) :
    st.resources.slist.bestWithAddress.isSome = true := by
  rw [hst]
  exact bestWithAddress_isSome_of_glueMatch _ _ _ n gn ga hn hg hmatch

theorem referral_continue_matchCount
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (resp : VeriDNS.Spec.Format) (sname : ByteArray)
    (hst : st.resources.slist
      = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority))
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname)) :
    st.resources.slist.matchCount
      = Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname := by
  rw [hst]; rfl


theorem referral_continue_matchCount_ge
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hdmc : 0 < Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority
        state.resources.sname) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority
          state.resources.sname ≤ st.resources.slist.matchCount := by
  obtain ⟨st, hcont, _, _, _, _, _, _, _, hdisj⟩ :=
    VeriDNS.Proof.Refinement.afterResume_referral_continue_cases state entryName resp
      hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  refine ⟨st, hcont, ?_⟩
  have hne : (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)).isEmpty
      = false := by
    have h := VeriDNS.Proof.Refinement.extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn
      (RR := VeriDNS.Spec.ResourceRecord) resp.authority hns
    simpa using h
  rcases hdisj with h1 | ⟨nsNames, mc, _hwalk, hguard, hslist⟩ | ⟨_hsb, hguard⟩
  ·
    rw [h1]; exact Nat.le_refl _
  ·
    rw [hslist]
    rw [VeriDNS.Proof.Refinement.searchFails_setUpAddresses,
        VeriDNS.Proof.Refinement.matchCount_setUpAddresses, hne] at hguard
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt] at hguard
    exact hguard
  ·
    exfalso
    rw [VeriDNS.Proof.Refinement.searchFails_setUpAddresses,
        VeriDNS.Proof.Refinement.matchCount_setUpAddresses, hne] at hguard
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt,
      Nat.le_zero] at hguard
    omega




theorem delegationMatchCount_gt_of_closer (slist : DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hclose : Server.delegationCloserB slist sname resp = true)
    (hne : slist.servers.isEmpty = false) :
    Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname
      > slist.matchCount := by
  unfold Server.delegationCloserB at hclose
  rw [Bool.or_eq_true] at hclose
  rcases hclose with hsf | hdec
  ·
    have : slist.servers.isEmpty = true := hsf
    rw [this] at hne
    exact absurd hne (by decide)
  · exact of_decide_eq_true hdec

theorem markQueried_matchCount (slist : DnsSList) (name : ByteArray) :
    (slist.markQueried name).matchCount = slist.matchCount := rfl

theorem markQueried_isEmpty (slist : DnsSList) (name : ByteArray) :
    (slist.markQueried name).servers.isEmpty = slist.servers.isEmpty := by
  simp only [DnsSList.markQueried, Array.isEmpty, Array.size_map]




theorem forIn_le_helper (l : List Nat) (init : Nat)
    (f : Nat → Nat → Id (ForInStep Nat))
    (hf : ∀ i r, ∃ r', f i r = ForInStep.yield r' ∧ r' ≤ r + 1) :
    Id.run (forIn l init f) ≤ init + l.length := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    obtain ⟨r', hr', hle⟩ := hf a init
    rw [List.forIn_cons, hr']
    show Id.run (forIn rest r' f) ≤ init + (rest.length + 1)
    have := ih r'
    omega

theorem suffixMatchCount_le (a b : Array ByteArray) :
    Resolver.suffixMatchCount a b ≤ min a.size b.size := by
  unfold Resolver.suffixMatchCount
  simp only [Id.run, bind, pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine Nat.le_trans (forIn_le_helper _ 0 _ ?_) ?_
  · intro i r
    by_cases hc : (r == i && DomainName.nameEqCI a[a.size - 1 - i]! b[b.size - 1 - i]!) = true
    · exact ⟨r + 1, if_pos hc, Nat.le_refl _⟩
    · exact ⟨r, if_neg hc, Nat.le_succ _⟩
  · simp only [List.length_range', Nat.zero_add, Std.Legacy.Range.size]
    omega

theorem delegationMatchCount_le (authority : Array ByteArray) (sname : ByteArray)
    (snameLabels : Array ByteArray)
    (hsn : DomainName.wireFormatToLabels sname = .ok snameLabels) :
    Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) authority sname
      ≤ snameLabels.size := by
  simp only [Resolver.delegationMatchCount]
  split
  · exact Nat.zero_le _
  · rw [hsn]
    split
    · rename_i _ _ _ _ hbw _
      injection hbw with hbw
      subst hbw
      exact Nat.le_trans (suffixMatchCount_le _ _) (Nat.min_le_left _ _)
    · exact Nat.zero_le _

theorem delegation_metric_decrease
    (slist stSlist : DnsSList) (name sname : ByteArray)
    (resp : VeriDNS.Spec.Format) (snameLabels : Array ByteArray)
    (hsn : DomainName.wireFormatToLabels sname = .ok snameLabels)
    (hst : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname
      ≤ stSlist.matchCount)
    (hcloser : Server.delegationCloserB (slist.markQueried name) sname resp = true)
    (hne : slist.servers.isEmpty = false) :
    snameLabels.size - stSlist.matchCount < snameLabels.size - slist.matchCount := by
  have hgt := delegationMatchCount_gt_of_closer (slist.markQueried name) sname resp hcloser
    (by rw [markQueried_isEmpty]; exact hne)
  rw [markQueried_matchCount] at hgt
  have hle := delegationMatchCount_le resp.authority sname snameLabels hsn
  omega



theorem bestWithAddress_singleton (s : DnsSList) (e : SlistEntry) (a : BitVec 32)
    (hs : s.servers = #[e]) (ha : e.address = some a) :
    s.bestWithAddress = some (e, a) := by
  have hmem : e ∈ s.servers := by rw [hs]; exact Array.mem_singleton.mpr rfl
  have hsome := bestWithAddress_isSome_of_mem s e a hmem ha
  obtain ⟨⟨e', a'⟩, hbw⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hmem', ha'⟩ := bestWithAddress_mem s e' a' hbw
  rw [hs] at hmem'
  have he : e' = e := Array.mem_singleton.mp hmem'
  subst he
  rw [ha] at ha'
  injection ha' with haa
  rw [hbw, ← haa]

theorem addressTargets_singleton_none (s : DnsSList) (e : SlistEntry) (a : BitVec 32)
    (hs : s.servers = #[e]) (ha : e.address = some a) :
    s.addressTargets[0]? = none := by
  have hempty : s.addressTargets = #[] := by
    unfold DnsSList.addressTargets
    rw [hs, Array.filterMap_eq_empty_iff]
    intro x hx
    rw [Array.mem_singleton] at hx
    subst hx
    rw [ha]
  rw [hempty]
  rfl

theorem markQueried_singleton (s : DnsSList) (n : ByteArray) (a : Option (BitVec 32)) (k : Nat)
    (hs : s.servers = #[⟨n, a, k⟩]) :
    (s.markQueried n).servers = #[⟨n, a, k + 1⟩] := by
  unfold DnsSList.markQueried
  simp only [hs, Array.map_singleton]
  rw [if_pos (byteArray_beq_refl n)]

theorem probeRoundB_true_of_lt (sname : ByteArray) (revealed : Nat)
    (h0 : 0 < revealed) (h : revealed < DomainName.labelCount sname) :
    Resolver.probeRoundB sname revealed = true := by
  unfold Resolver.probeRoundB
  simp [h0, h]

theorem bumpRevealed_metric_lt (sname : ByteArray) (revealed : Nat)
    (h : revealed < DomainName.labelCount sname) :
    DomainName.labelCount sname - Resolver.bumpRevealed sname revealed
      < DomainName.labelCount sname - revealed := by
  unfold Resolver.bumpRevealed
  split <;> omega

theorem bumpRevealed_pos (sname : ByteArray) (revealed : Nat)
    (h : revealed < DomainName.labelCount sname) :
    0 < Resolver.bumpRevealed sname revealed := by
  unfold Resolver.bumpRevealed
  split <;> omega

theorem flatProbeLadder_chain
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (sbelt : DnsSList) (deadline : UInt32) (depth : Nat)
    (nsName : ByteArray) (ipAddr : BitVec 32)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (I : Nat → UInt16) (TK : Nat → UInt32)
    (hegress : Server.blockedEgress ipAddr = false)
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hcanon : CanonicalName qu.qname)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hplk : ∀ (seed : UInt16) (r : Nat), 0 < r → r < DomainName.labelCount qu.qname →
        VeriDNS.Impl.NameTree.treeLookup T
          (DomainName.randomizeCase seed (DomainName.minimisedName qu.qname r))
          (BitVec.ofNat 16 1) = .nodata)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup T
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr)
    (hown : ∀ (seed : UInt16), ∀ rr ∈ rrs.toList, VeriDNS.Impl.DomainName.nameEqCI
        (VeriDNS.Spec.RRParse.rrName rr) (DomainName.randomizeCase seed qu.qname) = true) :
    ∀ (revealed fuel k ctr ectr : Nat) (cl : UInt32)
      (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord),
      TimelyWorld cl TK ectr deadline fuel →
      0 < revealed →
      DomainName.labelCount qu.qname - revealed < fuel →
      state.currentStep = .sendQueries →
      state.resources.sname = qu.qname →
      state.lastQuery = some q →
      state.cnameChain = #[] →
      state.resources.slist.servers = #[⟨nsName, some ipAddr, k⟩] →
      ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
        (∀ w : World, w.oracle = mkHonestOracle (treeRespond T negAuth) →
            w.ids = I → w.clock = cl → w.tick = TK → w.exchCtr = ectr → w.idCtr = ctr →
          DescentChain sbelt deadline depth (.ok resp, cout) state fuel revealed w)
        ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
        ∧ resp.question = q.question := by
  have key : ∀ (n revealed fuel k ctr ectr : Nat) (cl : UInt32)
      (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord),
      DomainName.labelCount qu.qname - revealed = n →
      TimelyWorld cl TK ectr deadline fuel →
      0 < revealed →
      DomainName.labelCount qu.qname - revealed < fuel →
      state.currentStep = .sendQueries →
      state.resources.sname = qu.qname →
      state.lastQuery = some q →
      state.cnameChain = #[] →
      state.resources.slist.servers = #[⟨nsName, some ipAddr, k⟩] →
      ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache),
        (∀ w : World, w.oracle = mkHonestOracle (treeRespond T negAuth) →
            w.ids = I → w.clock = cl → w.tick = TK → w.exchCtr = ectr → w.idCtr = ctr →
          DescentChain sbelt deadline depth (.ok resp, cout) state fuel revealed w)
        ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
        ∧ resp.question = q.question := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n IH =>
      intro revealed fuel k ctr ectr cl state hn htimely hrev hfuel hstep hsn hlq hchain hsl
      have hdl : ¬ (cl ≥ deadline) := htimely.not_deadline
      have hbq : (Resolver.buildSubQuery state revealed).isSome = true := by
        simp only [Resolver.buildSubQuery, hlq, hqu, Option.isSome_some]
      obtain ⟨subQuery₀, hbuild⟩ := Option.isSome_iff_exists.mp hbq
      have hcanS : CanonicalName state.resources.sname := by rw [hsn]; exact hcanon
      have hhdr := buildSubQuery_withSecrets_header state revealed subQuery₀
        (I ctr) (I (ctr + 1)) q hlq hbuild
      have hsects := buildSubQuery_withSecrets_sections state revealed subQuery₀
        (I ctr) (I (ctr + 1)) hbuild
      have htcS : ((Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.tc == 1)
          = false := by rw [hhdr.1]; exact htcq
      by_cases hfull : DomainName.labelCount qu.qname ≤ revealed
      ·
        cases fuel with
        | zero => omega
        | succ fuel' =>
        have hprobeF : Resolver.probeRoundB state.resources.sname revealed = false := by
          rw [hsn]; exact probeRoundB_false_of_fullReveal _ _ hfull
        have hsent := buildSubQuery_withSecrets_roundtrips state revealed subQuery₀
          (I ctr) (I (ctr + 1)) hbuild hprobeF hcanS
        have hqSent := buildSubQuery_withSecrets_question state revealed subQuery₀
          (I ctr) (I (ctr + 1)) q qu hlq hqu hbuild hprobeF
        rw [hsn] at hqSent
        have hsfS : ((Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.rcode
            == VeriDNS.Spec.Rcode.serverFailure) = false := by
          rw [hhdr.2, hrcq]; decide
        have hfeS : ((Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.rcode
            == VeriDNS.Spec.Rcode.formatError) = false := by
          rw [hhdr.2, hrcq]; decide
        have hlkF := hflk (I (ctr + 1))
        have haeq := treeRespond_answer_eq T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
          { qname := DomainName.randomizeCase (I (ctr + 1)) qu.qname,
            qtype := qu.qtype, qclass := qu.qclass } rrs hqSent hlkF
        have hadd := treeRespond_additional_empty T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) _ hqSent
        have hpos : 0 < rrs.size :=
          (treeLookup_answer T _ _ rrs (hflk (I (ctr + 1)))).1
        have hmem : rrs[0] ∈ rrs := Array.getElem_mem hpos
        have hrt := treeRespond_answer_roundtrips T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) _ rrs hsent hqSent hlkF hsz
          (fun rr h => (hwfRR rr h).1)
        have hopt : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional,
            Edns.isOptRR b = false := by
          rw [hadd.1]; intro b hb; simp at hb
        have harc : (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).header.arcount
            = BitVec.ofNat 16 (treeRespond T negAuth
                (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional.size := by
          rw [hadd.1, hadd.2]; rfl
        have ha : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).answer,
            Server.capTtlRR b = b := by
          have hans : (treeRespond T negAuth
              (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).answer
              = rrs.map VeriDNS.Spec.RRParse.rrBytes := by rw [haeq]
          rw [hans]; intro b hb
          rw [Array.mem_map] at hb; obtain ⟨rr, hrr, rfl⟩ := hb
          exact capTtlRR_rrBytes (hwfRR rr (Array.mem_def.mp hrr))
        have hn' : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).authority,
            Server.capTtlRR b = b := by
          have hauth : (treeRespond T negAuth
              (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).authority = #[] := by
            rw [haeq]; exact hsects.2
          rw [hauth]; intro b hb; simp at hb
        have hd : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional,
            Server.capTtlRR b = b := by
          rw [hadd.1]; intro b hb; simp at hb
        have hrtRR := parseRaw_rrBytes (hwfRR rrs[0] (Array.mem_def.mp hmem)).1
        refine ⟨_, _, fun w hwo hwids hwclk hwtick hwectr hwctr => DescentChain.terminal
          (flatAuthoritative_answerRound_delivers T negAuth sbelt state deadline depth fuel'
            revealed w ⟨nsName, some ipAddr, k⟩ ipAddr subQuery₀
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
            (treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))))
            _ rrs rrs[0]
            hwo (by rw [hwids, hwctr]) rfl hstep (by rw [hwclk]; exact hdl)
            (bestWithAddress_singleton _ _ _ hsl rfl)
            hegress hbuild hprobeF hsent hrt hopt harc ha hn' hd hqSent hlkF hmem hrtRR
            (hown (I (ctr + 1)) rrs[0] (Array.mem_def.mp hmem)) htcS hsfS hfeS), ?_, ?_⟩
        · rw [finalizeAnswer_answer, haeq]
          exact hchain
        · exact finalizeAnswer_question _ _ q hlq
      ·
        rw [Nat.not_le] at hfull
        cases fuel with
        | zero => omega
        | succ fuel' =>
        have hprobeS : Resolver.probeRoundB state.resources.sname revealed = true := by
          rw [hsn]; exact probeRoundB_true_of_lt _ _ hrev hfull
        have hsent := buildSubQuery_withSecrets_roundtrips_probe state revealed subQuery₀
          (I ctr) (I (ctr + 1)) hbuild hprobeS hcanS
        have hqSent := buildSubQuery_withSecrets_question_probe state revealed subQuery₀
          (I ctr) (I (ctr + 1)) q qu hlq hqu hbuild hprobeS
        rw [hsn] at hqSent
        have hrcS : (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))).header.rcode
            = VeriDNS.Spec.Rcode.noError := by rw [hhdr.2, hrcq]
        have hlkP := hplk (I (ctr + 1)) revealed hrev hfull
        have hguards := treeRespond_nodata_probeConsumed T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
          (state.resources.slist.markQueried nsName) state.resources.sname
          { qname := DomainName.randomizeCase (I (ctr + 1))
              (DomainName.minimisedName qu.qname revealed),
            qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
          hqSent hlkP hsects.1 hnoNs hrcS htcS
        have hndeq := treeRespond_nodata_eq T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
          { qname := DomainName.randomizeCase (I (ctr + 1))
              (DomainName.minimisedName qu.qname revealed),
            qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
          hqSent hlkP
        have hadd := treeRespond_additional_empty T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) _ hqSent
        have hoptP : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional,
            Edns.isOptRR b = false := by
          rw [hadd.1]; intro b hb; simp at hb
        have harcP : (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).header.arcount
            = BitVec.ofNat 16 (treeRespond T negAuth
                (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional.size := by
          rw [hadd.1, hadd.2]; rfl
        have haP : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).answer,
            Server.capTtlRR b = b := by
          have hans : (treeRespond T negAuth
              (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).answer = #[] := by
            rw [hndeq]; exact hsects.1
          rw [hans]; intro b hb; simp at hb
        have hnP : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).authority,
            Server.capTtlRR b = b := by
          have hauth : (treeRespond T negAuth
              (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).authority = negAuth := by
            rw [hndeq]
          rw [hauth]; exact hnegCap
        have hdP : ∀ b ∈ (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))).additional,
            Server.capTtlRR b = b := by
          rw [hadd.1]; intro b hb; simp at hb
        have hsanEqP : Server.capTtls (Edns.stripOpt (treeRespond T negAuth
            (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))))
            = treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))) := by
          rw [Edns.stripOpt_eq_self _ hoptP harcP]
          exact capTtls_eq_self _ haP hnP hdP
        have hrtP := treeRespond_nodata_roundtrips T negAuth
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
          { qname := DomainName.randomizeCase (I (ctr + 1))
              (DomainName.minimisedName qu.qname revealed),
            qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
          hsent hqSent hlkP hnsz hcanNeg
        have hbpos : 0 < Resolver.bumpRevealed state.resources.sname revealed := by
          rw [hsn]; exact bumpRevealed_pos _ _ hfull
        have hblt : DomainName.labelCount qu.qname
            - Resolver.bumpRevealed state.resources.sname revealed
            < DomainName.labelCount qu.qname - revealed := by
          rw [hsn]; exact bumpRevealed_metric_lt _ _ hfull
        obtain ⟨resp, cout, htail, hpinA, hpinQ⟩ := IH
          (DomainName.labelCount qu.qname
            - Resolver.bumpRevealed state.resources.sname revealed)
          (by omega)
          (Resolver.bumpRevealed state.resources.sname revealed) fuel' (k + 1) (ctr + 2)
          (ectr + 1) (cl + TK ectr)
          ({ state with resources := { state.resources with
              slist := state.resources.slist.markQueried nsName } })
          rfl htimely.step hbpos (by omega) hstep hsn hlq hchain
          (markQueried_singleton _ _ _ _ hsl)
        refine ⟨resp, cout, fun w hwo hwids hwclk hwtick hwectr hwctr => ?_, hpinA, hpinQ⟩
        have hwire := oracle_supplies_round (treeRespond T negAuth)
          (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1)))
          (Server.ipv4ToAddr ipAddr) w hwo hsent
          (treeRespond_header_id T negAuth _) (treeRespond_question T negAuth _)
          { qname := DomainName.randomizeCase (I (ctr + 1))
              (DomainName.minimisedName qu.qname revealed),
            qtype := BitVec.ofNat 16 1, qclass := qu.qclass }
          hqSent
        exact honestProbeConsumeNode sbelt state deadline depth fuel' revealed w
          ⟨nsName, some ipAddr, k⟩ ipAddr subQuery₀
          (treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))))
          (treeRespond T negAuth (Server.withSecrets subQuery₀ (I ctr) (I (ctr + 1))))
          (.ok resp, cout)
          (by rw [hwclk]; exact hdl)
          (bestWithAddress_singleton _ _ _ hsl rfl)
          hegress hbuild hprobeS
          (by rw [hwids, hwctr]; exact hwire.1)
          hrtP
          (by rw [hwids, hwctr]; exact hwire.2.1)
          (by rw [hwids, hwctr]; exact hwire.2.2)
          (treeRespond_qr_opcode T negAuth _ _ hqSent).1
          (by rw [(treeRespond_qr_opcode T negAuth _ _ hqSent).2,
              (withSecrets_qr_opcode subQuery₀ _ _).2,
              buildSubQuery_opcode _ _ _ hbuild])
          hsanEqP hguards.1 hguards.2.1 hguards.2.2.1 hguards.2.2.2.1
          hguards.2.2.2.2
          (fun w' ho' _ hids' hclk' hectr' htick' hctr' =>
            htail w' (ho'.trans hwo) (hids'.trans hwids)
              (by rw [hclk', hwclk, hwtick, hwectr])
              (htick'.trans hwtick)
              (by rw [hectr', hwectr])
              (by rw [hctr', hwctr]))
  intro revealed fuel k ctr ectr cl state htimely hrev hfuel hstep hsn hlq hchain hsl
  exact key _ revealed fuel k ctr ectr cl state rfl htimely hrev hfuel hstep hsn hlq hchain hsl

theorem resolveWithIO_flatMultiLabel_adequate
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (nsName : ByteArray) (ipAddr : BitVec 32) (k : Nat)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetwork (treeRespond T negAuth) w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (htimely : TimelyWorld w.clock w.tick w.exchCtr (now + budget) fuel)
    (hfuel : DomainName.labelCount qu.qname - Server.seedRevealed state < fuel)
    (hstep : state.currentStep = .sendQueries)
    (hsn : state.resources.sname = qu.qname)
    (hlq : state.lastQuery = some q)
    (hchain : state.cnameChain = #[])
    (hsl : state.resources.slist.servers = #[⟨nsName, some ipAddr, k⟩])
    (hegress : Server.blockedEgress ipAddr = false)
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hcanon : CanonicalName qu.qname)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hplk : ∀ (seed : UInt16) (r : Nat), 0 < r → r < DomainName.labelCount qu.qname →
        VeriDNS.Impl.NameTree.treeLookup T
          (DomainName.randomizeCase seed (DomainName.minimisedName qu.qname r))
          (BitVec.ofNat 16 1) = .nodata)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup T
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr)
    (hown : ∀ (seed : UInt16), ∀ rr ∈ rrs.toList, VeriDNS.Impl.DomainName.nameEqCI
        (VeriDNS.Spec.RRParse.rrName rr) (DomainName.randomizeCase seed qu.qname) = true) :
    ∃ (K : Nat) (w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w = some ((.ok resp, cout), w')
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question := by
  have hrev : 0 < Server.seedRevealed state := by
    unfold Server.seedRevealed; omega
  obtain ⟨resp, cout, hch, hpinA, hpinQ⟩ := flatProbeLadder_chain T negAuth sbelt
    (now + budget) depth nsName ipAddr q qu rrs w.ids w.tick hegress hqu htcq hrcq
    hcanon hnoNs hnsz hcanNeg hnegCap hplk hflk hsz hwfRR hown
    (Server.seedRevealed state) fuel k w.idCtr w.exchCtr w.clock state htimely hrev hfuel
    hstep hsn hlq hchain hsl
  obtain ⟨K, w', hrun⟩ := resolveWithIO_adequate_of_chain query sbelt cache now fuel depth
    budget w state (.ok resp, cout) hpause (hch w hcoop rfl rfl rfl rfl rfl)
  exact ⟨K, w', resp, cout, hrun, hpinA, hpinQ⟩

/-- `tick ≡ 0` sanity specialization (finding 061): in a zero-latency world the
timely capstone collapses to the pre-061 frozen-clock statement — same
premises (`hdl` alone), same conclusion. -/
theorem resolveWithIO_flatMultiLabel_adequate_tick0
    (T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (negAuth : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (nsName : ByteArray) (ipAddr : BitVec 32) (k : Nat)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetwork (treeRespond T negAuth) w)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (htick : ∀ i, w.tick i = 0)
    (hdl : ¬ (w.clock ≥ now + budget))
    (hfuel : DomainName.labelCount qu.qname - Server.seedRevealed state < fuel)
    (hstep : state.currentStep = .sendQueries)
    (hsn : state.resources.sname = qu.qname)
    (hlq : state.lastQuery = some q)
    (hchain : state.cnameChain = #[])
    (hsl : state.resources.slist.servers = #[⟨nsName, some ipAddr, k⟩])
    (hegress : Server.blockedEgress ipAddr = false)
    (hqu : q.question[0]? = some qu)
    (htcq : (q.header.tc == 1) = false)
    (hrcq : q.header.rcode = VeriDNS.Spec.Rcode.noError)
    (hcanon : CanonicalName qu.qname)
    (hnoNs : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) negAuth 2 = false)
    (hnsz : negAuth.size < 65536)
    (hcanNeg : CanonicalSection negAuth)
    (hnegCap : ∀ b ∈ negAuth, Server.capTtlRR b = b)
    (hplk : ∀ (seed : UInt16) (r : Nat), 0 < r → r < DomainName.labelCount qu.qname →
        VeriDNS.Impl.NameTree.treeLookup T
          (DomainName.randomizeCase seed (DomainName.minimisedName qu.qname r))
          (BitVec.ofNat 16 1) = .nodata)
    (hflk : ∀ seed : UInt16, VeriDNS.Impl.NameTree.treeLookup T
        (DomainName.randomizeCase seed qu.qname) qu.qtype = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr)
    (hown : ∀ (seed : UInt16), ∀ rr ∈ rrs.toList, VeriDNS.Impl.DomainName.nameEqCI
        (VeriDNS.Spec.RRParse.rrName rr) (DomainName.randomizeCase seed qu.qname) = true) :
    ∃ (K : Nat) (w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w = some ((.ok resp, cout), w')
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question :=
  resolveWithIO_flatMultiLabel_adequate T negAuth query sbelt cache now fuel depth budget
    w state nsName ipAddr k q qu rrs hcoop hpause
    (TimelyWorld.of_tick0 htick fuel hdl) hfuel hstep hsn hlq hchain hsl hegress hqu htcq
    hrcq hcanon hnoNs hnsz hcanNeg hnegCap hplk hflk hsz hwfRR hown






theorem foldNameCase_size (n : ByteArray) :
    (VeriDNS.Impl.DomainName.foldNameCase n).size = n.size := by
  unfold VeriDNS.Impl.DomainName.foldNameCase
  show (n.data.map VeriDNS.Impl.DomainName.foldCaseByte).size = n.data.size
  exact Array.size_map

theorem nameEqCI_size {a b : ByteArray}
    (h : VeriDNS.Impl.DomainName.nameEqCI a b = true) : a.size = b.size := by
  unfold VeriDNS.Impl.DomainName.nameEqCI at h
  have heq := VeriDNS.Proof.Refinement.byteArray_beq_iff_eq.mp h
  have hsz := congrArg ByteArray.size heq
  rwa [foldNameCase_size, foldNameCase_size] at hsz

def DescentCacheInv (c : DnsCache) (bound : Nat) : Prop :=
  ∀ e ∈ c.records,
    ((e.rr.type == BitVec.ofNat 16 2) = true → e.rr.name.size < bound)
    ∧ Resolver.credAdditional.toCode ≤ e.credibility.toCode

theorem DescentCacheInv.of_empty {c : DnsCache} (h : c.records = #[]) (bound : Nat) :
    DescentCacheInv c bound := by
  intro e he
  rw [h] at he
  simp at he

theorem DescentCacheInv.mono {c : DnsCache} {bound bound' : Nat}
    (hinv : DescentCacheInv c bound) (h : bound ≤ bound') : DescentCacheInv c bound' :=
  fun e he => ⟨fun ht => Nat.lt_of_lt_of_le ((hinv e he).1 ht) h, (hinv e he).2⟩

theorem DescentCacheInv.nsKey_none {c : DnsCache} {bound : Nat}
    (hinv : DescentCacheInv c bound) (sname : ByteArray) (hge : bound ≤ sname.size) :
    ∀ e ∈ c.records,
      (VeriDNS.Impl.DomainName.nameEqCI e.rr.name sname
        && e.rr.type == BitVec.ofNat 16 2 && e.rr.class == BitVec.ofNat 16 1) = false := by
  intro e he
  cases ht : (e.rr.type == BitVec.ofNat 16 2) with
  | false => simp
  | true =>
    have hlt := (hinv e he).1 ht
    have hne : VeriDNS.Impl.DomainName.nameEqCI e.rr.name sname = false := by
      cases hci : VeriDNS.Impl.DomainName.nameEqCI e.rr.name sname with
      | false => rfl
      | true => exact absurd (nameEqCI_size hci) (by omega)
    simp [hne]

theorem DescentCacheInv.noBetterGlue {c : DnsCache} {bound : Nat}
    (hinv : DescentCacheInv c bound) (grr : VeriDNS.Spec.ResourceRecord) (now : UInt32) :
    NoBetterGlue c grr Resolver.credAdditional now :=
  fun e2 he2 _ _ _ _ => (hinv e2 he2).2

theorem mem_touchKeys_inv (c : DnsCache) (ks : Array RRKey) (now : UInt32) (e : CacheEntry)
    (he : e ∈ (c.touchKeys ks now).records) :
    ∃ e' ∈ c.records, e.rr = e'.rr ∧ e.credibility = e'.credibility := by
  unfold DnsCache.touchKeys at he
  replace he : e ∈ c.records.map (touchEntry ks now) := he
  rw [Array.mem_map] at he
  obtain ⟨a, ha, hae⟩ := he
  refine ⟨a, ha, ?_, ?_⟩ <;>
  · rw [← hae]
    unfold touchEntry
    split <;> rfl

theorem mem_boundLru_inv (c : DnsCache) (touches : Array RRKey) (now : UInt32) (e : CacheEntry)
    (he : e ∈ (c.boundLru touches now).records) :
    ∃ e' ∈ c.records, e.rr = e'.rr ∧ e.credibility = e'.credibility := by
  unfold DnsCache.boundLru DnsCache.boundLruKeys at he
  replace he : e ∈ evictLruKeys (c.touchKeys touches now).records
      (c.touchKeys touches now).records.size := he
  exact mem_touchKeys_inv c touches now e (mem_of_mem_evictLruKeys he)

theorem mem_cacheUnlessTruncated_inv (c : DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32) (e : CacheEntry)
    (he : e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now).records) :
    e ∈ c.records
    ∨ ∃ b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) raws,
        ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
          ∧ e = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
  unfold Resolver.cacheUnlessTruncated at he
  split at he
  · exact Or.inl he
  · exact mem_cacheRRs_inv c _ cred now e he

theorem DescentCacheInv.write {c : DnsCache} {bound : Nat} (bound' : Nat)
    (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32) (touches : Array RRKey)
    (hinv : DescentCacheInv c bound)
    (hmono : bound ≤ bound')
    (hcredA : Resolver.credAdditional.toCode ≤ credA.toCode)
    (hcredD : Resolver.credAdditional.toCode ≤ credD.toCode)
    (hauthB : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) authRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 2) = true → rr.name.size < bound')
    (haddB : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection
        (RR := VeriDNS.Spec.ResourceRecord) addRaws,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == BitVec.ofNat 16 2) = true → rr.name.size < bound') :
    DescentCacheInv ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          c resp authRaws credA now)
        resp addRaws credD now).boundLru touches now) bound' := by
  intro e he
  obtain ⟨e', he', hrr, hcred⟩ := mem_boundLru_inv _ _ _ e he
  rw [hrr, hcred]
  rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e' he' with h1 | ⟨b, hb, rr, hp, hpush⟩
  · rcases mem_cacheUnlessTruncated_inv _ _ _ _ _ e' h1 with h0 | ⟨b, hb, rr, hp, hpush⟩
    · have h := hinv e' h0
      exact ⟨fun ht => Nat.lt_of_lt_of_le (h.1 ht) hmono, h.2⟩
    · subst hpush
      exact ⟨fun ht => hauthB b hb rr hp ht, hcredA⟩
  · subst hpush
    exact ⟨fun ht => haddB b hb rr hp ht, hcredD⟩