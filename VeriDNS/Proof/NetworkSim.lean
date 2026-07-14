import VeriDNS.Proof.FreeIO
import VeriDNS.Proof.WorldNetwork
import VeriDNS.Proof.AnswerTerminal






namespace VeriDNS.Proof.NetworkSim

open VeriDNS.Spec (RRType RRClass)
open VeriDNS.Spec.Net
open VeriDNS.Proof.Refinement VeriDNS.Proof.FreeIO

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
    (hnc : cnameRR q.qname (αResp respImpl).answer = none ∨ q.qtype.covers RRType.cname = true)
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



abbrev SpoofReply (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat)
    (id : UInt16) (ab : ByteArray) (resp : VeriDNS.Spec.Format) (qm : Query) : Prop :=
  ∃ (origin : String) (reply : Datagram) (srcPort : Nat),
    Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply) ∧
    accepts (queryDatagram id.toNat resolverAddr (byteAddrToModel ab) srcPort ednsBuf qm) reply
      = true ∧
    RespAgree (αResp resp) reply.msg ∧
    (αResp resp).isReferral = reply.msg.isReferral ∧
    reply.msg.tc = false ∧
    αSection resp.authority = reply.msg.authority ∧
    (∀ b ∈ resp.answer.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
    (∀ b ∈ resp.authority.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
    (reply.msg.isReferral = true →
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
      ((resp.header.tc == 1) = reply.msg.tc))

def WorldModels (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat)
    (now : Time) (w : World) : Prop :=
  ∀ (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format) (qm : Query),
    w.oracle (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Server.withSecrets q id cid)) ab = some d →
    VeriDNS.Impl.Server.acceptExchanged ab d = some bytes →
    VeriDNS.Impl.Message.decode bytes = .ok resp0 →
    VeriDNS.Impl.Server.sanitizeTtlsCap resp0 = some resp₀ →
    VeriDNS.Impl.Server.acceptResponse (VeriDNS.Impl.Server.withSecrets q id cid) resp₀ = some resp →
    αQuery q = some qm →

    ( (∃ srv tr ref, serverAt net (byteAddrToModel ab) = some srv ∧
          ServerAnswers srv now [] true qm tr ref ∧
          RespAgree (αResp resp) ref ∧
          linkReach net ns resolverAddr (byteAddrToModel ab) = true ∧

          truncateToCap (negotiatedUdp ednsBuf) qm ref = (ref, false) ∧

          (αResp resp).isReferral = ref.isReferral ∧
          (VeriDNS.Spec.Net.cnameRR qm.qname (αResp resp).answer = none
            ↔ VeriDNS.Spec.Net.cnameRR qm.qname ref.answer = none) ∧

          αSection resp.answer = ref.answer ∧

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

      ∨ SpoofReply net ns resolverAddr ednsBuf id ab resp qm )

def WorldModelsTcp (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat)
    (now : Time) (w : World) : Prop :=
  ∀ (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format) (qm : Query),
    w.tcpOracle (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Server.withSecrets q id cid)) ab = some bytes →
    VeriDNS.Impl.Message.decode bytes = .ok resp0 →
    VeriDNS.Impl.Server.sanitizeTtlsCap resp0 = some resp₀ →
    VeriDNS.Impl.Server.acceptResponse (VeriDNS.Impl.Server.withSecrets q id cid) resp₀ = some resp →
    αQuery q = some qm →
    (∃ srv tr ref, serverAt net (byteAddrToModel ab) = some srv ∧
        ServerAnswers srv now [] true qm tr ref ∧
        RespAgree (αResp resp) ref ∧
        linkReach net ns resolverAddr (byteAddrToModel ab) = true ∧

        (αResp resp).isReferral = ref.isReferral ∧
        (VeriDNS.Spec.Net.cnameRR qm.qname (αResp resp).answer = none
          ↔ VeriDNS.Spec.Net.cnameRR qm.qname ref.answer = none) ∧

        αSection resp.answer = ref.answer ∧

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

theorem WorldModelsTcp_tcpOracle (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (now : Time) {w w' : World} (hor : w'.tcpOracle = w.tcpOracle)
    (h : WorldModelsTcp net ns ra ednsBuf now w) : WorldModelsTcp net ns ra ednsBuf now w' := by
  intro q id cid ab bytes resp0 resp₀ resp qm hO hd hs hacc hαq
  exact h q id cid ab bytes resp0 resp₀ resp qm (by rw [← hor]; exact hO) hd hs hacc hαq



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

theorem answer_classifier (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id sp : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hnr : ref.isReferral = false)
    (hnc : cnameRR q.qname ref.answer = none ∨ q.qtype.covers RRType.cname = true
            ∨ (∃ rr ∈ ref.answer, q.qtype.covers rr.rdata.rtype = true))
    (htc : ref.tc = false)
    (v : Response) (hbridge : RespAgree v { ref with aa := false }) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ht, ha, hw⟩ := honest_wire_premises net ns ra addr id sp ednsBuf q ref hreachS hreachR
  exact answer_hasVerdict net ns ra ednsBuf rttOf addr rest q srv tr ref id sp c hmiss hnmiss hfind hans
    (replyDatagram (queryDatagram id ra addr sp ednsBuf q) ref) ht ha
    (by rw [show (truncateToCap (negotiatedUdp ednsBuf) q ref).1 = ref from by rw [hfit]]; exact hw)
    hnr hnc htc v hbridge

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
    (hcn : cnameRR q.qname reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname)))
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

theorem cname_classifier (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (cn : RR) (target : Name) (id sp : Nat) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hcn : cnameRR q.qname ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname (ref.answerOwned q.qname)))
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

theorem cname_classifier_bridge (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (cn : RR) (target : Name) (id sp : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hcn : cnameRR q.qname ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname (ref.answerOwned q.qname)))
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

theorem cname_classifier_bridge_at (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (cn : RR) (target : Name) (id sp : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (hreachS : linkReach net ns ra addr = true) (hreachR : linkReach net ns ra ra = true)
    (hfit : truncateToCap (negotiatedUdp ednsBuf) q ref = (ref, false))
    (hcn : cnameRR q.qname ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname (ref.answerOwned q.qname)))
    (cf : VeriDNS.Spec.Net.Cache) (hcf : VeriDNS.Spec.Net.WriteRefines now' cf cf0)
    (hrec : Resolves net ns ra ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q v cout := by
  obtain ⟨ht, ha, hw⟩ := honest_wire_premises net ns ra addr id sp ednsBuf q ref hreachS hreachR
  exact ⟨_, _, _, _,
    Resolves.answerCname addr rest q srv tr ref cn target id sp c nsl
      ftr rpath tEnd cout final hmiss hnmiss hfind hans
      (replyDatagram (queryDatagram id ra addr sp ednsBuf q) ref) ht ha
      (by rw [show (truncateToCap (negotiatedUdp ednsBuf) q ref).1 = ref from by rw [hfit]]; exact hw)
      hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

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
    (hcn : cnameRR q.qname ref.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now') (htc : ref.tc = false)
    (cf0 : VeriDNS.Spec.Net.Cache)
    (hcf0 : VeriDNS.Spec.Net.WriteRefines now' cf0 (c.absorb now q.qname (ref.answerOwned q.qname)))
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

theorem cnameRR_ref_target
    (qn : Name) (resp : VeriDNS.Spec.Format) (ref : Response) (target' : Name) (cn0 : RR)
    (hcn0 : cnameRR qn (αResp resp).answer = some cn0)
    (htgt0 : cn0.rdata = RData.cname target')
    (hcnsome : ∀ cn, cnameRR qn (αResp resp).answer = some cn →
        ∃ cn', cnameRR qn ref.answer = some cn' ∧ cn'.rdata = cn.rdata) :
    ∃ cn', cnameRR qn ref.answer = some cn' ∧ cn'.rdata = RData.cname target' := by
  obtain ⟨cn', hcn', hrd⟩ := hcnsome cn0 hcn0
  exact ⟨cn', hcn', by rw [hrd, htgt0]⟩

theorem answer_records_match (z : Zone) (qname : Name) (qt : QType) (qcls : RRClass) (r : RR)
    (h : r ∈ (recordsAt z qname).filter (fun r => qt.covers r.rdata.rtype && r.cls == qcls)) :
    nameEq r.owner qname = true ∧ qt.covers r.rdata.rtype = true ∧ (r.cls == qcls) = true := by
  rw [List.mem_filter] at h
  obtain ⟨hrec, hp⟩ := h
  rw [recordsAt, List.mem_filter] at hrec
  rw [Bool.and_eq_true] at hp
  exact ⟨hrec.2, hp.1, hp.2⟩

theorem isReferral_of_authority_nil (r : Response) (h : r.authority = []) : r.isReferral = false := by
  simp [Response.isReferral, h]

theorem isReferral_of_answer_nonempty (r : Response) (h : r.answer ≠ []) : r.isReferral = false := by
  unfold Response.isReferral
  have : r.answer.isEmpty = false := by
    cases hr : r.answer with
    | nil => exact absurd hr h
    | cons _ _ => rfl
  simp [this]

theorem serverAnswers_tc_false {s : Server} {now : Time} {seen : List Name} {o : Bool} {q : Query}
    {tr : List Step} {resp : Response} (h : ServerAnswers s now seen o q tr resp) :
    resp.tc = false := by
  induction h with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih => exact ih
  | _ => rfl

theorem cnameRR_filter_none {qn : Name} {l : List RR} {p : RR → Bool} (h : cnameRR qn l = none) :
    cnameRR qn (l.filter p) = none := by
  unfold cnameRR at h ⊢
  rw [List.find?_eq_none] at h ⊢
  intro r hr
  exact h r (List.mem_filter.mp hr).1


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

def ModelOneExpiry (c : VeriDNS.Spec.Net.Cache) : Prop :=
  ∀ e₁ ∈ c.pos, ∀ e₂ ∈ c.pos, e₁.sameKey e₂.rr = true →
    e₁.insertedAt + e₁.rr.ttl = e₂.insertedAt + e₂.rr.ttl

theorem MatchMaxEquiv.cacheRefines {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c') :
    VeriDNS.Spec.Net.CacheRefines c c' :=
  ⟨fun n q => (h.1 n q).subperm, h.2.1, h.2.2⟩

theorem ModelOneExpiry.filterPos {c : VeriDNS.Spec.Net.Cache} (h : ModelOneExpiry c)
    (qf : VeriDNS.Spec.Net.CacheRR → Bool) : ModelOneExpiry (c.filterPos qf) := by
  intro e₁ he₁ e₂ he₂ hk
  exact h e₁ (List.mem_filter.mp he₁).1 e₂ (List.mem_filter.mp he₂).1 hk

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

theorem MatchMaxEquiv.served {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (c.served now q).Perm (c'.served now q) := by
  rw [c.served_eq_topServed_filter, c'.served_eq_topServed_filter]
  exact (h.1 now q).filter _

theorem perm_flatMap_congr {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a t ih =>
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem MatchMaxEquiv.nsHostsAt {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (nm : VeriDNS.Spec.Net.Name) :
    (c.nsHostsAt now nm).Perm (c'.nsHostsAt now nm) := by
  unfold VeriDNS.Spec.Net.Cache.nsHostsAt
  exact (h.1 now _).filterMap _

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

theorem MatchMaxEquiv.hit {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    (c.hit now q).Perm (c'.hit now q) := by
  unfold VeriDNS.Spec.Net.Cache.hit
  rw [c.served_eq_topServed_filter, c'.served_eq_topServed_filter]
  exact ((h.1 now q).filter _).map _

theorem MatchMaxEquiv.cnameServed {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (qname : VeriDNS.Spec.Net.Name) (qcls : RRClass) :
    (c.cnameServed now qname qcls).Perm (c'.cnameServed now qname qcls) := by
  unfold VeriDNS.Spec.Net.Cache.cnameServed
  exact (h.served now _).filterMap _

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



open VeriDNS.Spec (RRType) in
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

def modelPushOf (now : VeriDNS.Spec.Net.Time) (cred : VeriDNS.Spec.Net.Cred)
    (r : VeriDNS.Spec.Net.RR) : List VeriDNS.Spec.Net.CacheRR :=
  if VeriDNS.Spec.Net.cacheable r then [⟨r, now, cred⟩] else []

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

theorem section_owner_extra_perm (sec : Array ByteArray) (sname : ByteArray)
    (qnN : VeriDNS.Spec.Net.Name)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hsq : αName sname = some qnN)
    (hsc : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qnN)
    (hsv : ∀ x ∈ qnN, x.size ≤ 63)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sec)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf
        (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sec),
        RRCanonMappable e) :
    (((VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sec)).toList.flatMap
        (pushOf cred now)).filterMap αCacheRR).Perm
      ((VeriDNS.Spec.Net.normalizeTTL
          ((αSection sec).filter (fun r => VeriDNS.Spec.Net.nameEq r.owner qnN))).reverse.flatMap
        (modelPushOf now.toNat (αCred cred))) := by
  rw [flatMap_pushOf_filterMap_eq _ cred now hno]
  have hb : (VeriDNS.Impl.Cache.normRaws
        (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sec)).toList.filterMap
      (fun b => (VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b).bind αRR)
      = VeriDNS.Spec.Net.normalizeTTL
          ((αSection sec).filter (fun r => VeriDNS.Spec.Net.nameEq r.owner qnN)) := by
    have hαs : (VeriDNS.Impl.Cache.normRaws
          (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sec)).toList.filterMap
        (fun b => (VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b).bind αRR)
        = αSection (VeriDNS.Impl.Cache.normRaws
          (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sec)) := by
      unfold αSection
      congr 1
      funext b
      cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
    rw [hαs, αSection_normRaws _ hcanmap, αSection_ownerRaws_eq sname qnN sec hsq hsc hsv]
  rw [hb]
  exact (List.reverse_perm _).symm.flatMap_right _

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

theorem absorb_answerOwned_pos (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (qn : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response) :
    (c.absorb now qn (resp.answerOwned qn)).pos
      = ((VeriDNS.Spec.Net.normalizeTTL
            (resp.answer.filter (fun r => VeriDNS.Spec.Net.nameEq r.owner qn))).reverse.flatMap
            (modelPushOf now (if resp.aa then VeriDNS.Spec.Net.Cred.authoritative
                                          else VeriDNS.Spec.Net.Cred.glue)))
        ++ c.pos := by
  have hsub : (resp.answer.filter (fun r => VeriDNS.Spec.Net.nameEq r.owner qn)).filter
      (fun r => VeriDNS.Spec.Net.isAncestor qn r.owner)
      = resp.answer.filter (fun r => VeriDNS.Spec.Net.nameEq r.owner qn) :=
    List.filter_eq_self.mpr (fun r hr =>
      VeriDNS.Spec.Net.isAncestor_of_nameEq (List.mem_filter.mp hr).2)
  unfold VeriDNS.Spec.Net.Cache.absorb
  simp only [VeriDNS.Spec.Net.Response.answerOwned_answer,
    VeriDNS.Spec.Net.Response.answerOwned_authority,
    VeriDNS.Spec.Net.Response.answerOwned_additional,
    VeriDNS.Spec.Net.Response.answerOwned_aa, List.filter_nil,
    show VeriDNS.Spec.Net.normalizeTTL ([] : List VeriDNS.Spec.Net.RR) = [] from rfl,
    List.foldl_nil]
  rw [hsub, foldl_insert_concrete]
  rfl

theorem not_fresh_of_ttl_zero (e : VeriDNS.Spec.Net.CacheRR) (nowT : VeriDNS.Spec.Net.Time)
    (h0 : e.rr.ttl = 0) (hle : e.insertedAt ≤ nowT) :
    e.fresh nowT = false := by
  unfold VeriDNS.Spec.Net.CacheRR.fresh
  rw [h0, Nat.add_zero, Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  exact Nat.not_lt.mpr hle

open VeriDNS.Spec (RRType) in
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

theorem matching_absorb_append (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query) :
    ∃ M, ∀ (c : VeriDNS.Spec.Net.Cache),
      (c.absorb now bw resp).matching now' q = M ++ c.matching now' q := by
  obtain ⟨N, hN⟩ := absorb_pos_append now bw resp
  refine ⟨N.filter (fun e => e.fresh now' && VeriDNS.Spec.Net.nameEq e.rr.owner q.qname
                          && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass)), fun c => ?_⟩
  unfold VeriDNS.Spec.Net.Cache.matching
  rw [hN c, List.filter_append]



theorem rrtype_eq_of_beq : ∀ {a b : RRType}, (a == b) = true → a = b :=
  fun h => VeriDNS.Proof.Refinement.rrtype_eq_of_beq h

theorem rrclass_eq_of_beq : ∀ {a b : RRClass}, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

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

theorem cacheRR_sameKey_refl (e : VeriDNS.Spec.Net.CacheRR) : e.sameKey e.rr = true := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey
  simp [VeriDNS.Spec.Net.nameEq_refl, rrtype_beq_self, rrclass_beq_self]

theorem cacheRR_sameKey_trans {e1 e2 : VeriDNS.Spec.Net.CacheRR} {r : VeriDNS.Spec.Net.RR}
    (h1 : e1.sameKey e2.rr = true) (h2 : e2.sameKey r = true) : e1.sameKey r = true := by
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at h1 h2 ⊢
  simp only [Bool.and_eq_true] at h1 h2 ⊢
  obtain ⟨⟨hn1, ht1⟩, hc1⟩ := h1
  obtain ⟨⟨hn2, ht2⟩, hc2⟩ := h2
  exact ⟨⟨VeriDNS.Spec.Net.nameEq_trans hn1 hn2, by rw [rrtype_eq_of_beq ht1]; exact ht2⟩,
         by rw [rrclass_eq_of_beq hc1]; exact hc2⟩

def topOf (L : List VeriDNS.Spec.Net.CacheRR) : List VeriDNS.Spec.Net.CacheRR :=
  L.filter (fun e => L.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))

theorem topServed_eq_topOf (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (q : VeriDNS.Spec.Net.Query) : c.topServed now q = topOf (c.matching now q) := rfl

theorem ble_self (n : Nat) : Nat.ble n n = true := Nat.ble_eq.mpr (Nat.le_refl _)

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



theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

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

theorem topOf_append_congr {M L L' : List VeriDNS.Spec.Net.CacheRR} (h : topOf L = topOf L') :
    topOf (M ++ L) = topOf (M ++ L') := by
  rw [topOf_append_key, topOf_append_key, h]



theorem perm_foldl_eq {α β : Type} {f : β → α → β}
    (lcomm : ∀ b x y, f (f b x) y = f (f b y) x)
    {l1 l2 : List α} (h : l1.Perm l2) (acc : β) : l1.foldl f acc = l2.foldl f acc := by
  induction h generalizing acc with
  | nil => rfl
  | cons x h ih => exact ih (f acc x)
  | swap x y l => simp only [List.foldl_cons]; rw [lcomm acc x y]
  | trans h1 h2 ih1 ih2 => exact (ih1 acc).trans (ih2 acc)

theorem perm_all {α : Type} {L L' : List α} (f : α → Bool) (h : L.Perm L') : L.all f = L'.all f := by
  apply bool_ext
  rw [List.all_eq_true, List.all_eq_true]
  exact ⟨fun hL x hx => hL x (h.mem_iff.mpr hx), fun hL x hx => hL x (h.mem_iff.mp hx)⟩

theorem filter_self_perm {α : Type} {L L' : List α} (g : α → α → Bool) (h : L.Perm L') :
    (L.filter (fun e => L.all (g e))).Perm (L'.filter (fun e => L'.all (g e))) := by
  have hc : L.filter (fun e => L.all (g e)) = L.filter (fun e => L'.all (g e)) := by
    apply List.filter_congr
    intro e _
    rw [perm_all (g e) h]
  rw [hc]
  exact h.filter _

theorem topOf_perm {L L' : List VeriDNS.Spec.Net.CacheRR} (h : L.Perm L') :
    (topOf L).Perm (topOf L') := by
  unfold topOf
  have hcongr : L.filter (fun e => L.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
      = L.filter (fun e => L'.all (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) := by
    apply List.filter_congr; intro e _; rw [perm_all _ h]
  rw [hcongr]
  exact h.filter _

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

theorem topServed_absorb_congr (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name)
    (resp : VeriDNS.Spec.Net.Response) (now' : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    {c c' : VeriDNS.Spec.Net.Cache} (h : (c.topServed now' q).Perm (c'.topServed now' q)) :
    ((c.absorb now bw resp).topServed now' q).Perm ((c'.absorb now bw resp).topServed now' q) := by
  obtain ⟨M, hM⟩ := matching_absorb_append now bw resp now' q
  rw [topServed_eq_topOf, topServed_eq_topOf, hM c, hM c'] at *
  exact topOf_append_perm h



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

theorem absorbNeg_neg_append (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (resp : VeriDNS.Spec.Net.Response) :
    ∃ pre, ∀ (c : VeriDNS.Spec.Net.Cache), (c.absorbNeg now q resp).neg = pre ++ c.neg := by
  unfold VeriDNS.Spec.Net.Cache.absorbNeg
  cases VeriDNS.Spec.Net.soaNegTtl q.qname resp with
  | none => exact ⟨[], fun c => rfl⟩
  | some ttl =>
    by_cases h1 : (resp.rcode == VeriDNS.Spec.Net.RCode.nameError) = true
    · refine ⟨[⟨q.qname, none, now, min ttl VeriDNS.Spec.Net.maxNegativeTtl⟩],
        fun c => ?_⟩
      simp [h1]
    · by_cases h2 : (resp.rcode == VeriDNS.Spec.Net.RCode.noError && resp.answer.isEmpty) = true
      · refine ⟨[⟨q.qname, some q.qtype, now, min ttl VeriDNS.Spec.Net.maxNegativeTtl⟩],
          fun c => ?_⟩
        simp [h1, h2]
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

theorem MatchMaxEquiv.absorb {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    (now : VeriDNS.Spec.Net.Time) (bw : VeriDNS.Spec.Net.Name) (resp : VeriDNS.Spec.Net.Response) :
    MatchMaxEquiv (c.absorb now bw resp) (c'.absorb now bw resp) := by
  refine ⟨fun now' q => ?_, fun now' q => ?_, fun now' q => ?_⟩
  · exact topServed_absorb_congr now bw resp now' q (h.1 now' q)
  · rw [negHit_absorb, negHit_absorb]; exact h.2.1 now' q
  · rw [negHitNx_absorb, negHitNx_absorb]; exact h.2.2 now' q

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

theorem served_foldl_insert_nonusable_nil (now : Time) (q : Query) (cred : Cred)
    (huse : cred.usable = false) :
    ∀ (rs : List RR) (c : Cache), c.served now q = [] →
      (rs.foldl (fun a r => a.insert now cred r) c).served now q = [] := by
  intro rs
  induction rs with
  | nil => intro c h; exact h
  | cons r rest ih => intro c h; exact ih _ (served_insert_nonusable_nil c now q cred r huse h)

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

theorem insert_neg (c : Cache) (now : Time) (cred : Cred) (r : RR) :
    (c.insert now cred r).neg = c.neg := by
  unfold Cache.insert; by_cases hc : cacheable r <;> simp [hc]

theorem foldl_insert_neg (now : Time) (cred : Cred) :
    ∀ (rs : List RR) (c : Cache), ((rs.foldl (fun a r => a.insert now cred r) c).neg = c.neg) := by
  intro rs
  induction rs with
  | nil => intro c; rfl
  | cons r rest ih => intro c; rw [List.foldl_cons, ih, insert_neg]

theorem absorb_neg (c : Cache) (now : Time) (bw : Name) (resp : Response) :
    (c.absorb now bw resp).neg = c.neg := by
  unfold Cache.absorb
  simp only [foldl_insert_neg]

theorem absorb_negHit_eq (c : Cache) (now : Time) (bw : Name) (q : Query) (resp : Response) :
    (c.absorb now bw resp).negHit now q = c.negHit now q := by
  unfold Cache.negHit; rw [absorb_neg]

theorem MatchMaxEquiv.hit_nil {c c' : VeriDNS.Spec.Net.Cache} (h : MatchMaxEquiv c c')
    {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query} (hm : c.hit now q = []) :
    c'.hit now q = [] := by
  have hp := h.hit now q; rw [hm] at hp; exact (List.perm_nil.mp hp.symm)

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
  | gaveUp c slist q =>
    intro cc hmm
    exact ⟨cc, _, Resolves.gaveUp cc slist q, RespAgree.refl _, hmm⟩
  | loopDetected c slist q =>
    intro cc hmm
    exact ⟨cc, _, Resolves.loopDetected cc slist q, RespAgree.refl _, hmm⟩
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
          (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).1
          (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).2.1
          (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).2.2))
        cf hcf,
        RespAgree.refl _, MatchMaxEquiv.refl _⟩
    · exact ⟨cf, _, Resolves.trustedReply addr origin rest q id srcPort cc reply
        (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) htrans hacc hnr htc
        cc (Or.inr rfl) cf (hcf.trans_perm hmm.1 hmm.2.1 hmm.2.2),
        RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ (hmm.absorb _ _ reply.msg)

    exact ⟨cout', f', Resolves.refer addr rest q pq srv tr ref ftr rpath tEnd f' id srcPort cc cout'
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) hprobe
      hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono
      sl (((MatchMaxEquiv.referralSlist (hmm.absorb _ _ reply.msg) _ _ _).symm.subperm).trans hsl) hres, hrag, hmout⟩
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec _ih =>
    intro cc hmm

    exact ⟨cout, final, Resolves.referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort cc cout
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) hprobe
      hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono
      sl cf0 (hcf0.trans_perm (hmm.absorb _ _ reply.msg).1 (hmm.absorb _ _ reply.msg).2.1
        (hmm.absorb _ _ reply.msg).2.2)
      hsl cf hcf hrec, RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec _ih =>
    intro cc hmm

    exact ⟨cout, final, Resolves.trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort cc cout
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) hprobe
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
      cf0 (hcf0.trans_perm (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).1
        (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).2.1
        (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).2.2)
      cf hcf hrec,
      RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec _ih =>
    intro cc hmm
    exact ⟨cout, _, Resolves.trustedCname addr origin rest q cn target id srcPort cc nsl ftr rpath tEnd cout final
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss)
      reply htrans hacc hcn hqt htgt hfresh hmono htc
      cf0 (hcf0.trans_perm (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).1
        (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).2.1
        (hmm.absorb _ q.qname (reply.msg.answerOwned q.qname)).2.2)
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
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.rejectSpoof addr rest q pq ftr rpath tEnd f' cc cout' id srcPort reply hprobe hreject hres, hrag, hmout⟩
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.badResponse addr rest q pq ftr rpath tEnd f' cc cout' id srcPort reply hprobe htrans hacc hbad hres, hrag, hmout⟩
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply
      hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd f' cc cout' reply
      (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) hprobe
      hfind hans htrans hacc href hunfollow hres, hrag, hmout⟩
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
    intro cc hmm
    rcases hcf0 with hw | rfl
    · exact ⟨cf, _, Resolves.ancestorDenied addr origin rest q pq id srcPort cc reply
        (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) hprobe htrans hacc hrc htc
        cf0 (Or.inl (hw.trans_perm (hmm.absorbNeg _ pq reply.msg).1
          (hmm.absorbNeg _ pq reply.msg).2.1 (hmm.absorbNeg _ pq reply.msg).2.2))
        cf hcf,
        RespAgree.refl _, MatchMaxEquiv.refl _⟩
    · exact ⟨cf, _, Resolves.ancestorDenied addr origin rest q pq id srcPort cc reply
        (hmm.hit_nil hmiss) ((hmm.2.1 _ _).symm.trans hnmiss) hprobe htrans hacc hrc htc
        cc (Or.inr rfl) cf (hcf.trans_perm hmm.1 hmm.2.1 hmm.2.2),
        RespAgree.refl _, MatchMaxEquiv.refl _⟩
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih =>
    intro cc hmm
    obtain ⟨cout', f', hres, hrag, hmout⟩ := ih _ hmm
    exact ⟨cout', f', Resolves.chooseServer slist slist' q ftr rpath tEnd f' cc cout' hperm hres, hrag, hmout⟩

theorem hasVerdict_cache_congr {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState}
    {ra : String} {eb : Nat} {rtt : String → Nat} {now : VeriDNS.Spec.Net.Time}
    {nseen : List VeriDNS.Spec.Net.Name} {seen : List Name} {c c' : VeriDNS.Spec.Net.Cache}
    {slist : List String} {q : VeriDNS.Spec.Net.Query} {v : VeriDNS.Spec.Net.Response}
    (h : HasVerdict net ns ra eb rtt now nseen seen c slist q v) (hmm : MatchMaxEquiv c c') :
    HasVerdict net ns ra eb rtt now nseen seen c' slist q v := by
  obtain ⟨tr, sp, tEnd, cout, resp, hres, hag⟩ := h
  obtain ⟨cout', resp', hres', hrag, _⟩ := resolves_cache_congr hres c' hmm
  exact ⟨tr, sp, tEnd, cout', resp', hres', RespAgree.trans hag hrag⟩



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

theorem topOf_appendL_perm_appendR {L A B : List VeriDNS.Spec.Net.CacheRR} (h : A.Perm B) :
    (topOf (L ++ A)).Perm (topOf (B ++ L)) :=
  topOf_perm ((List.Perm.append_left L h).trans List.perm_append_comm)

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
theorem refer_hop_MatchMaxEquiv (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray)
    (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (aa : Bool) (haa : aa = false)
    (hcut : αName cut = some bwN) (htc : (resp.header.tc == 1) = false)
    (href : (αResp resp).isReferral = true)
    (h1 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr (VeriDNS.Impl.Resolver.credAuthority aa) now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAuthority aa, now⟩)
    (h2 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr VeriDNS.Impl.Resolver.credAdditional now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩)
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
theorem answerCname_hop_MatchMaxEquiv (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format) (sname : ByteArray)
    (bwN : VeriDNS.Spec.Net.Name) (now : UInt32) (hcut : αName sname = some bwN)
    (hsc : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo bwN)
    (hsv : ∀ x ∈ bwN, x.size ≤ 63)
    (htc : (resp.header.tc == 1) = false)
    (h1 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1), now⟩)
    (hnoA : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer), RRCanonMappable e) :
    MatchMaxEquiv
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)
          (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now))
      ((αCache c).absorb now.toNat bwN ((αResp resp).answerOwned bwN)) := by
  have hI := cacheRRs_αCache_pos (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer))
    (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now c h1
  rw [cacheUnlessTruncated_untruncated _ _ _ _ _ htc]
  have hM := absorb_answerOwned_pos (αCache c) now.toNat bwN (αResp resp)
  have hsec := section_owner_extra_perm resp.answer sname bwN (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now hcut hsc hsv hnoA hcanmap
  rw [αCred_credAnswer] at hsec
  refine ⟨fun nowT q' => ?_, fun nowT q' => ?_, fun nowT q' => ?_⟩
  · refine topServed_bridge_pos (αCache c) _ _ _ _ nowT q' hI ?_ hsec
    show ((αCache c).absorb now.toNat bwN ((αResp resp).answerOwned bwN)).pos = _
    rw [hM]; rfl
  · show VeriDNS.Spec.Net.Cache.negHit _ nowT q' = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHit
    rw [cacheRRs_negatives, VeriDNS.Spec.Net.absorb_neg]
  · show VeriDNS.Spec.Net.Cache.negHitNx _ nowT q' = _
    unfold αCache VeriDNS.Spec.Net.Cache.negHitNx
    rw [cacheRRs_negatives, VeriDNS.Spec.Net.absorb_neg]


def StateModels (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState) (ra : String)
    (ednsBuf : Nat) (rttOf : String → Nat) (now : VeriDNS.Spec.Net.Time) (q : VeriDNS.Spec.Net.Query)
    (state : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (c : VeriDNS.Spec.Net.Cache) (w : World) : Prop :=
  MatchMaxEquiv (αCache state.resources.cache) c
  ∧ αName state.resources.sname = some q.qname
  ∧ αTime state.now = now
  ∧ WorldModels net ns ra ednsBuf now w

theorem StateModels_swap_to_αCache
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : World}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w) :
    StateModels net ns ra ednsBuf rttOf now q state (αCache state.resources.cache) w :=
  ⟨MatchMaxEquiv.refl _, old.2⟩

def CacheWf (c : VeriDNS.Impl.Cache.DnsCache) (now : UInt32) : Prop :=
  (∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
      ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
  ∧ (∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
      e.rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
  ∧ (∀ e ∈ c.records, e.credibility = VeriDNS.Spec.Trustworthiness.authoritativeSection
      ∨ e.credibility = VeriDNS.Spec.Trustworthiness.authoritySection
      ∨ e.credibility = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
      ∨ e.credibility = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)

theorem CacheWf_mono {c c' : VeriDNS.Impl.Cache.DnsCache} {now : UInt32}
    (hsub : ∀ e ∈ c'.records, e ∈ c.records) (h : CacheWf c now) : CacheWf c' now :=
  ⟨fun e he => h.1 e (hsub e he), fun e he => h.2.1 e (hsub e he), fun e he => h.2.2 e (hsub e he)⟩

theorem CacheWf_empty (now : UInt32) : CacheWf VeriDNS.Impl.Cache.DnsCache.empty now :=
  ⟨fun _ he => absurd he (by simp [VeriDNS.Impl.Cache.DnsCache.empty]),
   fun _ he => absurd he (by simp [VeriDNS.Impl.Cache.DnsCache.empty]),
   fun _ he => absurd he (by simp [VeriDNS.Impl.Cache.DnsCache.empty])⟩

def entKeyB (e : VeriDNS.Impl.Cache.CacheEntry) (rr : VeriDNS.Spec.ResourceRecord) : Bool :=
  VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class

theorem entKeyB_trans {e f : VeriDNS.Impl.Cache.CacheEntry} {rr : VeriDNS.Spec.ResourceRecord}
    (h1 : entKeyB e f.rr = true) (h2 : entKeyB f rr = true) : entKeyB e rr = true := by
  unfold entKeyB at h1 h2 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  exact ⟨⟨VeriDNS.Proof.NameTree.nameEqCI_trans h1.1.1 h2.1.1, h1.1.2.trans h2.1.2⟩,
    h1.2.trans h2.2⟩

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

theorem warm_foldl_decomp (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
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
                ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := rfl
          obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := ih (c.store rr now cred)
          have hlist : (c.store rr now cred).records.toList
              = c.records.toList.filter (fun e => !(entKeyB e rr
                  && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata)))
                ++ [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩] := by
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
            List.filter Q [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩] ++ P, ?_, ?_, ?_, ?_⟩
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
              · have hpz : p = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :=
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
                by_cases hQz : Q ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = true
                · refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩, List.mem_append_left _ ?_, hek⟩
                  exact List.mem_filter.mpr
                    ⟨List.mem_singleton_self (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :
                      VeriDNS.Impl.Cache.CacheEntry), hQz⟩
                · have hmemz : (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :
                      VeriDNS.Impl.Cache.CacheEntry) ∈ (c.store rr now cred).records.toList := by
                    rw [hlist]
                    exact List.mem_append_right _ (List.mem_singleton_self _)
                  obtain ⟨p, hp, hpk⟩ := hD _ hmemz (by simpa using hQz)
                  exact ⟨p, List.mem_append_right _ hp, entKeyB_trans hek hpk⟩

            ·
              have hek : entKeyB e rr = true := by
                rw [Bool.not_eq_false', Bool.and_eq_true] at hkeep
                exact hkeep.1
              by_cases hQz : Q ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = true
              · refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩, List.mem_append_left _ ?_, hek⟩
                exact List.mem_filter.mpr
                  ⟨List.mem_singleton_self (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :
                    VeriDNS.Impl.Cache.CacheEntry), hQz⟩
              · have hmemz : (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :
                    VeriDNS.Impl.Cache.CacheEntry) ∈ (c.store rr now cred).records.toList := by
                  rw [hlist]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
                obtain ⟨p, hp, hpk⟩ := hD _ hmemz (by simpa using hQz)
                exact ⟨p, List.mem_append_right _ hp, entKeyB_trans hek hpk⟩
theorem entKeyB_symm {e f : VeriDNS.Impl.Cache.CacheEntry} (h : entKeyB e f.rr = true) :
    entKeyB f e.rr = true := by
  unfold entKeyB at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨⟨VeriDNS.Proof.NameTree.nameEqCI_symm h.1.1, h.1.2.symm⟩, h.2.symm⟩

theorem mem_flatMap_pushOf {l : List ByteArray} {cred : VeriDNS.Spec.Trustworthiness} {now : UInt32}
    {p : VeriDNS.Impl.Cache.CacheEntry} (hp : p ∈ l.flatMap (pushOf cred now)) :
    ∃ b ∈ l, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
      ∧ (rr.ttl == 0) = false
      ∧ p = ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := by
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

theorem mem_modelPushOf {now : VeriDNS.Spec.Net.Time} {cred : VeriDNS.Spec.Net.Cred}
    {r : VeriDNS.Spec.Net.RR} {x : VeriDNS.Spec.Net.CacheRR} (hx : x ∈ modelPushOf now cred r) :
    x.cred = cred ∧ x.insertedAt = now := by
  unfold modelPushOf at hx
  split at hx
  · rw [List.mem_singleton.mp hx]; exact ⟨rfl, rfl⟩
  · exact absurd hx (by simp)

theorem ble_additional_rank (c : VeriDNS.Spec.Net.Cred) :
    Nat.ble (VeriDNS.Spec.Net.Cred.additional.rank) c.rank = true := by
  rw [Nat.ble_eq]
  exact Nat.zero_le _

theorem topGate_of_ranks {m : List VeriDNS.Spec.Net.CacheRR} {a : VeriDNS.Spec.Net.CacheRR}
    (h : ∀ x ∈ m, x.sameKey a.rr = true → Nat.ble x.cred.rank a.cred.rank = true) :
    (m.all fun e2 => !(e2.sameKey a.rr) || Nat.ble e2.cred.rank a.cred.rank) = true := by
  rw [List.all_eq_true]
  intro x hx
  by_cases hk : x.sameKey a.rr = true
  · rw [hk, h x hx hk]; rfl
  · rw [Bool.not_eq_true] at hk; rw [hk]; rfl

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

  have hPfacts : ∀ p ∈ P, ∃ rr, p = (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩ : VeriDNS.Impl.Cache.CacheEntry)
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
        have hmemP : (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩ : VeriDNS.Impl.Cache.CacheEntry) ∈ (((VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)).toList
      ++ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList).foldl (warmStep VeriDNS.Impl.Resolver.credAdditional now) c).records := by
          rw [Array.mem_def, hdec]
          exact List.mem_append_right _ hpP
        have hsk : VeriDNS.Proof.NameTree.SameKey ea.rr rr := by
          have hk := hkey
          unfold entKeyB at hk
          rw [Bool.and_eq_true, Bool.and_eq_true] at hk
          exact ⟨hk.1.1, eq_of_beq hk.1.2, eq_of_beq hk.2⟩
        have hexpEq : ea.expiry = now + rr.ttl.toNat.toUInt32 :=
          hoe2 ea hmemEA (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩ : VeriDNS.Impl.Cache.CacheEntry) hmemP hsk
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
        have hle : (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.ttl.toNat ≤ (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩ : VeriDNS.Impl.Cache.CacheEntry).expiry.toNat := by
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
      have hcanonP : (⟨rr, now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner := by
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

theorem CacheWf_boundExpiryClasses (c : VeriDNS.Impl.Cache.DnsCache) (now : UInt32)
    (h : CacheWf c now) : CacheWf c.boundExpiryClasses now := by
  refine CacheWf_mono (c := c) ?_ h
  intro e he
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp] at he
  exact (Array.mem_filter.mp he).1

theorem CacheWf_touchKeys (c : VeriDNS.Impl.Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow now : UInt32) (h : CacheWf c now) : CacheWf (c.touchKeys ks tnow) now := by
  have hmem : ∀ e ∈ (c.touchKeys ks tnow).records,
      ∃ e₀, e₀ ∈ c.records ∧ e = VeriDNS.Impl.Cache.touchEntry ks tnow e₀ := by
    intro e he
    rw [VeriDNS.Impl.Cache.touchKeys_records] at he
    obtain ⟨e₀, he₀, hmap⟩ := Array.mem_map.mp he
    exact ⟨e₀, he₀, hmap.symm⟩
  refine ⟨?_, ?_, ?_⟩ <;> intro e he <;>
    obtain ⟨e₀, he₀, heq⟩ := hmem e he <;>
    rcases VeriDNS.Impl.Cache.touchEntry_cases ks tnow e₀ with h' | h' <;>
    rw [heq, h']
  · exact h.1 e₀ he₀
  · exact h.1 e₀ he₀
  · exact h.2.1 e₀ he₀
  · exact h.2.1 e₀ he₀
  · exact h.2.2 e₀ he₀
  · exact h.2.2 e₀ he₀

theorem CacheWf_boundLruKeys (c : VeriDNS.Impl.Cache.DnsCache) (now : UInt32)
    (h : CacheWf c now) : CacheWf c.boundLruKeys now := by
  refine CacheWf_mono (c := c) ?_ h
  intro e he
  unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  rw [hp] at he
  exact (Array.mem_filter.mp he).1

theorem CacheWf_boundLru (c : VeriDNS.Impl.Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow now : UInt32) (h : CacheWf c now) : CacheWf (c.boundLru ks tnow) now :=
  CacheWf_boundLruKeys _ now (CacheWf_touchKeys c ks tnow now h)

theorem CacheWf_storeChecked (c : VeriDNS.Impl.Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheWf c now)
    (hwfNew : (αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome
        ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
        ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
    (hcanonNew : ∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = some a →
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
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := rfl
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

theorem CacheWf_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative) :
    ∀ (l : List ByteArray) (cache : VeriDNS.Impl.Cache.DnsCache), CacheWf cache now →
      (∀ bytes ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome
            ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
            ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
          ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = some a →
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

theorem CacheWf_cacheRRs (cache : VeriDNS.Impl.Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheWf cache now)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome
            ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
            ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
          ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = some a →
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

theorem CacheWf_cacheUnlessTruncated (cache : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheWf cache now)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hraw : ∀ bytes ∈ (VeriDNS.Impl.Cache.normRaws raws).toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome
            ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
            ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
          ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = some a →
              rr.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))) :
    CacheWf (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) now := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]; exact CacheWf_cacheRRs cache _ cred now h hcred hraw

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
        have hmemz : (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :
            VeriDNS.Impl.Cache.CacheEntry) ∈ (c.store rr now cred).records.toList := by
          show _ ∈ ((c.records.filter _).push _).toList
          rw [Array.toList_push]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hkeyz : entKeyB (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ :
            VeriDNS.Impl.Cache.CacheEntry) rr = true := by
          unfold entKeyB
          rw [VeriDNS.Proof.NameTree.nameEqCI_refl]
          simp
        obtain ⟨Q, P, hdec, hsub, hB, hD⟩ := warm_foldl_decomp cred now rest (c.store rr now cred)
        by_cases hQz : Q ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = true
        · refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩, ?_, hkeyz, Nat.le_refl _⟩
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
      ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome
          ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
          ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
        ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = some a →
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

  have hPfacts : ∀ p ∈ P, ∃ rr, p = (⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry)
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
        have hcanPe : (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name
            = VeriDNS.Impl.DomainName.labelsToWireFormatGo x.rr.owner := by
          show rrx.name = _
          rw [hcanon, hnaEq]
        have h63Pe : ∀ lb ∈ x.rr.owner, lb.size ≤ 63 := by
          rw [← hnaEq]; exact h63
        have hkPeEnt : entKeyB (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry) ent.rr = true :=
          entKeyB_of_sameKey hpeα hentα hcanPe h63Pe
            (hwfW.2.1 ent hentR a hentα).1 (hwfW.2.1 ent hentR a hentα).2 hkx
        obtain ⟨e, heL, hek, hle⟩ := warm_foldl_key_covered cred now (VeriDNS.Impl.Cache.normRaws raws).toList c hno braw hbrawL rrx hprx hzx
        have heW : e ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records := Array.mem_def.mpr heL
        have hkE : entKeyB e ent.rr = true :=
          entKeyB_trans (show entKeyB e (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr = true from hek) hkPeEnt
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
      have hcanPe : (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name
          = VeriDNS.Impl.DomainName.labelsToWireFormatGo x.rr.owner := by
        show rrx.name = _
        rw [hcanon, hnaEq]
      have h63Pe : ∀ lb ∈ x.rr.owner, lb.size ≤ 63 := by
        rw [← hnaEq]; exact h63
      have hkPeEnt : entKeyB (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry) ent.rr = true :=
        entKeyB_of_sameKey hpeα hentα hcanPe h63Pe
          (hwfW.2.1 ent hentR a hentα).1 (hwfW.2.1 ent hentR a hentα).2 hkx
      obtain ⟨e, heL, hek, hle⟩ := warm_foldl_key_covered cred now (VeriDNS.Impl.Cache.normRaws raws).toList c hno braw hbrawL rrx hprx hzx
      have heW : e ∈ ((VeriDNS.Impl.Cache.normRaws raws).toList.foldl (warmStep cred now) c).records := Array.mem_def.mpr heL
      have hkE : entKeyB e ent.rr = true :=
        entKeyB_trans (show entKeyB e (⟨rrx, now + rrx.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr = true from hek) hkPeEnt
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
        have hpW : (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry)
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
          hoeW ea heaW (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry) hpW hsk
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
          have hkPEnt : entKeyB (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry) ent.rr = true :=
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
        have hle : (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.ttl.toNat
            ≤ (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).expiry.toNat := by
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
      have hcanonP : (⟨rrp, now + rrp.ttl.toNat.toUInt32, false, cred, now⟩ : VeriDNS.Impl.Cache.CacheEntry).rr.name
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

theorem cname_write_WriteRefines (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (sname : ByteArray) (bwN : VeriDNS.Spec.Net.Name) (now : UInt32)
    (hcut : αName sname = some bwN)
    (hsc : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo bwN)
    (hsv : ∀ x ∈ bwN, x.size ≤ 63)
    (htc : (resp.header.tc == 1) = false)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer), RRCanonMappable e) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)
        (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now))
      ((αCache c).absorb now.toNat bwN ((αResp resp).answerOwned bwN)) := by
  have hsec := section_owner_extra_perm resp.answer sname bwN
    (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now hcut hsc hsv hno hcanmap
  rw [αCred_credAnswer] at hsec
  have hMpos : ((αCache c).absorb now.toNat bwN ((αResp resp).answerOwned bwN)).pos
      = ((VeriDNS.Spec.Net.normalizeTTL ((αSection resp.answer).filter (fun r => VeriDNS.Spec.Net.nameEq r.owner bwN))).reverse.flatMap
          (modelPushOf now.toNat
            (if (resp.header.aa == 1) then VeriDNS.Spec.Net.Cred.authoritative else VeriDNS.Spec.Net.Cred.glue)))
        ++ (αCache c).pos :=
    absorb_answerOwned_pos (αCache c) now.toNat bwN (αResp resp)
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

theorem cname_write_WriteRefines_ref (c : VeriDNS.Impl.Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (sname : ByteArray) (bwN : VeriDNS.Spec.Net.Name) (now : UInt32)
    (hcut : αName sname = some bwN)
    (hsc : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo bwN)
    (hsv : ∀ x ∈ bwN, x.size ≤ 63)
    (htc : (resp.header.tc == 1) = false)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer), RRCanonMappable e)
    (ref : VeriDNS.Spec.Net.Response) (cm : VeriDNS.Spec.Net.Cache)
    (hansEq : αSection resp.answer = ref.answer)
    (haaEq : (resp.header.aa == 1) = ref.aa)
    (hmme : MatchMaxEquiv (αCache c) cm) :
    WriteRefines now.toNat
      (αCache (VeriDNS.Impl.Resolver.cacheUnlessTruncated (C := VeriDNS.Impl.Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (VeriDNS.Impl.Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname resp.answer)
        (VeriDNS.Impl.Resolver.credAnswer (resp.header.aa == 1)) now))
      (cm.absorb now.toNat bwN (ref.answerOwned bwN)) := by
  have h0 := cname_write_WriteRefines c resp sname bwN now hcut hsc hsv htc hwf hoe hval hno hcanmap
  have hcongr : (αCache c).absorb now.toNat bwN ((αResp resp).answerOwned bwN)
      = (αCache c).absorb now.toNat bwN (ref.answerOwned bwN) :=
    VeriDNS.Spec.Net.absorb_resp_congr _ _ _
      (by simp only [VeriDNS.Spec.Net.Response.answerOwned_aa]; exact haaEq)
      (by simp only [VeriDNS.Spec.Net.Response.answerOwned_answer]
          rw [show (αResp resp).answer = αSection resp.answer from rfl, hansEq]) rfl rfl
  rw [hcongr] at h0
  have hmabs := hmme.absorb now.toNat bwN (ref.answerOwned bwN)
  exact h0.trans_perm hmabs.1 hmabs.2.1 hmabs.2.2

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

theorem matchMaxEquiv_absorb_step {c1 c2 c : VeriDNS.Spec.Net.Cache} {now : VeriDNS.Spec.Net.Time}
    {bw : VeriDNS.Spec.Net.Name} {resp : VeriDNS.Spec.Net.Response}
    (hbridge : MatchMaxEquiv c1 (c2.absorb now bw resp)) (hold : MatchMaxEquiv c2 c) :
    MatchMaxEquiv c1 (c.absorb now bw resp) :=
  hbridge.trans (hold.absorb now bw resp)

theorem matchMaxEquiv_absorbNeg_step {c1 c2 c : VeriDNS.Spec.Net.Cache} {now : VeriDNS.Spec.Net.Time}
    {q : VeriDNS.Spec.Net.Query} {resp : VeriDNS.Spec.Net.Response}
    (hbridge : MatchMaxEquiv c1 (c2.absorbNeg now q resp)) (hold : MatchMaxEquiv c2 c) :
    MatchMaxEquiv c1 (c.absorbNeg now q resp) :=
  hbridge.trans (hold.absorbNeg now q resp)

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
        (acc.storeChecked rr (VeriDNS.Impl.Resolver.credAuthority aa) state.now).records = acc.records.push ⟨rr, state.now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAuthority aa, state.now⟩)
    (h2 : ∀ (acc : VeriDNS.Impl.Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (VeriDNS.Impl.Cache.normRaws (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr VeriDNS.Impl.Resolver.credAdditional state.now).records = acc.records.push ⟨rr, state.now + rr.ttl.toNat.toUInt32, false, VeriDNS.Impl.Resolver.credAdditional, state.now⟩)
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

theorem StateModels_answerCname_preserve
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : VeriDNS.Spec.Net.Time} {q : VeriDNS.Spec.Net.Query}
    {state stateB : VeriDNS.Impl.Resolver.State VeriDNS.Impl.SList.DnsSList VeriDNS.Impl.Cache.DnsCache
      VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {c : VeriDNS.Spec.Net.Cache} {w : VeriDNS.Proof.FreeIO.World} {bwN : VeriDNS.Spec.Net.Name}
    {resp : VeriDNS.Spec.Format} {target : VeriDNS.Spec.Net.Name}
    (old : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hbridge : MatchMaxEquiv (αCache stateB.resources.cache)
        ((αCache state.resources.cache).absorb now bwN ((αResp resp).answerOwned bwN)))
    (hsnameNew : αName stateB.resources.sname = some target)
    (hnow : stateB.now = state.now) :
    StateModels net ns ra ednsBuf rttOf now { q with qname := target } stateB
      (c.absorb now bwN ((αResp resp).answerOwned bwN)) w := by
  refine ⟨matchMaxEquiv_absorb_step hbridge old.1, hsnameNew, hnow ▸ old.2.2.1, old.2.2.2⟩

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
