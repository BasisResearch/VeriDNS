import VeriDNS.Proof.ResolveWithIOSound
import VeriDNS.Proof.TcpFraming




open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache VeriDNS.Spec
open VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message

theorem serveTcpDatagram_served
    (connSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray) (query : VeriDNS.Spec.Format)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none) :
    Server.serveTcpDatagram (M := Prog) (Sock := Unit) connSock acl sbelt cache queryBytes clientAddr
      = (do
        let nowT ← VeriDNS.Spec.UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)
        let (resolveResult, cache') ← Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache nowT
        let (response, cache'') ← Server.replyForResolution (M := Prog) (Sock := Unit)
          query resolveResult cache' nowT
        VeriDNS.Spec.UdpSocket.tcpSend (M := Prog) (Sock := Unit) (Addr := ByteArray) connSock
          (VeriDNS.Impl.TcpFraming.frameTcp (VeriDNS.Impl.Message.encode response))
        pure (cache''.boundLru (Server.serveTouches query sbelt cache nowT) nowT)) := by
  unfold Server.serveTcpDatagram
  simp [hperm, hdec, hqp, -Prog.bind_def, -Prog.pure_def]
  intro h
  exact absurd h (by simpa using hqr)


theorem serveTcpDatagram_verdict_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (queryBytes clientAddr : ByteArray)
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (cache : DnsCache) (w w' : World) (cacheOut : DnsCache)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqrbit : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqany : qu.qtype.toNat ≠ 255)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hqvalid : ∀ x ∈ qm.qname, 0 < x.size ∧ x.size ≤ 63)
    (hqlen : qm.qname.length ≤ 127)
    (hrd : qm.rd = false) (hqstar : qm.qtype ≠ QType.star) (hqin : qm.qclass = RRClass.in)
    (hCacheWf : CacheWf cache w.clock) (hNsCanon : CacheNsCanon cache)
    (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache)
    (hCap : cache.records.size ≤ DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hRecC : VeriDNS.Proof.DeliveredWire.CacheRecCanon cache)
    (hNegSoaC : VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cache)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w)
    (hrun : Prog.run n (Server.serveTcpDatagram (M := Prog) (Sock := Unit)
        clientSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w')) :
    ∃ (m : Nat) (rr : Except String VeriDNS.Spec.Format) (cache' : DnsCache) (w₂ : World),
      Prog.run m (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache w.clock) w = some ((rr, cache'), w₂)
      ∧ ((∃ msg, rr = .error msg
            ∧ (∃ slist v,
                HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] []
                  (αCache cache) slist qm v (αCache cache)
                ∧ v.rcode = RCode.servFail ∧ v.answer = [])
            ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w₂
            ∧ CacheWf cache' w.clock
            ∧ CacheNsCanon cache'
            ∧ CacheCnameCanon cache'
            ∧ (∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
            ∧ CacheNegWf cache' qu.qclass
            ∧ CacheNsDistinct cache'
            ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache'
            ∧ cache'.records.size ≤ DnsCache.capacity
            ∧ (CacheWf cacheOut w.clock ∧ CacheNsCanon cacheOut ∧ CacheCnameCanon cacheOut
                ∧ (∀ e ∈ cacheOut.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                ∧ CacheNegWf cacheOut qu.qclass ∧ CacheNsDistinct cacheOut
                ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cacheOut
                ∧ cacheOut.records.size ≤ DnsCache.capacity
                ∧ VeriDNS.Proof.DeliveredWire.CacheRecCanon cacheOut
                ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cacheOut))
        ∨ (∃ resp slist v cOut coutM,
            rr = .ok resp
            ∧ resp.question[0]? = some qu
            ∧ CacheRefines cOut (αCache cache)
            ∧ HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] [] cOut slist qm v coutM
            ∧ (αResp (Server.deliveredResponse query resp)).rcode = v.rcode
            ∧ (αResp (Server.deliveredResponse query resp)).answer
                = VeriDNS.Spec.Net.scrubAnswer qm.qname v.answer
            ∧ CacheRefines (αCache cache') coutM
            ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w₂
            ∧ CacheWf cache' w.clock
            ∧ CacheNsCanon cache'
            ∧ CacheCnameCanon cache'
            ∧ (∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
            ∧ CacheNegWf cache' qu.qclass
            ∧ CacheNsDistinct cache'
            ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache'
            ∧ cache'.records.size ≤ DnsCache.capacity
            ∧ (CacheWf cacheOut w.clock ∧ CacheNsCanon cacheOut ∧ CacheCnameCanon cacheOut
                ∧ (∀ e ∈ cacheOut.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                ∧ CacheNegWf cacheOut qu.qclass ∧ CacheNsDistinct cacheOut
                ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cacheOut
                ∧ cacheOut.records.size ≤ DnsCache.capacity
                ∧ VeriDNS.Proof.DeliveredWire.CacheRecCanon cacheOut
                ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cacheOut)
            ∧ ((VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp)).size ≤ 65535 →
                VeriDNS.Impl.TcpFraming.unframeTcp
                    (VeriDNS.Impl.TcpFraming.frameTcp
                      (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp)))
                  = some (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                ∧ VeriDNS.Impl.Message.decode
                    (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                  = .ok (Server.deliveredResponse query resp)))) := by
  rw [serveTcpDatagram_served clientSock acl sbelt cache queryBytes clientAddr query
    hperm hdec hqrbit hqp] at hrun
  obtain ⟨m0, rfl, hrun2⟩ := run_now_bind_inv _ w hrun
  clear hrun
  obtain ⟨m₁, m₂, x, w₂, hle, hrunRes, hrunK⟩ := run_bind_inv hrun2
  obtain ⟨rr, cache'⟩ := x
  refine ⟨m₁, rr, cache', w₂, hrunRes, ?_⟩
  have hq16 : query.question.size < 65536 := by
    have h1 := (VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec).1
    have h2 := query.header.qdcount.isLt
    have h216 : 2 ^ 16 = 65536 := rfl
    omega
  cases rr with
  | error msg =>
    obtain ⟨hWM', hwf1', hwf2', hwf3', hwf4', hwf5', hwf6', hwf7', hwf8'⟩ :=
      resolveWithIO_error_sound net ns ra ednsBuf rttOf sbelt 5 hnetWF hGlSbelt
        m₁ query qu qm.qname t 6 40 cache w w₂ w.clock msg cache'
        hqu hqm hcanon ht hqany (by have h := hqc; rw [hqin] at h; exact h)
        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hclock hw hwTcp hrunRes
    obtain ⟨hrecC', hnegC'⟩ :=
      resolveWithIO_error_sections m₁ query sbelt cache w.clock 40 6 5 w w₂ msg cache'
        hq16 hRecC hNegSoaC hrunRes
    have hV : ∃ slist v,
        HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] []
          (αCache cache) slist qm v (αCache cache)
        ∧ v.rcode = RCode.servFail ∧ v.answer = [] := by
      by_cases hm1 : msg = "cname chain too long"
      · exact ⟨[], _, VeriDNS.Proof.WorldNetwork.loopDetected_hasVerdictAt net ns ra ednsBuf
          rttOf (αCache cache) [] qm
          { aa := false, rcode := RCode.servFail, answer := [], authority := [],
            additional := [] } rfl rfl, rfl, rfl⟩
      by_cases hm2 : msg = "cname loop detected"
      · exact ⟨[], _, VeriDNS.Proof.WorldNetwork.loopDetected_hasVerdictAt net ns ra ednsBuf
          rttOf (αCache cache) [] qm
          { aa := false, rcode := RCode.servFail, answer := [], authority := [],
            additional := [] } rfl rfl, rfl, rfl⟩
      by_cases hm3 : msg = "resolveWithIO: no servers with addresses in SLIST"
      · exact ⟨[], _, VeriDNS.Proof.WorldNetwork.exhausted_hasVerdictAt net ns ra ednsBuf
          rttOf (αCache cache) qm
          { aa := false, rcode := RCode.servFail, answer := [], authority := [],
            additional := [] } rfl rfl, rfl, rfl⟩
      · exact ⟨[], _, VeriDNS.Proof.WorldNetwork.gaveUp_hasVerdictAt net ns ra ednsBuf
          rttOf (αCache cache) [] qm
          { aa := false, rcode := RCode.servFail, answer := [], authority := [],
            additional := [] } rfl rfl, rfl, rfl⟩
    obtain ⟨m₃, m₄, y, w₃, hle2, hrunReply, hrunTail⟩ := run_bind_inv hrunK
    obtain ⟨response, cache''⟩ := y
    obtain ⟨-, hcE⟩ := replyForResolution_run_err_inv hrunReply
    rw [hcE] at hrunTail
    dsimp only at hrunTail
    obtain ⟨m₅, m₆, u, w₄, hle3, hrunSend, hrunPure⟩ := run_bind_inv hrunTail
    have hrunPure' : Prog.run m₆ (pure (cache'.boundLru
          (Server.serveTouches query sbelt cache w.clock) w.clock) : Prog DnsCache) w₄
        = some (cacheOut, w') := hrunPure
    rw [run_pure'] at hrunPure'
    obtain ⟨rfl, rfl⟩ : cache'.boundLru
          (Server.serveTouches query sbelt cache w.clock) w.clock = cacheOut ∧ w₄ = w' := by
      simpa using hrunPure'
    exact Or.inl ⟨msg, rfl, hV, hWM', hwf1', hwf2', hwf3', hwf4', hwf5', hwf6', hwf7', hwf8',
      CacheWf_boundLru _ _ _ _ hwf1',
      CacheNsCanon_boundLru _ _ _ hwf2',
      CacheCnameCanon_boundLru _ _ _ hwf3',
      wfrrAll_boundLru _ _ hwf4',
      CacheNegWf_boundLru _ _ hwf5',
      CacheNsDistinct_boundLru _ _ _ hwf6',
      VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hwf7',
      VeriDNS.Proof.Cache.boundLru_bounded _ _ _,
      VeriDNS.Proof.DeliveredWire.cacheRecCanon_boundLru _ _ _ hrecC',
      cacheNegSoaCanon_boundLru _ _ _ hnegC'⟩
  | ok resp =>
    obtain ⟨slist, v, cOut, coutM, hcOutR, hHV, hrc, hans, hCR, hWM, hwf1, hwf2, hwf3, hwf4,
        hwf5, hwf6, hwf7, hwf8⟩ :=
      resolveWithIO_verdict_sound net ns ra ednsBuf rttOf sbelt 5 hnetWF hGlSbelt
        m₁ query qu qm t 6 40 cache w w₂ w.clock resp cache'
        hqu hqm hcanon ht hqany hqq hqc hqvalid hqlen hrd hqstar hqin
        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hclock hw hwTcp hrunRes
    have hq0 : resp.question[0]? = some qu := by
      rw [resolveWithIO_ok_question m₁ query sbelt cache w.clock 40 6 5 w w₂ resp cache' hrunRes]
      exact hqu
    obtain ⟨⟨⟨hca, hcn, hcd, hnsc, harc⟩, hqdc⟩, hrecOut, hnegOut⟩ :=
      resolveWithIO_ok_sections m₁ query sbelt cache w.clock 40 6 5 w w₂ resp cache'
        hq16 hRecC hNegSoaC hrunRes
    obtain ⟨h0lt, h0eq⟩ := Array.getElem?_eq_some_iff.mp hqu
    have hqf0 : VeriDNS.Proof.Message.QuestionFromLabels qu := by
      have hqf := (VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec).2.2.2.2.1 ⟨0, h0lt⟩
      simp only [Fin.getElem_fin] at hqf
      rwa [h0eq] at hqf
    have hq255 : qu.qname.size ≤ 255 := by
      obtain ⟨ls, hv, hle, heq⟩ := hqf0
      rw [← heq]
      exact hle
    have hqn : VeriDNS.Proof.DeliveredWire.CanonicalName (Server.clientQname query) := by
      have hclientq : Server.clientQname query = qu.qname := by
        unfold Server.clientQname
        rw [hqu]
        rfl
      rw [hclientq]
      exact VeriDNS.Proof.DeliveredWire.canonicalName_of_questionFromLabels hqf0
    refine Or.inr ⟨resp, slist, v, cOut, coutM, rfl, hq0, hcOutR, hHV,
      (deliveredResponse_abstracts_rcode query resp).trans hrc,
      (by rw [deliveredResponse_answer_exact hqu hqm hcanon
        hqvalid hq255 hca hwf8.2, hans]),
      hCR, hWM, hwf1, hwf2, hwf3, hwf4, hwf5, hwf6, hwf7, hwf8.1, ?_, ?_⟩
    · have hrw : RespWriteWf query resp w.clock := respWriteWf_of_answerWriteWf hwf8.2
      obtain ⟨m₃, m₄, y, w₃, hle2, hrunReply, hrunTail⟩ := run_bind_inv hrunK
      obtain ⟨response, cache''⟩ := y
      dsimp only at hrunTail
      obtain ⟨m₅, m₆, u, w₄, hle3, hrunSend, hrunPure⟩ := run_bind_inv hrunTail
      have hrunPure' : Prog.run m₆ (pure (cache''.boundLru
            (Server.serveTouches query sbelt cache w.clock) w.clock) : Prog DnsCache) w₄
          = some (cacheOut, w') := hrunPure
      rw [run_pure'] at hrunPure'
      obtain ⟨rfl, rfl⟩ : cache''.boundLru
            (Server.serveTouches query sbelt cache w.clock) w.clock = cacheOut ∧ w₄ = w' := by
        simpa using hrunPure'
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := replyPath_cacheOut_wf
        (Server.serveTouches query sbelt cache w.clock) w.clock qu hrunReply hrw hq0
        ⟨qm.qname, hqm, hcanon, fun x hx => (hqvalid x hx).2⟩
        hwf1 hwf2 hwf3 hwf4 hwf6 hwf7 hwf5
      obtain ⟨c1, c2⟩ := replyPath_cacheOut_canon hrunReply
        (Server.serveTouches query sbelt cache w.clock) w.clock hca hcn hrecOut hnegOut
      exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, c1, c2⟩
    · intro hfits
      have hqe : resp.question = query.question :=
        resolveWithIO_ok_question m₁ query sbelt cache w.clock 40 6 5 w w₂ resp cache' hrunRes
      constructor
      · exact VeriDNS.Proof.TcpFraming.unframeTcp_frameTcp _ hfits
      · refine VeriDNS.Proof.DeliveredWire.deliveredResponse_decode_encode query resp
          hqdc hnsc harc ?_ hqn ?_ hca hcn hcd
        · have hcs : VeriDNS.Proof.DeliveredWire.CanonicalSection
              (Server.deliveredResponse query resp).answer :=
            VeriDNS.Proof.DeliveredWire.canonicalSection_scrubAnswerB hca hqn
          have hle := VeriDNS.Proof.DeliveredWire.encode_size_answer_le
            (Server.deliveredResponse query resp) hcs
          have hda : (Server.deliveredResponse query resp).answer
              = Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord)
                  (Server.clientQname query) resp.answer := rfl
          rw [hda] at hle
          omega
        · intro i
          have hi : i.val < query.question.size := by rw [← hqe]; exact i.isLt
          have hqi := (VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec).2.2.2.2.1
            ⟨i.val, hi⟩
          simpa [hqe] using hqi

set_option maxHeartbeats 1000000 in
theorem serveTcpDatagram_total
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (queryBytes clientAddr : ByteArray)
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (cache : DnsCache) (w w' : World) (cacheOut : DnsCache)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqrbit : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hqu : query.question[0]? = some qu)
    (hqany : qu.qtype.toNat ≠ 255)
    (hqc : αClass qu.qclass = some RRClass.in)
    (hCacheWf : CacheWf cache w.clock) (hNsCanon : CacheNsCanon cache)
    (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache)
    (hCap : cache.records.size ≤ DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hRecC : VeriDNS.Proof.DeliveredWire.CacheRecCanon cache)
    (hNegSoaC : VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cache)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w)
    (hrun : Prog.run n (Server.serveTcpDatagram (M := Prog) (Sock := Unit)
        clientSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w')) :
    ∃ (qm : Query) (t : RRType),
      αName qu.qname = some qm.qname
      ∧ αType qu.qtype = some t
      ∧ qm.qtype = QType.rr t ∧ qm.qclass = RRClass.in ∧ qm.rd = false
      ∧ ∃ (m : Nat) (rr : Except String VeriDNS.Spec.Format) (cache' : DnsCache) (w₂ : World),
        Prog.run m (Server.resolveWithIO (M := Prog) (Sock := Unit)
            query sbelt cache w.clock) w = some ((rr, cache'), w₂)
        ∧ ((∃ msg, rr = .error msg
              ∧ (∃ slist v,
                  HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] []
                    (αCache cache) slist qm v (αCache cache)
                  ∧ v.rcode = RCode.servFail ∧ v.answer = [])
              ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w₂
              ∧ CacheWf cache' w.clock
              ∧ CacheNsCanon cache'
              ∧ CacheCnameCanon cache'
              ∧ (∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
              ∧ CacheNegWf cache' qu.qclass
              ∧ CacheNsDistinct cache'
              ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache'
              ∧ cache'.records.size ≤ DnsCache.capacity
              ∧ (CacheWf cacheOut w.clock ∧ CacheNsCanon cacheOut ∧ CacheCnameCanon cacheOut
                  ∧ (∀ e ∈ cacheOut.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                  ∧ CacheNegWf cacheOut qu.qclass ∧ CacheNsDistinct cacheOut
                  ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cacheOut
                  ∧ cacheOut.records.size ≤ DnsCache.capacity
                  ∧ VeriDNS.Proof.DeliveredWire.CacheRecCanon cacheOut
                  ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cacheOut))
          ∨ (∃ resp slist v cOut coutM,
              rr = .ok resp
              ∧ resp.question[0]? = some qu
              ∧ CacheRefines cOut (αCache cache)
              ∧ HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] [] cOut slist qm v coutM
              ∧ (αResp (Server.deliveredResponse query resp)).rcode = v.rcode
              ∧ (αResp (Server.deliveredResponse query resp)).answer
                  = VeriDNS.Spec.Net.scrubAnswer qm.qname v.answer
              ∧ CacheRefines (αCache cache') coutM
              ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w₂
              ∧ CacheWf cache' w.clock
              ∧ CacheNsCanon cache'
              ∧ CacheCnameCanon cache'
              ∧ (∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
              ∧ CacheNegWf cache' qu.qclass
              ∧ CacheNsDistinct cache'
              ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache'
              ∧ cache'.records.size ≤ DnsCache.capacity
              ∧ (CacheWf cacheOut w.clock ∧ CacheNsCanon cacheOut ∧ CacheCnameCanon cacheOut
                  ∧ (∀ e ∈ cacheOut.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                  ∧ CacheNegWf cacheOut qu.qclass ∧ CacheNsDistinct cacheOut
                  ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cacheOut
                  ∧ cacheOut.records.size ≤ DnsCache.capacity
                  ∧ VeriDNS.Proof.DeliveredWire.CacheRecCanon cacheOut
                  ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cacheOut)
              ∧ ((VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp)).size ≤ 65535 →
                  VeriDNS.Impl.TcpFraming.unframeTcp
                      (VeriDNS.Impl.TcpFraming.frameTcp
                        (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp)))
                    = some (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                  ∧ VeriDNS.Impl.Message.decode
                      (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                    = .ok (Server.deliveredResponse query resp)))) := by
  obtain ⟨h0lt, h0eq⟩ := Array.getElem?_eq_some_iff.mp hqu
  have hqf0 : VeriDNS.Proof.Message.QuestionFromLabels qu := by
    have hqf := (VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec).2.2.2.2.1 ⟨0, h0lt⟩
    simp only [Fin.getElem_fin] at hqf
    rwa [h0eq] at hqf
  obtain ⟨ls, hv, hsz, heq⟩ := hqf0
  have hqm : αName qu.qname = some ls.toList := by
    rw [← heq]
    exact αName_labelsToWireFormat ls hv
  have hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo ls.toList := by
    rw [← heq]
    rfl
  have hvmem : ∀ x ∈ ls.toList, 0 < x.size ∧ x.size ≤ 63 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    have hthis := hv i (by simpa using hi)
    rw [show ls[i] = x from by rw [← hxi]; simp] at hthis
    exact hthis
  have hqlen : ls.toList.length ≤ 127 := by
    have hge := labelsToWireFormatGo_size_ge ls.toList (fun l hl => (hvmem l hl).1)
    have hszGo : (VeriDNS.Impl.DomainName.labelsToWireFormatGo ls.toList).size ≤ 255 := hsz
    omega
  obtain ⟨t, ht⟩ := αType_total qu.qtype
  refine ⟨⟨ls.toList, QType.rr t, RRClass.in, false⟩, t, hqm, ht, rfl, rfl, rfl, ?_⟩
  exact serveTcpDatagram_verdict_sound net ns ra ednsBuf rttOf clientSock acl sbelt
    hnetWF hGlSbelt n queryBytes clientAddr query qu
    ⟨ls.toList, QType.rr t, RRClass.in, false⟩ t cache w w' cacheOut
    hperm hdec hqrbit hqp hqu hqm hcanon ht hqany rfl hqc hvmem hqlen rfl
    (fun h => QType.noConfusion h) rfl
    hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hRecC hNegSoaC
    hclock hw hwTcp hrun
