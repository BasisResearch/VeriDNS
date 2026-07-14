import VeriDNS.Proof.Depth1Adequacy
import VeriDNS.Proof.ServeTcp






namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message


theorem storeNegativeIfCacheable_runs (resp : VeriDNS.Spec.Format) (base : DnsCache)
    (nowT : UInt32) (w : World) :
    ∃ (m : Nat) (c : DnsCache) (w' : World),
      Prog.run m (Server.storeNegativeIfCacheable (M := Prog) (Sock := Unit) resp base nowT) w
        = some (c, w') := by
  unfold Server.storeNegativeIfCacheable
  split
  · split
    · exact ⟨1, _, _, run_log_bind _ _ w (run_pure' 0 _ _)⟩
    · split
      · exact ⟨1, _, _, run_log_bind _ _ w (run_pure' 0 _ _)⟩
      · exact ⟨0, _, _, run_pure' 0 _ _⟩
    · exact ⟨0, _, _, run_pure' 0 _ _⟩
  · exact ⟨0, _, _, run_pure' 0 _ _⟩

theorem replyForResolution_runs (query : VeriDNS.Spec.Format)
    (rr : Except String VeriDNS.Spec.Format) (cache' : DnsCache) (nowT : UInt32) (w : World) :
    ∃ (m : Nat) (out : VeriDNS.Spec.Format × DnsCache) (w' : World),
      Prog.run m (Server.replyForResolution (M := Prog) (Sock := Unit) query rr cache' nowT) w
        = some (out, w') := by
  unfold Server.replyForResolution
  cases rr with
  | error msg => exact ⟨1, _, _, run_log_bind _ _ w (run_pure' 0 _ _)⟩
  | ok resp =>
    obtain ⟨m, c, w', h⟩ := storeNegativeIfCacheable_runs resp
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT) nowT w
    exact ⟨m + 0, _, w', run_bind h _ (run_pure' 0 _ _)⟩


theorem serveDatagram_delivers_of_resolve
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList) (cache : DnsCache)
    (queryBytes clientAddr : ByteArray) (query : VeriDNS.Spec.Format)
    (K : Nat) (rr : Except String VeriDNS.Spec.Format) (cache' : DnsCache) (w w₂ : World)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hres : Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache w.clock) w = some ((rr, cache'), w₂)) :
    ∃ (n : Nat) (cacheOut : DnsCache) (w' : World),
      Prog.run n (Server.serveDatagram (M := Prog) (Sock := Unit)
        clientSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w') := by
  rw [serveDatagram_served clientSock acl sbelt cache queryBytes clientAddr query
    hperm hdec hqr hqp]
  obtain ⟨m, out, w₃, hreply⟩ := replyForResolution_runs query rr cache' w.clock w₂
  obtain ⟨response, c''⟩ := out
  exact ⟨(K + (m + 0)) + 1, _, w₃,
    run_now_bind _ w (run_bind hres _ (run_bind hreply _ (run_pure' 0 _ _)))⟩

theorem serveTcpDatagram_delivers_of_resolve
    (connSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList) (cache : DnsCache)
    (queryBytes clientAddr : ByteArray) (query : VeriDNS.Spec.Format)
    (K : Nat) (rr : Except String VeriDNS.Spec.Format) (cache' : DnsCache) (w w₂ : World)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hres : Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache w.clock) w = some ((rr, cache'), w₂)) :
    ∃ (n : Nat) (cacheOut : DnsCache) (w' : World),
      Prog.run n (Server.serveTcpDatagram (M := Prog) (Sock := Unit)
        connSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w') := by
  rw [serveTcpDatagram_served connSock acl sbelt cache queryBytes clientAddr query
    hperm hdec hqr hqp]
  obtain ⟨m, out, w₃, hreply⟩ := replyForResolution_runs query rr cache' w.clock w₂
  obtain ⟨response, c''⟩ := out
  exact ⟨(K + (m + 0)) + 1, _, w₃,
    run_now_bind _ w (run_bind hres _ (run_bind hreply _ (run_pure' 0 _ _)))⟩


theorem serveDatagram_depth1_adequate
    (clientSock : Unit) (acl : Server.ClientAcl)
    (queryBytes clientAddr : ByteArray)
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (childT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (childNeg : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entry : SlistEntry) (rootIp : BitVec 32) (subQuery₀ sent : VeriDNS.Spec.Format)
    (nsAuth glue : Array ByteArray) (nsRaw glueRaw : ByteArray)
    (nsrr grr : VeriDNS.Spec.ResourceRecord) (snameLabels : Array ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hcoop : CooperativeNetworkAddr respond w)
    (hroot : ∀ q', respond (Server.ipv4ToAddr rootIp) q' = referralReply q' nsAuth glue)
    (hchild : ∀ q', respond (Server.ipv4ToAddr
        (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr))) q'
      = treeRespond childT childNeg q')
    (hegressChild : Server.blockedEgress
        (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr)) = false)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 w.clock cache = .ok (.paused state))
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ w.clock + 5))
    (hbest : state.resources.slist.bestWithAddress = some (entry, rootIp))
    (hegress : Server.blockedEgress rootIp = false)
    (hbuild : Resolver.buildSubQuery state (Server.seedRevealed state) = some subQuery₀)
    (hrev : DomainName.labelCount state.resources.sname ≤ Server.seedRevealed state)
    (hcanon : CanonicalName state.resources.sname)
    (hsn : DomainName.wireFormatToLabels state.resources.sname = .ok snameLabels)
    (hlq : state.lastQuery = some q)
    (hqu : q.question[0]? = some qu)
    (hqtc : (q.header.tc == 1) = false)
    (hqsf : (q.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcold : state.resources.cache.records = #[])
    (hchain0 : state.cnameChain = #[])
    (hnsz : nsAuth.size < 65536) (hgsz : glue.size < 65536)
    (hcanNs : CanonicalSection nsAuth) (hcanGlue : CanonicalSection glue)
    (hoptG : ∀ b ∈ glue, Edns.isOptRR b = false)
    (hnA : ∀ b ∈ nsAuth, Server.capTtlRR b = b)
    (hdG : ∀ b ∈ glue, Server.capTtlRR b = b)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) nsAuth 6 = false)
    (hclq : ∀ q', Server.delegationCloserB (state.resources.slist.markQueried entry.name)
        state.resources.sname (referralReply q' nsAuth glue) = true)
    (hbaiq : ∀ q', Server.respInBailiwick state.resources.sname
        (referralReply q' nsAuth glue) = true)
    (hauthN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) nsAuth) nsAuth)
        = #[nsRaw])
    (hpns : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsrr)
    (hnsName : DomainName.nameEqCI nsrr.name state.resources.sname = true)
    (hnsType : nsrr.type = BitVec.ofNat 16 2)
    (hnsClass : nsrr.class = BitVec.ofNat 16 1)
    (hnzNs : (nsrr.ttl == 0) = false)
    (hfreshNs : state.now + nsrr.ttl.toNat.toUInt32 > state.now)
    (haddN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) nsAuth) glue)
        = #[glueRaw])
    (hpg : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) glueRaw = some grr)
    (hgKey : DomainName.nameEqCI grr.name
        (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr) = true)
    (hgType : grr.type = BitVec.ofNat 16 1)
    (hgClass : grr.class = BitVec.ofNat 16 1)
    (hnzG : (grr.ttl == 0) = false)
    (hfreshG : state.now + grr.ttl.toNat.toUInt32 > state.now)
    (hgSize : ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr).size == 4)
        = true)
    (hlk : VeriDNS.Impl.NameTree.treeLookup childT
        (DomainName.randomizeCase (w.ids (w.idCtr + 3)) state.resources.sname) qu.qtype
        = .answer rrs)
    (hsz : rrs.size < 65536)
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr) :
    ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache) (K : Nat) (w₂ : World)
      (n : Nat) (cacheOut : DnsCache) (w' : World),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache w.clock) w = some ((.ok resp, cout), w₂)
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question
      ∧ Prog.run n (Server.serveDatagram (M := Prog) (Sock := Unit)
          clientSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w') := by
  obtain ⟨resp, cout, K, w₂, hrun, hansEq, hquesEq⟩ := resolveWithIO_depth1_adequate respond
    childT childNeg query sbelt cache w.clock 38 6 5 w state entry rootIp subQuery₀ sent
    nsAuth glue nsRaw glueRaw nsrr grr snameLabels q qu rrs
    hcoop hroot hchild hegressChild hpause hsentEq hsendq hdl hbest hegress hbuild hrev hcanon
    hsn hlq hqu hqtc hqsf hcold hchain0 hnsz hgsz hcanNs hcanGlue hoptG hnA hdG hns hsoa hclq
    hbaiq hauthN hpns hnsName hnsType hnsClass hnzNs hfreshNs haddN hpg hgKey hgType hgClass
    hnzG hfreshG hgSize hlk hsz hwfRR
  have hrun' : Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
      query sbelt cache w.clock) w = some ((.ok resp, cout), w₂) := hrun
  obtain ⟨n, cacheOut, w', hserve⟩ := serveDatagram_delivers_of_resolve clientSock acl sbelt
    cache queryBytes clientAddr query K (.ok resp) cout w w₂ hperm hdec hqr hqp hrun'
  exact ⟨resp, cout, K, w₂, n, cacheOut, w', hrun', hansEq, hquesEq, hserve⟩

end VeriDNS.Proof.Adequacy
