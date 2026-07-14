import VeriDNS.Proof.ResolveWithIOSound






open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache VeriDNS.Spec


def inCode : BitVec 16 := BitVec.ofNat 16 RRClass.in.toCode

theorem qclass_eq_inCode {qc : BitVec 16} (h : αClass qc = some RRClass.in) : qc = inCode :=
  αClass_inj h (αClass_toCode RRClass.in)

def ServePack (cache : DnsCache) (clk : UInt32) (qc : BitVec 16) : Prop :=
  CacheWf cache clk
  ∧ CacheNsCanon cache
  ∧ CacheCnameCanon cache
  ∧ (∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
  ∧ CacheNegWf cache qc
  ∧ CacheNsDistinct cache
  ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache
  ∧ cache.records.size ≤ DnsCache.capacity
  ∧ VeriDNS.Proof.DeliveredWire.CacheRecCanon cache
  ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cache

theorem CacheNegWf_empty (qc : BitVec 16) : CacheNegWf DnsCache.empty qc := by
  intro e he
  simp [DnsCache.empty] at he

theorem ServePack_empty (clk : UInt32) (qc : BitVec 16) : ServePack DnsCache.empty clk qc :=
  ⟨CacheWf_empty clk,
   CacheNsCanon_empty,
   CacheCnameCanon_empty,
   fun _ he => absurd he (by simp [DnsCache.empty]),
   CacheNegWf_empty qc,
   CacheNsDistinct_empty,
   VeriDNS.Proof.NameTree.oneExpiry_empty,
   by simp [DnsCache.empty, DnsCache.capacity],
   VeriDNS.Proof.DeliveredWire.cacheRecCanon_empty,
   VeriDNS.Proof.DeliveredWire.cacheNegSoaCanon_empty⟩


def ServedGates (acl : Server.ClientAcl) (queryBytes clientAddr : ByteArray) : Prop :=
  Server.permitted acl clientAddr = true
  ∧ ∃ query : VeriDNS.Spec.Format,
      VeriDNS.Impl.Message.decode queryBytes = .ok query
      ∧ (query.header.qr == 1) = false
      ∧ Server.queryProblem query = none

def InScope (acl : Server.ClientAcl) (queryBytes clientAddr : ByteArray) : Prop :=
  ∀ query : VeriDNS.Spec.Format,
    Server.permitted acl clientAddr = true →
    VeriDNS.Impl.Message.decode queryBytes = .ok query →
    (query.header.qr == 1) = false →
    Server.queryProblem query = none →
    ∀ qu, query.question[0]? = some qu →
      qu.qtype.toNat ≠ 255 ∧ αClass qu.qclass = some RRClass.in

theorem question_head_of_queryProblem_none {q : VeriDNS.Spec.Format}
    (h : Server.queryProblem q = none) : ∃ qu, q.question[0]? = some qu := by
  have hint : Server.interpretableQuery q = true := by
    by_contra hni
    rw [Bool.not_eq_true] at hni
    simp [Server.queryProblem, hni] at h
  have hsz : q.question.size = 1 := by
    simpa [Server.interpretableQuery] using hint
  exact ⟨q.question[0]'(by omega), Array.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩⟩


theorem serveDatagram_unserved
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray)
    (h : ¬ ServedGates acl queryBytes clientAddr) :
    Server.serveDatagram (M := Prog) (Sock := Unit) clientSock acl sbelt cache
        queryBytes clientAddr
      = pure cache := by
  by_cases hperm : Server.permitted acl clientAddr = true
  · cases hdec : VeriDNS.Impl.Message.decode queryBytes with
    | error e =>
      unfold Server.serveDatagram
      simp [hperm, hdec, -Prog.bind_def, -Prog.pure_def]
      cases hraw : Server.rawDatagramReply queryBytes <;> rfl
    | ok query =>
      by_cases hqr : (query.header.qr == 1) = true
      · unfold Server.serveDatagram
        simp [hperm, hdec, -Prog.bind_def, -Prog.pure_def]
        intro hne
        exact absurd (by simpa using hqr) hne
      · cases hqp : Server.queryProblem query with
        | some rc =>
          unfold Server.serveDatagram
          simp [hperm, hdec, hqp, -Prog.bind_def, -Prog.pure_def]
          intro _
          rfl
        | none =>
          exact absurd ⟨hperm, query, hdec, Bool.not_eq_true _ ▸ hqr, hqp⟩ h
  · exact VeriDNS.Proof.Server.serveDatagram_denied clientSock acl sbelt cache
      queryBytes clientAddr (Bool.not_eq_true _ ▸ hperm)


def ServeJustification (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (sbelt : DnsSList) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (t : RRType) (cache : DnsCache) (w : World)
    (cacheOut : DnsCache) : Prop :=
  ∃ qm : Query,
    αName qu.qname = some qm.qname
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
            ∧ ((VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp)).size ≤ VeriDNS.Impl.Edns.clientCap query →
                Server.truncateUdp
                    (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                    (Server.deliveredResponse query resp)
                    (VeriDNS.Impl.Edns.clientCap query)
                  = (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp), false)
                ∧ VeriDNS.Impl.Message.decode
                    (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                  = .ok (Server.deliveredResponse query resp))))

theorem ServeJustification.packOut {net : Network} {ns : NetState} {ra : String}
    {ednsBuf : Nat} {rttOf : String → Nat} {sbelt : DnsSList}
    {query : VeriDNS.Spec.Format} {qu : VeriDNS.Spec.Question} {t : RRType}
    {cache : DnsCache} {w : World} {cacheOut : DnsCache}
    (h : ServeJustification net ns ra ednsBuf rttOf sbelt query qu t cache w cacheOut) :
    ServePack cacheOut w.clock qu.qclass := by
  obtain ⟨qm, -, -, -, -, m, rr, cache', w₂, -, hdisj⟩ := h
  rcases hdisj with
      ⟨msg, -, -, -, -, -, -, -, -, -, -, -, hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap,
        hrec, hnsoa⟩
    | ⟨resp, slist, v, cOut, coutM, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap, hrec, hnsoa⟩, -⟩
  · exact ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap, hrec, hnsoa⟩
  · exact ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap, hrec, hnsoa⟩


def serveSeq (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList) :
    List (ByteArray × ByteArray) → DnsCache → Server.RateBucket
      → Prog (DnsCache × Server.RateBucket)
  | [], cache, rb => pure (cache, rb)
  | d :: rest, cache, rb =>
    Server.afterRecv (M := Prog) (Sock := Unit) clientSock acl sbelt cache rb d.1 d.2
      >>= fun cr => serveSeq clientSock acl sbelt rest cr.1 cr.2

def JustifiedTrace (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (clientSock : Unit) (acl : Server.ClientAcl)
    (sbelt : DnsSList) :
    List (ByteArray × ByteArray) → DnsCache → Server.RateBucket → World → Prop
  | [], _, _, _ => True
  | d :: rest, cache, rb, w =>
    ∃ (cache₂ : DnsCache) (rb₂ : Server.RateBucket) (w₂ : World) (m : Nat),
      Prog.run m (Server.afterRecv (M := Prog) (Sock := Unit)
          clientSock acl sbelt cache rb d.1 d.2) w = some ((cache₂, rb₂), w₂)
      ∧ (∀ (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (t : RRType),
          (Server.RateBucket.bump rb (Server.clientIp d.2)).isSome = true →
          Server.permitted acl d.2 = true →
          VeriDNS.Impl.Message.decode d.1 = .ok query →
          (query.header.qr == 1) = false →
          Server.queryProblem query = none →
          query.question[0]? = some qu →
          αType qu.qtype = some t →
          ServeJustification net ns ra ednsBuf rttOf sbelt query qu t cache w cache₂)
      ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl sbelt rest cache₂ rb₂ w₂


theorem serveSeq_sound (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt) :
    ∀ (ds : List (ByteArray × ByteArray)) (n : Nat) (cache : DnsCache)
      (rb : Server.RateBucket) (w : World) (out : DnsCache × Server.RateBucket) (w' : World),
    Prog.run n (serveSeq clientSock acl sbelt ds cache rb) w = some (out, w') →
    (∀ d ∈ ds, InScope acl d.1 d.2) →
    ServePack cache w.clock inCode →
    w.clock.toNat + 604800 < 2 ^ 32 →
    WorldModels net ns ra ednsBuf (αTime w.clock) w →
    WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w →
    ServePack out.1 w.clock inCode
    ∧ w'.clock = w.clock ∧ w'.oracle = w.oracle
    ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w'
    ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl sbelt ds cache rb w := by
  intro ds
  induction ds with
  | nil =>
    intro n cache rb w out w' hrun hscope hpack hclock hw hwTcp
    simp only [serveSeq, run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨hpack, rfl, rfl, hw, trivial⟩
  | cons d rest ih =>
    intro n cache rb w out w' hrun hscope hpack hclock hw hwTcp
    rw [serveSeq] at hrun
    obtain ⟨m₁, m₂, cr, w₂, -, h1, h2⟩ := run_bind_inv hrun
    obtain ⟨hor₂, hclk₂, -⟩ := run_world_frame h1
    have hw₂ : WorldModels net ns ra ednsBuf (αTime w₂.clock) w₂ := by
      rw [hclk₂]
      exact WorldModels_oracle net ns ra ednsBuf (αTime w.clock) hor₂ hw
    have hwTcp₂ : WorldModelsTcp net ns ra ednsBuf (αTime w₂.clock) w₂ := by
      rw [hclk₂]
      exact WorldModelsTcp_tcpOracle net ns ra ednsBuf (αTime w.clock)
        (run_world_tcpOracle_frame h1) hwTcp
    have hclock₂ : w₂.clock.toNat + 604800 < 2 ^ 32 := by rw [hclk₂]; exact hclock
    have hstep : ServePack cr.1 w.clock inCode
        ∧ (∀ (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (t : RRType),
            (Server.RateBucket.bump rb (Server.clientIp d.2)).isSome = true →
            Server.permitted acl d.2 = true →
            VeriDNS.Impl.Message.decode d.1 = .ok query →
            (query.header.qr == 1) = false →
            Server.queryProblem query = none →
            query.question[0]? = some qu →
            αType qu.qtype = some t →
            ServeJustification net ns ra ednsBuf rttOf sbelt query qu t cache w cr.1) := by
      cases hb : Server.RateBucket.bump rb (Server.clientIp d.2) with
      | none =>
        have hred : Server.afterRecv (M := Prog) (Sock := Unit)
            clientSock acl sbelt cache rb d.1 d.2 = pure (cache, rb) := by
          unfold Server.afterRecv
          rw [hb]
        rw [hred] at h1
        simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h1
        rw [← h1.1]
        exact ⟨hpack, fun _ _ _ hadm _ _ _ _ _ _ => absurd hadm (by simp)⟩
      | some rb' =>
        have hred : Server.afterRecv (M := Prog) (Sock := Unit)
            clientSock acl sbelt cache rb d.1 d.2
            = Server.serveDatagram (M := Prog) (Sock := Unit)
                clientSock acl sbelt cache d.1 d.2 >>= fun c => pure (c, rb') := by
          unfold Server.afterRecv
          rw [hb]
          exact map_eq_pure_bind _ _
        rw [hred] at h1
        obtain ⟨k₁, k₂, c₃, w₃, -, hs1, hs2⟩ := run_bind_inv h1
        simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hs2
        obtain ⟨hcr, hw3⟩ := hs2
        rw [hw3] at hs1
        subst hcr
        by_cases hg : ServedGates acl d.1 d.2
        ·
          obtain ⟨hperm, query, hdec, hqr, hqp⟩ := hg
          obtain ⟨qu, hqu⟩ := question_head_of_queryProblem_none hqp
          obtain ⟨hq255, hqc⟩ :=
            hscope d (List.mem_cons_self ..) query hperm hdec hqr hqp qu hqu
          have hclassEq : qu.qclass = inCode := qclass_eq_inCode hqc
          obtain ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap, hrec, hnsoa⟩ := hpack
          obtain ⟨qm, t, hqm, ht, hqt, hqcl, hrdm, hrest⟩ :=
            serveDatagram_total net ns ra ednsBuf rttOf clientSock acl sbelt
              hnetWF hGlSbelt k₁ d.1 d.2 query qu cache w w₂ c₃
              hperm hdec hqr hqp hqu hq255 hqc
              hwf hns hcn hwfrr hnsd hoe hcap (by rw [hclassEq]; exact hneg) hrec hnsoa
              hclock hw hwTcp hs1
          have hjust : ServeJustification net ns ra ednsBuf rttOf sbelt query qu t
              cache w c₃ := ⟨qm, hqm, hqt, hqcl, hrdm, hrest⟩
          refine ⟨by rw [← hclassEq]; exact hjust.packOut, ?_⟩
          intro query' qu' t' _ _ hdec' _ _ hqu' ht'
          have hq : query' = query := by
            rw [hdec] at hdec'
            exact (Except.ok.inj hdec').symm
          subst hq
          have hqeq : qu' = qu := by
            rw [hqu] at hqu'
            exact (Option.some.inj hqu').symm
          subst hqeq
          have hteq : t' = t := by
            rw [ht] at ht'
            exact (Option.some.inj ht').symm
          subst hteq
          exact hjust
        ·
          rw [serveDatagram_unserved clientSock acl sbelt cache d.1 d.2 hg] at hs1
          simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hs1
          rw [← hs1.1]
          refine ⟨hpack, ?_⟩
          intro query qu t _ hperm hdec hqr hqp _ _
          exact absurd ⟨hperm, query, hdec, hqr, hqp⟩ hg
    obtain ⟨hpack₂, hjustStep⟩ := hstep
    have hpack₂' : ServePack cr.1 w₂.clock inCode := by rw [hclk₂]; exact hpack₂
    obtain ⟨hpackOut, hclkOut, horOut, hwOut, htrace⟩ :=
      ih m₂ cr.1 cr.2 w₂ out w' h2 (fun d' hd' => hscope d' (List.mem_cons_of_mem d hd'))
        hpack₂' hclock₂ hw₂ hwTcp₂
    refine ⟨by rw [← hclk₂]; exact hpackOut,
      hclkOut.trans hclk₂, horOut.trans hor₂,
      by rw [hclk₂] at hwOut; exact hwOut,
      cr.1, cr.2, w₂, m₁, by simpa using h1, hjustStep, htrace⟩


theorem serveSeq_total (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (ds : List (ByteArray × ByteArray)) (n : Nat) (w : World)
    (out : DnsCache × Server.RateBucket) (w' : World)
    (hrun : Prog.run n
        (serveSeq clientSock acl sbelt ds DnsCache.empty Server.RateBucket.empty) w
      = some (out, w'))
    (hscope : ∀ d ∈ ds, InScope acl d.1 d.2)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w) :
    ServePack out.1 w.clock inCode
    ∧ w'.clock = w.clock ∧ w'.oracle = w.oracle
    ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w'
    ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl sbelt ds
        DnsCache.empty Server.RateBucket.empty w :=
  serveSeq_sound net ns ra ednsBuf rttOf clientSock acl sbelt hnetWF hGlSbelt
    ds n DnsCache.empty Server.RateBucket.empty w out w' hrun hscope
    (ServePack_empty w.clock inCode) hclock hw hwTcp
