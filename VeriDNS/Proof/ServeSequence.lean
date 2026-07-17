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
      ∧ VeriDNS.Impl.Edns.ednsProblem query = none

/-- The query-shape scope predicate on a served datagram. Both former clauses
    are now CLOSED at the serve boundary and no longer restrict the input:

    * `αClass qu.qclass = some RRClass.in` is *derived* from `queryProblem = none`
      (non-IN → REFUSED at ingress, `Server.queryProblem_none_qclass`); and
    * `qu.qtype.toNat ≠ 255` is no longer required — a QTYPE=ANY query is *handled*
      by the RFC 8482 §4.2 serve arm (`Server.serveDatagram_any`), not excluded.

    So `InScope` is now unconditionally `True`: every datagram is in scope. The
    predicate is retained (rather than deleted) only so the seed/ledger history
    stays legible; `serveSeq_total` no longer carries an `InScope` hypothesis. -/
def InScope (_acl : Server.ClientAcl) (_queryBytes _clientAddr : ByteArray) : Prop :=
  True

theorem question_head_of_queryProblem_none {q : VeriDNS.Spec.Format}
    (h : Server.queryProblem q = none) : ∃ qu, q.question[0]? = some qu := by
  have hint : Server.interpretableQuery q = true := by
    by_contra hni
    rw [Bool.not_eq_true] at hni
    simp [Server.queryProblem, hni] at h
  have hsz : q.question.size = 1 := by
    simpa [Server.interpretableQuery] using hint
  exact ⟨q.question[0]'(by omega), Array.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩⟩


/-- An unserved datagram leaves the cache untouched.  With client-reply sends
now VISIBLE in `Prog` (finding 054), the unserved arms are no longer all
literally `pure cache`: the undecodable-with-FORMERR arm and the
`queryProblem` error-reply arm each perform one `sendTo` first, so the old
`= pure cache` equation is replaced by this disjunction (either no reply, or
exactly one error reply then `pure cache`). -/
theorem serveDatagram_unserved
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray)
    (h : ¬ ServedGates acl queryBytes clientAddr) :
    Server.serveDatagram (M := Prog) (Sock := Unit) clientSock acl sbelt cache
        queryBytes clientAddr
      = pure cache
    ∨ ∃ reply, Server.serveDatagram (M := Prog) (Sock := Unit) clientSock acl sbelt cache
        queryBytes clientAddr
      = (VeriDNS.Spec.UdpSocket.sendTo (M := Prog) clientSock reply clientAddr
          >>= fun _ => pure cache) := by
  by_cases hperm : Server.permitted acl clientAddr = true
  · cases hdec : VeriDNS.Impl.Message.decode queryBytes with
    | error e =>
      unfold Server.serveDatagram
      cases hraw : Server.rawDatagramReply queryBytes with
      | none =>
        refine Or.inl ?_
        simp [hperm, hdec, hraw, -Prog.bind_def, -Prog.pure_def]
      | some reply =>
        refine Or.inr ⟨reply, ?_⟩
        simp [hperm, hdec, hraw, -Prog.bind_def, -Prog.pure_def]
    | ok query =>
      by_cases hqr : (query.header.qr == 1) = true
      · refine Or.inl ?_
        unfold Server.serveDatagram
        simp [hperm, hdec, -Prog.bind_def, -Prog.pure_def]
        intro hne
        exact absurd (by simpa using hqr) hne
      · cases hqp : Server.queryProblem query with
        | some rc =>
          refine Or.inr ⟨VeriDNS.Impl.Message.encode
            (Server.finalizeForClient (Server.buildErrorResponse query rc)), ?_⟩
          unfold Server.serveDatagram
          simp [hperm, hdec, hqp, -Prog.bind_def, -Prog.pure_def]
          intro hq1
          exact absurd (show (query.header.qr == 1) = true by simp [hq1]) hqr
        | none =>
          cases hedns : VeriDNS.Impl.Edns.ednsProblem query with
          | some ep =>
            refine Or.inr ⟨VeriDNS.Impl.Message.encode
              (Server.ednsProblemResponse query ep), ?_⟩
            unfold Server.serveDatagram
            simp [hperm, hdec, hqp, hedns, -Prog.bind_def, -Prog.pure_def]
            intro hq1
            exact absurd (show (query.header.qr == 1) = true by simp [hq1]) hqr
          | none =>
            exact absurd ⟨hperm, query, hdec, Bool.not_eq_true _ ▸ hqr, hqp, hedns⟩ h
  · exact Or.inl (VeriDNS.Proof.Server.serveDatagram_denied clientSock acl sbelt cache
      queryBytes clientAddr (Bool.not_eq_true _ ▸ hperm))


/-- The RFC 8482 §4.2 ANY serve arm justification: the query is a QTYPE=ANY
    query, the cache is unchanged by serving it (`cacheOut = cache`, so its
    `ServePack` invariants carry over), and the delivered wire is exactly the
    synthesized minimal HINFO response `Server.synthAnyResponse query`. -/
def AnyServeJustification (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (w : World) (cache cacheOut : DnsCache) : Prop :=
  Server.isAnyQuery query = true
  ∧ cacheOut = cache
  ∧ ServePack cache w.clock qu.qclass

/-- The per-datagram justification a served query produces: either the RFC 8482
    ANY arm (`AnyServeJustification`, no resolution), or the resolution-soundness
    justification of the non-ANY path. -/
def ServeJustification (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (sbelt : DnsSList) (query : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (t : RRType) (cache : DnsCache) (w : World)
    (cacheOut : DnsCache) : Prop :=
  AnyServeJustification query qu w cache cacheOut
  ∨ ∃ qm : Query,
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
            ∧ VeriDNS.Spec.Net.GaveUpWitness (αTime w.clock) (αCache cache) [] qm
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
                = VeriDNS.Spec.Net.typeScrub qm.qtype (VeriDNS.Spec.Net.scrubAnswer qm.qname v.answer)
            ∧ (∀ bytes ∈ (Server.deliveredResponse query resp).additional,
                ∃ pr : VeriDNS.Spec.ResourceRecord × Nat,
                  VeriDNS.Impl.DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes = .ok pr
                  ∧ VeriDNS.Impl.Resolver.isAncestorB (Server.clientQname query) pr.1.name = true)
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
            ∧ (((VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp)).size ≤ VeriDNS.Impl.Edns.clientCap query →
                Server.truncateUdp
                    (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                    (Server.deliveredResponse query resp)
                    (VeriDNS.Impl.Edns.clientCap query)
                  = (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp), false)
                ∧ VeriDNS.Impl.Message.decode
                    (VeriDNS.Impl.Message.encode (Server.deliveredResponse query resp))
                  = .ok (Server.deliveredResponse query resp))
              ∧ (Server.truncateUdp
                    (VeriDNS.Impl.Message.encode
                      (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp)))
                    (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp))
                    (VeriDNS.Impl.Edns.clientCap query)).1.size
                  ≤ VeriDNS.Impl.Edns.clientCap query
              ∧ ((Server.truncateUdp
                    (VeriDNS.Impl.Message.encode
                      (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp)))
                    (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp))
                    (VeriDNS.Impl.Edns.clientCap query)).2 = true ↔
                  (VeriDNS.Impl.Edns.clientCap query
                      < (VeriDNS.Impl.Message.encode
                          (VeriDNS.Impl.Edns.withReplyOpt query
                            (Server.deliveredResponse query resp))).size
                    ∧ VeriDNS.Impl.Edns.clientCap query
                      < (VeriDNS.Impl.Message.encode
                          { VeriDNS.Impl.Edns.withReplyOpt query
                              (Server.deliveredResponse query resp) with
                            header := { (VeriDNS.Impl.Edns.withReplyOpt query
                              (Server.deliveredResponse query resp)).header with
                              arcount := 0 }
                            additional := #[] }).size)))))

theorem ServeJustification.packOut {net : Network} {ns : NetState} {ra : String}
    {ednsBuf : Nat} {rttOf : String → Nat} {sbelt : DnsSList}
    {query : VeriDNS.Spec.Format} {qu : VeriDNS.Spec.Question} {t : RRType}
    {cache : DnsCache} {w : World} {cacheOut : DnsCache}
    (h : ServeJustification net ns ra ednsBuf rttOf sbelt query qu t cache w cacheOut) :
    ServePack cacheOut w.clock qu.qclass := by
  rcases h with ⟨-, hcout, hpack⟩ | h
  · rw [hcout]; exact hpack
  obtain ⟨qm, -, -, -, -, m, rr, cache', w₂, -, hdisj⟩ := h
  rcases hdisj with
      ⟨msg, -, -, -, -, -, -, -, -, -, -, -, -, hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap,
        hrec, hnsoa⟩
    | ⟨resp, slist, v, cOut, coutM, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
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
          VeriDNS.Impl.Edns.ednsProblem query = none →
          query.question[0]? = some qu →
          αType qu.qtype = some t →
          ServeJustification net ns ra ednsBuf rttOf sbelt query qu t cache w cache₂)
      ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl sbelt rest cache₂ rb₂ w₂


set_option maxHeartbeats 1000000 in
theorem serveSeq_sound (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt) :
    ∀ (ds : List (ByteArray × ByteArray)) (n : Nat) (cache : DnsCache)
      (rb : Server.RateBucket) (w : World) (out : DnsCache × Server.RateBucket) (w' : World),
    Prog.run n (serveSeq clientSock acl sbelt ds cache rb) w = some (out, w') →
    (∀ d ∈ ds, InScope acl d.1 d.2) →
    (∀ i, w.tick i = 0) →
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
    intro n cache rb w out w' hrun hscope htick hpack hclock hw hwTcp
    simp only [serveSeq, run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨hpack, rfl, rfl, hw, trivial⟩
  | cons d rest ih =>
    intro n cache rb w out w' hrun hscope htick hpack hclock hw hwTcp
    rw [serveSeq] at hrun
    obtain ⟨m₁, m₂, cr, w₂, -, h1, h2⟩ := run_bind_inv hrun
    obtain ⟨hor₂, htickEq₂, -⟩ := run_world_frame h1
    have hclk₂ : w₂.clock = w.clock := run_world_clock_frame_tick0 htick h1
    have htick₂ : ∀ i, w₂.tick i = 0 := fun i => by rw [htickEq₂]; exact htick i
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
            VeriDNS.Impl.Edns.ednsProblem query = none →
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
        exact ⟨hpack, fun _ _ _ hadm _ _ _ _ _ _ _ => absurd hadm (by simp)⟩
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
          obtain ⟨hperm, query, hdec, hqr, hqp, hedns⟩ := hg
          obtain ⟨qu, hqu⟩ := question_head_of_queryProblem_none hqp
          have hqc : αClass qu.qclass = some RRClass.in :=
            αClass_in_of_queryProblem_none hqp hqu
          have hclassEq : qu.qclass = inCode := qclass_eq_inCode hqc
          by_cases hany : Server.isAnyQuery query = true
          · -- RFC 8482 §4.2 ANY serve arm: no resolution, cache unchanged.
            have hserve : Server.serveDatagram (M := Prog) (Sock := Unit)
                clientSock acl sbelt cache d.1 d.2 = (do
                  let response := VeriDNS.Impl.Edns.withReplyOpt query
                    (Server.synthAnyResponse query)
                  let (truncated, _) := Server.truncateUdp
                    (VeriDNS.Impl.Message.encode response) response
                    (VeriDNS.Impl.Edns.clientCap query)
                  VeriDNS.Spec.UdpSocket.sendTo (M := Prog) clientSock truncated d.2
                  pure cache) :=
              serveDatagram_any clientSock acl sbelt cache d.1 d.2 query hperm hdec hqr hqp
                hedns hany
            rw [hserve] at hs1
            obtain ⟨p1, p2, p3, w₃, -, -, hspure⟩ := run_bind_inv hs1
            simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hspure
            have hc3 : c₃ = cache := hspure.1.symm
            subst hc3
            refine ⟨hpack, ?_⟩
            intro query' qu' t' _ _ hdec' _ _ _ hqu' _
            have hq : query' = query := by rw [hdec] at hdec'; exact (Except.ok.inj hdec').symm
            subst hq
            have hqeq : qu' = qu := by rw [hqu] at hqu'; exact (Option.some.inj hqu').symm
            subst hqeq
            exact Or.inl ⟨hany, rfl, by rw [hclassEq]; exact hpack⟩
          · -- non-ANY served path: full resolution soundness.
            have hnany : Server.isAnyQuery query = false := by
              simpa using hany
            have hq255 : qu.qtype.toNat ≠ 255 := Server.not_anyQuery_qtype hnany hqu
            obtain ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hcap, hrec, hnsoa⟩ := hpack
            obtain ⟨qm, t, hqm, ht, hqt, hqcl, hrdm, hrest⟩ :=
              serveDatagram_total net ns ra ednsBuf rttOf clientSock acl sbelt
                hnetWF hGlSbelt k₁ d.1 d.2 query qu cache w w₂ c₃
                hperm hdec hqr hqp hedns hqu hnany
                hwf hns hcn hwfrr hnsd hoe hcap (by rw [hclassEq]; exact hneg) hrec hnsoa
                hclock hw hwTcp hs1
            -- `serveDatagram_total` now also pins the delivery log (`w'.sent`, finding
            -- 054); `ServeJustification` is world-output-free, so drop that conjunct.
            have hjust : ServeJustification net ns ra ednsBuf rttOf sbelt query qu t
                cache w c₃ := by
              obtain ⟨m, rr, cache'', w₄, hrun', hdisj⟩ := hrest
              refine Or.inr ⟨qm, hqm, hqt, hqcl, hrdm, m, rr, cache'', w₄, hrun', ?_⟩
              rcases hdisj with
                  ⟨msg, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpk, -⟩ |
                  ⟨resp, slist, v, cOut, coutM, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
                    g11, g12, g13, g14, g15, g16, g17, gpk, -, gtrio⟩
              · exact Or.inl ⟨msg, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpk⟩
              · exact Or.inr ⟨resp, slist, v, cOut, coutM, g1, g2, g3, g4, g5, g6, g7, g8,
                  g9, g10, g11, g12, g13, g14, g15, g16, g17, gpk, gtrio⟩
            refine ⟨by rw [← hclassEq]; exact hjust.packOut, ?_⟩
            intro query' qu' t' _ _ hdec' _ _ _ hqu' ht'
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
          have hcOut : cache = c₃ := by
            rcases serveDatagram_unserved clientSock acl sbelt cache d.1 d.2 hg with
              heq | ⟨reply, heq⟩
            · rw [heq] at hs1
              simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hs1
              exact hs1.1
            · rw [heq] at hs1
              obtain ⟨k₃, k₄, u, wS, -, -, hspure⟩ := run_bind_inv hs1
              simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hspure
              exact hspure.1
          rw [← hcOut]
          refine ⟨hpack, ?_⟩
          intro query qu t _ hperm hdec hqr hqp hedns _ _
          exact absurd ⟨hperm, query, hdec, hqr, hqp, hedns⟩ hg
    obtain ⟨hpack₂, hjustStep⟩ := hstep
    have hpack₂' : ServePack cr.1 w₂.clock inCode := by rw [hclk₂]; exact hpack₂
    obtain ⟨hpackOut, hclkOut, horOut, hwOut, htrace⟩ :=
      ih m₂ cr.1 cr.2 w₂ out w' h2 (fun d' hd' => hscope d' (List.mem_cons_of_mem d hd'))
        htick₂ hpack₂' hclock₂ hw₂ hwTcp₂
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
    (htick : ∀ i, w.tick i = 0)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w) :
    ServePack out.1 w.clock inCode
    ∧ w'.clock = w.clock ∧ w'.oracle = w.oracle
    ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w'
    ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl sbelt ds
        DnsCache.empty Server.RateBucket.empty w :=
  serveSeq_sound net ns ra ednsBuf rttOf clientSock acl sbelt hnetWF hGlSbelt
    ds n DnsCache.empty Server.RateBucket.empty w out w' hrun (fun _ _ => trivial)
    htick (ServePack_empty w.clock inCode) hclock hw hwTcp

/-- `serveSeq_total` at the production entry point: for an SBELT built by
    `DnsSList.mkSbelt` (as `main` does with the root hints, VeriDNS/Main.lean),
    the `GluelessProv` premise is discharged by `GluelessProv_mkSbelt` —
    no caller-supplied SBELT fact remains. -/
theorem serveSeq_total_mkSbelt (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (clientSock : Unit) (acl : Server.ClientAcl)
    (roots : Array (ByteArray × BitVec 32))
    (hnetWF : net.WF)
    (ds : List (ByteArray × ByteArray)) (n : Nat) (w : World)
    (out : DnsCache × Server.RateBucket) (w' : World)
    (hrun : Prog.run n
        (serveSeq clientSock acl (DnsSList.mkSbelt roots) ds
          DnsCache.empty Server.RateBucket.empty) w
      = some (out, w'))
    (htick : ∀ i, w.tick i = 0)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w) :
    ServePack out.1 w.clock inCode
    ∧ w'.clock = w.clock ∧ w'.oracle = w.oracle
    ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w'
    ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl (DnsSList.mkSbelt roots) ds
        DnsCache.empty Server.RateBucket.empty w :=
  serveSeq_total net ns ra ednsBuf rttOf clientSock acl (DnsSList.mkSbelt roots)
    hnetWF (GluelessProv_mkSbelt roots) ds n w out w' hrun htick hclock hw hwTcp


/-! ### Priming base case (audit W4 finding #1)

`main` does not serve from the empty cache: it serves from
`primeRootHints`, whose cache writes are `Server.primeWrites` applied to a
decode→`sanitizeTtlsCap` reply (`Server.forwardQuery` sanitizes every
response before returning it).  The lemmas below prove the serve invariant
pack at that primed cache from the wire facts alone — no network-honesty
hypothesis is needed, because the ingest filter `Server.primeKeepRR` keeps
only class-IN NS / 4-byte-A records, whose abstraction is total on
canonically decoded blobs. -/

/-- The clock-stable members of `ServePack` (everything but the size bound,
which is only re-established by the closing `boundLru`). -/
private def PrimePackCore (cache : DnsCache) (clk : UInt32) (qc : BitVec 16) : Prop :=
  CacheWf cache clk
  ∧ CacheNsCanon cache
  ∧ CacheCnameCanon cache
  ∧ (∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
  ∧ CacheNegWf cache qc
  ∧ CacheNsDistinct cache
  ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache
  ∧ VeriDNS.Proof.DeliveredWire.CacheRecCanon cache
  ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cache

/-- Everything the pack proof needs about one raw kept by the priming
filter: it is a canonical ingress blob from `sect`, and any parse of it is a
class-IN NS record or a class-IN A record with 4-byte rdata. -/
private theorem primeKeep_facts {sect : Array ByteArray} {b : ByteArray}
    (hcanon : VeriDNS.Proof.DeliveredWire.CanonicalSection sect)
    (hb : b ∈ ((Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        ⟨#[0]⟩ sect).filter Server.primeKeepRR).toList) :
    VeriDNS.Proof.Message.CanonicalRR b
    ∧ b ∈ sect
    ∧ ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        rr.class = (1 : BitVec 16)
        ∧ (rr.type = (2 : BitVec 16)
            ∨ (rr.type = (1 : BitVec 16) ∧ rr.rdata.size = 4)) := by
  have hbf : b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
      ⟨#[0]⟩ sect).filter Server.primeKeepRR := Array.mem_def.mpr hb
  obtain ⟨hbb, hkeep⟩ := Array.mem_filter.mp hbf
  have hsect : b ∈ sect.toList := bailiwickRaws_toList_sub (Array.mem_def.mp hbb)
  refine ⟨hcanon b (Array.mem_def.mpr hsect), Array.mem_def.mpr hsect, ?_⟩
  intro rr hp
  unfold Server.primeKeepRR at hkeep
  rw [hp] at hkeep
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hkeep
  exact ⟨hkeep.1, hkeep.2.imp id (fun h => ⟨h.1, h.2⟩)⟩

/-- Totality of the abstraction on the record shapes the priming filter
keeps: canonical owner name (any parse), canonical NS rdata (from the
ingress blob shape), a 4-byte A rdata, and class IN. -/
private theorem primeKeep_αRR_isSome {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hcanon : VeriDNS.Proof.Message.CanonicalRR b)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hcls : rr.class = (1 : BitVec 16))
    (hty : rr.type = (2 : BitVec 16) ∨ (rr.type = (1 : BitVec 16) ∧ rr.rdata.size = 4)) :
    (αRR rr).isSome = true := by
  obtain ⟨na, hna, -, -⟩ := parseRaw_name_canonical hp
  have hcl : αClass rr.class = some RRClass.in := by rw [hcls]; rfl
  have hrd : (αRData rr.type rr.rdata).isSome = true := by
    rcases hty with h2 | ⟨h1, hsz⟩
    · obtain ⟨nrd, hnrd, -, -, -⟩ := canonicalRR_nsRdata_canonical hcanon hp h2
      rw [h2]
      show ((αName rr.rdata).map VeriDNS.Spec.Net.RData.ns).isSome = true
      rw [hnrd]
      rfl
    · rw [h1]
      show ((αIPv4 rr.rdata).map VeriDNS.Spec.Net.RData.a).isSome = true
      unfold αIPv4
      rw [if_pos hsz]
      rfl
  obtain ⟨rd, hrdv⟩ := Option.isSome_iff_exists.mp hrd
  unfold αRR
  rw [hna, hrdv, hcl]
  rfl

/-- One priming ingest preserves the clock-stable pack members. -/
private theorem primePackCore_write {c : DnsCache} {qc : BitVec 16}
    (resp : VeriDNS.Spec.Format) (fraws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
        ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
        ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
        ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (hclock : now.toNat + 604800 < 2 ^ 32)
    (hcanon : ∀ b ∈ fraws.toList, VeriDNS.Proof.Message.CanonicalRR b)
    (hkeep : ∀ b ∈ fraws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        rr.class = (1 : BitVec 16)
        ∧ (rr.type = (2 : BitVec 16)
            ∨ (rr.type = (1 : BitVec 16) ∧ rr.rdata.size = 4)))
    (httl : ∀ b ∈ fraws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        rr.ttl.toNat ≤ 604800)
    (hpack : PrimePackCore c now qc) :
    PrimePackCore (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      c resp fraws cred now) now qc := by
  obtain ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hrec, hnsoa⟩ := hpack
  have hval : ∀ b ∈ fraws.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (αRR rr).isSome = true := by
    intro b hb rr hp
    obtain ⟨hcls, hty⟩ := hkeep b hb rr hp
    exact primeKeep_αRR_isSome (hcanon b hb) hp hcls hty
  have hno : ∀ b ∈ fraws.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat := by
    intro b hb rr hp
    exact uint32_add_ttl_toNat now rr.ttl.toNat (httl b hb rr hp) hclock
  obtain ⟨hrec', hnsoa'⟩ := stateSections_write hrec hnsoa resp fraws cred now hcanon
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hrec', hnsoa'⟩
  · apply CacheWf_cacheUnlessTruncated _ _ _ _ _ hwf hcred
    intro raw hraw rr hp
    exact parseRaw_entry_canonical cred now hp (normRaws_hval hval raw hraw rr hp)
      (normRaws_hno hno raw hraw rr hp)
  · apply CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hns
    intro raw hraw rr hp htype
    exact canonicalRR_nsRdata_canonical (hcanon raw hraw) hp htype
  · apply CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hcn
    intro raw hraw rr hp htype
    exact canonicalRR_cnameRdata_canonical (hcanon raw hraw) hp htype
  · exact wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
  · exact CacheNegWf_cacheUnlessTruncated _ _ _ _ _ hneg
  · exact CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hnsd
  · exact VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hoe _ _ _ _

private theorem primeWrites_eq (cache : DnsCache) (resp : VeriDNS.Spec.Format)
    (now : UInt32) :
    Server.primeWrites cache resp now
      = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
            ((Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                ⟨#[0]⟩ resp.answer).filter Server.primeKeepRR)
            (Resolver.credAnswer (resp.header.aa == 1)) now)
          resp
          ((Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              ⟨#[0]⟩ resp.additional).filter Server.primeKeepRR)
          Resolver.credAdditional now).boundLru #[] now := rfl

/-- THE PRIMING BASE CASE: the serve invariant pack survives the root-hint
priming writes.  `resp` is only constrained to be what `forwardQuery`
actually hands `primeRootHints`: a `Message.decode`-ok reply passed through
`sanitizeTtlsCap`.  No honesty assumption on the network is needed — decode
canonicity, the TTL cap, and the `primeKeepRR` ingest filter discharge every
per-record obligation. -/
theorem ServePack_primeWrites (cache : DnsCache) {bytes : ByteArray}
    {resp0 resp : VeriDNS.Spec.Format} (now : UInt32) (qc : BitVec 16)
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsan : Server.sanitizeTtlsCap resp0 = some resp)
    (hclock : now.toNat + 604800 < 2 ^ 32)
    (hpack : ServePack cache now qc) :
    ServePack (Server.primeWrites cache resp now) now qc := by
  have hsw : SectionsWf resp := by
    have hresp : resp = Server.capTtls (Edns.stripOpt resp0) := by
      unfold Server.sanitizeTtlsCap at hsan
      exact (Option.some.inj hsan).symm
    rw [hresp]
    exact sectionsWf_capTtls_stripOpt_of_decode hdec
  obtain ⟨hcanAns, -, hcanAdd, -, -⟩ := hsw
  obtain ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, -, hrec, hnsoa⟩ := hpack
  have core0 : PrimePackCore cache now qc :=
    ⟨hwf, hns, hcn, hwfrr, hneg, hnsd, hoe, hrec, hnsoa⟩
  have core1 : PrimePackCore (Resolver.cacheUnlessTruncated
      (RR := VeriDNS.Spec.ResourceRecord) cache resp
      ((Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
          ⟨#[0]⟩ resp.answer).filter Server.primeKeepRR)
      (Resolver.credAnswer (resp.header.aa == 1)) now) now qc := by
    apply primePackCore_write resp _ _ now ?_ hclock
      (fun b hb => (primeKeep_facts hcanAns hb).1)
      (fun b hb => (primeKeep_facts hcanAns hb).2.2)
      (fun b hb rr hp => VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 resp hsan b
        (Or.inl (Or.inl (primeKeep_facts hcanAns hb).2.1)) rr hp)
      core0
    unfold Resolver.credAnswer
    by_cases ha : (resp.header.aa == 1) = true
    · rw [if_pos ha]
      exact Or.inl rfl
    · rw [if_neg ha]
      exact Or.inr (Or.inr (Or.inl rfl))
  have core2 := primePackCore_write resp
    ((Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        ⟨#[0]⟩ resp.additional).filter Server.primeKeepRR)
    Resolver.credAdditional now (Or.inr (Or.inr (Or.inr rfl))) hclock
    (fun b hb => (primeKeep_facts hcanAdd hb).1)
    (fun b hb => (primeKeep_facts hcanAdd hb).2.2)
    (fun b hb rr hp => VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 resp hsan b
      (Or.inr (primeKeep_facts hcanAdd hb).2.1) rr hp)
    core1
  obtain ⟨hwf2, hns2, hcn2, hwfrr2, hneg2, hnsd2, hoe2, hrec2, hnsoa2⟩ := core2
  rw [primeWrites_eq]
  exact ⟨CacheWf_boundLru _ _ _ _ hwf2,
    CacheNsCanon_boundLru _ _ _ hns2,
    CacheCnameCanon_boundLru _ _ _ hcn2,
    wfrrAll_boundLru _ _ hwfrr2,
    CacheNegWf_boundLru _ _ hneg2,
    CacheNsDistinct_boundLru _ _ _ hnsd2,
    VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hoe2,
    VeriDNS.Proof.Cache.boundLru_bounded _ _ _,
    VeriDNS.Proof.DeliveredWire.cacheRecCanon_boundLru _ _ _ hrec2,
    cacheNegSoaCanon_boundLru _ _ _ hnsoa2⟩

/-- The primed cache at the empty base: exactly what `main` builds before
serving (modulo the run-equations `hdec`/`hsan`, which record what
`forwardQuery` returned). -/
theorem ServePack_primeWrites_empty {bytes : ByteArray}
    {resp0 resp : VeriDNS.Spec.Format} (now : UInt32) (qc : BitVec 16)
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsan : Server.sanitizeTtlsCap resp0 = some resp)
    (hclock : now.toNat + 604800 < 2 ^ 32) :
    ServePack (Server.primeWrites DnsCache.empty resp now) now qc :=
  ServePack_primeWrites DnsCache.empty now qc hdec hsan hclock
    (ServePack_empty now qc)

/-- `serveSeq_total` at the REAL initial state: the SBELT is
`DnsSList.mkSbelt` (as in `main`) and the initial cache is the root-hint
primed cache (`primeWrites` on the sanitized priming reply), not
`DnsCache.empty`.  Together with `serveSeq_total_mkSbelt` this closes the
deployed invariant chain's base case: every capstone premise about the
initial cache is now established, not assumed. -/
theorem serveSeq_total_primed (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (clientSock : Unit) (acl : Server.ClientAcl)
    (roots : Array (ByteArray × BitVec 32))
    (hnetWF : net.WF)
    {bytes : ByteArray} {resp0 resp : VeriDNS.Spec.Format}
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsan : Server.sanitizeTtlsCap resp0 = some resp)
    (ds : List (ByteArray × ByteArray)) (n : Nat) (w : World)
    (out : DnsCache × Server.RateBucket) (w' : World)
    (hrun : Prog.run n
        (serveSeq clientSock acl (DnsSList.mkSbelt roots) ds
          (Server.primeWrites DnsCache.empty resp w.clock) Server.RateBucket.empty) w
      = some (out, w'))
    (htick : ∀ i, w.tick i = 0)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w) :
    ServePack out.1 w.clock inCode
    ∧ w'.clock = w.clock ∧ w'.oracle = w.oracle
    ∧ WorldModels net ns ra ednsBuf (αTime w.clock) w'
    ∧ JustifiedTrace net ns ra ednsBuf rttOf clientSock acl (DnsSList.mkSbelt roots) ds
        (Server.primeWrites DnsCache.empty resp w.clock) Server.RateBucket.empty w :=
  serveSeq_sound net ns ra ednsBuf rttOf clientSock acl (DnsSList.mkSbelt roots)
    hnetWF (GluelessProv_mkSbelt roots) ds n
    (Server.primeWrites DnsCache.empty resp w.clock) Server.RateBucket.empty
    w out w' hrun (fun _ _ => trivial)
    htick (ServePack_primeWrites_empty w.clock inCode hdec hsan hclock) hclock hw hwTcp
