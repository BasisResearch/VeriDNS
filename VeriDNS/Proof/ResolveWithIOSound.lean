import VeriDNS.Proof.IoResumeSound
import VeriDNS.Proof.IoResumeErrorSound
import VeriDNS.Proof.SentMinimised
import VeriDNS.Proof.DeliveredWire
import VeriDNS.Proof.AnswerScrubAlpha
import VeriDNS.Proof.Server
import VeriDNS.Proof.Edns




open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache VeriDNS.Spec

theorem resolve_paused_inv
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hα : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused st)) :
    ∃ sname' chain',
      Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qu.qtype qu.qclass now0 8 qu.qname #[]
          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .miss sname' chain'
      ∧ st.resources.cache = cache
      ∧ st.resources.sname = sname'
      ∧ st.now = now0
      ∧ st.cnameChain = chain'
      ∧ st.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries
      ∧ st.lastQuery = some query
      ∧ st.resources.sbelt = sbelt
      ∧ ( st.resources.slist = default
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
                sname' cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now0 128 = some (nsNames, mc)
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList)
                  (NS := VeriDNS.Spec.SlistEntry) nsNames
                  (reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now0 nsNames) mc)
          ∨ st.resources.slist = sbelt ) := by
  unfold Resolver.resolve at hres
  cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now0 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) with
  | negative rc soaAuth chainN =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal, hqu, hla] at hres
    exact absurd hres (by simp)
  | answerHit snameH chainH rrs =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal, hqu, hla] at hres
    exact absurd hres (by simp)
  | abort =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal, hqu, hla] at hres
    exact absurd hres (by simp)
  | miss sname' chain' =>
    obtain ⟨stP, hloopP, hPcache, hPsname, hPnow, hPchain, hPstep, hPlq, hPsbelt, hPdisj⟩ :=
      loop_checkAnswer_miss_struct
        (Resolver.initFromQuery (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
          (RR := VeriDNS.Spec.ResourceRecord) query sbelt now0 cache)
        query qu sname' chain'
        rfl rfl hqu
        (by rw [initFromQuery_sname query sbelt now0 cache qu hqu]; exact hla)
        (by
          intro hsEq
          rw [initFromQuery_sname query sbelt now0 cache qu hqu] at hsEq
          rcases localAnswer_miss_ident_or_fresh cache qu.qtype qu.qclass now0 8
              qu.qname #[] (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
              sname' chain' hla with ⟨-, h2⟩ | hfr
          · exact h2
          · exfalso
            have hmem : qu.qname ∈ (Resolver.cnameChaseVisited
                (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]).toList := by
              simp [Resolver.cnameChaseVisited]
            have hfalse := hfr qu.qname hmem
            rw [show sname' = qu.qname from hsEq] at hfalse
            rw [nameEqCI_of_αName_canonical (VeriDNS.Spec.Net.nameEq_refl qn) hcanon hcanon
              (fun x hx => (αName_valid hα x hx).2) (fun x hx => (αName_valid hα x hx).2)] at hfalse
            exact absurd hfalse (by simp))
        rfl 61
    have hEq : Except.ok (Resolver.ResolveYield.paused stP)
        = (Except.ok (Resolver.ResolveYield.paused st) :
            Except String (Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
              VeriDNS.Spec.ResourceRecord)) := by
      rw [← hloopP]; exact hres
    have hstEq : stP = st := by injection hEq with h1; injection h1
    subst hstEq
    refine ⟨sname', chain', rfl, hPcache, hPsname, hPnow, hPchain, hPstep, hPlq, hPsbelt, ?_⟩
    rcases hPdisj with h | h | ⟨nsNames, mc, hw, heq⟩ | h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨nsNames, mc, hw, heq⟩)
    · exact Or.inr (Or.inr h)

theorem paused_chain_answerWriteWf
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hα : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hwf : CacheWf cache now0) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache
      = .ok (.paused st)) :
    AnswerWriteWf st.cnameChain now0 := by
  obtain ⟨sname', chain', hla, -, -, -, hchain, -, -, -, -⟩ :=
    resolve_paused_inv query qu qn sbelt now0 cache st hqu hα hcanon hres
  rw [hchain]
  exact answerWriteWf_of_chain_provenance hwf hns hcnc hwfrr
    (localAnswer_chain_provenance 8 qu.qname #[] _ chain' (by rw [hla]; rfl)
      (by intro raw h; simp at h))

theorem resolveWithIO_paused_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32) (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (query : VeriDNS.Spec.Format) (q : Query) (depth fuel' : Nat)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (cache : DnsCache) (c : Cache) (w w' : World) (now0 : UInt32) (now : Net.Time)
    (nseen seen : List Name) (depthFloor : Nat) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state))
    (hSM : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hwmTcp : WorldModelsTcp net ns ra ednsBuf now w)
    (hCacheWf : CacheWf state.resources.cache state.now)
    (hNsCanon : CacheNsCanon state.resources.cache)
    (hCnCanon : CacheCnameCanon state.resources.cache)
    (hwfrr : ∀ e ∈ state.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNegWf : ∀ qu : VeriDNS.Spec.Question,
        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
        CacheNegWf state.resources.cache qu.qclass)
    (hNsDistinct : CacheNsDistinct state.resources.cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey state.resources.cache)
    (hCap : state.resources.cache.records.size ≤ DnsCache.capacity)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfreshInv : ∀ b ∈ seen, b.length < depthFloor)
    (hMC : state.resources.slist.matchCount = depthFloor)
    (hGlProv : GluelessProv state.resources.slist)
    (hGlBelt : GluelessProv state.resources.sbelt)
    (hqm : ∀ qu : VeriDNS.Spec.Question,
        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
        αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass)
    (hrd : q.rd = false) (hqstar : q.qtype ≠ QType.star) (hqin : q.qclass = RRClass.in)
    (hclock : state.now.toNat + 604800 < 2 ^ 32)
    (hsnameCanon : state.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hqlen : q.qname.length ≤ 127)
    (hqvalid : ∀ x ∈ q.qname, 0 < x.size ∧ x.size ≤ 63)
    (hCCM : CnameChainModels state q nseen)
    (hAW : AnswerWriteWf state.cnameChain state.now)
    (hstep : state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ slist v coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v coutM
      ∧ (modelSlistOf state.resources.slist).Subperm slist
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = αSection state.cnameChain ++ v.answer
      ∧ CacheRefines (αCache cout) coutM
      ∧ WorldModels net ns ra ednsBuf now w'
      ∧ CacheWf cout state.now
      ∧ CacheNsCanon cout
      ∧ CacheCnameCanon cout
      ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
      ∧ (∀ qu : VeriDNS.Spec.Question,
          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
          CacheNegWf cout qu.qclass)
      ∧ CacheNsDistinct cout
      ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
      ∧ cout.records.size ≤ DnsCache.capacity
      ∧ AnswerWriteWf resp.answer state.now := by
  have hrun' : Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state (now0 + budget) depth fuel' (Server.seedRevealed state)) w
      = some ((.ok resp, cout), w') := by
    unfold Server.resolveWithIO at hrun
    simp only [hpaused] at hrun
    exact hrun
  exact ioResumeLoop_sound net ns ra ednsBuf rttOf sbelt (now0 + budget) hnetWF hGlSbelt
    n q depth fuel' (Server.seedRevealed state) state c w w' now nseen seen depthFloor resp cout
    hSM hwmTcp hCacheWf hNsCanon hCnCanon hwfrr hNegWf hNsDistinct hOE hCap hmiss hnmiss
    hfreshInv hMC hGlProv hGlBelt hqm hrd hqstar hqin hclock hsnameCanon hqlen hqvalid hCCM hAW hstep hrun'

theorem resolveWithIO_paused_sound'
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32) (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (q : Query) (depth fuel' : Nat)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (cache : DnsCache) (c : Cache) (w w' : World) (now0 : UInt32) (now : Net.Time)
    (nseen seen : List Name) (depthFloor : Nat) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hα : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state))
    (hCacheWf : CacheWf cache now0)
    (hNsCanon : CacheNsCanon cache)
    (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache)
    (hCap : cache.records.size ≤ DnsCache.capacity)
    (hclock : now0.toNat + 604800 < 2 ^ 32)
    (hSM : StateModels net ns ra ednsBuf rttOf now q state c w)
    (hwmTcp : WorldModelsTcp net ns ra ednsBuf now w)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfreshInv : ∀ b ∈ seen, b.length < depthFloor)
    (hMC : state.resources.slist.matchCount = depthFloor)
    (hGlProv : GluelessProv state.resources.slist)
    (hqm : αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass)
    (hrd : q.rd = false) (hqstar : q.qtype ≠ QType.star) (hqin : q.qclass = RRClass.in)
    (hsnameCanon : state.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hqlen : q.qname.length ≤ 127)
    (hqvalid : ∀ x ∈ q.qname, 0 < x.size ∧ x.size ≤ 63)
    (hCCM : CnameChainModels state q nseen)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ slist v coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v coutM
      ∧ (modelSlistOf state.resources.slist).Subperm slist
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = αSection state.cnameChain ++ v.answer
      ∧ CacheRefines (αCache cout) coutM
      ∧ WorldModels net ns ra ednsBuf now w'
      ∧ CacheWf cout state.now
      ∧ CacheNsCanon cout
      ∧ CacheCnameCanon cout
      ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
      ∧ (∀ qu : VeriDNS.Spec.Question,
          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
          CacheNegWf cout qu.qclass)
      ∧ CacheNsDistinct cout
      ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
      ∧ cout.records.size ≤ DnsCache.capacity
      ∧ AnswerWriteWf resp.answer state.now := by
  obtain ⟨sname', chain', hla, hstCache, hstSname, hstNow, hstChain, hstStep, hstLQ, hstSbelt, -⟩ :=
    resolve_paused_inv query qu qn sbelt now0 cache state hqu hα hcanon hpaused
  exact resolveWithIO_paused_sound net ns ra ednsBuf rttOf sbelt budget hnetWF hGlSbelt
    n query q depth fuel' state cache c w w' now0 now nseen seen depthFloor resp cout
    hpaused hSM hwmTcp
    (by rw [hstCache, hstNow]; exact hCacheWf)
    (by rw [hstCache]; exact hNsCanon)
    (by rw [hstCache]; exact hCnCanon)
    (by rw [hstCache]; exact hwfrr)
    (by
      intro qu' ⟨q₀, hlq, hq0⟩
      have hq : query = q₀ := Option.some.inj (hstLQ.symm.trans hlq)
      subst hq
      rw [hqu] at hq0
      obtain rfl := Option.some.inj hq0
      rw [hstCache]; exact hNegWf)
    (by rw [hstCache]; exact hNsDistinct)
    (by rw [hstCache]; exact hOE)
    (by rw [hstCache]; exact hCap)
    hmiss hnmiss hfreshInv hMC hGlProv
    (by rw [hstSbelt]; exact hGlSbelt)
    (by
      intro qu' ⟨q₀, hlq, hq0⟩
      have hq : query = q₀ := Option.some.inj (hstLQ.symm.trans hlq)
      subst hq
      rw [hqu] at hq0
      obtain rfl := Option.some.inj hq0
      exact hqm)
    hrd hqstar hqin
    (by rw [hstNow]; exact hclock)
    hsnameCanon hqlen hqvalid hCCM
    (by
      rw [hstNow]
      exact paused_chain_answerWriteWf query qu qn sbelt now0 cache state hqu hα hcanon
        hCacheWf hNsCanon hCnCanon hwfrr hpaused)
    hstStep hrun

theorem paused_StateModels_noPeel
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (w : World)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (hw : WorldModels net ns ra ednsBuf (αTime now0) w)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state))
    (hnoPeel : state.resources.sname = qu.qname) :
    StateModels net ns ra ednsBuf rttOf (αTime now0) qm state (αCache cache) w := by
  obtain ⟨sname', chain', hla, hstCache, hstSname, hstNow, hstChain, hstStep, hstLQ, hstSbelt, -⟩ :=
    resolve_paused_inv query qu qm.qname sbelt now0 cache state hqu hqm hcanon hpaused
  have hSMinit := StateModels_initFromQuery (net := net) (ns := ns) (ra := ra) (ednsBuf := ednsBuf)
    (rttOf := rttOf) (q := query) (sbelt := sbelt) (now := now0) (initCache := cache)
    (qu := qu) (qm := qm) (w := w) hqu hqm hw
  exact StateModels_cacheCname_preserve hSMinit
    (by rw [hstCache, initFromQuery_cache])
    (by rw [hnoPeel]; exact hqm)
    (by rw [hstNow, initFromQuery_now])

theorem localAnswer_miss_reads (cache : DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
    (sname' : ByteArray) (chain' : Array ByteArray)
    (h : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname chain visited = .miss sname' chain') :
    cache.lookupNegative sname qt qc now = none
      ∧ (cache.lookupAnswerable sname qt qc now).isEmpty = true := by
  cases fuel with
  | zero => exact absurd h (by simp [Resolver.localAnswer])
  | succ f =>
    unfold Resolver.localAnswer at h
    cases hneg : (VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
        cache sname qt qc now) with
    | some rc => rw [hneg] at h; exact absurd h (by simp)
    | none =>
      rw [hneg] at h
      by_cases hemp : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true
      · exact ⟨hneg, hemp⟩
      · rw [if_neg hemp] at h; exact absurd h (by simp)

theorem paused_cacheMiss
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hwf : CacheWf cache now0)
    (hnegwf : CacheNegWf cache qu.qclass)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state)) :
    (αCache cache).hit (αTime now0) qm = []
      ∧ (αCache cache).negHit (αTime now0) qm = false := by
  obtain ⟨sname', chain', hla, -⟩ :=
    resolve_paused_inv query qu qm.qname sbelt now0 cache state hqu hqm hcanon hpaused
  obtain ⟨hneg, hemp⟩ := localAnswer_miss_reads cache qu.qtype qu.qclass now0 8 qu.qname #[]
    (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) sname' chain' hla
  exact ⟨hit_nil_of_lookupAnswerable_empty cache qu.qname qu.qtype qu.qclass now0 qm t
          hemp hqm ht hqq hqc hcanon hvN hwf,
         lookupNegative_none_negHit_false cache qu.qname qu.qtype qu.qclass now0 qm t
          ht hqq hcanon hvN hnegwf hneg⟩

theorem localAnswer_abort_reads (cache : DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
    (h : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited = .abort) :
    cache.lookupNegative sname qt qc now = none
      ∧ (cache.lookupAnswerable sname qt qc now).isEmpty = true := by
  unfold Resolver.localAnswer at h
  cases hneg : (VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
      cache sname qt qc now) with
  | some rc => rw [hneg] at h; exact absurd h (by simp)
  | none =>
    rw [hneg] at h
    by_cases hemp : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true
    · exact ⟨hneg, hemp⟩
    · rw [if_neg hemp] at h; exact absurd h (by simp)

/-- The pure resolver core can only error out of its initial (pre-network) segment via
the local CNAME-chase abort — and an abort implies the entry-point cache reads missed:
no cached negative entry and no answerable RRset for the client's question. -/
theorem resolve_error_inv
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache) (msg : String)
    (hqu : query.question[0]? = some qu)
    (hα : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .error msg) :
    Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now0 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .abort := by
  unfold Resolver.resolve at hres
  cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now0 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) with
  | negative rc soaAuth chainN =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal, hqu, hla] at hres
    exact absurd hres (by simp)
  | answerHit snameH chainH rrs =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal, hqu, hla] at hres
    exact absurd hres (by simp)
  | miss sname' chain' =>
    exfalso
    obtain ⟨stP, hloopP, -, -, -, -, -, -, -, -⟩ :=
      loop_checkAnswer_miss_struct
        (Resolver.initFromQuery (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
          (RR := VeriDNS.Spec.ResourceRecord) query sbelt now0 cache)
        query qu sname' chain'
        rfl rfl hqu
        (by rw [initFromQuery_sname query sbelt now0 cache qu hqu]; exact hla)
        (by
          intro hsEq
          rw [initFromQuery_sname query sbelt now0 cache qu hqu] at hsEq
          rcases localAnswer_miss_ident_or_fresh cache qu.qtype qu.qclass now0 8
              qu.qname #[] (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
              sname' chain' hla with ⟨-, h2⟩ | hfr
          · exact h2
          · exfalso
            have hmem : qu.qname ∈ (Resolver.cnameChaseVisited
                (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]).toList := by
              simp [Resolver.cnameChaseVisited]
            have hfalse := hfr qu.qname hmem
            rw [show sname' = qu.qname from hsEq] at hfalse
            rw [nameEqCI_of_αName_canonical (VeriDNS.Spec.Net.nameEq_refl qn) hcanon hcanon
              (fun x hx => (αName_valid hα x hx).2) (fun x hx => (αName_valid hα x hx).2)] at hfalse
            exact absurd hfalse (by simp))
        rfl 61
    have hEq : Except.ok (Resolver.ResolveYield.paused stP)
        = (Except.error msg :
            Except String (Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
              VeriDNS.Spec.ResourceRecord)) := by
      rw [← hloopP]; exact hres
    exact absurd hEq (by simp)
  | abort => rfl

/-- Direct-error twin of `paused_cacheMiss`: if the pure resolver core errors out of its
initial segment, the start cache verifiably missed the client's question. -/
theorem resolve_error_cacheMiss
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache) (msg : String)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hwf : CacheWf cache now0)
    (hnegwf : CacheNegWf cache qu.qclass)
    (herr : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .error msg) :
    (αCache cache).hit (αTime now0) qm = []
      ∧ (αCache cache).negHit (αTime now0) qm = false := by
  have hla := resolve_error_inv query qu qm.qname sbelt now0 cache msg hqu hqm hcanon herr
  obtain ⟨hneg, hemp⟩ := localAnswer_abort_reads cache qu.qtype qu.qclass now0 7 qu.qname #[]
    (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) hla
  exact ⟨hit_nil_of_lookupAnswerable_empty cache qu.qname qu.qtype qu.qclass now0 qm t
          hemp hqm ht hqq hqc hcanon hvN hwf,
         lookupNegative_none_negHit_false cache qu.qname qu.qtype qu.qclass now0 qm t
          ht hqq hcanon hvN hnegwf hneg⟩

/-- Every SERVFAIL exit of the runtime resolver core establishes the model give-up
witness's cache-miss facts: whichever error path fired (deadline, IO-round fuel,
glueless depth, address-less SLIST, CNAME abort, …), the start cache had neither a
positive nor a negative cached answer for the client's question (RFC 1034 §5.3.1
step 1 — giving up never shadows a cached answer). -/
theorem resolveWithIO_error_cacheMiss
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (fuel' depth : Nat) (budget : UInt32)
    (w w' : World) (msg : String) (cache' : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hwf : CacheWf cache now0)
    (hnegwf : CacheNegWf cache qu.qclass)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.error msg, cache'), w')) :
    (αCache cache).hit (αTime now0) qm = []
      ∧ (αCache cache).negHit (αTime now0) qm = false := by
  unfold Server.resolveWithIO at hrun
  cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache with
  | ok y =>
    cases y with
    | done resp₀ stF =>
      rw [hres, run_pure'] at hrun
      exact absurd hrun (by simp)
    | paused st =>
      exact paused_cacheMiss query qu qm t sbelt now0 cache st
        hqu hqm hcanon ht hqq hqc hvN hwf hnegwf hres
  | error e =>
    exact resolve_error_cacheMiss query qu qm t sbelt now0 cache e
      hqu hqm hcanon ht hqq hqc hvN hwf hnegwf hres

/-- Visibility corollary for the capstone error arms: a SERVFAIL exit of the resolver
core always carries a model `GaveUpWitness` — the give-up verdict is justified, never
free (`Resolves.gaveUp`'s premise is dischargeable on every implementation error path). -/
theorem servfail_means_gaveUpWitness
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (fuel' depth : Nat) (budget : UInt32)
    (w w' : World) (msg : String) (cache' : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hwf : CacheWf cache now0)
    (hnegwf : CacheNegWf cache qu.qclass)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.error msg, cache'), w')) :
    VeriDNS.Spec.Net.GaveUpWitness (αTime now0) (αCache cache) [] qm := by
  obtain ⟨hmiss, hnmiss⟩ := resolveWithIO_error_cacheMiss n query qu qm t sbelt now0 cache
    fuel' depth budget w w' msg cache' hqu hqm hcanon ht hqq hqc hvN hwf hnegwf hrun
  exact .serversExhausted hmiss hnmiss rfl

theorem paused_CnameChainModels_noPeel
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state))
    (hchain : state.cnameChain = #[]) :
    CnameChainModels state qm [] := by
  obtain ⟨sname', chain', hla, hstCache, hstSname, hstNow, hstChain, hstStep, hstLQ, hstSbelt, -⟩ :=
    resolve_paused_inv query qu qm.qname sbelt now0 cache state hqu hqm hcanon hpaused
  unfold CnameChainModels
  intro nm hnm
  rw [List.mem_cons] at hnm
  rcases hnm with rfl | hnm
  · refine ⟨qu.qname, ?_, hqm, hcanon, hvN⟩
    rw [hstLQ, hchain]
    simp only [Option.bind_some, hqu, Option.elim]
    simp [Resolver.cnameChaseVisited]
  · simp at hnm

theorem paused_GluelessProv
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hα : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hNsCanon : CacheNsCanon cache)
    (hGlSbelt : GluelessProv sbelt)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state)) :
    GluelessProv state.resources.slist := by
  obtain ⟨sname', chain', hla, hstCache, hstSname, hstNow, hstChain, hstStep, hstLQ, hstSbelt, hdisj⟩ :=
    resolve_paused_inv query qu qn sbelt now0 cache state hqu hα hcanon hpaused
  rcases hdisj with h | ⟨nsNames, mc, hw, heq⟩ | h
  · rw [h]; exact GluelessProv_default
  · rw [heq]
    exact GluelessProv_fromNsWithGlueAll_of_canonical nsNames
      (reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now0 nsNames) mc
      (walkNs_names_canonical cache now0 hNsCanon 128 sname' nsNames mc hw)
  · rw [h]; exact hGlSbelt

theorem resolveWithIO_noPeel_paused_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32) (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (depth fuel' : Nat)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (cache : DnsCache) (w w' : World) (now0 : UInt32)
    (resp : VeriDNS.Spec.Format) (cout : DnsCache)
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
    (hCacheWf : CacheWf cache now0) (hNsCanon : CacheNsCanon cache) (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache) (hCap : cache.records.size ≤ DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hclock : now0.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime now0) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime now0) w)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state))
    (hnoPeel : state.resources.sname = qu.qname)
    (hchain : state.cnameChain = #[])
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ slist v coutM,
      HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] (αCache cache) slist qm v coutM
      ∧ (modelSlistOf state.resources.slist).Subperm slist
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = αSection state.cnameChain ++ v.answer
      ∧ CacheRefines (αCache cout) coutM
      ∧ WorldModels net ns ra ednsBuf (αTime now0) w'
      ∧ CacheWf cout state.now
      ∧ CacheNsCanon cout
      ∧ CacheCnameCanon cout
      ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
      ∧ (∀ qu : VeriDNS.Spec.Question,
          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
          CacheNegWf cout qu.qclass)
      ∧ CacheNsDistinct cout
      ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
      ∧ cout.records.size ≤ DnsCache.capacity
      ∧ AnswerWriteWf resp.answer state.now := by
  have hvN : ∀ x ∈ qm.qname, x.size ≤ 63 := fun x hx => (hqvalid x hx).2
  have hαq : αQType qu.qtype = some qm.qtype := by
    have h255 : ¬ qu.qtype.toNat = 255 := hqany
    unfold αQType; rw [if_neg h255, ht]; simp [hqq]
  exact resolveWithIO_paused_sound' net ns ra ednsBuf rttOf sbelt budget hnetWF hGlSbelt
    n query qu qm.qname qm depth fuel' state cache (αCache cache) w w' now0 (αTime now0)
    [] [] state.resources.slist.matchCount resp cout
    hqu hqm hcanon hpaused
    hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hclock
    (paused_StateModels_noPeel net ns ra ednsBuf rttOf query qu qm sbelt now0 cache state w
      hqu hqm hcanon hw hpaused hnoPeel)
    hwTcp
    hNegWf
    (paused_cacheMiss query qu qm t sbelt now0 cache state
      hqu hqm hcanon ht hqq hqc hvN hCacheWf hNegWf hpaused).1
    (paused_cacheMiss query qu qm t sbelt now0 cache state
      hqu hqm hcanon ht hqq hqc hvN hCacheWf hNegWf hpaused).2
    (by intro b hb; simp at hb)
    rfl
    (paused_GluelessProv query qu qm.qname sbelt now0 cache state
      hqu hqm hcanon hNsCanon hGlSbelt hpaused)
    ⟨hαq, hqc⟩
    hrd hqstar hqin
    (by rw [hnoPeel]; exact hcanon)
    hqlen hqvalid
    (paused_CnameChainModels_noPeel query qu qm sbelt now0 cache state
      hqu hqm hcanon hvN hpaused hchain)
    hrun

theorem αType_ne_cname_of_ne5 {qt : BitVec 16} {t : RRType} (ht : αType qt = some t)
    (h5 : (qt == (5 : BitVec 16)) = false) : t ≠ RRType.cname := by
  intro hteq
  subst hteq
  have h5nat : qt.toNat = 5 := by
    unfold αType at ht
    split at ht <;> simp_all
  have hq5 : qt = (5 : BitVec 16) := by
    apply BitVec.eq_of_toNat_eq
    simpa using h5nat
  rw [hq5] at h5
  simp at h5

theorem initVisited_models (qu : VeriDNS.Spec.Question) (qn : Name)
    (hqm : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hvN : ∀ x ∈ qn, x.size ≤ 63) :
    ∀ nm ∈ qn :: ([] : List Name),
      ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
          qu.qname #[]).toList,
        αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
          ∧ (∀ x ∈ nm, x.size ≤ 63) := by
  intro nm hnm
  rcases List.mem_cons.mp hnm with rfl | hnm
  · exact ⟨qu.qname, by simp [Resolver.cnameChaseVisited], hqm, hcanon, hvN⟩
  · simp at hnm

theorem localAnswer_qt5_inv (cache : DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (sname : ByteArray) (chain visited : Array ByteArray)
    (res : Resolver.LocalResult VeriDNS.Spec.ResourceRecord)
    (h5 : (qt == (5 : BitVec 16)) = true)
    (h : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now 8 sname chain visited = res) :
    (∃ rc, VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
        cache sname qt qc now = some rc
      ∧ res = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now) chain)
    ∨ (VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
          cache sname qt qc now = none
      ∧ (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = false
      ∧ res = .answerHit sname chain (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now))
    ∨ res = .miss sname chain := by
  unfold Resolver.localAnswer at h
  cases hn : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
      cache sname qt qc now with
  | some rc =>
    simp only [hn] at h
    exact Or.inl ⟨rc, rfl, h.symm⟩
  | none =>
    simp only [hn] at h
    by_cases hemp : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true
    · rw [if_pos hemp, if_pos h5] at h
      exact Or.inr (Or.inr h.symm)
    · rw [if_neg hemp] at h
      exact Or.inr (Or.inl ⟨rfl, by simpa using hemp, h.symm⟩)

theorem resolveWithIO_paused_full_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32) (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (depth fuel' : Nat)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (cache : DnsCache) (w w' : World) (now0 : UInt32)
    (resp : VeriDNS.Spec.Format) (cout : DnsCache)
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
    (hCacheWf : CacheWf cache now0) (hNsCanon : CacheNsCanon cache) (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache) (hCap : cache.records.size ≤ DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hclock : now0.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime now0) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime now0) w)
    (hpaused : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused state))
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ slist v cOut coutM,
      CacheRefines cOut (αCache cache)
      ∧ HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] cOut slist qm v coutM
      ∧ (modelSlistOf state.resources.slist).Subperm slist
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer
      ∧ CacheRefines (αCache cout) coutM
      ∧ WorldModels net ns ra ednsBuf (αTime now0) w'
      ∧ CacheWf cout state.now
      ∧ CacheNsCanon cout
      ∧ CacheCnameCanon cout
      ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
      ∧ (∀ qu : VeriDNS.Spec.Question,
          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
          CacheNegWf cout qu.qclass)
      ∧ CacheNsDistinct cout
      ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
      ∧ cout.records.size ≤ DnsCache.capacity
      ∧ AnswerWriteWf resp.answer state.now := by
  have hvN : ∀ x ∈ qm.qname, x.size ≤ 63 := fun x hx => (hqvalid x hx).2
  obtain ⟨sname', chain', hla, hstCache, hstSname, hstNow, hstChain, hstStep, hstLQ, hstSbelt, -⟩ :=
    resolve_paused_inv query qu qm.qname sbelt now0 cache state hqu hqm hcanon hpaused
  cases h5 : (qu.qtype == (5 : BitVec 16)) with
  | true =>
    obtain ⟨hneg, hemp⟩ := localAnswer_miss_reads cache qu.qtype qu.qclass now0 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) sname' chain' hla
    have hneg' : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
        cache qu.qname qu.qtype qu.qclass now0 = none := hneg
    have hemp' : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now0).isEmpty
        = true := hemp
    have hla5 : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now0 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .miss qu.qname #[] := by
      unfold Resolver.localAnswer
      simp only [hneg']
      rw [if_pos hemp', if_pos h5]
    have hinj := hla5.symm.trans hla
    injection hinj with h1 h2
    obtain ⟨slist, v, coutM, hHV, hSub, hrc, hans, hCR, hWM, hwf1, hwf2, hwf3, hwf4, hwf5,
        hwf6, hwf7, hwf8⟩ :=
      resolveWithIO_noPeel_paused_sound net ns ra ednsBuf rttOf sbelt budget hnetWF hGlSbelt
        n query qu qm t depth fuel' state cache w w' now0 resp cout
        hqu hqm hcanon ht hqany hqq hqc hqvalid hqlen hrd hqstar hqin
        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hclock hw hwTcp hpaused
        (by rw [hstSname, ← h1]) (by rw [hstChain, ← h2]) hrun
    refine ⟨slist, v, αCache cache, coutM, CacheRefines.refl _, hHV, hSub, hrc, ?_,
      hCR, hWM, hwf1, hwf2, hwf3, hwf4, hwf5, hwf6, hwf7, hwf8⟩
    rw [hans, hstChain, ← h2]
    rfl
  | false =>
    have htne : t ≠ RRType.cname := αType_ne_cname_of_ne5 ht h5
    have hpeel := localAnswer_chase_peel net ns ra ednsBuf rttOf cache (αCache cache)
      qu.qtype qu.qclass now0 qm t [] qu.qname
      ht hqq htne hqc (MatchMaxEquiv.refl _) hCacheWf hCnCanon hwfrr hNegWf
      8 qu.qname qm.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      [] (.miss sname' chain') hla hqm hcanon hvN hqlen rfl
      (initVisited_models qu qm.qname hqm hcanon hvN)
    obtain ⟨links, nF, nseenF, hchainDec, hαF, hcanF, hvalF, hlenF, hvisF, hhitF, hnhitF,
        hlinksC, htrans⟩ := hpeel
    have hSMinit := StateModels_initFromQuery (net := net) (ns := ns) (ra := ra)
      (ednsBuf := ednsBuf) (rttOf := rttOf) (q := query) (sbelt := sbelt) (now := now0)
      (initCache := cache) (qu := qu) (qm := qm) (w := w) hqu hqm hw
    have hSM : StateModels net ns ra ednsBuf rttOf (αTime now0) { qm with qname := nF }
        state (αCache cache) w :=
      StateModels_cacheCname_preserve hSMinit
        (by rw [hstCache, initFromQuery_cache])
        (by rw [hstSname]; exact hαF)
        (by rw [hstNow, initFromQuery_now])
    have hCCM : CnameChainModels state { qm with qname := nF } nseenF := by
      unfold CnameChainModels
      rw [hstLQ, hstChain]
      simp only [Option.bind_some, hqu, Option.elim]
      exact hvisF
    have hαq : αQType qu.qtype = some qm.qtype := by
      have h255 : ¬ qu.qtype.toNat = 255 := hqany
      unfold αQType; rw [if_neg h255, ht]; simp [hqq]
    obtain ⟨slist, v, coutM, hHV, hSub, hrc, hans, hCR, hWM, hwf1, hwf2, hwf3, hwf4, hwf5,
        hwf6, hwf7, hwf8⟩ :=
      resolveWithIO_paused_sound' net ns ra ednsBuf rttOf sbelt budget hnetWF hGlSbelt
        n query qu qm.qname { qm with qname := nF } depth fuel' state cache (αCache cache)
        w w' now0 (αTime now0) nseenF [] state.resources.slist.matchCount resp cout
        hqu hqm hcanon hpaused
        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hclock
        hSM hwTcp hNegWf hhitF hnhitF
        (by intro b hb; simp at hb)
        rfl
        (paused_GluelessProv query qu qm.qname sbelt now0 cache state
          hqu hqm hcanon hNsCanon hGlSbelt hpaused)
        ⟨hαq, hqc⟩
        hrd hqstar hqin
        (by rw [hstSname]; exact hcanF)
        hlenF (αName_valid hαF)
        hCCM
        hrun
    have hansL : (αResp resp).answer = links ++ v.answer := by
      rw [hans, hstChain, hchainDec]
      rfl
    obtain ⟨cOut, hcOutR, -, hHV0⟩ := htrans (αCache cache) (CacheRefines.refl _)
      v slist coutM hHV (αResp resp) hrc hansL
    exact ⟨slist, αResp resp, cOut, coutM, hcOutR, hHV0, hSub, rfl, rfl,
      hCR, hWM, hwf1, hwf2, hwf3, hwf4, hwf5, hwf6, hwf7, hwf8⟩

theorem resolveWithIO_negHit_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (cache : DnsCache) (w w' : World) (now0 : UInt32) (fuel' depth : Nat)
    (rc : VeriDNS.Spec.Rcode) (slist : List String) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t) (hqq : qm.qtype = QType.rr t)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hnegwf : CacheNegWf cache qu.qclass)
    (hlk : cache.lookupNegative qu.qname qu.qtype qu.qclass now0 = some rc)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ v, HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] (αCache cache) slist qm v (αCache cache)
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer := by
  have hlk' : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
      cache qu.qname qu.qtype qu.qclass now0 = some rc := hlk
  have hneg : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now0 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now0) #[] := by
    unfold Resolver.localAnswer
    rw [hlk']
  have hred := run_resolveWithIO_negHit w n query sbelt cache now0 fuel' depth budget qu rc
    (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection (C := DnsCache)
      (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now0) #[] hqu hneg
  rw [hred] at hrun
  have hpair := Option.some.inj hrun
  rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
  have hrespEq := Except.ok.inj hpair.1.1
  obtain ⟨hnegT, hrcEq⟩ := lookupNegative_negHit_negResponse cache qu.qname qu.qtype qu.qclass now0
    qm t rc hlk hqm ht hqq hcanon hvN hnegwf
  refine ⟨{ aa := false, rcode := αRCode rc, answer := [], authority := [], additional := [],
            ra := false, tc := false }, ?_, ?_, ?_⟩
  · exact negHit_hasVerdictAt net ns ra ednsBuf rttOf (αCache cache) slist qm hnegT _
      ⟨by
        show αRCode rc = (if (αCache cache).negHitNx (αTime now0) qm
          then RCode.nameError else RCode.noError)
        exact hrcEq, List.Perm.refl _⟩
  · rw [← hrespEq, finalizeAnswer_abstracts_rcode]; rfl
  · rw [← hrespEq, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]; rfl

theorem resolveWithIO_answerHit_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (cache : DnsCache) (w w' : World) (now0 : UInt32) (fuel' depth : Nat)
    (slist : List String) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t) (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hCacheWf : CacheWf cache now0)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hlkNeg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative (C := DnsCache)
        cache qu.qname qu.qtype qu.qclass now0 = none)
    (hne : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now0).isEmpty = false)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ v, HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] (αCache cache) slist qm v (αCache cache)
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer := by
  have hhit : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now0 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .answerHit qu.qname #[] (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0) := by
    unfold Resolver.localAnswer
    simp only [hlkNeg]
    rw [if_neg (show ¬ (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
      (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now0).isEmpty = true
      from by rw [hne]; simp)]
    rfl
  have hred := run_resolveWithIO_answerHit w n query sbelt cache now0 fuel' depth budget qu
    qu.qname #[] (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0) hqu hhit
  rw [hred] at hrun
  have hpair := Option.some.inj hrun
  rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
  have hrespEq := Except.ok.inj hpair.1.1
  obtain ⟨heqHit, hlenHit⟩ := lookupAnswerable_hit_bridge cache qu.qname qu.qtype qu.qclass now0
    qm t hqm ht hqq hqc hcanon hvN hCacheWf hne
  have hwfrrs : ∀ rr ∈ (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0),
      VeriDNS.Proof.NameTree.WfRR rr := by
    intro rr hrr
    obtain ⟨e, he, -, hrre⟩ := lookupAnswerable_mem_entry (Array.mem_def.mp hrr)
    rw [hrre]
    exact VeriDNS.Proof.NameTree.wfRR_set_ttl (hwfrr e he) _
  refine ⟨{ aa := false, rcode := RCode.noError,
            answer := (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0).toList.filterMap αRR,
            authority := [], additional := [], ra := false, tc := false }, ?_, ?_, ?_⟩
  · exact cacheHit_hasVerdictAt net ns ra ednsBuf rttOf (αCache cache) slist qm _ rfl hlenHit _
      ⟨rfl, by show List.Perm _ ((αCache cache).hit (αTime now0) qm); rw [heqHit]⟩
  · rw [← hrespEq, finalizeAnswer_abstracts_rcode]; rfl
  · rw [← hrespEq, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain,
      show (Resolver.cacheResponse query (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0)).answer
        = (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0).map
            (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)) from rfl,
      αSection_map_rrBytes_wf _ hwfrrs]
    show αSection (#[] : Array ByteArray)
        ++ (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0).toList.filterMap αRR
      = (cache.lookupAnswerable qu.qname qu.qtype qu.qclass now0).toList.filterMap αRR
    rfl

theorem resolveWithIO_negative_full_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (cache : DnsCache) (w w' : World) (now0 : UInt32) (fuel' depth : Nat)
    (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
    (chainN : Array ByteArray)
    (slist : List String) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t) (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hqlen : qm.qname.length ≤ 127)
    (hCacheWf : CacheWf cache now0) (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now0 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .negative rc soaAuth chainN)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ v, HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] (αCache cache) slist qm v (αCache cache)
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer := by
  cases h5 : (qu.qtype == (5 : BitVec 16)) with
  | true =>
    rcases localAnswer_qt5_inv cache qu.qtype qu.qclass now0 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        (.negative rc soaAuth chainN) h5 hla with
      ⟨rc', hn, heq⟩ | ⟨-, -, heq⟩ | heq
    · injection heq with h1 h2 h3
      have hlk : cache.lookupNegative qu.qname qu.qtype qu.qclass now0 = some rc := by
        rw [h1]; exact hn
      exact resolveWithIO_negHit_sound net ns ra ednsBuf rttOf sbelt budget
        n query qu qm t cache w w' now0 fuel' depth rc slist resp cout
        hqu hqm hcanon ht hqq hvN hNegWf hlk hrun
    · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  | false =>
    have htne : t ≠ RRType.cname := αType_ne_cname_of_ne5 ht h5
    have hpeel := localAnswer_chase_peel net ns ra ednsBuf rttOf cache (αCache cache)
      qu.qtype qu.qclass now0 qm t [] qu.qname
      ht hqq htne hqc (MatchMaxEquiv.refl _) hCacheWf hCnCanon hwfrr hNegWf
      8 qu.qname qm.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      [] (.negative rc soaAuth chainN) hla hqm hcanon hvN hqlen rfl
      (initVisited_models qu qm.qname hqm hcanon hvN)
    obtain ⟨links, hchainDec, harm⟩ := hpeel
    have hred := run_resolveWithIO_negHit w n query sbelt cache now0 fuel' depth budget qu rc
      soaAuth chainN hqu hla
    rw [hred] at hrun
    have hpair := Option.some.inj hrun
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
    have hrespEq := Except.ok.inj hpair.1.1
    have hrcE : (αResp resp).rcode = αRCode rc := by
      rw [← hrespEq, finalizeAnswer_abstracts_rcode]
      rfl
    have hansE : (αResp resp).answer = links := by
      rw [← hrespEq, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
      show αSection chainN ++ αSection (#[] : Array ByteArray) = links
      rw [show αSection (#[] : Array ByteArray) = ([] : List VeriDNS.Spec.Net.RR) from rfl,
        List.append_nil, hchainDec]
      rfl
    exact ⟨αResp resp, harm (αResp resp) hrcE hansE slist, rfl, rfl⟩

theorem resolveWithIO_answerHit_full_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (cache : DnsCache) (w w' : World) (now0 : UInt32) (fuel' depth : Nat)
    (snameH : ByteArray) (chainH : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (slist : List String) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t) (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hvN : ∀ x ∈ qm.qname, x.size ≤ 63)
    (hqlen : qm.qname.length ≤ 127)
    (hCacheWf : CacheWf cache now0) (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now0 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit snameH chainH rrs)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ v, HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] (αCache cache) slist qm v (αCache cache)
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer := by
  cases h5 : (qu.qtype == (5 : BitVec 16)) with
  | true =>
    rcases localAnswer_qt5_inv cache qu.qtype qu.qclass now0 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        (.answerHit snameH chainH rrs) h5 hla with
      ⟨rc', hn, heq⟩ | ⟨hn, hne, heq⟩ | heq
    · exact absurd heq (by simp)
    · exact resolveWithIO_answerHit_sound net ns ra ednsBuf rttOf sbelt budget
        n query qu qm t cache w w' now0 fuel' depth slist resp cout
        hqu hqm hcanon ht hqq hqc hvN hCacheWf hwfrr hn hne hrun
    · exact absurd heq (by simp)
  | false =>
    have htne : t ≠ RRType.cname := αType_ne_cname_of_ne5 ht h5
    obtain ⟨hnegH, hansH, hneH⟩ := localAnswer_answerHit_inv cache qu.qtype qu.qclass now0 8
      qu.qname #[] (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      snameH chainH rrs hla
    have hwfrrs : ∀ rr ∈ rrs, VeriDNS.Proof.NameTree.WfRR rr := by
      intro rr hrr
      rw [← hansH] at hrr
      obtain ⟨e, he, -, hrre⟩ := lookupAnswerable_mem_entry (Array.mem_def.mp hrr)
      rw [hrre]
      exact VeriDNS.Proof.NameTree.wfRR_set_ttl (hwfrr e he) _
    have hpeel := localAnswer_chase_peel net ns ra ednsBuf rttOf cache (αCache cache)
      qu.qtype qu.qclass now0 qm t [] qu.qname
      ht hqq htne hqc (MatchMaxEquiv.refl _) hCacheWf hCnCanon hwfrr hNegWf
      8 qu.qname qm.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      [] (.answerHit snameH chainH rrs) hla hqm hcanon hvN hqlen rfl
      (initVisited_models qu qm.qname hqm hcanon hvN)
    obtain ⟨links, hchainDec, harm⟩ := hpeel
    have hred := run_resolveWithIO_answerHit w n query sbelt cache now0 fuel' depth budget qu
      snameH chainH rrs hqu hla
    rw [hred] at hrun
    have hpair := Option.some.inj hrun
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
    have hrespEq := Except.ok.inj hpair.1.1
    have hrcE : (αResp resp).rcode = RCode.noError := by
      rw [← hrespEq, finalizeAnswer_abstracts_rcode]
      rfl
    have hansE : (αResp resp).answer = links ++ rrs.toList.filterMap αRR := by
      rw [← hrespEq, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain,
        show (Resolver.cacheResponse query rrs).answer
          = rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)) from rfl,
        αSection_map_rrBytes_wf _ hwfrrs]
      show αSection chainH ++ rrs.toList.filterMap αRR = links ++ rrs.toList.filterMap αRR
      rw [hchainDec]
      rfl
    exact ⟨αResp resp, harm (αResp resp) hrcE hansE slist, rfl, rfl⟩

theorem resolve_pauses_of_miss
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (sname' : ByteArray) (chain' : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hα : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now0 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .miss sname' chain') :
    ∃ st, @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ query sbelt 64 now0 cache = .ok (.paused st) := by
  obtain ⟨stP, hloopP, -, -, -, -, -, -, -, -⟩ :=
    loop_checkAnswer_miss_struct
      (Resolver.initFromQuery (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
        (RR := VeriDNS.Spec.ResourceRecord) query sbelt now0 cache)
      query qu sname' chain'
      rfl rfl hqu
      (by rw [initFromQuery_sname query sbelt now0 cache qu hqu]; exact hla)
      (by
        intro hsEq
        rw [initFromQuery_sname query sbelt now0 cache qu hqu] at hsEq
        rcases localAnswer_miss_ident_or_fresh cache qu.qtype qu.qclass now0 8
            qu.qname #[] (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
            sname' chain' hla with ⟨-, h2⟩ | hfr
        · exact h2
        · exfalso
          have hmem : qu.qname ∈ (Resolver.cnameChaseVisited
              (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]).toList := by
            simp [Resolver.cnameChaseVisited]
          have hfalse := hfr qu.qname hmem
          rw [show sname' = qu.qname from hsEq] at hfalse
          rw [nameEqCI_of_αName_canonical (VeriDNS.Spec.Net.nameEq_refl qn) hcanon hcanon
            (fun x hx => (αName_valid hα x hx).2) (fun x hx => (αName_valid hα x hx).2)] at hfalse
          exact absurd hfalse (by simp))
      rfl 61
  refine ⟨stP, ?_⟩
  unfold Resolver.resolve
  exact hloopP

theorem resolveWithIO_done_answerWriteWf
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (sbelt : DnsSList)
    (cache : DnsCache) (now0 : UInt32) (fuel' depth : Nat) (budget : UInt32)
    (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hwf : CacheWf cache now0) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hdone : (∃ rc soaAuth chain,
        Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
            cache qu.qtype qu.qclass now0 8 qu.qname #[]
            (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
          = .negative rc soaAuth chain)
      ∨ (∃ sname chain rrs,
        Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
            cache qu.qtype qu.qclass now0 8 qu.qname #[]
            (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
          = .answerHit sname chain rrs))
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    AnswerWriteWf resp.answer now0 := by
  rcases hdone with ⟨rc, soaAuth, chain, hla⟩ | ⟨snameH, chain, rrs, hla⟩
  · rw [run_resolveWithIO_negHit w n query sbelt cache now0 fuel' depth budget qu rc
      soaAuth chain hqu hla] at hrun
    have hpair := Option.some.inj hrun
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
    obtain rfl := Except.ok.inj hpair.1.1
    apply answerWriteWf_finalize
    · exact answerWriteWf_of_chain_provenance hwf hns hcnc hwfrr
        (localAnswer_chain_provenance 8 qu.qname #[] _ chain (by rw [hla]; rfl)
          (by intro raw h; simp at h))
    · exact answerWriteWf_empty now0
  · rw [run_resolveWithIO_answerHit w n query sbelt cache now0 fuel' depth budget qu
      snameH chain rrs hqu hla] at hrun
    have hpair := Option.some.inj hrun
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
    obtain rfl := Except.ok.inj hpair.1.1
    apply answerWriteWf_finalize
    · exact answerWriteWf_of_chain_provenance hwf hns hcnc hwfrr
        (localAnswer_chain_provenance 8 qu.qname #[] _ chain (by rw [hla]; rfl)
          (by intro raw h; simp at h))
    · obtain ⟨-, hrrs, -⟩ := localAnswer_answerHit_inv cache qu.qtype qu.qclass now0
        8 qu.qname #[] _ snameH chain rrs hla
      have hrrs' : rrs = cache.lookupAnswerable snameH qu.qtype qu.qclass now0 := by
        rw [← hrrs]; rfl
      show AnswerWriteWf (rrs.map
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))) now0
      rw [hrrs']
      exact answerWriteWf_lookup_map hwf hns hcnc hwfrr

theorem resolveWithIO_verdict_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32) (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (depth fuel' : Nat)
    (cache : DnsCache) (w w' : World) (now0 : UInt32)
    (resp : VeriDNS.Spec.Format) (cout : DnsCache)
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
    (hCacheWf : CacheWf cache now0) (hNsCanon : CacheNsCanon cache) (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache) (hCap : cache.records.size ≤ DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hclock : now0.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime now0) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime now0) w)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    ∃ slist v cOut coutM,
      CacheRefines cOut (αCache cache)
      ∧ HasVerdictAt net ns ra ednsBuf rttOf (αTime now0) [] [] cOut slist qm v coutM
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer
      ∧ CacheRefines (αCache cout) coutM
      ∧ WorldModels net ns ra ednsBuf (αTime now0) w'
      ∧ CacheWf cout now0
      ∧ CacheNsCanon cout
      ∧ CacheCnameCanon cout
      ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
      ∧ CacheNegWf cout qu.qclass
      ∧ CacheNsDistinct cout
      ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
      ∧ cout.records.size ≤ DnsCache.capacity
      ∧ AnswerWriteWf resp.answer now0 := by
  have hvN : ∀ x ∈ qm.qname, x.size ≤ 63 := fun x hx => (hqvalid x hx).2
  cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now0 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) with
  | negative rc soaAuth chainN =>
    obtain ⟨v, hHV, hrc, hans⟩ := resolveWithIO_negative_full_sound net ns ra ednsBuf rttOf
      sbelt budget n query qu qm t cache w w' now0 fuel' depth rc soaAuth chainN
      [] resp cout
      hqu hqm hcanon ht hqq hqc hvN hqlen hCacheWf hCnCanon hwfrr hNegWf hla hrun
    have hAWr : AnswerWriteWf resp.answer now0 :=
      resolveWithIO_done_answerWriteWf n query qu sbelt cache now0 fuel' depth budget w w'
        resp cout hqu hCacheWf hNsCanon hCnCanon hwfrr (Or.inl ⟨rc, soaAuth, chainN, hla⟩) hrun
    have hred := run_resolveWithIO_negHit w n query sbelt cache now0 fuel' depth budget qu rc
      soaAuth chainN hqu hla
    rw [hred] at hrun
    have hpair := Option.some.inj hrun
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
    obtain ⟨⟨-, hcout⟩, hworld⟩ := hpair
    exact ⟨[], v, αCache cache, αCache cache, CacheRefines.refl _, hHV, hrc, hans,
      (by rw [← hcout]; exact CacheRefines.refl _),
      (by rw [← hworld]; exact hw),
      (by rw [← hcout]; exact hCacheWf),
      (by rw [← hcout]; exact hNsCanon),
      (by rw [← hcout]; exact hCnCanon),
      (by rw [← hcout]; exact hwfrr),
      (by rw [← hcout]; exact hNegWf),
      (by rw [← hcout]; exact hNsDistinct),
      (by rw [← hcout]; exact hOE),
      (by rw [← hcout]; exact hCap), hAWr⟩
  | answerHit snameH chainH rrs =>
    obtain ⟨v, hHV, hrc, hans⟩ := resolveWithIO_answerHit_full_sound net ns ra ednsBuf rttOf
      sbelt budget n query qu qm t cache w w' now0 fuel' depth snameH chainH rrs
      [] resp cout
      hqu hqm hcanon ht hqq hqc hvN hqlen hCacheWf hCnCanon hwfrr hNegWf hla hrun
    have hAWr : AnswerWriteWf resp.answer now0 :=
      resolveWithIO_done_answerWriteWf n query qu sbelt cache now0 fuel' depth budget w w'
        resp cout hqu hCacheWf hNsCanon hCnCanon hwfrr (Or.inr ⟨snameH, chainH, rrs, hla⟩) hrun
    have hred := run_resolveWithIO_answerHit w n query sbelt cache now0 fuel' depth budget qu
      snameH chainH rrs hqu hla
    rw [hred] at hrun
    have hpair := Option.some.inj hrun
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpair
    obtain ⟨⟨-, hcout⟩, hworld⟩ := hpair
    exact ⟨[], v, αCache cache, αCache cache, CacheRefines.refl _, hHV, hrc, hans,
      (by rw [← hcout]; exact CacheRefines.refl _),
      (by rw [← hworld]; exact hw),
      (by rw [← hcout]; exact hCacheWf),
      (by rw [← hcout]; exact hNsCanon),
      (by rw [← hcout]; exact hCnCanon),
      (by rw [← hcout]; exact hwfrr),
      (by rw [← hcout]; exact hNegWf),
      (by rw [← hcout]; exact hNsDistinct),
      (by rw [← hcout]; exact hOE),
      (by rw [← hcout]; exact hCap), hAWr⟩
  | miss sname' chain' =>
    obtain ⟨state, hpaused⟩ := resolve_pauses_of_miss query qu qm.qname sbelt now0 cache
      sname' chain' hqu hqm hcanon hla
    obtain ⟨-, -, -, -, -, hstNow, -, -, hstLQ, -, -⟩ :=
      resolve_paused_inv query qu qm.qname sbelt now0 cache state hqu hqm hcanon hpaused
    obtain ⟨slist, v, cOut, coutM, hcOutR, hHV, hSub, hrc, hans, hCR, hWM, hwf1, hwf2, hwf3,
        hwf4, hwf5, hwf6, hwf7, hwf8⟩ :=
      resolveWithIO_paused_full_sound net ns ra ednsBuf rttOf sbelt budget hnetWF hGlSbelt
        n query qu qm t depth fuel' state cache w w' now0 resp cout
        hqu hqm hcanon ht hqany hqq hqc hqvalid hqlen hrd hqstar hqin
        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hclock hw hwTcp hpaused hrun
    exact ⟨slist, v, cOut, coutM, hcOutR, hHV, hrc, hans, hCR, hWM,
      (by rw [← hstNow]; exact hwf1),
      hwf2, hwf3, hwf4,
      hwf5 qu ⟨query, hstLQ, hqu⟩,
      hwf6, hwf7, hwf8.1,
      (by rw [← hstNow]; exact hwf8.2)⟩
  | abort =>
    have hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache
        = .error "cname chain too long" := by
      unfold Resolver.resolve
      rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
      simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal, hqu, hla]
    unfold Server.resolveWithIO at hrun
    simp only [hres] at hrun
    rw [run_pure'] at hrun
    exact absurd hrun (by simp)

theorem deliveredResponse_abstracts_rcode (query resp : VeriDNS.Spec.Format) :
    (αResp (Server.deliveredResponse query resp)).rcode = (αResp resp).rcode := by
  rw [(αResp_components _).1, (αResp_components _).1]
  rfl

theorem answerWriteWf_allAbstract {answer : Array ByteArray} {now : UInt32}
    (h : AnswerWriteWf answer now) : VeriDNS.Proof.Refinement.AllAbstract answer := by
  intro b hb rr hpr
  exact Option.isSome_iff_exists.mp (h b (Array.mem_def.mp hb) rr hpr).1

/-- A non-`*` query type abstracts to the `QType.rr` of its `αType` image
    (the serve-boundary form of the `αQType` gate: `hqany` rules out 255). -/
theorem αQType_of_αType_ne255 {qt : BitVec 16} {t : VeriDNS.Spec.RRType}
    (h : αType qt = some t) (h255 : qt.toNat ≠ 255) :
    αQType qt = some (VeriDNS.Spec.Net.QType.rr t) := by
  unfold αQType
  rw [if_neg h255, h]
  rfl

theorem deliveredResponse_answer_exact {query resp : VeriDNS.Spec.Format}
    {qu : VeriDNS.Spec.Question} {mq : VeriDNS.Spec.Net.Name}
    {qtq : VeriDNS.Spec.Net.QType} {now : UInt32}
    (hqu : query.question[0]? = some qu)
    (hq : αName qu.qname = some mq)
    (hqc : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo mq)
    (hqt : αQType qu.qtype = some qtq)
    (hqv : ∀ x ∈ mq, 0 < x.size ∧ x.size ≤ 63)
    (hq255 : qu.qname.size ≤ 255)
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection resp.answer)
    (hAW : AnswerWriteWf resp.answer now) :
    (αResp (Server.deliveredResponse query resp)).answer
      = VeriDNS.Spec.Net.typeScrub qtq
          (VeriDNS.Spec.Net.scrubAnswer mq ((αResp resp).answer)) := by
  have hclient : Server.clientQname query = qu.qname := by
    unfold Server.clientQname
    rw [hqu]
    rfl
  have hclientT : Server.clientQtype query = qu.qtype := by
    unfold Server.clientQtype
    rw [hqu]
    rfl
  have hda : (Server.deliveredResponse query resp).answer
      = VeriDNS.Impl.Resolver.typeScrubB (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQtype query)
          (VeriDNS.Impl.Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord)
            (Server.clientQname query) resp.answer) := rfl
  rw [(αResp_components _).2.1, (αResp_components _).2.1, hda, hclient, hclientT,
    VeriDNS.Proof.Refinement.αSection_typeScrubB_eq hqt,
    VeriDNS.Proof.Refinement.αSection_scrubAnswerB_eq
      hca (answerWriteWf_allAbstract hAW) hq hqc hqv hq255]

instance : LawfulMonad Prog := LawfulMonad.mk'
  (id_map := fun p => by
    induction p with
    | pure a => rfl
    | step c k ih =>
      show Prog.step c (fun r => id <$> k r) = Prog.step c k
      exact congrArg (Prog.step c) (funext fun r => ih r))
  (pure_bind := fun a f => rfl)
  (bind_assoc := fun p f g => Prog.bind_assoc p f g)

theorem serveDatagram_served
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray) (query : VeriDNS.Spec.Format)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hedns : VeriDNS.Impl.Edns.ednsProblem query = none)
    (hnany : Server.isAnyQuery query = false) :
    Server.serveDatagram (M := Prog) (Sock := Unit) clientSock acl sbelt cache queryBytes clientAddr
      = (do
        let nowT ← VeriDNS.Spec.UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)
        let (resolveResult, cache') ← Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache nowT
        let (response, cache'') ← Server.replyForResolution (M := Prog) (Sock := Unit)
          query resolveResult cache' nowT
        let reply := VeriDNS.Impl.Edns.withReplyOpt query response
        let (truncated, _) := Server.truncateUdp (VeriDNS.Impl.Message.encode reply) reply
          (VeriDNS.Impl.Edns.clientCap query)
        VeriDNS.Spec.UdpSocket.sendTo (M := Prog) clientSock truncated clientAddr
        pure (cache''.boundLru (Server.serveTouches query sbelt cache nowT) nowT)) := by
  unfold Server.serveDatagram
  simp [hperm, hdec, hqp, hedns, hnany, -Prog.bind_def, -Prog.pure_def]
  intro h
  exact absurd h (by simpa using hqr)

/-- The QTYPE=ANY serve arm (RFC 8482 §4.2): a served ANY query bypasses
    resolution entirely — `serveDatagram` sends the synthesized minimal HINFO
    response and returns the cache **unchanged** (no resolution, no cache write).
    This is what closes the query-shape ANY gate at the serve boundary. -/
theorem serveDatagram_any
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : DnsSList)
    (cache : DnsCache) (queryBytes clientAddr : ByteArray) (query : VeriDNS.Spec.Format)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hedns : VeriDNS.Impl.Edns.ednsProblem query = none)
    (hany : Server.isAnyQuery query = true) :
    Server.serveDatagram (M := Prog) (Sock := Unit) clientSock acl sbelt cache queryBytes clientAddr
      = (do
        let response := VeriDNS.Impl.Edns.withReplyOpt query (Server.synthAnyResponse query)
        let (truncated, _) := Server.truncateUdp (VeriDNS.Impl.Message.encode response) response
          (VeriDNS.Impl.Edns.clientCap query)
        VeriDNS.Spec.UdpSocket.sendTo (M := Prog) clientSock truncated clientAddr
        pure cache) := by
  unfold Server.serveDatagram
  simp [hperm, hdec, hqp, hedns, hany, -Prog.bind_def, -Prog.pure_def]
  intro h
  exact absurd h (by simpa using hqr)





theorem negativelyCacheable_rcode {resp : VeriDNS.Spec.Format}
    (h : Server.negativelyCacheable resp = true) :
    resp.header.rcode = Rcode.nameError ∨ resp.header.rcode = Rcode.noError := by
  unfold Server.negativelyCacheable at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with h' | h'
  · left
    have h'' := h'.1
    cases hr : resp.header.rcode <;> rw [hr] at h'' <;>
      first | rfl | exact absurd h'' (by decide)
  · right
    have h'' := h'.1
    cases hr : resp.header.rcode <;> rw [hr] at h'' <;>
      first | rfl | exact absurd h'' (by decide)




theorem answerWrite_invariants (query resp : VeriDNS.Spec.Format) (cache' : DnsCache)
    (nowT : UInt32) {qc : BitVec 16}
    (hrw : RespWriteWf query resp nowT)
    (hwf : CacheWf cache' nowT) (hns : CacheNsCanon cache') (hcnc : CacheCnameCanon cache')
    (hwfrr : ∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hnsd : CacheNsDistinct cache') (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey cache')
    (hneg : CacheNegWf cache' qc) :
    CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT) nowT
    ∧ CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT)
    ∧ CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT)
    ∧ (∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT).records,
        VeriDNS.Proof.NameTree.WfRR e.rr)
    ∧ CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT)
    ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Server.clientQname query) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) nowT)
    ∧ CacheNegWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Server.clientQname query) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) nowT) qc := by
  have hval : ∀ raw ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Server.clientQname query) resp.answer).toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
        (αRR rr).isSome = true :=
    fun raw hraw rr hp => (hrw raw hraw rr hp).1
  have hno : ∀ raw ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Server.clientQname query) resp.answer).toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
        (nowT + rr.ttl.toNat.toUInt32).toNat = nowT.toNat + rr.ttl.toNat :=
    fun raw hraw rr hp => (hrw raw hraw rr hp).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply CacheWf_cacheUnlessTruncated _ _ _ _ _ hwf ?_ ?_
    · unfold Resolver.credAnswer
      by_cases ha : (resp.header.aa == 1) = true
      · rw [if_pos ha]; exact Or.inl rfl
      · rw [if_neg ha]; exact Or.inr (Or.inr (Or.inl rfl))
    · intro raw hraw rr hp
      exact parseRaw_entry_canonical _ nowT hp (normRaws_hval hval raw hraw rr hp)
        (normRaws_hno hno raw hraw rr hp)
  · apply CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hns
    intro raw hraw rr hp htype
    exact (hrw raw hraw rr hp).2.2.1 htype
  · apply CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hcnc
    intro raw hraw rr hp htype
    exact (hrw raw hraw rr hp).2.2.2 htype
  · exact wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
  · exact CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hnsd
  · exact VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hoe _ _ _ _
  · exact CacheNegWf_cacheUnlessTruncated _ _ _ _ _ hneg

theorem storeNegativeIfCacheable_run_inv {n : Nat} {resp : VeriDNS.Spec.Format}
    {base : DnsCache} {nowT : UInt32} {w : World} {c : DnsCache} {w' : World}
    (h : Prog.run n (Server.storeNegativeIfCacheable (M := Prog) (Sock := Unit) resp base nowT) w
      = some (c, w')) :
    c = base
    ∨ (Server.negativelyCacheable resp = true
        ∧ ∃ negTtl soaRR qu,
          Server.extractSoaNegative (Server.clientQname resp) resp.authority
            = some (negTtl, soaRR)
          ∧ resp.question[0]? = some qu
          ∧ c = base.storeNegative qu.qname qu.qtype qu.qclass resp.header.rcode
              (some { soaRR with ttl := Server.capNegativeTtl negTtl })
              (nowT + (Server.capNegativeTtl negTtl).toNat.toUInt32) nowT) := by
  unfold Server.storeNegativeIfCacheable at h
  by_cases hneg : Server.negativelyCacheable resp = true
  · rw [if_pos hneg] at h
    split at h
    · rename_i negTtl soaRR qu hext hq
      obtain ⟨m, rfl, h'⟩ := run_log_bind_inv _ _ w h
      simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h'
      exact Or.inr ⟨hneg, negTtl, soaRR, qu, hext, hq, h'.1.symm⟩
    · rename_i hext _
      by_cases hae : (!resp.authority.isEmpty) = true
      · rw [if_pos hae] at h
        obtain ⟨m, rfl, h'⟩ := run_log_bind_inv _ _ w h
        simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h'
        exact Or.inl h'.1.symm
      · rw [if_neg hae] at h
        obtain ⟨m₁, m₂, u, w₂, hle, h1, h2⟩ := run_bind_inv h
        simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h1 h2
        exact Or.inl h2.1.symm
    · simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl h.1.symm
  · rw [if_neg hneg] at h
    simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl h.1.symm

theorem replyForResolution_run_ok_inv {n : Nat} {query resp : VeriDNS.Spec.Format}
    {cache' : DnsCache} {nowT : UInt32} {w : World}
    {response : VeriDNS.Spec.Format} {cache'' : DnsCache} {w' : World}
    (h : Prog.run n (Server.replyForResolution (M := Prog) (Sock := Unit)
        query (.ok resp) cache' nowT) w = some ((response, cache''), w')) :
    response = Server.deliveredResponse query resp
    ∧ (cache'' = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache' resp
          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Server.clientQname query) resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) nowT
      ∨ (Server.negativelyCacheable resp = true
          ∧ ∃ negTtl soaRR qu,
            Server.extractSoaNegative (Server.clientQname resp) resp.authority
              = some (negTtl, soaRR)
            ∧ resp.question[0]? = some qu
            ∧ cache'' = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                cache' resp
                (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Server.clientQname query) resp.answer)
                (Resolver.credAnswer (resp.header.aa == 1)) nowT).storeNegative
                qu.qname qu.qtype qu.qclass resp.header.rcode
                (some { soaRR with ttl := Server.capNegativeTtl negTtl })
                (nowT + (Server.capNegativeTtl negTtl).toNat.toUInt32) nowT)) := by
  unfold Server.replyForResolution at h
  obtain ⟨m₁, m₂, c, w₂, hle, h1, h2⟩ := run_bind_inv h
  simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨hresp, hcache⟩, hw⟩ := h2
  refine ⟨hresp.symm, ?_⟩
  rcases storeNegativeIfCacheable_run_inv h1 with hc | ⟨hnegc, negTtl, soaRR, qu, hext, hq, hc⟩
  · exact Or.inl (hcache ▸ hc ▸ rfl)
  · exact Or.inr ⟨hnegc, negTtl, soaRR, qu, hext, hq, hcache ▸ hc ▸ rfl⟩

theorem replyForResolution_run_err_inv {n : Nat} {query : VeriDNS.Spec.Format} {msg : String}
    {cache' : DnsCache} {nowT : UInt32} {w : World}
    {response : VeriDNS.Spec.Format} {cache'' : DnsCache} {w' : World}
    (h : Prog.run n (Server.replyForResolution (M := Prog) (Sock := Unit)
        query (.error msg) cache' nowT) w = some ((response, cache''), w')) :
    response = Server.finalizeForClient (Server.buildErrorResponse query Rcode.serverFailure)
    ∧ cache'' = cache' := by
  unfold Server.replyForResolution at h
  obtain ⟨m, rfl, h'⟩ := run_log_bind_inv _ _ w h
  rw [run_pure'] at h'
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  exact ⟨h'.1.1.symm, h'.1.2.symm⟩

theorem replyPath_cacheOut_wf {n : Nat} {query resp : VeriDNS.Spec.Format}
    {cache' : DnsCache} {nowT : UInt32} {w : World}
    {response : VeriDNS.Spec.Format} {cache'' : DnsCache} {w' : World}
    (ks : Array RRKey) (tnow : UInt32) (qu : VeriDNS.Spec.Question)
    (hrun : Prog.run n (Server.replyForResolution (M := Prog) (Sock := Unit)
        query (.ok resp) cache' nowT) w = some ((response, cache''), w'))
    (hrw : RespWriteWf query resp nowT)
    (hq0 : resp.question[0]? = some qu)
    (hqcanon : ∃ na, αName qu.qname = some na
        ∧ qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
        ∧ ∀ x ∈ na, x.size ≤ 63)
    (hwf : CacheWf cache' nowT) (hns : CacheNsCanon cache') (hcnc : CacheCnameCanon cache')
    (hwfrr : ∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hnsd : CacheNsDistinct cache') (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey cache')
    (hneg : CacheNegWf cache' qu.qclass) :
    CacheWf (cache''.boundLru ks tnow) nowT
    ∧ CacheNsCanon (cache''.boundLru ks tnow)
    ∧ CacheCnameCanon (cache''.boundLru ks tnow)
    ∧ (∀ e ∈ (cache''.boundLru ks tnow).records, VeriDNS.Proof.NameTree.WfRR e.rr)
    ∧ CacheNegWf (cache''.boundLru ks tnow) qu.qclass
    ∧ CacheNsDistinct (cache''.boundLru ks tnow)
    ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey (cache''.boundLru ks tnow)
    ∧ (cache''.boundLru ks tnow).records.size ≤ DnsCache.capacity := by
  obtain ⟨bwf, bns, bcnc, bwfrr, bnsd, boe, bneg⟩ :=
    answerWrite_invariants query resp cache' nowT hrw hwf hns hcnc hwfrr hnsd hoe hneg
  obtain ⟨-, hcases⟩ := replyForResolution_run_ok_inv hrun
  have hpack : CacheWf cache'' nowT ∧ CacheNsCanon cache'' ∧ CacheCnameCanon cache''
      ∧ (∀ e ∈ cache''.records, VeriDNS.Proof.NameTree.WfRR e.rr)
      ∧ CacheNegWf cache'' qu.qclass ∧ CacheNsDistinct cache''
      ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache'' := by
    rcases hcases with rfl | ⟨hnegc, negTtl, soaRR, qu', hext, hq0', rfl⟩
    · exact ⟨bwf, bns, bcnc, bwfrr, bneg, bnsd, boe⟩
    · obtain rfl : qu' = qu := by
        rw [hq0] at hq0'; exact (Option.some.inj hq0').symm
      exact ⟨bwf, bns, bcnc, bwfrr,
        CacheNegWf_storeNegative _ _ _ _ _ _ bneg (negativelyCacheable_rcode hnegc) hqcanon,
        bnsd, boe⟩
  obtain ⟨pwf, pns, pcnc, pwfrr, pneg, pnsd, poe⟩ := hpack
  exact ⟨CacheWf_boundLru _ ks tnow _ pwf,
    VeriDNS.Proof.Refinement.CacheNsCanon_boundLru _ ks tnow pns,
    VeriDNS.Proof.Refinement.CacheCnameCanon_boundLru _ ks tnow pcnc,
    wfrrAll_boundLru ks tnow pwfrr,
    CacheNegWf_boundLru ks tnow pneg,
    VeriDNS.Proof.Refinement.CacheNsDistinct_boundLru _ ks tnow pnsd,
    VeriDNS.Proof.NameTree.oneExpiry_boundLru ks tnow poe,
    VeriDNS.Proof.Cache.boundLru_bounded _ ks tnow⟩



theorem finalizeAnswer_question
    {s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {q₀ : VeriDNS.Spec.Format} (hlq : s.lastQuery = some q₀) (resp : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s resp).question = q₀.question := by
  unfold Resolver.finalizeAnswer
  rw [hlq]

private def StepPin (q₀ : VeriDNS.Spec.Format) :
    Resolver.StepResult DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
      → Prop
  | .answer resp stF => resp.question = q₀.question ∧ stF.lastQuery = some q₀
  | .goto _ s' => s'.lastQuery = some q₀
  | .needsIO s' => s'.lastQuery = some q₀
  | .error _ => True

private theorem step_question_pin
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q₀ : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q₀) :
    StepPin q₀ (Resolver.step s) := by
  unfold Resolver.step
  cases s.currentStep with
  | checkAnswer =>
    unfold Resolver.stepCheckLocal
    rw [hlq]
    repeat' split
    all_goals trivial
  | findServers =>
    unfold Resolver.stepFindServers
    dsimp only []
    repeat' split
    all_goals trivial
  | sendQueries =>
    unfold Resolver.stepSendQueries
    repeat' split
    all_goals trivial
  | analyzeResponse =>
    unfold Resolver.stepAnalyzeResponse
    try dsimp only []
    repeat' split
    all_goals first
      | trivial
      | exact hlq
      | exact ⟨finalizeAnswer_question hlq _, hlq⟩

private theorem loop_question_pin (q₀ : VeriDNS.Spec.Format) :
    ∀ (fuel : Nat)
      (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
      s.lastQuery = some q₀ →
      ∀ (y : Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
          VeriDNS.Spec.ResourceRecord),
        Resolver.resolve.loop s fuel = .ok y →
        (∀ resp stF, y = .done resp stF → resp.question = q₀.question)
        ∧ (∀ st, y = .paused st → st.lastQuery = some q₀) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hlq y h
    rw [Resolver.resolve.loop] at h
    exact absurd h (by simp)
  | succ n IHf =>
    intro s hlq y h
    rw [Resolver.resolve.loop] at h
    have hpin := step_question_pin s q₀ hlq
    cases hstep : Resolver.step s with
    | answer resp stF =>
      rw [hstep] at h hpin
      obtain rfl : Resolver.ResolveYield.done resp stF = y := by
        injection h
      exact ⟨fun resp' stF' hd => by injection hd with h1 h2; exact h1 ▸ hpin.1,
        fun st hd => absurd hd (by simp)⟩
    | goto ns s' =>
      rw [hstep] at h hpin
      exact IHf { s' with currentStep := ns } (by exact hpin) y h
    | needsIO s' =>
      rw [hstep] at h hpin
      obtain rfl : Resolver.ResolveYield.paused s' = y := by
        injection h
      exact ⟨fun resp' stF' hd => absurd hd (by simp),
        fun st hd => by injection hd with h1; exact h1 ▸ hpin⟩
    | error msg =>
      rw [hstep] at h
      exact absurd h (by simp)

private theorem resume_question
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {q₀ resp : VeriDNS.Spec.Format} {fuel : Nat}
    {y : Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord}
    (hlq : state.lastQuery = some q₀)
    (h : Resolver.resume state resp fuel = .ok y) :
    (∀ r stF, y = .done r stF → r.question = q₀.question)
    ∧ (∀ st, y = .paused st → st.lastQuery = some q₀) :=
  loop_question_pin q₀ fuel { state with lastResponse := some resp } (by exact hlq) y (by exact h)

private theorem afterResume_question
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord}
    {q₀ : VeriDNS.Spec.Format} (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hlq : state.lastQuery = some q₀) :
    (∀ r c, Server.afterResume state entryName resp = .finished (.ok r) c →
        r.question = q₀.question)
    ∧ (∀ st', Server.afterResume state entryName resp = .continue st' →
        st'.lastQuery = some q₀) := by
  have hlq' : (Server.dropIfBizarre state entryName resp).lastQuery = some q₀ := by
    unfold Server.dropIfBizarre
    split <;> exact hlq
  unfold Server.afterResume
  cases hres : Resolver.resume (Server.dropIfBizarre state entryName resp) resp 64 with
  | ok y =>
    have hq := resume_question hlq' hres
    cases y with
    | done finalResp stF =>
      refine ⟨fun r c hfin => ?_, fun st' hc => absurd hc (by simp)⟩
      injection hfin with h1 h2
      injection h1 with h1'
      exact h1' ▸ hq.1 finalResp stF rfl
    | paused state' =>
      refine ⟨fun r c hfin => absurd hfin (by simp), fun st' hc => ?_⟩
      injection hc with h1
      exact h1 ▸ (show (Server.boundStateCache
          (Server.roundTouches (Server.dropIfBizarre state entryName resp) resp)
          state').lastQuery = some q₀ from
        hq.2 state' rfl)
  | error msg =>
    refine ⟨fun r c hfin => ?_, fun st' hc => absurd hc (by simp)⟩
    injection hfin with h1 h2
    exact absurd h1 (by simp)

private theorem gluelessRecheck_question
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {subCache : DnsCache} {hit : VeriDNS.Spec.Format} {q₀ : VeriDNS.Spec.Format}
    (hlq : state.lastQuery = some q₀)
    (hgr : Server.gluelessRecheck state subCache = some hit) :
    hit.question = q₀.question := by
  unfold Server.gluelessRecheck at hgr
  rw [hlq] at hgr
  dsimp only [] at hgr
  cases hqu : q₀.question[0]? with
  | none =>
    rw [hqu] at hgr
    exact absurd hgr (by simp)
  | some qu =>
    rw [hqu] at hgr
    dsimp only [] at hgr
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative subCache state.resources.sname
        qu.qtype qu.qclass state.now with
    | some rc =>
      rw [hneg] at hgr
      exact (Option.some.inj hgr) ▸ finalizeAnswer_question hlq _
    | none =>
      rw [hneg] at hgr
      dsimp only [] at hgr
      split at hgr
      · exact absurd hgr (by simp)
      · exact (Option.some.inj hgr) ▸ finalizeAnswer_question hlq _

theorem ioResumeLoop_ok_question (sbelt : DnsSList) (deadline : UInt32) :
    ∀ (n : Nat) (depth fuel' revealed : Nat)
      (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord)
      (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
      (q₀ : VeriDNS.Spec.Format), state.lastQuery = some q₀ →
      Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth fuel'
          revealed) w = some ((.ok resp, cout), w') →
      resp.question = q₀.question := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro depth fuel' revealed state w w' resp cout q₀ hlq hrun
    obtain _ | f := fuel'
    · rw [run_ioResumeLoop_fuel_zero] at hrun
      exact absurd hrun (by simp)
    · cases n with
      | zero =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_zero] at hrun
        exact absurd hrun (by simp)
      | succ m =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_eq] at hrun
        by_cases hdl : w.clock ≥ deadline
        · simp only [if_pos hdl, run_pure'] at hrun
          exact absurd hrun (by simp)
        · rw [if_neg hdl] at hrun
          simp only [seqPureUnit] at hrun
          cases hbest : state.resources.slist.bestWithAddress with
          | none =>
            rw [hbest] at hrun
            cases hat : state.resources.slist.addressTargets[0]? with
            | none => simp only [hat, run_pure'] at hrun; exact absurd hrun (by simp)
            | some nsName =>
              cases hd : depth with
              | zero =>
                rw [hd] at hrun; simp only [hat, run_pure'] at hrun
                exact absurd hrun (by simp)
              | succ depth' =>
                rw [hd] at hrun
                simp only [hat] at hrun
                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
                    VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _
                    (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache with
                | ok y =>
                  cases y with
                  | done subResp subSt =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog)
                        (Sock := Unit) state.resources.slist nsName (Except.ok subResp))
                        >>= fun slist' =>
                        Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                          { state with resources := { state.resources with slist := slist' } }
                          deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                    exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hrunB
                  | paused st =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.ioResumeLoop (M := Prog) (Sock := Unit)
                        sbelt st deadline depth' f (Server.seedRevealed st))
                        >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
                        (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                          state.resources.slist nsName p.1) >>= fun slist' =>
                        match p.1 with
                        | .ok subResp =>
                          match Server.extractAAddress nsName subResp.answer with
                          | some _ =>
                            (match Server.gluelessRecheck state p.2 with
                            | some hit =>
                              pure (.ok hit,
                                p.2.touchKeys (Server.recheckTouches state) state.now)
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := slist',
                                    cache := p.2.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed)
                          | none =>
                            Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                              { state with resources := { state.resources with
                                  slist := slist' } } deadline depth' f revealed
                        | .error _ =>
                          Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                            { state with resources := { state.resources with
                                slist := slist' } } deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mI, mK, p, w₂, hle, -, hrunK⟩ := run_bind_inv hrun'
                    obtain ⟨subResult, subCache⟩ := p
                    obtain ⟨mA, mB, slist', w₃, hle2, -, hrunB⟩ := run_bind_inv hrunK
                    cases subResult with
                    | ok subResp =>
                      dsimp only [] at hrunB
                      cases hA : Server.extractAAddress nsName subResp.answer with
                      | some addr =>
                        rw [hA] at hrunB
                        cases hgr : Server.gluelessRecheck state subCache with
                        | some hit =>
                          rw [hgr] at hrunB
                          rw [run_pure'] at hrunB
                          obtain rfl : hit = resp := by
                            have := Option.some.inj hrunB
                            rw [Prod.mk.injEq, Prod.mk.injEq] at this
                            exact Except.ok.inj this.1.1
                          exact gluelessRecheck_question hlq hgr
                        | none =>
                          rw [hgr] at hrunB
                          exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hrunB
                      | none =>
                        rw [hA] at hrunB
                        exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hrunB
                    | error e =>
                      dsimp only [] at hrunB
                      exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hrunB
                | error msg =>
                  rw [hres] at hrun
                  have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog)
                      (Sock := Unit) state.resources.slist nsName (Except.error msg))
                      >>= fun slist' =>
                      Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                        { state with resources := { state.resources with slist := slist' } }
                        deadline depth' f revealed) _
                      = some ((Except.ok resp, cout), w') := hrun
                  obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                  exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hrunB
          | some entryIp =>
            obtain ⟨entry, ipAddr⟩ := entryIp
            rw [hbest] at hrun
            cases hbuild : Resolver.buildSubQuery state revealed with
            | none => simp only [hbuild, run_pure'] at hrun; exact absurd hrun (by simp)
            | some subQuery₀ =>
              simp only [hbuild] at hrun
              by_cases hblk : Server.blockedEgress ipAddr = true
              · simp only [hblk, if_true] at hrun
                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨m2, hm2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨m2c, hm2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨m3, hm3, hrun⟩ := run_log_bind_inv _ _ _ hrun
                dsimp only [] at hrun
                exact IH m3 (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
              simp only [Bool.not_eq_true] at hblk
              simp only [hblk, Bool.false_eq_true, if_false] at hrun
              obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
              obtain ⟨m2, hm2, hrun⟩ := run_randomId_bind_inv _ _ hrun
              obtain ⟨m2c, hm2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
              obtain ⟨mC, mD, upstreamResp, w₃, hle2, -, hrun⟩ := run_bind_inv hrun
              cases upstreamResp with
              | none =>
                dsimp only [] at hrun
                exact IH mD (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
              | some resp₀ =>
                dsimp only [] at hrun
                cases hacc : Server.acceptResponse
                    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
                    resp₀ with
                | none =>
                  rw [hacc] at hrun
                  obtain ⟨m3, hm3, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  exact IH m3 (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                | some resp₂ =>
                  rw [hacc] at hrun
                  obtain ⟨m3, hm3, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  by_cases htcT : (resp₂.header.tc == 1) = true
                  case pos =>
                    rw [if_pos htcT] at hrun
                    rcases run_tcpFallbackGuard_inv _ _ _ _ _ hrun with
                      ⟨mF, hmF, hrun⟩ | ⟨mD, _, _, _, tcpRespA, hmD, _, _, _, _, _, hrun⟩
                    · dsimp only [] at hrun
                      obtain ⟨mFl, hmFl, hrun⟩ := run_log_bind_inv _ _ _ hrun
                      exact IH mFl (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                    · dsimp only [] at hrun
                      by_cases hunf : Server.unfollowableDelegationB
                          (state.resources.slist.markQueried entry.name)
                          state.resources.sname tcpRespA = true
                      · rw [if_pos hunf] at hrun
                        obtain ⟨m4, hm4, hrun⟩ := run_log_bind_inv _ _ _ hrun
                        exact IH m4 (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                      · rw [if_neg hunf] at hrun
                        by_cases hfeT : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.formatError
                            && !state.noEdns) = true
                        case pos =>
                          -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                          rw [if_pos hfeT] at hrun
                          obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                          exact IH mf (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                        rw [if_neg hfeT] at hrun
                        by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                            && Server.strictDenialB tcpRespA) = true
                        · -- 051/064: minimised-probe NXDOMAIN now falls back (full-qname re-probe),
                          -- an IH recursion like probe-consume.
                          rw [if_pos hstT] at hrun
                          obtain ⟨ms', hms', hrun⟩ := run_log_bind_inv _ _ _ hrun
                          exact IH ms' (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                        rw [if_neg hstT] at hrun
                        by_cases hpg : (Resolver.probeRoundB state.resources.sname revealed
                            && !Server.probePassableB tcpRespA) = true
                        · rw [if_pos hpg] at hrun
                          obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                          exact IH mp (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                        rw [if_neg hpg] at hrun
                        cases haft : Server.afterResume
                            { state with resources := { state.resources with
                                slist := state.resources.slist.markQueried entry.name } }
                            entry.name tcpRespA with
                        | finished result cache₂ =>
                          rw [haft] at hrun
                          simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
                          exact (afterResume_question (state := { state with resources :=
                              { state.resources with
                                slist := state.resources.slist.markQueried entry.name } })
                              entry.name tcpRespA (by exact hlq)).1 resp cache₂
                            (by rw [hrun.1.1] at haft; exact haft)
                        | «continue» state'' =>
                          rw [haft] at hrun
                          dsimp only [] at hrun
                          exact IH mD (by omega) depth f _ _ _ _ _ _ _
                            ((afterResume_question entry.name tcpRespA (by exact hlq)).2 state'' haft)
                            hrun
                  rw [if_neg htcT, run_bind_pureSome] at hrun
                  dsimp only [] at hrun
                  by_cases hunf : Server.unfollowableDelegationB
                      (state.resources.slist.markQueried entry.name)
                      state.resources.sname resp₂ = true
                  · rw [if_pos hunf] at hrun
                    obtain ⟨m4, hm4, hrun⟩ := run_log_bind_inv _ _ _ hrun
                    exact IH m4 (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                  · rw [if_neg hunf] at hrun
                    by_cases hfeT : (resp₂.header.rcode == VeriDNS.Spec.Rcode.formatError
                        && !state.noEdns) = true
                    case pos =>
                      -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                      rw [if_pos hfeT] at hrun
                      obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                      exact IH mf (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                    rw [if_neg hfeT] at hrun
                    by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                        && Server.strictDenialB resp₂) = true
                    · -- 051/064: minimised-probe NXDOMAIN now falls back (full-qname re-probe),
                      -- an IH recursion like probe-consume.
                      rw [if_pos hstT] at hrun
                      obtain ⟨ms', hms', hrun⟩ := run_log_bind_inv _ _ _ hrun
                      exact IH ms' (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                    rw [if_neg hstT] at hrun
                    by_cases hpg : (Resolver.probeRoundB state.resources.sname revealed
                        && !Server.probePassableB resp₂) = true
                    · rw [if_pos hpg] at hrun
                      obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                      exact IH mp (by omega) depth f _ _ _ _ _ _ _ (by exact hlq) hrun
                    rw [if_neg hpg] at hrun
                    cases haft : Server.afterResume
                        { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } }
                        entry.name resp₂ with
                    | finished result cache₂ =>
                      rw [haft] at hrun
                      simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
                      exact (afterResume_question (state := { state with resources :=
                          { state.resources with
                            slist := state.resources.slist.markQueried entry.name } })
                          entry.name resp₂ (by exact hlq)).1 resp cache₂
                        (by rw [hrun.1.1] at haft; exact haft)
                    | «continue» state'' =>
                      rw [haft] at hrun
                      dsimp only [] at hrun
                      exact IH m3 (by omega) depth f _ _ _ _ _ _ _
                        ((afterResume_question entry.name resp₂ (by exact hlq)).2 state'' haft)
                        hrun

theorem resolveWithIO_ok_question
    (n : Nat) (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache)
    (now0 : UInt32) (fuel' depth : Nat) (budget : UInt32)
    (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    resp.question = query.question := by
  unfold Server.resolveWithIO at hrun
  cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache with
  | ok y =>
    cases y with
    | done resp₀ stF =>
      rw [hres, run_pure'] at hrun
      obtain rfl : resp₀ = resp := by
        have := Option.some.inj hrun
        rw [Prod.mk.injEq, Prod.mk.injEq] at this
        exact Except.ok.inj this.1.1
      exact (loop_question_pin query 64
        (Resolver.initFromQuery (S := DnsSList) (C := DnsCache)
          (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
          query sbelt now0 cache) rfl _ (by exact hres)).1 _ _ rfl
    | paused st =>
      rw [hres] at hrun
      have hlq : st.lastQuery = some query :=
        (loop_question_pin query 64
          (Resolver.initFromQuery (S := DnsSList) (C := DnsCache)
            (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now0 cache) rfl _ (by exact hres)).2 st rfl
      exact ioResumeLoop_ok_question sbelt (now0 + budget) n depth fuel'
        (Server.seedRevealed st) st w w' resp cout query hlq hrun
  | error msg =>
    rw [hres, run_pure'] at hrun
    simp at hrun



section DeliveredSections

open VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message

def SectionsWf (r : VeriDNS.Spec.Format) : Prop :=
  CanonicalSection r.answer ∧ CanonicalSection r.authority ∧ CanonicalSection r.additional
  ∧ r.header.nscount.toNat = r.authority.size
  ∧ r.header.arcount.toNat = r.additional.size

def RespSections (r : VeriDNS.Spec.Format) : Prop :=
  SectionsWf r ∧ r.header.qdcount.toNat = r.question.size

def StateSections
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord) : Prop :=
  CacheRecCanon s.resources.cache ∧ CacheNegSoaCanon s.resources.cache
  ∧ CanonicalSection s.cnameChain
  ∧ (∀ r, s.lastResponse = some r → SectionsWf r)

theorem lookupNegativeSoa_size (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) : (c.lookupNegativeSoa name qt qc now).size ≤ 1 := by
  unfold VeriDNS.Impl.Cache.DnsCache.lookupNegativeSoa
  cases c.findNegative name qt qc now with
  | none => simp
  | some e =>
    unfold VeriDNS.Impl.Cache.NegativeEntry.authority
    cases hsoa : e.soa <;> simp [hsoa]

theorem localAnswer_negative_soa_inv (cache : DnsCache) (qt qc : BitVec 16) (now : UInt32) :
    ∀ (fuel : Nat) (sname0 : ByteArray) (chain0 visited0 : Array ByteArray)
      {rc : VeriDNS.Spec.Rcode} {soaAuth : Array VeriDNS.Spec.ResourceRecord}
      {chain : Array ByteArray},
      Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qt qc now fuel sname0 chain0 visited0
        = .negative rc soaAuth chain →
      ∃ sn, soaAuth = cache.lookupNegativeSoa sn qt qc now := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname0 chain0 visited0 rc soaAuth chain h
    simp only [Resolver.localAnswer] at h
    exact absurd h (by simp)
  | succ n ih =>
    intro sname0 chain0 visited0 rc soaAuth chain h
    unfold Resolver.localAnswer at h
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname0 qt qc now with
    | some rc0 =>
      rw [hneg] at h
      injection h with h1 h2 h3
      exact ⟨sname0, by rw [← h2]; rfl⟩
    | none =>
      rw [hneg] at h
      dsimp only [] at h
      by_cases hie : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname0 qt qc now).isEmpty = true
      · rw [if_pos hie] at h
        by_cases hq5 : (qt == (5 : BitVec 16)) = true
        · rw [if_pos hq5] at h
          exact absurd h (by simp)
        · rw [if_neg hq5] at h
          cases hcrr : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
              (RR := VeriDNS.Spec.ResourceRecord) cache sname0 (5 : BitVec 16) qc now)[0]? with
          | none =>
            rw [hcrr] at h
            exact absurd h (by simp)
          | some crr =>
            rw [hcrr] at h
            dsimp only [] at h
            by_cases hvis : (visited0.any fun v =>
                VeriDNS.Impl.DomainName.nameEqCI v (VeriDNS.Spec.RRParse.rrRdata
                  (RR := VeriDNS.Spec.ResourceRecord) crr)) = true
            · rw [if_pos hvis] at h
              exact absurd h (by simp)
            · rw [if_neg hvis] at h
              exact ih _ _ _ h
      · rw [if_neg hie] at h
        exact absurd h (by simp)

theorem localAnswer_chain_canonical {cache : DnsCache} {qt qc : BitVec 16} {now : UInt32}
    (hrec : CacheRecCanon cache)
    {fuel : Nat} {sname : ByteArray} {chain visited : Array ByteArray}
    {chainOut : Array ByteArray}
    (hchain : CanonicalSection chain)
    (h : chainOf (Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname chain visited) = some chainOut) :
    CanonicalSection chainOut := by
  intro b hb
  rcases localAnswer_chain_links fuel sname chain visited chainOut h b
      (by simpa using hb) with hin | ⟨sn, hin⟩
  · exact hchain b (by simpa using hin)
  · rw [Array.toList_map, List.mem_map] at hin
    obtain ⟨rr, hrr, rfl⟩ := hin
    exact canonicalRR_rrBytes
      (lookupAnswerable_rrWireCanon cache sn (5 : BitVec 16) qc now hrec rr hrr)

theorem sectionsWf_negativeResponse {cache : DnsCache} (sn : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (hneg : CacheNegSoaCanon cache) (q : VeriDNS.Spec.Format)
    (rc : VeriDNS.Spec.Rcode) :
    SectionsWf (Resolver.negativeResponse (RR := VeriDNS.Spec.ResourceRecord) q rc
      (cache.lookupNegativeSoa sn qt qc now)) := by
  refine ⟨canonicalSection_empty, ?_, canonicalSection_empty, ?_, rfl⟩
  · exact canonicalSection_map_rrBytes (lookupNegativeSoa_rrWireCanon cache sn qt qc now hneg)
  · show (BitVec.ofNat 16 (cache.lookupNegativeSoa sn qt qc now).size).toNat
      = ((cache.lookupNegativeSoa sn qt qc now).map _).size
    rw [Array.size_map, BitVec.toNat_ofNat]
    have := lookupNegativeSoa_size cache sn qt qc now
    have h216 : 2 ^ 16 = 65536 := rfl
    omega

theorem sectionsWf_cacheResponse {cache : DnsCache} (sn : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (hrec : CacheRecCanon cache) (q : VeriDNS.Spec.Format)
    {rrs : Array VeriDNS.Spec.ResourceRecord}
    (hrrs : VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sn qt qc now = rrs) :
    SectionsWf (Resolver.cacheResponse (RR := VeriDNS.Spec.ResourceRecord) q rrs) := by
  refine ⟨?_, canonicalSection_empty, canonicalSection_empty, rfl, rfl⟩
  refine canonicalSection_map_rrBytes fun rr hrr => ?_
  have hrr' : rr ∈ (cache.lookupAnswerable sn qt qc now).toList := by
    rw [show cache.lookupAnswerable sn qt qc now
        = VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
            (RR := VeriDNS.Spec.ResourceRecord) cache sn qt qc now from rfl, hrrs]
    exact hrr
  exact lookupAnswerable_rrWireCanon cache sn qt qc now hrec rr hrr'

theorem finalizeAnswer_frame
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (r : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s r).authority = r.authority
    ∧ (Resolver.finalizeAnswer s r).additional = r.additional
    ∧ (Resolver.finalizeAnswer s r).header.nscount = r.header.nscount
    ∧ (Resolver.finalizeAnswer s r).header.arcount = r.header.arcount := by
  unfold Resolver.finalizeAnswer
  cases s.lastQuery <;>
    (unfold Resolver.prependChain; split <;> exact ⟨rfl, rfl, rfl, rfl⟩)

theorem finalizeAnswer_qdcount
    {s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {q₀ : VeriDNS.Spec.Format} (hlq : s.lastQuery = some q₀) (r : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s r).question = q₀.question
    ∧ (Resolver.finalizeAnswer s r).header.qdcount = BitVec.ofNat 16 q₀.question.size := by
  unfold Resolver.finalizeAnswer
  rw [hlq]
  exact ⟨rfl, rfl⟩

theorem respSections_finalizeAnswer
    {s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {q₀ : VeriDNS.Spec.Format}
    (hlq : s.lastQuery = some q₀) (hsz : q₀.question.size < 65536)
    (hchain : CanonicalSection s.cnameChain)
    {r : VeriDNS.Spec.Format} (hr : SectionsWf r) :
    RespSections (Resolver.finalizeAnswer s r) := by
  obtain ⟨hca, hcn, hcd, hns, har⟩ := hr
  obtain ⟨hauth, hadd, hnsc, harc⟩ := finalizeAnswer_frame s r
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [finalizeAnswer_answer, prependChain_answer]
    split
    · exact hca
    · exact canonicalSection_append hchain hca
  · rw [hauth]; exact hcn
  · rw [hadd]; exact hcd
  · rw [hnsc, hauth]; exact hns
  · rw [harc, hadd]; exact har
  · obtain ⟨hq, hqd⟩ := finalizeAnswer_qdcount hlq r
    rw [hqd, hq, BitVec.toNat_ofNat]
    have h216 : 2 ^ 16 = 65536 := rfl
    omega

theorem sectionsWf_capTtls_of_decode {bytes : ByteArray} {r : VeriDNS.Spec.Format}
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok r) :
    SectionsWf (Server.capTtls r) := by
  obtain ⟨hqd, han, hns, har, hq, hca, hcn, hcd⟩ := decode_ok_wire_facts hdec
  obtain ⟨hh, hqq, hasz, hnsz, hdsz⟩ := capTtls_frame r
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalSection_map_capTtlRR hca
  · exact canonicalSection_map_capTtlRR hcn
  · exact canonicalSection_map_capTtlRR hcd
  · rw [hh, hnsz]; exact hns
  · rw [hh, hdsz]; exact har

theorem sectionsWf_capTtls_stripOpt_of_decode {bytes : ByteArray} {r : VeriDNS.Spec.Format}
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok r) :
    SectionsWf (Server.capTtls (Edns.stripOpt r)) := by
  obtain ⟨hqd, han, hns, har, hq, hca, hcn, hcd⟩ := decode_ok_wire_facts hdec
  obtain ⟨hh, hqq, hasz, hnsz, hdsz⟩ := capTtls_frame (Edns.stripOpt r)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalSection_map_capTtlRR hca
  · exact canonicalSection_map_capTtlRR hcn
  · exact canonicalSection_map_capTtlRR
      (fun b hb => hcd b ((Array.mem_filter.mp hb).1))
  · rw [hh, hnsz]; exact hns
  ·
    rw [hh, hdsz]
    have hlt : (r.additional.filter (fun b => !Edns.isOptRR b)).size < 2 ^ 16 := by
      have hle : (r.additional.filter (fun b => !Edns.isOptRR b)).size ≤ r.additional.size :=
        Array.size_filter_le
      have : r.additional.size < 2 ^ 16 := by rw [← har]; exact r.header.arcount.isLt
      omega
    show (BitVec.ofNat 16 (r.additional.filter (fun b => !Edns.isOptRR b)).size).toNat
      = (r.additional.filter (fun b => !Edns.isOptRR b)).size
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem stateSections_write {c : DnsCache} (hrec : CacheRecCanon c) (hneg : CacheNegSoaCanon c)
    (resp : VeriDNS.Spec.Format) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hraws : ∀ b ∈ raws.toList, CanonicalRR b) :
    CacheRecCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now)
    ∧ CacheNegSoaCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now) :=
  ⟨cacheRecCanon_cacheUnlessTruncated c resp raws cred now hrec (normRaws_rrWireCanon hraws),
   cacheNegSoaCanon_congr (cacheUnlessTruncated_negatives c resp raws cred now) hneg⟩

theorem bailiwickRaws_canonical {bw : ByteArray} {sect : Array ByteArray}
    (h : CanonicalSection sect) :
    ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw sect).toList,
      CanonicalRR b :=
  fun b hb => h b (by simpa using bailiwickRaws_toList_sub hb)

theorem ownerRaws_canonical {sname : ByteArray} {sect : Array ByteArray}
    (h : CanonicalSection sect) :
    ∀ b ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sect).toList,
      CanonicalRR b :=
  fun b hb => h b (by simpa using ownerRaws_toList_sub hb)

theorem cnameRaws_canonical {sname : ByteArray} {sect : Array ByteArray}
    (h : CanonicalSection sect) :
    ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) sname sect).toList,
      CanonicalRR b :=
  fun b hb => h b (by simpa using cnameRaws_toList_sub hb)

theorem prependCnameLink_canonical {chain : Array ByteArray} {resp : VeriDNS.Spec.Format}
    (hchain : CanonicalSection chain) (hans : CanonicalSection resp.answer) :
    CanonicalSection
      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) chain resp) := by
  unfold Resolver.prependCnameLink
  cases hq : resp.question[0]? with
  | none => exact hchain
  | some qu =>
    dsimp only []
    cases hcl : Resolver.extractCnameRR (RR := VeriDNS.Spec.ResourceRecord) qu.qname
        resp.answer with
    | none => exact hchain
    | some link =>
      intro b hb
      rcases Array.mem_push.mp hb with h | rfl
      · exact hchain b h
      · exact hans _ (Array.mem_of_find?_eq_some hcl)

private def SectionsPin (q₀ : VeriDNS.Spec.Format) :
    Resolver.StepResult DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
      → Prop
  | .answer resp stF => RespSections resp ∧ StateSections stF
  | .goto _ s' => s'.lastQuery = some q₀ ∧ StateSections s'
  | .needsIO s' => s'.lastQuery = some q₀ ∧ StateSections s'
  | .error _ => True

private theorem checkLocal_sections_pin
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q₀ : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q₀)
    (hsz : q₀.question.size < 65536)
    (hrec : CacheRecCanon s.resources.cache) (hneg : CacheNegSoaCanon s.resources.cache)
    (hchain : CanonicalSection s.cnameChain)
    (hlr : ∀ r, s.lastResponse = some r → SectionsWf r) :
    SectionsPin q₀ (Resolver.stepCheckLocal s) := by
    unfold Resolver.stepCheckLocal
    rw [hlq]
    dsimp only []
    cases hqu : q₀.question[0]? with
    | none =>
      dsimp only []
      exact ⟨hlq, hrec, hneg, hchain, hlr⟩
    | some qu =>
      dsimp only []
      cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          s.resources.cache qu.qtype qu.qclass s.now 8 s.resources.sname s.cnameChain
          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
            s.cnameChain) with
      | negative rc soaAuth chain =>
        dsimp only []
        have hchain' : CanonicalSection chain :=
          localAnswer_chain_canonical hrec hchain (congrArg chainOf hla)
        obtain ⟨sn, hsoa⟩ := localAnswer_negative_soa_inv s.resources.cache qu.qtype qu.qclass
          s.now 8 _ _ _ hla
        refine ⟨respSections_finalizeAnswer (by exact rfl) hsz hchain' ?_,
          hrec, hneg, hchain', hlr⟩
        rw [hsoa]
        exact sectionsWf_negativeResponse sn qu.qtype qu.qclass s.now hneg q₀ rc
      | answerHit sn chain rrs =>
        dsimp only []
        have hchain' : CanonicalSection chain :=
          localAnswer_chain_canonical hrec hchain (congrArg chainOf hla)
        obtain ⟨hlneg, hans, hne⟩ := localAnswer_answerHit_inv s.resources.cache qu.qtype
          qu.qclass s.now 8 _ _ _ _ _ _ hla
        exact ⟨respSections_finalizeAnswer (by exact rfl) hsz hchain'
            (sectionsWf_cacheResponse sn qu.qtype qu.qclass s.now hrec q₀ hans),
          hrec, hneg, hchain', hlr⟩
      | miss sn chain =>
        dsimp only []
        have hchain' : CanonicalSection chain :=
          localAnswer_chain_canonical hrec hchain (congrArg chainOf hla)
        split
        · exact ⟨hlq, hrec, hneg, hchain, hlr⟩
        · exact ⟨rfl, hrec, hneg, hchain', hlr⟩
      | abort => trivial

private theorem findServers_sections_pin
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q₀ : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q₀)
    (hrec : CacheRecCanon s.resources.cache) (hneg : CacheNegSoaCanon s.resources.cache)
    (hchain : CanonicalSection s.cnameChain)
    (hlr : ∀ r, s.lastResponse = some r → SectionsWf r) :
    SectionsPin q₀ (Resolver.stepFindServers s) := by
  unfold Resolver.stepFindServers
  dsimp only []
  repeat' split
  all_goals exact ⟨hlq, hrec, hneg, hchain, hlr⟩

private theorem sendQueries_sections_pin
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q₀ : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q₀)
    (hrec : CacheRecCanon s.resources.cache) (hneg : CacheNegSoaCanon s.resources.cache)
    (hchain : CanonicalSection s.cnameChain)
    (hlr : ∀ r, s.lastResponse = some r → SectionsWf r) :
    SectionsPin q₀ (Resolver.stepSendQueries s) := by
  unfold Resolver.stepSendQueries
  repeat' split
  all_goals exact ⟨hlq, hrec, hneg, hchain, hlr⟩

private theorem analyzeResponse_sections_pin
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q₀ : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q₀)
    (hsz : q₀.question.size < 65536)
    (hrec : CacheRecCanon s.resources.cache) (hneg : CacheNegSoaCanon s.resources.cache)
    (hchain : CanonicalSection s.cnameChain)
    (hlr : ∀ r, s.lastResponse = some r → SectionsWf r) :
    SectionsPin q₀ (Resolver.stepAnalyzeResponse s) := by
    unfold Resolver.stepAnalyzeResponse
    cases hlrs : s.lastResponse with
    | none =>
      dsimp only []
      trivial
    | some resp =>
      have hresp : SectionsWf resp := hlr resp hlrs
      obtain ⟨hca, hcn, hcd, hnsC, harC⟩ := hresp
      dsimp only []
      cases hchase : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp with
      | some canonicalName =>
        dsimp only []
        split
        · exact ⟨respSections_finalizeAnswer (by exact hlq) hsz hchain
            ⟨hca, hcn, hcd, hnsC, harC⟩, hrec, hneg, hchain, hlr⟩
        · split
          · trivial
          · obtain ⟨hrec', hneg'⟩ := stateSections_write hrec hneg resp _ _ _
              (cnameRaws_canonical hca)
            exact ⟨hlq, hrec', hneg', prependCnameLink_canonical hchain hca,
              fun r hr => by simp at hr⟩
      | none =>
        dsimp only []
        split
        · exact ⟨hlq, hrec, hneg, hchain, fun r hr => by simp at hr⟩
        · split
          · split
            · obtain ⟨hrec', hneg'⟩ := stateSections_write hrec hneg resp _ _ _
                (bailiwickRaws_canonical hcn)
              obtain ⟨hrec'', hneg''⟩ := stateSections_write hrec' hneg' resp _ _ _
                (bailiwickRaws_canonical hcd)
              exact ⟨hlq, hrec'', hneg'', hchain, fun r hr => by simp at hr⟩
            · split
              · exact ⟨respSections_finalizeAnswer (by exact hlq) hsz hchain
                  ⟨hca, hcn, hcd, hnsC, harC⟩, hrec, hneg, hchain, hlr⟩
              ·
                exact ⟨hlq, hrec, hneg, hchain, fun r hr => by simp at hr⟩
          · split
            · obtain ⟨hrec', hneg'⟩ := stateSections_write hrec hneg resp _ _ _
                (ownerRaws_canonical hca)
              exact ⟨respSections_finalizeAnswer (by exact hlq) hsz hchain
                  ⟨hca, hcn, hcd, hnsC, harC⟩, hrec', hneg', hchain,
                fun r hr => by
                  obtain rfl : resp = r := by simpa using hr
                  exact ⟨hca, hcn, hcd, hnsC, harC⟩⟩
            · split
              · exact ⟨respSections_finalizeAnswer (by exact hlq) hsz hchain
                  ⟨hca, hcn, hcd, hnsC, harC⟩, hrec, hneg, hchain, hlr⟩
              · split
                · exact ⟨respSections_finalizeAnswer (by exact hlq) hsz hchain
                    ⟨hca, hcn, hcd, hnsC, harC⟩, hrec, hneg, hchain, hlr⟩
                · split
                  · exact ⟨respSections_finalizeAnswer (by exact hlq) hsz hchain
                      ⟨hca, hcn, hcd, hnsC, harC⟩, hrec, hneg, hchain, hlr⟩
                  · -- G (else): foreign / nameError-with-answer / ambiguous empty
                    -- ⇒ retry (goto sendQueries)
                    exact ⟨hlq, hrec, hneg, hchain, fun r hr => by simp at hr⟩

private theorem step_sections_pin
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q₀ : VeriDNS.Spec.Format) (hlq : s.lastQuery = some q₀)
    (hsz : q₀.question.size < 65536) (hss : StateSections s) :
    SectionsPin q₀ (Resolver.step s) := by
  obtain ⟨hrec, hneg, hchain, hlr⟩ := hss
  unfold Resolver.step
  cases s.currentStep
  · exact checkLocal_sections_pin s q₀ hlq hsz hrec hneg hchain hlr
  · exact findServers_sections_pin s q₀ hlq hrec hneg hchain hlr
  · exact sendQueries_sections_pin s q₀ hlq hrec hneg hchain hlr
  · exact analyzeResponse_sections_pin s q₀ hlq hsz hrec hneg hchain hlr

private theorem loop_sections_pin (q₀ : VeriDNS.Spec.Format) (hsz : q₀.question.size < 65536) :
    ∀ (fuel : Nat)
      (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord),
      s.lastQuery = some q₀ → StateSections s →
      ∀ (y : Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
          VeriDNS.Spec.ResourceRecord),
        Resolver.resolve.loop s fuel = .ok y →
        (∀ resp stF, y = .done resp stF → RespSections resp ∧ StateSections stF)
        ∧ (∀ st, y = .paused st → st.lastQuery = some q₀ ∧ StateSections st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hlq hss y h
    rw [Resolver.resolve.loop] at h
    exact absurd h (by simp)
  | succ n IHf =>
    intro s hlq hss y h
    rw [Resolver.resolve.loop] at h
    have hpin := step_sections_pin s q₀ hlq hsz hss
    have hqpin := step_question_pin s q₀ hlq
    cases hstep : Resolver.step s with
    | answer resp stF =>
      rw [hstep] at h hpin
      obtain rfl : Resolver.ResolveYield.done resp stF = y := by
        injection h
      exact ⟨fun resp' stF' hd => by
          injection hd with h1 h2
          exact h1 ▸ h2 ▸ hpin,
        fun st hd => absurd hd (by simp)⟩
    | goto ns s' =>
      rw [hstep] at h hpin hqpin
      exact IHf { s' with currentStep := ns } (by exact hpin.1) (by exact hpin.2) y h
    | needsIO s' =>
      rw [hstep] at h hpin
      obtain rfl : Resolver.ResolveYield.paused s' = y := by
        injection h
      exact ⟨fun resp' stF' hd => absurd hd (by simp),
        fun st hd => by injection hd with h1; exact h1 ▸ hpin⟩
    | error msg =>
      rw [hstep] at h
      exact absurd h (by simp)

private theorem resume_sections
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {q₀ resp : VeriDNS.Spec.Format} {fuel : Nat}
    {y : Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord}
    (hlq : state.lastQuery = some q₀) (hsz : q₀.question.size < 65536)
    (hss : StateSections state) (hresp : SectionsWf resp)
    (h : Resolver.resume state resp fuel = .ok y) :
    (∀ r stF, y = .done r stF → RespSections r ∧ StateSections stF)
    ∧ (∀ st, y = .paused st → st.lastQuery = some q₀ ∧ StateSections st) := by
  obtain ⟨hrec, hneg, hchain, -⟩ := hss
  exact loop_sections_pin q₀ hsz fuel { state with lastResponse := some resp } (by exact hlq)
    ⟨hrec, hneg, hchain, fun r hr => by
      obtain rfl : resp = r := by simpa using hr
      exact hresp⟩ y (by exact h)

theorem cacheNegSoaCanon_touchKeys (c : DnsCache) (ks : Array RRKey) (tnow : UInt32)
    (h : CacheNegSoaCanon c) : CacheNegSoaCanon (c.touchKeys ks tnow) := by
  intro e he rr hrr
  rw [touchKeys_negatives, Array.toList_map, List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  rw [touchNegEntry_soa] at hrr
  exact h e₀ he₀ rr hrr

theorem cacheNegSoaCanon_boundLru (c : DnsCache) (ks : Array RRKey) (tnow : UInt32)
    (h : CacheNegSoaCanon c) : CacheNegSoaCanon (c.boundLru ks tnow) :=
  cacheNegSoaCanon_congr rfl (cacheNegSoaCanon_touchKeys c ks tnow h)
private theorem afterResume_sections
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord}
    {q₀ : VeriDNS.Spec.Format} (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hlq : state.lastQuery = some q₀) (hsz : q₀.question.size < 65536)
    (hss : StateSections state) (hresp : SectionsWf resp) :
    (∀ r c, Server.afterResume state entryName resp = .finished (.ok r) c →
        RespSections r ∧ CacheRecCanon c ∧ CacheNegSoaCanon c)
    ∧ (∀ st', Server.afterResume state entryName resp = .continue st' →
        st'.lastQuery = some q₀ ∧ StateSections st') := by
  have hlq' : (Server.dropIfBizarre state entryName resp).lastQuery = some q₀ := by
    unfold Server.dropIfBizarre
    split <;> exact hlq
  have hss' : StateSections (Server.dropIfBizarre state entryName resp) := by
    obtain ⟨hrec, hneg, hchain, hlr⟩ := hss
    unfold Server.dropIfBizarre
    split <;> exact ⟨hrec, hneg, hchain, hlr⟩
  unfold Server.afterResume
  cases hres : Resolver.resume (Server.dropIfBizarre state entryName resp) resp 64 with
  | ok y =>
    have hq := resume_sections hlq' hsz hss' hresp hres
    cases y with
    | done finalResp stF =>
      refine ⟨fun r c hfin => ?_, fun st' hc => absurd hc (by simp)⟩
      injection hfin with h1 h2
      injection h1 with h1'
      obtain ⟨hrs, hrecF, hnegF, -, -⟩ :
          RespSections finalResp ∧ StateSections stF := hq.1 finalResp stF rfl
      subst h1'
      subst h2
      exact ⟨hrs, VeriDNS.Proof.DeliveredWire.cacheRecCanon_boundLru _ _ _ hrecF,
        cacheNegSoaCanon_boundLru _ _ _ hnegF⟩
    | paused state' =>
      refine ⟨fun r c hfin => absurd hfin (by simp), fun st' hc => ?_⟩
      injection hc with h1
      obtain ⟨hlq'', hrec', hneg', hchain', hlr'⟩ :
          state'.lastQuery = some q₀ ∧ StateSections state' := hq.2 state' rfl
      subst h1
      exact ⟨by exact hlq'', VeriDNS.Proof.DeliveredWire.cacheRecCanon_boundLru _ _ _ hrec',
        cacheNegSoaCanon_boundLru _ _ _ hneg', hchain', hlr'⟩
  | error msg =>
    refine ⟨fun r c hfin => ?_, fun st' hc => absurd hc (by simp)⟩
    injection hfin with h1 h2
    exact absurd h1 (by simp)

private theorem gluelessRecheck_sections
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {subCache : DnsCache} {hit : VeriDNS.Spec.Format} {q₀ : VeriDNS.Spec.Format}
    (hlq : state.lastQuery = some q₀) (hsz : q₀.question.size < 65536)
    (hchain : CanonicalSection state.cnameChain)
    (hrec : CacheRecCanon subCache) (hneg : CacheNegSoaCanon subCache)
    (hgr : Server.gluelessRecheck state subCache = some hit) :
    RespSections hit := by
  unfold Server.gluelessRecheck at hgr
  rw [hlq] at hgr
  dsimp only [] at hgr
  cases hqu : q₀.question[0]? with
  | none =>
    rw [hqu] at hgr
    exact absurd hgr (by simp)
  | some qu =>
    rw [hqu] at hgr
    dsimp only [] at hgr
    cases hnegq : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative subCache
        state.resources.sname qu.qtype qu.qclass state.now with
    | some rc =>
      rw [hnegq] at hgr
      obtain rfl : _ = hit := Option.some.inj hgr
      exact respSections_finalizeAnswer hlq hsz hchain
        (sectionsWf_negativeResponse state.resources.sname qu.qtype qu.qclass state.now
          hneg q₀ rc)
    | none =>
      rw [hnegq] at hgr
      dsimp only [] at hgr
      split at hgr
      · exact absurd hgr (by simp)
      · obtain rfl : _ = hit := Option.some.inj hgr
        exact respSections_finalizeAnswer hlq hsz hchain
          (sectionsWf_cacheResponse state.resources.sname qu.qtype qu.qclass state.now
            hrec q₀ rfl)

private theorem resolve_sections
    {query : VeriDNS.Spec.Format} {sbelt : DnsSList} {now : UInt32} {cache : DnsCache}
    (hsz : query.question.size < 65536)
    (hrec : CacheRecCanon cache) (hneg : CacheNegSoaCanon cache)
    {y : Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord}
    (h : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now cache = .ok y) :
    (∀ resp stF, y = .done resp stF → RespSections resp ∧ StateSections stF)
    ∧ (∀ st, y = .paused st → st.lastQuery = some query ∧ StateSections st) :=
  loop_sections_pin query hsz 64
    (Resolver.initFromQuery (S := DnsSList) (C := DnsCache)
      (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
      query sbelt now cache) rfl
    ⟨hrec, hneg, canonicalSection_empty,
      fun r hr => by simp [Resolver.initFromQuery] at hr⟩
    y (by exact h)

theorem extractSoaNegative_rrWireCanon {qname : ByteArray} {authority : Array ByteArray}
    (hcn : CanonicalSection authority)
    {negTtl : BitVec 32} {soaRR : VeriDNS.Spec.ResourceRecord}
    (hext : Server.extractSoaNegative qname authority = some (negTtl, soaRR)) :
    RRWireCanon soaRR := by
  unfold Server.extractSoaNegative at hext
  obtain ⟨b, hb, hf⟩ := Array.exists_of_findSome?_eq_some hext
  cases hdec : DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | error e =>
    rw [hdec] at hf
    exact absurd hf (by simp)
  | ok pr =>
    obtain ⟨rr, p⟩ := pr
    rw [hdec] at hf
    dsimp only at hf
    split at hf
    · split at hf
      · injection hf with hf
        obtain ⟨h1, h2⟩ := Prod.mk.inj hf
        have hpr : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr := by
          show (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
            | .ok (rr, _) => some rr | .error _ => none) = some rr
          rw [hdec]
        exact h2 ▸ rrWireCanon_set_ttl _ (rrWireCanon_of_parseRaw (hcn b hb) hpr)
      · exact absurd hf (by simp)
    · exact absurd hf (by simp)

theorem cacheNegSoaCanon_storeNegative {c : DnsCache}
    (name : ByteArray) (qt qc : BitVec 16) (rc : VeriDNS.Spec.Rcode)
    (soa : Option VeriDNS.Spec.ResourceRecord) (expiry tnow : UInt32)
    (h : CacheNegSoaCanon c)
    (hnew : ∀ rr, soa = some rr → RRWireCanon rr) :
    CacheNegSoaCanon (c.storeNegative name qt qc rc soa expiry tnow) := by
  intro e he
  simp only [DnsCache.storeNegative] at he
  rcases Array.mem_push.mp (by simpa using he) with hmem | rfl
  · exact h e (by simpa using (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hmem)).1)
  · exact hnew

theorem ioResumeLoop_ok_sections (sbelt : DnsSList) (deadline : UInt32) :
    ∀ (n : Nat) (depth fuel' revealed : Nat)
      (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord)
      (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
      (q₀ : VeriDNS.Spec.Format), state.lastQuery = some q₀ →
      q₀.question.size < 65536 → StateSections state →
      Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth fuel'
          revealed) w = some ((.ok resp, cout), w') →
      RespSections resp ∧ CacheRecCanon cout ∧ CacheNegSoaCanon cout := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro depth fuel' revealed state w w' resp cout q₀ hlq hsz hss hrun
    obtain _ | f := fuel'
    · rw [run_ioResumeLoop_fuel_zero] at hrun
      exact absurd hrun (by simp)
    · cases n with
      | zero =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_zero] at hrun
        exact absurd hrun (by simp)
      | succ m =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_eq] at hrun
        by_cases hdl : w.clock ≥ deadline
        · simp only [if_pos hdl, run_pure'] at hrun
          exact absurd hrun (by simp)
        · rw [if_neg hdl] at hrun
          simp only [seqPureUnit] at hrun
          cases hbest : state.resources.slist.bestWithAddress with
          | none =>
            rw [hbest] at hrun
            cases hat : state.resources.slist.addressTargets[0]? with
            | none => simp only [hat, run_pure'] at hrun; exact absurd hrun (by simp)
            | some nsName =>
              cases hd : depth with
              | zero =>
                rw [hd] at hrun; simp only [hat, run_pure'] at hrun
                exact absurd hrun (by simp)
              | succ depth' =>
                rw [hd] at hrun
                simp only [hat] at hrun
                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
                    VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _
                    (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache with
                | ok y =>
                  cases y with
                  | done subResp subSt =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog)
                        (Sock := Unit) state.resources.slist nsName (Except.ok subResp))
                        >>= fun slist' =>
                        Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                          { state with resources := { state.resources with slist := slist' } }
                          deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                    exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                      (by exact hss) hrunB
                  | paused st =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.ioResumeLoop (M := Prog) (Sock := Unit)
                        sbelt st deadline depth' f (Server.seedRevealed st))
                        >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
                        (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                          state.resources.slist nsName p.1) >>= fun slist' =>
                        match p.1 with
                        | .ok subResp =>
                          match Server.extractAAddress nsName subResp.answer with
                          | some _ =>
                            (match Server.gluelessRecheck state p.2 with
                            | some hit =>
                              pure (.ok hit,
                                p.2.touchKeys (Server.recheckTouches state) state.now)
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := slist',
                                    cache := p.2.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed)
                          | none =>
                            Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                              { state with resources := { state.resources with
                                  slist := slist' } } deadline depth' f revealed
                        | .error _ =>
                          Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                            { state with resources := { state.resources with
                                slist := slist' } } deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mI, mK, p, w₂, hle, hrunSub, hrunK⟩ := run_bind_inv hrun'
                    obtain ⟨subResult, subCache⟩ := p
                    obtain ⟨mA, mB, slist', w₃, hle2, -, hrunB⟩ := run_bind_inv hrunK
                    obtain ⟨hrecS, hnegS, hchainS, hlrS⟩ := hss
                    have hszA : (Server.mkAddressQuery nsName).question.size < 65536 := by
                      show (1 : Nat) < 65536
                      omega
                    have hstPin := (resolve_sections hszA hrecS hnegS hres).2 st rfl
                    cases subResult with
                    | ok subResp =>
                      have hsub := IH mI (by omega) depth' f (Server.seedRevealed st) st _ _
                        subResp subCache _ hstPin.1 hszA hstPin.2 hrunSub
                      dsimp only [] at hrunB
                      cases hA : Server.extractAAddress nsName subResp.answer with
                      | some addr =>
                        rw [hA] at hrunB
                        cases hgr : Server.gluelessRecheck state subCache with
                        | some hit =>
                          rw [hgr] at hrunB
                          rw [run_pure'] at hrunB
                          obtain ⟨⟨hhit, hcoutEq⟩, hwEq⟩ :
                              (Except.ok hit = Except.ok resp
                                ∧ subCache.touchKeys (Server.recheckTouches state) state.now
                                    = cout) ∧ w₃ = w' := by
                            have := Option.some.inj hrunB
                            rw [Prod.mk.injEq, Prod.mk.injEq] at this
                            exact this
                          obtain rfl : hit = resp := Except.ok.inj hhit
                          subst hcoutEq
                          exact ⟨gluelessRecheck_sections hlq hsz hchainS hsub.2.1 hsub.2.2 hgr,
                            cacheRecCanon_touchKeys _ _ _ hsub.2.1,
                            cacheNegSoaCanon_touchKeys _ _ _ hsub.2.2⟩
                        | none =>
                          rw [hgr] at hrunB
                          exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                            (by exact ⟨cacheRecCanon_touchKeys _ _ _ hsub.2.1,
                              cacheNegSoaCanon_touchKeys _ _ _ hsub.2.2, hchainS, hlrS⟩) hrunB
                      | none =>
                        rw [hA] at hrunB
                        exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                          (by exact ⟨hrecS, hnegS, hchainS, hlrS⟩) hrunB
                    | error e =>
                      dsimp only [] at hrunB
                      exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                        (by exact ⟨hrecS, hnegS, hchainS, hlrS⟩) hrunB
                | error msg =>
                  rw [hres] at hrun
                  have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog)
                      (Sock := Unit) state.resources.slist nsName (Except.error msg))
                      >>= fun slist' =>
                      Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                        { state with resources := { state.resources with slist := slist' } }
                        deadline depth' f revealed) _
                      = some ((Except.ok resp, cout), w') := hrun
                  obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                  exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                    (by exact hss) hrunB
          | some entryIp =>
            obtain ⟨entry, ipAddr⟩ := entryIp
            rw [hbest] at hrun
            cases hbuild : Resolver.buildSubQuery state revealed with
            | none => simp only [hbuild, run_pure'] at hrun; exact absurd hrun (by simp)
            | some subQuery₀ =>
              simp only [hbuild] at hrun
              by_cases hblk : Server.blockedEgress ipAddr = true
              · simp only [hblk, if_true] at hrun
                rcases m with _ | _ | _ | _ | m'
                · obtain ⟨_, h1, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h3, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨a1, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨a2, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨a2c, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨a3, h3, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  have ham : a3 = m' := by omega
                  rw [ham] at hrun
                  exact IH m' (by omega) depth f _
                    { state with resources := { state.resources with
                        slist := state.resources.slist.markQueried entry.name } }
                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
              simp only [Bool.not_eq_true] at hblk
              simp only [hblk, Bool.false_eq_true, if_false] at hrun
              rcases m with _ | _ | _ | _ | m'
              · obtain ⟨_, h1, -⟩ := run_log_bind_inv _ _ _ hrun; omega
              · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨_, h2, -⟩ := run_randomId_bind_inv _ _ hrun; omega
              · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨_, h2c, -⟩ := run_randomId_bind_inv _ _ hrun; omega
              · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨_, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨_, h3⟩ := run_forwardQuery_bind_inv _ _ _ _ hrun; omega
              · cases hO : w.oracle (VeriDNS.Impl.Message.encode
                    (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
                    (Server.ipv4ToAddr ipAddr) with
                | none =>
                  rw [run_round_bind_eq_none _ _ _ _ _ hO] at hrun
                  simp only [] at hrun
                  exact IH m' (by omega) depth f _
                    { state with resources := { state.resources with
                        slist := state.resources.slist.markQueried entry.name } }
                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                | some d =>
                  cases ha : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d with
                  | none =>
                    rw [run_round_bind_eq_acceptNone _ _ _ _ _ d hO ha] at hrun
                    simp only [] at hrun
                    exact IH m' (by omega) depth f _
                      { state with resources := { state.resources with
                          slist := state.resources.slist.markQueried entry.name } }
                      _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                  | some bytes =>
                    cases hdec : VeriDNS.Impl.Message.decode bytes with
                    | error errmsg =>
                      rw [run_round_bind_eq_decodeError _ _ _ _ _ d bytes errmsg hO ha hdec]
                        at hrun
                      simp only [] at hrun
                      exact IH m' (by omega) depth f _
                        { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } }
                        _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                    | ok resp₀ =>
                      rw [run_round_bind_eq _ _ _ _ _ d bytes resp₀ hO ha hdec] at hrun
                      cases hsani : Server.sanitizeTtlsCap resp₀ with
                      | none =>
                        simp only [hsani] at hrun
                        exact IH m' (by omega) depth f _
                          { state with resources := { state.resources with
                              slist := state.resources.slist.markQueried entry.name } }
                          _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                      | some respS =>
                        simp only [hsani] at hrun
                        have hwfS : SectionsWf respS := by
                          have hcap : respS = Server.capTtls (Edns.stripOpt resp₀) := by
                            unfold Server.sanitizeTtlsCap at hsani
                            exact (Option.some.inj hsani).symm
                          rw [hcap]
                          exact sectionsWf_capTtls_stripOpt_of_decode hdec
                        cases haccR : Server.acceptResponse
                            (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
                            respS with
                        | none =>
                          simp only [haccR] at hrun
                          obtain ⟨mr, hmr, hrun⟩ := run_log_bind_inv _ _ _ hrun
                          exact IH mr (by omega) depth f _
                            { state with resources := { state.resources with
                                slist := state.resources.slist.markQueried entry.name } }
                            _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                        | some respA =>
                          simp only [haccR] at hrun
                          obtain ⟨ml, hml, hrun⟩ := run_log_bind_inv _ _ _ hrun
                          by_cases htcT : (respA.header.tc == 1) = true
                          case pos =>
                            rw [if_pos htcT] at hrun
                            rcases run_tcpFallbackGuard_inv _ _ _ _ _ hrun with
                              ⟨mF, hmF, hrun⟩ | ⟨mD, _, raw2, tcpResp, tcpRespA, hmD, _, hdec2, hsan2, hacc2, _, hrun⟩
                            · dsimp only [] at hrun
                              obtain ⟨mFl, hmFl, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              exact IH mFl (by omega) depth f _
                                { state with resources := { state.resources with
                                    slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                            · dsimp only [] at hrun
                              have hwfS2 : SectionsWf tcpResp := by
                                have hcap : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                  unfold Server.sanitizeTtlsCap at hsan2
                                  exact (Option.some.inj hsan2).symm
                                rw [hcap]
                                exact sectionsWf_capTtls_stripOpt_of_decode hdec2
                              have hwfA : SectionsWf tcpRespA := by
                                rw [acceptResponse_some_eq hacc2]
                                exact hwfS2
                              by_cases hunf : Server.unfollowableDelegationB
                                  (state.resources.slist.markQueried entry.name)
                                  state.resources.sname tcpRespA = true
                              · simp only [hunf, if_true] at hrun
                                obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH mu (by omega) depth f _
                                  { state with resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name } }
                                  _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                              · rw [if_neg hunf] at hrun
                                by_cases hfeT : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                    && !state.noEdns) = true
                                case pos =>
                                  -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                                  rw [if_pos hfeT] at hrun
                                  obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH mf (by omega) depth f _
                                    { state with
                                          resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name },
                                          noEdns := true }
                                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                rw [if_neg hfeT] at hrun
                                by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                    && Server.strictDenialB tcpRespA) = true
                                · -- 051/064: minimised-probe NXDOMAIN now falls back (full-qname re-probe),
                                  -- an IH recursion like probe-consume.
                                  rw [if_pos hstT] at hrun
                                  obtain ⟨ms', hms', hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH ms' (by omega) depth f _
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                rw [if_neg hstT] at hrun
                                by_cases hpg : (Resolver.probeRoundB state.resources.sname revealed
                                    && !Server.probePassableB tcpRespA) = true
                                · rw [if_pos hpg] at hrun
                                  obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH mp (by omega) depth f _
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                rw [if_neg hpg] at hrun
                                cases haft : Server.afterResume
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    entry.name tcpRespA with
                                | finished result cache₂ =>
                                  rw [haft] at hrun
                                  simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
                                  obtain ⟨hAS, hrecF, hnegF⟩ :=
                                    (afterResume_sections (state := { state with resources :=
                                        { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } })
                                      entry.name tcpRespA (by exact hlq) hsz (by exact hss) hwfA).1
                                    resp cache₂ (by rw [hrun.1.1] at haft; exact haft)
                                  exact ⟨hAS, hrun.1.2 ▸ hrecF, hrun.1.2 ▸ hnegF⟩
                                | «continue» state'' =>
                                  rw [haft] at hrun
                                  dsimp only [] at hrun
                                  have hcs := (afterResume_sections (state := { state with resources :=
                                      { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } })
                                    entry.name tcpRespA (by exact hlq) hsz (by exact hss) hwfA).2
                                    state'' haft
                                  exact IH mD (by omega) depth f _ state'' _ _ _ _ _
                                    hcs.1 hsz hcs.2 hrun
                          rw [if_neg htcT, run_bind_pureSome] at hrun
                          dsimp only [] at hrun
                          have hwfA : SectionsWf respA := by
                            rw [acceptResponse_some_eq haccR]
                            exact hwfS
                          by_cases hunf : Server.unfollowableDelegationB
                              (state.resources.slist.markQueried entry.name)
                              state.resources.sname respA = true
                          · simp only [hunf, if_true] at hrun
                            obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                            exact IH mu (by omega) depth f _
                              { state with resources := { state.resources with
                                  slist := state.resources.slist.markQueried entry.name } }
                              _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                          · rw [if_neg hunf] at hrun
                            by_cases hfeT : (respA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                && !state.noEdns) = true
                            case pos =>
                              -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                              rw [if_pos hfeT] at hrun
                              obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              exact IH mf (by omega) depth f _
                                { state with
                                  resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name },
                                  noEdns := true }
                                _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                            rw [if_neg hfeT] at hrun
                            by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                && Server.strictDenialB respA) = true
                            · -- 051/064: minimised-probe NXDOMAIN now falls back (full-qname re-probe),
                              -- an IH recursion like probe-consume.
                              rw [if_pos hstT] at hrun
                              obtain ⟨ms', hms', hrun⟩ := run_log_bind_inv _ _ _ hrun
                              exact IH ms' (by omega) depth f _
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                            rw [if_neg hstT] at hrun
                            by_cases hpg : (Resolver.probeRoundB state.resources.sname revealed
                                && !Server.probePassableB respA) = true
                            · rw [if_pos hpg] at hrun
                              obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              exact IH mp (by omega) depth f _
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                            rw [if_neg hpg] at hrun
                            cases haft : Server.afterResume
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                entry.name respA with
                            | finished result cache₂ =>
                              rw [haft] at hrun
                              simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
                              obtain ⟨hAS, hrecF, hnegF⟩ :=
                                (afterResume_sections (state := { state with resources :=
                                    { state.resources with
                                      slist := state.resources.slist.markQueried entry.name } })
                                  entry.name respA (by exact hlq) hsz (by exact hss) hwfA).1
                                resp cache₂ (by rw [hrun.1.1] at haft; exact haft)
                              exact ⟨hAS, hrun.1.2 ▸ hrecF, hrun.1.2 ▸ hnegF⟩
                            | «continue» state'' =>
                              rw [haft] at hrun
                              dsimp only [] at hrun
                              have hcs := (afterResume_sections (state := { state with resources :=
                                  { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } })
                                entry.name respA (by exact hlq) hsz (by exact hss) hwfA).2
                                state'' haft
                              exact IH ml (by omega) depth f _ state'' _ _ _ _ _
                                hcs.1 hsz hcs.2 hrun

theorem resolveWithIO_ok_sections
    (n : Nat) (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache)
    (now0 : UInt32) (fuel' depth : Nat) (budget : UInt32)
    (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hsz : query.question.size < 65536)
    (hrec : CacheRecCanon cache) (hneg : CacheNegSoaCanon cache)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.ok resp, cout), w')) :
    RespSections resp ∧ CacheRecCanon cout ∧ CacheNegSoaCanon cout := by
  unfold Server.resolveWithIO at hrun
  cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache with
  | ok y =>
    cases y with
    | done resp₀ stF =>
      rw [hres, run_pure'] at hrun
      obtain ⟨⟨h1, h2⟩, h3⟩ : (Except.ok resp₀ = Except.ok resp ∧ cache = cout) ∧ w = w' := by
        have := Option.some.inj hrun
        rw [Prod.mk.injEq, Prod.mk.injEq] at this
        exact this
      obtain rfl : resp₀ = resp := Except.ok.inj h1
      subst h2
      exact ⟨((resolve_sections hsz hrec hneg hres).1 resp₀ stF rfl).1, hrec, hneg⟩
    | paused st =>
      rw [hres] at hrun
      have hstPin := (resolve_sections hsz hrec hneg hres).2 st rfl
      exact ioResumeLoop_ok_sections sbelt (now0 + budget) n depth fuel'
        (Server.seedRevealed st) st w w' resp cout query hstPin.1 hsz hstPin.2 hrun
  | error msg =>
    rw [hres, run_pure'] at hrun
    simp at hrun

theorem ioResumeLoop_error_sections (sbelt : DnsSList) (deadline : UInt32) :
    ∀ (n : Nat) (depth fuel' revealed : Nat)
      (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord)
      (w w' : World) (msg : String) (cout : DnsCache)
      (q₀ : VeriDNS.Spec.Format), state.lastQuery = some q₀ →
      q₀.question.size < 65536 → StateSections state →
      Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth fuel'
          revealed) w = some ((.error msg, cout), w') →
      CacheRecCanon cout ∧ CacheNegSoaCanon cout := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro depth fuel' revealed state w w' msg cout q₀ hlq hsz hss hrun
    obtain _ | f := fuel'
    · rw [run_ioResumeLoop_fuel_zero] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨⟨-, rfl⟩, -⟩ := hrun
      exact ⟨hss.1, hss.2.1⟩
    · cases n with
      | zero =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_zero] at hrun
        exact absurd hrun (by simp)
      | succ m =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_eq] at hrun
        by_cases hdl : w.clock ≥ deadline
        · simp only [if_pos hdl, run_pure'] at hrun
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨⟨-, rfl⟩, -⟩ := hrun
          exact ⟨hss.1, hss.2.1⟩
        · rw [if_neg hdl] at hrun
          simp only [seqPureUnit] at hrun
          cases hbest : state.resources.slist.bestWithAddress with
          | none =>
            rw [hbest] at hrun
            cases hat : state.resources.slist.addressTargets[0]? with
            | none =>
              simp only [hat, run_pure'] at hrun
              simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨⟨-, rfl⟩, -⟩ := hrun
              exact ⟨hss.1, hss.2.1⟩
            | some nsName =>
              cases hd : depth with
              | zero =>
                rw [hd] at hrun; simp only [hat, run_pure'] at hrun
                simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨⟨-, rfl⟩, -⟩ := hrun
                exact ⟨hss.1, hss.2.1⟩
              | succ depth' =>
                rw [hd] at hrun
                simp only [hat] at hrun
                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
                    VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _
                    (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache with
                | ok y =>
                  cases y with
                  | done subResp subSt =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog)
                        (Sock := Unit) state.resources.slist nsName (Except.ok subResp))
                        >>= fun slist' =>
                        Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                          { state with resources := { state.resources with slist := slist' } }
                          deadline depth' f revealed) _
                        = some ((Except.error msg, cout), w') := hrun
                    obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                    exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                      (by exact hss) hrunB
                  | paused st =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.ioResumeLoop (M := Prog) (Sock := Unit)
                        sbelt st deadline depth' f (Server.seedRevealed st))
                        >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
                        (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                          state.resources.slist nsName p.1) >>= fun slist' =>
                        match p.1 with
                        | .ok subResp =>
                          match Server.extractAAddress nsName subResp.answer with
                          | some _ =>
                            (match Server.gluelessRecheck state p.2 with
                            | some hit =>
                              pure (.ok hit,
                                p.2.touchKeys (Server.recheckTouches state) state.now)
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := slist',
                                    cache := p.2.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed)
                          | none =>
                            Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                              { state with resources := { state.resources with
                                  slist := slist' } } deadline depth' f revealed
                        | .error _ =>
                          Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                            { state with resources := { state.resources with
                                slist := slist' } } deadline depth' f revealed) _
                        = some ((Except.error msg, cout), w') := hrun
                    obtain ⟨mI, mK, p, w₂, hle, hrunSub, hrunK⟩ := run_bind_inv hrun'
                    obtain ⟨subResult, subCache⟩ := p
                    obtain ⟨mA, mB, slist', w₃, hle2, -, hrunB⟩ := run_bind_inv hrunK
                    obtain ⟨hrecS, hnegS, hchainS, hlrS⟩ := hss
                    have hszA : (Server.mkAddressQuery nsName).question.size < 65536 := by
                      show (1 : Nat) < 65536
                      omega
                    have hstPin := (resolve_sections hszA hrecS hnegS hres).2 st rfl
                    cases subResult with
                    | ok subResp =>
                      have hsub := ioResumeLoop_ok_sections sbelt deadline mI depth' f
                        (Server.seedRevealed st) st _ _ subResp subCache _ hstPin.1 hszA
                        hstPin.2 hrunSub
                      dsimp only [] at hrunB
                      cases hA : Server.extractAAddress nsName subResp.answer with
                      | some addr =>
                        rw [hA] at hrunB
                        cases hgr : Server.gluelessRecheck state subCache with
                        | some hit =>
                          rw [hgr] at hrunB
                          rw [run_pure'] at hrunB
                          exact absurd hrunB (by simp)
                        | none =>
                          rw [hgr] at hrunB
                          exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                            (by exact ⟨cacheRecCanon_touchKeys _ _ _ hsub.2.1,
                              cacheNegSoaCanon_touchKeys _ _ _ hsub.2.2, hchainS, hlrS⟩) hrunB
                      | none =>
                        rw [hA] at hrunB
                        exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                          (by exact ⟨hrecS, hnegS, hchainS, hlrS⟩) hrunB
                    | error e =>
                      dsimp only [] at hrunB
                      exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                        (by exact ⟨hrecS, hnegS, hchainS, hlrS⟩) hrunB
                | error e =>
                  rw [hres] at hrun
                  have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog)
                      (Sock := Unit) state.resources.slist nsName (Except.error e))
                      >>= fun slist' =>
                      Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                        { state with resources := { state.resources with slist := slist' } }
                        deadline depth' f revealed) _
                      = some ((Except.error msg, cout), w') := hrun
                  obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                  exact IH mB (by omega) depth' f _ _ _ _ _ _ _ (by exact hlq) hsz
                    (by exact hss) hrunB
          | some entryIp =>
            obtain ⟨entry, ipAddr⟩ := entryIp
            rw [hbest] at hrun
            cases hbuild : Resolver.buildSubQuery state revealed with
            | none =>
              simp only [hbuild, run_pure'] at hrun
              simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨⟨-, rfl⟩, -⟩ := hrun
              exact ⟨hss.1, hss.2.1⟩
            | some subQuery₀ =>
              simp only [hbuild] at hrun
              by_cases hblk : Server.blockedEgress ipAddr = true
              · simp only [hblk, if_true] at hrun
                rcases m with _ | _ | _ | _ | m'
                · obtain ⟨_, h1, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h3, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨a1, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨a2, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨a2c, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨a3, h3, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  have ham : a3 = m' := by omega
                  rw [ham] at hrun
                  exact IH m' (by omega) depth f _
                    { state with resources := { state.resources with
                        slist := state.resources.slist.markQueried entry.name } }
                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
              · simp only [Bool.not_eq_true] at hblk
                simp only [hblk, Bool.false_eq_true, if_false] at hrun
                rcases m with _ | _ | _ | _ | m'
                · obtain ⟨_, h1, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h3⟩ := run_forwardQuery_bind_inv _ _ _ _ hrun; omega
                · cases hO : w.oracle (VeriDNS.Impl.Message.encode
                      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
                      (Server.ipv4ToAddr ipAddr) with
                  | none =>
                    rw [run_round_bind_eq_none _ _ _ _ _ hO] at hrun
                    simp only [] at hrun
                    exact IH m' (by omega) depth f _
                      { state with resources := { state.resources with
                          slist := state.resources.slist.markQueried entry.name } }
                      _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                  | some d =>
                    cases ha : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d with
                    | none =>
                      rw [run_round_bind_eq_acceptNone _ _ _ _ _ d hO ha] at hrun
                      simp only [] at hrun
                      exact IH m' (by omega) depth f _
                        { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } }
                        _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                    | some bytes =>
                      cases hdec : VeriDNS.Impl.Message.decode bytes with
                      | error errmsg =>
                        rw [run_round_bind_eq_decodeError _ _ _ _ _ d bytes errmsg hO ha hdec]
                          at hrun
                        simp only [] at hrun
                        exact IH m' (by omega) depth f _
                          { state with resources := { state.resources with
                              slist := state.resources.slist.markQueried entry.name } }
                          _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                      | ok resp₀ =>
                        rw [run_round_bind_eq _ _ _ _ _ d bytes resp₀ hO ha hdec] at hrun
                        cases hsani : Server.sanitizeTtlsCap resp₀ with
                        | none =>
                          simp only [hsani] at hrun
                          exact IH m' (by omega) depth f _
                            { state with resources := { state.resources with
                                slist := state.resources.slist.markQueried entry.name } }
                            _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                        | some respS =>
                          simp only [hsani] at hrun
                          have hwfS : SectionsWf respS := by
                            have hcap : respS = Server.capTtls (Edns.stripOpt resp₀) := by
                              unfold Server.sanitizeTtlsCap at hsani
                              exact (Option.some.inj hsani).symm
                            rw [hcap]
                            exact sectionsWf_capTtls_stripOpt_of_decode hdec
                          cases haccR : Server.acceptResponse
                              (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
                              respS with
                          | none =>
                            simp only [haccR] at hrun
                            obtain ⟨mr, hmr, hrun⟩ := run_log_bind_inv _ _ _ hrun
                            exact IH mr (by omega) depth f _
                              { state with resources := { state.resources with
                                  slist := state.resources.slist.markQueried entry.name } }
                              _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                          | some respA =>
                            simp only [haccR] at hrun
                            obtain ⟨ml, hml, hrun⟩ := run_log_bind_inv _ _ _ hrun
                            by_cases htcT : (respA.header.tc == 1) = true
                            case pos =>
                              rw [if_pos htcT] at hrun
                              rcases run_tcpFallbackGuard_inv _ _ _ _ _ hrun with
                                ⟨mF, hmF, hrun⟩ | ⟨mD, _, raw2, tcpResp, tcpRespA, hmD, _, hdec2, hsan2, hacc2, _, hrun⟩
                              · dsimp only [] at hrun
                                obtain ⟨mFl, hmFl, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH mFl (by omega) depth f _
                                  { state with resources := { state.resources with
                                      slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                  _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                              · dsimp only [] at hrun
                                have hwfS2 : SectionsWf tcpResp := by
                                  have hcap : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                    unfold Server.sanitizeTtlsCap at hsan2
                                    exact (Option.some.inj hsan2).symm
                                  rw [hcap]
                                  exact sectionsWf_capTtls_stripOpt_of_decode hdec2
                                have hwfA : SectionsWf tcpRespA := by
                                  rw [acceptResponse_some_eq hacc2]
                                  exact hwfS2
                                by_cases hunf : Server.unfollowableDelegationB
                                    (state.resources.slist.markQueried entry.name)
                                    state.resources.sname tcpRespA = true
                                · simp only [hunf, if_true] at hrun
                                  obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH mu (by omega) depth f _
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                · rw [if_neg hunf] at hrun
                                  by_cases hfeT : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                      && !state.noEdns) = true
                                  case pos =>
                                    -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                                    rw [if_pos hfeT] at hrun
                                    obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                    exact IH mf (by omega) depth f _
                                      { state with
                                            resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name },
                                            noEdns := true }
                                      _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                  rw [if_neg hfeT] at hrun
                                  by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                      && Server.strictDenialB tcpRespA) = true
                                  · -- 051/064: minimised-probe NXDOMAIN now falls back (full-qname re-probe),
                                    -- an IH recursion like probe-consume.
                                    rw [if_pos hstT] at hrun
                                    obtain ⟨ms', hms', hrun⟩ := run_log_bind_inv _ _ _ hrun
                                    exact IH ms' (by omega) depth f _
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                  · rw [if_neg hstT] at hrun
                                    by_cases hpg : (Resolver.probeRoundB state.resources.sname revealed
                                        && !Server.probePassableB tcpRespA) = true
                                    · rw [if_pos hpg] at hrun
                                      obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                      exact IH mp (by omega) depth f _
                                        { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                        _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                    · rw [if_neg hpg] at hrun
                                      cases haft : Server.afterResume
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name tcpRespA with
                                      | finished result cache₂ =>
                                        rw [haft] at hrun
                                        simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
                                        obtain ⟨⟨hres', hcout'⟩, -⟩ := hrun
                                        subst hres'
                                        subst hcout'
                                        rw [afterResume_error_cache haft]
                                        exact ⟨hss.1, hss.2.1⟩
                                      | «continue» state'' =>
                                        rw [haft] at hrun
                                        dsimp only [] at hrun
                                        have hcs := (afterResume_sections (state := { state with resources :=
                                            { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } })
                                          entry.name tcpRespA (by exact hlq) hsz (by exact hss) hwfA).2
                                          state'' haft
                                        exact IH mD (by omega) depth f _ state'' _ _ _ _ _
                                          hcs.1 hsz hcs.2 hrun
                            rw [if_neg htcT, run_bind_pureSome] at hrun
                            dsimp only [] at hrun
                            have hwfA : SectionsWf respA := by
                              rw [acceptResponse_some_eq haccR]
                              exact hwfS
                            by_cases hunf : Server.unfollowableDelegationB
                                (state.resources.slist.markQueried entry.name)
                                state.resources.sname respA = true
                            · simp only [hunf, if_true] at hrun
                              obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              exact IH mu (by omega) depth f _
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                            · rw [if_neg hunf] at hrun
                              by_cases hfeT : (respA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                  && !state.noEdns) = true
                              case pos =>
                                -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                                rw [if_pos hfeT] at hrun
                                obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH mf (by omega) depth f _
                                  { state with
                                        resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name },
                                        noEdns := true }
                                  _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                              rw [if_neg hfeT] at hrun
                              by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                  && Server.strictDenialB respA) = true
                              · -- 051/064: minimised-probe NXDOMAIN now falls back (full-qname re-probe),
                                -- an IH recursion like probe-consume.
                                rw [if_pos hstT] at hrun
                                obtain ⟨ms', hms', hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH ms' (by omega) depth f _
                                  { state with resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name } }
                                  _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                              · rw [if_neg hstT] at hrun
                                by_cases hpg : (Resolver.probeRoundB state.resources.sname revealed
                                    && !Server.probePassableB respA) = true
                                · rw [if_pos hpg] at hrun
                                  obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH mp (by omega) depth f _
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    _ _ _ _ _ (by exact hlq) hsz (by exact hss) hrun
                                · rw [if_neg hpg] at hrun
                                  cases haft : Server.afterResume
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA with
                                  | finished result cache₂ =>
                                    rw [haft] at hrun
                                    simp only [run_pure', Option.some.injEq, Prod.mk.injEq] at hrun
                                    obtain ⟨⟨hres', hcout'⟩, -⟩ := hrun
                                    subst hres'
                                    subst hcout'
                                    rw [afterResume_error_cache haft]
                                    exact ⟨hss.1, hss.2.1⟩
                                  | «continue» state'' =>
                                    rw [haft] at hrun
                                    dsimp only [] at hrun
                                    have hcs := (afterResume_sections (state := { state with resources :=
                                        { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } })
                                      entry.name respA (by exact hlq) hsz (by exact hss) hwfA).2
                                      state'' haft
                                    exact IH ml (by omega) depth f _ state'' _ _ _ _ _
                                      hcs.1 hsz hcs.2 hrun

theorem resolveWithIO_error_sections
    (n : Nat) (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache)
    (now0 : UInt32) (fuel' depth : Nat) (budget : UInt32)
    (w w' : World) (msg : String) (cout : DnsCache)
    (hsz : query.question.size < 65536)
    (hrec : CacheRecCanon cache) (hneg : CacheNegSoaCanon cache)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.error msg, cout), w')) :
    CacheRecCanon cout ∧ CacheNegSoaCanon cout := by
  unfold Server.resolveWithIO at hrun
  cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache with
  | ok y =>
    cases y with
    | done resp₀ stF =>
      rw [hres, run_pure'] at hrun
      exact absurd hrun (by simp)
    | paused st =>
      rw [hres] at hrun
      have hstPin := (resolve_sections hsz hrec hneg hres).2 st rfl
      exact ioResumeLoop_error_sections sbelt (now0 + budget) n depth fuel'
        (Server.seedRevealed st) st w w' msg cout query hstPin.1 hsz hstPin.2 hrun
  | error e =>
    rw [hres, run_pure'] at hrun
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨⟨-, rfl⟩, -⟩ := hrun
    exact ⟨hrec, hneg⟩


theorem replyPath_cacheOut_canon {n : Nat} {query resp : VeriDNS.Spec.Format}
    {cache' : DnsCache} {nowT : UInt32} {w : World}
    {response : VeriDNS.Spec.Format} {cache'' : DnsCache} {w' : World}
    (hrun : Prog.run n (Server.replyForResolution (M := Prog) (Sock := Unit)
        query (.ok resp) cache' nowT) w = some ((response, cache''), w'))
    (ks : Array RRKey) (tnow : UInt32)
    (hca : CanonicalSection resp.answer) (hcn : CanonicalSection resp.authority)
    (hrec : CacheRecCanon cache') (hneg : CacheNegSoaCanon cache') :
    CacheRecCanon (cache''.boundLru ks tnow)
    ∧ CacheNegSoaCanon (cache''.boundLru ks tnow) := by
  obtain ⟨-, hcases⟩ := replyForResolution_run_ok_inv hrun
  obtain ⟨brec, bneg⟩ := stateSections_write hrec hneg resp _ _ _
    (ownerRaws_canonical hca)
  have hpack : CacheRecCanon cache'' ∧ CacheNegSoaCanon cache'' := by
    rcases hcases with rfl | ⟨hnegc, negTtl, soaRR, qu', hext, hq0', rfl⟩
    · exact ⟨brec, bneg⟩
    · refine ⟨cacheRecCanon_storeNegative _ _ _ _ _ _ _ _ brec, ?_⟩
      refine cacheNegSoaCanon_storeNegative _ _ _ _ _ _ _ bneg ?_
      intro rr hrr
      obtain rfl : { soaRR with ttl := Server.capNegativeTtl negTtl } = rr :=
        Option.some.inj hrr
      exact rrWireCanon_set_ttl _ (extractSoaNegative_rrWireCanon hcn hext)
  exact ⟨VeriDNS.Proof.DeliveredWire.cacheRecCanon_boundLru _ ks tnow hpack.1,
    cacheNegSoaCanon_boundLru _ ks tnow hpack.2⟩

theorem extractSoaNegative_owner {qname : ByteArray} {authority : Array ByteArray}
    {negTtl : BitVec 32} {soaRR : VeriDNS.Spec.ResourceRecord}
    (hext : Server.extractSoaNegative qname authority = some (negTtl, soaRR)) :
    Resolver.isAncestorB soaRR.name qname = true := by
  unfold Server.extractSoaNegative at hext
  obtain ⟨b, hb, hf⟩ := Array.exists_of_findSome?_eq_some hext
  cases hdec : DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | error e =>
    rw [hdec] at hf
    exact absurd hf (by simp)
  | ok pr =>
    obtain ⟨rr, p⟩ := pr
    rw [hdec] at hf
    dsimp only at hf
    split at hf
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      split at hf
      · injection hf with hf
        obtain ⟨h1, h2⟩ := Prod.mk.inj hf
        exact h2 ▸ hcond.2
      · exact absurd hf (by simp)
    · exact absurd hf (by simp)

theorem cacheNegSoaOwner_storeNegative {c : DnsCache}
    (name : ByteArray) (qt qc : BitVec 16) (rc : VeriDNS.Spec.Rcode)
    (soa : Option VeriDNS.Spec.ResourceRecord) (expiry tnow : UInt32)
    (h : CacheNegSoaOwner c)
    (hnew : ∀ rr, soa = some rr → Resolver.isAncestorB rr.name name = true) :
    CacheNegSoaOwner (c.storeNegative name qt qc rc soa expiry tnow) := by
  intro e he
  simp only [DnsCache.storeNegative] at he
  rcases Array.mem_push.mp (by simpa using he) with hmem | rfl
  · exact h e (by simpa using (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hmem)).1)
  · exact hnew

theorem cacheNegSoaOwner_touchKeys (c : DnsCache) (ks : Array RRKey) (tnow : UInt32)
    (h : CacheNegSoaOwner c) : CacheNegSoaOwner (c.touchKeys ks tnow) := by
  intro e he rr hrr
  rw [touchKeys_negatives, Array.toList_map, List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  rw [touchNegEntry_soa] at hrr
  rw [touchNegEntry_name]
  exact h e₀ he₀ rr hrr

theorem cacheNegSoaOwner_boundLru (c : DnsCache) (ks : Array RRKey) (tnow : UInt32)
    (h : CacheNegSoaOwner c) : CacheNegSoaOwner (c.boundLru ks tnow) :=
  cacheNegSoaOwner_congr rfl (cacheNegSoaOwner_touchKeys c ks tnow h)

theorem replyPath_cacheOut_negSoaOwner {n : Nat} {query resp : VeriDNS.Spec.Format}
    {cache' : DnsCache} {nowT : UInt32} {w : World}
    {response : VeriDNS.Spec.Format} {cache'' : DnsCache} {w' : World}
    (hrun : Prog.run n (Server.replyForResolution (M := Prog) (Sock := Unit)
        query (.ok resp) cache' nowT) w = some ((response, cache''), w'))
    (ks : Array RRKey) (tnow : UInt32)
    (hown : CacheNegSoaOwner cache') :
    CacheNegSoaOwner (cache''.boundLru ks tnow) := by
  obtain ⟨-, hcases⟩ := replyForResolution_run_ok_inv hrun
  have hpack : CacheNegSoaOwner cache'' := by
    rcases hcases with rfl | ⟨hnegc, negTtl, soaRR, qu, hext, hq0, rfl⟩
    · exact cacheNegSoaOwner_congr
        (VeriDNS.Proof.Refinement.cacheUnlessTruncated_negatives _ _ _ _ _) hown
    · refine cacheNegSoaOwner_storeNegative _ _ _ _ _ _ _
        (cacheNegSoaOwner_congr
          (VeriDNS.Proof.Refinement.cacheUnlessTruncated_negatives _ _ _ _ _) hown) ?_
      intro rr hrr
      obtain rfl : { soaRR with ttl := Server.capNegativeTtl negTtl } = rr :=
        Option.some.inj hrr
      have hcq : Server.clientQname resp = qu.qname := by
        simp [Server.clientQname, hq0]
      have hanc := extractSoaNegative_owner hext
      rw [hcq] at hanc
      exact hanc
  exact cacheNegSoaOwner_boundLru _ ks tnow hpack

end DeliveredSections

theorem deliveredResponse_question (query resp : VeriDNS.Spec.Format) :
    (Server.deliveredResponse query resp).question = resp.question := rfl


theorem resolveWithIO_error_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (budget : UInt32) (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qn : Name)
    (t : RRType) (depth fuel' : Nat)
    (cache : DnsCache) (w w' : World) (now0 : UInt32)
    (msg : String) (cache' : DnsCache)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qn)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (ht : αType qu.qtype = some t)
    (hqany : qu.qtype.toNat ≠ 255)
    (hqc : αClass qu.qclass = some RRClass.in)
    (hCacheWf : CacheWf cache now0) (hNsCanon : CacheNsCanon cache)
    (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache)
    (hCap : cache.records.size ≤ DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hclock : now0.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime now0) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime now0) w)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now0 fuel' depth budget) w = some ((.error msg, cache'), w')) :
    WorldModels net ns ra ednsBuf (αTime now0) w'
    ∧ CacheWf cache' now0
    ∧ CacheNsCanon cache'
    ∧ CacheCnameCanon cache'
    ∧ (∀ e ∈ cache'.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    ∧ CacheNegWf cache' qu.qclass
    ∧ CacheNsDistinct cache'
    ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cache'
    ∧ cache'.records.size ≤ DnsCache.capacity := by
  have hcls1 : qu.qclass = (1 : BitVec 16) := αClass_in_one hqc
  have hWM' : WorldModels net ns ra ednsBuf (αTime now0) w' := by
    obtain ⟨hor, -, -⟩ := run_world_frame hrun
    exact WorldModels_oracle net ns ra ednsBuf (αTime now0) hor hw
  refine ⟨hWM', ?_⟩
  unfold Server.resolveWithIO at hrun
  cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _ query sbelt 64 now0 cache with
  | ok y =>
    cases y with
    | done resp stF =>
      simp only [hres, run_pure'] at hrun
      exact absurd hrun (by simp)
    | paused st =>
      simp only [hres] at hrun
      obtain ⟨sname', chain', hla, hstCache, hstSname, hstNow, hstChain, hstStep, hstLq,
        hstSbelt, hstSlist⟩ :=
        resolve_paused_inv query qu qn sbelt now0 cache st hqu hqm hcanon hres
      have hpack :=
        ioResumeLoop_error_sound net ns ra ednsBuf rttOf sbelt (now0 + budget) hnetWF hGlSbelt
          n depth fuel' (Server.seedRevealed st) st w w' (αTime now0) msg cache'
          hw
          hwTcp
          (by rw [hstNow])
          (by
            rw [hstCache, hstNow]
            exact ⟨hCacheWf, hNsCanon, hCnCanon, hwfrr, (by rw [← hcls1]; exact hNegWf),
              hNsDistinct, hOE⟩)
          (by rw [hstCache]; exact hCap)
          (by rw [hstNow]; exact hclock)
          (by
            rcases hstSlist with h | ⟨nsNames, mcW, hwalk, heq⟩ | h
            · rw [h]; exact GluelessProv_default
            · rw [heq]
              exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                (walkNs_names_canonical _ now0 hNsCanon 128 sname' nsNames mcW
                  (by exact hwalk))
            · rw [h]; exact hGlSbelt)
          (by rw [hstSbelt]; exact hGlSbelt)
          (by
            rw [hstSname]
            exact localAnswer_miss_sname_abs 8 qu.qname #[] _ sname' chain' hla hCnCanon
              ⟨qn, hqm⟩)
          (by
            intro qu2 hqu2
            obtain ⟨q02, hq02, hqu02⟩ := hqu2
            rw [hstLq] at hq02
            obtain rfl := Option.some.inj hq02
            obtain rfl := Option.some.inj (hqu02.symm.trans hqu)
            constructor
            · rw [show αQType qu2.qtype = (αType qu2.qtype).map VeriDNS.Spec.Net.QType.rr from by
                unfold αQType
                split
                · next h255 => exact absurd h255 hqany
                · rfl]
              rw [ht]
              rfl
            · rw [hqc]; rfl)
          hrun
      obtain ⟨hpk, hcap'⟩ := hpack
      rw [hstNow] at hpk
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpk
      exact ⟨h1, h2, h3, h4, (by rw [hcls1]; exact h5), h6, h7, hcap'⟩
  | error e =>
    simp only [hres, run_pure'] at hrun
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨⟨-, rfl⟩, -⟩ := hrun
    exact ⟨hCacheWf, hNsCanon, hCnCanon, hwfrr, hNegWf, hNsDistinct, hOE, hCap⟩


/-- α-bridge: the Internet-class code abstracts to `RRClass.in`. -/
theorem αClass_inClassCode : αClass VeriDNS.Impl.Server.inClassCode = some RRClass.in := rfl

/-- The query-shape class gate is *derivable* at the serve boundary: a served
    query (`queryProblem = none`, RFC-refused otherwise) has an Internet-class
    first question, so `αClass qu.qclass = some RRClass.in` need not be assumed.
    This is what removes `hqin`/`hqc` from the serve capstones (plan-2
    Query-shape row, non-IN → REFUSED). -/
theorem αClass_in_of_queryProblem_none {query : VeriDNS.Spec.Format}
    {qu : VeriDNS.Spec.Question} (hqp : Server.queryProblem query = none)
    (hqu : query.question[0]? = some qu) :
    αClass qu.qclass = some RRClass.in := by
  rw [VeriDNS.Impl.Server.queryProblem_none_qclass hqp hqu]; exact αClass_inClassCode


theorem serveDatagram_verdict_sound
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
    (hedns : VeriDNS.Impl.Edns.ednsProblem query = none)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqany : qu.qtype.toNat ≠ 255)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hqvalid : ∀ x ∈ qm.qname, 0 < x.size ∧ x.size ≤ 63)
    (hqlen : qm.qname.length ≤ 127)
    (hrd : qm.rd = false) (hqstar : qm.qtype ≠ QType.star)
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
    (hrun : Prog.run n (Server.serveDatagram (M := Prog) (Sock := Unit)
        clientSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w')) :
    ∃ (m : Nat) (rr : Except String VeriDNS.Spec.Format) (cache' : DnsCache) (w₂ : World),
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
                ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cacheOut)
            ∧ w'.sent = w.sent
                ++ [((Server.truncateUdp
                      (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
                        (Server.finalizeForClient
                          (Server.buildErrorResponse query Rcode.serverFailure))))
                      (VeriDNS.Impl.Edns.withReplyOpt query
                        (Server.finalizeForClient
                          (Server.buildErrorResponse query Rcode.serverFailure)))
                      (VeriDNS.Impl.Edns.clientCap query)).1, clientAddr)])
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
            ∧ w'.sent = w.sent
                ++ [((Server.truncateUdp
                      (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
                        (Server.deliveredResponse query resp)))
                      (VeriDNS.Impl.Edns.withReplyOpt query
                        (Server.deliveredResponse query resp))
                      (VeriDNS.Impl.Edns.clientCap query)).1, clientAddr)]
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
                            additional := #[] }).size))))) := by
  have hqin : qm.qclass = RRClass.in := by
    have h := αClass_in_of_queryProblem_none hqp hqu
    rw [hqc] at h; exact Option.some.inj h
  have hnany : Server.isAnyQuery query = false :=
    Server.isAnyQuery_false_of_qtype hqu hqany
  rw [serveDatagram_served clientSock acl sbelt cache queryBytes clientAddr query
    hperm hdec hqrbit hqp hedns hnany] at hrun
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
    have hGW : VeriDNS.Spec.Net.GaveUpWitness (αTime w.clock) (αCache cache) [] qm :=
      servfail_means_gaveUpWitness m₁ query qu qm t sbelt w.clock cache 40 6 5 w w₂ msg cache'
        hqu hqm hcanon ht hqq hqc (fun x hx => (hqvalid x hx).2) hCacheWf hNegWf hrunRes
    have hV : ∃ slist v,
        HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] []
          (αCache cache) slist qm v (αCache cache)
        ∧ v.rcode = RCode.servFail ∧ v.answer = [] :=
      ⟨[], _, VeriDNS.Proof.WorldNetwork.gaveUp_hasVerdictAt net ns ra ednsBuf
        rttOf (αCache cache) [] qm hGW
        { aa := false, rcode := RCode.servFail, answer := [], authority := [],
          additional := [] } rfl rfl, rfl, rfl⟩
    obtain ⟨m₃, m₄, y, w₃, hle2, hrunReply, hrunTail⟩ := run_bind_inv hrunK
    obtain ⟨response, cache''⟩ := y
    obtain ⟨hrespE, hcE⟩ := replyForResolution_run_err_inv hrunReply
    rw [hcE, hrespE] at hrunTail
    dsimp only at hrunTail
    obtain ⟨tb, tf, htr⟩ : ∃ tb tf, Server.truncateUdp
        (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
          (Server.finalizeForClient (Server.buildErrorResponse query Rcode.serverFailure))))
        (VeriDNS.Impl.Edns.withReplyOpt query
          (Server.finalizeForClient (Server.buildErrorResponse query Rcode.serverFailure)))
        (VeriDNS.Impl.Edns.clientCap query) = (tb, tf) := ⟨_, _, rfl⟩
    rw [htr] at hrunTail
    dsimp only at hrunTail
    obtain ⟨m₅, m₆, u, w₄, hle3, hrunSend, hrunPure⟩ := run_bind_inv hrunTail
    have hsent : w₄.sent = w.sent
        ++ [((Server.truncateUdp
              (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
                (Server.finalizeForClient
                  (Server.buildErrorResponse query Rcode.serverFailure))))
              (VeriDNS.Impl.Edns.withReplyOpt query
                (Server.finalizeForClient
                  (Server.buildErrorResponse query Rcode.serverFailure)))
              (VeriDNS.Impl.Edns.clientCap query)).1, clientAddr)] := by
      have h4 := run_sendTo_inv hrunSend
      have h3 := (VeriDNS.Proof.SentMinimised.replyForResolution_sends_frame
        query (.error msg) cache' w.clock hrunReply).1
      have h2 := (VeriDNS.Proof.SentMinimised.resolveWithIO_sends_frame
        query sbelt cache w.clock hrunRes).1
      rw [h4, htr]
      simp [h3, h2]
    have hrunPure' : Prog.run m₆ (pure (cache'.boundLru
          (Server.serveTouches query sbelt cache w.clock) w.clock) : Prog DnsCache) w₄
        = some (cacheOut, w') := hrunPure
    rw [run_pure'] at hrunPure'
    obtain ⟨rfl, rfl⟩ : cache'.boundLru
          (Server.serveTouches query sbelt cache w.clock) w.clock = cacheOut ∧ w₄ = w' := by
      simpa using hrunPure'
    exact Or.inl ⟨msg, rfl, hV, hGW, hWM', hwf1', hwf2', hwf3', hwf4', hwf5', hwf6', hwf7', hwf8',
      ⟨CacheWf_boundLru _ _ _ _ hwf1',
       CacheNsCanon_boundLru _ _ _ hwf2',
       CacheCnameCanon_boundLru _ _ _ hwf3',
       wfrrAll_boundLru _ _ hwf4',
       CacheNegWf_boundLru _ _ hwf5',
       CacheNsDistinct_boundLru _ _ _ hwf6',
       VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hwf7',
       VeriDNS.Proof.Cache.boundLru_bounded _ _ _,
       VeriDNS.Proof.DeliveredWire.cacheRecCanon_boundLru _ _ _ hrecC',
       cacheNegSoaCanon_boundLru _ _ _ hnegC'⟩,
      hsent⟩
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
    have hrw : RespWriteWf query resp w.clock := respWriteWf_of_answerWriteWf hwf8.2
    obtain ⟨m₃, m₄, y, w₃, hle2, hrunReply, hrunTail⟩ := run_bind_inv hrunK
    obtain ⟨response, cache''⟩ := y
    have hrespD : response = Server.deliveredResponse query resp :=
      (replyForResolution_run_ok_inv hrunReply).1
    rw [hrespD] at hrunTail
    dsimp only at hrunTail
    obtain ⟨tb, tf, htr⟩ : ∃ tb tf, Server.truncateUdp
        (VeriDNS.Impl.Message.encode
          (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp)))
        (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp))
        (VeriDNS.Impl.Edns.clientCap query) = (tb, tf) := ⟨_, _, rfl⟩
    rw [htr] at hrunTail
    dsimp only at hrunTail
    obtain ⟨m₅, m₆, u, w₄, hle3, hrunSend, hrunPure⟩ := run_bind_inv hrunTail
    have hsent : w₄.sent = w.sent
        ++ [((Server.truncateUdp
              (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
                (Server.deliveredResponse query resp)))
              (VeriDNS.Impl.Edns.withReplyOpt query
                (Server.deliveredResponse query resp))
              (VeriDNS.Impl.Edns.clientCap query)).1, clientAddr)] := by
      have h4 := run_sendTo_inv hrunSend
      have h3 := (VeriDNS.Proof.SentMinimised.replyForResolution_sends_frame
        query (.ok resp) cache' w.clock hrunReply).1
      have h2 := (VeriDNS.Proof.SentMinimised.resolveWithIO_sends_frame
        query sbelt cache w.clock hrunRes).1
      rw [h4, htr]
      simp [h3, h2]
    have hrunPure' : Prog.run m₆ (pure (cache''.boundLru
          (Server.serveTouches query sbelt cache w.clock) w.clock) : Prog DnsCache) w₄
        = some (cacheOut, w') := hrunPure
    rw [run_pure'] at hrunPure'
    obtain ⟨rfl, rfl⟩ : cache''.boundLru
          (Server.serveTouches query sbelt cache w.clock) w.clock = cacheOut ∧ w₄ = w' := by
      simpa using hrunPure'
    refine Or.inr ⟨resp, slist, v, cOut, coutM, rfl, hq0, hcOutR, hHV,
      (deliveredResponse_abstracts_rcode query resp).trans hrc,
      (by rw [deliveredResponse_answer_exact hqu hqm hcanon
        (show αQType qu.qtype = some qm.qtype by
          rw [hqq]; exact αQType_of_αType_ne255 ht hqany)
        hqvalid hq255 hca hwf8.2, hans]),
      (fun bytes hb =>
        VeriDNS.Proof.Server.deliveredResponse_additional_inBailiwick query resp hb),
      hCR, hWM, hwf1, hwf2, hwf3, hwf4, hwf5, hwf6, hwf7, hwf8.1, ?_, hsent, ?_⟩
    · obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := replyPath_cacheOut_wf
        (Server.serveTouches query sbelt cache w.clock) w.clock qu hrunReply hrw hq0
        ⟨qm.qname, hqm, hcanon, fun x hx => (hqvalid x hx).2⟩
        hwf1 hwf2 hwf3 hwf4 hwf6 hwf7 hwf5
      obtain ⟨c1, c2⟩ := replyPath_cacheOut_canon hrunReply
        (Server.serveTouches query sbelt cache w.clock) w.clock hca hcn hrecOut hnegOut
      exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, c1, c2⟩
    · have hqe : resp.question = query.question :=
        resolveWithIO_ok_question m₁ query sbelt cache w.clock 40 6 5 w w₂ resp cache' hrunRes
      refine ⟨?_, ?_, VeriDNS.Proof.Edns.truncateUdp_tc_iff _ _ _⟩
      · intro hfits
        constructor
        · exact VeriDNS.Proof.Server.truncateUdp_no_trunc_cap _ _ _ hfits
        · refine VeriDNS.Proof.DeliveredWire.deliveredResponse_decode_encode query resp
            hqdc hnsc harc ?_ hqn ?_ hca hcn hcd
          · have hcs : VeriDNS.Proof.DeliveredWire.CanonicalSection
                (Server.deliveredResponse query resp).answer :=
              VeriDNS.Proof.DeliveredWire.canonicalSection_typeScrubB
                (VeriDNS.Proof.DeliveredWire.canonicalSection_scrubAnswerB hca hqn)
            have hle := VeriDNS.Proof.DeliveredWire.encode_size_answer_le
              (Server.deliveredResponse query resp) hcs
            have hda : (Server.deliveredResponse query resp).answer
                = Resolver.typeScrubB (RR := VeriDNS.Spec.ResourceRecord)
                    (Server.clientQtype query)
                    (Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord)
                      (Server.clientQname query) resp.answer) := rfl
            rw [hda] at hle
            have hcaple : VeriDNS.Impl.Edns.clientCap query ≤ 1232 :=
              VeriDNS.Impl.Edns.clientCap_le query
            omega
          · intro i
            have hi : i.val < query.question.size := by rw [← hqe]; exact i.isLt
            have hqi := (VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec).2.2.2.2.1
              ⟨i.val, hi⟩
            simpa [hqe] using hqi
      · refine VeriDNS.Proof.Edns.truncateUdp_size_cap _ _ _
          (VeriDNS.Impl.Edns.clientCap_ge query) ?_
        rw [VeriDNS.Impl.Edns.withReplyOpt_question,
          VeriDNS.Proof.Edns.deliveredResponse_question, hqe]
        exact VeriDNS.Proof.Edns.question_skeleton_le_512 hqp hqu hq255



theorem labelsToWireFormatGo_size_ge :
    ∀ (ls : List ByteArray), (∀ l ∈ ls, 0 < l.size) →
      2 * ls.length + 1 ≤ (VeriDNS.Impl.DomainName.labelsToWireFormatGo ls).size := by
  intro ls
  induction ls with
  | nil =>
    intro _
    show 1 ≤ (VeriDNS.Impl.DomainName.labelsToWireFormatGo []).size
    exact Nat.le_refl 1
  | cons l rest ih =>
    intro hv
    have hrest := ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    have hl := hv l (List.mem_cons_self ..)
    show 2 * (rest.length + 1) + 1
      ≤ ((ByteArray.empty.push l.size.toUInt8 ++ l)
          ++ VeriDNS.Impl.DomainName.labelsToWireFormatGo rest).size
    rw [ByteArray.size_append, ByteArray.size_append]
    have h1 : (ByteArray.empty.push l.size.toUInt8).size = 1 := rfl
    omega

set_option maxHeartbeats 1000000 in
theorem serveDatagram_total
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
    (hedns : VeriDNS.Impl.Edns.ednsProblem query = none)
    (hqu : query.question[0]? = some qu)
    (hnany : Server.isAnyQuery query = false)
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
    (hrun : Prog.run n (Server.serveDatagram (M := Prog) (Sock := Unit)
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
                  ∧ VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cacheOut)
              ∧ w'.sent = w.sent
                  ++ [((Server.truncateUdp
                        (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
                          (Server.finalizeForClient
                            (Server.buildErrorResponse query Rcode.serverFailure))))
                        (VeriDNS.Impl.Edns.withReplyOpt query
                          (Server.finalizeForClient
                            (Server.buildErrorResponse query Rcode.serverFailure)))
                        (VeriDNS.Impl.Edns.clientCap query)).1, clientAddr)])
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
              ∧ w'.sent = w.sent
                  ++ [((Server.truncateUdp
                        (VeriDNS.Impl.Message.encode (VeriDNS.Impl.Edns.withReplyOpt query
                          (Server.deliveredResponse query resp)))
                        (VeriDNS.Impl.Edns.withReplyOpt query
                          (Server.deliveredResponse query resp))
                        (VeriDNS.Impl.Edns.clientCap query)).1, clientAddr)]
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
                        (VeriDNS.Impl.Edns.withReplyOpt query
                          (Server.deliveredResponse query resp)))
                      (VeriDNS.Impl.Edns.withReplyOpt query (Server.deliveredResponse query resp))
                      (VeriDNS.Impl.Edns.clientCap query)).1.size
                    ≤ VeriDNS.Impl.Edns.clientCap query
                ∧ ((Server.truncateUdp
                      (VeriDNS.Impl.Message.encode
                        (VeriDNS.Impl.Edns.withReplyOpt query
                          (Server.deliveredResponse query resp)))
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
                              additional := #[] }).size))))) := by
  have hqc : αClass qu.qclass = some RRClass.in := αClass_in_of_queryProblem_none hqp hqu
  have hqany : qu.qtype.toNat ≠ 255 := Server.not_anyQuery_qtype hnany hqu
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
  exact serveDatagram_verdict_sound net ns ra ednsBuf rttOf clientSock acl sbelt
    hnetWF hGlSbelt n queryBytes clientAddr query qu
    ⟨ls.toList, QType.rr t, RRClass.in, false⟩ t cache w w' cacheOut
    hperm hdec hqrbit hqp hedns hqu hqm hcanon ht hqany rfl hqc hvmem hqlen rfl
    (fun h => QType.noConfusion h)
    hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hRecC hNegSoaC
    hclock hw hwTcp hrun
