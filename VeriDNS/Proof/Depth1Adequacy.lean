import VeriDNS.Proof.CooperativeNetwork





namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.DeliveredWire VeriDNS.Proof.Message


theorem referralReply_roundtrips
    (sent : VeriDNS.Spec.Format) (nsAuth glue : Array ByteArray)
    (hsent : Impl.Message.decode (Impl.Message.encode sent) = .ok sent)
    (hnsz : nsAuth.size < 65536) (hgsz : glue.size < 65536)
    (hcanNs : CanonicalSection nsAuth) (hcanGlue : CanonicalSection glue) :
    Impl.Message.decode (Impl.Message.encode (referralReply sent nsAuth glue))
      = .ok (referralReply sent nsAuth glue) := by
  obtain ⟨hqd, _han, _hns, _har, hvqf, _hcaA, _hcaN, _hcaD⟩ := decode_ok_wire_facts hsent
  apply decode_encode
  · exact hqd
  · rfl
  · show (BitVec.ofNat 16 nsAuth.size).toNat = nsAuth.size
    have h216 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [BitVec.toNat_ofNat, h216, Nat.mod_eq_of_lt hnsz]
  · show (BitVec.ofNat 16 glue.size).toNat = glue.size
    have h216 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [BitVec.toNat_ofNat, h216, Nat.mod_eq_of_lt hgsz]
  · exact validQuestionsOfForall hvqf
  · exact canonicalSection_validRRBytes canonicalSection_empty
  · exact canonicalSection_validRRBytes hcanNs
  · exact canonicalSection_validRRBytes hcanGlue


def glueIpOf (bytes : ByteArray) : BitVec 32 :=
  (bytes.data[0]!.toBitVec.setWidth 32 <<< 24) ||| (bytes.data[1]!.toBitVec.setWidth 32 <<< 16) |||
    (bytes.data[2]!.toBitVec.setWidth 32 <<< 8) ||| bytes.data[3]!.toBitVec.setWidth 32

theorem mem_reGlue_inv (cache : DnsCache) (now : UInt32) (nsNames : Array ByteArray)
    (gn : ByteArray) (ga : BitVec 32)
    (h : (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        cache now nsNames) :
    gn ∈ nsNames ∧ ∃ rr ∈ cache.lookupTopCred gn (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now,
      ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true
      ∧ ga = glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) := by
  unfold VeriDNS.Proof.Refinement.reGlue at h
  rw [Array.mem_flatMap] at h
  obtain ⟨nsName, hn, hmem⟩ := h
  rw [Array.mem_filterMap] at hmem
  obtain ⟨rr, hrr, hsome⟩ := hmem
  split at hsome
  · rename_i hsz
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hsome)
    subst h1
    exact ⟨hn, rr, hrr, hsz, h2.symm⟩
  · exact absurd hsome (by simp)

theorem referralWrite_reGlue_exact
    (c : DnsCache) (resp : VeriDNS.Spec.Format) (authRaws addRaws : Array ByteArray)
    (credA credD : Trustworthiness) (now : UInt32) (nsNames : Array ByteArray)
    (nsRaw glueRaw : ByteArray) (nsrr grr : VeriDNS.Spec.ResourceRecord)
    (htc : (resp.header.tc == 1) = false)
    (hcold : c.records = #[])
    (hauthN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) authRaws
        = #[nsRaw])
    (hpns : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsrr)
    (hnsType : nsrr.type = BitVec.ofNat 16 2)
    (haddN : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord) addRaws
        = #[glueRaw])
    (hpg : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) glueRaw = some grr) :
    ∀ gn ga, (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp authRaws credA now)
          resp addRaws credD now) now nsNames →
      ga = glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr) := by
  intro gn ga hmem
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
  rw [hw] at hmem
  obtain ⟨-, rr, hrr, _hsz, hga⟩ := mem_reGlue_inv _ now nsNames gn ga hmem
  obtain ⟨e, he, hlv, hreq⟩ := mem_lookupTopCred_inv _ gn _ _ now rr hrr
  unfold liveEntry at hlv
  simp only [Bool.and_eq_true] at hlv
  obtain ⟨⟨⟨_hnm, htp⟩, _hcl⟩, _hfr⟩ := hlv
  rcases mem_cacheRRs_inv _ _ credD now e he with h1 | ⟨b, hb, rr', hp', hpush⟩
  · rcases mem_storeChecked_inv c nsrr credA now e h1 with hc | hpush
    ·
      rw [hcold] at hc
      exact absurd hc (by simp)
    ·
      exfalso
      have herr : e.rr = nsrr := by rw [hpush]
      rw [herr, hnsType] at htp
      exact absurd htp (by decide)
  ·
    rw [haddN, Array.mem_singleton] at hb
    subst hb
    rw [hpg] at hp'
    rw [Option.some.injEq] at hp'
    subst hp'
    have herr : e.rr = grr := by rw [hpush]
    rw [hga, hreq, herr]
    rfl

theorem allGlued_of_singleton {G : Array (ByteArray × BitVec 32)} {nsNames : Array ByteArray}
    {nsName : ByteArray} {ga0 : BitVec 32}
    (hexact : ∀ n ∈ nsNames, n = nsName) (hg : (nsName, ga0) ∈ G) :
    ∀ n ∈ nsNames, ∃ gn ga, (gn, ga) ∈ G
      ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
          == VeriDNS.Impl.DomainName.foldNameCase n) = true := by
  intro n hn
  rw [hexact n hn]
  exact ⟨nsName, ga0, hg, byteArray_beq_refl _⟩



def twoServerRespond (rootIp : BitVec 32) (nsAuth glue : Array ByteArray)
    (childT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (childNeg : Array ByteArray) :
    ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format :=
  fun addr q => if addr == Server.ipv4ToAddr rootIp
    then referralReply q nsAuth glue
    else treeRespond childT childNeg q

theorem twoServerRespond_root (rootIp : BitVec 32) (nsAuth glue : Array ByteArray)
    (childT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (childNeg : Array ByteArray) :
    ∀ q', twoServerRespond rootIp nsAuth glue childT childNeg (Server.ipv4ToAddr rootIp) q'
      = referralReply q' nsAuth glue := by
  intro q'
  unfold twoServerRespond
  rw [byteArray_beq_refl]
  rfl

theorem twoServerRespond_child (rootIp : BitVec 32) (nsAuth glue : Array ByteArray)
    (childT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (childNeg : Array ByteArray)
    (addr : ByteArray) (hne : (addr == Server.ipv4ToAddr rootIp) = false) :
    ∀ q', twoServerRespond rootIp nsAuth glue childT childNeg addr q'
      = treeRespond childT childNeg q' := by
  intro q'
  unfold twoServerRespond
  rw [hne]
  rfl


set_option maxHeartbeats 1600000 in

theorem resolveWithIO_depth1_adequate
    (respond : ByteArray → VeriDNS.Spec.Format → VeriDNS.Spec.Format)
    (childT : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord) (childNeg : Array ByteArray)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel'' depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entry : SlistEntry) (rootIp : BitVec 32) (subQuery₀ sent : VeriDNS.Spec.Format)
    (nsAuth glue : Array ByteArray) (nsRaw glueRaw : ByteArray)
    (nsrr grr : VeriDNS.Spec.ResourceRecord) (snameLabels : Array ByteArray)
    (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hcoop : CooperativeNetworkAddr respond w)
    (hroot : ∀ q', respond (Server.ipv4ToAddr rootIp) q' = referralReply q' nsAuth glue)
    (hchild : ∀ q', respond (Server.ipv4ToAddr
        (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr))) q'
      = treeRespond childT childNeg q')
    (hegressChild : Server.blockedEgress
        (glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) grr)) = false)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hsentEq : sent = Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ now + budget))
    (hdl₂ : ¬ (w.clock + w.tick w.exchCtr ≥ now + budget))
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
    (hqfe : (q.header.rcode == VeriDNS.Spec.Rcode.formatError) = false)
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
    (hwfRR : ∀ rr ∈ rrs.toList, WfTreeRR rr)
    (hown : ∀ rr ∈ rrs.toList, VeriDNS.Impl.DomainName.nameEqCI
        (VeriDNS.Spec.RRParse.rrName rr)
        (DomainName.randomizeCase (w.ids (w.idCtr + 3)) state.resources.sname) = true) :
    ∃ (resp : VeriDNS.Spec.Format) (cout : DnsCache) (K : Nat) (w' : World),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now (fuel'' + 2) depth budget) w = some ((.ok resp, cout), w')
      ∧ resp.answer = rrs.map VeriDNS.Spec.RRParse.rrBytes
      ∧ resp.question = q.question := by
  have hprobe : Resolver.probeRoundB state.resources.sname (Server.seedRevealed state) = false :=
    probeRoundB_false_of_fullReveal _ _ hrev
  have hsent : Impl.Message.decode (Impl.Message.encode sent) = .ok sent := by
    rw [hsentEq]
    exact buildSubQuery_withSecrets_roundtrips state (Server.seedRevealed state) subQuery₀
      (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hbuild hprobe hcanon
  have hrt := referralReply_roundtrips sent nsAuth glue hsent hnsz hgsz hcanNs hcanGlue
  have hhdr := buildSubQuery_withSecrets_header state (Server.seedRevealed state) subQuery₀
    (w.ids w.idCtr) (w.ids (w.idCtr + 1)) q hlq hbuild
  have htcR : ((referralReply sent nsAuth glue).header.tc == 1) = false := by
    show (sent.header.tc == 1) = false
    rw [hsentEq, hhdr.1]
    exact hqtc
  have hauthN' : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
          (referralReply sent nsAuth glue).authority)
        (referralReply sent nsAuth glue).authority) = #[nsRaw] := hauthN
  have haddN' : VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
          (referralReply sent nsAuth glue).authority)
        (referralReply sent nsAuth glue).additional) = #[glueRaw] := haddN
  have hnone : ∀ e ∈ state.resources.cache.records,
      (DomainName.nameEqCI e.rr.name state.resources.sname
        && e.rr.type == BitVec.ofNat 16 2 && e.rr.class == BitVec.ofNat 16 1) = false := by
    intro e he
    rw [hcold] at he
    exact absurd he (by simp)
  have haddT : ∀ b ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
          (referralReply sent nsAuth glue).authority)
        (referralReply sent nsAuth glue).additional),
      ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (rr.type == BitVec.ofNat 16 2) = false := by
    intro b hb rr hpr
    rw [haddN', Array.mem_singleton] at hb
    subst hb
    rw [hpg, Option.some.injEq] at hpr
    subst hpr
    rw [hgType]
    decide
  have hkey := referralWrite_nsKey_facts state.resources.cache (referralReply sent nsAuth glue)
    (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
        (referralReply sent nsAuth glue).authority)
      (referralReply sent nsAuth glue).authority)
    (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
        (referralReply sent nsAuth glue).authority)
      (referralReply sent nsAuth glue).additional)
    (Resolver.credAuthority ((referralReply sent nsAuth glue).header.aa == 1))
    Resolver.credAdditional state.now state.resources.sname nsRaw nsrr
    htcR hauthN' hpns hnsName hnsType hnsClass hnzNs hfreshNs haddT hnone
  have hwalk0 := VeriDNS.Proof.Refinement.walkNs_base (C := DnsCache)
    (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
    (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
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
    (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 127 hkey.1
  simp only [hsn] at hwalk0
  have hnb0 : NoBetterGlue (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      state.resources.cache (referralReply sent nsAuth glue)
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
          (referralReply sent nsAuth glue).authority)
        (referralReply sent nsAuth glue).authority)
      (Resolver.credAuthority ((referralReply sent nsAuth glue).header.aa == 1)) state.now)
      grr Resolver.credAdditional state.now := by
    have hwIn : Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        state.resources.cache (referralReply sent nsAuth glue)
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
            (referralReply sent nsAuth glue).authority)
          (referralReply sent nsAuth glue).authority)
        (Resolver.credAuthority ((referralReply sent nsAuth glue).header.aa == 1)) state.now
        = state.resources.cache.storeChecked nsrr
            (Resolver.credAuthority ((referralReply sent nsAuth glue).header.aa == 1))
            state.now := by
      unfold Resolver.cacheUnlessTruncated
      simp only [htcR, Bool.false_eq_true, if_false]
      rw [hauthN', cacheRRs_singleton, hpns]
    intro e2 he2 _hfr _hnm htp _hcl
    rw [hwIn] at he2
    rcases mem_storeChecked_inv state.resources.cache nsrr _ state.now e2 he2 with hin | hpush
    · rw [hcold] at hin
      exact absurd hin (by simp)
    · exfalso
      have h2 : e2.rr = nsrr := by rw [hpush]
      rw [h2, hnsType, hgType] at htp
      exact absurd htp (by decide)
  have hexp : ∀ b' ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
          (referralReply sent nsAuth glue).authority)
        (referralReply sent nsAuth glue).additional),
      ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
      DomainName.nameEqCI rr.name grr.name = true → (rr.type == grr.type) = true →
      (rr.class == grr.class) = true →
      (state.now + rr.ttl.toNat.toUInt32 > state.now)
        ∧ ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4)
            = true := by
    intro b' hb' rr hpr _ _ _
    rw [haddN', Array.mem_singleton] at hb'
    subst hb'
    rw [hpg, Option.some.injEq] at hpr
    subst hpr
    exact ⟨hfreshG, hgSize⟩
  have hbmem : glueRaw ∈ VeriDNS.Spec.RRParse.normalizeSection (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
          (referralReply sent nsAuth glue).authority)
        (referralReply sent nsAuth glue).additional) := by
    rw [haddN']
    exact Array.mem_singleton.mpr rfl
  obtain ⟨ga0, hg⟩ := reGlue_preBoundLru_of_referral_glue
    (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      state.resources.cache (referralReply sent nsAuth glue)
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
    Resolver.credAdditional state.now
    ((VeriDNS.Spec.CacheSpec.lookupTopCred (C := DnsCache)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
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
        state.resources.sname (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now).filterMap
      (fun (rr : VeriDNS.Spec.ResourceRecord) =>
        if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
        else none))
    grr glueRaw (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr)
    hkey.2.1 hgKey htcR hbmem hpg hnzG hgType hgClass hfreshG hgSize hnb0 hexp
  have hneNs : (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) (referralReply sent nsAuth glue).authority) (referralReply sent nsAuth glue).authority)).isEmpty = false := by
    have h := VeriDNS.Proof.Refinement.extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn
      (RR := VeriDNS.Spec.ResourceRecord) ((referralReply sent nsAuth glue).authority) hns
    simpa using h
  have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
      (referralReply sent nsAuth glue).authority state.resources.sname ≤ snameLabels.size :=
    delegationMatchCount_le ((referralReply sent nsAuth glue).authority)
      state.resources.sname snameLabels hsn
  have hclose := VeriDNS.Proof.Refinement.currentCloser_false_of_ge
    (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) (referralReply sent nsAuth glue).authority) (referralReply sent nsAuth glue).authority))
    (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord)
        (referralReply sent nsAuth glue).authority)
      (referralReply sent nsAuth glue).additional))
    (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
      (referralReply sent nsAuth glue).authority state.resources.sname)
    snameLabels.size hneNs hge
  obtain ⟨resp, cout, hchain, hansEq, hquesEq⟩ :=
    depth1Delegation_chain respond childT childNeg sbelt state
    (now + budget) depth fuel'' (Server.seedRevealed state) w entry rootIp subQuery₀ sent
    nsAuth glue _ snameLabels.size _ q qu
    (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) nsrr) ga0 rrs
    hcoop (hroot sent)
    (fun gn ga hmem q' => by
      rw [referralWrite_reGlue_exact state.resources.cache (referralReply sent nsAuth glue)
        _ _ _ _ state.now _ nsRaw glueRaw nsrr grr htcR hcold hauthN' hpns hnsType haddN' hpg
        gn ga hmem]
      exact hchild q')
    (fun gn ga hmem => by
      rw [referralWrite_reGlue_exact state.resources.cache (referralReply sent nsAuth glue)
        _ _ _ _ state.now _ nsRaw glueRaw nsrr grr htcR hcold hauthN' hpns hnsType haddN' hpg
        gn ga hmem]
      exact hegressChild)
    hsentEq hsendq hdl hdl₂ hbest hegress hbuild hrev hcanon hlq hqu hqtc hqsf hqfe hchain0
    hrt hoptG hnA hdG hns hsoa (hclq sent) (hbaiq sent)
    rfl hwalk0 hclose
    (by rw [Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨_, hg⟩]; rfl)
    hkey.2.1 hg
    (allGlued_of_singleton hkey.2.2 hg)
    hlk hsz hwfRR hown
  obtain ⟨K, w', hrun⟩ := resolveWithIO_adequate_of_chain query sbelt cache now (fuel'' + 2)
    depth budget w state (.ok resp, cout) hpause hchain
  exact ⟨resp, cout, K, w', hrun, hansEq, hquesEq⟩

end VeriDNS.Proof.Adequacy
