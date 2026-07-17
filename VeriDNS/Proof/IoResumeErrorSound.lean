import VeriDNS.Proof.IoResumeSound
import VeriDNS.Proof.Resolver
open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache VeriDNS.Spec
set_option maxHeartbeats 2000000






def CachePackNC (c : DnsCache) (now : UInt32) : Prop :=
  CacheWf c now
  ∧ CacheNsCanon c
  ∧ CacheCnameCanon c
  ∧ (∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr)
  ∧ CacheNegWf c (1 : BitVec 16)
  ∧ CacheNsDistinct c
  ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey c

theorem CachePackNC.of_parts {c : DnsCache} {now : UInt32}
    (hwf : CacheWf c now) (hns : CacheNsCanon c) (hcnc : CacheCnameCanon c)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hneg : CacheNegWf c (1 : BitVec 16)) (hnsd : CacheNsDistinct c)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c) : CachePackNC c now :=
  ⟨hwf, hns, hcnc, hwfrr, hneg, hnsd, hoe⟩

theorem credAnswer_tier (aa : Bool) :
    Resolver.credAnswer aa = VeriDNS.Spec.Trustworthiness.authoritativeSection
    ∨ Resolver.credAnswer aa = VeriDNS.Spec.Trustworthiness.authoritySection
    ∨ Resolver.credAnswer aa = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
    ∨ Resolver.credAnswer aa = VeriDNS.Spec.Trustworthiness.additionalAuthoritative := by
  unfold Resolver.credAnswer
  cases aa
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl

theorem credAuthority_tier (aa : Bool) :
    Resolver.credAuthority aa = VeriDNS.Spec.Trustworthiness.authoritativeSection
    ∨ Resolver.credAuthority aa = VeriDNS.Spec.Trustworthiness.authoritySection
    ∨ Resolver.credAuthority aa = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
    ∨ Resolver.credAuthority aa = VeriDNS.Spec.Trustworthiness.additionalAuthoritative := by
  unfold Resolver.credAuthority
  cases aa
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)

theorem credAdditional_tier :
    (Resolver.credAdditional : VeriDNS.Spec.Trustworthiness)
        = VeriDNS.Spec.Trustworthiness.authoritativeSection
    ∨ (Resolver.credAdditional : VeriDNS.Spec.Trustworthiness)
        = VeriDNS.Spec.Trustworthiness.authoritySection
    ∨ (Resolver.credAdditional : VeriDNS.Spec.Trustworthiness)
        = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
    ∨ (Resolver.credAdditional : VeriDNS.Spec.Trustworthiness)
        = VeriDNS.Spec.Trustworthiness.additionalAuthoritative :=
  Or.inr (Or.inr (Or.inr rfl))

theorem cachePackNC_write (cache : DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hcred : cred = VeriDNS.Spec.Trustworthiness.authoritativeSection
      ∨ cred = VeriDNS.Spec.Trustworthiness.authoritySection
      ∨ cred = VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
      ∨ cred = VeriDNS.Spec.Trustworthiness.additionalAuthoritative)
    (haw : AnswerWriteWf raws now)
    (hp : CachePackNC cache now) :
    CachePackNC (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) now := by
  obtain ⟨hwf, hns, hcnc, hwfrr, hneg, hnsd, hoe⟩ := hp
  have hval : ∀ raw ∈ raws.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
        (αRR rr).isSome = true :=
    fun raw hraw rr hp' => (haw raw hraw rr hp').1
  have hno : ∀ raw ∈ raws.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat :=
    fun raw hraw rr hp' => (haw raw hraw rr hp').2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply CacheWf_cacheUnlessTruncated _ _ _ _ _ hwf hcred
    intro raw hraw rr hp'
    exact parseRaw_entry_canonical _ now hp' (normRaws_hval hval raw hraw rr hp')
      (normRaws_hno hno raw hraw rr hp')
  · apply CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hns
    intro raw hraw rr hp' htype
    exact (haw raw hraw rr hp').2.2.1 htype
  · apply CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hcnc
    intro raw hraw rr hp' htype
    exact (haw raw hraw rr hp').2.2.2 htype
  · exact wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
  · exact CacheNegWf_cacheUnlessTruncated _ _ _ _ _ hneg
  · exact CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hnsd
  · exact VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hoe _ _ _ _

theorem cachePackNC_touchKeys {c : DnsCache} {now : UInt32}
    (ks : Array RRKey) (tnow : UInt32) (hp : CachePackNC c now) :
    CachePackNC (c.touchKeys ks tnow) now := by
  obtain ⟨hwf, hns, hcnc, hwfrr, hneg, hnsd, hoe⟩ := hp
  exact ⟨CacheWf_touchKeys c ks tnow now hwf, CacheNsCanon_touchKeys c ks tnow hns,
    CacheCnameCanon_touchKeys c ks tnow hcnc, wfrrAll_touchKeys ks tnow hwfrr,
    CacheNegWf_touchKeys ks tnow hneg, CacheNsDistinct_touchKeys c ks tnow hnsd,
    VeriDNS.Proof.NameTree.oneExpiry_touchKeys ks tnow hoe⟩

theorem cachePackNC_boundLru {c : DnsCache} {now : UInt32}
    (ks : Array RRKey) (tnow : UInt32) (hp : CachePackNC c now) :
    CachePackNC (c.boundLru ks tnow) now
    ∧ (c.boundLru ks tnow).records.size ≤ DnsCache.capacity := by
  obtain ⟨hwf, hns, hcnc, hwfrr, hneg, hnsd, hoe⟩ := hp
  exact ⟨⟨CacheWf_boundLru c ks tnow now hwf, CacheNsCanon_boundLru c ks tnow hns,
    CacheCnameCanon_boundLru c ks tnow hcnc, wfrrAll_boundLru ks tnow hwfrr,
    CacheNegWf_boundLru ks tnow hneg, CacheNsDistinct_boundLru c ks tnow hnsd,
    VeriDNS.Proof.NameTree.oneExpiry_boundLru ks tnow hoe⟩,
    VeriDNS.Proof.Cache.boundLru_bounded c ks tnow⟩



structure RespPackFacts (resp : VeriDNS.Spec.Format) (now : UInt32) : Prop where
  awAns : AnswerWriteWf resp.answer now
  awAuth : AnswerWriteWf resp.authority now
  exAuth : ∀ b ∈ resp.authority.toList, ∃ rr,
    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
      ∧ αRR rr ≠ none
  awAdd : (αResp resp).isReferral = true → AnswerWriteWf resp.additional now
  canonAuth : ∀ b ∈ resp.authority.toList, VeriDNS.Proof.Message.CanonicalRR b

theorem answerWriteWf_ownerRaws {sect : Array ByteArray} {now : UInt32} (sname : ByteArray)
    (h : AnswerWriteWf sect now) :
    AnswerWriteWf (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sect) now :=
  fun raw hraw rr hp => h raw (ownerRaws_toList_sub hraw) rr hp

theorem answerWriteWf_bailiwickRaws {sect : Array ByteArray} {now : UInt32} (bw : ByteArray)
    (h : AnswerWriteWf sect now) :
    AnswerWriteWf (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw sect) now :=
  fun raw hraw rr hp => h raw (bailiwickRaws_toList_sub hraw) rr hp

theorem answerWriteWf_cnameRaws {sect : Array ByteArray} {now : UInt32} (sname : ByteArray)
    (h : AnswerWriteWf sect now) :
    AnswerWriteWf (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) sname sect) now :=
  fun raw hraw rr hp => h raw (cnameRaws_toList_sub hraw) rr hp



theorem cnameToChase_target_abs {resp : VeriDNS.Spec.Format} {cn : ByteArray} {now : UInt32}
    (h : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some cn)
    (haw : AnswerWriteWf resp.answer now) :
    ∃ na, αName cn = some na := by
  obtain ⟨qu, hqu, hex⟩ := VeriDNS.Proof.Resolver.cnameToChase_extractCname h
  unfold Resolver.extractCname at hex
  obtain ⟨b, hb, hfb⟩ := Array.exists_of_findSome?_eq_some hex
  cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hp] at hfb; exact absurd hfb (by simp)
  | some rr =>
    rw [hp] at hfb
    dsimp only [] at hfb
    split at hfb
    · next hcond =>
      rw [Option.some.injEq] at hfb
      subst hfb
      rw [Bool.and_eq_true] at hcond
      have ht5 : rr.type = BitVec.ofNat 16 5 :=
        eq_of_beq hcond.1
      obtain ⟨na, hna, -⟩ := (haw b (Array.mem_def.mp hb) rr hp).2.2.2 ht5
      exact ⟨na, hna⟩
    · exact absurd hfb (by simp)

theorem localAnswer_miss_sname_abs {cache : DnsCache} {qt qc : BitVec 16} {now : UInt32} :
    ∀ (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
      (sname' : ByteArray) (chain' : Array ByteArray),
      Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname chain visited = .miss sname' chain' →
      CacheCnameCanon cache →
      (∃ qn, αName sname = some qn) →
      ∃ qn', αName sname' = some qn' := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname chain visited sname' chain' hres
    exact absurd hres (by simp [Resolver.localAnswer])
  | succ f IHf =>
    intro sname chain visited sname' chain' hres hcnc hsn
    unfold Resolver.localAnswer at hres
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now with
    | some rc => rw [hneg] at hres; exact absurd hres (by simp)
    | none =>
      rw [hneg] at hres
      dsimp only [] at hres
      by_cases hie : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true
      · rw [if_pos hie] at hres
        by_cases hq5 : (qt == (5 : BitVec 16)) = true
        · rw [if_pos hq5] at hres
          obtain ⟨rfl, -⟩ := Resolver.LocalResult.miss.inj hres
          exact hsn
        · rw [if_neg hq5] at hres
          cases hcrr : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
              (RR := VeriDNS.Spec.ResourceRecord) cache sname (5 : BitVec 16) qc now)[0]? with
          | none =>
            rw [hcrr] at hres
            obtain ⟨rfl, -⟩ := Resolver.LocalResult.miss.inj hres
            exact hsn
          | some crr =>
            rw [hcrr] at hres
            dsimp only [] at hres
            split at hres
            · obtain ⟨rfl, -⟩ := Resolver.LocalResult.miss.inj hres
              exact hsn
            · obtain ⟨na, hna, -⟩ := cname_rdata_canonical_of_CacheCnameCanon cache sname
                qc now hcnc crr (Array.mem_def.mp (Array.mem_of_getElem? hcrr))
              exact IHf _ _ _ _ _ hres hcnc ⟨na, hna⟩
      · rw [if_neg hie] at hres
        exact absurd hres (by simp)

theorem step_carry
    (s s2 : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (next : VeriDNS.Spec.AlgorithmStep)
    (hstep : Resolver.step (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
        (RR := VeriDNS.Spec.ResourceRecord) s = .goto next s2
      ∨ Resolver.step (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
        (RR := VeriDNS.Spec.ResourceRecord) s = .needsIO s2)
    (hp : CachePackNC s.resources.cache s.now)
    (hgl : GluelessProv s.resources.slist)
    (hglb : GluelessProv s.resources.sbelt)
    (hrf : ∀ resp, s.lastResponse = some resp → RespPackFacts resp s.now) :
    CachePackNC s2.resources.cache s.now
    ∧ s2.now = s.now
    ∧ GluelessProv s2.resources.slist
    ∧ s2.resources.sbelt = s.resources.sbelt
    ∧ (∀ resp, s2.lastResponse = some resp → RespPackFacts resp s.now)
    ∧ ((∃ qn, αName s.resources.sname = some qn) →
        ∃ qn', αName s2.resources.sname = some qn')
    ∧ s2.lastQuery = s.lastQuery := by
  have hns : CacheNsCanon s.resources.cache := hp.2.1
  rcases hstep with hstep | hstep
  case inl =>
    cases hcs : s.currentStep <;> simp only [Resolver.step, hcs] at hstep
    case checkAnswer =>
      unfold Resolver.stepCheckLocal at hstep
      cases hlq : s.lastQuery with
      | none =>
        rw [hlq] at hstep
        obtain ⟨-, rfl⟩ : next = .findServers ∧ s2 = s := by
          exact ⟨(Resolver.StepResult.goto.inj hstep).1.symm, (Resolver.StepResult.goto.inj hstep).2.symm⟩
        exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, hlq⟩
      | some q =>
        rw [hlq] at hstep
        dsimp only [] at hstep
        cases hqu : q.question[0]? with
        | none =>
          rw [hqu] at hstep
          obtain ⟨-, rfl⟩ : next = .findServers ∧ s2 = s :=
            ⟨(Resolver.StepResult.goto.inj hstep).1.symm, (Resolver.StepResult.goto.inj hstep).2.symm⟩
          exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, hlq⟩
        | some qu =>
          rw [hqu] at hstep
          dsimp only [] at hstep
          cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
              s.resources.cache qu.qtype qu.qclass s.now 8 s.resources.sname s.cnameChain
              (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname s.cnameChain) with
          | negative rc soaAuth chain => rw [hla] at hstep; exact absurd hstep (by simp)
          | answerHit sname chain rrs => rw [hla] at hstep; exact absurd hstep (by simp)
          | abort => rw [hla] at hstep; exact absurd hstep (by simp)
          | miss sname' chain =>
            rw [hla] at hstep
            dsimp only [] at hstep
            by_cases hsn : (sname' == s.resources.sname) = true
            · rw [if_pos hsn] at hstep
              obtain ⟨-, rfl⟩ : next = .findServers ∧ s2 = s :=
                ⟨(Resolver.StepResult.goto.inj hstep).1.symm, (Resolver.StepResult.goto.inj hstep).2.symm⟩
              exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, hlq⟩
            · rw [if_neg hsn] at hstep
              obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
              exact ⟨hp, rfl, GluelessProv_default, rfl, hrf,
                fun hs => localAnswer_miss_sname_abs 8 s.resources.sname s.cnameChain _
                  sname' chain hla hp.2.2.1 hs, rfl⟩
    case findServers =>
      unfold Resolver.stepFindServers at hstep
      dsimp only [letFun] at hstep
      cases hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
          s.resources.sname s.resources.cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1)
          s.now 128 with
      | some p =>
        obtain ⟨nsNames, mc⟩ := p
        rw [hwalk] at hstep
        dsimp only [] at hstep
        split at hstep
        · obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
          exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, rfl⟩
        · split at hstep
          · obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
            exact ⟨hp, rfl, hglb, rfl, hrf, fun h => h, rfl⟩
          · obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
            refine ⟨hp, rfl, ?_, rfl, hrf, fun h => h, rfl⟩
            exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
              (walkNs_names_canonical s.resources.cache s.now hns 128 s.resources.sname
                nsNames mc hwalk)
      | none =>
        rw [hwalk] at hstep
        dsimp only [] at hstep
        split at hstep
        · obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
          exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, rfl⟩
        · obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
          exact ⟨hp, rfl, hglb, rfl, hrf, fun h => h, rfl⟩
    case sendQueries =>
      unfold Resolver.stepSendQueries at hstep
      cases hlr : s.lastResponse with
      | some resp =>
        rw [hlr] at hstep
        obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
        exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, rfl⟩
      | none => rw [hlr] at hstep; exact absurd hstep (by simp)
    case analyzeResponse =>
      unfold Resolver.stepAnalyzeResponse at hstep
      cases hlr : s.lastResponse with
      | none => rw [hlr] at hstep; exact absurd hstep (by simp)
      | some resp =>
        rw [hlr] at hstep
        dsimp only [] at hstep
        have hfacts := hrf resp hlr
        cases hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp with
        | some canonicalName =>
          rw [hcn] at hstep
          dsimp only [] at hstep
          by_cases htc : (resp.header.tc == 1) = true
          · rw [if_pos htc] at hstep; exact absurd hstep (by simp)
          · rw [if_neg htc] at hstep
            split at hstep
            · exact absurd hstep (by simp)
            · obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
              refine ⟨?_, rfl, GluelessProv_default, rfl, ?_, fun _ => cnameToChase_target_abs hcn hfacts.awAns, rfl⟩
              · exact cachePackNC_write _ _ _ _ _ (credAnswer_tier _)
                  (answerWriteWf_cnameRaws _ hfacts.awAns) hp
              · intro r hr; exact absurd hr (by simp)
        | none =>
          rw [hcn] at hstep
          dsimp only [] at hstep
          by_cases hsf : (resp.header.rcode == Rcode.serverFailure
              || !Resolver.classifiableB resp) = true
          · rw [if_pos hsf] at hstep
            obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
            refine ⟨hp, rfl, hgl, rfl, ?_, fun h => h, rfl⟩
            intro r hr; exact absurd hr (by simp)
          · rw [if_neg hsf] at hstep
            by_cases h4a : (!Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp
                && !(resp.header.rcode == Rcode.nameError)
                && resp.answer.isEmpty
                && !resp.authority.isEmpty) = true
            · rw [if_pos h4a] at hstep
              by_cases href : (Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord)
                    resp.authority 2
                  && resp.header.aa == 0
                  && resp.header.rcode == Rcode.noError
                  && !Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord)
                    resp.authority 6) = true
              · rw [if_pos href] at hstep
                obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at h4a href
                have hir : (αResp resp).isReferral = true :=
                  αResp_isReferral_true_of_referralShape h4a.1.2 (by
                      rw [href.1.1.2]) (by rw [href.1.2]) href.1.1.1 href.2 hfacts.exAuth
                refine ⟨?_, rfl, ?_, rfl, ?_, fun h => h, rfl⟩
                · exact cachePackNC_write _ _ _ _ _ credAdditional_tier
                    (answerWriteWf_bailiwickRaws _ (hfacts.awAdd hir))
                    (cachePackNC_write _ _ _ _ _ (credAuthority_tier _)
                      (answerWriteWf_bailiwickRaws _ hfacts.awAuth) hp)
                · exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                    (extractNsNames_ownerRaws_canonical resp.authority hfacts.canonAuth)
                · intro r hr; exact absurd hr (by simp)
              · rw [if_neg href] at hstep
                split at hstep
                · exact absurd hstep (by simp)
                ·
                  obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
                  refine ⟨hp, rfl, hgl, rfl, ?_, fun h => h, rfl⟩
                  intro r hr; exact absurd hr (by simp)
            · rw [if_neg h4a] at hstep
              split at hstep
              · exact absurd hstep (by simp)      -- C: entitledAnswerB ⇒ answer
              · split at hstep
                · exact absurd hstep (by simp)    -- D: nameError && empty ⇒ answer
                · split at hstep
                  · exact absurd hstep (by simp)  -- E: SOA-nodata ⇒ answer
                  · split at hstep
                    · exact absurd hstep (by simp) -- F: tc==1 ⇒ answer
                    · -- G (else): foreign / nameError-with-answer / ambiguous empty
                      -- ⇒ retry (goto sendQueries)
                      obtain ⟨-, rfl⟩ := Resolver.StepResult.goto.inj hstep
                      refine ⟨hp, rfl, hgl, rfl, ?_, fun h => h, rfl⟩
                      intro r hr; exact absurd hr (by simp)
  case inr =>
    cases hcs : s.currentStep <;> simp only [Resolver.step, hcs] at hstep
    case checkAnswer =>
      unfold Resolver.stepCheckLocal at hstep
      cases hlq : s.lastQuery with
      | none => rw [hlq] at hstep; exact absurd hstep (by simp)
      | some q =>
        rw [hlq] at hstep
        dsimp only [] at hstep
        cases hqu : q.question[0]? with
        | none => rw [hqu] at hstep; exact absurd hstep (by simp)
        | some qu =>
          rw [hqu] at hstep
          dsimp only [] at hstep
          split at hstep <;> first
            | exact absurd hstep (by simp)
            | (split at hstep <;> exact absurd hstep (by simp))
    case findServers =>
      unfold Resolver.stepFindServers at hstep
      dsimp only [letFun] at hstep
      split at hstep
      · try dsimp only [] at hstep
        split at hstep
        · exact absurd hstep (by simp)
        · split at hstep <;> exact absurd hstep (by simp)
      · try dsimp only [] at hstep
        split at hstep <;> exact absurd hstep (by simp)
    case sendQueries =>
      unfold Resolver.stepSendQueries at hstep
      cases hlr : s.lastResponse with
      | some resp => rw [hlr] at hstep; exact absurd hstep (by simp)
      | none =>
        rw [hlr] at hstep
        obtain rfl : s = s2 := Resolver.StepResult.needsIO.inj hstep
        exact ⟨hp, rfl, hgl, rfl, hrf, fun h => h, rfl⟩
    case analyzeResponse =>
      unfold Resolver.stepAnalyzeResponse at hstep
      cases hlr : s.lastResponse with
      | none => rw [hlr] at hstep; exact absurd hstep (by simp)
      | some resp =>
        rw [hlr] at hstep
        dsimp only [] at hstep
        split at hstep
        · try dsimp only [] at hstep
          split at hstep
          · exact absurd hstep (by simp)
          · split at hstep <;> exact absurd hstep (by simp)
        · split at hstep
          · exact absurd hstep (by simp)
          · split at hstep
            · split at hstep <;> (try split at hstep) <;> exact absurd hstep (by simp)
            · split at hstep
              · exact absurd hstep (by simp)
              · split at hstep
                · exact absurd hstep (by simp)
                · split at hstep
                  · exact absurd hstep (by simp)
                  · split at hstep <;> (try split at hstep) <;> exact absurd hstep (by simp)


theorem dropIfBizarre_fields
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format) :
    (Server.dropIfBizarre state entryName resp).resources.cache = state.resources.cache
    ∧ (Server.dropIfBizarre state entryName resp).now = state.now
    ∧ (Server.dropIfBizarre state entryName resp).resources.sbelt = state.resources.sbelt
    ∧ (Server.dropIfBizarre state entryName resp).resources.sname = state.resources.sname
    ∧ (Server.dropIfBizarre state entryName resp).lastResponse = state.lastResponse
    ∧ (Server.dropIfBizarre state entryName resp).lastQuery = state.lastQuery := by
  unfold Server.dropIfBizarre
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dropIfBizarre_glProv
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (h : GluelessProv state.resources.slist) :
    GluelessProv (Server.dropIfBizarre state entryName resp).resources.slist := by
  unfold Server.dropIfBizarre
  split
  · exact GluelessProv_removeServer entryName h
  · exact h

theorem resolveLoop_paused_carry :
    ∀ (fuel : Nat)
      (s s' : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
      Resolver.resolve.loop (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
          (RR := VeriDNS.Spec.ResourceRecord) s fuel = .ok (.paused s') →
      CachePackNC s.resources.cache s.now →
      GluelessProv s.resources.slist →
      GluelessProv s.resources.sbelt →
      (∀ resp, s.lastResponse = some resp → RespPackFacts resp s.now) →
      CachePackNC s'.resources.cache s.now
      ∧ s'.now = s.now
      ∧ GluelessProv s'.resources.slist
      ∧ s'.resources.sbelt = s.resources.sbelt
      ∧ ((∃ qn, αName s.resources.sname = some qn) →
          ∃ qn', αName s'.resources.sname = some qn')
      ∧ s'.lastQuery = s.lastQuery := by
  intro fuel
  induction fuel with
  | zero =>
    intro s s' h
    exact absurd h (by simp [Resolver.resolve.loop])
  | succ f IH =>
    intro s s' h hp hgl hglb hrf
    rw [Resolver.resolve.loop] at h
    split at h
    · exact absurd h (by simp)
    · next nextStep s2 hst =>
      obtain ⟨hp2, hnow2, hgl2, hsb2, hrf2, hsn2, hlq2⟩ :=
        step_carry s s2 nextStep (Or.inl hst) hp hgl hglb hrf
      obtain ⟨hpI, hnowI, hglI, hsbI, hsnI, hlqI⟩ :=
        IH { s2 with currentStep := nextStep } s' h
          (by show CachePackNC s2.resources.cache s2.now; rw [hnow2]; exact hp2)
          (by exact hgl2) (by rw [hsb2]; exact hglb)
          (by show ∀ resp, s2.lastResponse = some resp → RespPackFacts resp s2.now
              rw [hnow2]; exact hrf2)
      refine ⟨?_, ?_, hglI, ?_, ?_, ?_⟩
      · show CachePackNC s'.resources.cache s.now
        rw [← hnow2]
        exact hnowI ▸ hpI
      · exact hnowI.trans hnow2
      · exact hsbI.trans hsb2
      · exact fun hs => hsnI (hsn2 hs)
      · exact hlqI.trans hlq2
    · next s2 hst =>
      obtain rfl : s2 = s' := by
        have h1 := Except.ok.inj h
        exact Resolver.ResolveYield.paused.inj h1
      obtain ⟨hp2, hnow2, hgl2, hsb2, -, hsn2, hlq2⟩ :=
        step_carry s s2 s.currentStep (Or.inr hst) hp hgl hglb hrf
      exact ⟨hp2, hnow2, hgl2, hsb2, hsn2, hlq2⟩
    · exact absurd h (by simp)

theorem afterResume_error_cache
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {resp : VeriDNS.Spec.Format} {msg : String} {cacheE : DnsCache}
    (heq : Server.afterResume state entryName resp = .finished (.error msg) cacheE) :
    cacheE = state.resources.cache := by
  unfold Server.afterResume at heq
  split at heq
  · exact absurd heq (by simp)
  · exact absurd heq (by simp)
  · have h2 := (Server.IoStep.finished.inj heq).2
    exact h2.symm

theorem afterResume_continue_carry
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {resp : VeriDNS.Spec.Format}
    {state'' : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    (heq : Server.afterResume state entryName resp = .continue state'')
    (hp : CachePackNC state.resources.cache state.now)
    (hgl : GluelessProv state.resources.slist)
    (hglb : GluelessProv state.resources.sbelt)
    (hrf : RespPackFacts resp state.now) :
    CachePackNC state''.resources.cache state.now
    ∧ state''.resources.cache.records.size ≤ DnsCache.capacity
    ∧ state''.now = state.now
    ∧ GluelessProv state''.resources.slist
    ∧ state''.resources.sbelt = state.resources.sbelt
    ∧ ((∃ qn, αName state.resources.sname = some qn) →
        ∃ qn', αName state''.resources.sname = some qn')
    ∧ state''.lastQuery = state.lastQuery := by
  unfold Server.afterResume at heq
  split at heq
  · exact absurd heq (by simp)
  case _ st' hres =>
    obtain rfl : Server.boundStateCache
        (Server.roundTouches (Server.dropIfBizarre state entryName resp) resp) st' = state'' :=
      Server.IoStep.continue.inj heq
    obtain ⟨hdc, hdn, hdb, hdsn, hdlr, hdlq⟩ := dropIfBizarre_fields state entryName resp
    have hres' : Resolver.resolve.loop (S := DnsSList) (C := DnsCache)
        (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        { Server.dropIfBizarre state entryName resp with lastResponse := some resp } 64
        = .ok (.paused st') := hres
    obtain ⟨hpL, hnowL, hglL, hsbL, hsnL, hlqL⟩ :=
      resolveLoop_paused_carry 64 _ st' hres'
        (by show CachePackNC (Server.dropIfBizarre state entryName resp).resources.cache
              (Server.dropIfBizarre state entryName resp).now
            rw [hdc, hdn]; exact hp)
        (by exact dropIfBizarre_glProv state entryName resp hgl)
        (by show GluelessProv (Server.dropIfBizarre state entryName resp).resources.sbelt
            rw [hdb]; exact hglb)
        (by intro r hr
            obtain rfl : resp = r := Option.some.inj hr
            show RespPackFacts resp (Server.dropIfBizarre state entryName resp).now
            rw [hdn]; exact hrf)
    have hpL' : CachePackNC st'.resources.cache state.now :=
      hdn ▸ (show CachePackNC st'.resources.cache
        (Server.dropIfBizarre state entryName resp).now from hpL)
    have hnowL' : st'.now = state.now :=
      (show st'.now = (Server.dropIfBizarre state entryName resp).now from hnowL).trans hdn
    have hsbL' : st'.resources.sbelt = state.resources.sbelt :=
      (show st'.resources.sbelt
        = (Server.dropIfBizarre state entryName resp).resources.sbelt from hsbL).trans hdb
    obtain ⟨hpB, hcapB⟩ := cachePackNC_boundLru
      (Server.roundTouches (Server.dropIfBizarre state entryName resp) resp) st'.now hpL'
    refine ⟨hpB, hcapB, hnowL', hglL, hsbL', ?_, ?_⟩
    · intro hs
      refine hsnL ?_
      show ∃ qn, αName (Server.dropIfBizarre state entryName resp).resources.sname = some qn
      rw [hdsn]
      exact hs
    · show st'.lastQuery = state.lastQuery
      exact (show st'.lastQuery
          = (Server.dropIfBizarre state entryName resp).lastQuery from hlqL).trans hdlq
  · exact absurd heq (by simp)


theorem sectionWriteWf_of_wire {resp0 respS : VeriDNS.Spec.Format} {sect : Array ByteArray}
    {now : UInt32}
    (hsani : Server.sanitizeTtlsCap resp0 = some respS)
    (hclock : now.toNat + 604800 < 2 ^ 32)
    (hsel : ∀ b ∈ sect.toList, (b ∈ respS.answer ∨ b ∈ respS.authority) ∨ b ∈ respS.additional)
    (hvalid : ∀ b ∈ sect.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ αRR rr ≠ none)
    (hcanon : ∀ raw ∈ sect.toList, VeriDNS.Proof.Message.CanonicalRR raw) :
    AnswerWriteWf sect now := by
  intro raw hraw rr hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨rr', hpr', hα'⟩ := hvalid raw hraw
    rw [hpr'] at hp
    injection hp with h
    subst h
    cases hα : αRR rr' with
    | none => exact absurd hα hα'
    | some r => rfl
  · have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani raw
      (hsel raw hraw) rr hp
    exact uint32_add_ttl_toNat now rr.ttl.toNat httl hclock
  · intro htype
    exact canonicalRR_nsRdata_canonical (hcanon raw hraw) hp htype
  · intro htype
    exact canonicalRR_cnameRdata_canonical (hcanon raw hraw) hp htype

theorem respPackFacts_of_wire {resp0 respS respA : VeriDNS.Spec.Format} {now : UInt32}
    {bytes : ByteArray}
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some respS)
    (hAeq : respA = respS)
    (hclock : now.toNat + 604800 < 2 ^ 32)
    (hvalAns : ∀ b ∈ respA.answer.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ αRR rr ≠ none)
    (hvalAuth : ∀ b ∈ respA.authority.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ αRR rr ≠ none)
    (hvalAdd : (αResp respA).isReferral = true →
      ∀ b ∈ respA.additional.toList, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
          ∧ αRR rr ≠ none) :
    RespPackFacts respA now := by
  have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
    unfold Server.sanitizeTtlsCap at hsani
    exact (Option.some.inj hsani).symm
  have hcapAns : respA.answer = resp0.answer.map Server.capTtlRR := by
    rw [hAeq, hcapEq]; rfl
  have hcapAuth : respA.authority = resp0.authority.map Server.capTtlRR := by
    rw [hAeq, hcapEq]; rfl
  have hcapAdd : respA.additional
      = (resp0.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by
    rw [hAeq, hcapEq]; rfl
  have hcanonAns : ∀ raw ∈ respA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
    intro raw hmem
    rw [hcapAns, Array.toList_map, List.mem_map] at hmem
    obtain ⟨b0, hb0, rfl⟩ := hmem
    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
      (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
  have hcanonAuth : ∀ raw ∈ respA.authority.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
    intro raw hmem
    rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
    obtain ⟨b0, hb0, rfl⟩ := hmem
    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
      (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
  have hcanonAdd : ∀ raw ∈ respA.additional.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
    intro raw hmem
    rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
    obtain ⟨b0, hb0, rfl⟩ := hmem
    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
      (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0
        (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
  refine ⟨?_, ?_, hvalAuth, ?_, hcanonAuth⟩
  · exact sectionWriteWf_of_wire hsani hclock
      (fun b hb => Or.inl (Or.inl (by rw [← hAeq]; exact Array.mem_def.mpr hb)))
      hvalAns hcanonAns
  · exact sectionWriteWf_of_wire hsani hclock
      (fun b hb => Or.inl (Or.inr (by rw [← hAeq]; exact Array.mem_def.mpr hb)))
      hvalAuth hcanonAuth
  · intro hir
    exact sectionWriteWf_of_wire hsani hclock
      (fun b hb => Or.inr (by rw [← hAeq]; exact Array.mem_def.mpr hb))
      (hvalAdd hir) hcanonAdd


theorem αQuery_buildSubQuery_exists
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {sub : VeriDNS.Spec.Format} {revealed : Nat}
    (hbuild : Resolver.buildSubQuery state revealed = some sub)
    (hsnA : ∃ qn, αName state.resources.sname = some qn)
    (hqmA : ∀ qu : VeriDNS.Spec.Question,
      (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
      (αQType qu.qtype).isSome ∧ (αClass qu.qclass).isSome) :
    ∃ qm, αQuery sub = some qm := by
  obtain ⟨qF, qu, hlq, hqu, hsub⟩ := buildSubQuery_inv state sub revealed hbuild
  obtain ⟨qn, hqn⟩ := hsnA
  obtain ⟨hqtS, hqcS⟩ := hqmA qu ⟨qF, hlq, hqu⟩
  obtain ⟨qt, hqt⟩ := Option.isSome_iff_exists.mp hqtS
  obtain ⟨qc, hqc⟩ := Option.isSome_iff_exists.mp hqcS
  have hq0 : sub.question[0]? = some (Resolver.subQuestion state.resources.sname revealed qu) := by
    rw [hsub]; rfl
  unfold αQuery
  rw [hq0]
  unfold Resolver.subQuestion
  by_cases hpr : Resolver.probeRoundB state.resources.sname revealed = true
  · rw [if_pos hpr]
    dsimp only []
    rw [VeriDNS.Proof.QnameMin.αName_minimisedName hqn revealed, hqc]
    exact ⟨_, rfl⟩
  · rw [if_neg hpr]
    dsimp only []
    rw [hqn, hqt, hqc]
    exact ⟨_, rfl⟩


set_option maxHeartbeats 4000000 in
theorem ioResumeLoop_error_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (deadline : UInt32) (hnetWF : net.WF)
    (hGlSbelt : GluelessProv sbelt) :
    ∀ (n : Nat) (depth fuel' revealed : Nat)
      (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      (w w' : World) (now : Net.Time) (msg : String) (cout : DnsCache),
      WorldModels net ns ra ednsBuf now w →
      WorldModelsTcp net ns ra ednsBuf now w →
      αTime state.now = now →
      CachePackNC state.resources.cache state.now →
      state.resources.cache.records.size ≤ DnsCache.capacity →
      state.now.toNat + 604800 < 2 ^ 32 →
      GluelessProv state.resources.slist →
      GluelessProv state.resources.sbelt →
      (∃ qn, αName state.resources.sname = some qn) →
      (∀ qu : VeriDNS.Spec.Question,
        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
        (αQType qu.qtype).isSome ∧ (αClass qu.qclass).isSome) →
      Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth
          fuel' revealed) w
        = some ((.error msg, cout), w') →
      CachePackNC cout state.now ∧ cout.records.size ≤ DnsCache.capacity := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro depth fuel' revealed state w w' now msg cout hwm hwmTcp htm hp hCap hclock hGlProv hGlBelt
      hsnA hqmA hrun
    obtain _ | f := fuel'
    · rw [run_ioResumeLoop_fuel_zero] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨⟨-, rfl⟩, -⟩ := hrun
      exact ⟨hp, hCap⟩
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
          exact ⟨hp, hCap⟩
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
              exact ⟨hp, hCap⟩
            | some nsName =>
              cases hd : depth with
              | zero =>
                rw [hd] at hrun
                simp only [hat, run_pure'] at hrun
                simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨⟨-, rfl⟩, -⟩ := hrun
                exact ⟨hp, hCap⟩
              | succ depth' =>
                rw [hd] at hrun
                simp only [hat] at hrun
                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
                    VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _
                    (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache with
                | ok y =>
                  cases y with
                  | done subResp =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                        state.resources.slist nsName (Except.ok subResp)) >>= fun slist' =>
                        Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                          { state with resources := { state.resources with slist := slist' } }
                          deadline depth' f revealed) _
                        = some ((Except.error msg, cout), w') := hrun
                    cases hA : Server.extractAAddress nsName subResp.answer with
                    | some addr =>
                      unfold Server.gluelessUpdatedSlist at hrun'
                      simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrun'
                      rw [← Prog.bind_def] at hrun'
                      obtain ⟨m2, hm2, hrun'⟩ := run_log_bind_inv _ _ _ hrun'
                      exact IH m2 (by omega) depth' f revealed
                        { state with resources := { state.resources with
                            slist := state.resources.slist.addAddress nsName addr } }
                        _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                        (by exact hCap) (by exact hclock)
                        (by exact GluelessProv_addAddress nsName addr hGlProv)
                        (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun'
                    | none =>
                      unfold Server.gluelessUpdatedSlist at hrun'
                      simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrun'
                      rw [← Prog.bind_def] at hrun'
                      obtain ⟨m2, hm2, hrun'⟩ := run_log_bind_inv _ _ _ hrun'
                      exact IH m2 (by omega) depth' f revealed
                        { state with resources := { state.resources with
                            slist := state.resources.slist.removeServer nsName } }
                        _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                        (by exact hCap) (by exact hclock)
                        (by exact GluelessProv_removeServer nsName hGlProv)
                        (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun'
                  | paused st =>
                    rw [hres] at hrun
                    obtain ⟨mI, mK, p, w2, hfuelIK, hrunI, hrunK⟩ := run_bind_inv hrun
                    obtain ⟨subResult, subCache⟩ := p
                    dsimp only [] at hrunK
                    obtain ⟨horacle2, -, -⟩ := run_world_frame hrunI
                    have htcpO2 := run_world_tcpOracle_frame hrunI
                    cases subResult with
                    | error e =>
                      unfold Server.gluelessUpdatedSlist at hrunK
                      simp only [Prog.bind_def, Prog.bind_assoc] at hrunK
                      rw [← Prog.bind_def] at hrunK
                      obtain ⟨m2, hm2, hrunK⟩ := run_log_bind_inv _ _ _ hrunK
                      exact IH m2 (by omega) depth' f revealed
                        { state with resources := { state.resources with
                            slist := state.resources.slist.removeServer nsName } }
                        _ w' now msg cout
                        (WorldModels_oracle net ns ra ednsBuf now (by exact horacle2) hwm)
                        (by exact WorldModelsTcp_tcpOracle net ns ra ednsBuf now htcpO2 hwmTcp)
                        (by exact htm) (by exact hp) (by exact hCap) (by exact hclock)
                        (by exact GluelessProv_removeServer nsName hGlProv)
                        (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrunK
                    | ok subResp =>
                      cases hA : Server.extractAAddress nsName subResp.answer with
                      | none =>
                        unfold Server.gluelessUpdatedSlist at hrunK
                        simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrunK
                        rw [← Prog.bind_def] at hrunK
                        obtain ⟨m2, hm2, hrunK⟩ := run_log_bind_inv _ _ _ hrunK
                        exact IH m2 (by omega) depth' f revealed
                          { state with resources := { state.resources with
                              slist := state.resources.slist.removeServer nsName } }
                          _ w' now msg cout
                          (WorldModels_oracle net ns ra ednsBuf now (by exact horacle2) hwm)
                          (by exact WorldModelsTcp_tcpOracle net ns ra ednsBuf now htcpO2 hwmTcp)
                          (by exact htm) (by exact hp) (by exact hCap) (by exact hclock)
                          (by exact GluelessProv_removeServer nsName hGlProv)
                          (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrunK
                      | some addr =>
                        unfold Server.gluelessUpdatedSlist at hrunK
                        simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrunK
                        rw [← Prog.bind_def] at hrunK
                        obtain ⟨m2, hm2, hrunK⟩ := run_log_bind_inv _ _ _ hrunK
                        have hrunK' : Prog.run m2
                            (match Server.gluelessRecheck state subCache with
                            | some hit =>
                              (pure (.ok hit,
                                  subCache.touchKeys (Server.recheckTouches state) state.now) :
                                Prog (Except String VeriDNS.Spec.Format × DnsCache))
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.addAddress nsName addr,
                                    cache := subCache.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed) _
                            = some ((Except.error msg, cout), w') := hrunK
                        clear hrunK
                        cases hgr : Server.gluelessRecheck state subCache with
                        | some hit =>
                          simp only [hgr, run_pure'] at hrunK'
                          exact absurd hrunK' (by simp)
                        | none =>
                          simp only [hgr] at hrunK'
                          have hnsMem : nsName ∈ state.resources.slist.addressTargets.toList := by
                            obtain ⟨h0, heq0⟩ := Array.getElem?_eq_some_iff.mp hat
                            exact heq0 ▸ Array.mem_def.mp (Array.getElem_mem h0)
                          obtain ⟨nsQ, hαns, hcanNs, hlenNs⟩ := hGlProv nsName hnsMem
                          have hvalNs : ∀ x ∈ nsQ, x.size ≤ 63 :=
                            fun x hx => (αName_valid hαns x hx).2
                          obtain ⟨sname', chain', hlaS, hstCache, hstSname, hstNow, hstChain,
                            hstStep, hstLq, hstSbelt, hstSlist⟩ :=
                            resolve_mkAddressQuery_paused_inv nsName sbelt state.now
                              state.resources.cache st nsQ hαns hcanNs hres
                          have hnegwfMain : CacheNegWf state.resources.cache (1 : BitVec 16) :=
                            hp.2.2.2.2.1
                          have hpeelS := localAnswer_chase_peel net ns ra ednsBuf rttOf
                            state.resources.cache (αCache state.resources.cache)
                            (1 : BitVec 16) (1 : BitVec 16) state.now
                            ⟨nsQ, QType.rr RRType.a, RRClass.in, false⟩ RRType.a [] nsName
                            rfl rfl (by intro h; cases h) rfl (MatchMaxEquiv.refl _)
                            hp.1 hp.2.2.1 hp.2.2.2.1
                            hnegwfMain 8 nsName nsQ #[]
                            (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                              nsName #[])
                            [] (.miss sname' chain') hlaS hαns hcanNs hvalNs hlenNs rfl
                            (by
                              intro nm hnm
                              rcases List.mem_cons.mp hnm with rfl | hnm'
                              · exact ⟨nsName, by simp [Resolver.cnameChaseVisited], hαns,
                                  hcanNs, hvalNs⟩
                              · exact absurd hnm' (List.not_mem_nil))
                          obtain ⟨linksS, nF, nseenF, hchainS, hnF, hnFcan, hnFval, hlenF, hvisF,
                            hmissF, hnmissF, hlinksCn, -⟩ := hpeelS
                          obtain ⟨slistSub, vSub, coutMSub, hVsub, -, hrcSub, hansSub, hcrSub, hwm2,
                            hwfS, hnsS, hcnS, hwfrrS, hnegS, hnsdS, hoeS, hcapS, hawSub⟩ :=
                            ioResumeLoop_sound net ns ra ednsBuf rttOf sbelt deadline hnetWF hGlSbelt
                              mI ⟨nF, QType.rr RRType.a, RRClass.in, false⟩ depth' f
                              (Server.seedRevealed st) st
                              (αCache state.resources.cache) _ w2 now nseenF []
                              st.resources.slist.matchCount subResp subCache
                              (by
                                refine ⟨?_, ?_, ?_, hwm⟩
                                · rw [hstCache]; exact MatchMaxEquiv.refl _
                                · rw [hstSname]; exact hnF
                                · rw [hstNow]; exact htm)
                              (by exact hwmTcp)
                              (by rw [hstCache, hstNow]; exact hp.1)
                              (by rw [hstCache]; exact hp.2.1)
                              (by rw [hstCache]; exact hp.2.2.1)
                              (by rw [hstCache]; exact hp.2.2.2.1)
                              (by
                                intro qu2 hqu2
                                obtain ⟨q02, hq02, hqu02⟩ := hqu2
                                rw [hstLq] at hq02
                                obtain rfl := Option.some.inj hq02
                                rw [mkAddressQuery_question] at hqu02
                                obtain rfl := Option.some.inj hqu02
                                rw [hstCache]
                                exact hnegwfMain)
                              (by rw [hstCache]; exact hp.2.2.2.2.2.1)
                              (by rw [hstCache]; exact hp.2.2.2.2.2.2)
                              (by rw [hstCache]; exact hCap)
                              (by rw [← htm]; exact hmissF)
                              (by rw [← htm]; exact hnmissF)
                              (by intro b hb; exact absurd hb (List.not_mem_nil))
                              rfl
                              (by
                                rcases hstSlist with h | ⟨nsNames, mcW, hwalk, heq⟩ | h
                                · rw [h]; exact GluelessProv_default
                                · rw [heq]
                                  exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                    (walkNs_names_canonical _ state.now hp.2.1 128 sname'
                                      nsNames mcW (by exact hwalk))
                                · rw [h]; exact hGlSbelt)
                              (by rw [hstSbelt]; exact hGlSbelt)
                              (by
                                intro qu2 hqu2
                                obtain ⟨q02, hq02, hqu02⟩ := hqu2
                                rw [hstLq] at hq02
                                obtain rfl := Option.some.inj hq02
                                rw [mkAddressQuery_question] at hqu02
                                obtain rfl := Option.some.inj hqu02
                                exact ⟨rfl, rfl⟩)
                              rfl
                              (by intro h; cases h)
                              rfl
                              (by rw [hstNow]; exact hclock)
                              (by rw [hstSname]; exact hnFcan)
                              hlenF
                              (fun x hx => αName_labels_valid hnF x hx)
                              (by
                                unfold CnameChainModels
                                have hanch : ((st.lastQuery.bind
                                    (fun q0 => q0.question[0]?)).elim st.resources.sname
                                      (fun qu => qu.qname)) = nsName := by
                                  rw [hstLq]
                                  rfl
                                rw [hanch, hstChain]
                                exact hvisF)
                              (by
                                rw [hstChain, hstNow]
                                exact localAnswer_chain_answerWriteWf hp.1 hp.2.1 hp.2.2.1
                                  hp.2.2.2.1 (congrArg chainOf hlaS) (answerWriteWf_empty _))
                              hstStep hrunI
                          rw [hstNow] at hwfS
                          have hnegSub1 : CacheNegWf subCache (1 : BitVec 16) :=
                            hnegS ⟨nsName, 1, 1⟩ ⟨Server.mkAddressQuery nsName, hstLq, rfl⟩
                          have hpSub : CachePackNC subCache state.now :=
                            ⟨hwfS, hnsS, hcnS, hwfrrS, hnegSub1, hnsdS, hoeS⟩
                          have hpSubT : CachePackNC
                              (subCache.touchKeys (Server.recheckTouches state) state.now)
                              state.now :=
                            cachePackNC_touchKeys _ _ hpSub
                          have hcapT : (subCache.touchKeys (Server.recheckTouches state)
                              state.now).records.size ≤ DnsCache.capacity := by
                            rw [VeriDNS.Impl.Cache.touchKeys_records, Array.size_map]
                            exact hcapS
                          exact IH m2 (by omega) depth' f revealed
                            { state with resources := { state.resources with
                                slist := state.resources.slist.addAddress nsName addr,
                                cache := subCache.touchKeys (Server.recheckTouches state)
                                  state.now } }
                            _ w' now msg cout
                            (WorldModels_oracle net ns ra ednsBuf now (by exact horacle2) hwm)
                            (by exact WorldModelsTcp_tcpOracle net ns ra ednsBuf now htcpO2 hwmTcp)
                            (by exact htm) (by exact hpSubT) (by exact hcapT) (by exact hclock)
                            (by exact GluelessProv_addAddress nsName addr hGlProv)
                            (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrunK'
                | error e =>
                  rw [hres] at hrun
                  have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                      state.resources.slist nsName (Except.error e)) >>= fun slist' =>
                      Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                        { state with resources := { state.resources with slist := slist' } }
                        deadline depth' f revealed) _
                      = some ((Except.error msg, cout), w') := hrun
                  unfold Server.gluelessUpdatedSlist at hrun'
                  simp only [Prog.bind_def, Prog.bind_assoc] at hrun'
                  rw [← Prog.bind_def] at hrun'
                  obtain ⟨m2, hm2, hrun'⟩ := run_log_bind_inv _ _ _ hrun'
                  exact IH m2 (by omega) depth' f revealed
                    { state with resources := { state.resources with
                        slist := state.resources.slist.removeServer nsName } }
                    _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                    (by exact hCap) (by exact hclock)
                    (by exact GluelessProv_removeServer nsName hGlProv)
                    (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun'
          | some entryIp =>
            obtain ⟨entry, ipAddr⟩ := entryIp
            rw [hbest] at hrun
            cases hbuild : Resolver.buildSubQuery state revealed with
            | none =>
              simp only [hbuild, run_pure'] at hrun
              simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨⟨-, rfl⟩, -⟩ := hrun
              exact ⟨hp, hCap⟩
            | some subQuery0 =>
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
                  exact IH m' (by omega) depth f
                    (Server.fallbackRevealed state.resources.sname revealed)
                    { state with resources := { state.resources with
                        slist := state.resources.slist.markQueried entry.name } }
                    _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                    (by exact hCap) (by exact hclock)
                    (by exact GluelessProv_markQueried entry.name hGlProv)
                    (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
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
                      (Server.withSecrets subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
                      (Server.ipv4ToAddr ipAddr) with
                  | none =>
                    rw [run_round_bind_eq_none _ _ _ _ _ hO] at hrun
                    simp only [] at hrun
                    exact IH m' (by omega) depth f
                      (Server.fallbackRevealed state.resources.sname revealed)
                      { state with resources := { state.resources with
                          slist := state.resources.slist.markQueried entry.name } }
                      _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                      (by exact hCap) (by exact hclock)
                      (by exact GluelessProv_markQueried entry.name hGlProv)
                      (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                  | some d =>
                    cases ha : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d with
                    | none =>
                      rw [run_round_bind_eq_acceptNone _ _ _ _ _ d hO ha] at hrun
                      simp only [] at hrun
                      exact IH m' (by omega) depth f
                        (Server.fallbackRevealed state.resources.sname revealed)
                        { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } }
                        _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                        (by exact hCap) (by exact hclock)
                        (by exact GluelessProv_markQueried entry.name hGlProv)
                        (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                    | some bytes =>
                      cases hdec : VeriDNS.Impl.Message.decode bytes with
                      | error errmsg =>
                        rw [run_round_bind_eq_decodeError _ _ _ _ _ d bytes errmsg hO ha hdec] at hrun
                        simp only [] at hrun
                        exact IH m' (by omega) depth f
                          (Server.fallbackRevealed state.resources.sname revealed)
                          { state with resources := { state.resources with
                              slist := state.resources.slist.markQueried entry.name } }
                          _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                          (by exact hCap) (by exact hclock)
                          (by exact GluelessProv_markQueried entry.name hGlProv)
                          (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                      | ok resp0 =>
                        rw [run_round_bind_eq _ _ _ _ _ d bytes resp0 hO ha hdec] at hrun
                        cases hsani : Server.sanitizeTtlsCap resp0 with
                        | none =>
                          simp only [hsani] at hrun
                          exact IH m' (by omega) depth f
                            (Server.fallbackRevealed state.resources.sname revealed)
                            { state with resources := { state.resources with
                                slist := state.resources.slist.markQueried entry.name } }
                            _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                            (by exact hCap) (by exact hclock)
                            (by exact GluelessProv_markQueried entry.name hGlProv)
                            (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                        | some respS =>
                          simp only [hsani] at hrun
                          cases haccR : Server.acceptResponse
                              (Server.withSecrets subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
                              respS with
                          | none =>
                            simp only [haccR] at hrun
                            obtain ⟨mr, hmr, hrun⟩ := run_log_bind_inv _ _ _ hrun
                            exact IH mr (by omega) depth f revealed
                              { state with resources := { state.resources with
                                  slist := state.resources.slist.markQueried entry.name } }
                              _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                              (by exact hCap) (by exact hclock)
                              (by exact GluelessProv_markQueried entry.name hGlProv)
                              (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                          | some respA =>
                            simp only [haccR] at hrun
                            obtain ⟨ml, hml, hrun⟩ := run_log_bind_inv _ _ _ hrun
                            by_cases htcT : (respA.header.tc == 1) = true
                            case pos =>
                              rw [if_pos htcT] at hrun
                              rcases run_tcpFallbackGuard_inv _ _ _ _ _ hrun with
                                ⟨mF, hmF, hrun⟩ |
                                ⟨mD, bytes2, raw2, tcpResp, tcpRespA, hmD, hOr, hdec2, hsan2, hacc2, _, hrun⟩
                              · dsimp only [] at hrun
                                obtain ⟨mFl, hmFl, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH mFl (by omega) depth f revealed
                                  { state with resources := { state.resources with
                                      slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                  _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                  (by exact hCap) (by exact hclock)
                                  (by exact GluelessProv_removeServer entry.name (GluelessProv_markQueried entry.name hGlProv))
                                  (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                              · dsimp only [] at hrun
                                by_cases hunf : Server.unfollowableDelegationB
                                    (state.resources.slist.markQueried entry.name)
                                    state.resources.sname tcpRespA = true
                                · simp only [hunf, if_true] at hrun
                                  obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH mu (by omega) depth f revealed
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                    (by exact hCap) (by exact hclock)
                                    (by exact GluelessProv_markQueried entry.name hGlProv)
                                    (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                                · rw [if_neg hunf] at hrun
                                  by_cases hfeT : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                      && !state.noEdns) = true
                                  case pos =>
                                    -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                                    rw [if_pos hfeT] at hrun
                                    obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                    exact IH mf (by omega) depth f revealed
                                      { state with
                                        resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name },
                                        noEdns := true }
                                      _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                      (by exact hCap) (by exact hclock)
                                      (by exact GluelessProv_markQueried entry.name hGlProv)
                                      (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                                  rw [if_neg hfeT] at hrun
                                  by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                      && Server.strictDenialB tcpRespA) = true
                                  case pos =>
                                    -- 051/064: the minimised-probe NXDOMAIN arm now recurses (full-qname
                                    -- fallback, RFC 9156 §2.3) instead of delivering.
                                    rw [if_pos hstT] at hrun
                                    obtain ⟨ms, hms, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                    exact IH ms (by omega) depth f
                                      (VeriDNS.Impl.DomainName.labelCount state.resources.sname)
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                      (by exact hCap) (by exact hclock)
                                      (by exact GluelessProv_markQueried entry.name hGlProv)
                                      (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                                  case neg =>
                                    rw [if_neg hstT] at hrun
                                    by_cases hpgT : (Resolver.probeRoundB state.resources.sname revealed
                                        && !Server.probePassableB tcpRespA) = true
                                    · rw [if_pos hpgT] at hrun
                                      obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                      exact IH mp (by omega) depth f
                                        (Resolver.bumpRevealed state.resources.sname revealed)
                                        { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                        _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                        (by exact hCap) (by exact hclock)
                                        (by exact GluelessProv_markQueried entry.name hGlProv)
                                        (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                                    · rw [if_neg hpgT] at hrun
                                      split at hrun
                                      · rename_i result cacheR hAR
                                        rw [run_pure'] at hrun
                                        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                                        obtain ⟨⟨hres, hcoutEq⟩, hwEq⟩ := hrun
                                        subst hres
                                        subst hcoutEq
                                        rw [afterResume_error_cache hAR]
                                        exact ⟨hp, hCap⟩
                                      · rename_i state'' heqC
                                        obtain ⟨qmS, hαQ⟩ := αQuery_buildSubQuery_exists hbuild hsnA hqmA
                                        have hwmTcpApp := hwmTcp subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1))
                                          (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA qmS
                                          hOr hdec2 hsan2 hacc2 hαQ
                                        obtain ⟨_, _, _, -, -, -, -, -, -, -, hVA, hVU,
                                          -, -, -, -, -, -, haddVal, -⟩ := hwmTcpApp
                                        have hrf : RespPackFacts tcpRespA state.now :=
                                          respPackFacts_of_wire hdec2 hsan2 (acceptResponse_some_eq hacc2)
                                            hclock hVA hVU (fun _ => haddVal)
                                        obtain ⟨hpC, hcapC, hnowC, hglC, hsbC, hsnC, hlqC⟩ :=
                                          afterResume_continue_carry heqC (by exact hp)
                                            (by exact GluelessProv_markQueried entry.name hGlProv)
                                            (by exact hGlBelt) (by exact hrf)
                                        exact (by
                                          obtain ⟨hpO, hcapO⟩ := IH mD (by omega) depth f
                                            (Server.revealedAfterContinue state.resources.sname revealed state'')
                                            state'' _ w' now msg cout
                                            (by exact hwm)
                                            (by exact hwmTcp)
                                            (by rw [show state''.now = state.now from hnowC]; exact htm)
                                            (by rw [show state''.now = state.now from hnowC]; exact hpC)
                                            (by exact hcapC)
                                            (by rw [show state''.now = state.now from hnowC]; exact hclock)
                                            (by exact hglC)
                                            (by rw [hsbC]; exact hGlBelt)
                                            (by exact hsnC hsnA)
                                            (by rw [hlqC]; exact hqmA) hrun
                                          rw [show state''.now = state.now from hnowC] at hpO
                                          exact ⟨hpO, hcapO⟩)
                            rw [if_neg htcT, run_bind_pureSome] at hrun
                            dsimp only [] at hrun
                            by_cases hunf : Server.unfollowableDelegationB
                                (state.resources.slist.markQueried entry.name)
                                state.resources.sname respA = true
                            · simp only [hunf, if_true] at hrun
                              obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              exact IH mu (by omega) depth f revealed
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                (by exact hCap) (by exact hclock)
                                (by exact GluelessProv_markQueried entry.name hGlProv)
                                (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                            · rw [if_neg hunf] at hrun
                              by_cases hfeT : (respA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                  && !state.noEdns) = true
                              case pos =>
                                -- 055: FORMERR → retry without EDNS (noEdns flag), IH recursion.
                                rw [if_pos hfeT] at hrun
                                obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH mf (by omega) depth f revealed
                                  { state with
                                    resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name },
                                    noEdns := true }
                                  _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                  (by exact hCap) (by exact hclock)
                                  (by exact GluelessProv_markQueried entry.name hGlProv)
                                  (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                              rw [if_neg hfeT] at hrun
                              by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                  && Server.strictDenialB respA) = true
                              case pos =>
                                -- 051/064: the minimised-probe NXDOMAIN arm now recurses (full-qname
                                -- fallback, RFC 9156 §2.3) instead of delivering.
                                rw [if_pos hstT] at hrun
                                obtain ⟨ms, hms, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                exact IH ms (by omega) depth f
                                  (VeriDNS.Impl.DomainName.labelCount state.resources.sname)
                                  { state with resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name } }
                                  _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                  (by exact hCap) (by exact hclock)
                                  (by exact GluelessProv_markQueried entry.name hGlProv)
                                  (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                              case neg =>
                                rw [if_neg hstT] at hrun
                                by_cases hpgT : (Resolver.probeRoundB state.resources.sname revealed
                                    && !Server.probePassableB respA) = true
                                · rw [if_pos hpgT] at hrun
                                  obtain ⟨mp, hmp, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  exact IH mp (by omega) depth f
                                    (Resolver.bumpRevealed state.resources.sname revealed)
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    _ w' now msg cout (by exact hwm) (by exact hwmTcp) (by exact htm) (by exact hp)
                                    (by exact hCap) (by exact hclock)
                                    (by exact GluelessProv_markQueried entry.name hGlProv)
                                    (by exact hGlBelt) (by exact hsnA) (by exact hqmA) hrun
                                · rw [if_neg hpgT] at hrun
                                  split at hrun
                                  · rename_i result cacheR hAR
                                    rw [run_pure'] at hrun
                                    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                                    obtain ⟨⟨hres, hcoutEq⟩, hwEq⟩ := hrun
                                    subst hres
                                    subst hcoutEq
                                    rw [afterResume_error_cache hAR]
                                    exact ⟨hp, hCap⟩
                                  · rename_i state'' heqC
                                    obtain ⟨qmS, hαQ⟩ := αQuery_buildSubQuery_exists hbuild hsnA hqmA
                                    have hwmApp := hwm subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1))
                                      (Server.ipv4ToAddr ipAddr) d bytes resp0 respS respA qmS
                                      hO ha hdec hsani haccR hαQ
                                    have hVA : ∀ b ∈ respA.answer.toList, ∃ rr,
                                        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                          ∧ αRR rr ≠ none := by
                                      rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, hvalid, -⟩ |
                                        ⟨_, _, _, -, -, -, -, -, -, hvld, -⟩
                                      · exact hvalid
                                      · exact hvld
                                    have hVU : ∀ b ∈ respA.authority.toList, ∃ rr,
                                        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                          ∧ αRR rr ≠ none := by
                                      rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, -, hvalidAuth, -⟩ |
                                        ⟨_, _, _, -, -, -, -, -, -, -, hvldA, -⟩
                                      · exact hvalidAuth
                                      · exact hvldA
                                    have hVD : (αResp respA).isReferral = true →
                                        ∀ b ∈ respA.additional.toList, ∃ rr,
                                          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                            ∧ αRR rr ≠ none := by
                                      intro hir
                                      rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, hnstail⟩ |
                                        ⟨_, reply, _, -, -, -, hclsLink, -, -, -, -, hrefImpl⟩
                                      · exact hnstail.2.2.2.2.2.1
                                      · have href : reply.msg.isReferral = true := hclsLink.symm.trans hir
                                        obtain ⟨-, -, -, haddWf, -, -, -⟩ := hrefImpl href
                                        exact haddWf
                                    have hrf : RespPackFacts respA state.now :=
                                      respPackFacts_of_wire hdec hsani (acceptResponse_some_eq haccR)
                                        hclock hVA hVU hVD
                                    obtain ⟨hpC, hcapC, hnowC, hglC, hsbC, hsnC, hlqC⟩ :=
                                      afterResume_continue_carry heqC (by exact hp)
                                        (by exact GluelessProv_markQueried entry.name hGlProv)
                                        (by exact hGlBelt) (by exact hrf)
                                    exact (by
                                      obtain ⟨hpO, hcapO⟩ := IH ml (by omega) depth f
                                        (Server.revealedAfterContinue state.resources.sname revealed state'')
                                        state'' _ w' now msg cout
                                        (by exact hwm)
                                        (by exact hwmTcp)
                                        (by rw [show state''.now = state.now from hnowC]; exact htm)
                                        (by rw [show state''.now = state.now from hnowC]; exact hpC)
                                        (by exact hcapC)
                                        (by rw [show state''.now = state.now from hnowC]; exact hclock)
                                        (by exact hglC)
                                        (by rw [hsbC]; exact hGlBelt)
                                        (by exact hsnC hsnA)
                                        (by rw [hlqC]; exact hqmA) hrun
                                      rw [show state''.now = state.now from hnowC] at hpO
                                      exact ⟨hpO, hcapO⟩)
