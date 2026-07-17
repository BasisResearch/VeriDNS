import VeriDNS.Proof.Refinement
import VeriDNS.Proof.MessageValid



namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (Trustworthiness RRType RRClass)
open VeriDNS.Impl
open VeriDNS.Spec.Net (Time)

theorem αType_ns_toNat {t : BitVec 16} (h : αType t = some RRType.ns) : t.toNat = 2 := by
  unfold αType at h
  split at h <;> simp_all
theorem rcode_ne_nameError_of_αRCode_noError {rc : VeriDNS.Spec.Rcode}
    (h : (αRCode rc == VeriDNS.Spec.Net.RCode.noError) = true) :
    (rc == VeriDNS.Spec.Rcode.nameError) = false := by
  cases rc <;> first | rfl | exact absurd h (by simp only [αRCode]; decide)
theorem αSection_ne_nil {rrs : Array ByteArray} (hne : rrs.toList ≠ [])
    (hg : ∀ b ∈ rrs.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) :
    αSection rrs ≠ [] := by
  unfold αSection
  match hl : rrs.toList with
  | [] => exact absurd hl hne
  | a :: as =>
    obtain ⟨rr, hpr, har⟩ := hg a (hl ▸ List.mem_cons_self)
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp har
    simp only [List.filterMap_cons, hpr, hr]
    exact List.cons_ne_nil _ _
theorem αSection_nil_imp {rrs : Array ByteArray}
    (hg : ∀ b ∈ rrs.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
    (h : αSection rrs = []) : rrs.toList = [] := by
  by_contra hne
  exact αSection_ne_nil hne hg h
theorem αQType_covers {bv : BitVec 16} {qtq : VeriDNS.Spec.Net.QType} {qt : RRType}
    (hq : αQType bv = some qtq) (ht : αType bv = some qt) : qtq.covers qt = true := by
  unfold αQType at hq
  split at hq
  ·
    obtain rfl := Option.some.inj hq
    rfl
  · rw [ht] at hq
    simp only [Option.map_some] at hq
    injection hq with hq
    subst hq
    simp only [VeriDNS.Spec.Net.QType.covers]
    exact VeriDNS.Proof.Refinement.rrtype_beq_self qt
theorem αType_of_αQType_rr {bv : BitVec 16} {t : RRType}
    (h : αQType bv = some (VeriDNS.Spec.Net.QType.rr t)) : αType bv = some t := by
  unfold αQType at h
  split at h
  · exact absurd h (by simp)
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hrr⟩ := h
    injection hrr with hrr; subst hrr; exact ha
theorem αSection_mem {rrs : Array ByteArray} {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hb : b ∈ rrs.toList)
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (har : αRR rr = some r) : r ∈ αSection rrs := by
  unfold αSection
  rw [List.mem_filterMap]
  exact ⟨b, hb, by rw [hpr]; exact har⟩
theorem answersQueryB_covered (respA : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (qtq : VeriDNS.Spec.Net.QType) (qt : RRType)
    (hq : respA.question[0]? = some qu)
    (hαqt : αType qu.qtype = some qt) (hαq : αQType qu.qtype = some qtq)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    (hvalid : ∀ b ∈ respA.answer.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none) :
    ∃ r ∈ αSection respA.answer, qtq.covers r.rdata.rtype = true := by
  obtain ⟨b, hb, hαb⟩ := (answersQueryB_corr respA qu qt hq hαqt).mp hans
  have hbl : b ∈ respA.answer.toList := by simpa using hb
  unfold αRRType at hαb
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hαb; exact absurd hαb (by simp)
  | some rr =>
    rw [hpr] at hαb
    obtain ⟨r, hrr⟩ := Option.ne_none_iff_exists'.mp (hvalid b hbl rr hpr)
    refine ⟨r, αSection_mem hbl hpr hrr, ?_⟩
    have hrt : αType rr.type = some r.rdata.rtype := αRR_rtype rr r hrr
    have hqteq : r.rdata.rtype = qt := by
      have : αType rr.type = some qt := hαb
      rw [hrt] at this; exact Option.some.inj this
    rw [hqteq]; exact αQType_covers hαq hαqt
theorem questionMatch_αType {respA sub : VeriDNS.Spec.Format} {qb : VeriDNS.Spec.Question}
    {qt : RRType} {qtq : VeriDNS.Spec.Net.QType}
    (hqm : Server.questionMatches respA.question sub.question = true)
    (hsub : sub.question[0]? = some qb)
    (hαt : αType qb.qtype = some qt) (hαq : αQType qb.qtype = some qtq) :
    ∃ qa, respA.question[0]? = some qa ∧ αType qa.qtype = some qt ∧ αQType qa.qtype = some qtq := by
  unfold Server.questionMatches at hqm
  rw [hsub] at hqm
  cases hra : respA.question[0]? with
  | none => rw [hra] at hqm; simp at hqm
  | some qa =>
    rw [hra] at hqm
    simp only [Bool.and_eq_true, beq_iff_eq] at hqm
    obtain ⟨⟨_, htype⟩, _⟩ := hqm
    exact ⟨qa, rfl, htype.symm ▸ hαt, htype.symm ▸ hαq⟩
theorem answersQueryB_αType_some (respA : VeriDNS.Spec.Format) (qa : VeriDNS.Spec.Question)
    (hq : respA.question[0]? = some qa)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    (hvalid : ∀ b ∈ respA.answer.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none) :
    ∃ qt, αType qa.qtype = some qt := by
  unfold Resolver.answersQueryB at hans
  rw [hq] at hans
  unfold Resolver.hasRRTypeIn at hans
  obtain ⟨i, hi, hcond⟩ := Array.any_eq_true.mp hans
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) respA.answer[i] with
  | none => rw [hpr] at hcond; simp at hcond
  | some rr =>
    rw [hpr] at hcond
    simp only [beq_iff_eq] at hcond
    have hbmem : respA.answer[i] ∈ respA.answer.toList := by
      simpa using Array.getElem_mem hi
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hvalid respA.answer[i] hbmem rr hpr)
    exact ⟨r.rdata.rtype, hcond ▸ αRR_rtype rr r hr⟩
theorem RespAgree.answer_ne_nil {a b : VeriDNS.Spec.Net.Response}
    (h : RespAgree a b) (hne : a.answer ≠ []) : b.answer ≠ [] := by
  intro hb
  exact hne ((hb ▸ h.2).eq_nil)
theorem respAgree_covered_ref {respA : VeriDNS.Spec.Format} {ref : VeriDNS.Spec.Net.Response}
    {qtq : VeriDNS.Spec.Net.QType}
    (h : RespAgree (αResp respA) ref)
    (hc : ∃ r ∈ αSection respA.answer, qtq.covers r.rdata.rtype = true) :
    ∃ r ∈ ref.answer, qtq.covers r.rdata.rtype = true := by
  obtain ⟨r, hr, hcov⟩ := hc
  refine ⟨r, ?_, hcov⟩
  have hp : (αResp respA).answer.Perm ref.answer := h.2
  rw [(αResp_components respA).2.1] at hp
  exact hp.mem_iff.mp hr
theorem positive_answer_covered {subQuery0 respA : VeriDNS.Spec.Format} {rid cid : UInt16}
    {q : VeriDNS.Spec.Net.Query}
    {ref : VeriDNS.Spec.Net.Response}
    (hαQ : αQuery subQuery0 = some q)
    (hqmatch : Server.questionMatches respA.question
      (Server.withSecrets subQuery0 rid cid).question = true)
    (hansI : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    (hvalid : ∀ b ∈ respA.answer.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
    (hragA : RespAgree (αResp respA) ref) :
    ∃ r ∈ ref.answer, q.qtype.covers r.rdata.rtype = true := by
  have hvalidWeak : ∀ b ∈ respA.answer.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
    intro b hb rr hpr
    obtain ⟨rr', hpr', har'⟩ := hvalid b hb
    rw [hpr] at hpr'; exact Option.some.inj hpr' ▸ har'
  obtain ⟨qb, hsub, _, hαQType, _⟩ := αQuery_fields hαQ
  cases hqa : respA.question[0]? with
  | none => rw [Resolver.answersQueryB, hqa] at hansI; exact absurd hansI (by simp)
  | some qa =>
    have hsub' : (Server.withSecrets subQuery0 rid cid).question[0]?
        = some { qname := VeriDNS.Impl.DomainName.randomizeCase cid qb.qname,
                 qtype := qb.qtype, qclass := qb.qclass } := by
      show ((subQuery0.question.map _))[0]? = _
      rw [Array.getElem?_map, hsub]
      rfl
    have hqteq : qa.qtype = qb.qtype := by
      unfold Server.questionMatches at hqmatch
      rw [hqa, hsub'] at hqmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hqmatch
      exact hqmatch.1.2
    obtain ⟨qt, hαType⟩ := answersQueryB_αType_some respA qa hqa hansI hvalidWeak
    exact respAgree_covered_ref hragA
      (answersQueryB_covered respA qa q.qtype qt hqa hαType (hqteq ▸ hαQType) hansI hvalidWeak)
theorem acceptResponse_questionMatches {sent resp r : VeriDNS.Spec.Format}
    (h : Server.acceptResponse sent resp = some r) :
    Server.questionMatches r.question sent.question = true := by
  have heq : r = resp := by
    unfold Server.acceptResponse at h
    split at h
    · injection h with h; exact h.symm
    · exact absurd h (by simp)
  subst heq
  exact (acceptResponse_requires_match sent r h).2

theorem hasRRTypeIn_of_model_NS {authority : Array ByteArray}
    (r : VeriDNS.Spec.Net.RR) (hr : r ∈ αSection authority)
    (hrt : r.rdata.rtype = RRType.ns) :
    Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) authority 2 = true := by
  unfold αSection at hr
  rw [List.mem_filterMap] at hr
  obtain ⟨b, hb, hmap⟩ := hr
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hmap; simp at hmap
  | some rr =>
    rw [hpr] at hmap
    have hαrr : αRRType b = some RRType.ns := by
      unfold αRRType; rw [hpr]
      have h2 := αRR_rtype rr r hmap
      rw [hrt] at h2; exact h2
    exact (hasRRTypeIn_corr authority 2 RRType.ns rfl).mpr ⟨b, by simpa using hb, hαrr⟩

theorem αResp_isReferral_false_of_finished
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA : VeriDNS.Spec.Format}
    {result : Except String VeriDNS.Spec.Format} {cout : Cache.DnsCache}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hansI : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false)
    (hAR : Server.afterResume state entryName respA = .finished result cout)
    (hvalid : ∀ b ∈ respA.answer.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
    (hvalidAuth : ∀ b ∈ respA.authority.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) :
    (αResp respA).isReferral = false := by
  by_contra hir
  rw [Bool.not_eq_false] at hir
  unfold VeriDNS.Spec.Net.Response.isReferral at hir
  simp only [Bool.and_eq_true] at hir
  obtain ⟨⟨⟨⟨hae, haaM⟩, hno⟩, hns⟩, hsoaM⟩ := hir
  have hansEmpty : respA.answer.isEmpty = true := by
    have h1 : αSection respA.answer = [] := by
      have h0 : (αResp respA).answer = [] := by rw [← List.isEmpty_iff]; exact hae
      rwa [(αResp_components respA).2.1] at h0
    have h2 := αSection_nil_imp hvalid h1
    simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, h2]
  have hnerr : (respA.header.rcode == VeriDNS.Spec.Rcode.nameError) = false := by
    apply rcode_ne_nameError_of_αRCode_noError
    rwa [(αResp_components respA).1] at hno
  have hhasNS : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) respA.authority 2 = true := by
    rw [(αResp_components respA).2.2.1, List.any_eq_true] at hns
    obtain ⟨r, hr, hrt⟩ := hns
    have hrteq : r.rdata.rtype = RRType.ns :=
      VeriDNS.Proof.Refinement.rrtype_eq_of_beq hrt
    exact hasRRTypeIn_of_model_NS r hr hrteq
  have hauth : respA.authority.isEmpty = false := by
    by_contra h
    rw [Bool.not_eq_false, Array.isEmpty_iff] at h
    rw [h] at hhasNS
    simp [Resolver.hasRRTypeIn] at hhasNS
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl

  have haa : (respA.header.aa == 0) = true := by
    have hb : (αResp respA).aa = false := by simpa using haaM
    rw [(αResp_components respA).2.2.2.2.1] at hb
    revert hb; generalize respA.header.aa = a; revert a; decide
  have hrc : (respA.header.rcode == VeriDNS.Spec.Rcode.noError) = true := by
    have hb : (αRCode respA.header.rcode == VeriDNS.Spec.Net.RCode.noError) = true := by
      rw [← (αResp_components respA).1]; exact hno
    revert hb; cases respA.header.rcode <;> decide
  have hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) respA.authority 6 = false := by
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    obtain ⟨b, hbmem, hαrr⟩ := (hasRRTypeIn_corr respA.authority 6 RRType.soa (by decide)).mp hcon
    unfold αRRType at hαrr
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [hpr] at hαrr; simp at hαrr
    | some rr =>
      rw [hpr] at hαrr
      obtain ⟨rr', hpr', hne⟩ := hvalidAuth b (by simpa using hbmem)
      rw [hpr] at hpr'; cases hpr'
      cases hαr : αRR rr with
      | none => exact absurd hαr hne
      | some mrr =>
        have hrt : αType rr.type = some mrr.rdata.rtype := αRR_rtype rr mrr hαr
        have hsoa' : mrr.rdata.rtype = RRType.soa :=
          Option.some.inj (hrt.symm.trans hαrr)
        have hmem : mrr ∈ (αResp respA).authority := by
          rw [(αResp_components respA).2.2.1]
          exact List.mem_filterMap.mpr ⟨b, by simpa using hbmem, by rw [hpr]; exact hαr⟩
        have hany : (αResp respA).authority.any (fun rr => rr.rdata.rtype == RRType.soa) = true :=
          List.any_eq_true.mpr ⟨mrr, hmem, by rw [hsoa']; decide⟩
        rw [hany] at hsoaM; simp at hsoaM
  obtain ⟨st, hcont⟩ := afterResume_referral_continues state entryName respA hstep hcname hbiz hansI hnerr
    hansEmpty hauth hhasNS haa hrc hsoa
  rw [hcont] at hAR
  exact absurd hAR (by simp)

theorem αResp_isReferral_true_of_referralShape {respA : VeriDNS.Spec.Format}
    (hansEmpty : respA.answer.isEmpty = true)
    (haa : (respA.header.aa == 0) = true)
    (hrc : (respA.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) respA.authority 2 = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) respA.authority 6 = false)
    (hvalidAuth : ∀ b ∈ respA.authority.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) :
    (αResp respA).isReferral = true := by
  unfold VeriDNS.Spec.Net.Response.isReferral
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [(αResp_components respA).2.1, αSection_empty_of_isEmpty hansEmpty]; rfl
  · rw [(αResp_components respA).2.2.2.2.1]
    revert haa; generalize respA.header.aa = a; revert a; decide
  · rw [(αResp_components respA).1]
    revert hrc; cases respA.header.rcode <;> decide
  · rw [(αResp_components respA).2.2.1]
    obtain ⟨b, hbmem, hαrr⟩ := (hasRRTypeIn_corr respA.authority 2 RRType.ns (by decide)).mp hns
    unfold αRRType at hαrr
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [hpr] at hαrr; simp at hαrr
    | some rr =>
      rw [hpr] at hαrr
      obtain ⟨rr', hpr', hne⟩ := hvalidAuth b (by simpa using hbmem)
      rw [hpr] at hpr'; cases hpr'
      cases hαr : αRR rr with
      | none => exact absurd hαr hne
      | some mrr =>
        have hrt : αType rr.type = some mrr.rdata.rtype := αRR_rtype rr mrr hαr
        have hns' : mrr.rdata.rtype = RRType.ns := Option.some.inj (hrt.symm.trans hαrr)
        have hmem : mrr ∈ αSection respA.authority :=
          List.mem_filterMap.mpr ⟨b, by simpa using hbmem, by rw [hpr]; exact hαr⟩
        exact List.any_eq_true.mpr ⟨mrr, hmem, by rw [hns']; decide⟩
  · rw [(αResp_components respA).2.2.1]
    suffices h : (αSection respA.authority).any (fun rr => rr.rdata.rtype == RRType.soa) = false by
      rw [h]; rfl
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    obtain ⟨mrr, hmem, hp⟩ := List.any_eq_true.mp hcon
    simp only [αSection, List.mem_filterMap] at hmem
    obtain ⟨b, hbmem, hmap⟩ := hmem
    have hcontra : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) respA.authority 6 = true := by
      apply (hasRRTypeIn_corr respA.authority 6 RRType.soa (by decide)).mpr
      refine ⟨b, by simpa using hbmem, ?_⟩
      unfold αRRType
      cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => rw [hpr] at hmap; simp at hmap
      | some rr =>
        simp only [hpr] at hmap
        have hrt : αType rr.type = some mrr.rdata.rtype := αRR_rtype rr mrr hmap
        have hsoa' : mrr.rdata.rtype = RRType.soa :=
          VeriDNS.Proof.Refinement.rrtype_eq_of_beq hp
        rw [hsoa'] at hrt; exact hrt
    rw [hcontra] at hsoa; simp at hsoa

theorem serverAnswers_referral_inv {s : VeriDNS.Spec.Net.Server} {now : Time}
    {seen : List VeriDNS.Spec.Net.Name} {o : Bool} {q : VeriDNS.Spec.Net.Query}
    {tr : List VeriDNS.Spec.Net.Step} {ref : VeriDNS.Spec.Net.Response}
    (hans : VeriDNS.Spec.Net.ServerAnswers s now seen o q tr ref) (href : ref.isReferral = true) :
    (∃ z d, VeriDNS.Spec.Net.bestZone s q.qname q.qclass = some z
        ∧ VeriDNS.Spec.Net.bestDeleg z q.qname = some d ∧ ref.authority = d.nsSet)
      ∨ (VeriDNS.Spec.Net.bestZone s q.qname q.qclass = none
        ∧ ref.authority = VeriDNS.Spec.Net.cachedDelegation s now q.qname q.qclass) := by
  cases hans with
  | referral q z d hz hd hca => exact Or.inl ⟨z, d, hz, hd, rfl⟩
  | fromCache q here hz hh hne => exact Or.inr ⟨hz, rfl⟩
  | referralCacheAnswer q z d here hz hd hca hne =>
      exfalso; apply hne
      unfold VeriDNS.Spec.Net.Response.isReferral at href
      simp only [Bool.and_eq_true] at href
      exact List.isEmpty_iff.mp href.1.1.1.1
  | _ => simp [VeriDNS.Spec.Net.Response.isReferral] at href

/-- A `nameError` honest reply carries only CNAME records in its answer section
    (the empty NXDOMAIN answer, or the CNAME links prepended when chasing a chain
    into a non-existent name).  Used to show a genuine type-`qt` answer
    (`qt ≠ cname`) is never NXDOMAIN — the honest-side witness that a foreign
    off-owner acceptance never fires on an NXDOMAIN with data. -/
theorem serverAnswers_nameError_answer_cnames {s : VeriDNS.Spec.Net.Server} {now : Time}
    {seen : List VeriDNS.Spec.Net.Name} {o : Bool} {q : VeriDNS.Spec.Net.Query}
    {tr : List VeriDNS.Spec.Net.Step} {ref : VeriDNS.Spec.Net.Response}
    (hans : VeriDNS.Spec.Net.ServerAnswers s now seen o q tr ref)
    (hrc : ref.rcode = VeriDNS.Spec.Net.RCode.nameError) :
    ∀ r ∈ ref.answer, r.rdata.rtype = RRType.cname := by
  induction hans with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih =>
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [ht]; rfl
    · exact ih hrc r hr
  | nameError q z hz hd hh hw hent => intro r hr; simp at hr
  | _ => exact absurd hrc (by simp)

/-- **Honest ¬NXDOMAIN witness.**  If an honest reply covers the (non-CNAME)
    query type with a genuine answer record, it is not NXDOMAIN: an NXDOMAIN
    carries only CNAME chain links, none of which covers a non-CNAME type.  This
    lets the answer terminal establish `¬ nameError` for the off-owner
    entitlement bridge (findings 036 / off-owner-A). -/
theorem serverAnswers_covered_not_nameError {s : VeriDNS.Spec.Net.Server} {now : Time}
    {seen : List VeriDNS.Spec.Net.Name} {o : Bool} {q : VeriDNS.Spec.Net.Query}
    {tr : List VeriDNS.Spec.Net.Step} {ref : VeriDNS.Spec.Net.Response}
    (hans : VeriDNS.Spec.Net.ServerAnswers s now seen o q tr ref)
    (hcov : ∃ r ∈ ref.answer, q.qtype.covers r.rdata.rtype = true)
    (hqt : q.qtype.covers RRType.cname = false) :
    ref.rcode ≠ VeriDNS.Spec.Net.RCode.nameError := by
  intro hrc
  obtain ⟨r, hr, hcovr⟩ := hcov
  have hcn := serverAnswers_nameError_answer_cnames hans hrc r hr
  rw [hcn] at hcovr
  rw [hcovr] at hqt
  exact absurd hqt (by simp)

/-- A `nameError` honest reply with a NON-empty answer section came from a CNAME
    chase, hence its query type does not cover CNAME (the `cname` constructor's
    side condition).  The base `nameError` constructor delivers an empty answer. -/
theorem serverAnswers_nameError_nonempty_qtype_not_cname {s : VeriDNS.Spec.Net.Server}
    {now : Time} {seen : List VeriDNS.Spec.Net.Name} {o : Bool} {q : VeriDNS.Spec.Net.Query}
    {tr : List VeriDNS.Spec.Net.Step} {ref : VeriDNS.Spec.Net.Response}
    (hans : VeriDNS.Spec.Net.ServerAnswers s now seen o q tr ref)
    (hrc : ref.rcode = VeriDNS.Spec.Net.RCode.nameError)
    (hne : ref.answer ≠ []) :
    q.qtype.covers RRType.cname = false := by
  induction hans with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih => exact hcov
  | nameError q z hz hd hh hw hent => exact absurd rfl hne
  | _ => exact absurd hrc (by simp)

/-- **Honest ¬NXDOMAIN witness (unconditional).**  If an honest reply covers the
    query type with a genuine answer record, it is not NXDOMAIN — regardless of
    whether the query type covers CNAME.  When it does, a nameError reply carries
    an empty answer (the base `nameError` constructor), so no covered record
    exists; when it does not, the CNAME-chain witness applies. -/
theorem serverAnswers_covered_not_nameError_uncond {s : VeriDNS.Spec.Net.Server} {now : Time}
    {seen : List VeriDNS.Spec.Net.Name} {o : Bool} {q : VeriDNS.Spec.Net.Query}
    {tr : List VeriDNS.Spec.Net.Step} {ref : VeriDNS.Spec.Net.Response}
    (hans : VeriDNS.Spec.Net.ServerAnswers s now seen o q tr ref)
    (hcov : ∃ r ∈ ref.answer, q.qtype.covers r.rdata.rtype = true) :
    ref.rcode ≠ VeriDNS.Spec.Net.RCode.nameError := by
  intro hrc
  obtain ⟨r, hr, hcovr⟩ := hcov
  have hne : ref.answer ≠ [] := List.ne_nil_of_mem hr
  have hqt := serverAnswers_nameError_nonempty_qtype_not_cname hans hrc hne
  exact serverAnswers_covered_not_nameError hans ⟨r, hr, hcovr⟩ hqt hrc

theorem αType_cname_toNat {t : BitVec 16} (h : αType t = some RRType.cname) : t.toNat = 5 := by
  unfold αType at h
  split at h <;> simp_all


theorem αRR_cname_target (rr : VeriDNS.Spec.ResourceRecord) (cn : VeriDNS.Spec.Net.RR)
    (h5 : rr.type = (5 : BitVec 16)) (h : αRR rr = some cn) :
    ∃ tgt, cn.rdata = VeriDNS.Spec.Net.RData.cname tgt ∧ αName rr.rdata = some tgt := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    have hcnr : cn.rdata = rdata := by rw [← Option.some.inj h]
    unfold αRData at hrd
    rw [h5] at hrd
    simp only [show (5 : BitVec 16).toNat = 5 from rfl] at hrd
    rw [Option.map_eq_some_iff] at hrd
    obtain ⟨tgt, htgt, hrdeq⟩ := hrd
    exact ⟨tgt, by rw [hcnr, ← hrdeq], htgt⟩
  · exact absurd h (by simp)

theorem αRR_ns_host (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h2 : rr.type = (2 : BitVec 16)) (h : αRR rr = some r) :
    ∃ host, r.rdata = VeriDNS.Spec.Net.RData.ns host ∧ αName rr.rdata = some host := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    have hcnr : r.rdata = rdata := by rw [← Option.some.inj h]
    unfold αRData at hrd
    rw [h2] at hrd
    simp only [show (2 : BitVec 16).toNat = 2 from rfl] at hrd
    rw [Option.map_eq_some_iff] at hrd
    obtain ⟨host, hhost, hrdeq⟩ := hrd
    exact ⟨host, by rw [hcnr, ← hrdeq], hhost⟩
  · exact absurd h (by simp)

theorem αRR_a_addr (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h1 : rr.type = (1 : BitVec 16)) (h : αRR rr = some r) :
    ∃ a, r.rdata = VeriDNS.Spec.Net.RData.a a ∧ αIPv4 rr.rdata = some a := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    have hcnr : r.rdata = rdata := by rw [← Option.some.inj h]
    unfold αRData at hrd
    rw [h1] at hrd
    simp only [show (1 : BitVec 16).toNat = 1 from rfl] at hrd
    rw [Option.map_eq_some_iff] at hrd
    obtain ⟨a, ha, hrdeq⟩ := hrd
    exact ⟨a, by rw [hcnr, ← hrdeq], ha⟩
  · exact absurd h (by simp)

theorem modelSlistOf_fromNsWithGlue_αSection (names additional : Array ByteArray) (mc : Nat) (s : String)
    (hvalid : ∀ b ∈ additional.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none)
    (h : s ∈ modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names
        (Resolver.extractGlueRecords additional) mc)) :
    ∃ r ∈ αSection additional, ∃ a, r.rdata = VeriDNS.Spec.Net.RData.a a ∧ s = a.toDotted := by
  obtain ⟨raw, hraw, rr, off, a, hdec, htype, hαiv, hs⟩ :=
    modelSlistOf_fromNsWithGlue_model names additional mc s h
  have hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr := by
    show (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw with
      | .ok (rr, _) => some rr | .error _ => none) = some rr
    rw [hdec]
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hvalid raw (by simpa using hraw) rr hpr)
  obtain ⟨a', hrd, hαiv'⟩ := αRR_a_addr rr r (by simpa using htype) hr
  have ha'eq : a' = a := by rw [hαiv'] at hαiv; exact Option.some.inj hαiv
  subst a'
  exact ⟨r, αSection_mem (by simpa using hraw) hpr hr, a, hrd, hs⟩

theorem extractNsNames_referredServers (authority : Array ByteArray)
    (hvalid : ∀ b ∈ authority.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none) :
    (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) authority).toList.filterMap αName
      = (αSection authority).filterMap (fun r => match r.rdata with
          | VeriDNS.Spec.Net.RData.ns h => some h | _ => none) := by
  simp only [Resolver.extractNsNames, αSection, Array.toList_filterMap, List.filterMap_filterMap]
  apply filterMap_congr_mem
  intro b hb
  have hrd_eq : VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) = fun rr => rr.rdata := rfl
  have hrt_eq : VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) = fun rr => rr.type := rfl
  cases hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => simp only [hpb, Option.bind_none]
  | some rr =>
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hvalid b hb rr hpb)
    simp only [hpb, hr, hrd_eq, hrt_eq, Option.bind_some]
    by_cases h2 : rr.type == (2 : BitVec 16)
    · obtain ⟨host, hrd, hname⟩ := αRR_ns_host rr r (by simpa using h2) hr
      rw [if_pos (by simpa using h2), Option.bind_some, hname, hrd]
    · rw [if_neg (by simpa using h2), Option.bind_none]
      have h2rr := αRR_rtype rr r hr
      cases hrt : r.rdata with
      | ns host =>
        exfalso
        rw [hrt] at h2rr
        have hty2 : rr.type = (2 : BitVec 16) := by
          apply BitVec.eq_of_toNat_eq; simpa using αType_ns_toNat h2rr
        rw [hty2] at h2; simp at h2
      | _ => rfl

theorem extractNsNames_referredServers_αResp (resp : VeriDNS.Spec.Format)
    (hvalid : ∀ b ∈ resp.authority.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none) :
    (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority).toList.filterMap αName
      = VeriDNS.Spec.Net.referredServers (αResp resp) := by
  rw [extractNsNames_referredServers resp.authority hvalid]
  unfold VeriDNS.Spec.Net.referredServers
  rw [(αResp_components resp).2.2.1]
  apply filterMap_congr_mem
  intro r _
  cases r.rdata <;> rfl


theorem extractNsNames_abstracts (authority : Array ByteArray)
    (hvalid : ∀ raw ∈ authority.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr → αRR rr ≠ none)
    (b : ByteArray)
    (hb : b ∈ (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) authority).toList) :
    ∃ h, αName b = some h := by
  obtain ⟨raw, hraw, rr, hpr, htype, hrd⟩ := mem_extractNsNames authority b (Array.mem_def.mpr hb)
  have hαrr : αRR rr ≠ none := hvalid raw (Array.mem_def.mp hraw) rr hpr
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hαrr
  have htype' : rr.type = (2 : BitVec 16) := by
    have h := htype; simp only [VeriDNS.Spec.RRParse.rrType] at h; exact beq_iff_eq.mp h
  obtain ⟨host, _, hname⟩ := αRR_ns_host rr r htype' hr
  exact ⟨host, by rw [show (b = rr.rdata) from hrd.symm]; exact hname⟩

theorem parseRaw_name_canonical {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    ∃ na, αName rr.name = some na ∧ rr.name = DomainName.labelsToWireFormatGo na
      ∧ (∀ x ∈ na, x.size ≤ 63) := by
  have hm : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
      | .ok (rr, _) => some rr | .error _ => none) = some rr := h
  cases hrun : DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | error e => simp [hrun] at hm
  | ok p =>
    obtain ⟨rr', pos'⟩ := p
    simp only [hrun] at hm
    obtain rfl : rr' = rr := Option.some.inj hm
    obtain ⟨labels, hvalid, hname, _, _⟩ := VeriDNS.Proof.Message.run_resourceRecordDecode_valid hrun
    refine ⟨labels.toList, ?_, ?_, ?_⟩
    · rw [← hname]; unfold αName
      rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip labels hvalid]
    · rw [← hname]; rfl
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      exact (hvalid i (by simpa using hi)).2

theorem questionFromLabels_canonical {qu : VeriDNS.Spec.Question}
    (h : VeriDNS.Proof.Message.QuestionFromLabels qu) :
    ∃ qn, αName qu.qname = some qn ∧ qu.qname = DomainName.labelsToWireFormatGo qn
      ∧ (∀ x ∈ qn, x.size ≤ 63) := by
  obtain ⟨ls, hvalid, _hsz, hname⟩ := h
  refine ⟨ls.toList, ?_, ?_, ?_⟩
  · rw [← hname]; unfold αName
    rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip ls hvalid]
  · rw [← hname]; rfl
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact (hvalid i (by simpa using hi)).2

theorem cnamePred_agree {sname : ByteArray} {qn : VeriDNS.Spec.Net.Name}
    {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord} {cn : VeriDNS.Spec.Net.RR}
    (hsq : αName sname = some qn)
    (hsc : sname = DomainName.labelsToWireFormatGo qn)
    (hsv : ∀ x ∈ qn, x.size ≤ 63)
    (hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hcn : αRR rr = some cn) :
    ((rr.type == (5 : BitVec 16)) && VeriDNS.Impl.DomainName.nameEqCI rr.name sname)
      = ((cn.rdata.rtype == RRType.cname) && VeriDNS.Spec.Net.nameEq cn.owner qn) := by
  have hty : (rr.type == (5 : BitVec 16)) = (cn.rdata.rtype == RRType.cname) := by
    cases h5 : rr.type == (5 : BitVec 16) with
    | true =>
      obtain ⟨tgt, hrdeq, -⟩ := αRR_cname_target rr cn (eq_of_beq h5) hcn
      rw [hrdeq]; rfl
    | false =>
      have h2 := αRR_rtype rr cn hcn
      cases hrt : cn.rdata.rtype <;>
        first
        | rfl
        | (exfalso
           rw [hrt] at h2
           have h5nat := αType_cname_toNat h2
           have h5eq : rr.type = (5 : BitVec 16) := by
             apply BitVec.eq_of_toNat_eq; simpa using h5nat
           rw [h5eq] at h5; simp at h5)
  obtain ⟨na, hαn, hcann, hvn⟩ := parseRaw_name_canonical hpb
  have hown : αName rr.name = some cn.owner := (αRR_fields rr cn hcn).1
  obtain rfl : na = cn.owner := Option.some.inj (hαn.symm.trans hown)
  have hci : VeriDNS.Impl.DomainName.nameEqCI rr.name sname
      = VeriDNS.Spec.Net.nameEq cn.owner qn :=
    nameEqCI_eq_nameEq hcann hvn hown hsc hsv hsq
  rw [hty, hci]

theorem αSection_ownerRaws_eq (sname : ByteArray) (qnN : VeriDNS.Spec.Net.Name)
    (section_ : Array ByteArray)
    (hsq : αName sname = some qnN)
    (hsc : sname = DomainName.labelsToWireFormatGo qnN)
    (hsv : ∀ x ∈ qnN, x.size ≤ 63) :
    αSection (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname section_)
      = (αSection section_).filter (fun r => VeriDNS.Spec.Net.nameEq r.owner qnN) := by
  unfold αSection Resolver.ownerRaws
  rw [Array.toList_filter]
  apply filter_filterMap_comm
  intro b r hg
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hg; simp at hg
  | some rr =>
    rw [hpr] at hg
    have hn : αName rr.name = some r.owner := (αRR_fields rr r hg).1
    obtain ⟨na, hαn, hcann, hvn⟩ := parseRaw_name_canonical hpr
    obtain rfl : na = r.owner := Option.some.inj (hαn.symm.trans hn)
    show VeriDNS.Impl.DomainName.nameEqCI (VeriDNS.Spec.RRParse.rrName rr) sname
      = VeriDNS.Spec.Net.nameEq r.owner qnN
    exact nameEqCI_eq_nameEq hcann hvn hn hsc hsv hsq

/-- Finding 019 α-bridge: the impl chase-link slice (`cnameRaws`) abstracts to
the model chase-link slice (the `cnameOwned` filter) — `cnamePred_agree` gives
the pointwise predicate agreement. -/
theorem αSection_cnameRaws_eq (sname : ByteArray) (qnN : VeriDNS.Spec.Net.Name)
    (section_ : Array ByteArray)
    (hsq : αName sname = some qnN)
    (hsc : sname = DomainName.labelsToWireFormatGo qnN)
    (hsv : ∀ x ∈ qnN, x.size ≤ 63) :
    αSection (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) sname section_)
      = (αSection section_).filter
          (fun r => r.rdata.rtype == VeriDNS.Spec.RRType.cname
            && VeriDNS.Spec.Net.nameEq r.owner qnN) := by
  unfold αSection Resolver.cnameRaws
  rw [Array.toList_filter]
  apply filter_filterMap_comm
  intro b r hg
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hg; simp at hg
  | some rr =>
    rw [hpr] at hg
    show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == (5 : BitVec 16)
        && VeriDNS.Impl.DomainName.nameEqCI
            (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr) sname)
      = (r.rdata.rtype == VeriDNS.Spec.RRType.cname && VeriDNS.Spec.Net.nameEq r.owner qnN)
    exact cnamePred_agree hsq hsc hsv hpr hg

theorem cnameRR_none_of_extractCname_none {sname : ByteArray} {qn : VeriDNS.Spec.Net.Name}
    {answer : Array ByteArray}
    (hsq : αName sname = some qn)
    (hsc : sname = DomainName.labelsToWireFormatGo qn)
    (hsv : ∀ x ∈ qn, x.size ≤ 63)
    (h : Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) sname answer = none) :
    VeriDNS.Spec.Net.cnameRR qn (αSection answer) = none := by
  rw [VeriDNS.Spec.Net.cnameRR, List.find?_eq_none]
  intro r hr hpred
  unfold αSection at hr
  rw [List.mem_filterMap] at hr
  obtain ⟨b, hb, hmap⟩ := hr
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hmap; simp at hmap
  | some rr =>
    rw [hpr] at hmap
    have hagree := cnamePred_agree hsq hsc hsv hpr hmap
    rw [Resolver.extractCname, Array.findSome?_eq_none_iff] at h
    have hb' := h b (by simpa using hb)
    rw [← hagree, Bool.and_eq_true] at hpred
    simp only [hpr] at hb'
    rw [if_pos (Bool.and_eq_true _ _ |>.mpr
      ⟨show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
          == (5 : BitVec 16)) = true from hpred.1,
       show VeriDNS.Impl.DomainName.nameEqCI
          (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr) sname = true
        from hpred.2⟩)] at hb'
    cases hb'

theorem cnameRR_some_of_extractCname {sname : ByteArray} {qn : VeriDNS.Spec.Net.Name}
    {answer : Array ByteArray} {target : ByteArray}
    (hsq : αName sname = some qn)
    (hsc : sname = DomainName.labelsToWireFormatGo qn)
    (hsv : ∀ x ∈ qn, x.size ≤ 63)
    (h : Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) sname answer = some target)
    (hvalid : ∀ b ∈ answer.toList, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b
        = some rr → αRR rr ≠ none) :
    ∃ cn tgt, VeriDNS.Spec.Net.cnameRR qn (αSection answer) = some cn
      ∧ cn.rdata = VeriDNS.Spec.Net.RData.cname tgt ∧ αName target = some tgt := by
  unfold Resolver.extractCname at h
  rw [← Array.findSome?_toList] at h
  simp only [show ∀ rr : VeriDNS.Spec.ResourceRecord,
      VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr = rr.type from fun _ => rfl,
    show ∀ rr : VeriDNS.Spec.ResourceRecord,
      VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr = rr.rdata from fun _ => rfl,
    show ∀ rr : VeriDNS.Spec.ResourceRecord,
      VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr = rr.name from fun _ => rfl] at h
  rw [VeriDNS.Spec.Net.cnameRR]
  unfold αSection
  revert h hvalid
  generalize answer.toList = L
  induction L with
  | nil => intro _ h; simp at h
  | cons b L' ih =>
    intro hvalid h
    have hvalid' : ∀ b ∈ L', ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        αRR rr ≠ none := fun x hx => hvalid x (List.mem_cons_of_mem _ hx)
    rw [List.findSome?_cons] at h
    cases hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none =>
      rw [hpb] at h
      simp only [List.filterMap_cons, hpb]
      exact ih hvalid' (by simpa using h)
    | some rr =>
      have hrr : αRR rr ≠ none := hvalid b (by simp) rr hpb
      obtain ⟨cn, hcn⟩ := Option.ne_none_iff_exists'.mp hrr
      rw [hpb] at h
      simp only [List.filterMap_cons, hpb, hcn]
      have hagree := cnamePred_agree hsq hsc hsv hpb hcn
      by_cases hp5 : (rr.type == (5 : BitVec 16)
          && VeriDNS.Impl.DomainName.nameEqCI rr.name sname) = true
      · simp only [hp5, if_true] at h
        have htgt : target = rr.rdata := (Option.some.inj h).symm
        obtain ⟨tgt, hrdeq, hname⟩ := αRR_cname_target rr cn
          (eq_of_beq (Bool.and_eq_true _ _ |>.mp hp5).1) hcn
        refine ⟨cn, tgt, ?_, hrdeq, by rw [htgt]; exact hname⟩
        refine List.find?_cons_of_pos ?_
        show (cn.rdata.rtype == RRType.cname && VeriDNS.Spec.Net.nameEq cn.owner qn) = true
        rw [← hagree]; exact hp5
      · rw [Bool.not_eq_true] at hp5
        simp only [hp5, if_false] at h
        have hnp : ¬ (fun r : VeriDNS.Spec.Net.RR =>
            r.rdata.rtype == RRType.cname && VeriDNS.Spec.Net.nameEq r.owner qn) cn = true := by
          show ¬ (cn.rdata.rtype == RRType.cname && VeriDNS.Spec.Net.nameEq cn.owner qn) = true
          rw [← hagree, hp5]; simp
        obtain ⟨cn1, tgt1, hfind1, hrd1, hnm1⟩ := ih hvalid' (by simpa using h)
        refine ⟨cn1, tgt1, ?_, hrd1, hnm1⟩
        rw [List.find?_cons_of_neg (a := cn) hnp]
        exact hfind1

theorem parseRaw_entry_canonical {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hαRR : (αRR rr).isSome = true)
    (hnoov : (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome = true
        ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
        ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
      ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ = some a →
          rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63)) := by
  obtain ⟨na, hαN, hcanN, hsz⟩ := parseRaw_name_canonical hp
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show (αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩).isSome = true
    unfold αCacheRR
    simp only [Option.isSome_map]
    exact hαRR
  · rw [hnoov]; exact Nat.le_add_left _ _
  · rw [hnoov]; omega
  · intro a ha
    have hrr := αCacheRR_rr ha
    have hfields := αRR_fields rr a.rr hrr
    have hown : a.rr.owner = na := by
      have hn := hfields.1
      rw [hαN] at hn
      exact (Option.some.inj hn).symm
    rw [hown]
    exact ⟨hcanN, hsz⟩

private theorem ba_empty_append' (a : ByteArray) : ByteArray.empty ++ a = a := by
  ext1; simp [ByteArray.data_append]

private theorem ba_append_empty' (a : ByteArray) : a ++ ByteArray.empty = a := by
  ext1; simp [ByteArray.data_append]

theorem rrWire_nsRdata_canonical (ls : Array ByteArray)
    (hvls : VeriDNS.Proof.DomainName.ValidLabels ls)
    (hle_ls : (VeriDNS.Impl.DomainName.labelsToWireFormat ls).size ≤ 255)
    (c : BitVec 16) (ttl : BitVec 32) (rdLs : Array ByteArray)
    (hvrd : VeriDNS.Proof.DomainName.ValidLabels rdLs)
    (hsz : (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs).size < 65536)
    {rr : VeriDNS.Spec.ResourceRecord}
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
            (VeriDNS.Proof.Message.rrWire ls 2 c ttl
              (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs)) = some rr) :
    ∃ na, αName rr.rdata = some na
      ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
      ∧ (∀ x ∈ na, x.size ≤ 63) := by
  have hrun := VeriDNS.Proof.Message.run_resourceRecordDecode_rrWire ls hvls hle_ls 2 c ttl
    (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs) hsz ByteArray.empty ByteArray.empty
  rw [ba_append_empty', ba_empty_append'] at hrun
  simp only [show ByteArray.empty.size = 0 from rfl] at hrun
  have hm : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode
      (VeriDNS.Proof.Message.rrWire ls 2 c ttl
        (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs)) with
      | .ok (rr, _) => some rr | .error _ => none) = some rr := hp
  simp only [hrun] at hm
  obtain rfl : rr = _ := (Option.some.inj hm).symm
  refine ⟨rdLs.toList, ?_, ?_, ?_⟩
  · show αName (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs) = some rdLs.toList
    unfold αName
    rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip rdLs hvrd]
  · rfl
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact (hvrd i (by simpa using hi)).2

theorem canonicalRR_nsRdata_canonical {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hcanon : VeriDNS.Proof.Message.CanonicalRR b)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hns : rr.type = 2) :
    ∃ na, αName rr.rdata = some na
      ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
      ∧ (∀ x ∈ na, x.size ≤ 63) ∧ na.length ≤ 127 := by
  obtain ⟨ls, t, c, ttl, rdata, hvls, hle_ls, hrd, rfl⟩ := hcanon
  have hsz := VeriDNS.Proof.Message.canonicalRdata_size_lt hrd
  have hrun := VeriDNS.Proof.Message.run_resourceRecordDecode_rrWire ls hvls hle_ls t c ttl rdata hsz
    ByteArray.empty ByteArray.empty
  rw [ba_append_empty', ba_empty_append'] at hrun
  simp only [show ByteArray.empty.size = 0 from rfl] at hrun
  have hm : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode
      (VeriDNS.Proof.Message.rrWire ls t c ttl rdata) with
      | .ok (rr, _) => some rr | .error _ => none) = some rr := hp
  simp only [hrun] at hm
  obtain rfl := (Option.some.inj hm).symm
  have ht2 : t = 2 := hns
  cases hrd with
  | @nameType _ rdLs ht hv hle =>
    refine ⟨rdLs.toList, ?_, ?_, ?_, ?_⟩
    · show αName (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs) = some rdLs.toList
      unfold αName
      rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip rdLs hv]
    · rfl
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      exact (hv i (by simpa using hi)).2
    ·
      have hpos : ∀ x ∈ rdLs.toList, 0 < x.size := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        exact (hv i (by simpa using hi)).1
      have hb := VeriDNS.Proof.DomainName.labelsToWireFormatGo_length_bound rdLs.toList hpos
      have hle' : (VeriDNS.Impl.DomainName.labelsToWireFormatGo rdLs.toList).size ≤ 255 := hle
      omega
  | @soa m' r' tail' hm' hr' hlem hler htail => exact absurd ht2 (by decide)
  | @prefixedName _ _ _ ht _ _ =>
    rcases ht with ⟨ht', -⟩ | ⟨ht', -⟩ <;> exact absurd (ht'.symm.trans ht2) (by decide)
  | @other _ _ h2 _ _ _ _ _ _ => exact absurd ht2 h2

theorem canonicalRR_cnameRdata_canonical {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hcanon : VeriDNS.Proof.Message.CanonicalRR b)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hcn : rr.type = 5) :
    ∃ na, αName rr.rdata = some na
      ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
      ∧ (∀ x ∈ na, x.size ≤ 63) ∧ na.length ≤ 127 := by
  obtain ⟨ls, t, c, ttl, rdata, hvls, hle_ls, hrd, rfl⟩ := hcanon
  have hsz := VeriDNS.Proof.Message.canonicalRdata_size_lt hrd
  have hrun := VeriDNS.Proof.Message.run_resourceRecordDecode_rrWire ls hvls hle_ls t c ttl rdata hsz
    ByteArray.empty ByteArray.empty
  rw [ba_append_empty', ba_empty_append'] at hrun
  simp only [show ByteArray.empty.size = 0 from rfl] at hrun
  have hm : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode
      (VeriDNS.Proof.Message.rrWire ls t c ttl rdata) with
      | .ok (rr, _) => some rr | .error _ => none) = some rr := hp
  simp only [hrun] at hm
  obtain rfl := (Option.some.inj hm).symm
  have ht5 : t = 5 := hcn
  cases hrd with
  | @nameType _ rdLs ht hv hle =>
    refine ⟨rdLs.toList, ?_, ?_, ?_, ?_⟩
    · show αName (VeriDNS.Impl.DomainName.labelsToWireFormat rdLs) = some rdLs.toList
      unfold αName
      rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip rdLs hv]
    · rfl
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      exact (hv i (by simpa using hi)).2
    ·
      have hpos : ∀ x ∈ rdLs.toList, 0 < x.size := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        exact (hv i (by simpa using hi)).1
      have hb := VeriDNS.Proof.DomainName.labelsToWireFormatGo_length_bound rdLs.toList hpos
      have hle' : (VeriDNS.Impl.DomainName.labelsToWireFormatGo rdLs.toList).size ≤ 255 := hle
      omega
  | @soa m' r' tail' hm' hr' hlem hler htail => exact absurd ht5 (by decide)
  | @prefixedName _ _ _ ht _ _ =>
    rcases ht with ⟨ht', -⟩ | ⟨ht', -⟩ <;> exact absurd (ht'.symm.trans ht5) (by decide)
  | @other _ _ _ h5 _ _ _ _ _ => exact absurd ht5 h5

end VeriDNS.Proof.Refinement
