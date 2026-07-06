import VeriDNS.Proof.Refinement
import VeriDNS.Proof.MessageValid

/-! # Answer-terminal abstraction & glue lemmas

  Extracted from `Refinement.lean` (which was a 4000-line monolith). This module groups the
  `αSection`-faithfulness lemmas, the query-type/`αType` bridges, and the positive answer-terminal
  covered-record glue (`positive_answer_covered` and its support) that the forward-simulation driver's
  answer terminal consumes. Kept in dependency order; everything imports the core abstractions from
  `Refinement`. -/

namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (Trustworthiness RRType RRClass)
open VeriDNS.Impl
open VeriDNS.Spec.Net (Time)

/-- `αType` pins the NS code: only wire type `2` abstracts to the model `ns` record type. Lets the honest
    *negative* terminal turn a model-authority NS record back into the impl's `hasRRTypeIn authority 2`
    (the impl referral-guard's NS check) — the authority half of the `isReferral` correspondence. -/
theorem αType_ns_toNat {t : BitVec 16} (h : αType t = some RRType.ns) : t.toNat = 2 := by
  unfold αType at h
  split at h <;> simp_all
/-- Only the impl `noError` rcode abstracts to model `noError`, so a model-`noError` response is not an
    NXDOMAIN. The `noError` half of the honest-negative `isReferral` correspondence (model `noError` ⟹ the
    impl referral-guard's `rcode ≠ nameError`). -/
theorem rcode_ne_nameError_of_αRCode_noError {rc : VeriDNS.Spec.Rcode}
    (h : (αRCode rc == VeriDNS.Spec.Net.RCode.noError) = true) :
    (rc == VeriDNS.Spec.Rcode.nameError) = false := by
  cases rc <;> first | rfl | exact absurd h (by simp only [αRCode]; decide)
/-- **`αSection` is non-dropping when every raw RR abstracts** (faithfulness, the answer-terminal direction).
    If `rrs` is non-empty and each raw RR both `parseRaw`s and `αRR`s to a model record, then `αSection rrs`
    is non-empty too — no record is silently filtered out. Combined with `decode_*_parseRaw` (`parseRaw ≠ none`
    for every decoded RR) plus `αRR`-totality on well-typed honest RRs, this gives `αSection`-faithful empty/
    non-empty agreement, closing the malformed-answer `isReferral` gap at the honest answer terminal. -/
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
/-- **`αSection` reflects emptiness when every raw RR abstracts** (the reverse of `αSection_ne_nil`). An
    empty model section with all RRs abstracting forces an empty raw section — the honest *negative*
    terminal's bridge from `(αResp respA).answer/authority` emptiness back to the impl's raw sections (for
    the `isReferral` correspondence: model `answer.isEmpty` ⟹ impl `answer.isEmpty`). -/
theorem αSection_nil_imp {rrs : Array ByteArray}
    (hg : ∀ b ∈ rrs.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
    (h : αSection rrs = []) : rrs.toList = [] := by
  by_contra hne
  exact αSection_ne_nil hne hg h
/-- **The model query type covers the abstracted record type it matched.** If a wire qtype `bv` abstracts
    both to a model query type `qtq` (`αQType`) and to a record type `qt` (`αType`), then `qtq.covers qt`.
    `αType bv = some qt` forces `bv ≠ ANY`, so `αQType bv = .rr qt`, and `(.rr qt).covers qt = (qt == qt)`.
    The `covers`-reflexivity step of the honest answer terminal's `answersQueryB → covered-RR` glue. -/
theorem αQType_covers {bv : BitVec 16} {qtq : VeriDNS.Spec.Net.QType} {qt : RRType}
    (hq : αQType bv = some qtq) (ht : αType bv = some qt) : qtq.covers qt = true := by
  unfold αQType at hq
  split at hq
  · rename_i h255
    rw [show αType bv = none from by simp [αType, h255]] at ht
    exact absurd ht (by simp)
  · rw [ht] at hq
    simp only [Option.map_some] at hq
    injection hq with hq
    subst hq
    simp only [VeriDNS.Spec.Net.QType.covers]
    cases qt <;> rfl
/-- **Extract the record type from a non-ANY abstracted query type.** If a wire qtype abstracts to a
    model `.rr t` query type, it abstracts to record type `t` (`αQType`'s non-255 branch is `(αType).map
    .rr`). The answersQuery=true terminal is always non-ANY (an ANY query matches no record type), so this
    recovers the `αType` input that `answersQueryB_covered` needs from the `αQType` that `αQuery` provides. -/
theorem αType_of_αQType_rr {bv : BitVec 16} {t : RRType}
    (h : αQType bv = some (VeriDNS.Spec.Net.QType.rr t)) : αType bv = some t := by
  unfold αQType at h
  split at h
  · exact absurd h (by simp)
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hrr⟩ := h
    injection hrr with hrr; subst hrr; exact ha
/-- **Forward `αSection` membership**: a raw RR that `parseRaw`s and `αRR`s to a model record `r` puts `r`
    in `αSection`. The witness direction the honest answer terminal needs to lift the impl's matching answer
    record (`answersQueryB` found a `qtype` RR) into a covered record of the model answer section. -/
theorem αSection_mem {rrs : Array ByteArray} {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hb : b ∈ rrs.toList)
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (har : αRR rr = some r) : r ∈ αSection rrs := by
  unfold αSection
  rw [List.mem_filterMap]
  exact ⟨b, hb, by rw [hpr]; exact har⟩
/-- **Honest answer-terminal glue: `answersQueryB` ⟹ the model answer carries a covered record.** When the
    impl's `answersQueryB` matched a `qtype` record, the model answer section (`αSection`) contains a record
    `r` whose type the query covers — the third disjunct of the relaxed `Resolves.answer` `hnc` (and what the
    positive cname / wildcard cases need). The single lift-level input is `hvalid`: the matched RR abstracts
    (`αRR ≠ none`), which holds for a well-formed decoded honest response (`decode_*_parseRaw` + valid rdata).
    Everything else is the committed `answersQueryB_corr` + `αSection_mem` + `αRR_rtype` + `αQType_covers`. -/
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
/-- **Transfer abstracted query-type info across `questionMatches` to the response's own question.** The
    answer terminal knows `αType`/`αQType` of the *sub-query* `qb` (via `αQuery`), but `answersQueryB`
    inspects the *response's* first question `qa`. Since `acceptResponse` enforced `questionMatches` (equal
    qtype), `qa` carries the same abstractions — the question bridge `answersQueryB_covered` consumes. -/
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
/-- **`answersQueryB` + well-formedness ⟹ the queried type is handled** (`αType ≠ none`). The matched
    answer record has the query's type and abstracts (`hvalid`), so its type is one `αRData`/`αType` handle
    (`αRR_rtype`). This discharges `answersQueryB_covered`'s `αType` premise WITHOUT casing on ANY — an ANY
    query (qtype 255) would match only a type-255 record, which cannot abstract, contradicting `hvalid`. -/
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
/-- `RespAgree` transfers answer-section non-emptiness (the answer `Perm`-component). At the *positive*
    answer terminal the verdict `αResp resp` has a non-empty answer (the impl found a matching record), so
    the agreeing server response `ref` does too — hence `ref.isReferral = false` (via
    `isReferral_false_of_answer_ne_nil`) for EVERY `ServerAnswers` constructor, discharging
    `serverAnswer_hasVerdict`'s `hnr` uniformly in the `cases hans` `| _` arm. -/
theorem RespAgree.answer_ne_nil {a b : VeriDNS.Spec.Net.Response}
    (h : RespAgree a b) (hne : a.answer ≠ []) : b.answer ≠ [] := by
  intro hb
  exact hne ((hb ▸ h.2).eq_nil)
/-- **Move a covered record across `RespAgree` into the model `ref` answer.** The honest positive answer
    terminal gets a covered record in `αSection respA.answer` (from `answersQueryB_covered`); `RespAgree`'s
    answer-`Perm` carries it into `ref.answer` — supplying BOTH the relaxed `Resolves.answer` 3rd-disjunct
    `hnc` (`∃ rr ∈ ref.answer, covers …`) and (via non-emptiness) `hnr` uniformly, with NO `cases hans`. -/
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
/-- **The honest positive answer terminal carries a covered record in the model `ref` answer** — the
    relaxed `Resolves.answer` 3rd-disjunct `hnc` (and, via non-emptiness, `hnr`), UNIFORM over every
    `ServerAnswers` ctor (no `cases hans`). Packages the full bridge chain: `αQuery_fields` (the sub-query's
    `αQType = q.qtype`) + `questionMatches` (transfer to the response's question) + `answersQueryB_αType_some`
    (the queried type is handled) + `answersQueryB_covered` (covered record in `αSection respA.answer`) +
    `respAgree_covered_ref` (move it into `ref.answer`). The single un-discharged input is `hvalid` (the
    response's RRs abstract — well-formed decode), threaded from the strengthened `WorldModels`. -/
theorem positive_answer_covered {subQuery0 respA : VeriDNS.Spec.Format} {q : VeriDNS.Spec.Net.Query}
    {ref : VeriDNS.Spec.Net.Response}
    (hαQ : αQuery subQuery0 = some q)
    (hqmatch : Server.questionMatches respA.question subQuery0.question = true)
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
    have hqteq : qa.qtype = qb.qtype := by
      unfold Server.questionMatches at hqmatch
      rw [hqa, hsub] at hqmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hqmatch
      exact hqmatch.1.2
    obtain ⟨qt, hαType⟩ := answersQueryB_αType_some respA qa hqa hansI hvalidWeak
    exact respAgree_covered_ref hragA
      (answersQueryB_covered respA qa q.qtype qt hqa hαType (hqteq ▸ hαQType) hansI hvalidWeak)
/-- **An accepted reply's question matches the sent query** (the driver form). `acceptResponse` returns its
    input unchanged on success, so from `acceptResponse sent resp = some r` we get `r = resp` and then the
    `questionMatches` gate — exactly the `hqmatch` input `positive_answer_covered` needs, derived from the
    driver's `acceptResponse` case split. -/
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

/-- **A model-section NS record reflects to the impl's `hasRRTypeIn _ 2`.** If the abstracted section
    (`αSection`) contains an NS record, the raw section has an NS RR (type code 2) — the authority half of
    the honest-negative `isReferral` correspondence (model `authority.any NS` ⟹ the impl referral-guard's
    `hasRRTypeIn authority 2`). Composes `αSection`-membership inversion with `αRR_rtype` + `αType_ns_toNat`
    (re-expressed through `hasRRTypeIn_corr`). -/
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

/-- **Honest-negative correspondence: a  (negative) response is not a model referral.** At the
    answersQuery=false answer terminal the impl reached `.answer` (not the referral `.goto`), so its referral
    guard did not fire. With the faithfulness conjuncts (`hvalid`/`hvalidAuth`) making `αSection` reflect
    emptiness and NS-presence, a model `isReferral = true` would force exactly the impl guard's conditions
    (empty answer, `rcode ≠ nameError`, NS authority) — so `afterResume_referral_continues` would yield
    `.continue`, contradicting `.finished`. Hence `(αResp respA).isReferral = false`, which (via the
    WorldModels `hisref`) gives `ref.isReferral = false` for the honest-negative `serverAnswer_hasVerdict`. -/
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
    have hrteq : r.rdata.rtype = RRType.ns := by
      revert hrt; cases r.rdata.rtype <;> intro hrt <;> first | rfl | exact absurd hrt (by decide)
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

/-- **Forward `isReferral = true` bridge** (mirror of `αResp_isReferral_false_of_finished`). From the impl's
    referral-guard facts (empty answer, aa=0, NOERROR, NS in authority, no SOA) plus the authority faithfulness
    `hvalidAuth`, the model view `(αResp respA).isReferral = true`. This is what the refer-branch driver needs to
    turn the tightened guard's `goto_referral` facts into `href` (via `hisref`). -/
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
        have hsoa' : mrr.rdata.rtype = RRType.soa := by
          revert hp; cases mrr.rdata.rtype <;> intro hp <;> first | rfl | exact absurd hp (by decide)
        rw [hsoa'] at hrt; exact hrt
    rw [hcontra] at hsoa; simp at hsoa

/-- **`ServerAnswers` inversion for a referral response.** A model server answer that is `isReferral`-shaped
    comes from EITHER a zone delegation (the `referral` constructor: `bestZone = some z`, `bestDeleg z = some d`,
    `authority = d.nsSet`) OR a cached delegation (the `fromCache` constructor: `bestZone = none`,
    `authority = cachedDelegation …`). All other constructors are non-referral (aa=true, or NXDOMAIN rcode, or a
    non-empty answer). This is the disjunctive case-split the refer-branch driver needs to route to
    `serverReferForget` (zone) vs the cache-delegation path. -/
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

/--  pins the CNAME code (only wire type 5 abstracts to model `cname`). -/
theorem αType_cname_toNat {t : BitVec 16} (h : αType t = some RRType.cname) : t.toNat = 5 := by
  unfold αType at h
  split at h <;> simp_all

/-- **CNAME faithfulness: impl `extractCname = none` ⟹ model `cnameRR = none`** on the abstracted answer.
    If the impl finds no raw CNAME, the model answer section has none either (a model CNAME would come from a
    raw type-5 RR the impl would have found). The honest-negative `hnc` input (with WorldModels `hcnbi`). -/
theorem cnameRR_none_of_extractCname_none {answer : Array ByteArray}
    (h : Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) answer = none) :
    VeriDNS.Spec.Net.cnameRR (αSection answer) = none := by
  rw [VeriDNS.Spec.Net.cnameRR, List.find?_eq_none]
  intro r hr hcname
  unfold αSection at hr
  rw [List.mem_filterMap] at hr
  obtain ⟨b, hb, hmap⟩ := hr
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hmap; simp at hmap
  | some rr =>
    rw [hpr] at hmap
    have hrteq : r.rdata.rtype = RRType.cname := by
      revert hcname; cases r.rdata.rtype <;> intro hcname <;> first | rfl | exact absurd hcname (by decide)
    have h2 := αRR_rtype rr r hmap
    rw [hrteq] at h2
    have h5 : rr.type.toNat = 5 := αType_cname_toNat h2
    have htype5 : VeriDNS.Spec.RRParse.rrType rr = (5 : BitVec 16) := by
      show rr.type = (5 : BitVec 16)
      apply BitVec.eq_of_toNat_eq; simp [h5]
    rw [Resolver.extractCname, Array.findSome?_eq_none_iff] at h
    have hb' := h b (by simpa using hb)
    simp [hpr, htype5] at hb'

/-- **A type-5 RR abstracts to a model CNAME whose target is the abstracted rdata name.** Unpacks
    `αRR rr = some cn` for `rr.type = 5`: `cn.rdata = RData.cname tgt` with `tgt = αName rr.rdata`. -/
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

/-- **A type-2 RR abstracts to a model NS record whose host is the abstracted rdata name.** The NS analogue
    of `αRR_cname_target`: unpacks `αRR rr = some r` for `rr.type = 2` to `r.rdata = RData.ns host` with
    `host = αName rr.rdata`. The per-record half of the referral SLIST connector's NS-names correspondence
    (`extractNsNames`'s type-2 rdata ↔ `referredServers`'s `.ns` hosts). -/
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

/-- **A type-1 RR abstracts to a model `A` record whose address is the abstracted rdata IPv4.** The A-record
    analogue of `αRR_ns_host`: `αRR rr = some r` for `rr.type = 1` gives `r.rdata = RData.a a` with
    `a = αIPv4 rr.rdata`. The per-record bridge from a glue A record to its model `RData.a`. -/
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

/-- **Every referral-SLIST address is the dotted form of a model `A` record in the abstracted additional
    section.** The glueAddresses-compatible form of `modelSlistOf_fromNsWithGlue_model`: under decode-validity,
    each impl referral-SLIST address `s` is `a.toDotted` for a model record `r = RData.a a` in
    `αSection additional` — exactly the shape `glueAddresses` reads. The address-set ⊆ direction of step 4c,
    now in model (`αSection`/`RData.a`) terms ready for the per-host dedup `Perm` to `glueAddresses`. -/
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

/-- **NS-names correspondence (the referral SLIST connector's first half).** The impl's NS-host list
    (`extractNsNames`, abstracted name-by-name through `αName`) equals the model's `referredServers` read off
    the abstracted authority section — both filter to NS records and drop `αName`-failures, so under
    decode-validity they coincide exactly. Composes `αRR_ns_host` (per-NS-record) via `filterMap_filterMap` +
    `filterMap_congr_mem`. The `referredServers (αResp resp)` half of step 4c. -/
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

/-- **NS-names correspondence, response form** — directly `referredServers (αResp resp)`. The driver-ready
    corollary of `extractNsNames_referredServers`: the impl's abstracted NS-host list IS the model's
    `referredServers` of the abstracted response, the form the referral SLIST connector and `referral`
    constructors consume. -/
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

/-- **CNAME faithfulness, `some` direction (list form).** The first raw type-5 RR found by `extractCname`'s
    `findSome?` is exactly the first model CNAME found by `cnameRR`'s `find?` over the abstracted section —
    both skip parse-failures and non-CNAMEs, so under `hvalid` (every parsed RR abstracts) they coincide,
    and the chased raw `target` abstracts to the model CNAME's target name. -/
theorem cnameRR_some_of_extractCname {answer : Array ByteArray} {target : ByteArray}
    (h : Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) answer = some target)
    (hvalid : ∀ b ∈ answer.toList, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b
        = some rr → αRR rr ≠ none) :
    ∃ cn tgt, VeriDNS.Spec.Net.cnameRR (αSection answer) = some cn
      ∧ cn.rdata = VeriDNS.Spec.Net.RData.cname tgt ∧ αName target = some tgt := by
  unfold Resolver.extractCname at h
  rw [← Array.findSome?_toList] at h
  simp only [show ∀ rr : VeriDNS.Spec.ResourceRecord,
      VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr = rr.type from fun _ => rfl,
    show ∀ rr : VeriDNS.Spec.ResourceRecord,
      VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr = rr.rdata from fun _ => rfl] at h
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
      by_cases h5 : rr.type == (5 : BitVec 16)
      · simp only [h5, if_true] at h
        have htgt : target = rr.rdata := (Option.some.inj h).symm
        obtain ⟨tgt, hrdeq, hname⟩ := αRR_cname_target rr cn (by simpa using h5) hcn
        refine ⟨cn, tgt, ?_, hrdeq, by rw [htgt]; exact hname⟩
        have hp : (fun r : VeriDNS.Spec.Net.RR => r.rdata.rtype == RRType.cname) cn = true := by
          show (cn.rdata.rtype == RRType.cname) = true; rw [hrdeq]; rfl
        exact List.find?_cons_of_pos hp
      · simp only [h5, if_false] at h
        have hne : (cn.rdata.rtype == RRType.cname) = false := by
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
        have hnp : ¬ (fun r : VeriDNS.Spec.Net.RR => r.rdata.rtype == RRType.cname) cn = true := by
          show ¬ (cn.rdata.rtype == RRType.cname) = true; simp [hne]
        obtain ⟨cn1, tgt1, hfind1, hrd1, hnm1⟩ := ih hvalid' (by simpa using h)
        refine ⟨cn1, tgt1, ?_, hrd1, hnm1⟩
        rw [List.find?_cons_of_neg (a := cn) hnp]
        exact hfind1

/-- **Every NS name extracted from a well-formed authority section abstracts.** Under `hvalid` (every parsed
    authority RR abstracts), each `n ∈ extractNsNames authority` — being the rdata of an NS RR — has
    `αName n = some h`. Rules out `hpoint`'s malformed-NS-name edge case: a non-abstractable NS name with
    byte-matching glue would be addressed by the impl but dropped by the model (`αName`-filtered out of
    `referredServers`), breaking the slist correspondence; `hvalid` (from the codec round-trip on a decoded
    response) guarantees it cannot arise. -/
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

/-- **Decoded RR names are CANONICAL** (`rr.name = labelsToWireFormatGo (αName rr.name)`, labels ≤ 63). Because
    `ResourceRecord.decode` sets `name := labelsToWireFormat labels` (re-encoded from the decoded label array),
    a `parseRaw`-decoded name is exactly the canonical wire form of its abstraction. This discharges the
    canonicity precondition of `nameEqCI_of_αName_canonical` — the BACKWARD `nameEq → nameEqCI` direction
    `hpoint`'s per-host FIRST-match agreement needs (so a model `nameEq`-match forces the impl `nameEqCI`-match,
    making the two `find?` scans pick the SAME glue). The same canonicity that the hhit read-path needed, here
    discharged from the decode structure (not assumed). -/
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

/-- **Per-raw `CacheWf` discharge from the parse.** A raw RR that `parseRaw`s to `rr` which abstracts
    (`αRR rr` is `some` — holds for a well-formed honest response; the spoofed case is handled separately) and
    whose TTL doesn't overflow the clock yields the `CacheWf` clauses for the stored entry: it abstracts
    (`αCacheRR` is `some` = `αRR` is `some`), the expiry window is sane (`hnoov`), and the owner is canonical
    (`parseRaw_name_canonical` + `αRR_fields`: the abstraction's owner IS `αName rr.name`). This discharges the
    `hraw` hypothesis of `CacheWf_cacheRRs`/`CacheWf_cacheUnlessTruncated`, completing `CacheWf`'s `absorb`
    preservation for honest referral writes. -/
theorem parseRaw_entry_canonical {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hαRR : (αRR rr).isSome = true)
    (hnoov : (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    ((αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome = true
        ∧ rr.ttl.toNat ≤ (now + rr.ttl.toNat.toUInt32).toNat
        ∧ (now + rr.ttl.toNat.toUInt32).toNat - rr.ttl.toNat ≤ now.toNat)
      ∧ (∀ a, αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ = some a →
          rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63)) := by
  obtain ⟨na, hαN, hcanN, hsz⟩ := parseRaw_name_canonical hp
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show (αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩).isSome = true
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

/-- **`parseRaw` of an `rrWire` NS blob has CANONICAL rdata.** The codec re-encodes NS/CNAME/PTR rdata names
    (`decodeRRCanonical`), so every stored RR-blob is `rrWire ls 2 c ttl (labelsToWireFormat rdLs)` with valid
    `rdLs`. Re-parsing it (`run_resourceRecordDecode_rrWire`) returns that exact rdata, whose `αName` round-trips
    to `rdLs.toList` (canonical wire). This is the per-record `hrdcanon` the keystone's `hhost` needs — a CODEC
    guarantee (adversarial- and warm-cache-safe), stronger than the honest-disjunct NS-canonicity. The `hsz` bound
    (rdata < 65536) is the 16-bit-rdlength round-trip condition; for a decoded NS name it follows from the RFC 1035
    §2.3.4 ≤255-octet name limit (a separate hardening obligation). -/
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

/-- **A `CanonicalRR`-shaped NS record has canonical rdata.** The `CanonicalRR` invariant (every cached RR-blob
    is a `decodeRRCanonical` output) gives the `rrWire`/`ValidLabels`/≤255 decomposition for free, so an NS-typed
    record (`rr.type = 2`) parsed from such a blob has an `αName`-canonical rdata target. This is the per-record
    `hrdcanon` the keystone's `hhost`/`hnd` need — and unlike the honest-disjunct NS canonicity it holds for ANY
    cached blob (warm cache, adversarial response), since it is a pure codec guarantee. -/
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
  | @other _ _ h2 _ _ _ _ => exact absurd ht2 h2

/-- **A `CanonicalRR`-shaped CNAME record has canonical rdata** — the type-5 twin of
    `canonicalRR_nsRdata_canonical`. The `CanonicalRdata.nameType` case already covers `t = 5`
    (the ctor's disjunct `t = 2 ∨ t = 5 ∨ t = 12`); only the type-code discharges of the
    `soa`/`other` cases change. The per-record CNAME-rdata canonicity `CacheCnameCanon_absorb`
    threads through the referral cache write — a pure codec guarantee, warm-cache- and
    adversarial-response-safe. -/
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
  | @other _ _ _ h5 _ _ _ => exact absurd ht5 h5

end VeriDNS.Proof.Refinement
