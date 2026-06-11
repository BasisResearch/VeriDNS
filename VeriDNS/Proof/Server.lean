import VeriDNS.Spec.Resilience
import VeriDNS.Spec.NegativeCache
import VeriDNS.Impl.Server

namespace VeriDNS.Proof.Server
open VeriDNS.Spec VeriDNS.Impl.Server

-- ============================================================
-- buildResponse properties
-- ============================================================

/-- buildResponse preserves the query ID. -/
theorem buildResponse_preserves_id (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).header.id = q.header.id := by
  unfold buildResponse; rfl

/-- buildResponse sets QR=1 (response flag). -/
theorem buildResponse_sets_qr (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).header.qr = 1 := by
  unfold buildResponse; rfl

/-- buildResponse preserves the question section. -/
theorem buildResponse_preserves_question (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).question = q.question := by
  unfold buildResponse; rfl

/-- buildResponse sets the specified rcode. -/
theorem buildResponse_sets_rcode (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).header.rcode = rc := by
  unfold buildResponse; rfl

/-- buildErrorResponse preserves the query ID (corollary). -/
theorem buildErrorResponse_preserves_id (q : Format) (rc : Rcode)
    : (buildErrorResponse q rc).header.id = q.header.id := by
  unfold buildErrorResponse; exact buildResponse_preserves_id q rc #[] #[] #[]

-- ============================================================
-- truncateUdp properties
-- ============================================================

/-- When encoded ≤ 512 bytes, truncateUdp returns it unchanged. -/
theorem truncateUdp_no_trunc (encoded : ByteArray) (msg : Format)
    (h : encoded.size ≤ 512)
    : truncateUdp encoded msg = (encoded, false) := by
  unfold truncateUdp; simp [h]

-- ============================================================
-- Flag hygiene: the server satisfies the NLP-generated complement
-- semantics for AA and RA (Spec/Header.lean §4.1.1)
-- ============================================================

/-- Headers this server emits to clients. -/
def emittedHeader (h : VeriDNS.Spec.Header) : Prop :=
  ∃ resp : Format, h = (finalizeForClient resp).header

theorem finalizeForClient_qr (resp : Format) :
    (finalizeForClient resp).header.qr = 1 := rfl

theorem finalizeForClient_ra (resp : Format) :
    (finalizeForClient resp).header.ra = 1 := rfl

theorem finalizeForClient_aa (resp : Format) :
    (finalizeForClient resp).header.aa = 0 := rfl

theorem finalizeForClient_id (resp : Format) :
    (finalizeForClient resp).header.id = resp.header.id := rfl

/-- RFC 1035 §4.1.1 Z "must be zero in all queries and responses": every
    emitted header carries Z = 0 (this also strips an unvalidated AD bit,
    RFC 4035 §3.2.3). -/
theorem finalizeForClient_z (resp : Format) :
    (finalizeForClient resp).header.z = 0 := rfl

/-- ra_semantics_0 ("denotes whether recursive query support is available in
    the name server"), instantiated with `isAvailable := true`: this server
    pursues queries recursively, and every emitted header has RA = 1. -/
theorem server_ra_semantics : ra_semantics_0 emittedHeader true := by
  intro h hem _hqr
  obtain ⟨resp, rfl⟩ := hem
  exact ⟨fun _ => rfl, fun _ => finalizeForClient_ra resp⟩

/-- aa_semantics_0 ("specifies that the responding name server is an authority
    for the domain name in question section"), instantiated with
    `isAuthority := false`: this server is not an authority for any zone, and
    accordingly never emits a header with AA = 1. -/
theorem server_aa_semantics : aa_semantics_0 emittedHeader false := by
  intro h hem _hqr haa
  obtain ⟨resp, rfl⟩ := hem
  rw [finalizeForClient_aa resp] at haa
  exact absurd haa (by decide)

-- ============================================================
-- Glueless NS: the SLIST satisfies the NLP-generated recommendation
-- (RFC 1034 §5.3.3 step 2: "It may be the case that the addresses are
-- not available... the best is to start parallel resolver processes
-- looking for the addresses")
-- ============================================================

open VeriDNS.Impl.SList in
/-- recommendation_addressesAvailable instantiated over DnsSList:
    `addressesAvailable := some server has an address, or there are no servers`
    (vacuously available); `lookAddresses := addressTargets is nonempty`.
    When servers exist but none has an address, there is something to look up. -/
theorem slist_recommendation :
    recommendation_addressesAvailable DnsSList
      (fun sl => sl.servers.any (·.address.isSome) || sl.servers.isEmpty)
      (fun sl => sl.addressTargets.size > 0) := by
  intro sl hfalse
  rw [Bool.or_eq_false_iff] at hfalse
  obtain ⟨hany, hne⟩ := hfalse
  -- some server exists, and every server's address is none
  rw [Array.any_eq_false] at hany
  cases Nat.eq_zero_or_pos sl.addressTargets.size with
  | inr hpos => exact hpos
  | inl hzero =>
    exfalso
    -- servers nonempty: take the first
    have hsz : 0 < sl.servers.size := by
      cases hs : sl.servers.isEmpty with
      | true => rw [hs] at hne; simp at hne
      | false =>
        cases Nat.eq_zero_or_pos sl.servers.size with
        | inl h0 =>
          have : sl.servers = #[] := Array.size_eq_zero_iff.mp h0
          rw [this] at hs; simp at hs
        | inr hp => exact hp
    have haddr := hany 0 hsz
    -- its address is none, so it appears in addressTargets
    have htgt : sl.addressTargets = #[] := Array.size_eq_zero_iff.mp hzero
    unfold DnsSList.addressTargets at htgt
    rw [Array.filterMap_eq_empty_iff] at htgt
    have := htgt sl.servers[0] (Array.getElem_mem hsz)
    cases haddrEq : sl.servers[0].address with
    | some a => rw [haddrEq] at haddr; simp at haddr
    | none => rw [haddrEq] at this; simp at this

-- ============================================================
-- RFC 5452 query matching and ID unpredictability
-- (verified text in Spec/Resilience.lean)
-- ============================================================

/-- Accepted responses match the query's ID, name, class, and type — RFC 5452
    §9.1: "A resolver implementation MUST match responses to all of the
    following attributes of the query: ... Query ID, Query name, Query class
    and type. A mismatch and the response MUST be considered invalid."
    (Source address/port matching is a socket-layer concern.) -/
theorem acceptResponse_matches (sent resp r : Format)
    (h : acceptResponse sent resp = some r) :
    (r.header.id == sent.header.id) = true ∧
    questionMatches r.question sent.question = true := by
  unfold acceptResponse at h
  split at h
  · rename_i hcond
    have heq : resp = r := Option.some.inj h
    subst heq
    simpa [Bool.and_eq_true] using hcond
  · exact absurd h (by simp)

/-- RFC 5452 §9.2: outgoing queries carry the drawn unpredictable ID
    ("Use an unpredictable query ID for outgoing queries, utilizing the
    full range available (0-65535)"). -/
theorem withRandomId_id (q : Format) (rid : UInt16) :
    (withRandomId q rid).header.id = VeriDNS.Impl.bv16OfUInt16 rid := rfl

/-- The acceptance gate satisfies the generated §9.1 matching obligation
    (`querymatchingrules_match_obligation`, derived from the MUST-match
    bullet list in Spec/Resilience.lean) for the message-level attributes:
    Query ID, Query name, Query class and type.

    The first three matchers (source address, destination address,
    destination port) are socket-layer attributes enforced below this gate by
    `UdpSocket.exchange` (Impl/UdpSocket.lean + ffi `veri_dns_exchange`):
    each upstream query runs on its own socket `connect(2)`-ed to the queried
    server, so the kernel discards any datagram whose source address/port do
    not match, and the fresh ephemeral local port is the (unpredictable)
    destination port of the response. They are therefore instantiated as
    `true` here — every datagram that reaches this gate already matches
    them. -/
theorem accept_match_obligation (sent : Format) :
    querymatchingrules_match_obligation Format
      (fun resp => (acceptResponse sent resp).isSome)
      (fun _ => true)  -- source address: kernel-enforced by connect(2)
      (fun _ => true)  -- destination address: kernel-enforced by connect(2)
      (fun _ => true)  -- destination port: per-exchange ephemeral port
      (fun resp => resp.header.id == sent.header.id)
      (fun resp => questionMatches resp.question sent.question)
      (fun resp => questionMatches resp.question sent.question) := by
  intro resp hacc
  have hcond : (resp.header.id == sent.header.id
      && questionMatches resp.question sent.question) = true := by
    cases hb : (resp.header.id == sent.header.id
        && questionMatches resp.question sent.question) with
    | true => rfl
    | false =>
      replace hacc : (acceptResponse sent resp).isSome = true := hacc
      unfold acceptResponse at hacc
      rw [hb] at hacc
      simp at hacc
  rw [Bool.and_eq_true] at hcond
  exact ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hcond.1⟩, hcond.2⟩, hcond.2⟩

-- ============================================================
-- RFC 1035 §4.1.1: RCODE use conditions (query hygiene)
-- ============================================================

/-- `queryProblem` satisfies the generated `rcode_formatError_semantics`
    ("The name server was unable to interpret the query"): an
    uninterpretable query is classified FORMERR. -/
theorem hygiene_formatError :
    rcode_formatError_semantics Format interpretableQuery
      (fun q => queryProblem q = some Rcode.formatError) := by
  intro q h
  unfold queryProblem
  rw [h]
  rfl

/-- `queryProblem` satisfies the generated `rcode_notImplemented_semantics`
    ("The name server does not support the requested kind of query") over
    interpretable queries: an unsupported kind is classified NOTIMP.
    (An uninterpretable query has no judgeable kind — it is FORMERR by
    `hygiene_formatError`.) -/
theorem hygiene_notImplemented :
    rcode_notImplemented_semantics { q : Format // interpretableQuery q = true }
      (fun q => supportsQueryKind q.val)
      (fun q => queryProblem q.val = some Rcode.notImplemented) := by
  intro ⟨q, hq⟩ h
  have h' : supportsQueryKind q = false := h
  unfold queryProblem
  rw [hq, h']
  rfl

/-- `queryProblem` satisfies the generated `rcode_refused_semantics` ("The
    name server refuses to perform the specified operation for policy
    reasons") over interpretable, supported queries: when the requested
    operation is one this recursive-only server refuses (RD=0, iterative
    service), the query is classified REFUSED. -/
theorem hygiene_refused :
    rcode_refused_semantics
      { q : Format // interpretableQuery q = true ∧ supportsQueryKind q = true }
      (fun q => performsRequestedOperation q.val)
      (fun q => queryProblem q.val = some Rcode.refused) := by
  intro ⟨q, hq, hs⟩ h
  have h' : performsRequestedOperation q = false := h
  show queryProblem q = some Rcode.refused
  unfold queryProblem
  rw [hq, hs, h']
  rfl

-- ============================================================
-- RFC 2308 §5: negative-TTL cap
-- ============================================================

/-- `capNegativeTtl` satisfies the generated
    `cachingnegativeanswers_limit_negativeresponse_ttl` ("Values of one to
    three hours have been found to work well and would make sensible a
    default"): every stored negative TTL is ≤ 10800 seconds. -/
theorem capNegativeTtl_conforms :
    cachingnegativeanswers_limit_negativeresponse_ttl (BitVec 32)
      (fun t => (capNegativeTtl t).toNat) := by
  intro t
  show (capNegativeTtl t).toNat ≤ 10800
  unfold capNegativeTtl
  split
  · assumption
  · simp [negativeTtlCap]

-- ============================================================
-- RFC 1034 §5.3.3: delegation validation
-- ============================================================

open VeriDNS.Impl.SList in
/-- Instantiation of the generated `obligation_replyIgnored` ("the resolver
    should check to see that the delegation is 'closer' ... If not, the
    reply is bogus and should be ignored"): over delegation-shaped
    responses, whenever the closeness check fails, the shim's bogus gate
    fires — the reply never reaches `resume` or the cache. -/
theorem shim_obligation_replyIgnored :
    obligation_replyIgnored
      { p : DnsSList × ByteArray × Format // delegationShapedB p.2.2 = true }
      (fun p => delegationCloserB p.val.1 p.val.2.1 p.val.2.2)
      (fun p => bogusDelegationB p.val.1 p.val.2.1 p.val.2.2 = true) := by
  intro ⟨⟨slist, sname, resp⟩, hshape⟩ hcond
  unfold bogusDelegationB
  have hc : delegationCloserB slist sname resp = false := hcond
  rw [hshape, hc]
  rfl

-- ============================================================
-- RFC 1035 §7.2: server selection (retransmission discipline)
-- ============================================================

section Selection
open VeriDNS.Impl.SList

private theorem pickBest_foldl_min (l : List ServerEntry)
    (acc : Option (ServerEntry × BitVec 32)) (e : ServerEntry) (ad : BitVec 32)
    (h : l.foldl DnsSList.pickBest acc = some (e, ad)) :
    (∀ b bd, acc = some (b, bd) → e.queryCount ≤ b.queryCount) ∧
    (∀ o ∈ l, o.address.isSome = true → e.queryCount ≤ o.queryCount) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at h
    refine ⟨fun b bd hb => ?_, fun o ho => absurd ho (List.not_mem_nil)⟩
    rw [hb] at h
    have hp := Option.some.inj h
    rw [Prod.mk.injEq] at hp
    rw [hp.1]
    exact Nat.le_refl _
  | cons x xs ih =>
    rw [List.foldl_cons] at h
    obtain ⟨hacc, hrest⟩ := ih (DnsSList.pickBest acc x) h
    refine ⟨fun b bd hb => ?_, fun o ho hoaddr => ?_⟩
    · subst hb
      cases hxa : x.address with
      | none =>
        exact hacc b bd (by unfold DnsSList.pickBest; rw [hxa])
      | some xa =>
        by_cases hlt : x.queryCount < b.queryCount
        · have := hacc x xa (by unfold DnsSList.pickBest; rw [hxa]; simp [hlt])
          omega
        · exact hacc b bd (by unfold DnsSList.pickBest; rw [hxa]; simp [hlt])
    · rcases List.mem_cons.mp ho with rfl | hmem
      · -- o = x: x carries an address, so pickBest kept x or something ≤ x
        obtain ⟨xa, hxa⟩ := Option.isSome_iff_exists.mp hoaddr
        cases hb : acc with
        | none =>
          have := hacc o xa (by unfold DnsSList.pickBest; rw [hxa, hb])
          omega
        | some p =>
          obtain ⟨b, bd⟩ := p
          by_cases hlt : o.queryCount < b.queryCount
          · have := hacc o xa (by unfold DnsSList.pickBest; rw [hxa, hb]; simp [hlt])
            omega
          · have := hacc b bd (by unfold DnsSList.pickBest; rw [hxa, hb]; simp [hlt])
            omega
      · exact hrest o hmem hoaddr

/-- `bestWithAddress` returns a least-queried addressed server. -/
theorem bestWithAddress_min (s : DnsSList) (e : ServerEntry) (ad : BitVec 32)
    (h : DnsSList.bestWithAddress s = some (e, ad)) :
    ∀ o ∈ s.servers, o.address.isSome = true → e.queryCount ≤ o.queryCount := by
  unfold DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  intro o ho
  exact (pickBest_foldl_min _ _ _ _ h).2 o (by simpa using ho)

/-- The §7.2 selection event: `a` was picked and the state altered
    (marked queried). -/
def addressChosen (s : DnsSList) (a : ServerEntry) (s' : DnsSList) : Prop :=
  (∃ ad, DnsSList.bestWithAddress s = some (a, ad)) ∧ s' = s.markQueried a.name

/-- `a` is selected even though a strictly less-tried addressed competitor
    remains — the situation §7.2 forbids ("prevent its selection again
    until all other addresses have been tried"). -/
def selectedOverLessTried (s : DnsSList) (a : ServerEntry) : Bool :=
  match DnsSList.bestWithAddress s with
  | some (e, _) =>
    e.name == a.name
      && s.servers.any fun o => o.address.isSome && o.queryCount < e.queryCount
  | none => false

/-- Instantiation of the generated `sendingthequeries_prevent_selection`:
    after an address is chosen and marked, it is never selected while an
    untried (strictly less-queried) addressed alternative remains —
    least-queried-first selection is the prevention, `markQueried` the
    state alteration, and a full cycle (all counts equal again) the
    "until all other addresses have been tried" escape that yields
    retransmission. -/
theorem slist_prevent_selection :
    sendingthequeries_prevent_selection DnsSList ServerEntry
      addressChosen selectedOverLessTried := by
  intro s a s' _hev
  unfold selectedOverLessTried
  cases hb : DnsSList.bestWithAddress s' with
  | none => rfl
  | some p =>
    obtain ⟨e, ad⟩ := p
    dsimp only
    have hmin := bestWithAddress_min s' e ad hb
    cases hn : (e.name == a.name) with
    | false => rfl
    | true =>
      rw [Bool.true_and]
      cases hany : s'.servers.any
          (fun o => o.address.isSome && o.queryCount < e.queryCount) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨i, hi, ho⟩ := Array.any_eq_true.mp hany
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ho
        exact absurd (hmin _ (s'.servers.getElem_mem hi) ho.1) (by omega)

end Selection

-- ============================================================
-- RFC 1035 §7.3: TTL sanity
-- ============================================================

private theorem not_excessive_of_mem {a : Array ByteArray} {bytes : ByteArray}
    (hany : ¬ a.any excessiveTtl = true) (hmem : bytes ∈ a) :
    excessiveTtl bytes = false := by
  cases hb : excessiveTtl bytes with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hx⟩ := Array.getElem_of_mem hmem
    exact absurd (Array.any_eq_true.mpr ⟨i, hi, hx ▸ hb⟩) hany

/-- `sanitizeTtls` satisfies the generated `processingresponses_limit_ttls`
    ("either discard the whole response, or limit all TTLs in the response
    to 1 week"): a kept response carries no RR with TTL > 604800. -/
theorem sanitize_limit_ttls :
    processingresponses_limit_ttls ResourceRecord
      (RRParse.parseRaw (RR := ResourceRecord))
      (fun rr => rr.ttl.toNat)
      sanitizeTtls := by
  intro resp resp' hp bytes hmem rr hparse
  unfold sanitizeTtls at hp
  split at hp
  · exact absurd hp (by simp)
  · rename_i hex
    have hr : resp = resp' := Option.some.inj hp
    subst hr
    simp only [Bool.or_eq_true, not_or] at hex
    obtain ⟨⟨h1, h2⟩, h3⟩ := hex
    have hbad : excessiveTtl bytes = false := by
      rcases hmem with (hm | hm) | hm
      · exact not_excessive_of_mem h1 hm
      · exact not_excessive_of_mem h2 hm
      · exact not_excessive_of_mem h3 hm
    unfold excessiveTtl at hbad
    rw [hparse] at hbad
    simpa using hbad

end VeriDNS.Proof.Server
