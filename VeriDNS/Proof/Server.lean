import VeriDNS.Spec.Resilience
import VeriDNS.Spec.NegativeCache
import VeriDNS.Impl.Server
import VeriDNS.Impl.UdpSocket

namespace VeriDNS.Proof.Server
open VeriDNS.Spec VeriDNS.Impl.Server

theorem buildResponse_preserves_id (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).header.id = q.header.id := by
  unfold buildResponse; rfl

theorem buildResponse_sets_qr (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).header.qr = 1 := by
  unfold buildResponse; rfl

theorem buildResponse_preserves_question (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).question = q.question := by
  unfold buildResponse; rfl

theorem buildResponse_sets_rcode (q : Format) (rc : Rcode)
    (ans auth add : Array ByteArray)
    : (buildResponse q rc ans auth add).header.rcode = rc := by
  unfold buildResponse; rfl

theorem buildErrorResponse_preserves_id (q : Format) (rc : Rcode)
    : (buildErrorResponse q rc).header.id = q.header.id := by
  unfold buildErrorResponse; exact buildResponse_preserves_id q rc #[] #[] #[]

theorem truncateUdp_no_trunc (encoded : ByteArray) (msg : Format)
    (h : encoded.size ≤ 512)
    : truncateUdp encoded msg = (encoded, false) := by
  unfold truncateUdp; simp [h]

theorem truncateUdp_flag_oversized (encoded : ByteArray) (msg : Format) :
    (truncateUdp encoded msg).2 = true → 512 < encoded.size := by
  unfold truncateUdp
  split <;> rename_i h1
  · simp
  · intro _; omega

/-- **RFC 2181 §9 — TC signals loss of answer/authority data, never additional-only trimming.**
    If `truncateUdp` sets the truncation flag, the emitted message has had its **entire authority
    and additional sections removed** — i.e. the trim went strictly past the discardable additional
    section. Trimming only the additional section (which fits under 512) returns the flag `false`
    and never sets TC. This is the guarantee that closes the TC-over-truncation issue: a client is never
    forced into a (here unsupported) TCP retry merely because optional additional data was dropped. -/
theorem truncateUdp_truncated (encoded : ByteArray) (msg : Format)
    (h : (truncateUdp encoded msg).2 = true) :
    ∃ m : Format,
      truncateUdp encoded msg = (VeriDNS.Impl.Message.encode m, true) ∧
      m.header.tc = 1 ∧
      m.header.id = msg.header.id ∧
      m.question = msg.question ∧
      m.additional = #[] ∧
      m.authority = #[] ∧
      (m.answer = msg.answer ∨ m.answer = #[]) := by
  unfold truncateUdp at h ⊢
  split <;> rename_i h1
  · rw [if_pos h1] at h; simp at h
  · rw [if_neg h1] at h
    dsimp only [] at h ⊢
    split <;> rename_i h2
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h
      split <;> rename_i h3
      · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
      · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- **The additional-only trim keeps answer and authority intact and does NOT set TC.** When the
    datagram is oversized but fits once only the additional section is dropped, the emitted message
    retains the full answer and authority sections and carries the original TC bit (0 for a normal
    reply). Together with `truncateUdp_truncated` this pins the exact RFC 2181 §9 behaviour. -/
theorem truncateUdp_additional_only (encoded : ByteArray) (msg : Format)
    (h : (truncateUdp encoded msg).2 = false) (hover : ¬ encoded.size ≤ 512) :
    ∃ m : Format,
      truncateUdp encoded msg = (VeriDNS.Impl.Message.encode m, false) ∧
      m.header.tc = msg.header.tc ∧
      m.answer = msg.answer ∧
      m.authority = msg.authority ∧
      m.additional = #[] := by
  unfold truncateUdp at h ⊢
  rw [if_neg hover] at h ⊢
  dsimp only [] at h ⊢
  split <;> rename_i h2
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg h2] at h
    split at h <;> simp at h

theorem truncateUdp_size (encoded : ByteArray) (msg : Format) :
    (truncateUdp encoded msg).1.size ≤ 512 ∨
    (truncateUdp encoded msg).1 = VeriDNS.Impl.Message.encode
      { msg with
        header := { msg.header with tc := 1, arcount := 0, nscount := 0, ancount := 0 }
        answer := #[], authority := #[], additional := #[] } := by
  unfold truncateUdp
  split <;> rename_i h1
  · exact Or.inl h1
  · dsimp only []
    split <;> rename_i h2
    · exact Or.inl h2
    · split <;> rename_i h3
      · exact Or.inl h3
      · exact Or.inr rfl

theorem truncateUdp_udpusage (encoded : ByteArray) (msg : Format) :
    udpusage_prop_0 ⟨(truncateUdp encoded msg).1⟩ ∨
    (truncateUdp encoded msg).1 = VeriDNS.Impl.Message.encode
      { msg with
        header := { msg.header with tc := 1, arcount := 0, nscount := 0, ancount := 0 }
        answer := #[], authority := #[], additional := #[] } :=
  truncateUdp_size encoded msg

theorem truncateUdp_udpusage_tc (encoded : ByteArray) (msg : Format)
    (h : (truncateUdp encoded msg).2 = true) :
    ∃ m : Format, truncateUdp encoded msg = (VeriDNS.Impl.Message.encode m, true) ∧
      udpusage_prop_1 ⟨encoded⟩ m.header := by
  obtain ⟨m, heq, htc, -, -, -, -, -⟩ := truncateUdp_truncated encoded msg h
  exact ⟨m, heq, fun _ => htc⟩

theorem truncate_tc_semantics (encoded : ByteArray) (msg : Format) :
    tc_semantics_0
      (fun h => ∃ m : Format,
        truncateUdp encoded msg = (VeriDNS.Impl.Message.encode m, true) ∧
        h = m.header)
      (decide (512 < encoded.size)) := by
  rintro h ⟨m, heq, rfl⟩ _
  have hflag : (truncateUdp encoded msg).2 = true := by rw [heq]
  have hgt := truncateUdp_flag_oversized encoded msg hflag
  simpa using hgt

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

theorem finalizeForClient_z (resp : Format) :
    (finalizeForClient resp).header.z = 0 := rfl

theorem server_ra_semantics : ra_semantics_0 emittedHeader true := by
  intro h hem _hqr
  obtain ⟨resp, rfl⟩ := hem
  exact ⟨fun _ => rfl, fun _ => finalizeForClient_ra resp⟩

theorem server_aa_semantics : aa_semantics_0 emittedHeader false := by
  intro h hem _hqr haa
  obtain ⟨resp, rfl⟩ := hem
  rw [finalizeForClient_aa resp] at haa
  exact absurd haa (by decide)

theorem server_qr_semantics : qr_semantics_0 emittedHeader true := by
  intro h hem
  obtain ⟨resp, rfl⟩ := hem
  exact ⟨fun _ => rfl, fun _ => finalizeForClient_qr resp⟩

theorem emitted_z_conforms (resp : Format) :
    z_prop_0 (finalizeForClient resp).header :=
  finalizeForClient_z resp

theorem emitted_aa_conforms (resp : Format) :
    aa_prop_0 (finalizeForClient resp).header :=
  fun _ => finalizeForClient_aa resp

theorem response_id_conforms (query resp0 : Format) :
    id_prop_1 query.header
      (finalizeForClient
        { resp0 with header := { resp0.header with id := query.header.id } }).header :=
  fun _ => (finalizeForClient_id _).symm

open VeriDNS.Impl.SList in

theorem slist_recommendation :
    recommendation_addressesAvailable DnsSList
      (fun sl => sl.servers.any (·.address.isSome) || sl.servers.isEmpty)
      (fun sl => sl.addressTargets.size > 0) := by
  intro sl hfalse
  rw [Bool.or_eq_false_iff] at hfalse
  obtain ⟨hany, hne⟩ := hfalse

  rw [Array.any_eq_false] at hany
  cases Nat.eq_zero_or_pos sl.addressTargets.size with
  | inr hpos => exact hpos
  | inl hzero =>
    exfalso

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

    have htgt : sl.addressTargets = #[] := Array.size_eq_zero_iff.mp hzero
    unfold DnsSList.addressTargets at htgt
    rw [Array.filterMap_eq_empty_iff] at htgt
    have := htgt sl.servers[0] (Array.getElem_mem hsz)
    cases haddrEq : sl.servers[0].address with
    | some a => rw [haddrEq] at haddr; simp at haddr
    | none => rw [haddrEq] at this; simp at this

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

theorem accept_id_conforms (sent resp r : Format)
    (h : acceptResponse sent resp = some r) :
    algorithm_prop_1 r.header sent.header := by
  intro _
  have hid := (acceptResponse_matches sent resp r h).1
  simpa using hid

theorem exchanged_matches (queried : ByteArray) (d : Exchanged ByteArray)
    (bytes : ByteArray) (h : acceptExchanged queried d = some bytes) :
    (d.source == queried) = true ∧
    (d.destination.extract 0 4 == d.localAddr.extract 0 4) = true ∧
    (d.destination.extract 4 6 == d.localAddr.extract 4 6) = true ∧
    bytes = d.payload := by
  unfold acceptExchanged at h
  split at h
  · rename_i hcond
    unfold datagramMatches at hcond
    rw [Bool.and_eq_true, Bool.and_eq_true] at hcond
    exact ⟨hcond.1.1, hcond.1.2, hcond.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem exchanged_mismatch_dropped (queried : ByteArray) (d : Exchanged ByteArray)
    (h : datagramMatches queried d = false) :
    acceptExchanged queried d = none := by
  unfold acceptExchanged
  rw [h]
  rfl

theorem withRandomId_id (q : Format) (rid : UInt16) :
    (withRandomId q rid).header.id = VeriDNS.Impl.bv16OfUInt16 rid := rfl

theorem accept_match_obligation (sent : Format) (queried : ByteArray) :
    querymatchingrules_match_obligation (Exchanged ByteArray × Format)
      (fun p => (acceptExchanged queried p.1).isSome
        && (acceptResponse sent p.2).isSome)
      (fun p => p.1.source == queried)
      (fun p => p.1.destination.extract 0 4 == p.1.localAddr.extract 0 4)
      (fun p => p.1.destination.extract 4 6 == p.1.localAddr.extract 4 6)
      (fun p => p.2.header.id == sent.header.id)
      (fun p => questionMatches p.2.question sent.question)
      (fun p => questionMatches p.2.question sent.question) := by
  intro p hacc
  obtain ⟨d, resp⟩ := p
  rw [Bool.and_eq_true] at hacc
  obtain ⟨hd, hr⟩ := hacc

  obtain ⟨bytes, hb⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨hsrc, hdip, hdport, _⟩ := exchanged_matches queried d bytes hb

  have hcond : (resp.header.id == sent.header.id
      && questionMatches resp.question sent.question) = true := by
    cases hbq : (resp.header.id == sent.header.id
        && questionMatches resp.question sent.question) with
    | true => rfl
    | false =>
      unfold acceptResponse at hr
      rw [hbq] at hr
      simp at hr
  rw [Bool.and_eq_true] at hcond
  exact ⟨⟨⟨⟨⟨hsrc, hdip⟩, hdport⟩, hcond.1⟩, hcond.2⟩, hcond.2⟩

theorem hygiene_formatError :
    rcode_formatError_semantics Format interpretableQuery
      (fun q => queryProblem q = some Rcode.formatError) := by
  intro q h
  unfold queryProblem
  rw [h]
  rfl

theorem hygiene_notImplemented :
    rcode_notImplemented_semantics { q : Format // interpretableQuery q = true }
      (fun q => supportsQueryKind q.val)
      (fun q => queryProblem q.val = some Rcode.notImplemented) := by
  intro ⟨q, hq⟩ h
  have h' : supportsQueryKind q = false := h
  unfold queryProblem
  rw [hq, h']
  rfl

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

theorem hygiene_serverFailure (query : Format) :
    rcode_serverFailure_semantics (Except String Format)
      (fun r => r.isOk)
      (fun r => (match r with
        | .ok resp => resp
        | .error _ => buildErrorResponse query .serverFailure).header.rcode
          = Rcode.serverFailure) := by
  intro r hfail
  match r with
  | .ok _ => exact absurd (show (true : Bool) = false from hfail) (by decide)
  | .error _ =>
    show (buildErrorResponse query .serverFailure).header.rcode
      = Rcode.serverFailure
    unfold buildErrorResponse
    exact buildResponse_sets_rcode query .serverFailure #[] #[] #[]

theorem capNegativeTtl_conforms :
    cachingnegativeanswers_limit_negativeresponse_ttl (BitVec 32)
      (fun t => (capNegativeTtl t).toNat) := by
  intro t
  show (capNegativeTtl t).toNat ≤ 10800
  unfold capNegativeTtl
  split
  · assumption
  · simp [negativeTtlCap]

open VeriDNS.Impl.SList in

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

section Selection
open VeriDNS.Impl.SList

private theorem pickBest_foldl_min (l : List SlistEntry)
    (acc : Option (SlistEntry × BitVec 32)) (e : SlistEntry) (ad : BitVec 32)
    (h : l.foldl DnsSList.pickBest acc = some (e, ad)) :
    (∀ b bd, acc = some (b, bd) → e.transmissionCount ≤ b.transmissionCount) ∧
    (∀ o ∈ l, o.address.isSome = true → e.transmissionCount ≤ o.transmissionCount) := by
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
        by_cases hlt : x.transmissionCount < b.transmissionCount
        · have := hacc x xa (by unfold DnsSList.pickBest; rw [hxa]; simp [hlt])
          omega
        · exact hacc b bd (by unfold DnsSList.pickBest; rw [hxa]; simp [hlt])
    · rcases List.mem_cons.mp ho with rfl | hmem
      ·
        obtain ⟨xa, hxa⟩ := Option.isSome_iff_exists.mp hoaddr
        cases hb : acc with
        | none =>
          have := hacc o xa (by unfold DnsSList.pickBest; rw [hxa, hb])
          omega
        | some p =>
          obtain ⟨b, bd⟩ := p
          by_cases hlt : o.transmissionCount < b.transmissionCount
          · have := hacc o xa (by unfold DnsSList.pickBest; rw [hxa, hb]; simp [hlt])
            omega
          · have := hacc b bd (by unfold DnsSList.pickBest; rw [hxa, hb]; simp [hlt])
            omega
      · exact hrest o hmem hoaddr

theorem bestWithAddress_min (s : DnsSList) (e : SlistEntry) (ad : BitVec 32)
    (h : DnsSList.bestWithAddress s = some (e, ad)) :
    ∀ o ∈ s.servers, o.address.isSome = true → e.transmissionCount ≤ o.transmissionCount := by
  unfold DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  intro o ho
  exact (pickBest_foldl_min _ _ _ _ h).2 o (by simpa using ho)

def addressChosen (s : DnsSList) (a : SlistEntry) (s' : DnsSList) : Prop :=
  (∃ ad, DnsSList.bestWithAddress s = some (a, ad)) ∧ s' = s.markQueried a.name

def selectedOverLessTried (s : DnsSList) (a : SlistEntry) : Bool :=
  match DnsSList.bestWithAddress s with
  | some (e, _) =>
    e.name == a.name
      && s.servers.any fun o => o.address.isSome && o.transmissionCount < e.transmissionCount
  | none => false

theorem slist_prevent_selection :
    sendingthequeries_prevent_selection DnsSList SlistEntry
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
          (fun o => o.address.isSome && o.transmissionCount < e.transmissionCount) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨i, hi, ho⟩ := Array.any_eq_true.mp hany
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ho
        exact absurd (hmin _ (s'.servers.getElem_mem hi) ho.1) (by omega)

end Selection

private theorem not_excessive_of_mem {a : Array ByteArray} {bytes : ByteArray}
    (hany : ¬ a.any excessiveTtl = true) (hmem : bytes ∈ a) :
    excessiveTtl bytes = false := by
  cases hb : excessiveTtl bytes with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hx⟩ := Array.getElem_of_mem hmem
    exact absurd (Array.any_eq_true.mpr ⟨i, hi, hx ▸ hb⟩) hany

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

/-- **RFC-faithful drop policy for undecodable client datagrams.** The raw
    reply policy yields no reply, so a datagram that fails to decode as a DNS message is never
    answered — closing the spoofed-source reflection / fingerprinting surface that a FORMERR reply
    to garbage would open. -/
theorem rawDatagramReply_drops (queryBytes : ByteArray) :
    rawDatagramReply queryBytes = none := rfl

/-- **The undecodable-input branch of `serveOne` performs no send and leaves the cache unchanged.**
    In *any* `UdpSocket` monad, the effect run when a client datagram fails to decode is exactly
    `pure cache`: no `sendTo`, no state change. This is the operational form of the #13 guarantee —
    the resolver emits nothing in response to a datagram it cannot parse. -/
theorem serveOne_undecodable_no_reply {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (queryBytes : ByteArray) (clientSock : Sock) (clientAddr : ByteArray) (cache : VeriDNS.Impl.Cache.DnsCache) :
    ((if let some reply := rawDatagramReply queryBytes then
        VeriDNS.Spec.UdpSocket.sendTo (M := M) clientSock reply clientAddr
      else pure ()) >>= fun _ => (pure cache : M VeriDNS.Impl.Cache.DnsCache)) = pure cache := by
  simp [rawDatagramReply]

/-- **Retransmit is a no-op over a deterministic transport — the soundness-preservation argument for
    transport-layer retransmit.** `retryOption` over an action that always returns the same value collapses to
    a single attempt. The `Prog`-model `exchange` oracle used by `ioResumeLoop_sound` is exactly such
    a deterministic action (a pure function of the query bytes), so wiring `retransmitLimit` retries
    into the real `UdpSocket.exchange` cannot change the verified behaviour — retransmit buys real
    liveness (transient packet loss to a good server no longer forces premature failover) while the
    correctness proof stands untouched. -/
theorem retryOption_pure {M : Type → Type} [Monad M] [LawfulMonad M] {α : Type}
    (v : Option α) (n : Nat) :
    VeriDNS.Impl.UdpSocket.retryOption (pure v : M (Option α)) n = pure v := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold VeriDNS.Impl.UdpSocket.retryOption
    cases v with
    | none => simpa using ih
    | some a => simp

/-- **`retryOption` gives up cleanly** — over an action that always times out (`pure none`), the
    bounded retry returns `none` after exhausting its budget (it neither hangs nor loops). Instance
    of `retryOption_pure`. -/
theorem retryOption_all_timeout {M : Type → Type} [Monad M] [LawfulMonad M] {α : Type} (n : Nat) :
    VeriDNS.Impl.UdpSocket.retryOption (pure none : M (Option α)) n = pure none :=
  retryOption_pure none n

end VeriDNS.Proof.Server
