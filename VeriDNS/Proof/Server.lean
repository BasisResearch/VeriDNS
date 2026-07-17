import VeriDNS.Spec.Resilience
import VeriDNS.Spec.NegativeCache
import VeriDNS.Impl.Server
import VeriDNS.Impl.UdpSocket
import VeriDNS.Proof.AnswerScrub
import VeriDNS.Proof.Message
import VeriDNS.Proof.Cache

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

theorem truncateUdp_no_trunc_cap (encoded : ByteArray) (msg : Format) (cap : Nat)
    (h : encoded.size ≤ cap)
    : truncateUdp encoded msg cap = (encoded, false) := by
  unfold truncateUdp; simp [h]

theorem truncateUdp_flag_oversized (encoded : ByteArray) (msg : Format) :
    (truncateUdp encoded msg).2 = true → 512 < encoded.size := by
  unfold truncateUdp
  split <;> rename_i h1
  · simp
  · intro _; omega

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

theorem finalizeForClient_answer (resp : Format) :
    (finalizeForClient resp).answer = resp.answer := rfl

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
    simp only [Bool.and_eq_true] at hcond
    exact ⟨hcond.1.1.1, hcond.1.1.2⟩
  · exact absurd h (by simp)

/-- **Finding 030 pin (QR half).**  A datagram whose header does not carry
    QR=1 — a query, or a reflected copy of our own query — is never accepted
    as the reply to an outstanding question (RFC 1035 §4.1.1). -/
theorem accepts_requires_qr_response (sent resp : Format)
    (h : (resp.header.qr == 1) = false) :
    acceptResponse sent resp = none := by
  unfold acceptResponse
  rw [if_neg]
  intro hc
  simp only [Bool.and_eq_true] at hc
  rw [h] at hc
  exact Bool.false_ne_true hc.1.2

/-- **Finding 030 pin (OPCODE half).**  A datagram whose OPCODE is not the
    standard QUERY opcode this resolver originates (e.g. IQUERY or STATUS)
    is never accepted as the reply to an outstanding question. -/
theorem accepts_requires_opcode_query (sent resp : Format)
    (h : (resp.header.opcode == VeriDNS.Spec.Opcode.query) = false) :
    acceptResponse sent resp = none := by
  unfold acceptResponse
  rw [if_neg]
  intro hc
  simp only [Bool.and_eq_true] at hc
  rw [h] at hc
  exact Bool.false_ne_true hc.2

/-- Forward reading of the 030 pins: an accepted response carries QR=1 and
    the QUERY opcode. -/
theorem acceptResponse_qr_opcode (sent resp r : Format)
    (h : acceptResponse sent resp = some r) :
    (r.header.qr == 1) = true
      ∧ (r.header.opcode == VeriDNS.Spec.Opcode.query) = true := by
  unfold acceptResponse at h
  split at h
  · rename_i hcond
    have heq : resp = r := Option.some.inj h
    subst heq
    simp only [Bool.and_eq_true] at hcond
    exact ⟨hcond.1.2, hcond.2⟩
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

/-- The shim's transport-accept predicate for finding 017: a received datagram
    `d` is surfaced by `forwardQuery` as the reply to `sent` (queried at
    `queried`) only when it is accepted at BOTH layers — its source matches the
    queried server (`acceptExchanged`), and its decoded payload `resp` echoes
    the query's transaction id and question section (`acceptResponse`). -/
def shimAccepts (queried : ByteArray) (sent : Format)
    (d : Exchanged ByteArray) (resp : Format) : Prop :=
  ∃ bytes, acceptExchanged queried d = some bytes
    ∧ VeriDNS.Impl.Message.decode bytes = Except.ok resp
    ∧ acceptResponse sent resp = some resp

/-- Finding 017 pin, at the shim's Lean edge. If the shim accepts a datagram as
    the reply, then that datagram (a) came from the queried source and (b) its
    decoded response matches the outstanding query on transaction id and on the
    (0x20-cased) question section. Contrapositive: a datagram from the wrong
    source, or one whose content fails the id/question match, is never surfaced
    as the reply — junk from the legitimate source cannot consume the round.

    Below this edge, the C `veri_dns_exchange` recv loop is the trusted floor
    that keeps reading past a non-matching datagram until a matching reply
    arrives or the round deadline is hit (mirroring this same predicate on the
    wire). RFC 5452 §4.2–4.4: match the question, the ID, and the source
    address of the authentic response. -/
theorem shim_accept_requires_source_and_query_match
    (queried : ByteArray) (sent : Format) (d : Exchanged ByteArray) (resp : Format)
    (h : shimAccepts queried sent d resp) :
    (d.source == queried) = true
      ∧ (resp.header.id == sent.header.id) = true
      ∧ questionMatches resp.question sent.question = true := by
  obtain ⟨bytes, hexc, _hdec, hacc⟩ := h
  have hsrc := (exchanged_matches queried d bytes hexc).1
  have hmatch := acceptResponse_matches sent resp resp hacc
  exact ⟨hsrc, hmatch.1, hmatch.2⟩

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

/-- Gate (032): a TC-set query is FORMERRed. Unconditional — every classifier
    gate that can fire before the TC gate is itself a FORMERR gate, so a TC-set
    query is FORMERR no matter what else is wrong with it. -/
theorem hygiene_formatError_tc {q : Format} (h : tcClear q = false) :
    queryProblem q = some Rcode.formatError := by
  unfold queryProblem
  by_cases h1 : interpretableQuery q <;> simp [h1, h]

/-- Gate (042): a query with stuffed answer/authority (or a non-OPT additional)
    section is FORMERRed. Unconditional, as for `hygiene_formatError_tc`. -/
theorem hygiene_formatError_sections {q : Format} (h : sectionsQueryShaped q = false) :
    queryProblem q = some Rcode.formatError := by
  unfold queryProblem
  by_cases h1 : interpretableQuery q <;> by_cases h2 : tcClear q <;> simp [h1, h2, h]

theorem hygiene_notImplemented :
    rcode_notImplemented_semantics
      { q : Format // interpretableQuery q = true ∧ tcClear q = true
        ∧ sectionsQueryShaped q = true }
      (fun q => supportsQueryKind q.val)
      (fun q => queryProblem q.val = some Rcode.notImplemented) := by
  intro ⟨q, hq, htc, hsec⟩ h
  have h' : supportsQueryKind q = false := h
  show queryProblem q = some Rcode.notImplemented
  unfold queryProblem
  rw [hq, htc, hsec, h']
  rfl

theorem hygiene_refused :
    rcode_refused_semantics
      { q : Format // interpretableQuery q = true ∧ tcClear q = true
        ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = true }
      (fun q => performsRequestedOperation q.val)
      (fun q => queryProblem q.val = some Rcode.refused) := by
  intro ⟨q, hq, htc, hsec, hs⟩ h
  have h' : performsRequestedOperation q = false := h
  show queryProblem q = some Rcode.refused
  unfold queryProblem
  rw [hq, htc, hsec, hs, h']
  rfl

/-- Non-IN class rejection is RFC-correct REFUSED. A recursive resolver serves
    only Internet-class queries; declining any other class (e.g. CHAOS) is a
    local-policy decision, which RFC 1035 §4.1.1 maps to `REFUSED`. This is the
    RFC-correctness certificate for the non-IN → REFUSED serve-boundary decision
    (plan-2 Query-shape row; CHAOS). Restricted to queries that pass the earlier
    `queryProblem` gates so the class clause is the operative one. -/
theorem hygiene_refused_class :
    rcode_refused_semantics
      { q : Format // interpretableQuery q = true ∧ tcClear q = true
        ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = true
        ∧ performsRequestedOperation q = true }
      (fun q => queryClassSupported q.val)
      (fun q => queryProblem q.val = some Rcode.refused) := by
  intro ⟨q, hq, htc, hsec, hs, hp⟩ h
  have h' : queryClassSupported q = false := h
  show queryProblem q = some Rcode.refused
  unfold queryProblem
  rw [hq, htc, hsec, hs, hp, h']
  rfl

/-- Gate (044b): AXFR/IXFR from a recursive resolver with no zone to transfer is
    REFUSED (RFC 5936 §5 authority requirement; unbound parity). Stated as the
    RFC 1035 refused-semantics instance: the "operation" a zone-transfer QTYPE
    requests is one this server declines by policy. -/
theorem hygiene_refused_zoneTransfer :
    rcode_refused_semantics
      { q : Format // interpretableQuery q = true ∧ tcClear q = true
        ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = true
        ∧ performsRequestedOperation q = true ∧ queryClassSupported q = true }
      (fun q => !qtypeZoneTransfer q.val)
      (fun q => queryProblem q.val = some Rcode.refused) := by
  intro ⟨q, hq, htc, hsec, hs, hp, hc⟩ h
  have h' : qtypeZoneTransfer q = true := by simpa using h
  show queryProblem q = some Rcode.refused
  unfold queryProblem
  rw [hq, htc, hsec, hs, hp, hc, h']
  rfl

/-- Gate (044b): a meta-QTYPE question (OPT/TKEY/TSIG/MAILB/MAILA/128–248) is
    not an interpretable question — OPT is not a query type (RFC 6891 §6.1.1) —
    so it is FORMERRed (unbound parity). -/
theorem hygiene_formatError_metaQtype :
    rcode_formatError_semantics
      { q : Format // interpretableQuery q = true ∧ tcClear q = true
        ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = true
        ∧ performsRequestedOperation q = true ∧ queryClassSupported q = true
        ∧ qtypeZoneTransfer q = false }
      (fun q => !qtypeMetaQuery q.val)
      (fun q => queryProblem q.val = some Rcode.formatError) := by
  intro ⟨q, hq, htc, hsec, hs, hp, hc, hzt⟩ h
  have h' : qtypeMetaQuery q = true := by simpa using h
  show queryProblem q = some Rcode.formatError
  unfold queryProblem
  rw [hq, htc, hsec, hs, hp, hc, hzt, h']
  rfl

/-- **The unified total query-shape classifier characterization** (the one
    theorem the per-gate `hygiene_*` lemmas are corollaries of). Both an rcode
    is produced only for the listed reason (soundness) and every listed reason
    produces its rcode (completeness): a query that passes every gate is served
    (`queryProblem_none_iff`). Each disjunct is prefix-guarded by the gates that
    fire earlier in the classifier, so the disjunction is exact (pairwise
    disjoint and exhaustive over `some`). -/
theorem queryProblem_spec (q : Format) (rc : Rcode) :
    queryProblem q = some rc ↔
      ((rc = Rcode.formatError
          ∧ (interpretableQuery q = false
             ∨ (interpretableQuery q = true ∧ tcClear q = false)
             ∨ (interpretableQuery q = true ∧ tcClear q = true
                 ∧ sectionsQueryShaped q = false)
             ∨ (interpretableQuery q = true ∧ tcClear q = true
                 ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = true
                 ∧ performsRequestedOperation q = true ∧ queryClassSupported q = true
                 ∧ qtypeZoneTransfer q = false ∧ qtypeMetaQuery q = true)))
       ∨ (rc = Rcode.notImplemented
          ∧ interpretableQuery q = true ∧ tcClear q = true
          ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = false)
       ∨ (rc = Rcode.refused
          ∧ interpretableQuery q = true ∧ tcClear q = true
          ∧ sectionsQueryShaped q = true ∧ supportsQueryKind q = true
          ∧ (performsRequestedOperation q = false
             ∨ (performsRequestedOperation q = true ∧ queryClassSupported q = false)
             ∨ (performsRequestedOperation q = true ∧ queryClassSupported q = true
                 ∧ qtypeZoneTransfer q = true)))) := by
  unfold queryProblem
  cases h1 : interpretableQuery q <;> cases h2 : tcClear q
    <;> cases h3 : sectionsQueryShaped q <;> cases h4 : supportsQueryKind q
    <;> cases h5 : performsRequestedOperation q <;> cases h6 : queryClassSupported q
    <;> cases h7 : qtypeZoneTransfer q <;> cases h8 : qtypeMetaQuery q
    <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, eq_comm]

/-- Completeness half in its usable form: a query passes the classifier
    (`queryProblem = none`, i.e. is served) iff it passes EVERY gate. -/
theorem queryProblem_none_iff (q : Format) :
    queryProblem q = none ↔
      interpretableQuery q = true ∧ tcClear q = true ∧ sectionsQueryShaped q = true
        ∧ supportsQueryKind q = true ∧ performsRequestedOperation q = true
        ∧ queryClassSupported q = true ∧ qtypeZoneTransfer q = false
        ∧ qtypeMetaQuery q = false := by
  constructor
  · exact queryProblem_none_gates
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    unfold queryProblem
    rw [h1, h2, h3, h4, h5, h6, h7, h8]
    rfl

/-! ### (032) TC-bit pins: the reply's TC is the truncation flag, never an echo

Two halves. (a) `finalizeForClient` — the choke point every client-bound reply
passes — forces TC = 0, so neither the client's TC bit (query header) nor an
upstream response's TC bit survives into a reply. (b) `truncateUdp_tc_exact`:
on a TC=0 input, the wire message's TC equals `truncateUdp`'s truncation flag
exactly. Together with the `tcClear` FORMERR gate (`hygiene_formatError_tc`),
the client's TC bit is fully severed from the reply. -/

theorem finalizeForClient_tc (resp : Format) :
    (finalizeForClient resp).header.tc = 0 := rfl

theorem errorResponse_tc (query : Format) (rc : Rcode) :
    (finalizeForClient (buildErrorResponse query rc)).header.tc = 0 := rfl

theorem deliveredResponse_tc_zero (query resp : Format) :
    (deliveredResponse query resp).header.tc = 0 := rfl

theorem synthAnyResponse_tc (query : Format) :
    (synthAnyResponse query).header.tc = 0 := rfl

/-- (032)/(044a): on a reply whose pre-truncation TC is 0 (every reply, by
    `finalizeForClient_tc`), the message put on the UDP wire carries TC equal to
    the truncation flag — TC=0 when nothing (or only additional) was dropped,
    TC=1 exactly when `truncateUdp` truncated. -/
theorem truncateUdp_tc_exact (msg : Format) (cap : Nat) (htc : msg.header.tc = 0) :
    (∃ m : Format,
      truncateUdp (VeriDNS.Impl.Message.encode msg) msg cap
          = (VeriDNS.Impl.Message.encode m, false) ∧ m.header.tc = 0)
    ∨ (∃ m : Format,
      truncateUdp (VeriDNS.Impl.Message.encode msg) msg cap
          = (VeriDNS.Impl.Message.encode m, true) ∧ m.header.tc = 1) := by
  unfold truncateUdp
  split <;> rename_i h1
  · exact Or.inl ⟨msg, rfl, htc⟩
  · dsimp only []
    split <;> rename_i h2
    · exact Or.inl ⟨_, rfl, htc⟩
    · split <;> rename_i h3
      · exact Or.inr ⟨_, rfl, rfl⟩
      · exact Or.inr ⟨_, rfl, rfl⟩

/-- (032) end-to-end for the resolve path: the wire bytes `serveDatagram` sends
    for a served query are the encoding of a message whose TC bit is exactly the
    truncation flag (the delivered response enters `truncateUdp` with TC=0). -/
theorem serveReply_tc_is_truncation (query resp : Format) (cap : Nat) :
    (∃ m : Format,
      truncateUdp (VeriDNS.Impl.Message.encode (deliveredResponse query resp))
          (deliveredResponse query resp) cap
        = (VeriDNS.Impl.Message.encode m, false) ∧ m.header.tc = 0)
    ∨ (∃ m : Format,
      truncateUdp (VeriDNS.Impl.Message.encode (deliveredResponse query resp))
          (deliveredResponse query resp) cap
        = (VeriDNS.Impl.Message.encode m, true) ∧ m.header.tc = 1) :=
  truncateUdp_tc_exact _ cap rfl

/-! ### (033) FORMERR/gate-reply question-echo pins

The gate reply echoes AT MOST the first question — a multi-question query's
FORMERR does not amplify the client's stuffing — and what it does echo is the
client's own first question, with `qdcount` consistent. -/

theorem errorResponse_question (query : Format) (rc : Rcode) :
    (finalizeForClient (buildErrorResponse query rc)).question
      = query.question.extract 0 1 := rfl

theorem errorResponse_question_size_le (query : Format) (rc : Rcode) :
    (finalizeForClient (buildErrorResponse query rc)).question.size ≤ 1 := by
  rw [errorResponse_question, Array.size_extract]
  omega

theorem errorResponse_question_head (query : Format) (rc : Rcode) :
    (finalizeForClient (buildErrorResponse query rc)).question[0]?
      = query.question[0]? := by
  rw [errorResponse_question]
  cases hq : query.question[0]? with
  | none =>
    have hnone := Array.getElem?_eq_none_iff.mp hq
    rw [Array.getElem?_eq_none_iff, Array.size_extract]
    omega
  | some qu =>
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hq
    rw [Array.getElem?_eq_some_iff]
    refine ⟨by rw [Array.size_extract]; omega, ?_⟩
    rw [Array.getElem_extract]
    exact hget

theorem errorResponse_qdcount (query : Format) (rc : Rcode) :
    (finalizeForClient (buildErrorResponse query rc)).header.qdcount.toNat
      = (finalizeForClient (buildErrorResponse query rc)).question.size := by
  show (BitVec.ofNat 16 (query.question.extract 0 1).size).toNat
    = (query.question.extract 0 1).size
  rw [BitVec.toNat_ofNat]
  have hle : (query.question.extract 0 1).size ≤ 1 := by
    rw [Array.size_extract]; omega
  omega

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

theorem rawDatagramReply_headerUndecodable_drops {queryBytes : ByteArray} {e : String}
    (h : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.Header.decode queryBytes = .error e) :
    rawDatagramReply queryBytes = none := by
  unfold rawDatagramReply
  rw [h]

theorem rawDatagramReply_response_drops {queryBytes : ByteArray}
    {hd : VeriDNS.Spec.Header} {n : Nat}
    (h : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.Header.decode queryBytes = .ok (hd, n))
    (hqr : hd.qr = 1) :
    rawDatagramReply queryBytes = none := by
  unfold rawDatagramReply
  rw [h]
  simp (config := { decide := true }) [hqr]

private theorem opcode_eq_of_beq {a b : VeriDNS.Spec.Opcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem rawDatagramReply_formerr {queryBytes r : ByteArray}
    (h : rawDatagramReply queryBytes = some r) :
    ∃ hd n, VeriDNS.Impl.DnsParser.run VeriDNS.Impl.Header.decode queryBytes = .ok (hd, n) ∧
      hd.qr = 0 ∧ hd.opcode = VeriDNS.Spec.Opcode.query ∧
      r = VeriDNS.Impl.Message.encode
        { header := { hd with
                      qr := 1, aa := 0, tc := 0, ra := 1, z := 0
                      rcode := VeriDNS.Spec.Rcode.formatError
                      qdcount := 0, ancount := 0, nscount := 0, arcount := 0 }
          question := #[], answer := #[], authority := #[], additional := #[] } := by
  unfold rawDatagramReply at h
  split at h
  · exact absurd h (by simp)
  · rename_i hd n hrun
    split at h
    · rename_i hguard
      simp only [Bool.and_eq_true, beq_iff_eq] at hguard
      exact ⟨hd, n, hrun, hguard.1, opcode_eq_of_beq hguard.2, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

private theorem run_readBV16_ok_bound {buf : ByteArray} {pos pos' : Nat} {v : BitVec 16}
    (h : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.readBV16 buf pos = .ok (v, pos')) :
    pos + 1 < buf.data.size ∧ pos' = pos + 2 := by
  simp only [Primitives.run_readBV16] at h
  split at h
  · rename_i hc
    exact ⟨hc, ((Prod.mk.inj (Except.ok.inj h)).2).symm⟩
  · exact absurd h (by simp)

private theorem run_readUInt16BE_ok_bound {buf : ByteArray} {pos pos' : Nat} {v : UInt16}
    (h : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.DnsParser.readUInt16BE buf pos
      = .ok (v, pos')) :
    pos + 1 < buf.data.size ∧ pos' = pos + 2 := by
  simp only [Primitives.run_readUInt16BE] at h
  split at h
  · rename_i hc
    exact ⟨hc, ((Prod.mk.inj (Except.ok.inj h)).2).symm⟩
  · exact absurd h (by simp)

theorem headerDecode_min_size {queryBytes : ByteArray} {hd : VeriDNS.Spec.Header} {n : Nat}
    (h : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.Header.decode queryBytes = .ok (hd, n)) :
    12 ≤ queryBytes.size := by
  rw [show queryBytes.size = queryBytes.data.size from rfl]
  simp only [VeriDNS.Impl.Header.decode, Primitives.run_bind] at h
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i a1 p1 heq1
  obtain ⟨-, rfl⟩ := run_readBV16_ok_bound heq1
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i a2 p2 heq2
  obtain ⟨-, rfl⟩ := run_readUInt16BE_ok_bound heq2
  split at h
  case h_2 => simp only [Primitives.run_bind, Primitives.run_fail] at h
              exact absurd h (by simp)
  simp only [Primitives.run_bind, Primitives.run_pure] at h
  split at h
  case h_2 => simp only [Primitives.run_bind, Primitives.run_fail] at h
              exact absurd h (by simp)
  simp only [Primitives.run_bind, Primitives.run_pure] at h
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i a3 p3 heq3
  obtain ⟨-, rfl⟩ := run_readBV16_ok_bound heq3
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i a4 p4 heq4
  obtain ⟨-, rfl⟩ := run_readBV16_ok_bound heq4
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i a5 p5 heq5
  obtain ⟨-, rfl⟩ := run_readBV16_ok_bound heq5
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i a6 p6 heq6
  obtain ⟨hb, -⟩ := run_readBV16_ok_bound heq6
  omega

theorem encode_emptySections_size (hd : VeriDNS.Spec.Header) :
    (VeriDNS.Impl.Message.encode
      { header := hd, question := #[], answer := #[], authority := #[], additional := #[] }).size
      = 12 := rfl

theorem rawDatagramReply_no_amplification {queryBytes r : ByteArray}
    (h : rawDatagramReply queryBytes = some r) :
    r.size ≤ queryBytes.size := by
  obtain ⟨hd, n, hrun, _, _, rfl⟩ := rawDatagramReply_formerr h
  rw [encode_emptySections_size]
  exact headerDecode_min_size hrun

theorem serveOne_undecodable_no_reply {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    {queryBytes : ByteArray} {e : String}
    (hhdr : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.Header.decode queryBytes = .error e)
    (clientSock : Sock) (clientAddr : ByteArray) (cache : VeriDNS.Impl.Cache.DnsCache) :
    ((if let some reply := rawDatagramReply queryBytes then
        VeriDNS.Spec.UdpSocket.sendTo (M := M) clientSock reply clientAddr
      else pure ()) >>= fun _ => (pure cache : M VeriDNS.Impl.Cache.DnsCache)) = pure cache := by
  simp [rawDatagramReply_headerUndecodable_drops hhdr]



theorem permitted_nil (addr : ByteArray) : permitted [] addr = false := rfl

theorem serveDatagram_denied {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (clientSock : Sock) (acl : ClientAcl) (sbelt : VeriDNS.Impl.SList.DnsSList)
    (cache : VeriDNS.Impl.Cache.DnsCache) (queryBytes clientAddr : ByteArray)
    (h : permitted acl clientAddr = false) :
    serveDatagram (M := M) (Sock := Sock) clientSock acl sbelt cache queryBytes clientAddr
      = pure cache := by
  unfold serveDatagram
  simp [h]

theorem defaultAcl_permits_loopback :
    permitted defaultAcl ⟨#[127, 0, 0, 1, 0, 53]⟩ = true := by decide



theorem deliveredResponse_answer (query resp : Format) :
    (deliveredResponse query resp).answer =
      VeriDNS.Impl.Resolver.typeScrubB (RR := ResourceRecord) (clientQtype query)
        (VeriDNS.Impl.Resolver.scrubAnswerB (RR := ResourceRecord)
          (clientQname query) resp.answer) := by
  unfold deliveredResponse
  rw [finalizeForClient_answer]

theorem deliveredResponse_id (query resp : Format) :
    (deliveredResponse query resp).header.id = query.header.id := rfl

theorem deliveredResponse_rd (query resp : Format) :
    (deliveredResponse query resp).header.rd = query.header.rd := rfl

theorem errorResponse_rd (query : Format) (rc : Rcode) :
    (finalizeForClient (buildErrorResponse query rc)).header.rd = query.header.rd := rfl

theorem deliveredResponse_authority (query resp : Format) :
    (deliveredResponse query resp).authority =
      scrubAuthorityB (clientQname query) resp.authority := rfl

theorem deliveredResponse_authority_owned (query resp : Format) {bytes : ByteArray}
    (h : bytes ∈ (deliveredResponse query resp).authority) :
    ∃ pr : ResourceRecord × Nat,
      VeriDNS.Impl.DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes = .ok pr
      ∧ VeriDNS.Impl.Resolver.isAncestorB pr.1.name (clientQname query) = true := by
  rw [deliveredResponse_authority] at h
  unfold scrubAuthorityB at h
  have hp := (Array.mem_filter.mp h).2
  split at hp
  · next rr rest heq => exact ⟨(rr, rest), heq, hp⟩
  · exact absurd hp (by simp)

theorem deliveredResponse_additional (query resp : Format) :
    (deliveredResponse query resp).additional =
      scrubAdditionalB (clientQname query) resp.additional := rfl

/-- **047 pin (impl side)**: every record delivered in the additional section
lies in the bailiwick of the query name. An off-cut / foreign additional
record (e.g. `attacker.example` glue) is scrubbed before it reaches the
client. -/
theorem deliveredResponse_additional_inBailiwick (query resp : Format) {bytes : ByteArray}
    (h : bytes ∈ (deliveredResponse query resp).additional) :
    ∃ pr : ResourceRecord × Nat,
      VeriDNS.Impl.DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes = .ok pr
      ∧ VeriDNS.Impl.Resolver.isAncestorB (clientQname query) pr.1.name = true := by
  rw [deliveredResponse_additional] at h
  unfold scrubAdditionalB at h
  have hp := (Array.mem_filter.mp h).2
  split at hp
  · next rr rest heq => exact ⟨(rr, rest), heq, hp⟩
  · exact absurd hp (by simp)

theorem deliveredResponse_authentic (query resp : Format) {bytes' : ByteArray}
    (h : bytes' ∈ (deliveredResponse query resp).answer) :
    ∃ bytes ∈ resp.answer, ∃ (rr : ResourceRecord) (n : ByteArray),
      RRParse.parseRaw (RR := ResourceRecord) bytes = some rr
      ∧ VeriDNS.Impl.Resolver.CnameReachableB (RR := ResourceRecord) (clientQname query) resp.answer n
      ∧ VeriDNS.Impl.DomainName.nameEqCI (RRParse.rrName rr) n = true
      ∧ bytes' = VeriDNS.Impl.Resolver.setOwnerB (RR := ResourceRecord) rr bytes n := by
  rw [deliveredResponse_answer] at h
  exact VeriDNS.Impl.Resolver.scrubAnswerB_authentic (RR := ResourceRecord)
    (VeriDNS.Impl.Resolver.typeScrubB_subset h)

/-- **068 pin (delivery)**: every record in the delivered answer section has
    the client's query type, or is a CNAME chain link, or the client asked
    QTYPE=* (RFC 1034 §3.6.2).  A same-owner wrong-type record riding along
    with an entitled answer — or delivered via the truncation acceptance arm —
    never reaches the client. -/
theorem deliveredResponse_answer_qtype_relevant (query resp : Format) {bytes : ByteArray}
    (h : bytes ∈ (deliveredResponse query resp).answer) :
    ∃ rr, RRParse.parseRaw (RR := ResourceRecord) bytes = some rr
      ∧ (RRParse.rrType (RR := ResourceRecord) rr = clientQtype query
         ∨ RRParse.rrType (RR := ResourceRecord) rr = (5 : BitVec 16)
         ∨ (clientQtype query).toNat = 255) := by
  rw [deliveredResponse_answer] at h
  exact VeriDNS.Impl.Resolver.typeScrubB_relevant h

theorem replyForResolution_ok_fst {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query resp : Format) (cache' : VeriDNS.Impl.Cache.DnsCache) (nowT : UInt32) :
    SatisfiesM (fun p : Format × VeriDNS.Impl.Cache.DnsCache => p.1 = deliveredResponse query resp)
      (replyForResolution (M := M) (Sock := Sock) query (.ok resp) cache' nowT) := by
  unfold replyForResolution
  simp only []
  apply SatisfiesM.bind_pre
  apply SatisfiesM.of_true
  intro cache''
  exact SatisfiesM.pure rfl

theorem replyForResolution_ok_authentic {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query resp : Format) (cache' : VeriDNS.Impl.Cache.DnsCache) (nowT : UInt32) :
    SatisfiesM (fun p : Format × VeriDNS.Impl.Cache.DnsCache =>
        ∀ bytes' ∈ p.1.answer, ∃ bytes ∈ resp.answer, ∃ (rr : ResourceRecord) (n : ByteArray),
          RRParse.parseRaw (RR := ResourceRecord) bytes = some rr
          ∧ VeriDNS.Impl.Resolver.CnameReachableB (RR := ResourceRecord) (clientQname query)
              resp.answer n
          ∧ VeriDNS.Impl.DomainName.nameEqCI (RRParse.rrName rr) n = true
          ∧ bytes' = VeriDNS.Impl.Resolver.setOwnerB (RR := ResourceRecord) rr bytes n)
      (replyForResolution (M := M) (Sock := Sock) query (.ok resp) cache' nowT) := by
  apply SatisfiesM.imp (replyForResolution_ok_fst query resp cache' nowT)
  rintro ⟨r, c⟩ (hfst : r = deliveredResponse query resp) bytes' hbytes
  rw [hfst] at hbytes
  exact deliveredResponse_authentic query resp hbytes



theorem negativelyCacheable_truncated (resp : Format) (h : resp.header.tc = 1) :
    negativelyCacheable resp = false := by
  unfold negativelyCacheable
  rw [h]
  rfl

/-- Finding 039 (RFC 6604 §3): an NXDOMAIN carrying answer records — a
    delivered CNAME chain terminating in NXDOMAIN, with the chain prepended by
    `finalizeAnswer` — is NOT negatively cacheable.  The nonexistence it proves
    is of the CHAIN-FINAL target, not the echoed query name (which exists: it
    owns a CNAME), so a name-wide `lookupNxdomain` entry at the original qname
    can never be produced by a chained response. -/
theorem negativelyCacheable_chained_nxdomain (resp : Format)
    (hrc : resp.header.rcode = Rcode.nameError)
    (hne : resp.answer.isEmpty = false) :
    negativelyCacheable resp = false := by
  unfold negativelyCacheable
  rw [hrc, hne]
  simp

/-- Finding 039 producer gate: the serve-layer negative store is a no-op on a
    chained (nonempty-answer) NXDOMAIN. -/
theorem storeNegativeIfCacheable_chained_nxdomain {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (resp : Format) (base : VeriDNS.Impl.Cache.DnsCache) (nowT : UInt32)
    (hrc : resp.header.rcode = Rcode.nameError)
    (hne : resp.answer.isEmpty = false) :
    storeNegativeIfCacheable (M := M) (Sock := Sock) resp base nowT = pure base := by
  unfold storeNegativeIfCacheable
  simp only [negativelyCacheable_chained_nxdomain resp hrc hne, Bool.false_eq_true, if_false]

theorem storeNegativeIfCacheable_truncated {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (resp : Format) (base : VeriDNS.Impl.Cache.DnsCache) (nowT : UInt32)
    (h : resp.header.tc = 1) :
    storeNegativeIfCacheable (M := M) (Sock := Sock) resp base nowT = pure base := by
  unfold storeNegativeIfCacheable
  simp only [negativelyCacheable_truncated resp h, Bool.false_eq_true, if_false]

theorem replyForResolution_truncated_cache_unchanged {M : Type → Type} {Sock : Type} [Monad M]
    [LawfulMonad M] [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query resp : Format) (cache' : VeriDNS.Impl.Cache.DnsCache) (nowT : UInt32)
    (h : resp.header.tc = 1) :
    replyForResolution (M := M) (Sock := Sock) query (.ok resp) cache' nowT
      = pure (deliveredResponse query resp, cache') := by
  unfold replyForResolution
  simp only []
  rw [VeriDNS.Proof.Cache.truncated_cache_unchanged _ _ _ _ _ h,
    storeNegativeIfCacheable_truncated _ _ _ h, pure_bind]


theorem RateBucket.bump_over (rb : RateBucket) (ip : BitVec 32) (i : Nat)
    (hfind : rb.counts.findIdx? (fun p => p.1 == ip) = some i)
    (hc : rateWindowLimit ≤ (rb.counts.getD i (ip, 0)).2) :
    rb.bump ip = none := by
  unfold RateBucket.bump
  simp only [hfind]
  rw [if_pos hc]

theorem afterRecv_ratelimited {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (clientSock : Sock) (acl : ClientAcl) (sbelt : VeriDNS.Impl.SList.DnsSList)
    (cache : VeriDNS.Impl.Cache.DnsCache) (rb : RateBucket) (queryBytes clientAddr : ByteArray)
    (h : rb.bump (clientIp clientAddr) = none) :
    afterRecv (M := M) (Sock := Sock) clientSock acl sbelt cache rb queryBytes clientAddr
      = pure (cache, rb) := by
  unfold afterRecv
  rw [h]



section LruTouchPins
open VeriDNS.Impl.Cache VeriDNS.Impl.SList

theorem localAnswerTouches_demand (cache : DnsCache) (qtype qclass : BitVec 16)
    (now : UInt32) (fuel : Nat) (sname : ByteArray) (visited : Array ByteArray) :
    demandKey sname qtype qclass
      ∈ localAnswerTouches cache qtype qclass now (fuel + 1) sname visited := by
  unfold localAnswerTouches
  dsimp only
  repeat' split
  all_goals simp_all [Array.mem_append]

theorem localAnswerTouches_cnameProbe (cache : DnsCache) (qtype qclass : BitVec 16)
    (now : UInt32) (fuel : Nat) (sname : ByteArray) (visited : Array ByteArray)
    (hneg : NegativeCacheSpec.retrieveNegative cache sname qtype qclass now = none)
    (hempty : (TrustworthinessSpec.answers cache sname qtype qclass now
        : Array ResourceRecord).isEmpty = true)
    (hq5 : (qtype == (5 : BitVec 16)) = false) :
    demandKey sname (5 : BitVec 16) qclass
      ∈ localAnswerTouches cache qtype qclass now (fuel + 1) sname visited := by
  unfold localAnswerTouches
  dsimp only
  simp only [hneg, hempty, hq5]
  repeat' split
  all_goals simp_all [Array.mem_append]

theorem localAnswerTouches_advance (cache : DnsCache) (qtype qclass : BitVec 16)
    (now : UInt32) (fuel : Nat) (sname : ByteArray) (visited : Array ByteArray)
    {crr : ResourceRecord}
    (hneg : NegativeCacheSpec.retrieveNegative cache sname qtype qclass now = none)
    (hempty : (TrustworthinessSpec.answers cache sname qtype qclass now
        : Array ResourceRecord).isEmpty = true)
    (hq5 : (qtype == (5 : BitVec 16)) = false)
    (hcrr : (TrustworthinessSpec.answers cache sname (5 : BitVec 16) qclass now
        : Array ResourceRecord)[0]? = some crr)
    (hnv : visited.any (fun v => VeriDNS.Impl.DomainName.nameEqCI v (RRParse.rrRdata crr))
        = false) :
    ∀ k ∈ localAnswerTouches cache qtype qclass now fuel (RRParse.rrRdata crr)
        (visited.push (RRParse.rrRdata crr)),
      k ∈ localAnswerTouches cache qtype qclass now (fuel + 1) sname visited := by
  intro k hk
  unfold localAnswerTouches
  dsimp only
  simp only [hneg, hempty, hq5, hcrr, hnv]
  repeat' split
  all_goals simp_all [Array.mem_append]

theorem checkLocalTouches_eq
    (s : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    {q : Format} {qu : Question}
    (hlq : s.lastQuery = some q) (hqu : q.question[0]? = some qu) :
    checkLocalTouches s
      = localAnswerTouches s.resources.cache qu.qtype qu.qclass s.now 8 s.resources.sname
        (VeriDNS.Impl.Resolver.cnameChaseVisited (RR := ResourceRecord) qu.qname
          s.cnameChain) := by
  unfold checkLocalTouches
  simp only [hlq, hqu]

theorem walkNsTouches_demand (cache : DnsCache) (nsType inClass : BitVec 16)
    (now : UInt32) (fuel : Nat) (name : ByteArray) :
    demandKey name nsType inClass
      ∈ walkNsTouches cache nsType inClass now (fuel + 1) name := by
  unfold walkNsTouches
  dsimp only
  repeat' split
  all_goals simp_all [Array.mem_append]

theorem walkNsTouches_parent (cache : DnsCache) (nsType inClass : BitVec 16)
    (now : UInt32) (fuel : Nat) (name parent : ByteArray)
    (hempty : (CacheSpec.lookupTopCred cache name nsType inClass now
        : Array ResourceRecord).isEmpty = true)
    (hp : VeriDNS.Impl.DomainName.parentDomainWire name = some parent) :
    ∀ k ∈ walkNsTouches cache nsType inClass now fuel parent,
      k ∈ walkNsTouches cache nsType inClass now (fuel + 1) name := by
  intro k hk
  unfold walkNsTouches
  dsimp only
  simp only [hempty, hp]
  repeat' split
  all_goals simp_all [Array.mem_append]

theorem findServersTouches_walk
    (s : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) :
    ∀ k ∈ walkNsTouches s.resources.cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now
        128 s.resources.sname,
      k ∈ findServersTouches s := by
  intro k hk
  unfold findServersTouches
  dsimp only
  repeat' split
  all_goals simp_all [Array.mem_append]

theorem findServersTouches_glue
    (s : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (nsNames : Array ByteArray) (mc : Nat)
    (hwalk : VeriDNS.Impl.Resolver.stepFindServers.walkNs (C := DnsCache)
        (RR := ResourceRecord) s.resources.sname s.resources.cache (BitVec.ofNat 16 2)
        (BitVec.ofNat 16 1) s.now 128 = some (nsNames, mc))
    (hcc : (!SlistFromNameSpec.searchFails (NS := SlistEntry) s.resources.slist
        && decide (mc < SlistFromNameSpec.matchCount (NS := SlistEntry) s.resources.slist))
        = false) :
    ∀ n ∈ nsNames,
      demandKey n (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) ∈ findServersTouches s := by
  intro n hn
  unfold findServersTouches
  dsimp only
  simp only [hwalk, hcc]
  repeat' split
  all_goals simp_all [Array.mem_append, Array.mem_map]
  all_goals exact Or.inr ⟨n, hn, rfl⟩

theorem recheckTouches_demand
    (state : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    {q : Format} {qu : Question}
    (hlq : state.lastQuery = some q) (hqu : q.question[0]? = some qu) :
    demandKey state.resources.sname qu.qtype qu.qclass ∈ recheckTouches state := by
  unfold recheckTouches
  simp only [hlq, hqu]
  simp

theorem roundTouches_checkLocal
    (s s₁ : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (resp : Format)
    (hstep : VeriDNS.Impl.Resolver.stepAnalyzeResponse { s with lastResponse := some resp }
        = .goto .checkAnswer s₁) :
    ∀ k ∈ checkLocalTouches s₁, k ∈ roundTouches s resp := by
  intro k hk
  unfold roundTouches
  simp only [hstep]
  simp_all [Array.mem_append]

theorem roundTouches_postChase
    (s s₁ s₂ : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (resp : Format)
    (hstep : VeriDNS.Impl.Resolver.stepAnalyzeResponse { s with lastResponse := some resp }
        = .goto .checkAnswer s₁)
    (hstep₂ : VeriDNS.Impl.Resolver.stepCheckLocal s₁ = .goto .findServers s₂) :
    ∀ k ∈ findServersTouches s₂, k ∈ roundTouches s resp := by
  intro k hk
  unfold roundTouches
  simp only [hstep, hstep₂]
  simp_all [Array.mem_append]

theorem roundTouches_referral
    (s s₁ : VeriDNS.Impl.Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (resp : Format)
    (hstep : VeriDNS.Impl.Resolver.stepAnalyzeResponse { s with lastResponse := some resp }
        = .goto .findServers s₁) :
    ∀ k ∈ findServersTouches s₁, k ∈ roundTouches s resp := by
  intro k hk
  unfold roundTouches
  simp only [hstep]
  exact hk

end LruTouchPins

end VeriDNS.Proof.Server
