import VeriDNS.Impl.Edns
import VeriDNS.Impl.Server
import VeriDNS.Proof.Message
import VeriDNS.Proof.Server

/-!
# EDNS0 sizing proofs (RFC 6891)

Cap-generic truncation theorems for `Server.truncateUdp` at an arbitrary
`cap` parameter (the serve path calls it at `Edns.clientCap query`, not the
hard-coded 512 the older theorems in `Proof/Server.lean` assume), plus the
minimal-message (header + question) size bound that makes the truncation
ladder *total*: stage 3 (header + question only) always fits any cap ≥ 512
for a served (single-question, ≤255-byte qname) query.
-/

namespace VeriDNS.Proof.Edns

open VeriDNS.Spec
open VeriDNS.Impl
open VeriDNS.Impl.Server

/-- Size of a concatenation is the sum of the sizes. -/
theorem baConcat_size : ∀ (l : List ByteArray),
    (VeriDNS.Proof.Message.baConcat l).size = (l.map ByteArray.size).sum
  | [] => rfl
  | b :: rest => by
    simp [VeriDNS.Proof.Message.baConcat_cons, ByteArray.size_append,
      baConcat_size rest]

/-- Exact size of an encoded message whose RR sections are all empty:
    12 header octets plus, per question, the qname wire plus 4 fixed octets
    (QTYPE + QCLASS). -/
theorem encode_size_of_emptyRR (msg : Format)
    (ha : msg.answer = #[]) (hn : msg.authority = #[]) (hd : msg.additional = #[]) :
    (VeriDNS.Impl.Message.encode msg).size
      = 12 + (msg.question.toList.map (fun q => q.qname.size + 4)).sum := by
  rw [VeriDNS.Proof.Message.encode_eq, ha, hn, hd]
  simp only [ByteArray.size_append, VeriDNS.Proof.Message.header_size, baConcat_size,
    Array.toList_empty, List.map_nil, List.sum_nil, ByteArray.size_empty, Nat.add_zero,
    List.map_map]
  refine congrArg (12 + ·) (congrArg List.sum (List.map_congr_left ?_))
  intro q _
  simp only [Function.comp_apply, VeriDNS.Proof.Message.question_bytes,
    ByteArray.size_append, VeriDNS.Proof.Message.tcBytes_size]

/-- **Cap-generic truncation size bound** (RFC 6891 §6.2.5 / RFC 1035 §4.2.1):
    for any cap ≥ 512, if the header + question skeleton fits in 512 octets
    (true of every served query: one question, qname ≤ 255), the truncation
    ladder delivers at most `cap` octets — never more, whatever the response. -/
theorem truncateUdp_size_cap (encoded : ByteArray) (msg : Format) (cap : Nat)
    (hcap : 512 ≤ cap)
    (hq : 12 + (msg.question.toList.map (fun q => q.qname.size + 4)).sum ≤ 512) :
    (truncateUdp encoded msg cap).1.size ≤ cap := by
  unfold truncateUdp
  split <;> rename_i h1
  · exact h1
  · dsimp only []
    split <;> rename_i h2
    · exact h2
    · split <;> rename_i h3
      · exact h3
      · rw [encode_size_of_emptyRR _ rfl rfl rfl]
        show 12 + (msg.question.toList.map (fun q => q.qname.size + 4)).sum ≤ cap
        omega

/-- **TC dual, exact iff**: the TC bit is set exactly when the full encoding
    *and* the stage-2 encoding (additional section dropped) both exceed the
    cap — i.e. truncation is flagged only when actually needed (RFC 1035
    §4.1.1 TC, RFC 6891 §7). -/
theorem truncateUdp_tc_iff (encoded : ByteArray) (msg : Format) (cap : Nat) :
    (truncateUdp encoded msg cap).2 = true ↔
      (cap < encoded.size ∧
        cap < (VeriDNS.Impl.Message.encode
          { msg with
            header := { msg.header with arcount := 0 }
            additional := #[] }).size) := by
  unfold truncateUdp
  split <;> rename_i h1
  · simp only [Bool.false_eq_true, false_iff, not_and, Nat.not_lt]
    omega
  · dsimp only []
    split <;> rename_i h2
    · simp only [Bool.false_eq_true, false_iff, not_and, Nat.not_lt]
      omega
    · split <;> rename_i h3
      · simp only [true_iff]
        omega
      · simp only [true_iff]
        omega

/-- Cap-generic version of `truncateUdp_flag_oversized`. -/
theorem truncateUdp_flag_oversized_cap (encoded : ByteArray) (msg : Format)
    (cap : Nat) (h : (truncateUdp encoded msg cap).2 = true) :
    cap < encoded.size := by
  unfold truncateUdp at h
  split at h <;> rename_i h1
  · simp at h
  · omega

/-- Cap-generic version of `truncateUdp_truncated`: a TC-flagged delivery is a
    re-encoded message with TC=1, empty additional/authority, the original id
    and question, and the answer either intact or dropped. -/
theorem truncateUdp_truncated_cap (encoded : ByteArray) (msg : Format) (cap : Nat)
    (h : (truncateUdp encoded msg cap).2 = true) :
    ∃ m : Format,
      truncateUdp encoded msg cap = (VeriDNS.Impl.Message.encode m, true) ∧
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

/-- Cap-generic version of `truncateUdp_additional_only`: an over-cap delivery
    that is *not* TC-flagged only dropped the additional section. -/
theorem truncateUdp_additional_only_cap (encoded : ByteArray) (msg : Format)
    (cap : Nat) (h : (truncateUdp encoded msg cap).2 = false)
    (hover : ¬ encoded.size ≤ cap) :
    ∃ m : Format,
      truncateUdp encoded msg cap = (VeriDNS.Impl.Message.encode m, false) ∧
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

/-! ## Served-query question skeleton bounds -/

/-- A served query (`queryProblem = none`) carries exactly one question
    (`interpretableQuery` is the first `queryProblem` gate). -/
theorem qdcount_of_queryProblem_none {q : Format}
    (h : Server.queryProblem q = none) : q.question.size = 1 := by
  by_cases h1 : Server.interpretableQuery q = true
  · have hb : (q.question.size == 1) = true := h1
    simpa using hb
  · exfalso
    unfold Server.queryProblem at h
    rw [Bool.not_eq_true] at h1
    simp [h1] at h

/-- A one-question section with head `qu` is literally `#[qu]`. -/
theorem question_singleton {q : Format} {qu : VeriDNS.Spec.Question}
    (hsz : q.question.size = 1) (hqu : q.question[0]? = some qu) :
    q.question = #[qu] := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hqu
  apply Array.ext
  · simpa using hsz
  · intro i hi₁ hi₂
    have hi0 : i = 0 := by
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hi₂
      omega
    subst hi0
    simpa using heq

/-- The header + question skeleton of a served query fits the 512 floor:
    12 (header) + qname ≤ 255 + 4 (QTYPE/QCLASS) = at most 271 octets. -/
theorem question_skeleton_le_512 {q : Format} {qu : VeriDNS.Spec.Question}
    (hqp : Server.queryProblem q = none) (hqu : q.question[0]? = some qu)
    (h255 : qu.qname.size ≤ 255) :
    12 + (q.question.toList.map (fun x => x.qname.size + 4)).sum ≤ 512 := by
  rw [question_singleton (qdcount_of_queryProblem_none hqp) hqu]
  simp
  omega

/-- `deliveredResponse` echoes the resolution response's question section. -/
theorem deliveredResponse_question (query resp : Format) :
    (Server.deliveredResponse query resp).question = resp.question := rfl

/-! ## EDNS query-problem gate pins (RFC 6891 §6.1.1, §6.1.3) -/

/-- The serve-boundary EDNS gate, as a program-rewrite lemma (generic lawful
    monad): a served-shape query with an EDNS problem is answered with
    `ednsProblemResponse` *before* any resolution, and the cache is untouched. -/
theorem serveDatagram_ednsProblem {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (clientSock : Sock) (acl : Server.ClientAcl) (sbelt : VeriDNS.Impl.SList.DnsSList)
    (cache : VeriDNS.Impl.Cache.DnsCache) (queryBytes clientAddr : ByteArray)
    (query : Format) (ep : VeriDNS.Impl.Edns.EdnsProblem)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqr : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hep : VeriDNS.Impl.Edns.ednsProblem query = some ep) :
    Server.serveDatagram (M := M) (Sock := Sock) clientSock acl sbelt cache
        queryBytes clientAddr
      = (do
          VeriDNS.Spec.UdpSocket.sendTo (M := M) clientSock
            (VeriDNS.Impl.Message.encode (Server.ednsProblemResponse query ep)) clientAddr
          pure cache) := by
  unfold Server.serveDatagram
  simp [hperm, hdec, hqp, hep]
  intro h
  exact absurd h (by simpa using hqr)

/-- **Finding 056 pin**: a multi-OPT query is answered FORMERR (RFC 6891
    §6.1.1), with the client's id echoed. -/
theorem ednsProblemResponse_multiOpt (q : Format) :
    (Server.ednsProblemResponse q .multiOpt).header.rcode = Rcode.formatError
    ∧ (Server.ednsProblemResponse q .multiOpt).header.id = q.header.id
    ∧ (Server.ednsProblemResponse q .multiOpt).header.qr = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- **Finding 065 pin**: an EDNS version > 0 query is answered BADVERS
    (RFC 6891 §6.1.3) — extended rcode 16 = header rcode NOERROR (the low 4
    bits) plus OPT TTL high byte 1 (the upper 8 bits), version 0, carried in
    exactly one OPT RR advertising our 1232-octet buffer. -/
theorem ednsProblemResponse_badVersion (q : Format) :
    (Server.ednsProblemResponse q .badVersion).header.rcode = Rcode.noError
    ∧ (Server.ednsProblemResponse q .badVersion).header.id = q.header.id
    ∧ (Server.ednsProblemResponse q .badVersion).additional
        = #[VeriDNS.Impl.Edns.optRRBadVersBytes VeriDNS.Impl.Edns.advertisedUdpSize]
    ∧ (Server.ednsProblemResponse q .badVersion).header.arcount = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The BADVERS OPT RR carries extended-rcode high byte 1 (BADVERS = 16) and
    EDNS version 0 in its TTL field (RFC 6891 §6.1.3). -/
theorem optRRBadVers_ext_rcode :
    ((VeriDNS.Impl.Edns.optRRBadVers VeriDNS.Impl.Edns.advertisedUdpSize).ttl >>> 24)
        &&& 0xFF = 1
    ∧ ((VeriDNS.Impl.Edns.optRRBadVers VeriDNS.Impl.Edns.advertisedUdpSize).ttl >>> 16)
        &&& 0xFF = 0 := by
  constructor <;> decide

/-- A query with no OPT RR in its additional section has no EDNS problem —
    the gate never fires on legacy traffic. -/
theorem ednsProblem_none_of_noOpt {q : Format}
    (h : ∀ b ∈ q.additional, VeriDNS.Impl.Edns.isOptRR b = false) :
    VeriDNS.Impl.Edns.ednsProblem q = none := by
  have hcount : VeriDNS.Impl.Edns.countOpt q.additional = 0 := by
    unfold VeriDNS.Impl.Edns.countOpt
    have : q.additional.filter VeriDNS.Impl.Edns.isOptRR = #[] := by
      rw [Array.filter_eq_empty_iff]
      intro b hb
      simp [h b hb]
    rw [this]
    rfl
  have hver : VeriDNS.Impl.Edns.findOptVersion q.additional = none := by
    unfold VeriDNS.Impl.Edns.findOptVersion
    rw [Array.findSome?_eq_none_iff]
    intro b hb
    have hopt := h b hb
    unfold VeriDNS.Impl.Edns.isOptRR at hopt
    cases hp : VeriDNS.Impl.Edns.parseRR b with
    | none => simp [hp]
    | some rr =>
      rw [hp] at hopt
      simp [hp, hopt]
  unfold VeriDNS.Impl.Edns.ednsProblem
  rw [hcount, hver]
  rfl

end VeriDNS.Proof.Edns
