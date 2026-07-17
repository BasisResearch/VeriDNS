import VeriDNS.Impl.Message
import VeriDNS.Impl.ResourceRecord






namespace VeriDNS.Impl.Edns

open VeriDNS.Spec
open VeriDNS.Impl

def advertisedUdpSize : Nat := 1232

def optType : BitVec 16 := 41

def parseRR (b : ByteArray) : Option VeriDNS.Spec.ResourceRecord :=
  match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | .ok (rr, _) => some rr
  | .error _ => none

def isOptRR (b : ByteArray) : Bool :=
  match parseRR b with
  | some rr => rr.type == optType
  | none => false

def optRR (size : Nat) : VeriDNS.Spec.ResourceRecord :=
  { name := ⟨#[0]⟩
    type := optType
    «class» := BitVec.ofNat 16 size
    ttl := 0
    rdlength := 0
    rdata := ByteArray.empty }

def optRRBytes (size : Nat) : ByteArray :=
  DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode (optRR size))

def findOptSize (section_ : Array ByteArray) : Option Nat :=
  section_.findSome? fun b =>
    match parseRR b with
    | some rr => if rr.type == optType then some rr.«class».toNat else none
    | none => none

def hasOpt (q : Format) : Bool := (findOptSize q.additional).isSome

def clientCap (q : Format) : Nat :=
  match findOptSize q.additional with
  | none => 512
  | some adv => max 512 (min adv advertisedUdpSize)

theorem clientCap_le (q : Format) : clientCap q ≤ advertisedUdpSize := by
  unfold clientCap advertisedUdpSize
  split <;> omega

/-- Exact lower bound: the client cap never goes below the RFC 1035 §2.3.4
    512-octet UDP floor, no matter what buffer size the client advertises. -/
theorem clientCap_ge (q : Format) : 512 ≤ clientCap q := by
  unfold clientCap
  split <;> omega

/-- Exact characterization, no-OPT case (RFC 6891 §6.2.3): a legacy (non-EDNS)
    query is capped at exactly 512 octets. -/
theorem clientCap_noOpt (q : Format) (h : findOptSize q.additional = none) :
    clientCap q = 512 := by
  unfold clientCap
  rw [h]

/-- Exact characterization, OPT case (RFC 6891 §6.2.3/§6.2.5): an EDNS query
    advertising `adv` octets is capped at exactly `max 512 (min adv 1232)` —
    the advertised buffer, clamped below by the 512 floor and above by our own
    1232 advertised size. -/
theorem clientCap_opt (q : Format) (adv : Nat)
    (h : findOptSize q.additional = some adv) :
    clientCap q = max 512 (min adv advertisedUdpSize) := by
  unfold clientCap
  rw [h]

/-- Two-sided EDNS0 sizing spec as a single iff: the cap collapses to the 512
    floor exactly when the client is legacy (no OPT) or advertised ≤ 512. -/
theorem clientCap_eq_512_iff (q : Format) :
    clientCap q = 512 ↔
      (findOptSize q.additional = none
        ∨ ∃ adv, findOptSize q.additional = some adv ∧ adv ≤ 512) := by
  cases h : findOptSize q.additional with
  | none => simp [clientCap_noOpt q h]
  | some adv =>
    rw [clientCap_opt q adv h]
    unfold advertisedUdpSize
    constructor
    · intro he
      exact Or.inr ⟨adv, rfl, by omega⟩
    · rintro (hn | ⟨adv', heq, hle⟩)
      · exact absurd hn (by simp)
      · obtain rfl : adv' = adv := (Option.some.inj heq).symm
        omega

/-- Number of OPT RRs in a section. RFC 6891 §6.1.1 allows at most one OPT
    per message; more is a FORMERR. -/
def countOpt (section_ : Array ByteArray) : Nat :=
  (section_.filter isOptRR).size

/-- The EDNS version of the first OPT RR: bits 23–16 of the OPT TTL field
    (RFC 6891 §6.1.3: EXTENDED-RCODE (31–24) | VERSION (23–16) | DO | Z). -/
def findOptVersion (section_ : Array ByteArray) : Option Nat :=
  section_.findSome? fun b =>
    match parseRR b with
    | some rr => if rr.type == optType then some (((rr.ttl >>> 16) &&& 0xFF).toNat)
                 else none
    | none => none

/-- EDNS-level problems with a query, gated after `queryProblem`
    (RFC 6891 §6.1.1 multiple OPT → FORMERR; §6.1.3 version > 0 → BADVERS). -/
inductive EdnsProblem where
  | multiOpt
  | badVersion
  deriving Repr, DecidableEq

def ednsProblem (q : Format) : Option EdnsProblem :=
  if 2 ≤ countOpt q.additional then some .multiOpt
  else match findOptVersion q.additional with
    | some v => if v == 0 then none else some .badVersion
    | none => none

/-- The OPT RR for a BADVERS response (RFC 6891 §6.1.3): extended-RCODE high
    byte 1 (BADVERS = 16 = 1·16 + header-RCODE 0), version 0, our payload
    size. -/
def optRRBadVers (size : Nat) : VeriDNS.Spec.ResourceRecord :=
  { name := ⟨#[0]⟩
    type := optType
    «class» := BitVec.ofNat 16 size
    ttl := BitVec.ofNat 32 (1 <<< 24)
    rdlength := 0
    rdata := ByteArray.empty }

def optRRBadVersBytes (size : Nat) : ByteArray :=
  DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode (optRRBadVers size))

/-- RFC 6891 §6.1.1: a response to an EDNS query carries exactly one OPT
    (advertising our `advertisedUdpSize`); a response to a legacy query
    carries none. The reply OPT is appended *before* `truncateUdp`, so the
    cap accounting counts its 11 octets. -/
def withReplyOpt (query resp : Format) : Format :=
  if hasOpt query then
    let addl := resp.additional.push (optRRBytes advertisedUdpSize)
    { resp with
      additional := addl
      header := { resp.header with arcount := BitVec.ofNat 16 addl.size } }
  else resp

@[simp] theorem withReplyOpt_question (query resp : Format) :
    (withReplyOpt query resp).question = resp.question := by
  unfold withReplyOpt
  split <;> rfl

@[simp] theorem withReplyOpt_answer (query resp : Format) :
    (withReplyOpt query resp).answer = resp.answer := by
  unfold withReplyOpt
  split <;> rfl

@[simp] theorem withReplyOpt_authority (query resp : Format) :
    (withReplyOpt query resp).authority = resp.authority := by
  unfold withReplyOpt
  split <;> rfl

@[simp] theorem withReplyOpt_header_id (query resp : Format) :
    (withReplyOpt query resp).header.id = resp.header.id := by
  unfold withReplyOpt
  split <;> rfl

@[simp] theorem withReplyOpt_header_rcode (query resp : Format) :
    (withReplyOpt query resp).header.rcode = resp.header.rcode := by
  unfold withReplyOpt
  split <;> rfl

@[simp] theorem withReplyOpt_header_tc (query resp : Format) :
    (withReplyOpt query resp).header.tc = resp.header.tc := by
  unfold withReplyOpt
  split <;> rfl

theorem withReplyOpt_noOpt {query : Format} (resp : Format)
    (h : hasOpt query = false) : withReplyOpt query resp = resp := by
  simp [withReplyOpt, h]

theorem withReplyOpt_opt {query : Format} (resp : Format)
    (h : hasOpt query = true) :
    (withReplyOpt query resp).additional
      = resp.additional.push (optRRBytes advertisedUdpSize) := by
  simp [withReplyOpt, h]

def stripOpt (m : Format) : Format :=
  { m with
    additional := m.additional.filter fun b => !isOptRR b
    header := { m.header with
      arcount := BitVec.ofNat 16 (m.additional.filter fun b => !isOptRR b).size } }

@[simp] theorem stripOpt_answer (m : Format) : (stripOpt m).answer = m.answer := rfl
@[simp] theorem stripOpt_authority (m : Format) : (stripOpt m).authority = m.authority := rfl
@[simp] theorem stripOpt_question (m : Format) : (stripOpt m).question = m.question := rfl
@[simp] theorem stripOpt_header_id (m : Format) :
    (stripOpt m).header.id = m.header.id := rfl
@[simp] theorem stripOpt_header_qr (m : Format) :
    (stripOpt m).header.qr = m.header.qr := rfl
@[simp] theorem stripOpt_header_opcode (m : Format) :
    (stripOpt m).header.opcode = m.header.opcode := rfl
@[simp] theorem stripOpt_header_aa (m : Format) :
    (stripOpt m).header.aa = m.header.aa := rfl
@[simp] theorem stripOpt_header_tc (m : Format) :
    (stripOpt m).header.tc = m.header.tc := rfl
@[simp] theorem stripOpt_header_rd (m : Format) :
    (stripOpt m).header.rd = m.header.rd := rfl
@[simp] theorem stripOpt_header_rcode (m : Format) :
    (stripOpt m).header.rcode = m.header.rcode := rfl

theorem stripOpt_projections (m : Format) :
    (stripOpt m).header.id = m.header.id
    ∧ (stripOpt m).header.qr = m.header.qr
    ∧ (stripOpt m).header.aa = m.header.aa
    ∧ (stripOpt m).header.tc = m.header.tc
    ∧ (stripOpt m).header.rd = m.header.rd
    ∧ (stripOpt m).header.rcode = m.header.rcode
    ∧ (stripOpt m).question = m.question
    ∧ (stripOpt m).answer = m.answer
    ∧ (stripOpt m).authority = m.authority :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stripOpt_eq_self (m : Format)
    (hnone : ∀ b ∈ m.additional, isOptRR b = false)
    (harc : m.header.arcount = BitVec.ofNat 16 m.additional.size) :
    stripOpt m = m := by
  have hfilter : m.additional.filter (fun b => !isOptRR b) = m.additional := by
    apply Array.filter_eq_self.mpr
    intro b hb
    simp [hnone b hb]
  unfold stripOpt
  rw [hfilter, ← harc]

end VeriDNS.Impl.Edns
