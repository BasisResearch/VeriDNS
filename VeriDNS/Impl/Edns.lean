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
