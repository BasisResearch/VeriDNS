import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check

/--
OPCODE          A four bit field that specifies kind of query in this
                message.  This value is set by the originator of a query
-/
@[blueprint "opcode", title := "Opcode (OPCODE field)"]
inductive VeriDNS.Spec.Opcode  where
  | query : VeriDNS.Spec.Opcode
  | iquery : VeriDNS.Spec.Opcode
  | status : VeriDNS.Spec.Opcode
  deriving Repr, BEq, Inhabited

check_rfc_doc VeriDNS.Spec.Opcode [1035][1431:1432]

def VeriDNS.Spec.Opcode.ofCode : Nat → Except String VeriDNS.Spec.Opcode :=
  fun n =>
  match n with
  | 0 => Except.ok VeriDNS.Spec.Opcode.query
  | 1 => Except.ok VeriDNS.Spec.Opcode.iquery
  | 2 => Except.ok VeriDNS.Spec.Opcode.status
  | x => Except.error ("invalid opcode: " ++ ToString.toString n)

def VeriDNS.Spec.Opcode.toCode : VeriDNS.Spec.Opcode → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.Opcode.query => 0
  | VeriDNS.Spec.Opcode.iquery => 1
  | VeriDNS.Spec.Opcode.status => 2

theorem VeriDNS.Spec.Opcode.ofCode_toCode : ∀ (x : VeriDNS.Spec.Opcode), VeriDNS.Spec.Opcode.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.Opcode.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.Opcode.ofCode x.toCode = Except.ok x) x
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Opcode.ofCode VeriDNS.Spec.Opcode.query.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Opcode.ofCode VeriDNS.Spec.Opcode.iquery.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Opcode.ofCode VeriDNS.Spec.Opcode.status.toCode))
    (Eq.refl x)

/--
RCODE           Response code - this 4 bit field is set as part of
                responses.  The values have the following
-/
@[blueprint "rcode", title := "Rcode (RCODE field)"]
inductive VeriDNS.Spec.Rcode  where
  | noError : VeriDNS.Spec.Rcode
  | formatError : VeriDNS.Spec.Rcode
  | serverFailure : VeriDNS.Spec.Rcode
  | nameError : VeriDNS.Spec.Rcode
  | notImplemented : VeriDNS.Spec.Rcode
  | refused : VeriDNS.Spec.Rcode
  deriving Repr, BEq, Inhabited

check_rfc_doc VeriDNS.Spec.Rcode [1035][1476:1477]

def VeriDNS.Spec.Rcode.toCode : VeriDNS.Spec.Rcode → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.Rcode.noError => 0
  | VeriDNS.Spec.Rcode.formatError => 1
  | VeriDNS.Spec.Rcode.serverFailure => 2
  | VeriDNS.Spec.Rcode.nameError => 3
  | VeriDNS.Spec.Rcode.notImplemented => 4
  | VeriDNS.Spec.Rcode.refused => 5

theorem VeriDNS.Spec.Rcode.formatError_code : VeriDNS.Spec.Rcode.formatError.toCode = 1 :=
  Eq.refl VeriDNS.Spec.Rcode.formatError.toCode

def VeriDNS.Spec.Rcode.ofCode : Nat → Except String VeriDNS.Spec.Rcode :=
  fun n =>
  match n with
  | 0 => Except.ok VeriDNS.Spec.Rcode.noError
  | 1 => Except.ok VeriDNS.Spec.Rcode.formatError
  | 2 => Except.ok VeriDNS.Spec.Rcode.serverFailure
  | 3 => Except.ok VeriDNS.Spec.Rcode.nameError
  | 4 => Except.ok VeriDNS.Spec.Rcode.notImplemented
  | 5 => Except.ok VeriDNS.Spec.Rcode.refused
  | x => Except.error ("invalid rcode: " ++ ToString.toString n)

theorem VeriDNS.Spec.Rcode.ofCode_toCode : ∀ (x : VeriDNS.Spec.Rcode), VeriDNS.Spec.Rcode.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.Rcode.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.Rcode.ofCode x.toCode = Except.ok x) x
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Rcode.ofCode VeriDNS.Spec.Rcode.noError.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Rcode.ofCode VeriDNS.Spec.Rcode.formatError.toCode))
    (fun h =>
      Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Rcode.ofCode VeriDNS.Spec.Rcode.serverFailure.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Rcode.ofCode VeriDNS.Spec.Rcode.nameError.toCode))
    (fun h =>
      Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Rcode.ofCode VeriDNS.Spec.Rcode.notImplemented.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Rcode.ofCode VeriDNS.Spec.Rcode.refused.toCode))
    (Eq.refl x)

@[blueprint "rcode_formatError_semantics"]
def VeriDNS.Spec.rcode_formatError_semantics : (σ : Type) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ interpretQuery respondsFormatError =>
  ∀ (s : σ), interpretQuery s = Bool.false → respondsFormatError s

/--
The header contains the following fields:
-/
@[blueprint "header", title := "DNS message header", uses := ["opcode", "rcode"]]
structure VeriDNS.Spec.Header  where
  id : BitVec 16
  qr : BitVec 1
  opcode : VeriDNS.Spec.Opcode
  aa : BitVec 1
  tc : BitVec 1
  rd : BitVec 1
  ra : BitVec 1
  z : BitVec 3
  rcode : VeriDNS.Spec.Rcode
  qdcount : BitVec 16
  ancount : BitVec 16
  nscount : BitVec 16
  arcount : BitVec 16
  deriving Repr, BEq, Inhabited

check_rfc_doc VeriDNS.Spec.Header [1035][1403:1403]

@[blueprint "aa_prop_0", title := "AA only in responses", uses := ["header"]]
def VeriDNS.Spec.aa_prop_0 : VeriDNS.Spec.Header → Prop :=
  fun h => h.qr = 0 → h.aa = 0

@[blueprint "rcode_refused_semantics"]
def VeriDNS.Spec.rcode_refused_semantics : (σ : Type) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ performSpecifiedOperationForPolicyReasons respondsRefused =>
  ∀ (s : σ), performSpecifiedOperationForPolicyReasons s = Bool.false → respondsRefused s

@[blueprint "ra_semantics_0"]
def VeriDNS.Spec.ra_semantics_0 : (VeriDNS.Spec.Header → Prop) → Bool → Prop :=
  fun emitted isAvailable =>
  ∀ (h : VeriDNS.Spec.Header), emitted h → h.qr = 1 → (h.ra = 1 ↔ isAvailable = Bool.true)

theorem VeriDNS.Spec.Opcode.status_code : VeriDNS.Spec.Opcode.status.toCode = 2 :=
  Eq.refl VeriDNS.Spec.Opcode.status.toCode

@[blueprint "rcode_serverFailure_semantics"]
def VeriDNS.Spec.rcode_serverFailure_semantics : (σ : Type) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ processQueryDueToProblemWithNameServer respondsServerFailure =>
  ∀ (s : σ), processQueryDueToProblemWithNameServer s = Bool.false → respondsServerFailure s

theorem VeriDNS.Spec.Rcode.refused_code : VeriDNS.Spec.Rcode.refused.toCode = 5 :=
  Eq.refl VeriDNS.Spec.Rcode.refused.toCode

theorem VeriDNS.Spec.Rcode.nameError_code : VeriDNS.Spec.Rcode.nameError.toCode = 3 :=
  Eq.refl VeriDNS.Spec.Rcode.nameError.toCode

@[blueprint "rcode_notImplemented_semantics"]
def VeriDNS.Spec.rcode_notImplemented_semantics : (σ : Type) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ supportRequestedKindOfQuery respondsNotImplemented =>
  ∀ (s : σ), supportRequestedKindOfQuery s = Bool.false → respondsNotImplemented s

@[blueprint "id_prop_1"]
def VeriDNS.Spec.id_prop_1 : VeriDNS.Spec.Header → VeriDNS.Spec.Header → Prop :=
  fun a b => a.qr = 0 ∧ b.qr = 1 → a.id = b.id

@[blueprint "z_prop_0"]
def VeriDNS.Spec.z_prop_0 : VeriDNS.Spec.Header → Prop :=
  fun h => h.z = 0

@[blueprint "rcode_nameError_semantics"]
def VeriDNS.Spec.rcode_nameError_semantics : (σ : Type) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ exist respondsNameError => ∀ (s : σ), exist s = Bool.false → respondsNameError s

theorem VeriDNS.Spec.Rcode.notImplemented_code : VeriDNS.Spec.Rcode.notImplemented.toCode = 4 :=
  Eq.refl VeriDNS.Spec.Rcode.notImplemented.toCode

theorem VeriDNS.Spec.Rcode.noError_code : VeriDNS.Spec.Rcode.noError.toCode = 0 :=
  Eq.refl VeriDNS.Spec.Rcode.noError.toCode

@[blueprint "aa_semantics_0"]
def VeriDNS.Spec.aa_semantics_0 : (VeriDNS.Spec.Header → Prop) → Bool → Prop :=
  fun emitted isAuthority =>
  ∀ (h : VeriDNS.Spec.Header), emitted h → h.qr = 1 → h.aa = 1 → isAuthority = Bool.true

@[blueprint "tc_semantics_0"]
def VeriDNS.Spec.tc_semantics_0 : (VeriDNS.Spec.Header → Prop) → Bool → Prop :=
  fun emitted isDue => ∀ (h : VeriDNS.Spec.Header), emitted h → h.tc = 1 → isDue = Bool.true

@[blueprint "qr_semantics_0"]
def VeriDNS.Spec.qr_semantics_0 : (VeriDNS.Spec.Header → Prop) → Bool → Prop :=
  fun emitted isQuery => ∀ (h : VeriDNS.Spec.Header), emitted h → (h.qr = 1 ↔ isQuery = Bool.true)

theorem VeriDNS.Spec.Opcode.query_code : VeriDNS.Spec.Opcode.query.toCode = 0 :=
  Eq.refl VeriDNS.Spec.Opcode.query.toCode

theorem VeriDNS.Spec.Rcode.serverFailure_code : VeriDNS.Spec.Rcode.serverFailure.toCode = 2 :=
  Eq.refl VeriDNS.Spec.Rcode.serverFailure.toCode

theorem VeriDNS.Spec.Opcode.iquery_code : VeriDNS.Spec.Opcode.iquery.toCode = 1 :=
  Eq.refl VeriDNS.Spec.Opcode.iquery.toCode
