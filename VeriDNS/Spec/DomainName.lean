import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check
include_rfc [1035][533:552] {
3.1. Name space definitions

Domain names in messages are expressed in terms of a sequence of labels.
Each label is represented as a one octet length field followed by that
number of octets.  Since every domain name ends with the null label of
the root, a domain name is terminated by a length byte of zero.  The
high order two bits of every length octet must be zero, and the
remaining six bits of the length field limit the label to 63 octets or
less.

To simplify implementations, the total length of a domain name (i.e.,
label octets and label length octets) is restricted to 255 octets or
less.

Although labels can contain any 8 bit values in octets that make up a
label, it is strongly recommended that labels follow the preferred
syntax described elsewhere in this memo, which is compatible with
existing host naming conventions.  Name servers and resolvers must
compare labels in a case-insensitive manner (i.e., A=a), assuming ASCII
with zero parity.  Non-alphabetic codes must match exactly.
}
@[blueprint "NameSpace"]
structure VeriDNS.Spec.NameSpace  where
  labels : Array ByteArray
  deriving BEq, Inhabited

def VeriDNS.Spec.namespace_prop_0 : VeriDNS.Spec.NameSpace → Prop :=
  fun msg => ∀ (elem : ByteArray), elem ∈ msg.labels → elem.size ≤ 255

def VeriDNS.Spec.namespace_limit_1 : Nat :=
  255

def VeriDNS.Spec.namespace_nonalphabetic_match_exactly : (UInt8 → UInt8 → Bool) → (UInt8 → Bool) → Prop :=
  fun compare alphabetic =>
  ∀ (a b : UInt8), alphabetic a = Bool.false → alphabetic b = Bool.false → compare a b = (a == b)

def VeriDNS.Spec.namespace_compare_example : (UInt8 → UInt8 → Bool) → Prop :=
  fun compare => compare 65 97 = Bool.true

def VeriDNS.Spec.namespace_limit_0 : Nat :=
  63

def VeriDNS.Spec.namespace_compare_caseinsensitive : (α : Type) → (α → α → Bool) → (α → α) → Prop :=
  fun α compare foldCase => ∀ (a b : α), foldCase a = foldCase b → compare a b = Bool.true

def VeriDNS.Spec.namespace_casefold_exact : (UInt8 → UInt8) → Prop :=
  fun foldCase => ∀ (b : UInt8),
    (65 ≤ b.toNat ∧ b.toNat ≤ 90 → (foldCase b).toNat = b.toNat + 32) ∧
    (¬(65 ≤ b.toNat ∧ b.toNat ≤ 90) → foldCase b = b)

def VeriDNS.Spec.namespace_compare_complete : (α : Type) → (α → α → Bool) → (α → α) → Prop :=
  fun α compare foldCase => ∀ (a b : α), compare a b = Bool.true → foldCase a = foldCase b
