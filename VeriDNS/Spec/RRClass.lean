import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check
include_rfc [1035][681:693] {
3.2.4. CLASS values

CLASS fields appear in resource records.  The following CLASS mnemonics
and values are defined:

IN              1 the Internet

CS              2 the CSNET class (Obsolete - used only for examples in
                some obsolete RFCs)

CH              3 the CHAOS class

HS              4 Hesiod [Dyer 87]
}include_rfc [1035][695:701] {
3.2.5. QCLASS values

QCLASS fields appear in the question section of a query.  QCLASS values
are a superset of CLASS values; every CLASS is a valid QCLASS.  In
addition to CLASS values, the following QCLASSes are defined:

*               255 any class
}
@[blueprint "RRClass"]
inductive VeriDNS.Spec.RRClass  where
  | «in» : VeriDNS.Spec.RRClass
  | cs : VeriDNS.Spec.RRClass
  | ch : VeriDNS.Spec.RRClass
  | hs : VeriDNS.Spec.RRClass
  deriving Repr, BEq, Inhabited, DecidableEq

def VeriDNS.Spec.RRClass.toCode : VeriDNS.Spec.RRClass → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.RRClass.in => 1
  | VeriDNS.Spec.RRClass.cs => 2
  | VeriDNS.Spec.RRClass.ch => 3
  | VeriDNS.Spec.RRClass.hs => 4

theorem VeriDNS.Spec.RRClass.cs_code : VeriDNS.Spec.RRClass.cs.toCode = 2 :=
  Eq.refl VeriDNS.Spec.RRClass.cs.toCode

@[blueprint "Qclass"]
inductive VeriDNS.Spec.Qclass  where
  | any : VeriDNS.Spec.Qclass
  deriving Repr, BEq, Inhabited

def VeriDNS.Spec.Qclass.ofCode : Nat → Except String VeriDNS.Spec.Qclass :=
  fun n =>
  match n with
  | 255 => Except.ok VeriDNS.Spec.Qclass.any
  | x => Except.error ("invalid qclass: " ++ ToString.toString n)

theorem VeriDNS.Spec.RRClass.hs_code : VeriDNS.Spec.RRClass.hs.toCode = 4 :=
  Eq.refl VeriDNS.Spec.RRClass.hs.toCode

def VeriDNS.Spec.RRClass.ofCode : Nat → Except String VeriDNS.Spec.RRClass :=
  fun n =>
  match n with
  | 1 => Except.ok VeriDNS.Spec.RRClass.in
  | 2 => Except.ok VeriDNS.Spec.RRClass.cs
  | 3 => Except.ok VeriDNS.Spec.RRClass.ch
  | 4 => Except.ok VeriDNS.Spec.RRClass.hs
  | x => Except.error ("invalid rrclass: " ++ ToString.toString n)

theorem VeriDNS.Spec.RRClass.ofCode_toCode : ∀ (x : VeriDNS.Spec.RRClass), VeriDNS.Spec.RRClass.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.RRClass.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.RRClass.ofCode x.toCode = Except.ok x) x
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRClass.ofCode VeriDNS.Spec.RRClass.in.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRClass.ofCode VeriDNS.Spec.RRClass.cs.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRClass.ofCode VeriDNS.Spec.RRClass.ch.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRClass.ofCode VeriDNS.Spec.RRClass.hs.toCode))
    (Eq.refl x)

def VeriDNS.Spec.Qclass.toCode : VeriDNS.Spec.Qclass → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.Qclass.any => 255

theorem VeriDNS.Spec.Qclass.any_code : VeriDNS.Spec.Qclass.any.toCode = 255 :=
  Eq.refl VeriDNS.Spec.Qclass.any.toCode

theorem VeriDNS.Spec.RRClass.ch_code : VeriDNS.Spec.RRClass.ch.toCode = 3 :=
  Eq.refl VeriDNS.Spec.RRClass.ch.toCode

theorem VeriDNS.Spec.Qclass.ofCode_toCode : ∀ (x : VeriDNS.Spec.Qclass), VeriDNS.Spec.Qclass.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.Qclass.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.Qclass.ofCode x.toCode = Except.ok x) x
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Qclass.ofCode VeriDNS.Spec.Qclass.any.toCode))
    (Eq.refl x)

theorem VeriDNS.Spec.RRClass.in_code : VeriDNS.Spec.RRClass.in.toCode = 1 :=
  Eq.refl VeriDNS.Spec.RRClass.in.toCode
