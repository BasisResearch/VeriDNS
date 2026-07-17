import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check
include_rfc [1035][621:658] {
3.2.2. TYPE values

TYPE fields are used in resource records.  Note that these types are a
subset of QTYPEs.

TYPE            value and meaning

A               1 a host address

NS              2 an authoritative name server

MD              3 a mail destination (Obsolete - use MX)

MF              4 a mail forwarder (Obsolete - use MX)

CNAME           5 the canonical name for an alias

SOA             6 marks the start of a zone of authority

MB              7 a mailbox domain name (EXPERIMENTAL)

MG              8 a mail group member (EXPERIMENTAL)

MR              9 a mail rename domain name (EXPERIMENTAL)

NULL            10 a null RR (EXPERIMENTAL)

WKS             11 a well known service description

PTR             12 a domain name pointer

HINFO           13 host information

MINFO           14 mailbox or mail list information

MX              15 mail exchange

TXT             16 text strings
}include_rfc [1035][660:679] {
3.2.3. QTYPE values

QTYPE fields appear in the question part of a query.  QTYPES are a
superset of TYPEs, hence all TYPEs are valid QTYPEs.  In addition, the
following QTYPEs are defined:
AXFR            252 A request for a transfer of an entire zone

MAILB           253 A request for mailbox-related records (MB, MG or MR)

MAILA           254 A request for mail agent RRs (Obsolete - see MX)

*               255 A request for all records
}include_rfc [3597][63:83] {
2.  Definition

   An "RR of unknown type" is an RR whose RDATA format is not known to
   the DNS implementation at hand, and whose type is not an assigned
   QTYPE or Meta-TYPE as specified in [RFC 2929] (section 3.1) nor
   within the range reserved in that section for assignment only to
   QTYPEs and Meta-TYPEs.  Such an RR cannot be converted to a type-
   specific text format, compressed, or otherwise handled in a type-
   specific way.

   In the case of a type whose RDATA format is class specific, an RR is
   considered to be of unknown type when the RDATA format for that
   combination of type and class is not known.

3.  Transparency

   To enable new RR types to be deployed without server changes, name
   servers and resolvers MUST handle RRs of unknown type transparently.
   That is, they must treat the RDATA section of such RRs as
   unstructured binary data, storing and transmitting it without change
   [RFC1123].
}
/--
TYPE fields are used in resource records.  Note that these types are a
subset of QTYPEs.
-/
@[blueprint "RRType"]
inductive VeriDNS.Spec.RRType  where
  | a : VeriDNS.Spec.RRType
  | ns : VeriDNS.Spec.RRType
  | md : VeriDNS.Spec.RRType
  | mf : VeriDNS.Spec.RRType
  | cname : VeriDNS.Spec.RRType
  | soa : VeriDNS.Spec.RRType
  | mb : VeriDNS.Spec.RRType
  | mg : VeriDNS.Spec.RRType
  | mr : VeriDNS.Spec.RRType
  | null : VeriDNS.Spec.RRType
  | wks : VeriDNS.Spec.RRType
  | ptr : VeriDNS.Spec.RRType
  | hinfo : VeriDNS.Spec.RRType
  | minfo : VeriDNS.Spec.RRType
  | mx : VeriDNS.Spec.RRType
  | txt : VeriDNS.Spec.RRType
  | unknown (code : BitVec 16) : VeriDNS.Spec.RRType
  deriving Repr, BEq, Inhabited, DecidableEq

check_rfc_doc VeriDNS.Spec.RRType [1035][623:624]
rfc_proves VeriDNS.Spec.RRType [3597][63:75]

def VeriDNS.Spec.RRType.isNamed : VeriDNS.Spec.RRType → Bool
  | VeriDNS.Spec.RRType.unknown _ => false
  | _ => true

def VeriDNS.Spec.RRType.toCode : VeriDNS.Spec.RRType → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.RRType.a => 1
  | VeriDNS.Spec.RRType.ns => 2
  | VeriDNS.Spec.RRType.md => 3
  | VeriDNS.Spec.RRType.mf => 4
  | VeriDNS.Spec.RRType.cname => 5
  | VeriDNS.Spec.RRType.soa => 6
  | VeriDNS.Spec.RRType.mb => 7
  | VeriDNS.Spec.RRType.mg => 8
  | VeriDNS.Spec.RRType.mr => 9
  | VeriDNS.Spec.RRType.null => 10
  | VeriDNS.Spec.RRType.wks => 11
  | VeriDNS.Spec.RRType.ptr => 12
  | VeriDNS.Spec.RRType.hinfo => 13
  | VeriDNS.Spec.RRType.minfo => 14
  | VeriDNS.Spec.RRType.mx => 15
  | VeriDNS.Spec.RRType.txt => 16
  | VeriDNS.Spec.RRType.unknown code => code.toNat

/--
QTYPE fields appear in the question part of a query.  QTYPES are a
-/
@[blueprint "Qtype"]
inductive VeriDNS.Spec.Qtype  where
  | axfr : VeriDNS.Spec.Qtype
  | mailb : VeriDNS.Spec.Qtype
  | maila : VeriDNS.Spec.Qtype
  | any : VeriDNS.Spec.Qtype
  deriving Repr, BEq, Inhabited

check_rfc_doc VeriDNS.Spec.Qtype [1035][662:662]

def VeriDNS.Spec.Qtype.toCode : VeriDNS.Spec.Qtype → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.Qtype.axfr => 252
  | VeriDNS.Spec.Qtype.mailb => 253
  | VeriDNS.Spec.Qtype.maila => 254
  | VeriDNS.Spec.Qtype.any => 255

def VeriDNS.Spec.RRType.ofCode : Nat → Except String VeriDNS.Spec.RRType :=
  fun n =>
  match n with
  | 1 => Except.ok VeriDNS.Spec.RRType.a
  | 2 => Except.ok VeriDNS.Spec.RRType.ns
  | 3 => Except.ok VeriDNS.Spec.RRType.md
  | 4 => Except.ok VeriDNS.Spec.RRType.mf
  | 5 => Except.ok VeriDNS.Spec.RRType.cname
  | 6 => Except.ok VeriDNS.Spec.RRType.soa
  | 7 => Except.ok VeriDNS.Spec.RRType.mb
  | 8 => Except.ok VeriDNS.Spec.RRType.mg
  | 9 => Except.ok VeriDNS.Spec.RRType.mr
  | 10 => Except.ok VeriDNS.Spec.RRType.null
  | 11 => Except.ok VeriDNS.Spec.RRType.wks
  | 12 => Except.ok VeriDNS.Spec.RRType.ptr
  | 13 => Except.ok VeriDNS.Spec.RRType.hinfo
  | 14 => Except.ok VeriDNS.Spec.RRType.minfo
  | 15 => Except.ok VeriDNS.Spec.RRType.mx
  | 16 => Except.ok VeriDNS.Spec.RRType.txt
  | x => Except.error ("invalid rrtype: " ++ ToString.toString n)

def VeriDNS.Spec.Qtype.ofCode : Nat → Except String VeriDNS.Spec.Qtype :=
  fun n =>
  match n with
  | 252 => Except.ok VeriDNS.Spec.Qtype.axfr
  | 253 => Except.ok VeriDNS.Spec.Qtype.mailb
  | 254 => Except.ok VeriDNS.Spec.Qtype.maila
  | 255 => Except.ok VeriDNS.Spec.Qtype.any
  | x => Except.error ("invalid qtype: " ++ ToString.toString n)

theorem VeriDNS.Spec.RRType.ofCode_toCode :
    ∀ (x : VeriDNS.Spec.RRType), x.isNamed = true →
      VeriDNS.Spec.RRType.ofCode x.toCode = Except.ok x := by
  intro x hx
  cases x <;> first
    | rfl
    | exact absurd hx (by simp [VeriDNS.Spec.RRType.isNamed])

rfc_proves VeriDNS.Spec.RRType.ofCode_toCode [1035][628:658]

theorem VeriDNS.Spec.Qtype.ofCode_toCode : ∀ (x : VeriDNS.Spec.Qtype), VeriDNS.Spec.Qtype.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.Qtype.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.Qtype.ofCode x.toCode = Except.ok x) x
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Qtype.ofCode VeriDNS.Spec.Qtype.axfr.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Qtype.ofCode VeriDNS.Spec.Qtype.mailb.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Qtype.ofCode VeriDNS.Spec.Qtype.maila.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.Qtype.ofCode VeriDNS.Spec.Qtype.any.toCode))
    (Eq.refl x)

rfc_proves VeriDNS.Spec.Qtype.ofCode_toCode [1035][673:679]
