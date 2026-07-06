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
  deriving Repr, BEq, Inhabited, DecidableEq

check_rfc_doc VeriDNS.Spec.RRType [1035][623:624]

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

/-- The TYPE-value assignments of RFC 1035 §3.2.2 are faithfully modelled: every
`RRType` encodes to its assigned wire code and decodes back to itself (total
round-trip over exactly the codes in the table). -/
theorem VeriDNS.Spec.RRType.ofCode_toCode : ∀ (x : VeriDNS.Spec.RRType), VeriDNS.Spec.RRType.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.RRType.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.RRType.ofCode x.toCode = Except.ok x) x
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.a.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.ns.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.md.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.mf.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.cname.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.soa.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.mb.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.mg.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.mr.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.null.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.wks.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.ptr.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.hinfo.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.minfo.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.mx.toCode))
    (fun h => Eq.symm h ▸ Eq.refl (VeriDNS.Spec.RRType.ofCode VeriDNS.Spec.RRType.txt.toCode))
    (Eq.refl x)

rfc_proves VeriDNS.Spec.RRType.ofCode_toCode [1035][628:658]

/-- The QTYPE-value assignments of RFC 1035 §3.2.3 are faithfully modelled: every
`Qtype` encodes to its assigned wire code and decodes back to itself. -/
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
