import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Resolver
import VeriDNS.RFC.Check
include_rfc [2181][343:384] {
5.4.1. Ranking data

   When considering whether to accept an RRSet in a reply, or retain an
   RRSet already in its cache instead, a server should consider the
   relative likely trustworthiness of the various data.  An
   authoritative answer from a reply should replace cached data that had
   been obtained from additional information in an earlier reply.
   However additional information from a reply will be ignored if the
   cache contains data from an authoritative answer or a zone file.

   The accuracy of data available is assumed from its source.
   Trustworthiness shall be, in order from most to least:

     + Data from a primary zone file, other than glue data,
     + Data from a zone transfer, other than glue,
     + The authoritative data included in the answer section of an
       authoritative reply.
     + Data from the authority section of an authoritative answer,
     + Glue from a primary zone, or glue from a zone transfer,
     + Data from the answer section of a non-authoritative answer, and
       non-authoritative data from the answer section of authoritative
       answers,
     + Additional information from an authoritative answer,
       Data from the authority section of a non-authoritative answer,
       Additional information from non-authoritative answers.

   Note that the answer section of an authoritative answer normally
   contains only authoritative data.  However when the name sought is an
   alias (see section 10.1.1) only the record describing that alias is
   necessarily authoritative.  Clients should assume that other records
   may have come from the server's cache.  Where authoritative answers
   are required, the client should query again, using the canonical name
   associated with the alias.

   Unauthenticated RRs received and cached from the least trustworthy of
   those groupings, that is data from the additional data section, and
   data from the authority section of a non-authoritative answer, should
   not be cached in such a way that they would ever be returned as
   answers to a received query.  They may be returned as additional
   information where appropriate.  Ignoring this would allow the
   trustworthiness of relatively untrustworthy data to be increased
   without cause or excuse.
}





/--
5.4.1. Ranking data

   When considering whether to accept an RRSet in a reply, or retain an
   RRSet already in its cache instead, a server should consider the
   relative likely trustworthiness of the various data.  An
   authoritative answer from a reply should replace cached data that had
   been obtained from additional information in an earlier reply.
   However additional information from a reply will be ignored if the
   cache contains data from an authoritative answer or a zone file.

   The accuracy of data available is assumed from its source.
   Trustworthiness shall be, in order from most to least:

     + Data from a primary zone file, other than glue data,
     + Data from a zone transfer, other than glue,
     + The authoritative data included in the answer section of an
       authoritative reply.
     + Data from the authority section of an authoritative answer,
     + Glue from a primary zone, or glue from a zone transfer,
     + Data from the answer section of a non-authoritative answer, and
       non-authoritative data from the answer section of authoritative
       answers,
     + Additional information from an authoritative answer,
       Data from the authority section of a non-authoritative answer,
       Additional information from non-authoritative answers.

   Note that the answer section of an authoritative answer normally
   contains only authoritative data.  However when the name sought is an
   alias (see section 10.1.1) only the record describing that alias is
   necessarily authoritative.  Clients should assume that other records
   may have come from the server's cache.  Where authoritative answers
   are required, the client should query again, using the canonical name
   associated with the alias.

-/
@[blueprint "Trustworthiness"]
inductive VeriDNS.Spec.Trustworthiness  where
  | primaryZone : VeriDNS.Spec.Trustworthiness
  | zoneTransfer : VeriDNS.Spec.Trustworthiness
  | authoritativeSection : VeriDNS.Spec.Trustworthiness
  | authoritySection : VeriDNS.Spec.Trustworthiness
  | gluePrimary : VeriDNS.Spec.Trustworthiness
  | sectionNonauthoritative : VeriDNS.Spec.Trustworthiness
  | additionalAuthoritative : VeriDNS.Spec.Trustworthiness
  deriving Repr, BEq, Inhabited

@[blueprint "TrustworthinessSpec"]
class VeriDNS.Spec.TrustworthinessSpec (C : Type) (RR : Type) where
  acceptRrset : C → RR → VeriDNS.Spec.Trustworthiness → UInt32 → C
  answers : C → ByteArray → BitVec 16 → BitVec 16 → UInt32 → Array RR

def VeriDNS.Spec.Trustworthiness.toCode : VeriDNS.Spec.Trustworthiness → Nat :=
  fun x =>
  match x with
  | VeriDNS.Spec.Trustworthiness.primaryZone => 0
  | VeriDNS.Spec.Trustworthiness.zoneTransfer => 1
  | VeriDNS.Spec.Trustworthiness.authoritativeSection => 2
  | VeriDNS.Spec.Trustworthiness.authoritySection => 3
  | VeriDNS.Spec.Trustworthiness.gluePrimary => 4
  | VeriDNS.Spec.Trustworthiness.sectionNonauthoritative => 5
  | VeriDNS.Spec.Trustworthiness.additionalAuthoritative => 6

theorem VeriDNS.Spec.Trustworthiness.sectionNonauthoritative_code : VeriDNS.Spec.Trustworthiness.sectionNonauthoritative.toCode = 5 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.sectionNonauthoritative.toCode

/--
   Unauthenticated RRs received and cached from the least trustworthy of
   those groupings, that is data from the additional data section, and
   data from the authority section of a non-authoritative answer, should
   not be cached in such a way that they would ever be returned as
   answers to a received query.  They may be returned as additional
   information where appropriate.  Ignoring this would allow the
   trustworthiness of relatively untrustworthy data to be increased
   without cause or excuse.
-/
def VeriDNS.Spec.obligation_untrustworthyNotAnswerable : (σ : Type) → (σ → VeriDNS.Spec.Trustworthiness) → (σ → Bool) → Prop :=
  fun σ credibility returnedAsAnswer =>
  ∀ (s : σ), (credibility s).toCode ≥ 6 → returnedAsAnswer s = Bool.false

def VeriDNS.Spec.Trustworthiness.ofCode : Nat → Except String VeriDNS.Spec.Trustworthiness :=
  fun n =>
  match n with
  | 0 => Except.ok VeriDNS.Spec.Trustworthiness.primaryZone
  | 1 => Except.ok VeriDNS.Spec.Trustworthiness.zoneTransfer
  | 2 => Except.ok VeriDNS.Spec.Trustworthiness.authoritativeSection
  | 3 => Except.ok VeriDNS.Spec.Trustworthiness.authoritySection
  | 4 => Except.ok VeriDNS.Spec.Trustworthiness.gluePrimary
  | 5 => Except.ok VeriDNS.Spec.Trustworthiness.sectionNonauthoritative
  | 6 => Except.ok VeriDNS.Spec.Trustworthiness.additionalAuthoritative
  | x => Except.error ("invalid trustworthiness: " ++ ToString.toString n)

theorem VeriDNS.Spec.Trustworthiness.additionalAuthoritative_code : VeriDNS.Spec.Trustworthiness.additionalAuthoritative.toCode = 6 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.additionalAuthoritative.toCode

theorem VeriDNS.Spec.Trustworthiness.authoritativeSection_code : VeriDNS.Spec.Trustworthiness.authoritativeSection.toCode = 2 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.authoritativeSection.toCode

theorem VeriDNS.Spec.Trustworthiness.gluePrimary_code : VeriDNS.Spec.Trustworthiness.gluePrimary.toCode = 4 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.gluePrimary.toCode

theorem VeriDNS.Spec.Trustworthiness.primaryZone_code : VeriDNS.Spec.Trustworthiness.primaryZone.toCode = 0 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.primaryZone.toCode

theorem VeriDNS.Spec.Trustworthiness.ofCode_toCode : ∀ (x : VeriDNS.Spec.Trustworthiness), VeriDNS.Spec.Trustworthiness.ofCode x.toCode = Except.ok x :=
  fun x =>
  VeriDNS.Spec.Trustworthiness.casesOn (motive := fun t =>
    x = t → VeriDNS.Spec.Trustworthiness.ofCode x.toCode = Except.ok x) x
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode VeriDNS.Spec.Trustworthiness.primaryZone.toCode))
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode VeriDNS.Spec.Trustworthiness.zoneTransfer.toCode))
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode
            VeriDNS.Spec.Trustworthiness.authoritativeSection.toCode))
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode
            VeriDNS.Spec.Trustworthiness.authoritySection.toCode))
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode VeriDNS.Spec.Trustworthiness.gluePrimary.toCode))
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode
            VeriDNS.Spec.Trustworthiness.sectionNonauthoritative.toCode))
    (fun h =>
      Eq.symm h ▸
        Eq.refl
          (VeriDNS.Spec.Trustworthiness.ofCode
            VeriDNS.Spec.Trustworthiness.additionalAuthoritative.toCode))
    (Eq.refl x)

theorem VeriDNS.Spec.Trustworthiness.authoritySection_code : VeriDNS.Spec.Trustworthiness.authoritySection.toCode = 3 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.authoritySection.toCode

@[blueprint "RankingData"]
structure VeriDNS.Spec.RankingData  where
  cacheable : BitVec 1
  data : ByteArray
  deriving BEq, Inhabited

def VeriDNS.Spec.Trustworthiness.atLeastAsTrustworthy : VeriDNS.Spec.Trustworthiness → VeriDNS.Spec.Trustworthiness → Prop :=
  fun a b => a.toCode ≤ b.toCode

theorem VeriDNS.Spec.Trustworthiness.zoneTransfer_code : VeriDNS.Spec.Trustworthiness.zoneTransfer.toCode = 1 :=
  Eq.refl VeriDNS.Spec.Trustworthiness.zoneTransfer.toCode

check_rfc_doc VeriDNS.Spec.Trustworthiness [2181][343:376]
check_rfc_doc VeriDNS.Spec.obligation_untrustworthyNotAnswerable [2181][377:384]
