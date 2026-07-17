import VeriDNS.Proof.AnswerScrubAlpha
import VeriDNS.Spec.Entitlement

/-!
# Entitlement transported through refinement

`Spec/Entitlement.lean` proves the non-interference frame at the model:
the model's filters ignore records entitled in no role. The impl's
delivered set is `scrubAnswerB` over wire bytes, and
`αSection_scrubAnswerB_eq` (Proof/AnswerScrubAlpha) identifies its
abstraction with the model's `scrubAnswer`. Composing the two transports
the frame to the implementation:

- `scrubAnswerB_excludes_unentitled` — a record not entitled in the
  answer role never appears in (the abstraction of) the impl's delivered
  set; the generalisation of `scrubAnswerB_excludes_foreign`.
- `αSection_scrubAnswerB_insert_frame` — splicing a canonical wire record
  whose abstraction is unentitled into the wire answer leaves the impl's
  delivered set (at the model level) exactly the scrub of the un-edited
  answer: the impl inherits `handle_frame`'s deliver conjunct.
-/

namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (RRParse ResourceRecord)
open VeriDNS.Spec.Net (Name Query Response RR CnameReachable scrubAnswer nameEq
  Entitled InsertedIn not_entitled_chain scrubAnswer_excludes_unentitled
  scrubAnswer_insert_frame not_entitled_additional isAncestor)
open VeriDNS.Impl.Resolver (scrubAnswerB isAncestorB)

/-- `αSection` over an array splice is a list insertion of the abstracted
record. -/
theorem αSection_insert {preA postA : Array ByteArray} {b : ByteArray}
    {rrI : ResourceRecord} {r : RR}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rrI)
    (hα : αRR rrI = some r) :
    αSection (preA ++ #[b] ++ postA) = αSection preA ++ r :: αSection postA := by
  unfold αSection
  rw [Array.toList_append, Array.toList_append, List.filterMap_append, List.filterMap_append]
  simp [hpr, hα]

theorem αSection_insertedIn {preA postA : Array ByteArray} {b : ByteArray}
    {rrI : ResourceRecord} {r : RR}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rrI)
    (hα : αRR rrI = some r) :
    InsertedIn r (αSection (preA ++ postA)) (αSection (preA ++ #[b] ++ postA)) :=
  ⟨αSection preA, αSection postA, αSection_append preA postA, αSection_insert hpr hα⟩

/-- **Transport of the exclusion**: a record not entitled in the answer
role never reaches the impl's delivered set. Generalises
`scrubAnswerB_excludes_foreign` to the role-parameterised `Entitled`. -/
theorem scrubAnswerB_excludes_unentitled
    {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection answer)
    (habs : AllAbstract answer)
    (hq : αName qname = some mqname)
    (hqc : qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo mqname)
    (hqv : ∀ x ∈ mqname, 0 < x.size ∧ x.size ≤ 63)
    (hq255 : qname.size ≤ 255)
    {q : Query} {resp : Response} {bw : Name} {r : RR}
    (hqn : q.qname = mqname) (hresp : resp.answer = αSection answer)
    (hne : ¬ Entitled q resp bw .answer r) :
    r ∉ αSection (scrubAnswerB (RR := ResourceRecord) qname answer) := by
  rw [αSection_scrubAnswerB_eq hca habs hq hqc hqv hq255]
  intro hr
  apply scrubAnswer_excludes_unentitled hne
  rw [hqn, hresp]
  exact hr

/-- **Transport of the deliver frame**: splice a canonical wire record `b`
whose abstraction `r` is not answer-entitled into the wire answer section;
the impl's delivered (scrubbed) set is, at the model level, exactly the
scrub of the answer WITHOUT the splice. The implementation inherits
`handle_frame`'s deliver conjunct. -/
theorem αSection_scrubAnswerB_insert_frame
    {qname : ByteArray} {preA postA : Array ByteArray} {b : ByteArray} {mqname : Name}
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection (preA ++ #[b] ++ postA))
    (habs : AllAbstract (preA ++ #[b] ++ postA))
    (hq : αName qname = some mqname)
    (hqc : qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo mqname)
    (hqv : ∀ x ∈ mqname, 0 < x.size ∧ x.size ≤ 63)
    (hq255 : qname.size ≤ 255)
    {rrI : ResourceRecord} {r : RR}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rrI)
    (hα : αRR rrI = some r)
    {q : Query} {big : Response} {bw : Name}
    (hqn : q.qname = mqname)
    (hbig : big.answer = αSection (preA ++ #[b] ++ postA))
    (hne : ¬ Entitled q big bw .answer r) :
    αSection (scrubAnswerB (RR := ResourceRecord) qname (preA ++ #[b] ++ postA))
      = scrubAnswer mqname (αSection (preA ++ postA)) := by
  rw [αSection_scrubAnswerB_eq hca habs hq hqc hqv hq255]
  apply scrubAnswer_insert_frame (αSection_insertedIn hpr hα)
  intro n hn
  apply not_entitled_chain hne
  rw [hqn, hbig]
  exact hn

/-! ## The delivered additional section (047)

The client-facing additional section is scrubbed by `scrubAdditionalB` to
records whose owner lies in the bailiwick of the query name. Its abstraction
is the model's bailiwick filter, and a record entitled in NO role — in
particular an off-cut / foreign additional (047) — never reaches the client. -/

/-- `scrubAdditionalB` is the impl's `bailiwickRaws` at the query name: it
keeps a record iff its owner is in the query bailiwick. -/
theorem scrubAdditionalB_eq_bailiwickRaws (qname : ByteArray) (additional : Array ByteArray) :
    VeriDNS.Impl.Server.scrubAdditionalB qname additional
      = VeriDNS.Impl.Resolver.bailiwickRaws (RR := ResourceRecord) qname additional := by
  unfold VeriDNS.Impl.Server.scrubAdditionalB VeriDNS.Impl.Resolver.bailiwickRaws
  refine Array.filter_congr rfl ?_ rfl rfl
  funext b
  cases hpr : VeriDNS.Impl.DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | ok pr =>
    have hp : RRParse.parseRaw (RR := ResourceRecord) b = some pr.1 := by
      show (match VeriDNS.Impl.DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
            | .ok (rr, _) => some rr | .error _ => none) = some pr.1
      rw [hpr]
    rw [hp]
    rfl
  | error e =>
    have hp : RRParse.parseRaw (RR := ResourceRecord) b = none := by
      show (match VeriDNS.Impl.DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
            | .ok (rr, _) => some rr | .error _ => none) = none
      rw [hpr]
    rw [hp]

/-- The abstraction of the scrubbed additional section is the model's
bailiwick filter at the (abstracted) query name. -/
theorem αSection_scrubAdditionalB_eq (qname : ByteArray) (qnameN : Name)
    (additional : Array ByteArray) (hq : αName qname = some qnameN) :
    αSection (VeriDNS.Impl.Server.scrubAdditionalB qname additional)
      = (αSection additional).filter (fun r => isAncestor qnameN r.owner) := by
  rw [scrubAdditionalB_eq_bailiwickRaws]
  exact αSection_bailiwickRaws_eq qname qnameN additional hq

/-- **047 pin (transported)**: a record not entitled in the additional role
(its owner off the query bailiwick) never appears in the abstraction of the
impl's delivered additional section. -/
theorem scrubAdditional_excludes_unentitled
    {qname : ByteArray} {additional : Array ByteArray} {qnameN : Name}
    (hq : αName qname = some qnameN)
    {q : Query} {resp : Response} {bw : Name} {r : RR}
    (hqn : q.qname = qnameN)
    (hne : ¬ Entitled q resp bw .additional r) :
    r ∉ αSection (VeriDNS.Impl.Server.scrubAdditionalB qname additional) := by
  rw [αSection_scrubAdditionalB_eq qname qnameN additional hq]
  intro hr
  have hmem := List.mem_filter.mp hr
  have hanc : isAncestor qnameN r.owner = true := hmem.2
  rw [← hqn] at hanc
  exact hne hanc

/-- **047 closed (delivery boundary)**: an off-cut / foreign additional
record (its owner off the query bailiwick — e.g. `attacker.example` glue
smuggled into the additional section) provably never reaches the client. It
is dropped by `scrubAdditionalB` before delivery. Corollary of the model's
`offcut_additional_unentitled` transported through the abstraction. -/
theorem offcut_additional_not_delivered
    {qname : ByteArray} {additional : Array ByteArray} {qnameN : Name}
    (hq : αName qname = some qnameN)
    {r : RR} (hoff : isAncestor qnameN r.owner = false) :
    r ∉ αSection (VeriDNS.Impl.Server.scrubAdditionalB qname additional) :=
  scrubAdditional_excludes_unentitled hq (q := { qname := qnameN, qtype := VeriDNS.Spec.Net.QType.star })
    (resp := { aa := false, rcode := VeriDNS.Spec.Net.RCode.noError,
               answer := [], authority := [], additional := [] })
    (bw := []) rfl
    (VeriDNS.Spec.Net.offcut_additional_unentitled hoff)

end VeriDNS.Proof.Refinement
