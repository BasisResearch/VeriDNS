import VeriDNS.Impl.Resolver
import VeriDNS.Impl.NameTree
import VeriDNS.Proof.NameTree
import VeriDNS.Proof.NameTreeComplete
import VeriDNS.Spec.Classify

/-!
# The completeness dual of the classification frame (DIRECTION row)

`Spec/Classify.lean` gives the response classification its RFC-tied outcomes.
This module proves the *completeness corollary* the repo most lacked: a `nodata`
verdict is deserved — the impl only classifies a response as NODATA when the
authoritative tree really holds no data of the queried type at that name.

The keystone is `classifyResponse_nodata_treeLookup`: on an honest response
consistent with the tree, `classifyResponse = .nodata` forces
`treeLookup = .nodata`.  The corollary `tree_hasData_not_nodata` is its
contrapositive over data-bearing names — the theorem findings 041/045 need.
Finding 040 is pinned by `classify_lameReferral_retry`: an AA=1 NS-authority
response (no SOA) classifies as `retry`, never a synthesised answer/NODATA.
-/

namespace VeriDNS.Proof.Classify

open VeriDNS.Spec (ClassOutcome Rcode Format)
open VeriDNS.Impl.NameTree (treeLookup Outcome)
open VeriDNS.Impl.Resolver
open VeriDNS.Proof.NameTree (ResponseConsistent HasType)

private theorem rcode_eq_of_beq {a b : Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- An SOA-in-authority witness (owned by an ancestor of `qname`) means the
    authority section contains a type-6 record — a `HasType … 6` witness. -/
theorem hasType_soa_of_hasSoaAuthorityFor {qname : ByteArray} {resp : Format}
    (h : hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord) qname resp.authority = true) :
    HasType resp.authority (6 : BitVec 16) := by
  unfold hasSoaAuthorityFor at h
  rw [Array.any_eq_true'] at h
  obtain ⟨b, hb, hcond⟩ := h
  revert hcond
  cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => intro hcond; simp at hcond
  | some rr =>
    intro hcond
    simp only [Bool.and_eq_true] at hcond
    have hty : VeriDNS.Spec.RRParse.rrType rr = (6 : BitVec 16) := by
      have := hcond.1; simpa [soaTypeCode] using eq_of_beq this
    exact ⟨b, by simpa using hb, rr, hp, hty⟩

/-- `classifyResponse … resp = .nodata` extracts the three NODATA facts the
    RFC 2308 §2.2 verdict rests on: NOERROR, empty answer, and a valid SOA
    negative proof for the query name. -/
theorem classifyResponse_nodata_facts {qname : ByteArray} {resp : Format}
    (h : classifyResponse (RR := VeriDNS.Spec.ResourceRecord) qname resp = .nodata) :
    (resp.header.rcode == Rcode.noError) = true ∧ resp.answer.isEmpty = true
      ∧ hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
          (echoedQname resp) resp.authority = true := by
  unfold classifyResponse at h
  split at h
  · exact absurd h (by simp)
  · -- cnameToChase = none
    split at h
    · exact absurd h (by simp)               -- retry (serverFail/unclassifiable)
    · split at h
      · -- B block
        split at h
        · exact absurd h (by simp)            -- referral
        · split at h <;> rename_i hb2
          · -- B.2 nodata
            cases h
            simp only [Bool.and_eq_true] at hb2
            exact ⟨hb2.1.1, hb2.1.2, hb2.2⟩
          · exact absurd h (by simp)          -- B.3 retry
      · -- ¬B tail
        split at h
        · exact absurd h (by simp)            -- C: entitled answer
        · split at h
          · exact absurd h (by simp)          -- D: nameError
          · split at h <;> rename_i he
            · -- E nodata
              cases h
              simp only [Bool.and_eq_true] at he
              exact ⟨he.1.1, he.1.2, he.2⟩
            · split at h
              · exact absurd h (by simp)       -- F answer (tc)
              · exact absurd h (by simp)       -- else: foreign / bizarre ⇒ retry

/-- **The completeness dual (DIRECTION row).**  On an honest response consistent
    with the authoritative tree `T`, whenever the impl classifies it as
    `nodata`, the tree really lacks data of the queried type at that name —
    `treeLookup T qname qtype = .nodata`.  A synthesised NODATA is therefore
    always *deserved*.  The SOA negative proof discharges the referral-exclusion
    premise of `ResponseConsistent.nodataDeserved` for free. -/
theorem classifyResponse_nodata_treeLookup {T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord}
    {resp : Format} {qu : VeriDNS.Spec.Question}
    (hcons : ResponseConsistent T resp)
    (htc : resp.header.tc = 0)
    (hqu : qu ∈ resp.question.toList)
    (hqn : echoedQname resp = qu.qname)
    (h : classifyResponse (RR := VeriDNS.Spec.ResourceRecord) (echoedQname resp) resp = .nodata) :
    treeLookup (RR := VeriDNS.Spec.ResourceRecord) T qu.qname qu.qtype = .nodata := by
  obtain ⟨hnoerr, hemp, hsoa⟩ := classifyResponse_nodata_facts h
  have hrc0 : resp.header.rcode = Rcode.noError := rcode_eq_of_beq hnoerr
  have hsoaType : HasType resp.authority (6 : BitVec 16) :=
    hasType_soa_of_hasSoaAuthorityFor hsoa
  -- the SOA negative proof kills the "NS ∧ aa=0 ∧ ¬SOA" referral shape
  have hnotref : ¬ (HasType resp.authority (2 : BitVec 16)
      ∧ resp.header.aa = 0 ∧ ¬ HasType resp.authority (6 : BitVec 16)) := by
    rintro ⟨_, _, hnSOA⟩; exact hnSOA hsoaType
  exact hcons.nodataDeserved qu hqu htc hrc0 hemp hnotref

/-- **The 041/045 pin.**  If the authoritative tree holds data of the queried
    type at the query name (`treeLookup = .answer`), an honest consistent
    response is *never* classified as NODATA — the wrong-answer door is shut. -/
theorem tree_hasData_not_nodata {T : VeriDNS.Spec.Node VeriDNS.Spec.ResourceRecord}
    {resp : Format} {qu : VeriDNS.Spec.Question} {rrs : Array VeriDNS.Spec.ResourceRecord}
    (hcons : ResponseConsistent T resp)
    (htc : resp.header.tc = 0)
    (hqu : qu ∈ resp.question.toList)
    (hqn : echoedQname resp = qu.qname)
    (hdata : treeLookup (RR := VeriDNS.Spec.ResourceRecord) T qu.qname qu.qtype = .answer rrs) :
    classifyResponse (RR := VeriDNS.Spec.ResourceRecord) (echoedQname resp) resp ≠ .nodata := by
  intro hnodata
  have hnd := classifyResponse_nodata_treeLookup hcons htc hqu hqn hnodata
  rw [hnd] at hdata
  exact absurd hdata (by simp)

/-- **The 040 pin.**  An AA=1 response carrying NS records in its authority
    section but no SOA (and an empty answer) is a lame referral: the impl
    classifies it as `retry`, never as an answer or a synthesised NODATA.
    RFC 1034 §4.3.2.d bizarre contents. -/
theorem classify_lameReferral_retry {qname : ByteArray} {resp : Format}
    (hcname : cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == Rcode.serverFailure
              || !classifiableB resp) = false)
    (hans : answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hne : (resp.header.rcode == Rcode.nameError) = false)
    (hemp : resp.answer.isEmpty = true)
    (hauthNE : resp.authority.isEmpty = false)
    (hNS : hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (hnoerr : (resp.header.rcode == Rcode.noError) = true)
    (haa1 : (resp.header.aa == 0) = false)
    (hnoSoa : hasSoaAuthorityFor (RR := VeriDNS.Spec.ResourceRecord)
        (echoedQname resp) resp.authority = false) :
    classifyResponse (RR := VeriDNS.Spec.ResourceRecord) qname resp = .retry := by
  unfold classifyResponse
  rw [hcname]
  rw [if_neg (by simp [hbiz])]
  rw [if_pos (by rw [hans, hne, hemp, hauthNE]; simp)]
  rw [if_neg (by rw [haa1]; simp)]
  rw [if_neg (by rw [hnoerr, hemp, hnoSoa]; simp)]

end VeriDNS.Proof.Classify
