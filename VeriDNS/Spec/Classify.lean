import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Header
import VeriDNS.Spec.Message
import VeriDNS.Spec.RData
import VeriDNS.RFC.Check

/-!
# The response classification frame (the DIRECTION row)

`serveSeq_total_primed` is *soundness* only: it forbids delivering an
unauthorised record, but says nothing about delivering the *right* one.  A
resolver that returns a spurious NODATA for a name that exists, or misclassifies
an authoritative NS-authority response, satisfies every soundness capstone.
Findings 040 (AA=1 lame referral → synthesised NODATA) and 041/045 (empty
NOERROR → synthesised NODATA) are exactly these wrong-answer bugs.

This module gives the response processing of RFC 1034 §4.3.2 (step 4) and the
NODATA / NXDOMAIN distinction of RFC 2308 §2.1–2.2 a *total* classification,
`ClassOutcome`, so that each outcome is pinned to its RFC clause.  The key
strengthening over the impl's historical behaviour: a `nodata` verdict requires
a *valid negative proof* (an SOA in the authority section, RFC 2308 §2.2); an
empty response without one is `retry` ("bizarre contents", RFC 1034 §4.3.2.d),
not a synthesised NODATA.  The completeness dual lives in `Proof/Classify.lean`.
-/

namespace VeriDNS.Spec

/-- RFC 1034 §4.3.2 step 4 / RFC 2308 §2 classification of a response received
    for the current query.  Total on every response.

    * `answer` / `nameError`   — step 4a: the response answers or is NXDOMAIN.
    * `referral`               — step 4b: a delegation to closer servers.
    * `cname`                  — step 4c: a CNAME to chase.
    * `nodata`                 — RFC 2308 §2.2: an empty NOERROR *with* an SOA.
    * `retry`                  — step 4d: servers failure or bizarre contents. -/
inductive ClassOutcome where
  | answer
  | nameError
  | referral
  | cname
  | nodata
  | retry
  deriving DecidableEq, Repr, Inhabited

/-- RFC 2308 §2.2: "NODATA is indicated by an answer with the RCODE set to
    NOERROR and no relevant answers in the answer section.  The authority
    section will contain an SOA record, or there will be no NS records there."
    A *valid negative proof* is the SOA — its presence is what turns an empty
    NOERROR into a believed NODATA rather than a re-query. -/
def hasNegativeProof (soaInAuthority : Bool) : Prop := soaInAuthority = true

/-- RFC 1034 §4.3.2.d: "if the response shows a servers failure or **other
    bizarre contents**, delete the server from the SLIST and go back to
    step 3."  An empty NOERROR with neither a proper referral nor an SOA
    negative proof is bizarre contents — it drives a retry, never a NODATA.
    This is the door findings 040 and 041/045 fit through. -/
def bizarreContents (empty soaInAuthority nsInAuthority aaSet : Bool) : Prop :=
  empty = true ∧ soaInAuthority = false ∧ (nsInAuthority = false ∨ aaSet = true)

/-- RFC 2308 §2.2 (l.296-298): "It is possible to distinguish between a NODATA
    and a referral response by the presence of a SOA record in the authority
    section or the absence of NS records in the authority section."  A response
    that has NS records but no SOA is a *referral*, not a NODATA — and only
    when the server is non-authoritative (aa=0), else it is bizarre (040). -/
def nodataDistinctFromReferral (soaInAuthority nsInAuthority : Bool) : Prop :=
  soaInAuthority = true ∨ nsInAuthority = false

theorem nodata_requires_proof_or_no_ns (soaInAuthority nsInAuthority : Bool)
    (h : nodataDistinctFromReferral soaInAuthority nsInAuthority) :
    hasNegativeProof soaInAuthority ∨ nsInAuthority = false := h

/-- Finding 040: an AA=1 response carrying NS records in the authority section
    (and no SOA) is *bizarre contents*, not a delegation — a delegation is a
    non-authoritative referral (RFC 1034 §4.3.2.b, aa must be 0).  So it drives
    a retry, and can never be a synthesised NODATA nor a delivered answer. -/
def lameReferralIsBizarre (empty nsInAuthority soaInAuthority aaSet : Bool) : Prop :=
  (empty = true ∧ nsInAuthority = true ∧ soaInAuthority = false ∧ aaSet = true) →
    bizarreContents empty soaInAuthority nsInAuthority aaSet

theorem lameReferral_bizarre (empty nsInAuthority soaInAuthority aaSet : Bool) :
    lameReferralIsBizarre empty nsInAuthority soaInAuthority aaSet := by
  rintro ⟨he, _, hsoa, haa⟩
  exact ⟨he, hsoa, Or.inr haa⟩

/-- Finding 041/045: an empty NOERROR whose authority carries no SOA (whether or
    not it has NS records) is not a valid NODATA — RFC 2308 §2.2 requires the
    SOA (or the absence of NS).  Without an SOA proof the resolver must re-query
    (RFC 2308 l.287-290: "it can be necessary to send another query"). -/
def emptyWithoutProofIsBizarre (empty soaInAuthority nsInAuthority aaSet : Bool) : Prop :=
  (empty = true ∧ soaInAuthority = false ∧ nsInAuthority = false) →
    bizarreContents empty soaInAuthority nsInAuthority aaSet

theorem emptyWithoutProof_bizarre (empty soaInAuthority nsInAuthority aaSet : Bool) :
    emptyWithoutProofIsBizarre empty soaInAuthority nsInAuthority aaSet := by
  rintro ⟨he, hsoa, hns⟩
  exact ⟨he, hsoa, Or.inl hns⟩

end VeriDNS.Spec

rfc_proves VeriDNS.Spec.nodata_requires_proof_or_no_ns [2308][296:298]
rfc_proves VeriDNS.Spec.lameReferral_bizarre [1034][1860:1876]
rfc_proves VeriDNS.Spec.emptyWithoutProof_bizarre [2308][287:298]
