import VeriDNS.Proof.Refinement
import VeriDNS.Proof.AnswerTerminal
import VeriDNS.Proof.AnswerScrub
import VeriDNS.Spec.AnswerAuthenticity

/-!
# The α-bridge: impl scrub refines the model entitlement

Connects the executable client-answer scrub (`Impl/AnswerScrub.lean`) to the model authenticity
notion (`Spec/AnswerAuthenticity.lean`) through the abstraction functions (`αRR`/`αName`/`αSection`).
The core is `cnameReachableB_to_model`: wire-level `CnameReachableB` transfers to model-level
`CnameReachable` under the answer's records abstracting (the `WfRR`/`αRR ≠ none` invariant
`ioResumeLoop_sound` already carries). The capstone `scrubAnswerB_delivered_model_authentic` then
shows every record the hardened Server delivers abstracts to a record whose owner is genuinely
`CnameReachable` from the query name in the *model* answer — so, composed with `ioResumeLoop_sound`
(`(αResp resp).answer = αSection cnameChain ++ v.answer`) and `resolves_answer_authoritative`, the
running resolver's client delivery is grounded and owner-authentic. Poison-conduit closed end to end.
-/

namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (RRParse ResourceRecord)
open VeriDNS.Spec.Net (Name RData nameEq nameEq_symm CnameReachable scrubAnswer)
open VeriDNS.Impl.DomainName (nameEqCI)
open VeriDNS.Impl.Resolver (CnameReachableB scrubAnswerB scrubAnswerB_authentic)

/-- The abstraction precondition threaded through the bridge: every parseable record in the answer
    abstracts. Discharged by the `WfRR` cache/response invariants `ioResumeLoop_sound` carries. -/
def AllAbstract (answer : Array ByteArray) : Prop :=
  ∀ b ∈ answer, ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr → ∃ r, αRR rr = some r

/-- `αRR` on a CNAME (type 5) record: its model rdata is `.cname` of the abstracted target, and the
    target abstracts. -/
theorem αRR_cname {rr : ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hαr : αRR rr = some r) (hty : (rr.type == (5 : BitVec 16)) = true) :
    ∃ mt, αName rr.rdata = some mt ∧ r.rdata = RData.cname mt := by
  have he : rr.type = (5 : BitVec 16) := by
    have h := hty; simp only [beq_iff_eq] at h; exact h
  have h5 : rr.type.toNat = 5 := by rw [he]; decide
  unfold αRR at hαr
  split at hαr
  · rename_i owner rdata cls hn hrd hcl
    obtain rfl := Option.some.inj hαr
    unfold αRData at hrd
    rw [h5] at hrd
    change Option.map RData.cname (αName rr.rdata) = some rdata at hrd
    rw [Option.map_eq_some_iff] at hrd
    obtain ⟨mt, hmt, hcn⟩ := hrd
    exact ⟨mt, hmt, hcn.symm⟩
  · exact absurd hαr (by simp)

/-- Every wire name reachable from `qname` (under `AllAbstract`) abstracts. -/
theorem αName_reachableB {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hab : AllAbstract answer) (hq : αName qname = some mqname) :
    ∀ {w : ByteArray}, CnameReachableB (RR := ResourceRecord) qname answer w →
      ∃ mw, αName w = some mw := by
  intro w hcr
  induction hcr with
  | root => exact ⟨mqname, hq⟩
  | step bytes hmem rr hpr hty n hn _hmatch _ih =>
    obtain ⟨r', hr'⟩ := hab bytes hmem rr hpr
    obtain ⟨mt, hmt, _⟩ := αRR_cname hr' hty
    exact ⟨mt, hmt⟩

/-- **The α-bridge (transfer).** Wire-level entitlement `CnameReachableB` implies model-level
    entitlement `CnameReachable` on the abstracted answer, under `AllAbstract`. -/
theorem cnameReachableB_to_model {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hab : AllAbstract answer) (hq : αName qname = some mqname) :
    ∀ {w : ByteArray}, CnameReachableB (RR := ResourceRecord) qname answer w →
      ∀ mw, αName w = some mw → CnameReachable mqname (αSection answer) mw := by
  intro w hcr
  induction hcr with
  | root =>
    intro mw hmw
    rw [hq] at hmw; obtain rfl := Option.some.inj hmw
    exact CnameReachable.root
  | step bytes hmem rr hpr hty n hn hmatch ih =>
    intro mw hmw
    obtain ⟨r', hr'⟩ := hab bytes hmem rr hpr
    obtain ⟨mt, hmt, hrd⟩ := αRR_cname hr' hty
    obtain rfl : mt = mw := Option.some.inj (hmt.symm.trans hmw)
    have hr'mem : r' ∈ αSection answer := αSection_mem (Array.mem_def.mp hmem) hpr hr'
    have hown : αName rr.name = some r'.owner := (αRR_fields rr r' hr').1
    have hmatchCI : nameEqCI n rr.name = true := VeriDNS.Proof.NameTree.nameEqCI_symm hmatch
    obtain ⟨mn, hmn, hnt⟩ := αName_of_nameEqCI hmatchCI hown
    refine CnameReachable.step r' hr'mem mt hrd mn (ih mn hmn) ?_
    rw [nameEq_symm]; exact hnt

/-- **End-to-end poison-conduit closure at the impl byte level.** Every record the hardened Server
    delivers to the client (`b ∈ scrubAnswerB qname resp.answer`) abstracts to a model record whose
    owner is genuinely `CnameReachable` from the query name in the *model* answer `αSection answer`.
    Composed with `ioResumeLoop_sound` (which grounds `αSection answer` in a model verdict) and
    `resolves_answer_authoritative`, this is the poison-conduit ruled out for the running resolver. -/
theorem scrubAnswerB_delivered_model_authentic
    {qname : ByteArray} {answer : Array ByteArray} {mqname : Name}
    (hab : AllAbstract answer) (hq : αName qname = some mqname)
    {b : ByteArray} (hb : b ∈ scrubAnswerB (RR := ResourceRecord) qname answer)
    {rr : ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (hpr : RRParse.parseRaw (RR := ResourceRecord) b = some rr) (hαr : αRR rr = some r) :
    ∃ n, CnameReachable mqname (αSection answer) n ∧ nameEq r.owner n = true := by
  obtain ⟨rr2, wn, hpr2, hcrB, hmatchCI⟩ := scrubAnswerB_authentic hb
  rw [hpr] at hpr2; obtain rfl := Option.some.inj hpr2
  obtain ⟨mwn, hmwn⟩ := αName_reachableB hab hq hcrB
  have hreach := cnameReachableB_to_model hab hq hcrB mwn hmwn
  have hown : αName rr.name = some r.owner := (αRR_fields rr r hαr).1
  obtain ⟨na, hna, hnt⟩ := αName_of_nameEqCI hmatchCI hmwn
  obtain rfl : na = r.owner := Option.some.inj (hna.symm.trans hown)
  exact ⟨mwn, hreach, hnt⟩

end VeriDNS.Proof.Refinement
