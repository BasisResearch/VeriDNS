import VeriDNS.Spec.NetworkModel

/-!
# Answer authenticity — ruling out the poison-conduit at the model level

The resolver's client-facing answer to a query for `qname` must consist only of records the
resolver is *entitled* to deliver: the RRset owned by `qname`, plus any records reached by
following a CNAME chain that is itself anchored at `qname`. A record whose owner is neither
`qname` nor the target of a CNAME genuinely present (and itself reachable) in the answer is an
**injected** record — the answer-injection / poison-conduit vector: an
answering server (or an off-path spoofer that wins the RFC 5452 race) stuffs an off-name record
(`victim-bank.com A …`) into the answer section of a legitimate reply.

This module specifies the entitlement as `CnameReachable` (the least set of owner names reachable
from `qname` via CNAME links present in the answer) and the delivery scrub `scrubAnswer`. The
flagship theorem `scrubAnswer_no_foreign` proves the model rules the vector out: **no record whose
owner is not CNAME-reachable from the query name survives delivery.** RFC 1034 §4.3.2 (the answer
to a query is the QNAME RRset, following CNAMEs), RFC 2181 §5.4.1 / §6 (only in-zone data).
-/

namespace VeriDNS.Spec.Net

/-- The CNAME target of a record, if it is a CNAME. -/
def cnameTarget? (rr : RR) : Option Name :=
  match rr.rdata with
  | .cname target => some target
  | _ => none

theorem cnameTarget?_some {rr : RR} {t : Name} (h : cnameTarget? rr = some t) :
    rr.rdata = .cname t := by
  unfold cnameTarget? at h
  cases hrd : rr.rdata with
  | cname target => rw [hrd] at h; simp only [Option.some.injEq] at h; subst t; rfl
  | a _ => rw [hrd] at h; simp at h
  | ns _ => rw [hrd] at h; simp at h
  | soa => rw [hrd] at h; simp at h
  | mx => rw [hrd] at h; simp at h
  | hinfo => rw [hrd] at h; simp at h
  | ptr _ => rw [hrd] at h; simp at h

/-- One CNAME-expansion round: `reach` together with the target of every CNAME record in `answer`
    whose owner is already authorized (case-insensitively, via `nameEq`). -/
def reachStep (answer : List RR) (reach : List Name) : List Name :=
  reach ++ answer.filterMap (fun rr =>
    (cnameTarget? rr).bind (fun target =>
      if reach.any (fun n => nameEq rr.owner n) then some target else none))

/-- Iterate `reachStep` `k` times from `reach`. -/
def reachIter (answer : List RR) : Nat → List Name → List Name
  | 0, reach => reach
  | k + 1, reach => reachIter answer k (reachStep answer reach)

/-- The owner names the resolver is entitled to deliver in an answer to `qname`: the closure of
    `{qname}` under the CNAME links present in `answer`. Iterating `answer.length` times reaches the
    fixpoint — each productive round consumes at least one distinct CNAME record. -/
def reachableNames (qname : Name) (answer : List RR) : List Name :=
  reachIter answer answer.length [qname]

/-- **The entitlement relation** — the least set containing `qname` and closed under following a
    CNAME record present in `answer` whose owner is already reachable. This is the model's ground
    truth for "the resolver may deliver a record with this owner". -/
inductive CnameReachable (qname : Name) (answer : List RR) : Name → Prop where
  | root : CnameReachable qname answer qname
  | step (rr : RR) (hmem : rr ∈ answer) (target : Name) (hcn : rr.rdata = .cname target)
      (n : Name) (hn : CnameReachable qname answer n) (hmatch : nameEq rr.owner n = true) :
      CnameReachable qname answer target

/-- **The client-delivery scrub.** Keep only records whose owner is entitled — the executable model
    of what the resolver must hand back to the client. -/
def scrubAnswer (qname : Name) (answer : List RR) : List RR :=
  answer.filter (fun rr => (reachableNames qname answer).any (fun n => nameEq rr.owner n))

/-- Delivering `delivered` for a query for `qname` (whose full reply answer section was `answer`) is
    **authentic** when every delivered record's owner is genuinely `CnameReachable` from `qname`. -/
def AnswerAuthenticWrt (qname : Name) (answer delivered : List RR) : Prop :=
  ∀ rr ∈ delivered, ∃ n, CnameReachable qname answer n ∧ nameEq rr.owner n = true

/-- Every name produced by `reachIter` from a fully-entitled seed is entitled. The engine behind
    the scrub's soundness: the fueled fixpoint never invents a name outside `CnameReachable`. -/
theorem reachIter_sound (qname : Name) (answer : List RR) :
    ∀ (k : Nat) (reach : List Name),
      (∀ m ∈ reach, CnameReachable qname answer m) →
      ∀ n ∈ reachIter answer k reach, CnameReachable qname answer n := by
  intro k
  induction k with
  | zero => intro reach hreach n hn; exact hreach n hn
  | succ k ih =>
    intro reach hreach n hn
    apply ih (reachStep answer reach) _ n hn
    intro m hm
    simp only [reachStep, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hreach m hm
    · rw [List.mem_filterMap] at hm
      obtain ⟨rr, hrrmem, hrreq⟩ := hm
      cases hct : cnameTarget? rr with
      | none => rw [hct] at hrreq; simp at hrreq
      | some target =>
        rw [hct] at hrreq
        simp only [Option.bind_some] at hrreq
        by_cases hg : reach.any (fun n => nameEq rr.owner n) = true
        · rw [if_pos hg] at hrreq
          rw [List.any_eq_true] at hg
          obtain ⟨o, homem, hoeq⟩ := hg
          have hmt : target = m := by simpa using hrreq
          subst hmt
          exact CnameReachable.step rr hrrmem target (cnameTarget?_some hct) o
            (hreach o homem) hoeq
        · rw [if_neg hg] at hrreq; simp at hrreq

/-- Every entitled *list* name is entitled in the `CnameReachable` sense. -/
theorem reachableNames_sound (qname : Name) (answer : List RR) :
    ∀ n ∈ reachableNames qname answer, CnameReachable qname answer n := by
  apply reachIter_sound
  intro m hm
  rw [List.mem_singleton] at hm; subst hm
  exact CnameReachable.root

/-- The scrub only ever drops records. -/
theorem scrubAnswer_subset {qname : Name} {answer : List RR} {rr : RR}
    (h : rr ∈ scrubAnswer qname answer) : rr ∈ answer :=
  (List.mem_filter.mp h).1

/-- **Every surviving record is entitled.** Each record the scrub keeps has an owner that is
    genuinely `CnameReachable` from the query name. -/
theorem scrubAnswer_authentic (qname : Name) (answer : List RR) :
    AnswerAuthenticWrt qname answer (scrubAnswer qname answer) := by
  intro rr hrr
  have hfil := List.mem_filter.mp hrr
  have hany : (reachableNames qname answer).any (fun n => nameEq rr.owner n) = true := by
    simpa using hfil.2
  rw [List.any_eq_true] at hany
  obtain ⟨n, hnmem, hneq⟩ := hany
  exact ⟨n, reachableNames_sound qname answer n hnmem, hneq⟩

/-- **The poison-conduit is ruled out by the spec.** A record whose owner is not entitled — not the
    query name and not reachable through a CNAME chain genuinely present in the answer — cannot
    appear in the scrubbed answer delivered to the client. This is exactly the answer-injection
    vector, now impossible in the model. -/
theorem scrubAnswer_no_foreign {qname : Name} {answer : List RR} {rr : RR}
    (hrr : rr ∈ scrubAnswer qname answer)
    (hforeign : ∀ n, CnameReachable qname answer n → nameEq rr.owner n = false) : False := by
  obtain ⟨n, hreach, heq⟩ := scrubAnswer_authentic qname answer rr hrr
  rw [hforeign n hreach] at heq
  simp at heq

/-- Contrapositive form: if every entitled name differs from `rr`'s owner, the scrub excludes `rr`. -/
theorem scrubAnswer_excludes {qname : Name} {answer : List RR} {rr : RR}
    (hforeign : ∀ n, CnameReachable qname answer n → nameEq rr.owner n = false) :
    rr ∉ scrubAnswer qname answer :=
  fun hrr => scrubAnswer_no_foreign hrr hforeign

end VeriDNS.Spec.Net
