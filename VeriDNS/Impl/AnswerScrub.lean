import VeriDNS.Impl.DomainName
import VeriDNS.Spec.Resolver



namespace VeriDNS.Impl.Resolver

open VeriDNS.Spec VeriDNS.Impl

variable {RR : Type} [RRParse RR]

def nameMemB (n : ByteArray) (reach : Array ByteArray) : Bool :=
  reach.any (fun m => DomainName.nameEqCI n m)

def reachTarget? [RRParse RR] (reach : Array ByteArray) (bytes : ByteArray) : Option ByteArray :=
  match RRParse.parseRaw (RR := RR) bytes with
  | some rr =>
    if RRParse.rrType rr == (5 : BitVec 16) && nameMemB (RRParse.rrName rr) reach
    then some (RRParse.rrRdata rr) else none
  | none => none

def reachStepB [RRParse RR] (answer reach : Array ByteArray) : Array ByteArray :=
  reach ++ answer.filterMap (reachTarget? (RR := RR) reach)

def reachIterB [RRParse RR] (answer : Array ByteArray) : Nat → Array ByteArray → Array ByteArray
  | 0, reach => reach
  | k + 1, reach => reachIterB answer k (reachStepB (RR := RR) answer reach)

/-! ### 060c: an equal, non-superlinear evaluation of `reachableNamesB`

`reachIterB` re-parses every answer record on every one of its `answer.size`
iterations (and, before the hoist in `scrubAnswerB` below, that whole closure
was recomputed once per delivered record) — about quartic in the record count,
seconds of CPU on a 300-record RRset. The evaluation below parses the answer
section ONCE into its CNAME links (`cnameLinksB`), iterates over the links
only, and stops at the first fixpoint. `reachableNamesB_eq_iter` proves the
result is the same array (same names, same order — the `find?` in
`scrubAnswerB` picks the same owner spelling), so nothing downstream changes:
`reachIterB` stays as the proof-facing reference form. -/

/-- The CNAME link `(owner, target)` carried by one raw answer record, if any:
    exactly the data `reachTarget?` re-derives from `bytes` on every iteration. -/
def cnameLinkB [RRParse RR] (bytes : ByteArray) : Option (ByteArray × ByteArray) :=
  match RRParse.parseRaw (RR := RR) bytes with
  | some rr =>
    if RRParse.rrType (RR := RR) rr == (5 : BitVec 16)
    then some (RRParse.rrName (RR := RR) rr, RRParse.rrRdata (RR := RR) rr)
    else none
  | none => none

/-- All CNAME links of an answer section, parsed once. -/
def cnameLinksB [RRParse RR] (answer : Array ByteArray) : Array (ByteArray × ByteArray) :=
  answer.filterMap (cnameLinkB (RR := RR))

/-- The step body of `reachTarget?` after the parse has been factored out. -/
def linkTarget? (reach : Array ByteArray) (l : ByteArray × ByteArray) : Option ByteArray :=
  if nameMemB l.1 reach then some l.2 else none

/-- `reachStepB` with the parse hoisted: composing the once-computed links with
    `linkTarget?` recovers `reachTarget?` pointwise. -/
theorem reachStepB_eq_links [RRParse RR] (answer reach : Array ByteArray) :
    reach ++ (cnameLinksB (RR := RR) answer).filterMap (linkTarget? reach)
      = reachStepB (RR := RR) answer reach := by
  unfold reachStepB cnameLinksB
  rw [Array.filterMap_filterMap]
  have hfun : (fun bytes => (cnameLinkB (RR := RR) bytes).bind (linkTarget? reach))
      = reachTarget? (RR := RR) reach := by
    funext bytes
    unfold cnameLinkB linkTarget? reachTarget?
    cases RRParse.parseRaw (RR := RR) bytes with
    | none => rfl
    | some rr =>
      by_cases ht : (RRParse.rrType (RR := RR) rr == (5 : BitVec 16)) = true
      · simp only [beq_iff_eq] at ht
        simp [ht]
      · simp only [Bool.not_eq_true, beq_eq_false_iff_ne] at ht
        split <;> simp_all
  rw [hfun]

/-- Link-driven iteration with fixpoint early exit: once a step adds no new
    name the iteration has converged and further steps are the identity. -/
def reachIterL (links : Array (ByteArray × ByteArray)) :
    Nat → Array ByteArray → Array ByteArray
  | 0, reach => reach
  | k + 1, reach =>
    let fresh := links.filterMap (linkTarget? reach)
    if fresh.isEmpty then reach
    else reachIterL links k (reach ++ fresh)

/-- A fixpoint of `reachStepB` is a fixpoint of the whole iteration. -/
theorem reachIterB_fixed [RRParse RR] (answer reach : Array ByteArray)
    (hfix : reachStepB (RR := RR) answer reach = reach) :
    ∀ k, reachIterB (RR := RR) answer k reach = reach := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => unfold reachIterB; rw [hfix]; exact ih

theorem reachIterL_eq_reachIterB [RRParse RR] (answer : Array ByteArray) :
    ∀ (k : Nat) (reach : Array ByteArray),
      reachIterL (cnameLinksB (RR := RR) answer) k reach
        = reachIterB (RR := RR) answer k reach := by
  intro k
  induction k with
  | zero => intro reach; rfl
  | succ k ih =>
    intro reach
    unfold reachIterL reachIterB
    by_cases hf : ((cnameLinksB (RR := RR) answer).filterMap (linkTarget? reach)).isEmpty = true
    · have hnil : (cnameLinksB (RR := RR) answer).filterMap (linkTarget? reach) = #[] :=
        Array.isEmpty_iff.mp hf
      have hfix : reachStepB (RR := RR) answer reach = reach := by
        rw [← reachStepB_eq_links, hnil, Array.append_empty]
      simp only [hf, if_true]
      rw [hfix, reachIterB_fixed (RR := RR) answer reach hfix k]
    · simp only [hf, if_false]
      rw [reachStepB_eq_links (RR := RR) answer reach] at *
      rw [← reachStepB_eq_links (RR := RR) answer reach]
      simpa using ih (reach ++ (cnameLinksB (RR := RR) answer).filterMap (linkTarget? reach))

def reachableNamesB [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  reachIterL (cnameLinksB (RR := RR) answer) answer.size #[qname]

/-- `reachableNamesB` computes exactly the reference iteration — the bridge
    every proof about the old body goes through. -/
theorem reachableNamesB_eq_iter [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) :
    reachableNamesB (RR := RR) qname answer
      = reachIterB (RR := RR) answer answer.size #[qname] :=
  reachIterL_eq_reachIterB (RR := RR) answer answer.size #[qname]

/-- The seed `qname` is always among the reachable names: `reachIterB` only
    appends to its accumulator, never dropping the initial `#[qname]`. -/
theorem mem_reachIterB_of_mem [RRParse RR] (answer : Array ByteArray) :
    ∀ (k : Nat) (reach : Array ByteArray) (n : ByteArray),
      n ∈ reach → n ∈ reachIterB (RR := RR) answer k reach := by
  intro k
  induction k with
  | zero => intro reach n h; exact h
  | succ k ih =>
    intro reach n h
    apply ih
    unfold reachStepB
    exact Array.mem_append_left _ h

theorem qname_mem_reachableNamesB [RRParse RR] (qname : ByteArray)
    (answer : Array ByteArray) : qname ∈ reachableNamesB (RR := RR) qname answer := by
  rw [reachableNamesB_eq_iter]
  exact mem_reachIterB_of_mem answer _ #[qname] qname (by simp)

def setOwnerB [RRParse RR] (rr : RR) (bytes m : ByteArray) : ByteArray :=
  m ++ bytes.extract (RRParse.rrName (RR := RR) rr).size bytes.size

/- 060c: `reachableNamesB qname answer` is loop-invariant, so it is hoisted out
   of the per-record closure via a `let` (zeta-definitionally the same term —
   the recomputation-per-record was the dominant factor of the reply-assembly
   blow-up). -/
def scrubAnswerB [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  let reach := reachableNamesB (RR := RR) qname answer
  answer.filterMap (fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr =>
      (reach.find? (fun m => DomainName.nameEqCI (RRParse.rrName rr) m)).map
        (setOwnerB (RR := RR) rr bytes)
    | none => none)

/-! ### Finding 068: qtype relevance of the delivered answer

`scrubAnswerB` is owner-based only, so an entitled response can smuggle
same-owner records of the WRONG type into the delivered answer section (and
the `tc == 1` acceptance arm can deliver a junk wrong-type record outright).
RFC 1034 §3.6.2: the answer section of a QTYPE=T response consists of chain
CNAMEs plus type-T records — nothing else.  `typeScrubB` is the byte-level
delivery filter (`Spec.Net.typeScrub` is its model image): keep a record iff
its type equals the query type, or it is a CNAME (type 5), or the query type
is `*` (255, which covers everything; unreachable at the serve boundary where
QTYPE=* is answered by the RFC 8482 minimal path).  Unparseable records are
dropped fail-closed (they never survive `scrubAnswerB` anyway). -/

def typeRelevantB [RRParse RR] (qtype : BitVec 16) (bytes : ByteArray) : Bool :=
  match RRParse.parseRaw (RR := RR) bytes with
  | some rr =>
    RRParse.rrType (RR := RR) rr == qtype
      || RRParse.rrType (RR := RR) rr == (5 : BitVec 16)
      || decide (qtype.toNat = 255)
  | none => false

def typeScrubB [RRParse RR] (qtype : BitVec 16) (answer : Array ByteArray) : Array ByteArray :=
  answer.filter (typeRelevantB (RR := RR) qtype)

theorem typeScrubB_subset [RRParse RR] {qtype : BitVec 16} {answer : Array ByteArray}
    {bytes : ByteArray} (h : bytes ∈ typeScrubB (RR := RR) qtype answer) :
    bytes ∈ answer :=
  (Array.mem_filter.mp h).1

theorem typeScrubB_size_le [RRParse RR] (qtype : BitVec 16) (answer : Array ByteArray) :
    (typeScrubB (RR := RR) qtype answer).size ≤ answer.size :=
  Array.size_filter_le

/-- **068 pin (impl side)**: every record surviving the byte-level type scrub
    parses to the query type or to a CNAME (or the query type is `*`). -/
theorem typeScrubB_relevant [RRParse RR] {qtype : BitVec 16} {answer : Array ByteArray}
    {bytes : ByteArray} (h : bytes ∈ typeScrubB (RR := RR) qtype answer) :
    ∃ rr, RRParse.parseRaw (RR := RR) bytes = some rr
      ∧ (RRParse.rrType (RR := RR) rr = qtype
         ∨ RRParse.rrType (RR := RR) rr = (5 : BitVec 16)
         ∨ qtype.toNat = 255) := by
  have hp := (Array.mem_filter.mp h).2
  unfold typeRelevantB at hp
  split at hp
  · next rr hpr =>
    refine ⟨rr, hpr, ?_⟩
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    rcases hp with (hc | hc) | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)
  · exact absurd hp (by simp)

end VeriDNS.Impl.Resolver
