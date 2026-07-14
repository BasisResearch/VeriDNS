import VeriDNS.Spec.NetworkModel




namespace VeriDNS.Spec.Net

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
  | generic _ _ => rw [hrd] at h; simp at h

def reachStep (answer : List RR) (reach : List Name) : List Name :=
  reach ++ answer.filterMap (fun rr =>
    (cnameTarget? rr).bind (fun target =>
      if reach.any (fun n => nameEq rr.owner n) then some target else none))

def reachIter (answer : List RR) : Nat → List Name → List Name
  | 0, reach => reach
  | k + 1, reach => reachIter answer k (reachStep answer reach)

def reachableNames (qname : Name) (answer : List RR) : List Name :=
  reachIter answer answer.length [qname]

inductive CnameReachable (qname : Name) (answer : List RR) : Name → Prop where
  | root : CnameReachable qname answer qname
  | step (rr : RR) (hmem : rr ∈ answer) (target : Name) (hcn : rr.rdata = .cname target)
      (n : Name) (hn : CnameReachable qname answer n) (hmatch : nameEq rr.owner n = true) :
      CnameReachable qname answer target

def scrubAnswer (qname : Name) (answer : List RR) : List RR :=
  answer.filterMap (fun rr =>
    ((reachableNames qname answer).find? (fun n => nameEq rr.owner n)).map
      (fun n => { rr with owner := n }))

def AnswerAuthenticWrt (qname : Name) (answer delivered : List RR) : Prop :=
  ∀ rr ∈ delivered, ∃ n, CnameReachable qname answer n ∧ nameEq rr.owner n = true

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

theorem reachableNames_sound (qname : Name) (answer : List RR) :
    ∀ n ∈ reachableNames qname answer, CnameReachable qname answer n := by
  apply reachIter_sound
  intro m hm
  rw [List.mem_singleton] at hm; subst hm
  exact CnameReachable.root

theorem scrubAnswer_mem {qname : Name} {answer : List RR} {r' : RR}
    (h : r' ∈ scrubAnswer qname answer) :
    ∃ r ∈ answer, ∃ n ∈ reachableNames qname answer,
      nameEq r.owner n = true ∧ r' = { r with owner := n } := by
  unfold scrubAnswer at h
  rw [List.mem_filterMap] at h
  obtain ⟨r, hr, hmap⟩ := h
  cases hf : (reachableNames qname answer).find? (fun n => nameEq r.owner n) with
  | none => rw [hf] at hmap; simp at hmap
  | some n =>
    rw [hf] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    exact ⟨r, hr, n, List.mem_of_find?_eq_some hf, List.find?_some hf, hmap.symm⟩

theorem scrubAnswer_data {qname : Name} {answer : List RR} {r' : RR}
    (h : r' ∈ scrubAnswer qname answer) :
    ∃ r ∈ answer, r'.rdata = r.rdata ∧ r'.ttl = r.ttl ∧ r'.cls = r.cls
      ∧ nameEq r'.owner r.owner = true := by
  obtain ⟨r, hr, n, -, hne, rfl⟩ := scrubAnswer_mem h
  exact ⟨r, hr, rfl, rfl, rfl, nameEq_symm r.owner n ▸ hne⟩

theorem scrubAnswer_authentic (qname : Name) (answer : List RR) :
    AnswerAuthenticWrt qname answer (scrubAnswer qname answer) := by
  intro rr hrr
  obtain ⟨r, hr, n, hnmem, hne, rfl⟩ := scrubAnswer_mem hrr
  exact ⟨n, reachableNames_sound qname answer n hnmem, nameEq_refl n⟩

theorem reachIter_head_cons (answer : List RR) :
    ∀ (k : Nat) (n : Name) (rest : List Name),
      ∃ rest', reachIter answer k (n :: rest) = n :: rest' := by
  intro k
  induction k with
  | zero => intro n rest; exact ⟨rest, rfl⟩
  | succ k ih =>
    intro n rest
    have hstep : reachStep answer (n :: rest)
        = n :: (rest ++ answer.filterMap (fun rr =>
            (cnameTarget? rr).bind (fun target =>
              if (n :: rest).any (fun m => nameEq rr.owner m) then some target else none))) := by
      unfold reachStep
      rfl
    show ∃ rest', reachIter answer k (reachStep answer (n :: rest)) = n :: rest'
    rw [hstep]
    exact ih n _

theorem reachableNames_head (qname : Name) (answer : List RR) :
    ∃ rest, reachableNames qname answer = qname :: rest :=
  reachIter_head_cons answer answer.length qname []

theorem scrubAnswer_owner_at_qname {qname : Name} {answer : List RR} {r' : RR}
    (h : r' ∈ scrubAnswer qname answer) (hq : nameEq r'.owner qname = true) :
    r'.owner = qname := by
  unfold scrubAnswer at h
  rw [List.mem_filterMap] at h
  obtain ⟨r, hr, hmap⟩ := h
  cases hf : (reachableNames qname answer).find? (fun n => nameEq r.owner n) with
  | none => rw [hf] at hmap; simp at hmap
  | some n =>
    rw [hf] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    have howner : r'.owner = n := by rw [← hmap]
    rw [howner] at hq
    have hrq : nameEq r.owner qname = true :=
      nameEq_trans (List.find?_some hf) hq
    obtain ⟨rest, hhead⟩ := reachableNames_head qname answer
    rw [hhead, List.find?_cons_of_pos hrq] at hf
    rw [howner, (Option.some.inj hf).symm]

theorem scrubAnswer_no_foreign {qname : Name} {answer : List RR} {rr : RR}
    (hrr : rr ∈ scrubAnswer qname answer)
    (hforeign : ∀ n, CnameReachable qname answer n → nameEq rr.owner n = false) : False := by
  obtain ⟨n, hreach, heq⟩ := scrubAnswer_authentic qname answer rr hrr
  rw [hforeign n hreach] at heq
  simp at heq

theorem scrubAnswer_excludes {qname : Name} {answer : List RR} {rr : RR}
    (hforeign : ∀ n, CnameReachable qname answer n → nameEq rr.owner n = false) :
    rr ∉ scrubAnswer qname answer :=
  fun hrr => scrubAnswer_no_foreign hrr hforeign

end VeriDNS.Spec.Net
