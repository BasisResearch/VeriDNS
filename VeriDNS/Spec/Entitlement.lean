import VeriDNS.Spec.NetworkSemantics
import VeriDNS.Spec.AnswerAuthenticity

/-!
# Entitlement: one non-interference relation for the owner-check family

Owner-check faults (subdomain riders, off-owner CNAMEs, off-owner SOAs,
answer injection) are one property in disguise: an off-entitlement record
placed in a response must not change what the resolver delivers, caches,
or asks next.

`Entitled q resp bw rr` says which records of a response the resolver may
act on, per response role (RFC 2181 §5.4.1, RFC 2308 §3):

- **answer**: the owner equals `q.qname` or a link on the CNAME chain
  rooted at `q.qname` (the chain of the response being judged);
- **negative authority**: an SOA whose owner is an ancestor of `q.qname`;
- **referral / glue**: the owner lies in the bailiwick `bw` of the
  delegation (or responding zone) under which the response is processed.

The frame theorems below prove that the model's own section filters are
`Entitled`-filters: inserting a record that is entitled in NO role changes
none of the model's observables — the delivered (scrubbed) answer, the
positive cache write (`Cache.absorb`, both the bailiwick form and the
`answerOwned` trusted form), the negative cache write (`Cache.absorbNeg` /
`soaNegTtl`), the CNAME chase target (`cnameRR`), and the referral glue
(`glueAddresses`). They are bundled in `handle_frame`.

The model's classification GUARDS (`Response.isReferral`,
`Response.inBailiwick`, the nodata test in `absorbNeg`) are deliberately
insertion-SENSITIVE in the fail-closed direction: a tampered response can
lose its classification (the referral is not followed, the negative write
is suppressed) but a non-entitled record never creates or redirects an
observable. `absorbNeg_insert_ans` and `isReferral_insert_ans` record the
fail-closed shape.

Both W1 counterexamples are CLOSED and flipped into scrub pins at the
bottom of this file: `glueAddresses` walks only NS records owned at the
referral cut (`cutServers`; pin `glueAddresses_offcut_ns_scrubbed`), and
`addressOf` owner-filters by the NS host's CNAME chain
(`addressOf_insert_frame`, pin `addressOf_offowner_scrubbed`).
-/

namespace VeriDNS.Spec.Net

open VeriDNS.Spec (RRType RRClass)

/-! ## The entitlement relation -/

/-- The role a record plays in a response, i.e. the capacity in which the
resolver might act on it. -/
inductive Role where
  /-- Delivered/absorbed answer data. -/
  | answer
  /-- Negative-caching authority (the SOA of an NXDOMAIN/NODATA). -/
  | negSoa
  /-- Referral NS data and its glue. -/
  | delegation
  /-- Delivered additional-section data (glue / hints for the query). -/
  | additional
  deriving DecidableEq, Repr

/-- What a resolver processing response `resp` for query `q` under
bailiwick `bw` may act on: one relation, one case per response role. -/
def Entitled (q : Query) (resp : Response) (bw : Name) : Role → RR → Prop
  /- Answer role: the owner is the query name or a link on the CNAME
  chain rooted at `q.qname` in this response's answer section. -/
  | .answer, rr => ∃ n, CnameReachable q.qname resp.answer n ∧ nameEq rr.owner n = true
  /- Negative-authority role: an SOA whose owner is an ancestor of the
  query name (RFC 2308 §3). -/
  | .negSoa, rr => rr.rdata.rtype = RRType.soa ∧ isAncestor rr.owner q.qname = true
  /- Referral / glue role: the owner lies in the bailiwick of the
  delegation (RFC 2181 §5.4.1). -/
  | .delegation, rr => isAncestor bw rr.owner = true
  /- Additional role: a record delivered in the additional section is
  entitled iff its owner lies in the bailiwick of the query name — glue and
  additional data for the query (RFC 1035 §4.3.2 / RFC 2181 §5.4.1). An
  off-cut / foreign additional record (047) is entitled in no role. -/
  | .additional, rr => isAncestor q.qname rr.owner = true
rfc_proves VeriDNS.Spec.Net.Entitled [2181][343:383]
rfc_proves VeriDNS.Spec.Net.Entitled [2308][465:472]

/-- Entitled in no role: the record the non-interference theorem is about. -/
def Unentitled (q : Query) (resp : Response) (bw : Name) (x : RR) : Prop :=
  ∀ role, ¬ Entitled q resp bw role x

theorem not_entitled_chain {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hne : ¬ Entitled q resp bw .answer x) :
    ∀ n, CnameReachable q.qname resp.answer n → nameEq x.owner n = false := by
  intro n hn
  cases h : nameEq x.owner n
  · rfl
  · exact absurd ⟨n, hn, h⟩ hne

theorem entitled_answer_of_chain {q : Query} {resp : Response} {bw : Name} {x : RR}
    (h : ∀ n, CnameReachable q.qname resp.answer n → nameEq x.owner n = false) :
    ¬ Entitled q resp bw .answer x := by
  rintro ⟨n, hn, hown⟩
  rw [h n hn] at hown
  exact Bool.noConfusion hown

theorem not_entitled_qname {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hne : ¬ Entitled q resp bw .answer x) : nameEq x.owner q.qname = false :=
  not_entitled_chain hne q.qname CnameReachable.root

theorem not_entitled_soa {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hne : ¬ Entitled q resp bw .negSoa x) (hsoa : x.rdata.rtype = RRType.soa) :
    isAncestor x.owner q.qname = false := by
  cases h : isAncestor x.owner q.qname
  · rfl
  · exact absurd ⟨hsoa, h⟩ hne

theorem not_entitled_bailiwick {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hne : ¬ Entitled q resp bw .delegation x) : isAncestor bw x.owner = false := by
  cases h : isAncestor bw x.owner
  · rfl
  · exact absurd h hne

theorem not_entitled_additional {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hne : ¬ Entitled q resp bw .additional x) : isAncestor q.qname x.owner = false := by
  cases h : isAncestor q.qname x.owner
  · rfl
  · exact absurd h hne

/-- Conversely, a record whose owner is in the query bailiwick IS entitled in
the additional role — the retain direction (in-bailiwick glue is not
over-scrubbed). -/
theorem entitled_additional_of_bailiwick {q : Query} {resp : Response} {bw : Name} {x : RR}
    (h : isAncestor q.qname x.owner = true) : Entitled q resp bw .additional x := h

/-! ## Record insertion -/

/-- `big` is `small` with `x` spliced in at some position. -/
def InsertedIn (x : RR) (small big : List RR) : Prop :=
  ∃ pre post, small = pre ++ post ∧ big = pre ++ x :: post

/-- Response sections. -/
inductive Sec where
  | ans | auth | add
  deriving DecidableEq, Repr

/-- `big` is `small` with `x` inserted into section `s`; every other field
of the response is unchanged. -/
def RespInsert (s : Sec) (x : RR) (small big : Response) : Prop :=
  big.aa = small.aa ∧ big.rcode = small.rcode ∧ big.tc = small.tc ∧ big.ra = small.ra ∧
    (match s with
     | .ans => InsertedIn x small.answer big.answer ∧ big.authority = small.authority
         ∧ big.additional = small.additional
     | .auth => big.answer = small.answer ∧ InsertedIn x small.authority big.authority
         ∧ big.additional = small.additional
     | .add => big.answer = small.answer ∧ big.authority = small.authority
         ∧ InsertedIn x small.additional big.additional)

theorem InsertedIn.subset {x : RR} {small big : List RR} (h : InsertedIn x small big) :
    ∀ r ∈ small, r ∈ big := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem InsertedIn.length {x : RR} {small big : List RR} (h : InsertedIn x small big) :
    big.length = small.length + 1 := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp only [List.length_append, List.length_cons]
  omega

/-! ## Generic insertion frames for list combinators -/

theorem filter_insert_of_neg {p : RR → Bool} {x : RR} (hx : p x = false)
    {small big : List RR} (hins : InsertedIn x small big) :
    big.filter p = small.filter p := by
  obtain ⟨pre, post, rfl, rfl⟩ := hins
  simp [List.filter_append, hx]

theorem filterMap_insert_of_none {α : Type} {f : RR → Option α} {x : RR} (hx : f x = none)
    {small big : List RR} (hins : InsertedIn x small big) :
    big.filterMap f = small.filterMap f := by
  obtain ⟨pre, post, rfl, rfl⟩ := hins
  simp [List.filterMap_append, hx]

theorem find?_insert_of_neg {p : RR → Bool} {x : RR} (hx : p x = false)
    {small big : List RR} (hins : InsertedIn x small big) :
    big.find? p = small.find? p := by
  obtain ⟨pre, post, rfl, rfl⟩ := hins
  simp [List.find?_append, hx]

theorem findSome?_insert_of_none {α : Type} {f : RR → Option α} {x : RR} (hx : f x = none)
    {small big : List RR} (hins : InsertedIn x small big) :
    big.findSome? f = small.findSome? f := by
  obtain ⟨pre, post, rfl, rfl⟩ := hins
  simp [List.findSome?_append, hx]

/-! ## CNAME chains as explicit paths

`reachableNames` computes the CNAME-chain closure with fuel
`answer.length`. To prove insertion-invariance of `scrubAnswer` we need
that this fuel SATURATES: every `CnameReachable` name is already present.
The pigeonhole is carried by explicit chain paths: a duplicate-free chain
uses each CNAME record at most once, so its length is bounded by
`answer.length`. -/

theorem cnameTarget?_of_rdata {x : RR} {t : Name} (h : x.rdata = RData.cname t) :
    cnameTarget? x = some t := by
  unfold cnameTarget?
  rw [h]

/-- A CNAME chain from `s` to `m` using the listed records in order. -/
inductive CnamePath (answer : List RR) : Name → List RR → Name → Prop where
  | nil (n : Name) : CnamePath answer n [] n
  | cons (x : RR) (hmem : x ∈ answer) (t : Name) (hcn : x.rdata = RData.cname t)
      (s m : Name) (p : List RR) (hmatch : nameEq x.owner s = true)
      (hp : CnamePath answer t p m) : CnamePath answer s (x :: p) m

theorem cnamePath_snoc {answer : List RR} (x : RR) (hmem : x ∈ answer) (t : Name)
    (hcn : x.rdata = RData.cname t) {s : Name} {p : List RR} {m : Name}
    (h : CnamePath answer s p m) (hmatch : nameEq x.owner m = true) :
    CnamePath answer s (p ++ [x]) t := by
  induction h with
  | nil n => exact .cons x hmem t hcn n t [] hmatch (.nil t)
  | cons y hymem u hycn s' m' p' hymatch hp ih =>
    exact .cons y hymem u hycn s' t (p' ++ [x]) hymatch (ih hmatch)

theorem cnamePath_reachable {qname : Name} {answer : List RR} {s : Name} {p : List RR}
    {m : Name} (h : CnamePath answer s p m) :
    CnameReachable qname answer s → CnameReachable qname answer m := by
  induction h with
  | nil n => exact id
  | cons x hmem t hcn s' m' p' hmatch hp ih =>
    intro hs
    exact ih (CnameReachable.step x hmem t hcn s' hs hmatch)

theorem cnameReachable_path {qname : Name} {answer : List RR} {n : Name} :
    CnameReachable qname answer n ↔ ∃ p, CnamePath answer qname p n := by
  constructor
  · intro h
    induction h with
    | root => exact ⟨[], .nil qname⟩
    | step x hmem t hcn n' hn hmatch ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨p ++ [x], cnamePath_snoc x hmem t hcn hp hmatch⟩
  · rintro ⟨p, hp⟩
    exact cnamePath_reachable hp CnameReachable.root

theorem cnamePath_cons_inv {answer : List RR} {x : RR} {p : List RR} {s m : Name}
    (h : CnamePath answer s (x :: p) m) :
    ∃ t, x ∈ answer ∧ x.rdata = RData.cname t ∧ nameEq x.owner s = true
      ∧ CnamePath answer t p m := by
  cases h with
  | cons _ hmem t hcn _ _ _ hmatch hp => exact ⟨t, hmem, hcn, hmatch, hp⟩

theorem cnamePath_append_split {answer : List RR} :
    ∀ (p1 : List RR) {s m : Name} {p2 : List RR}, CnamePath answer s (p1 ++ p2) m →
      ∃ u, CnamePath answer s p1 u ∧ CnamePath answer u p2 m := by
  intro p1
  induction p1 with
  | nil => intro s m p2 h; exact ⟨s, .nil s, h⟩
  | cons x p1' ih =>
    intro s m p2 h
    obtain ⟨t, hmem, hcn, hmatch, hp⟩ := cnamePath_cons_inv h
    obtain ⟨u, h1, h2⟩ := ih hp
    exact ⟨u, .cons x hmem t hcn s u p1' hmatch h1, h2⟩

theorem cnamePath_subset {answer : List RR} {s : Name} {p : List RR} {m : Name}
    (h : CnamePath answer s p m) : ∀ x ∈ p, x ∈ answer := by
  induction h with
  | nil n => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons y hymem u hycn s' m' p' hymatch hp ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hymem
    · exact ih x hx'

/-- Chain shortening: every chain has a duplicate-free sub-chain with the
same endpoints (repeated records land on the same target, so the loop
between two uses of a record can be cut out). -/
theorem cnamePath_shorten {answer : List RR} :
    ∀ (k : Nat) (p : List RR), p.length ≤ k → ∀ {s m : Name}, CnamePath answer s p m →
      ∃ p', p'.Nodup ∧ p' ⊆ p ∧ CnamePath answer s p' m := by
  intro k
  induction k with
  | zero =>
    intro p hlen s m h
    cases p with
    | nil => exact ⟨[], List.nodup_nil, List.Subset.refl _, h⟩
    | cons x rest => simp at hlen
  | succ k ih =>
    intro p hlen s m h
    cases p with
    | nil => exact ⟨[], List.nodup_nil, List.Subset.refl _, h⟩
    | cons x rest =>
      obtain ⟨t, hmem, hcn, hmatch, hp⟩ := cnamePath_cons_inv h
      by_cases hx : x ∈ rest
      · obtain ⟨r1, r2, hr⟩ := List.append_of_mem hx
        subst hr
        obtain ⟨u, _h1, h2⟩ := cnamePath_append_split r1 hp
        obtain ⟨t', hmem', hcn', hmatch', hp2⟩ := cnamePath_cons_inv h2
        have ht' : t = t' := by
          rw [hcn] at hcn'
          exact RData.cname.inj hcn'
        subst ht'
        have hnew : CnamePath answer s (x :: r2) m := .cons x hmem t hcn s m r2 hmatch hp2
        have hlen' : (x :: r2).length ≤ k := by
          simp only [List.length_cons, List.length_append] at hlen ⊢
          omega
        obtain ⟨p', hnd, hsub, hpath⟩ := ih _ hlen' hnew
        refine ⟨p', hnd, ?_, hpath⟩
        intro y hy
        rcases List.mem_cons.mp (hsub hy) with rfl | hy'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hy'))
      · have hlen' : rest.length ≤ k := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨p', hnd, hsub, hpath⟩ := ih rest hlen' hp
        refine ⟨x :: p', ?_, ?_, .cons x hmem t hcn s m p' hmatch hpath⟩
        · exact List.nodup_cons.mpr ⟨fun hxx => hx (hsub hxx), hnd⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub hy')

/-! ## Fuel saturation and completeness of `reachableNames` -/

theorem reachStep_sound {qname : Name} {answer : List RR} {reach : List Name}
    (hreach : ∀ m ∈ reach, CnameReachable qname answer m) :
    ∀ m ∈ reachStep answer reach, CnameReachable qname answer m := by
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

theorem reachIter_succ_out (answer : List RR) :
    ∀ (k : Nat) (reach : List Name),
      reachIter answer (k + 1) reach = reachStep answer (reachIter answer k reach) := by
  intro k
  induction k with
  | zero => intro reach; rfl
  | succ k ih =>
    intro reach
    show reachIter answer (k + 1) (reachStep answer reach) = _
    rw [ih (reachStep answer reach)]
    rfl

theorem mem_reachStep_of_mem {answer : List RR} {reach : List Name} {n : Name}
    (h : n ∈ reach) : n ∈ reachStep answer reach := by
  simp only [reachStep, List.mem_append]
  exact Or.inl h

theorem mem_reachIter_of_mem (answer : List RR) :
    ∀ (k : Nat) {reach : List Name} {n : Name}, n ∈ reach → n ∈ reachIter answer k reach := by
  intro k
  induction k with
  | zero => intro reach n h; exact h
  | succ k ih => intro reach n h; exact ih (mem_reachStep_of_mem h)

theorem mem_reachIter_mono (answer : List RR) {k k' : Nat} (hk : k ≤ k')
    {reach : List Name} {n : Name} (h : n ∈ reachIter answer k reach) :
    n ∈ reachIter answer k' reach := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  clear hk
  induction d with
  | zero => exact h
  | succ d ih =>
    rw [show k + (d + 1) = (k + d) + 1 by omega, reachIter_succ_out]
    exact mem_reachStep_of_mem ih

theorem reachStep_target_mem {answer : List RR} {reach : List Name} {x : RR} {t s : Name}
    (hx : x ∈ answer) (hcn : x.rdata = RData.cname t)
    (hs : s ∈ reach) (hmatch : nameEq x.owner s = true) :
    t ∈ reachStep answer reach := by
  simp only [reachStep, List.mem_append]
  refine Or.inr ?_
  rw [List.mem_filterMap]
  refine ⟨x, hx, ?_⟩
  rw [cnameTarget?_of_rdata hcn]
  have hg : reach.any (fun n => nameEq x.owner n) = true :=
    List.any_eq_true.mpr ⟨s, hs, hmatch⟩
  simp [hg]

theorem cnamePath_mem_reachIter {answer : List RR} :
    ∀ (p : List RR) {s m : Name}, CnamePath answer s p m →
      ∀ (j k : Nat) (reach : List Name), s ∈ reachIter answer j reach →
        p.length + j ≤ k → m ∈ reachIter answer k reach := by
  intro p
  induction p with
  | nil =>
    intro s m h j k reach hs hlen
    cases h with
    | nil => exact mem_reachIter_mono answer (by omega) hs
  | cons x rest ih =>
    intro s m h j k reach hs hlen
    obtain ⟨t, hmem, hcn, hmatch, hp⟩ := cnamePath_cons_inv h
    have ht : t ∈ reachIter answer (j + 1) reach := by
      rw [reachIter_succ_out]
      exact reachStep_target_mem hmem hcn hs hmatch
    refine ih hp (j + 1) k reach ht ?_
    simp only [List.length_cons] at hlen
    omega

/-- Completeness: the fuel `answer.length` used by `reachableNames`
saturates the CNAME-chain closure. Every reachable name is literally a
member of the computed list. -/
theorem reachableNames_complete {qname : Name} {answer : List RR} {n : Name}
    (h : CnameReachable qname answer n) : n ∈ reachableNames qname answer := by
  obtain ⟨p, hp⟩ := cnameReachable_path.mp h
  obtain ⟨p', hnd, hsub, hp'⟩ := cnamePath_shorten p.length p (Nat.le_refl _) hp
  have hsubA : p' ⊆ answer := by
    intro y hy
    exact cnamePath_subset hp' y hy
  have hlen : p'.length ≤ answer.length :=
    (List.subperm_of_subset hnd hsubA).length_le
  unfold reachableNames
  exact cnamePath_mem_reachIter p' hp' 0 answer.length [qname]
    (List.mem_singleton.mpr rfl) (by omega)

/-! ## Insertion-invariance of the chain closure and of `scrubAnswer` -/

theorem cnameReachable_of_subset {qname : Name} {a b : List RR}
    (hsub : ∀ r ∈ a, r ∈ b) {n : Name} (h : CnameReachable qname a n) :
    CnameReachable qname b n := by
  induction h with
  | root => exact CnameReachable.root
  | step rr hmem target hcn n' hn hmatch ih =>
    exact CnameReachable.step rr (hsub rr hmem) target hcn n' ih hmatch

theorem reachStep_insert_frame {qname : Name} {x : RR} {small big : List RR}
    (hins : InsertedIn x small big)
    (hforeign : ∀ n, CnameReachable qname big n → nameEq x.owner n = false)
    {reach : List Name} (hs : ∀ m ∈ reach, CnameReachable qname big m) :
    reachStep big reach = reachStep small reach := by
  have hguard : reach.any (fun n => nameEq x.owner n) = false := by
    rw [List.any_eq_false]
    intro m hm
    simp [hforeign m (hs m hm)]
  have hx : ((cnameTarget? x).bind (fun target =>
      if reach.any (fun n => nameEq x.owner n) then some target else none)) = none := by
    rw [hguard]
    cases cnameTarget? x <;> simp
  obtain ⟨pre, post, rfl, rfl⟩ := hins
  unfold reachStep
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_cons, hx]

theorem reachIter_insert_frame {qname : Name} {x : RR} {small big : List RR}
    (hins : InsertedIn x small big)
    (hforeign : ∀ n, CnameReachable qname big n → nameEq x.owner n = false) :
    ∀ (k : Nat) (reach : List Name), (∀ m ∈ reach, CnameReachable qname big m) →
      reachIter big k reach = reachIter small k reach := by
  intro k
  induction k with
  | zero => intro reach _; rfl
  | succ k ih =>
    intro reach hreach
    show reachIter big k (reachStep big reach) = reachIter small k (reachStep small reach)
    have hstep := reachStep_insert_frame hins hforeign hreach
    rw [hstep]
    apply ih
    intro m hm
    rw [← hstep] at hm
    exact reachStep_sound hreach m hm

theorem reachableNames_insert_eq {qname : Name} {x : RR} {small big : List RR}
    (hins : InsertedIn x small big)
    (hforeign : ∀ n, CnameReachable qname big n → nameEq x.owner n = false) :
    reachableNames qname big = reachStep small (reachableNames qname small) := by
  have hseed : ∀ m ∈ ([qname] : List Name), CnameReachable qname big m := by
    intro m hm
    rw [List.mem_singleton] at hm
    subst hm
    exact CnameReachable.root
  unfold reachableNames
  rw [hins.length, reachIter_insert_frame hins hforeign (small.length + 1) [qname] hseed,
    reachIter_succ_out]

theorem find?_reachableNames_insert {qname : Name} {x : RR} {small big : List RR}
    (hins : InsertedIn x small big)
    (hforeign : ∀ n, CnameReachable qname big n → nameEq x.owner n = false)
    (o : Name) :
    (reachableNames qname big).find? (fun n => nameEq o n)
      = (reachableNames qname small).find? (fun n => nameEq o n) := by
  rw [reachableNames_insert_eq hins hforeign]
  unfold reachStep
  rw [List.find?_append]
  cases hf : (reachableNames qname small).find? (fun n => nameEq o n) with
  | some v => rfl
  | none =>
    rw [Option.none_or]
    rw [List.find?_eq_none] at hf ⊢
    intro d hd
    apply hf
    apply reachableNames_complete
    exact reachStep_sound (reachableNames_sound qname small) d
      (by
        unfold reachStep
        exact List.mem_append_right _ hd)

/-- **Deliver frame**: inserting a record whose owner is foreign to the
whole CNAME chain leaves the scrubbed (delivered) answer literally
unchanged. -/
theorem scrubAnswer_insert_frame {qname : Name} {x : RR} {small big : List RR}
    (hins : InsertedIn x small big)
    (hforeign : ∀ n, CnameReachable qname big n → nameEq x.owner n = false) :
    scrubAnswer qname big = scrubAnswer qname small := by
  obtain ⟨pre, post, rfl, rfl⟩ := hins
  have hins : InsertedIn x (pre ++ post) (pre ++ x :: post) := ⟨pre, post, rfl, rfl⟩
  have hfun : (fun r : RR => ((reachableNames qname (pre ++ x :: post)).find?
        (fun n => nameEq r.owner n)).map (fun n => { r with owner := n }))
      = (fun r : RR => ((reachableNames qname (pre ++ post)).find?
        (fun n => nameEq r.owner n)).map (fun n => { r with owner := n })) := by
    funext r
    rw [find?_reachableNames_insert hins hforeign r.owner]
  have hxnone : ((reachableNames qname (pre ++ post)).find?
      (fun n => nameEq x.owner n)).map (fun n => { x with owner := n }) = none := by
    rw [List.find?_eq_none.mpr, Option.map_none]
    intro n hn
    simp [hforeign n (cnameReachable_of_subset hins.subset
      (reachableNames_sound qname (pre ++ post) n hn))]
  unfold scrubAnswer
  rw [hfun, List.filterMap_append, List.filterMap_append, List.filterMap_cons, hxnone]

/-! ## Cache-write frames -/

/-- `Cache.absorb` with its `let`-bindings expanded (for rewriting). -/
theorem Cache.absorb_eq (c : Cache) (now : Time) (bw : Name) (resp : Response) :
    c.absorb now bw resp =
      (normalizeTTL (resp.answer.filter (fun r => isAncestor bw r.owner))).foldl
        (fun a r => a.insert now (if resp.aa then Cred.authoritative else Cred.glue) r)
        ((normalizeTTL ((resp.authority.filter (fun r => r.rdata.rtype != RRType.soa)).filter
            (fun r => isAncestor bw r.owner))).foldl
          (fun a r => a.insert now (if resp.aa then Cred.authority else Cred.additional) r)
          ((normalizeTTL (resp.additional.filter (fun r => isAncestor bw r.owner))).foldl
            (fun a r => a.insert now Cred.additional r) c)) := rfl

/-- **Cache-write frame**: a record outside the absorb bailiwick, inserted
into any section, leaves the positive cache write unchanged. -/
theorem absorb_insert_frame {s : Sec} {x : RR} {small big : Response}
    (hins : RespInsert s x small big) {bw : Name}
    (hbw : isAncestor bw x.owner = false) (c : Cache) (now : Time) :
    c.absorb now bw big = c.absorb now bw small := by
  obtain ⟨haa, _hrc, _htc, _hra, hrest⟩ := hins
  rw [Cache.absorb_eq, Cache.absorb_eq, haa]
  cases s with
  | ans =>
    obtain ⟨hansIns, hauth, hadd⟩ := hrest
    rw [hauth, hadd, filter_insert_of_neg hbw hansIns]
  | auth =>
    obtain ⟨hans, hauthIns, hadd⟩ := hrest
    rw [hans, hadd, List.filter_filter, List.filter_filter,
      filter_insert_of_neg (by simp [hbw]) hauthIns]
  | add =>
    obtain ⟨hans, hauth, haddIns⟩ := hrest
    rw [hans, hauth, filter_insert_of_neg hbw haddIns]

theorem Response.answerOwned_rcode (qname : Name) (r : Response) :
    (r.answerOwned qname).rcode = r.rcode := rfl
theorem Response.answerOwned_ra (qname : Name) (r : Response) :
    (r.answerOwned qname).ra = r.ra := rfl
theorem Response.answerOwned_tc (qname : Name) (r : Response) :
    (r.answerOwned qname).tc = r.tc := rfl

theorem Response.ext' {r1 r2 : Response} (haa : r1.aa = r2.aa) (hrc : r1.rcode = r2.rcode)
    (hans : r1.answer = r2.answer) (hauth : r1.authority = r2.authority)
    (hadd : r1.additional = r2.additional) (hra : r1.ra = r2.ra) (htc : r1.tc = r2.tc) :
    r1 = r2 := by
  cases r1
  cases r2
  simp_all

/-- The trusted-arm cache filter (`answerOwned`) drops a record whose
owner is not the query name, so insertion anywhere leaves it unchanged. -/
theorem answerOwned_insert_frame {s : Sec} {x : RR} {small big : Response}
    (hins : RespInsert s x small big) {qn : Name} (hq : nameEq x.owner qn = false) :
    big.answerOwned qn = small.answerOwned qn := by
  obtain ⟨haa, hrc, htc, hra, hrest⟩ := hins
  have hans : big.answer.filter (fun rr => nameEq rr.owner qn)
      = small.answer.filter (fun rr => nameEq rr.owner qn) := by
    cases s with
    | ans => exact filter_insert_of_neg hq hrest.1
    | auth => rw [hrest.1]
    | add => rw [hrest.1]
  exact Response.ext'
    (by rw [Response.answerOwned_aa, Response.answerOwned_aa, haa])
    (by rw [Response.answerOwned_rcode, Response.answerOwned_rcode, hrc])
    (by rw [Response.answerOwned_answer, Response.answerOwned_answer, hans])
    (by rw [Response.answerOwned_authority, Response.answerOwned_authority])
    (by rw [Response.answerOwned_additional, Response.answerOwned_additional])
    (by rw [Response.answerOwned_ra, Response.answerOwned_ra, hra])
    (by rw [Response.answerOwned_tc, Response.answerOwned_tc, htc])

theorem Response.cnameOwned_rcode (qname : Name) (r : Response) :
    (r.cnameOwned qname).rcode = r.rcode := rfl
theorem Response.cnameOwned_ra (qname : Name) (r : Response) :
    (r.cnameOwned qname).ra = r.ra := rfl
theorem Response.cnameOwned_tc (qname : Name) (r : Response) :
    (r.cnameOwned qname).tc = r.tc := rfl

/-- The chase-arm cache filter (`cnameOwned`, finding 019) drops a record
whose owner is not the query name — the type conjunct only narrows the
filter further — so insertion anywhere leaves it unchanged. -/
theorem cnameOwned_insert_frame {s : Sec} {x : RR} {small big : Response}
    (hins : RespInsert s x small big) {qn : Name} (hq : nameEq x.owner qn = false) :
    big.cnameOwned qn = small.cnameOwned qn := by
  obtain ⟨haa, hrc, htc, hra, hrest⟩ := hins
  have hans : big.answer.filter
        (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qn)
      = small.answer.filter
        (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qn) := by
    cases s with
    | ans => exact filter_insert_of_neg (by simp [hq]) hrest.1
    | auth => rw [hrest.1]
    | add => rw [hrest.1]
  exact Response.ext'
    (by rw [Response.cnameOwned_aa, Response.cnameOwned_aa, haa])
    (by rw [Response.cnameOwned_rcode, Response.cnameOwned_rcode, hrc])
    (by rw [Response.cnameOwned_answer, Response.cnameOwned_answer, hans])
    (by rw [Response.cnameOwned_authority, Response.cnameOwned_authority])
    (by rw [Response.cnameOwned_additional, Response.cnameOwned_additional])
    (by rw [Response.cnameOwned_ra, Response.cnameOwned_ra, hra])
    (by rw [Response.cnameOwned_tc, Response.cnameOwned_tc, htc])

/-! ## Negative-cache frames -/

/-- The negative-TTL extractor ignores an inserted record that is not an
SOA entitled at `nm` (insertion into any section). -/
theorem soaNegTtl_insert_frame {s : Sec} {x : RR} {small big : Response}
    (hins : RespInsert s x small big) {nm : Name}
    (hx : x.rdata.rtype = RRType.soa → isAncestor x.owner nm = false) :
    soaNegTtl nm big = soaNegTtl nm small := by
  obtain ⟨_, _, _, _, hrest⟩ := hins
  unfold soaNegTtl
  cases s with
  | ans => rw [hrest.2.1]
  | add => rw [hrest.2.1]
  | auth =>
    refine findSome?_insert_of_none ?_ hrest.2.1
    show (match x.rdata with
      | RData.soa _ _ _ _ _ _ m => if isAncestor x.owner nm then some (min x.ttl m) else none
      | _ => none) = none
    cases hrd : x.rdata with
    | soa mn rn se re rt ex mi =>
      have hsoa : x.rdata.rtype = RRType.soa := by rw [hrd]; rfl
      simp [hx hsoa]
    | a addr => rfl
    | ns h => rfl
    | cname t => rfl
    | mx p e => rfl
    | hinfo cu os => rfl
    | ptr t => rfl
    | generic t d => rfl

/-- **Negative-cache frame (authority insertion)**: an off-owner SOA (or
any non-SOA record) inserted into the authority section leaves the
negative cache write unchanged. -/
theorem absorbNeg_insert_auth {x : RR} {small big : Response}
    (hins : RespInsert .auth x small big) {pq : Query}
    (hx : x.rdata.rtype = RRType.soa → isAncestor x.owner pq.qname = false)
    (c : Cache) (now : Time) :
    c.absorbNeg now pq big = c.absorbNeg now pq small := by
  have hsoa := soaNegTtl_insert_frame hins (nm := pq.qname) hx
  obtain ⟨_, hrc, _, _, hans, _, _⟩ := hins
  unfold Cache.absorbNeg
  rw [hsoa, hrc, hans]

/-- Negative-cache frame (additional insertion): `absorbNeg` never reads
the additional section. -/
theorem absorbNeg_insert_add {x : RR} {small big : Response}
    (hins : RespInsert .add x small big) (pq : Query) (c : Cache) (now : Time) :
    c.absorbNeg now pq big = c.absorbNeg now pq small := by
  obtain ⟨_, hrc, _, _, hans, hauth, _⟩ := hins
  have hsoa : soaNegTtl pq.qname big = soaNegTtl pq.qname small := by
    unfold soaNegTtl
    rw [hauth]
  unfold Cache.absorbNeg
  rw [hsoa, hrc, hans]

/-- Negative-cache behaviour under answer insertion is FAIL-CLOSED: the
inserted record can only suppress a NODATA classification (RFC 2308 §2.2
reads "no relevant answer"); it never creates or alters a negative cache
entry. -/
theorem absorbNeg_insert_ans {x : RR} {small big : Response}
    (hins : RespInsert .ans x small big) (pq : Query) (c : Cache) (now : Time) :
    c.absorbNeg now pq big = c.absorbNeg now pq small ∨ c.absorbNeg now pq big = c := by
  obtain ⟨_, hrc, _, _, hansIns, hauth, _⟩ := hins
  have hsoa : soaNegTtl pq.qname big = soaNegTtl pq.qname small := by
    unfold soaNegTtl
    rw [hauth]
  have hbigne : big.answer.isEmpty = false := by
    obtain ⟨pre, post, _, hbg⟩ := hansIns
    rw [hbg]
    cases pre <;> simp
  unfold Cache.absorbNeg
  rw [hsoa, hrc]
  cases hst : soaNegTtl pq.qname small with
  | none => exact Or.inl rfl
  | some ttl =>
    cases hrcne : (small.rcode == RCode.nameError) with
    | true =>
      -- 039: the tightened NXDOMAIN arm also requires an empty answer, so the
      -- inserted answer record suppresses the name-wide negative (fail-closed).
      have hne := rcode_eq_of_beq hrcne
      exact Or.inr (by simp [hbigne, hne])
    | false => exact Or.inr (by simp [hbigne])

/-! ## Next-query frames -/

/-- **CNAME-chase frame**: an off-owner record (in particular an off-owner
CNAME) never becomes the chased CNAME. -/
theorem cnameRR_insert_frame {qn : Name} {x : RR} {small big : List RR}
    (hins : InsertedIn x small big) (hq : nameEq x.owner qn = false) :
    cnameRR qn big = cnameRR qn small := by
  unfold cnameRR
  exact find?_insert_of_neg (by simp [hq]) hins

theorem referralCut_congr {r1 r2 : Response} (hauth : r1.authority = r2.authority) :
    referralCut r1 = referralCut r2 := by
  unfold referralCut
  rw [hauth]

theorem referredServers_congr {r1 r2 : Response} (hauth : r1.authority = r2.authority) :
    referredServers r1 = referredServers r2 := by
  unfold referredServers
  rw [hauth]

theorem cutServers_congr {r1 r2 : Response} (hauth : r1.authority = r2.authority) :
    cutServers r1 = cutServers r2 := by
  unfold cutServers
  rw [referralCut_congr hauth, hauth]

theorem glueAddresses_congr {r1 r2 : Response} (hauth : r1.authority = r2.authority)
    (hadd : r1.additional = r2.additional) : glueAddresses r1 = glueAddresses r2 := by
  unfold glueAddresses
  rw [cutServers_congr hauth, referralCut_congr hauth, hadd]

theorem filterMap_congr_fun {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- Glue frame (answer insertion): glue never reads the answer section. -/
theorem glueAddresses_insert_ans {x : RR} {small big : Response}
    (hins : RespInsert .ans x small big) : glueAddresses big = glueAddresses small :=
  glueAddresses_congr hins.2.2.2.2.2.1 hins.2.2.2.2.2.2

/-- **Glue frame (additional insertion)**: an additional record outside
the delegation bailiwick is never selected as glue. -/
theorem glueAddresses_insert_add {x : RR} {small big : Response}
    (hins : RespInsert .add x small big)
    (hcut : isAncestor (referralCut big) x.owner = false) :
    glueAddresses big = glueAddresses small := by
  obtain ⟨_, _, _, _, hans, hauth, haddIns⟩ := hins
  have hcuts : referralCut big = referralCut small :=
    referralCut_congr hauth
  have hcutS : isAncestor (referralCut small) x.owner = false := by
    rw [← hcuts]
    exact hcut
  unfold glueAddresses
  rw [cutServers_congr hauth, hcuts]
  apply filterMap_congr_fun
  intro h _
  rw [find?_insert_of_neg (by simp [hcutS]) haddIns]

/-- **Glueless address-pick frame**: an off-chain record inserted into the
answer never changes which address `addressOf` selects for a glueless NS
host (the fix for the former `addressOf_ignores_owner_leak`). -/
theorem addressOf_insert_frame {q : Query} {x : RR} {small big : Response} {bw : Name}
    (hins : RespInsert .ans x small big) (hne : Unentitled q big bw x) :
    addressOf q.qname big = addressOf q.qname small := by
  have hforeign := not_entitled_chain (hne .answer)
  have hinsA : InsertedIn x small.answer big.answer := hins.2.2.2.2.1
  have hreach : reachableNames q.qname big.answer
      = reachStep small.answer (reachableNames q.qname small.answer) :=
    reachableNames_insert_eq hinsA hforeign
  have hpred : ∀ o : Name,
      (reachableNames q.qname big.answer).any (fun n => nameEq o n)
        = (reachableNames q.qname small.answer).any (fun n => nameEq o n) := by
    intro o
    rw [hreach]
    cases hs : (reachableNames q.qname small.answer).any (fun n => nameEq o n) with
    | true =>
      rw [List.any_eq_true] at hs ⊢
      obtain ⟨n, hn, hno⟩ := hs
      exact ⟨n, by unfold reachStep; exact List.mem_append_left _ hn, hno⟩
    | false =>
      rw [List.any_eq_false] at hs ⊢
      intro n hn
      exact hs n (reachableNames_complete
        (reachStep_sound (reachableNames_sound q.qname small.answer) n hn))
  have hfun : aRecordOf (reachableNames q.qname big.answer)
      = aRecordOf (reachableNames q.qname small.answer) := by
    funext r
    unfold aRecordOf
    rw [hpred r.owner]
  have hxnone : aRecordOf (reachableNames q.qname small.answer) x = none := by
    unfold aRecordOf
    rw [if_neg]
    rw [Bool.not_eq_true, List.any_eq_false]
    intro n hn
    simp [hforeign n (cnameReachable_of_subset hinsA.subset
      (reachableNames_sound q.qname small.answer n hn))]
  unfold addressOf
  rw [hfun, filterMap_insert_of_none hxnone hinsA]

/-- `addressOf` reads only the answer section. -/
theorem addressOf_congr_answer {owner : Name} {r1 r2 : Response}
    (hans : r1.answer = r2.answer) : addressOf owner r1 = addressOf owner r2 := by
  unfold addressOf
  rw [hans]

theorem foldl_ipMinOpt_isSome :
    ∀ (l : List IPv4) (a : IPv4), ∃ b, l.foldl ipMinOpt (some a) = some b := by
  intro l
  induction l with
  | nil => intro a; exact ⟨a, rfl⟩
  | cons x t ih =>
    intro a
    rw [List.foldl_cons]
    exact ih _

/-- An entitled A record in the answer guarantees the (owner-filtered)
address pick succeeds — the discharge shape for `gluelessNs`'s
`hnsaddr` premise. -/
theorem addressOf_isSome_of_entitled {owner : Name} {resp : Response} {r : RR}
    {ip : IPv4} {n : Name} (hr : r ∈ resp.answer) (hrd : r.rdata = RData.a ip)
    (hreach : CnameReachable owner resp.answer n) (hown : nameEq r.owner n = true) :
    ∃ a, addressOf owner resp = some a := by
  have hmem : ip ∈ resp.answer.filterMap
      (aRecordOf (reachableNames owner resp.answer)) := by
    refine List.mem_filterMap.mpr ⟨r, hr, ?_⟩
    unfold aRecordOf
    rw [if_pos (List.any_eq_true.mpr ⟨n, reachableNames_complete hreach, hown⟩), hrd]
  unfold addressOf
  cases hl : resp.answer.filterMap (aRecordOf (reachableNames owner resp.answer)) with
  | nil => rw [hl] at hmem; exact absurd hmem (by simp)
  | cons y t =>
    obtain ⟨b, hb⟩ := foldl_ipMinOpt_isSome t y
    refine ⟨b.toDotted, ?_⟩
    rw [List.foldl_cons, show ipMinOpt none y = some y from rfl, hb, Option.map_some]

theorem beq_ns_false_of_ne {t : RRType} (h : t ≠ RRType.ns) :
    (t == RRType.ns) = false := by
  cases t <;> first | rfl | exact absurd rfl h

/-- An off-cut owner is in particular not (CI-)equal to the cut. -/
theorem not_nameEq_cut_of_offcut {cut : Name} {x : RR}
    (hcut : isAncestor cut x.owner = false) :
    nameEq x.owner cut = false := by
  cases h : nameEq x.owner cut
  · rfl
  · exfalso
    have hlen := nameEq_length h
    have hanc : isAncestor cut x.owner = true := by
      unfold isAncestor
      have hble : Nat.ble cut.length x.owner.length = true := by
        rw [Nat.ble_eq]
        omega
      rw [hble]
      have hdrop : x.owner.length - cut.length = 0 := by omega
      rw [hdrop, List.drop_zero]
      show nameEq cut x.owner = true
      rw [nameEq_symm]
      exact h
    rw [hanc] at hcut
    exact Bool.noConfusion hcut

/-- The referral cut is unmoved by inserting an authority record whose
owner is not (CI-)equal to the cut: a non-NS record is never the cut
witness, and an NS record inserted ahead of the genuine delegation would
BE the cut — excluded by the off-cut premise. -/
theorem referralCut_insert_auth {x : RR} {small big : Response}
    (hins : RespInsert .auth x small big)
    (hocut : nameEq x.owner (referralCut big) = false) :
    referralCut big = referralCut small := by
  obtain ⟨_, _, _, _, hans, hauthIns, hadd⟩ := hins
  by_cases hns : (x.rdata.rtype == RRType.ns) = true
  · obtain ⟨pre, post, hsm, hbg⟩ := hauthIns
    unfold referralCut
    rw [hsm, hbg, List.find?_append, List.find?_append]
    cases hf : pre.find? (fun r => r.rdata.rtype == RRType.ns) with
    | some v => rfl
    | none =>
      exfalso
      have hbig : referralCut big = x.owner := by
        unfold referralCut
        rw [hbg, List.find?_append, hf, Option.none_or,
          List.find?_cons_of_pos (p := fun r : RR => r.rdata.rtype == RRType.ns) hns]
        rfl
      rw [hbig, nameEq_refl] at hocut
      exact Bool.noConfusion hocut
  · unfold referralCut
    rw [find?_insert_of_neg (by simpa using hns) hauthIns]

/-- The delegation's NS-host set at the cut is unmoved by inserting an
off-cut authority record. -/
theorem cutServers_insert_auth {x : RR} {small big : Response}
    (hins : RespInsert .auth x small big)
    (hocut : nameEq x.owner (referralCut big) = false) :
    cutServers big = cutServers small := by
  have hcuts := referralCut_insert_auth hins hocut
  obtain ⟨_, _, _, _, hans, hauthIns, hadd⟩ := hins
  unfold cutServers
  rw [← hcuts, filter_insert_of_neg hocut hauthIns]

/-- **Glue frame (authority insertion)**: an authority record owned
outside the delegation cut — NS or otherwise — never changes the referral
glue (the fix for the former `glueAddresses_offcut_ns_leak`). -/
theorem glueAddresses_insert_auth {x : RR} {small big : Response}
    (hins : RespInsert .auth x small big)
    (hcut : isAncestor (referralCut big) x.owner = false) :
    glueAddresses big = glueAddresses small := by
  have hocut := not_nameEq_cut_of_offcut hcut
  have hcuts := referralCut_insert_auth hins hocut
  have hserv := cutServers_insert_auth hins hocut
  obtain ⟨_, _, _, _, hans, hauthIns, hadd⟩ := hins
  unfold glueAddresses
  rw [hserv, hcuts, hadd]

/-- The referral slist derived from the cache inherits the cache-write
frame. -/
theorem referralSlist_insert_frame {s : Sec} {x : RR} {small big : Response}
    (hins : RespInsert s x small big) {bw : Name}
    (hbw : isAncestor bw x.owner = false) (c : Cache) (now now' : Time)
    (nm : Name) (fuel : Nat) :
    (c.absorb now bw big).referralSlist now' nm fuel
      = (c.absorb now bw small).referralSlist now' nm fuel := by
  rw [absorb_insert_frame hins hbw c now]

/-! ## Fail-closed classification -/

/-- Inserting anything into the answer section of a referral destroys its
referral classification — the model rejects rather than follows it
(fail-closed; this is the dirty-referral guard). -/
theorem isReferral_insert_ans {x : RR} {small big : Response}
    (hins : RespInsert .ans x small big) : big.isReferral = false := by
  obtain ⟨_, _, _, _, ⟨pre, post, _, hbg⟩, _, _⟩ := hins
  apply isReferral_false_of_answer_ne_nil
  rw [hbg]
  cases pre <;> simp

/-! ## The non-interference bundle -/

/-- **`handle_frame`** — non-interference for the owner-check family.

The model's response handler is the relational `Resolves`; every
observable it derives from a response flows through one of the filter
functions below. If `x` is entitled in NO role, then inserting `x` into
any section of the response changes none of them:

1. the delivered (scrubbed) answer,
2. the positive cache write (`Cache.absorb` at the processing bailiwick),
3. the trusted-arm cache write (`absorb` of `answerOwned`),
4. the negative-cache TTL source (`soaNegTtl`, at the probe name),
5. the negative cache write (`absorbNeg`; equal, or fail-closed suppressed
   when the insertion breaks a NODATA classification),
6. the chased CNAME (`cnameRR`),
7. the referral glue (`glueAddresses`), given the delegation-bailiwick
   negation at this response's own cut — including an inserted off-cut NS
   record (the fix for the former `glueAddresses_offcut_ns_leak`: the
   glue walk now only serves NS records owned at the referral cut),
8. the glueless address pick (`addressOf`, at the query name).

`pq` ranges over the probe names the resolver may negatively cache at
(ancestors of `q.qname`, per `StrictProbe`). -/
theorem handle_frame {q : Query} {s : Sec} {x : RR} {small big : Response} {bw : Name}
    (hins : RespInsert s x small big) (hne : Unentitled q big bw x) :
    scrubAnswer q.qname big.answer = scrubAnswer q.qname small.answer
    ∧ (∀ c now, Cache.absorb c now bw big = Cache.absorb c now bw small)
    ∧ (∀ c now, Cache.absorb c now q.qname (big.answerOwned q.qname)
        = Cache.absorb c now q.qname (small.answerOwned q.qname))
    ∧ (∀ nm, isAncestor nm q.qname = true → soaNegTtl nm big = soaNegTtl nm small)
    ∧ (∀ c now pq, isAncestor pq.qname q.qname = true →
        Cache.absorbNeg c now pq big = Cache.absorbNeg c now pq small
          ∨ Cache.absorbNeg c now pq big = c)
    ∧ cnameRR q.qname big.answer = cnameRR q.qname small.answer
    ∧ (isAncestor (referralCut big) x.owner = false →
        glueAddresses big = glueAddresses small)
    ∧ addressOf q.qname big = addressOf q.qname small := by
  have hforeign := not_entitled_chain (hne .answer)
  have hq := not_entitled_qname (hne .answer)
  have hbw := not_entitled_bailiwick (hne .delegation)
  have hsoaAt : ∀ nm, isAncestor nm q.qname = true →
      x.rdata.rtype = RRType.soa → isAncestor x.owner nm = false := by
    intro nm hnm hsoa
    cases h : isAncestor x.owner nm
    · rfl
    · rw [← not_entitled_soa (hne .negSoa) hsoa]
      exact (isAncestor_trans h hnm).symm
  have hansEq : s ≠ Sec.ans → big.answer = small.answer := by
    intro hs
    obtain ⟨_, _, _, _, hrest⟩ := hins
    cases s with
    | ans => exact absurd rfl hs
    | auth => exact hrest.1
    | add => exact hrest.1
  refine ⟨?_, absorb_insert_frame hins hbw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. deliver
    cases hs : s with
    | ans =>
      subst hs
      exact scrubAnswer_insert_frame hins.2.2.2.2.1 hforeign
    | auth => rw [hansEq (by simp [hs])]
    | add => rw [hansEq (by simp [hs])]
  · -- 3. trusted cache write
    intro c now
    rw [answerOwned_insert_frame hins hq]
  · -- 4. soaNegTtl
    intro nm hnm
    exact soaNegTtl_insert_frame hins (hsoaAt nm hnm)
  · -- 5. absorbNeg
    intro c now pq hpq
    cases hs : s with
    | ans =>
      subst hs
      exact absorbNeg_insert_ans hins pq c now
    | auth =>
      subst hs
      exact Or.inl (absorbNeg_insert_auth hins (hsoaAt pq.qname hpq) c now)
    | add =>
      subst hs
      exact Or.inl (absorbNeg_insert_add hins pq c now)
  · -- 6. cname chase
    cases hs : s with
    | ans =>
      subst hs
      exact cnameRR_insert_frame hins.2.2.2.2.1 hq
    | auth => rw [hansEq (by simp [hs])]
    | add => rw [hansEq (by simp [hs])]
  · -- 7. glue
    intro hcut
    cases hs : s with
    | ans =>
      subst hs
      exact glueAddresses_insert_ans hins
    | auth =>
      subst hs
      exact glueAddresses_insert_auth hins hcut
    | add =>
      subst hs
      exact glueAddresses_insert_add hins hcut
  · -- 8. glueless address pick
    cases hs : s with
    | ans =>
      subst hs
      exact addressOf_insert_frame hins hne
    | auth => exact addressOf_congr_answer (hansEq (by simp [hs]))
    | add => exact addressOf_congr_answer (hansEq (by simp [hs]))

/-! ## The generalised scrub-exclusion and the original as a corollary -/

/-- Generalisation of `scrubAnswer_no_foreign` to the role-parameterised
`Entitled`: a record not entitled in the answer role is never delivered. -/
theorem scrubAnswer_excludes_unentitled {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hne : ¬ Entitled q resp bw .answer x) : x ∉ scrubAnswer q.qname resp.answer :=
  scrubAnswer_excludes (not_entitled_chain hne)

/-- The original `scrubAnswer_no_foreign` (`Spec/AnswerAuthenticity.lean`),
re-derived as the answer-role corollary of the entitlement machinery. The
original theorem is untouched; this pins that its statement is exactly
`¬ Entitled · · · .answer ·` exclusion. -/
theorem scrubAnswer_no_foreign_of_role {qname : Name} {answer : List RR} {x : RR}
    (hrr : x ∈ scrubAnswer qname answer)
    (hforeign : ∀ n, CnameReachable qname answer n → nameEq x.owner n = false) : False :=
  scrubAnswer_excludes_unentitled
    (q := { qname := qname, qtype := QType.star })
    (resp := { aa := false, rcode := RCode.noError, answer := answer,
               authority := [], additional := [] })
    (bw := [])
    (entitled_answer_of_chain hforeign) hrr

/-! ## The owner-check fault family as one-line corollaries -/

/-- **004 (subdomain rider)**: a rider inserted into the answer that is
entitled in no role is dropped from the delivered set, and the trusted-arm
cache write is as if it had never been there. -/
theorem subdomain_rider_inert {q : Query} {x : RR} {small big : Response} {bw : Name}
    (hins : RespInsert .ans x small big) (hne : Unentitled q big bw x) :
    x ∉ scrubAnswer q.qname big.answer
    ∧ scrubAnswer q.qname big.answer = scrubAnswer q.qname small.answer
    ∧ ∀ c now, Cache.absorb c now q.qname (big.answerOwned q.qname)
        = Cache.absorb c now q.qname (small.answerOwned q.qname) :=
  ⟨scrubAnswer_excludes_unentitled (hne .answer),
   (handle_frame hins hne).1, (handle_frame hins hne).2.2.1⟩

/-- **036 (off-owner CNAME)**: a CNAME whose owner is not the query name
is never chased — the next query is derived from an unchanged `cnameRR`. -/
theorem offowner_cname_not_chased {q : Query} {x : RR} {small big : Response} {bw : Name}
    {target : Name} (hins : RespInsert .ans x small big)
    (_hcn : x.rdata = RData.cname target) (hne : Unentitled q big bw x) :
    cnameRR q.qname big.answer = cnameRR q.qname small.answer :=
  (handle_frame hins hne).2.2.2.2.2.1

/-- **012/013 (off-owner SOA)**: an SOA whose owner is not an ancestor of
the query name is neither used as a negative-TTL source nor negatively
cached, at the query and at every strict-probe ancestor. -/
theorem offowner_soa_not_negcached {q : Query} {x : RR} {small big : Response} {bw : Name}
    (hins : RespInsert .auth x small big) (hne : Unentitled q big bw x)
    (pq : Query) (hpq : isAncestor pq.qname q.qname = true) (c : Cache) (now : Time) :
    Cache.absorbNeg c now pq big = Cache.absorbNeg c now pq small
    ∧ soaNegTtl pq.qname big = soaNegTtl pq.qname small := by
  have hsoaAt : x.rdata.rtype = RRType.soa → isAncestor x.owner pq.qname = false := by
    intro hsoa
    cases h : isAncestor x.owner pq.qname
    · rfl
    · rw [← not_entitled_soa (hne .negSoa) hsoa]
      exact (isAncestor_trans h hpq).symm
  exact ⟨absorbNeg_insert_auth hins hsoaAt c now,
    soaNegTtl_insert_frame hins hsoaAt⟩

/-- **Answer-injection**: a foreign record placed in any section never
reaches the client — it is excluded from the scrubbed answer and the
delivered set is unchanged. -/
theorem answer_injection_inert {q : Query} {s : Sec} {x : RR} {small big : Response}
    {bw : Name} (hins : RespInsert s x small big) (hne : Unentitled q big bw x) :
    x ∉ scrubAnswer q.qname big.answer
    ∧ scrubAnswer q.qname big.answer = scrubAnswer q.qname small.answer :=
  ⟨scrubAnswer_excludes_unentitled (hne .answer), (handle_frame hins hne).1⟩

/-- **047 (out-of-bailiwick additional, model side)**: an additional record
whose owner is off the query bailiwick is entitled in the additional role in
NO response — the delivery scrub is justified in dropping it. -/
theorem offcut_additional_unentitled {q : Query} {resp : Response} {bw : Name} {x : RR}
    (hoff : isAncestor q.qname x.owner = false) : ¬ Entitled q resp bw .additional x := by
  intro h
  have : isAncestor q.qname x.owner = true := h
  rw [this] at hoff
  exact Bool.noConfusion hoff

/-! ## The two W1 model gaps, closed: concrete scrub pins -/

/-- **MODEL GAP CLOSED (W1 finding, fixed).** `glueAddresses` formerly
collected glue for the hosts of EVERY authority-section NS record
(`referredServers`), including NS records owned ABOVE the delegation cut —
an off-cut NS record smuggled next to the genuine delegation could grow
the glue set with the address of a host the delegation never referred to.
The glue walk is now restricted to `cutServers` (NS records owned,
case-insensitively, at `referralCut` — matching unbound's scrubber, which
deletes off-cut NS records, and the impl's `ownerRaws`-filtered
`extractNsNames`). The former counterexample is now inert; the general
statement is `glueAddresses_insert_auth` above (bundled as
`handle_frame`'s clause 7, whose non-NS proviso is GONE). This concrete
twin pins the original W1 witness: the ROOT-owned `NS2.SUB` NS record no
longer contributes glue. -/
theorem glueAddresses_offcut_ns_scrubbed :
    ∀ (x : RR) (small big : Response),
      x = rr [] 100 (.ns (N ["NS2", "SUB"])) →
      small = { aa := false, rcode := RCode.noError, answer := [],
                authority := [rr ["SUB"] 100 (.ns (N ["NS1", "SUB"]))],
                additional := [rr ["NS1", "SUB"] 100 (.a ⟨7, 7, 7, 7⟩),
                               rr ["NS2", "SUB"] 100 (.a ⟨8, 8, 8, 8⟩)] } →
      big = { aa := false, rcode := RCode.noError, answer := [],
              authority := [rr ["SUB"] 100 (.ns (N ["NS1", "SUB"])),
                            rr [] 100 (.ns (N ["NS2", "SUB"]))],
              additional := [rr ["NS1", "SUB"] 100 (.a ⟨7, 7, 7, 7⟩),
                             rr ["NS2", "SUB"] 100 (.a ⟨8, 8, 8, 8⟩)] } →
      RespInsert .auth x small big
      ∧ isAncestor (referralCut big) x.owner = false
      ∧ x.rdata.rtype ≠ RRType.soa
      ∧ big.answer = []
      ∧ glueAddresses big = glueAddresses small := by
  rintro x small big rfl rfl rfl
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl,
      ⟨[rr ["SUB"] 100 (.ns (N ["NS1", "SUB"]))], [], rfl, rfl⟩, rfl⟩,
    by decide, by decide, rfl, by decide⟩

/-- **MODEL GAP CLOSED (W1 finding, fixed).** `addressOf` — the function
the `gluelessNs` rule uses to pick the address of a glueless NS host from
the sub-resolution's verdict — now filters to A records whose owner lies
on the CNAME chain rooted at the NS host (matching the impl's
`extractAAddress` reach-guard). The former counterexample (an off-owner
`EVIL.COM` A record inserted next to the genuine `NS1.SUB` A record
redirecting the pick) is now inert; the general statement is
`addressOf_insert_frame` above (bundled as `handle_frame`'s clause 8).
This concrete twin pins the original W1 witness. -/
theorem addressOf_offowner_scrubbed :
    ∀ (x : RR) (small big : Response),
      x = rr ["EVIL", "COM"] 100 (.a ⟨1, 1, 1, 1⟩) →
      small = { aa := false, rcode := RCode.noError,
                answer := [rr ["NS1", "SUB"] 100 (.a ⟨9, 9, 9, 9⟩)],
                authority := [], additional := [] } →
      big = { aa := false, rcode := RCode.noError,
              answer := [rr ["EVIL", "COM"] 100 (.a ⟨1, 1, 1, 1⟩),
                         rr ["NS1", "SUB"] 100 (.a ⟨9, 9, 9, 9⟩)],
              authority := [], additional := [] } →
      RespInsert .ans x small big
      ∧ nameEq x.owner (N ["NS1", "SUB"]) = false
      ∧ addressOf (N ["NS1", "SUB"]) big = addressOf (N ["NS1", "SUB"]) small := by
  rintro x small big rfl rfl rfl
  exact ⟨⟨rfl, rfl, rfl, rfl,
      ⟨[], [rr ["NS1", "SUB"] 100 (.a ⟨9, 9, 9, 9⟩)], rfl, rfl⟩, rfl, rfl⟩,
    by decide, by decide⟩

end VeriDNS.Spec.Net
