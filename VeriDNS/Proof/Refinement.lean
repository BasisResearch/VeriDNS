import VeriDNS.Impl.Cache
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Server
import VeriDNS.RFC.Check
import VeriDNS.Proof.DomainName
import VeriDNS.Proof.NameTreeComplete
import VeriDNS.Proof.Cache
import VeriDNS.Spec.NetworkSemantics

namespace VeriDNS.Proof.Refinement

open VeriDNS.Spec (Trustworthiness RRType RRClass)
open VeriDNS.Impl
open VeriDNS.Impl.DomainName (nameEqCI)

def αType (t : BitVec 16) : Option RRType :=
  match t.toNat with
  | 1 => some .a   | 2 => some .ns   | 3 => some .md    | 4 => some .mf
  | 5 => some .cname | 6 => some .soa | 7 => some .mb   | 8 => some .mg
  | 9 => some .mr  | 10 => some .null | 11 => some .wks | 12 => some .ptr
  | 13 => some .hinfo | 14 => some .minfo | 15 => some .mx | 16 => some .txt
  | _ => none

def αClass (c : BitVec 16) : Option RRClass :=
  match c.toNat with
  | 1 => some .in | 2 => some .cs | 3 => some .ch | 4 => some .hs | _ => none

/-- Abstract a wire QTYPE to the model's `QType`: `255` (QTYPE=ANY/`*`) → `.star`; otherwise the
    abstracted RR type wrapped as `.rr` (`none` for an unmodelled type). The query-side analogue of
    `αType`, used by the simulation to relate the wire query's qtype to the model `Query.qtype`. -/
def αQType (qt : BitVec 16) : Option VeriDNS.Spec.Net.QType :=
  if qt.toNat = 255 then some .star else (αType qt).map .rr

def αName (w : ByteArray) : Option VeriDNS.Spec.Net.Name :=
  match DomainName.wireFormatToLabels w with
  | .ok labels => some labels.toList
  | .error _ => none

/-- **`αName` validity**: an abstracted wire name has only DNS-valid labels (nonempty, ≤63 bytes) —
    `αName` succeeds exactly when `wireFormatToLabels` does, whose per-label guards enforce this
    (`Proof.DomainName.wireFormatToLabels_valid`). -/
theorem αName_valid {w : ByteArray} {na : VeriDNS.Spec.Net.Name} (h : αName w = some na) :
    ∀ x ∈ na, 0 < x.size ∧ x.size ≤ 63 := by
  unfold αName at h
  split at h
  · next labels hlab =>
    have hna : labels.toList = na := Option.some.inj h
    intro x hx
    exact VeriDNS.Proof.DomainName.wireFormatToLabels_valid hlab x (hna ▸ hx)
  · exact absurd h (by simp)

/-! ### Step 2: the bailiwick filter refines the model's `Net.isAncestor`

  The implementation's `Resolver.isAncestorB` and the model's `Net.isAncestor` use *different*
  case-fold machineries (`foldCaseByte`/`foldNameCase` vs `foldByte`/`bytesEqCI`/`labelEq`). These
  lemmas prove they agree, so the impl filter provably *is* the model's `keep := isAncestor bw
  owner` — the basis of the write-side anti-poison refinement. -/

/-- The model's byte case-fold (`Net.foldByte`) equals the implementation's (`foldCaseByte`). -/
theorem foldByte_eq (x : UInt8) :
    VeriDNS.Spec.Net.foldByte x = DomainName.foldCaseByte x := by
  unfold VeriDNS.Spec.Net.foldByte DomainName.foldCaseByte
  simp only [Nat.ble_eq, Bool.cond_eq_ite, decide_eq_true_eq, Bool.and_eq_true,
    UInt8.le_iff_toNat_le, show UInt8.toNat 65 = 65 from rfl, show UInt8.toNat 90 = 90 from rfl]

/-- `foldNameCase` distributes over `ByteArray` append (it is a per-byte map). A codec helper toward
    the fold/encode commutation `foldNameCase (labelsToWireFormat ls) = labelsToWireFormat
    (ls.map foldNameCase)` that the canonical-name half of `hhit` completeness needs. -/
theorem foldNameCase_append (a b : ByteArray) :
    DomainName.foldNameCase (a ++ b)
      = DomainName.foldNameCase a ++ DomainName.foldNameCase b := by
  apply ByteArray.ext
  simp [DomainName.foldNameCase, ByteArray.data_append, Array.map_append]

/-- Case-folding fixes bytes ≤ 63 — in particular DNS length bytes (labels ≤ 63 octets), which are
    below the `'A'`=65 lower bound of `foldCaseByte`. So `foldNameCase` leaves the wire length
    prefixes untouched, the key fact for the fold/encode commutation. -/
theorem foldCaseByte_le63 (b : UInt8) (h : b ≤ 63) : DomainName.foldCaseByte b = b := by
  unfold DomainName.foldCaseByte
  have hcond : (65 ≤ b && b ≤ 90) = false := by
    rcases Nat.lt_or_ge b.toNat 65 with hlt | hge
    · simp only [Bool.and_eq_false_iff]; left
      simp only [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, Nat.not_le]; exact hlt
    · exfalso; rw [UInt8.le_iff_toNat_le] at h
      simp only [show UInt8.toNat 63 = 63 from rfl] at h; omega
  simp [hcond]

/-- A valid (≤63-octet) label's length byte is below the case-fold range, so it is left untouched. -/
theorem size_toUInt8_le63 (x : ByteArray) (h : x.size ≤ 63) : x.size.toUInt8 ≤ 63 := by
  have hsz : x.size.toUInt8.toNat = x.size := by
    have : x.size.toUInt8.toNat = x.size % 256 := rfl
    omega
  rw [UInt8.le_iff_toNat_le, hsz, show UInt8.toNat 63 = 63 from rfl]; exact h

/-- Case-folding a single ≤63 length byte is the identity. -/
theorem foldNameCase_push (b : UInt8) (h : b ≤ 63) :
    DomainName.foldNameCase (ByteArray.empty.push b) = ByteArray.empty.push b := by
  apply ByteArray.ext
  simp [DomainName.foldNameCase, foldCaseByte_le63 b h]

/-- **Fold/encode commutation (list form).** Case-folding the wire encoding of a label list equals
    encoding the per-label case-folded list — because the length prefixes (≤63) are below the fold
    range. The structural heart of the canonical-name half of `hhit` completeness. -/
theorem foldNameCase_labelsToWireFormatGo (l : List ByteArray) (hv : ∀ x ∈ l, x.size ≤ 63) :
    DomainName.foldNameCase (DomainName.labelsToWireFormatGo l)
      = DomainName.labelsToWireFormatGo (l.map DomainName.foldNameCase) := by
  induction l with
  | nil =>
    show DomainName.foldNameCase ⟨#[0]⟩ = ⟨#[0]⟩
    apply ByteArray.ext
    show (#[(0:UInt8)]).map DomainName.foldCaseByte = #[0]
    rw [Array.map_singleton, show DomainName.foldCaseByte 0 = 0 from by decide]
  | cons x rest ih =>
    simp only [List.map_cons, DomainName.labelsToWireFormatGo]
    rw [foldNameCase_append, foldNameCase_append,
        ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))]
    have hxsz : (DomainName.foldNameCase x).size = x.size := Array.size_map
    rw [foldNameCase_push x.size.toUInt8 (size_toUInt8_le63 x (hv x List.mem_cons_self)), hxsz]

/-- **Fold/encode commutation (array form).** `αName`/`nameEqCI` interplay for canonical names: the
    case-fold of a canonical wire name is the canonical encoding of its case-folded labels. -/
theorem foldNameCase_labelsToWireFormat (ls : Array ByteArray) (hv : ∀ x ∈ ls, x.size ≤ 63) :
    DomainName.foldNameCase (DomainName.labelsToWireFormat ls)
      = DomainName.labelsToWireFormat (ls.map DomainName.foldNameCase) := by
  unfold DomainName.labelsToWireFormat
  rw [foldNameCase_labelsToWireFormatGo ls.toList (fun x hx => hv x (Array.mem_def.mpr hx)),
    Array.toList_map]

/-- `bytesEqCI` holds whenever the two byte lists have equal case-folds (`foldCaseByte`). -/
theorem bytesEqCI_of_mapEq (as bs : List UInt8)
    (h : as.map DomainName.foldCaseByte = bs.map DomainName.foldCaseByte) :
    VeriDNS.Spec.Net.bytesEqCI as bs = true := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons b bs => simp at h
  | cons a as ih => cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      unfold VeriDNS.Spec.Net.bytesEqCI
      rw [foldByte_eq, foldByte_eq, h.1]
      simp only [beq_self_eq_true, Bool.true_and]
      exact ih bs h.2

/-- Equal case-folds (`foldNameCase`) imply the model's case-insensitive label equality (`labelEq`). -/
theorem labelEq_of_foldEq (x y : ByteArray)
    (h : DomainName.foldNameCase x = DomainName.foldNameCase y) :
    VeriDNS.Spec.Net.labelEq x y = true := by
  unfold VeriDNS.Spec.Net.labelEq
  apply bytesEqCI_of_mapEq
  have hd : x.data.map DomainName.foldCaseByte = y.data.map DomainName.foldCaseByte := by
    unfold DomainName.foldNameCase at h; injection h
  rw [← Array.toList_map, ← Array.toList_map, hd]

/-- Two label lists with equal per-label case-folds are `nameEq` (the model's CI name equality). -/
theorem nameEq_of_mapfold (xs ys : List ByteArray)
    (h : xs.map DomainName.foldNameCase = ys.map DomainName.foldNameCase) :
    VeriDNS.Spec.Net.nameEq xs ys = true := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih => cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      unfold VeriDNS.Spec.Net.nameEq
      rw [labelEq_of_foldEq x y h.1]
      simp only [Bool.true_and]
      exact ih ys h.2

/-- Reverse of `bytesEqCI_of_mapEq`: `bytesEqCI` implies equal case-folds. -/
theorem mapEq_of_bytesEqCI (as bs : List UInt8)
    (h : VeriDNS.Spec.Net.bytesEqCI as bs = true) :
    as.map DomainName.foldCaseByte = bs.map DomainName.foldCaseByte := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons b bs => simp [VeriDNS.Spec.Net.bytesEqCI] at h
  | cons a as ih => cases bs with
    | nil => simp [VeriDNS.Spec.Net.bytesEqCI] at h
    | cons b bs =>
      unfold VeriDNS.Spec.Net.bytesEqCI at h
      simp only [Bool.and_eq_true] at h
      rw [foldByte_eq, foldByte_eq] at h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨eq_of_beq h.1, ih bs h.2⟩

/-- Reverse of `labelEq_of_foldEq`: the model's `labelEq` implies equal `foldNameCase`. -/
theorem foldEq_of_labelEq (x y : ByteArray) (h : VeriDNS.Spec.Net.labelEq x y = true) :
    DomainName.foldNameCase x = DomainName.foldNameCase y := by
  unfold VeriDNS.Spec.Net.labelEq at h
  have hm := mapEq_of_bytesEqCI x.data.toList y.data.toList h
  have harr : x.data.map DomainName.foldCaseByte = y.data.map DomainName.foldCaseByte := by
    apply Array.toList_inj.mp
    rw [Array.toList_map, Array.toList_map]; exact hm
  unfold DomainName.foldNameCase
  rw [harr]

/-- Reverse of `nameEq_of_mapfold`: the model's `nameEq` implies equal per-label case-folds. -/
theorem mapfold_of_nameEq (xs ys : List ByteArray)
    (h : VeriDNS.Spec.Net.nameEq xs ys = true) :
    xs.map DomainName.foldNameCase = ys.map DomainName.foldNameCase := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp [VeriDNS.Spec.Net.nameEq] at h
  | cons x xs ih => cases ys with
    | nil => simp [VeriDNS.Spec.Net.nameEq] at h
    | cons y ys =>
      unfold VeriDNS.Spec.Net.nameEq at h
      simp only [Bool.and_eq_true] at h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨foldEq_of_labelEq x y h.1, ih ys h.2⟩

/-- **Reverse name correspondence (under canonicity).** If `a`, `b` abstract (`αName`) to
    `nameEq`-equal model names and are *canonical* wire names (`a = labelsToWireFormatGo (its labels)`,
    valid ≤63 labels — the `WfRR` cache invariant), they are case-insensitively equal wire names
    (`nameEqCI`). The converse of `αName_of_nameEqCI`, needed for the COMPLETENESS half of `hhit`
    (recovering the impl predicate from a model `matching` entry). The canonicity hypothesis is
    essential — without it the converse is false (`αName` ignores post-null trailing bytes that
    `nameEqCI`/`foldNameCase` fold). Assembles the fold/encode commutation
    (`foldNameCase_labelsToWireFormatGo`) with `mapfold_of_nameEq`. -/
theorem nameEqCI_of_αName_canonical {a b : ByteArray} {na nb : VeriDNS.Spec.Net.Name}
    (h : VeriDNS.Spec.Net.nameEq na nb = true)
    (hca : a = DomainName.labelsToWireFormatGo na) (hcb : b = DomainName.labelsToWireFormatGo nb)
    (hva : ∀ x ∈ na, x.size ≤ 63) (hvb : ∀ x ∈ nb, x.size ≤ 63) :
    VeriDNS.Impl.DomainName.nameEqCI a b = true := by
  rw [VeriDNS.Proof.NameTree.nameEqCI_iff, hca, hcb,
      foldNameCase_labelsToWireFormatGo na hva, foldNameCase_labelsToWireFormatGo nb hvb,
      mapfold_of_nameEq na nb h]

/-- **Name-abstraction transfer**: if `a` and `b` are case-insensitively equal wire names and `b`
    abstracts (`αName`), then `a` abstracts too, to a model name `nameEq`-equal to `b`'s. So a stored
    cache entry whose owner matches the (abstractable) query name is itself abstractable and matches
    in the model — the reusable foundation for the cacheHit/negHit simulation branches. -/
theorem αName_of_nameEqCI {a b : ByteArray} {nb : VeriDNS.Spec.Net.Name}
    (h : nameEqCI a b = true) (hb : αName b = some nb) :
    ∃ na, αName a = some na ∧ VeriDNS.Spec.Net.nameEq na nb = true := by
  have hfold : DomainName.foldNameCase a = DomainName.foldNameCase b :=
    VeriDNS.Proof.NameTree.nameEqCI_iff.mp h
  unfold αName at hb ⊢
  cases hbl : DomainName.wireFormatToLabels b with
  | error e => rw [hbl] at hb; exact absurd hb (by simp)
  | ok bL =>
    rw [hbl] at hb; injection hb with hb; subst hb
    have hfb := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok b bL hbl
    cases hal : DomainName.wireFormatToLabels a with
    | error ea =>
      obtain ⟨ea', hea'⟩ := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_error a ea hal
      rw [hfold, hfb] at hea'
      exact absurd hea' (by simp)
    | ok aL =>
      refine ⟨aL.toList, rfl, ?_⟩
      have hfa := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok a aL hal
      rw [hfold, hfb] at hfa
      injection hfa with hfa
      apply nameEq_of_mapfold
      have := congrArg Array.toList hfa
      simpa using this.symm

/-- **`nameEqCI` (impl, case-insensitive byte compare) AGREES with `nameEq` (model, per-label `bytesEqCI`)
    on canonical, abstractable wire names — as a `Bool` equality (both directions).** Forward via
    `αName_of_nameEqCI`; backward via `nameEqCI_of_αName_canonical` (needs the canonical-wire-form hypotheses
    `a = labelsToWireFormatGo na`, discharged for decoded names by `parseRaw_name_canonical`). This is the
    per-element name-match bridge `hpoint`'s `find?` first-match agreement needs: a model `nameEq`-hit forces
    the impl `nameEqCI`-hit and vice-versa, so the two glue scans pick the SAME element. -/
theorem nameEqCI_eq_nameEq {a b : ByteArray} {na nb : VeriDNS.Spec.Net.Name}
    (hca : a = DomainName.labelsToWireFormatGo na) (hva : ∀ x ∈ na, x.size ≤ 63) (hαa : αName a = some na)
    (hcb : b = DomainName.labelsToWireFormatGo nb) (hvb : ∀ x ∈ nb, x.size ≤ 63) (hαb : αName b = some nb) :
    VeriDNS.Impl.DomainName.nameEqCI a b = VeriDNS.Spec.Net.nameEq na nb := by
  by_cases hne : VeriDNS.Spec.Net.nameEq na nb = true
  · rw [hne]; exact nameEqCI_of_αName_canonical hne hca hcb hva hvb
  · rw [Bool.not_eq_true] at hne
    rw [hne]
    cases hci : VeriDNS.Impl.DomainName.nameEqCI a b with
    | false => rfl
    | true =>
      obtain ⟨na', hαa', hnt⟩ := αName_of_nameEqCI hci hαb
      obtain rfl : na' = na := Option.some.inj (hαa'.symm.trans hαa)
      rw [hne] at hnt; exact absurd hnt (by simp)

/-- **Names of different byte-length are case-insensitively distinct.** `nameEqCI` is `foldNameCase`-then-`==`,
    and `foldNameCase` preserves size, so unequal sizes ⟹ `nameEqCI = false`. Reduces the `walkNs` intermediates'
    distinctness (an intermediate suffix vs the cut's NS owner — different label counts ⟹ different wire size)
    to a pure size argument, feeding `lookup_empty_after_cacheRRs`'s `hbwlive`. -/
theorem nameEqCI_size_ne {a b : ByteArray} (h : a.size ≠ b.size) :
    VeriDNS.Impl.DomainName.nameEqCI a b = false := by
  rw [← Bool.not_eq_true, VeriDNS.Proof.NameTree.nameEqCI_iff]
  intro heq
  exact h (by rw [← VeriDNS.Proof.NameTree.foldNameCase_size a,
    ← VeriDNS.Proof.NameTree.foldNameCase_size b, heq])

/-- **An in-bailiwick name and an out-of-bailiwick name are case-insensitively distinct.** Contrapositive of
    `isAncestorB_congr` (the bailiwick test depends only on a name's case-fold): if `owner` and `n` disagree on
    `isAncestorB bw`, they can't be `nameEqCI`-equal. Used in the in-bailiwick resolution: an out-of-bailiwick NS
    name (`isAncestorB cut · = false`) cannot match an in-bailiwick glue owner (`= true`), so it gets NO glue and
    is dropped from `modelSlistOf` — the bridge for `modelSlistOf(re-derived) = modelSlistOf(installed)`. -/
theorem nameEqCI_false_of_isAncestorB_ne {bw owner n : ByteArray}
    (h : Resolver.isAncestorB bw owner ≠ Resolver.isAncestorB bw n) :
    VeriDNS.Impl.DomainName.nameEqCI owner n = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  exact h (VeriDNS.Proof.NameTree.isAncestorB_congr bw owner n hc)

/-- **An out-of-bailiwick NS name gets NO glue from in-bailiwick glue records.** Every glue owner is at/below
    the cut (`hglue`), but `n` is not (`hn`); by `nameEqCI_false_of_isAncestorB_ne` no glue owner `nameEqCI`-
    matches `n`, so `findSome?` returns `none`. So `n` contributes nothing to `modelSlistOf` — the core of the
    in-bailiwick drop bridging `modelSlistOf(installed all-NS) = modelSlistOf(in-bailiwick NS)`. -/
theorem glue_findSome_none_of_out_of_bailiwick (cut n : ByteArray)
    (glue : Array (ByteArray × BitVec 32))
    (hn : Resolver.isAncestorB cut n = false)
    (hglue : ∀ gp ∈ glue, Resolver.isAncestorB cut gp.1 = true) :
    glue.findSome? (fun (gn, ga) =>
      if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none) = none := by
  rw [Array.findSome?_eq_none_iff]
  intro gp hgp
  have hne : VeriDNS.Impl.DomainName.nameEqCI gp.1 n = false :=
    nameEqCI_false_of_isAncestorB_ne (by rw [hglue gp hgp, hn]; simp)
  simp [hne]

/-- **The bridge: the impl bailiwick predicate refines the model's `Net.isAncestor`.** If
    `Resolver.isAncestorB bw owner` holds and both names abstract (`αName`), then the model's
    `isAncestor` holds of their abstractions. So the impl filter's `keep` is the model's `keep`. -/
theorem isAncestorB_isAncestor (bw owner : ByteArray) (bwN ownerN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (hown : αName owner = some ownerN)
    (h : Resolver.isAncestorB bw owner = true) :
    VeriDNS.Spec.Net.isAncestor bwN ownerN = true := by
  unfold αName at hbw hown
  cases hbwl : DomainName.wireFormatToLabels bw with
  | error e => rw [hbwl] at hbw; exact absurd hbw (by simp)
  | ok bwL =>
  cases hownl : DomainName.wireFormatToLabels owner with
  | error e => rw [hownl] at hown; exact absurd hown (by simp)
  | ok ownerL =>
    rw [hbwl] at hbw; rw [hownl] at hown
    injection hbw with hbw; injection hown with hown
    subst hbw; subst hown
    unfold Resolver.isAncestorB at h
    rw [hbwl, hownl] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, hbeq⟩ := h
    unfold VeriDNS.Spec.Net.isAncestor
    rw [Nat.ble_eq.mpr (by simpa using hlen)]
    simp only [cond_true]
    apply nameEq_of_mapfold
    rw [List.map_drop]
    simpa using hbeq

/-- Reverse of `isAncestorB_isAncestor`: under name canonicity, the *model*
    bailiwick test (`isAncestor` on abstracted names) implies the *impl* one
    (`isAncestorB` on the wire bytes). Together with the forward direction this
    gives the bidirectional bailiwick correspondence `hcorr`'s write-path Perm
    needs — the section-filter membership is now an iff, not just impl ⟹ model. -/
theorem isAncestor_isAncestorB (bw owner : ByteArray) (bwN ownerN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (hown : αName owner = some ownerN)
    (h : VeriDNS.Spec.Net.isAncestor bwN ownerN = true) :
    Resolver.isAncestorB bw owner = true := by
  unfold αName at hbw hown
  cases hbwl : DomainName.wireFormatToLabels bw with
  | error e => rw [hbwl] at hbw; exact absurd hbw (by simp)
  | ok bwL =>
  cases hownl : DomainName.wireFormatToLabels owner with
  | error e => rw [hownl] at hown; exact absurd hown (by simp)
  | ok ownerL =>
    rw [hbwl] at hbw; rw [hownl] at hown
    injection hbw with hbw; injection hown with hown
    subst hbw; subst hown
    unfold VeriDNS.Spec.Net.isAncestor at h
    unfold Resolver.isAncestorB
    rw [hbwl, hownl]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases hlen : Nat.ble bwL.toList.length ownerL.toList.length = true
    · rw [hlen, cond_true] at h
      refine ⟨by simpa using hlen, ?_⟩
      have := mapfold_of_nameEq _ _ h
      rw [List.map_drop] at this
      simpa using this
    · rw [Bool.eq_false_iff.mpr hlen, cond_false] at h; exact absurd h (by simp)

/-- `Array.foldl` over an array equals `List.foldl` over its `toList`. -/
theorem array_foldl_toList {β : Type} (f : β → ByteArray → β) (init : β) (a : Array ByteArray) :
    a.foldl f init = a.toList.foldl f init := by
  rw [← List.foldl_toArray, Array.toArray_toList]

/-- **Provenance for `DnsCache.store`**: a record in the updated cache was already there or is the
    freshly-stored RR. -/
theorem mem_store_records {c : Cache.DnsCache} {rr : VeriDNS.Spec.ResourceRecord} {now : UInt32}
    {cred : Trustworthiness} {e : Cache.CacheEntry}
    (h : e ∈ (c.store rr now cred).records) : e ∈ c.records ∨ e.rr = rr := by
  unfold Cache.DnsCache.store at h
  simp only [Array.mem_push] at h
  rcases h with h | h
  · exact Or.inl (Array.mem_filter.mp h).1
  · subst h; exact Or.inr rfl

/-- `storeChecked` either no-ops or delegates to `store`. -/
theorem storeChecked_cases (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) :
    c.storeChecked rr cred now = c ∨ c.storeChecked rr cred now = c.store rr now cred := by
  simp only [Cache.DnsCache.storeChecked]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **Provenance for `storeChecked`**: it only no-ops or delegates to `store`. -/
theorem mem_storeChecked_records {c : Cache.DnsCache} {rr : VeriDNS.Spec.ResourceRecord}
    {cred : Trustworthiness} {now : UInt32} {e : Cache.CacheEntry}
    (h : e ∈ (c.storeChecked rr cred now).records) : e ∈ c.records ∨ e.rr = rr := by
  rcases storeChecked_cases c rr cred now with heq | heq
  · rw [heq] at h; exact Or.inl h
  · rw [heq] at h; exact mem_store_records h

/-- **`cacheRRs` splits over a concatenation of raw sections** (`foldl` over `++`). Lets the referral absorb
    be split at the NS record: `cacheRRs c (pre ++ [nsRaw] ++ post)` first absorbs `pre`, then stores the NS
    (`storeChecked_self_live`), then absorbs `post` (which preserves it, `mem_cacheRRs_preserve`) — the
    structural backbone of the absorb-stores-the-NS half of the referral cache round-trip. -/
theorem cacheRRs_append (c : Cache.DnsCache) (raws₁ raws₂ : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) :
    Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c (raws₁ ++ raws₂) cred now
      = Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws₁ cred now)
          raws₂ cred now := by
  unfold Resolver.cacheRRs
  rw [Array.foldl_append]

/-- **`cacheRRs` on a singleton is one `storeChecked`.** -/
theorem cacheRRs_singleton (X : Cache.DnsCache) (b : ByteArray) (cred : Trustworthiness) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) X #[b] cred now
      = X.storeChecked rr cred now := by
  unfold Resolver.cacheRRs
  simp [hp]
  rfl

/-- **A genuinely-stored NS in the absorb survives to a live cache entry.** Splitting the raws at the NS
    record (`pre ++ [nsRaw] ++ post`): the prefix absorbs, the NS is stored (`storeChecked_self_live`, given
    `ttl ≠ 0` + no higher-cred incumbent), and the suffix preserves it (`mem_cacheRRs_preserve`, given no
    `post` raw conflicts it). So the referral absorb leaves a live NS entry at the cut — combined with
    `lookup_nonempty_of_mem`, the absorb-side of the cache round-trip (`lookup zone nsType inClass ≠ ∅`). -/
theorem mem_cacheRRs_live_of_split (c : Cache.DnsCache) (pre post : Array ByteArray) (nsRaw : ByteArray)
    (nsRR : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsRR)
    (hnz : (nsRR.ttl == 0) = false)
    (hbetter : ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c pre cred now).records.any
      fun e => DomainName.nameEqCI e.rr.name nsRR.name && e.rr.type == nsRR.type && e.rr.class == nsRR.class
        && (e.expiry > now || e.expiry == now + nsRR.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false)
    (hfresh : Cache.CacheEntry.fresh ⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred⟩ now = true)
    (hpost : ∀ b ∈ post, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (DomainName.nameEqCI nsRR.name rr.name && nsRR.type == rr.type && nsRR.class == rr.class
        && (now + nsRR.ttl.toNat.toUInt32 != now + rr.ttl.toNat.toUInt32 || nsRR.rdata == rr.rdata)) = false) :
    ∃ e ∈ (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (pre ++ #[nsRaw] ++ post) cred now).records,
      Cache.liveEntry e nsRR.name nsRR.type nsRR.class now = true := by
  refine ⟨⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred⟩, ?_, ?_⟩
  · rw [Array.append_assoc, cacheRRs_append c pre (#[nsRaw] ++ post),
       cacheRRs_append (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
         c pre cred now) #[nsRaw] post]
    refine VeriDNS.Proof.Cache.mem_cacheRRs_preserve _ post cred now
      ⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred⟩ ?_ ?_
    · rw [cacheRRs_singleton _ nsRaw cred now nsRR hp, Cache.DnsCache.storeChecked]
      simp only [hnz, Bool.false_eq_true, if_false, hbetter]
      exact Array.mem_push.mpr (Or.inr rfl)
    · intro b hb rr hpr; exact hpost b hb rr hpr
  · simp only [Cache.liveEntry, VeriDNS.Proof.NameTree.nameEqCI_refl, beq_self_eq_true, hfresh,
      Bool.and_self]

/-- **Provenance for `cacheRRs`**: every stored record was already in the cache or is one of the
    `raws` actually parsed and cached — `cacheRRs` invents nothing. Proven directly over the real
    `Array.foldl` (`Array.foldl_induction`), so the cache-write matcher is the canonical one. -/
theorem mem_cacheRRs_records (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32)
    (c : Cache.DnsCache) {e : Cache.CacheEntry}
    (h : e ∈ (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now).records) :
    e ∈ c.records ∨ ∃ b ∈ raws.toList,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some e.rr := by
  unfold Resolver.cacheRRs at h
  refine Array.foldl_induction
    (motive := fun _ (acc : Cache.DnsCache) => e ∈ acc.records →
      e ∈ c.records ∨ ∃ b ∈ raws.toList,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some e.rr)
    (fun he => Or.inl he) ?_ h
  intro i acc ih hacc
  cases hpi : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raws[i] with
  | none => simp only [hpi] at hacc; exact ih hacc
  | some rr =>
    simp only [hpi] at hacc
    rcases mem_storeChecked_records (rr := rr) hacc with h' | h'
    · exact ih h'
    · exact Or.inr ⟨raws[i], Array.mem_def.mp (Array.getElem_mem i.isLt), by rw [hpi, h']⟩

/-- **Every absorbed record is incumbent or in-bailiwick of the cut.** Absorbing `bailiwickRaws cut raws`
    leaves each cache entry either already present or with owner at-or-below `cut` (`isAncestorB cut owner`) —
    the structural backbone of "the referral absorb writes NS only at the cut, none at off-cut names": with
    the driver's cache-miss invariant it gives `lookup … nsType = ∅` above/off the cut (the `hempty` half of
    the `walkNs_ascend` path). Composes `mem_cacheRRs_records` (provenance) with `bailiwickRaws_owner_inBailiwick`. -/
theorem cacheRRs_bailiwick_owner (c : Cache.DnsCache) (cut : ByteArray) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) {e : Cache.CacheEntry}
    (h : e ∈ (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut raws) cred now).records) :
    e ∈ c.records ∨ Resolver.isAncestorB cut e.rr.name = true := by
  rcases mem_cacheRRs_records (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut raws)
      cred now c h with h' | ⟨b, hb, hpr⟩
  · exact Or.inl h'
  · exact Or.inr (Resolver.bailiwickRaws_owner_inBailiwick cut raws hb hpr)

/-- **A (parseable) name is in its own bailiwick.** `isAncestorB a a = true` whenever `a` decodes to labels —
    so the cut's own NS RRset (owner `= cut`) passes `bailiwickRaws cut` and is absorbed. The reflexivity the
    referral cache round-trip needs to know the delegation NS lands in the cache (feeds `lookup_nonempty`). -/
theorem isAncestorB_self {a : ByteArray} {labels : Array ByteArray}
    (h : DomainName.wireFormatToLabels a = .ok labels) : Resolver.isAncestorB a a = true := by
  unfold Resolver.isAncestorB
  rw [h]
  simp only [Nat.le_refl, decide_true, Nat.sub_self, List.drop_zero, Bool.and_self, decide_eq_true_eq]

/-- **`parentDomainWire` exposes the parent name structurally.** When `parentDomainWire wire = some parent`,
    `wire` decodes to a non-empty label list and `parent` is its tail re-encoded — the one-step link of the
    `walkNs` ascent's parent-chain (`walkNs_ascend`'s `List.Chain` hypothesis). -/
theorem parentDomainWire_some {wire parent : ByteArray}
    (h : DomainName.parentDomainWire wire = some parent) :
    ∃ labels, DomainName.wireFormatToLabels wire = .ok labels ∧ labels.size ≠ 0
      ∧ DomainName.labelsToWireFormat (labels.extract 1) = parent := by
  unfold DomainName.parentDomainWire at h
  split at h
  · exact absurd h (by simp)
  · next labels heq =>
    split at h
    · exact absurd h (by simp)
    · next hne => exact ⟨labels, heq, by simpa using hne, by simpa using h⟩

/-- **Dropping the first label preserves `ValidLabels`.** Each label of `labels.extract 1` is a label of
    `labels` (one index up), so the per-label `1 ≤ size ≤ 63` bound carries over. Lets `wireFormat_roundtrip`
    apply to the `parentDomainWire` result (`parentDomainWire_some`) — the parent decodes back to its labels,
    pinning the `walkNs` ascent's per-step label/match-count decrease. -/
theorem validLabels_extract {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    VeriDNS.Proof.DomainName.ValidLabels (labels.extract 1) := by
  intro i hi
  have hbound : 1 + i < labels.size := by
    have := hi; rw [Array.size_extract] at this; omega
  rw [Array.getElem_extract]
  exact hv (1 + i) hbound

/-- **Forward parent step in wire form.** For a valid, non-root label array, `parentDomainWire` of its wire
    encoding is the wire encoding of the array with its first label dropped. The `walkNs` ascent's per-step
    decrease: combined with `validLabels_extract` it iterates `parentDomainWire` from `sname` up to the
    delegation `zone` (a suffix), supplying `walkNs_ascend`'s `List.Chain` of `parentDomainWire` links. -/
theorem parentDomainWire_labelsToWireFormat {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) (hne : labels.size ≠ 0) :
    DomainName.parentDomainWire (DomainName.labelsToWireFormat labels)
      = some (DomainName.labelsToWireFormat (labels.extract 1)) := by
  unfold DomainName.parentDomainWire
  rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip labels hv]
  simp only [beq_iff_eq, hne, if_false, reduceIte]

/-- `ValidLabels` is closed under dropping any prefix (generalizes `validLabels_extract` to arbitrary start). -/
theorem validLabels_extract_start {labels : Array ByteArray} {s : Nat}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    VeriDNS.Proof.DomainName.ValidLabels (labels.extract s) := by
  intro i hi
  have hbound : s + i < labels.size := by
    have := hi; rw [Array.size_extract] at this; omega
  rw [Array.getElem_extract]
  exact hv (s + i) hbound

/-- Dropping `d` then 1 label = dropping `d+1` — the `walkNs` ascent's per-step suffix composition. -/
theorem extract_extract_one {labels : Array ByteArray} {d : Nat} :
    (labels.extract d).extract 1 = labels.extract (d + 1) := by
  rw [Array.extract_extract]
  congr 1
  simp only [Array.size_extract]
  omega

/-- **`parentDomainWire` ↔ model `Name.tail` under `αName`** (the per-node chain-alignment step of the full-walk
    keystone). A wire-form parent link (`parentDomainWire a = some b`) abstracts to a model tail step:
    `αName a = some na` with `na ≠ []` and `αName b = some na.tail`. So the impl `walkNs` ascent's
    `parentDomainWire`-chain maps, label-by-label, onto the model `referralSlist` ascent's `tail`-chain. Needs
    `ValidLabels` of the decoded labels (threaded from cache canonicity); `αName` is `wireFormatToLabels.toList`,
    and dropping the first label commutes with `αName` via `wireFormat_roundtrip` + `validLabels_extract`. -/
theorem parentDomainWire_αName {a b : ByteArray} {labels : Array ByteArray}
    (hwl : DomainName.wireFormatToLabels a = .ok labels)
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels)
    (h : DomainName.parentDomainWire a = some b) :
    labels.toList ≠ [] ∧ αName a = some labels.toList ∧ αName b = some labels.toList.tail := by
  have hαa : αName a = some labels.toList := by unfold αName; rw [hwl]
  obtain ⟨labels', hwl', hne, hpar⟩ := parentDomainWire_some h
  have hll : labels = labels' := Except.ok.inj (hwl.symm.trans hwl')
  rw [← hll] at hpar hne
  refine ⟨?_, hαa, ?_⟩
  · intro hc
    rw [Array.toList_eq_nil_iff] at hc
    rw [hc] at hne
    exact hne rfl
  · have hαb : αName b = some (labels.extract 1).toList := by
      rw [← hpar]; unfold αName
      rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip (labels.extract 1) (validLabels_extract hv)]
    rw [hαb]
    congr 1
    rw [Array.toList_extract]
    simp [List.drop_one]
    apply List.take_of_length_le
    simp [List.length_tail]

/-- Dropping the first array element commutes with `toList` as `List.tail`. -/
theorem array_extract_one_toList {α : Type} (a : Array α) : (a.extract 1).toList = a.toList.tail := by
  rw [Array.toList_extract]
  simp [List.drop_one]
  apply List.take_of_length_le
  simp [List.length_tail]

/-- **The impl `parentDomainWire`-chain abstracts to the model `tail`-chain** (the chain-mapping glue for the
    full-walk keystone). Given the start's decoded valid labels, an impl `List.Chain` of `parentDomainWire`
    links maps — label-by-label, via `parentDomainWire_αName` — onto a model `List.Chain` of `tail` links over
    the `αName`-images. This is what feeds `referralSlist_ascend` (whose chain is the model `tail`-chain) from
    the impl `walkNs_ascend`'s `parentDomainWire`-chain. -/
theorem parentDomainWire_chain_αName :
    ∀ (L : List ByteArray) (start : ByteArray) (lab : Array ByteArray),
      DomainName.wireFormatToLabels start = .ok lab →
      VeriDNS.Proof.DomainName.ValidLabels lab →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start L →
      List.Chain (fun (a b : VeriDNS.Spec.Net.Name) => a ≠ [] ∧ a.tail = b)
        lab.toList (L.map (fun w => (αName w).getD [])) := by
  intro L
  induction L with
  | nil => intro start lab _ _ _; exact List.Chain.nil
  | cons b rest ih =>
    intro start lab hwl hv hchain
    obtain ⟨hlink, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨lab', hwl', hne', hpar⟩ := parentDomainWire_some hlink
    have hll : lab = lab' := Except.ok.inj (hwl.symm.trans hwl')
    have hwlb : DomainName.wireFormatToLabels b = .ok (lab.extract 1) := by
      rw [← hpar, hll]
      exact VeriDNS.Proof.DomainName.wireFormat_roundtrip (lab'.extract 1) (validLabels_extract (hll ▸ hv))
    have hαb' : αName b = some (lab.extract 1).toList := by unfold αName; rw [hwlb]
    have hne : lab.toList ≠ [] := by
      intro hc; rw [Array.toList_eq_nil_iff] at hc
      rw [← hll] at hne'; rw [hc] at hne'; exact hne' rfl
    rw [List.map_cons]
    refine List.Chain.cons ⟨hne, ?_⟩ ?_
    · show lab.toList.tail = (αName b).getD []
      rw [hαb']
      exact (array_extract_one_toList lab).symm
    · show List.Chain _ ((αName b).getD []) _
      rw [show (αName b).getD [] = (lab.extract 1).toList from by simp [hαb']]
      exact ih b (lab.extract 1) hwlb (validLabels_extract hv) hchain'

/-- **Every node in the `parentDomainWire`-walk is a canonical wire name.** Given the start is canonical
    (decoded valid labels, `start = labelsToWireFormatGo`) and an ascending `parentDomainWire`-chain, each node —
    `start` and every ancestor — abstracts (`αName`) and is the literal `labelsToWireFormatGo` of its abstraction
    with ≤63-byte labels. (Ancestors ARE canonical by construction: `parentDomainWire` outputs
    `labelsToWireFormat = labelsToWireFormatGo ∘ toList` of the label-suffix.) This discharges the keystone's
    `hcanonNode`/cut-canonicity walk-node hypotheses from `sname`'s canonicity (the query name is canonical wire). -/
theorem chain_canonical :
    ∀ (L : List ByteArray) (start : ByteArray) (lab : Array ByteArray),
      DomainName.wireFormatToLabels start = .ok lab → VeriDNS.Proof.DomainName.ValidLabels lab →
      start = DomainName.labelsToWireFormatGo lab.toList →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start L →
      ∀ m ∈ start :: L, ∃ na, αName m = some na ∧ m = DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63) := by
  intro L
  induction L with
  | nil =>
    intro start lab hwl hv hcanon _ m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    refine ⟨lab.toList, by unfold αName; rw [hwl], hcanon, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Array.getElem_toList]
    exact (hv i (by rwa [Array.length_toList] at hi)).2
  | cons b rest ih =>
    intro start lab hwl hv hcanon hchain m hm
    obtain ⟨hlink, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨lab', hwl', hne, hpar⟩ := parentDomainWire_some hlink
    have hll : lab = lab' := Except.ok.inj (hwl.symm.trans hwl')
    have hwlb : DomainName.wireFormatToLabels b = .ok (lab.extract 1) := by
      rw [← hpar, hll]
      exact VeriDNS.Proof.DomainName.wireFormat_roundtrip (lab'.extract 1) (validLabels_extract (hll ▸ hv))
    have hbcanon : b = DomainName.labelsToWireFormatGo (lab.extract 1).toList := by
      rw [← hpar, hll]; rfl
    rcases List.mem_cons.mp hm with rfl | hm'
    · refine ⟨lab.toList, by unfold αName; rw [hwl], hcanon, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [Array.getElem_toList]
      exact (hv i (by rwa [Array.length_toList] at hi)).2
    · exact ih b (lab.extract 1) hwlb (validLabels_extract hv) hbcanon hchain' m hm'

/-- **A `parentDomainWire`-chain is no longer than the start's label count.** Each `parentDomainWire` step drops
    exactly one label, so a chain of `L.length` links from a name with `lab.size` labels reaches a `≥0`-label
    name — hence `L.length ≤ lab.size`. With the ≤127-label DNS-name bound this discharges the keystone's fuel
    hypotheses (`inter.length + 2 ≤ 128` and `≤ q.qname.length + 1`): the walk depth never exceeds the name. -/
theorem parentDomainWire_chain_length :
    ∀ (L : List ByteArray) (start : ByteArray) (lab : Array ByteArray),
      DomainName.wireFormatToLabels start = .ok lab → VeriDNS.Proof.DomainName.ValidLabels lab →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start L →
      L.length ≤ lab.size := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _; simp
  | cons b rest ih =>
    intro start lab hwl hv hchain
    obtain ⟨hlink, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨lab', hwl', hne, hpar⟩ := parentDomainWire_some hlink
    have hll : lab = lab' := Except.ok.inj (hwl.symm.trans hwl')
    have hwlb : DomainName.wireFormatToLabels b = .ok (lab.extract 1) := by
      rw [← hpar, hll]
      exact VeriDNS.Proof.DomainName.wireFormat_roundtrip (lab'.extract 1) (validLabels_extract (hll ▸ hv))
    have hib := ih b (lab.extract 1) hwlb (validLabels_extract hv) hchain'
    have hsz : (lab.extract 1).size = lab.size - 1 := by rw [Array.size_extract]; omega
    have hne' : lab.size ≠ 0 := by rw [hll]; exact hne
    rw [hsz] at hib
    simp only [List.length_cons]
    omega

/-- **The `parentDomainWire` ascent chain to any suffix.** From the wire form of `labels` dropped by `s`,
    the `n` successive `parentDomainWire` links reach the wire forms of the deeper suffixes
    `labels.extract (s+1) … labels.extract (s+n)` — a `List.Chain` of parent links. Built front-first via
    `List.Chain.cons` (each link is `parentDomainWire_labelsToWireFormat` + `extract_extract_one`, validity
    via `validLabels_extract_start`). Instantiated at `s = 0` it supplies `walkNs_ascend`'s `List.Chain`
    hypothesis from `sname` up to the delegation `zone` — the slist-connector's name-ascent obligation. -/
theorem parentChain_aux {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    ∀ (n s : Nat), s + n ≤ labels.size →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b)
        (DomainName.labelsToWireFormat (labels.extract s))
        ((List.range' (s + 1) n).map (fun i => DomainName.labelsToWireFormat (labels.extract i))) := by
  intro n
  induction n with
  | zero => intro s _; exact List.Chain.nil
  | succ n ih =>
    intro s hs
    have hne : (labels.extract s).size ≠ 0 := by
      simp only [Array.size_extract, Nat.min_self]; omega
    have hstep : DomainName.parentDomainWire (DomainName.labelsToWireFormat (labels.extract s))
        = some (DomainName.labelsToWireFormat (labels.extract (s + 1))) := by
      rw [parentDomainWire_labelsToWireFormat (validLabels_extract_start hv) hne, extract_extract_one]
    rw [List.range'_succ, List.map_cons]
    exact List.Chain.cons hstep (ih (s + 1) (by omega))

/-- `parentChain_aux` instantiated at the root (`s = 0`, `labels.extract 0 = labels`): the parent-link chain
    from `sname`'s wire form up through its `d` proper ancestor suffixes. The form `walkNs_ascend` consumes
    once the driver picks `zone = labels.extract d` (the delegation cut) and `inter = …extract 1 … d-1`. -/
theorem parentChain_from_root {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) (d : Nat) (hdle : d ≤ labels.size) :
    List.Chain (fun a b => DomainName.parentDomainWire a = some b)
      (DomainName.labelsToWireFormat labels)
      ((List.range' 1 d).map (fun i => DomainName.labelsToWireFormat (labels.extract i))) := by
  have h := parentChain_aux hv d 0 (by omega)
  simpa using h

/-- The name-ascent in `walkNs_ascend`'s exact `inter ++ [zone]` shape: `zone = labels.extract d` (the
    delegation cut) and `inter` the proper intermediate suffixes. Splits `parentChain_from_root`'s
    `range' 1 d` at its last element via `List.range'_concat`. Directly dischargeable as `walkNs_ascend`'s
    `List.Chain` hypothesis. -/
theorem parentChain_inter_zone {labels : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) (d : Nat) (hd : 0 < d) (hdle : d ≤ labels.size) :
    List.Chain (fun a b => DomainName.parentDomainWire a = some b)
      (DomainName.labelsToWireFormat labels)
      ((List.range' 1 (d - 1)).map (fun i => DomainName.labelsToWireFormat (labels.extract i))
        ++ [DomainName.labelsToWireFormat (labels.extract d)]) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h := parentChain_from_root hv (k + 1) hdle
  rw [List.range'_concat, List.map_append, List.map_cons, List.map_nil] at h
  have e2 : 1 + 1 * k = k + 1 := by omega
  rw [e2] at h
  simpa using h

/-! ### Phase 3 (capstone plan) — the impl referral write leaves negatives untouched

  The impl referral cache write is `cacheRRs` (a `foldl` of `storeChecked` over the bailiwick raws); it
  only ever mutates `records`, never `negatives`. With the model's `absorb_neg` (`absorb` leaves `neg`),
  this discharges the `negHit`/`negHitNx` components of the Phase-3 bridge
  `MatchMaxEquiv (αCache (impl write-fold)) ((αCache c).absorb …)` — leaving only the `topServed`
  (positive, per-key-max) component, the genuine write-path correspondence. -/

theorem store_negatives (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : VeriDNS.Spec.Trustworthiness) : (Cache.DnsCache.store c rr now cred).negatives = c.negatives :=
  rfl

theorem storeChecked_negatives (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    (c.storeChecked rr cred now).negatives = c.negatives := by
  rcases storeChecked_cases c rr cred now with h | h
  · rw [h]
  · rw [h, store_negatives]

theorem cacheRRs_negatives (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (c : Cache.DnsCache) :
    (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now).negatives
      = c.negatives := by
  unfold Resolver.cacheRRs
  refine Array.foldl_induction (motive := fun _ (acc : Cache.DnsCache) => acc.negatives = c.negatives)
    rfl ?_
  intro i acc hacc
  split
  · next rr' hrr' =>
    rw [show VeriDNS.Spec.TrustworthinessSpec.acceptRrset acc rr' cred now = acc.storeChecked rr' cred now
        from rfl, storeChecked_negatives]
    exact hacc
  · exact hacc

/-- **No dedup when fresh: `store` is a clean push.** If no record of `c` shares `rr`'s key, the dedup
    filter in `DnsCache.store` removes nothing, so the write is exactly `c.records.push entry`. This is the
    crux that makes the Phase-3 `topServed` bridge tractable: a referral's records descend below the
    current cut, hence aren't already cached, so the impl write is a pure push — differing from the model
    `absorb` (a prepend) only in *order*, which `topServed`/`Perm` (via `topOf_perm`) absorbs. -/
theorem store_fresh_records (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : VeriDNS.Spec.Trustworthiness)
    (h : ∀ e ∈ c.records, (VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class) = false) :
    (Cache.DnsCache.store c rr now cred).records
      = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := by
  have hf : Array.filter (fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != (now + rr.ttl.toNat.toUInt32) || e.rr.rdata == rr.rdata))) c.records = c.records := by
    apply Array.filter_eq_self.mpr
    intro e he
    rw [h e he]; simp
  show (Array.filter _ c.records).push _ = _
  rw [hf]

/-- **`storeChecked` is a clean push under freshness.** When `rr` is cacheable (`ttl ≠ 0`) and no record
    of `c` shares its key, the `betterExists` gate is `false` (it requires a same-key record) and `store`
    removes nothing, so `storeChecked` appends. Composes `store_fresh_records`; the single-step lemma the
    `cacheRRs` fold-push (Phase-3 `hrec`) iterates. -/
theorem storeChecked_fresh_push (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (httl : (rr.ttl == 0) = false)
    (h : ∀ e ∈ c.records, (VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class) = false) :
    (c.storeChecked rr cred now).records = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := by
  have hbetter : (c.records.any fun e =>
      VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false := by
    by_contra hc
    rw [Bool.not_eq_false, Array.any_eq_true] at hc
    obtain ⟨i, hi, hpe⟩ := hc
    rw [h c.records[i] (Array.getElem_mem hi)] at hpe
    simp at hpe
  simp only [Cache.DnsCache.storeChecked, httl, hbetter, Bool.false_eq_true, if_false]
  exact store_fresh_records c rr now cred h

/-- **`storeChecked` is a push, factored through its two gates (the RRset-capable per-step brick).** Given the
    record is cacheable (`httl : rr.ttl ≠ 0`), no strictly-more-credible same-key record blocks it
    (`hbetter`: the §5.4.1 max-cred gate misses — automatic for an RRset whose siblings share `rr`'s cred),
    and `store` itself is a pure push (`hstore`, from `store_push_records`/`store_fresh_records` — RRset
    siblings with distinct rdata are kept), `storeChecked` pushes `⟨rr, now+ttl, false, cred⟩`. Unlike
    `storeChecked_fresh_push` (no-same-key, excludes RRsets), this consumes the *filter-keeps-all* `hstore`,
    so it covers the referral NS RRset — the per-raw step of the concrete `cacheRRs` fold. -/
theorem storeChecked_push_of (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (httl : (rr.ttl == 0) = false)
    (hbetter : (c.records.any fun e =>
        VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type
          && e.rr.class == rr.class
          && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
          && e.credibility.toCode < cred.toCode) = false)
    (hstore : (Cache.DnsCache.store c rr now cred).records
        = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩) :
    (c.storeChecked rr cred now).records
      = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := by
  unfold Cache.DnsCache.storeChecked
  simp only [httl, hbetter, Bool.false_eq_true, if_false]
  exact hstore

/-- **`store` is a push whenever its dedup filter keeps every existing record** — the general form of
    `store_fresh_records` that also covers **RRsets** (records sharing `rr`'s key but with distinct rdata
    and the same expiry are *kept* by the filter, so adding another RRset member is still a pure push).
    This is the form the `cacheRRs` fold-push (Phase-3 `hrec`) needs, since referral NS records are an
    RRset (same owner+type, distinct targets). -/
theorem store_push_records (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : VeriDNS.Spec.Trustworthiness)
    (h : ∀ e ∈ c.records, (VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != (now + rr.ttl.toNat.toUInt32) || e.rr.rdata == rr.rdata)) = false) :
    (Cache.DnsCache.store c rr now cred).records
      = c.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := by
  have hf : Array.filter (fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
        && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry != (now + rr.ttl.toNat.toUInt32) || e.rr.rdata == rr.rdata))) c.records = c.records := by
    apply Array.filter_eq_self.mpr
    intro e he
    simp only [h e he, Bool.not_false]
  show (Array.filter _ c.records).push _ = _
  rw [hf]

/-- **The `cacheRRs` fold-push (Phase-3 `hrec` skeleton).** If every parsed raw's `acceptRrset` step is a
    pure append (the per-step hypothesis `h`, dischargeable by `storeChecked_fresh_push`/`store_push_records`
    under the freshness invariant), then the whole referral write appends to `c.records`:
    `(cacheRRs c raws cred now).records = c.records ++ extra`. With `αCache_pos_of_records_append`,
    `matching_αCache_records_append`, and `topServed_bridge_clause` this is exactly the `hrec` the
    `topServed` clause of the Phase-3 bridge consumes. -/
theorem cacheRRs_records_append (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (c : Cache.DnsCache)
    (h : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b ∈ raws.toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        ∃ pre, (VeriDNS.Spec.TrustworthinessSpec.acceptRrset acc rr cred now).records
          = acc.records ++ pre) :
    ∃ extra, (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now).records = c.records ++ extra := by
  unfold Resolver.cacheRRs
  refine Array.foldl_induction
    (motive := fun _ (acc : Cache.DnsCache) => ∃ pre, acc.records = c.records ++ pre)
    ⟨#[], by simp⟩ ?_
  intro i acc ⟨pre, hpre⟩
  split
  · next rr hrr =>
    obtain ⟨pre0, hp0⟩ := h acc raws[i] rr (by simp) hrr
    exact ⟨pre ++ pre0, hp0.trans (by rw [hpre, Array.append_assoc])⟩
  · next => exact ⟨pre, hpre⟩

/-- The per-raw cache contribution of a `storeChecked` write: the singleton pushed `CacheEntry` for a
    cacheable (`ttl≠0`) parse, `[]` for parse-failure or `ttl=0`. **Named** (not an anonymous `match`) so the
    write-path lemmas compose without the `match`-auxiliary defeq barrier — two syntactically-identical
    anonymous `match`es compile to *distinct* aux constants that `rw`/`simp`/`exact` won't bridge, but one
    named `def` is a single constant everywhere. -/
def pushOf (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (b : ByteArray) : List Cache.CacheEntry :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | some rr => if rr.ttl == 0 then [] else [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩]
  | none => []

theorem pushOf_none {b : ByteArray} (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = none) :
    pushOf cred now b = [] := by unfold pushOf; rw [h]

theorem pushOf_zero {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord} (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (h0 : (rr.ttl == 0) = true) : pushOf cred now b = [] := by
  unfold pushOf; rw [h]; simp only [h0, if_true]

theorem pushOf_pos {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord} (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (h : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (h0 : (rr.ttl == 0) = false) :
    pushOf cred now b = [⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩] := by
  unfold pushOf; rw [h]; simp only [h0, Bool.false_eq_true, if_false]

/-- **The CONCRETE `cacheRRs` fold-push.** Strengthening `cacheRRs_records_append` from an existential
    `∃ extra` to an *explicit* `extra = l.flatMap (pushOf cred now)`: given the per-raw push hypothesis `h`
    (each parsed `ttl≠0` record is a clean push — dischargeable by `storeChecked_push_of` under the freshness +
    same-cred invariant), the fold's records are `c.records ++ l.flatMap (pushOf cred now)`. This makes `extra`
    computable, so `extra.filterMap αCacheRR` (via `αCacheRR_push`) becomes the concrete list of model records
    the bridge's `extra ~ N` Perm compares against the model `absorb`'s inserted `N`. -/
theorem foldl_storeChecked_concrete (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (l : List ByteArray) (c : Cache.DnsCache)
    (h : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b ∈ l →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (rr.ttl == 0) = false →
        (acc.storeChecked rr cred now).records
          = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩) :
    (l.foldl (fun acc b => match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
        | some rr => acc.storeChecked rr cred now | none => acc) c).records.toList
      = c.records.toList ++ l.flatMap (pushOf cred now) := by
  induction l generalizing c with
  | nil => simp
  | cons b t ih =>
    have ht : ∀ (acc : Cache.DnsCache) (b' : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b' ∈ t →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some rr →
        (rr.ttl == 0) = false →
        (acc.storeChecked rr cred now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ :=
      fun acc b' rr hb' => h acc b' rr (List.mem_cons_of_mem _ hb')
    simp only [List.foldl_cons, List.flatMap_cons]
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [pushOf_none cred now hpr, List.nil_append]; exact ih c ht
    | some rr =>
      by_cases htt : (rr.ttl == 0) = true
      · rw [pushOf_zero cred now hpr htt, List.nil_append]
        have hsc : (c.storeChecked rr cred now).records.toList = c.records.toList := by
          unfold Cache.DnsCache.storeChecked; simp only [htt, if_true]
        simp only [hpr]
        rw [ih (c.storeChecked rr cred now) ht, hsc]
      · have htf : (rr.ttl == 0) = false := by simpa using htt
        rw [pushOf_pos cred now hpr htf]
        simp only [hpr]
        rw [ih (c.storeChecked rr cred now) ht, h c b rr (by simp) hpr htf, Array.toList_push,
          List.append_assoc]

theorem αName_labelsToWireFormat (labels : Array ByteArray)
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels) :
    αName (DomainName.labelsToWireFormat labels) = some labels.toList := by
  unfold αName
  rw [VeriDNS.Proof.DomainName.wireFormat_roundtrip labels hv]

theorem αType_toCode (rt : RRType) : αType (BitVec.ofNat 16 rt.toCode) = some rt := by
  cases rt <;> rfl

theorem αClass_toCode (rc : RRClass) : αClass (BitVec.ofNat 16 rc.toCode) = some rc := by
  cases rc <;> rfl

theorem αType_some_toCode {t : BitVec 16} {rt : RRType} (h : αType t = some rt) :
    t.toNat = rt.toCode := by
  unfold αType at h
  split at h <;> simp_all <;> subst h <;> rfl

theorem αType_injective {u v : BitVec 16} {rt : RRType}
    (hu : αType u = some rt) (hv : αType v = some rt) : u = v :=
  BitVec.eq_of_toNat_eq ((αType_some_toCode hu).trans (αType_some_toCode hv).symm)

/-- `αClass` is injective where defined: two wire classes abstracting to the same model `RRClass` are
    equal. Used (with `αType_injective` and `nameEqCI_of_αName_canonical`) for the reverse predicate
    correspondence `matching ⟹ answerableEntry` of `hhit` completeness. -/
theorem αClass_inj {u v : BitVec 16} {c : RRClass}
    (hu : αClass u = some c) (hv : αClass v = some c) : u = v := by
  apply BitVec.eq_of_toNat_eq
  cases c <;>
    (unfold αClass at hu hv
     split at hu <;> simp_all <;> split at hv <;> simp_all)

/-- **Image-restricted `beq→eq` for `RRType`.** `RRType` (62 constructors) is `deriving BEq` but
    *not* `LawfulBEq`, so the generic `eq_of_beq` is unavailable. We don't need it in full: on the
    *image* of `αType` (the 16 modelled types) the derived `==` does coincide with equality. Two wire
    types abstracting to `RRType`s that are `==` are equal. The companion of `αType_injective` for the
    reverse predicate correspondence `matching ⟹ answerableEntry` (a model `covers` carries a derived
    `t == a.rr.rtype`, which this turns into a genuine `t = a.rr.rtype`). Proven by exhaustive case
    split over the 16×16 image grid, each off-diagonal cell discharged by `decide` on the concrete
    `==`. -/
theorem eq_of_αType_beq {u v : BitVec 16} {x y : RRType}
    (hx : αType u = some x) (hy : αType v = some y) (h : (x == y) = true) : x = y := by
  unfold αType at hx hy
  split at hx <;> split at hy <;> simp_all <;> (subst hx; subst hy; exact absurd h (by decide))

/-- **Image-restricted `beq→eq` for `RRClass`** (the class analogue of `eq_of_αType_beq`). On the
    image of `αClass` the derived `==` coincides with equality; with `αClass_inj` this carries the
    model-side class match `a.rr.cls == q.qclass` back to the impl-side `e.rr.class == qc`. -/
theorem eq_of_αClass_beq {u v : BitVec 16} {x y : RRClass}
    (hx : αClass u = some x) (hy : αClass v = some y) (h : (x == y) = true) : x = y := by
  unfold αClass at hx hy
  split at hx <;> split at hy <;> simp_all <;> (subst hx; subst hy; exact absurd h (by decide))

def αCred : Trustworthiness → VeriDNS.Spec.Net.Cred
  | .primaryZone => .authoritative
  | .zoneTransfer => .authoritative
  | .authoritativeSection => .authoritative
  | .authoritySection => .authority
  | .additionalAuthoritative => .additional
  | _ => .glue

/-- The abstraction respects the RFC 2181 §5.4.1 usability gate: an impl credibility is usable as an
    answer (`toCode < untrustworthyFloor`) iff its model abstraction is `Cred.usable`. The impl's
    `answerableEntry` floor and the model's `Cache.served` `usable` filter are the *same* gate. -/
theorem αCred_usable (t : Trustworthiness) :
    (αCred t).usable = decide (t.toCode < VeriDNS.Impl.Cache.untrustworthyFloor) := by
  cases t <;> rfl

/-- **Credibility order correspondence (the keystone for `maxCredForKey ↔ Cache.served`).** On the
    resolver's actually-stored credibility set — `authoritativeSection` (answers, aa),
    `authoritySection` (authority, aa), `sectionNonauthoritative` (answers, non-aa),
    `additionalAuthoritative` (authority non-aa / additional / glue), i.e. the images of
    `credAnswer`/`credAuthority`/`credAdditional` — `αCred` is an order-*reversing* bijection onto
    `{authoritative, authority, glue, additional}`: the more-credible impl entry (lower `toCode`)
    abstracts to the higher model `Cred.rank`. So the impl's `maxCredForKey` test
    (`e.toCode ≤ all same-key e2.toCode`) coincides with the model's `served` test
    (`e2.rank ≤ e.rank` over the matching set) — closing the credibility-granularity gap on the set
    of credibilities the resolver ever caches. -/
theorem αCred_order_used (t1 t2 : Trustworthiness)
    (h1 : t1 = .authoritativeSection ∨ t1 = .authoritySection ∨
          t1 = .sectionNonauthoritative ∨ t1 = .additionalAuthoritative)
    (h2 : t2 = .authoritativeSection ∨ t2 = .authoritySection ∨
          t2 = .sectionNonauthoritative ∨ t2 = .additionalAuthoritative) :
    (t1.toCode ≤ t2.toCode)
      ↔ (VeriDNS.Spec.Net.Cred.rank (αCred t2) ≤ VeriDNS.Spec.Net.Cred.rank (αCred t1)) := by
  rcases h1 with rfl|rfl|rfl|rfl <;> rcases h2 with rfl|rfl|rfl|rfl <;>
    simp [αCred, VeriDNS.Spec.Net.Cred.rank, VeriDNS.Spec.Trustworthiness.toCode]

/-- The resolver only ever stores credibilities in the "used" set (`credAnswer`/`credAuthority`/
    `credAdditional`). Recording this as the cache invariant `αCred_order_used` is keyed on. -/
theorem cred_used_credAnswer (aa : Bool) :
    Resolver.credAnswer aa = .authoritativeSection ∨ Resolver.credAnswer aa = .authoritySection ∨
    Resolver.credAnswer aa = .sectionNonauthoritative ∨
    Resolver.credAnswer aa = .additionalAuthoritative := by
  cases aa
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl

theorem cred_used_credAuthority (aa : Bool) :
    Resolver.credAuthority aa = .authoritativeSection ∨
    Resolver.credAuthority aa = .authoritySection ∨
    Resolver.credAuthority aa = .sectionNonauthoritative ∨
    Resolver.credAuthority aa = .additionalAuthoritative := by
  cases aa
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)

theorem cred_used_credAdditional :
    Resolver.credAdditional = .authoritativeSection ∨
    Resolver.credAdditional = .authoritySection ∨
    Resolver.credAdditional = .sectionNonauthoritative ∨
    Resolver.credAdditional = .additionalAuthoritative :=
  Or.inr (Or.inr (Or.inr rfl))

/-- **The 4-tier model `Cred` ranking is RFC-faithful for the resolver (closes the credibility-
    granularity gap).** RFC 2181 §5.4.1 defines a 7-level trustworthiness order (impl
    `Trustworthiness.toCode`, 0–6); the model `Cred` is 4-tier and `αCred` collapses the top 3 levels
    to `authoritative` and two to `glue`. That collapse is *lossless for a recursive resolver*: the
    resolver only ever **assigns** credibilities via `credAnswer`/`credAuthority`/`credAdditional`
    (Resolver.lean), which yield exactly the 4-element set
    `{authoritativeSection, authoritySection, sectionNonauthoritative, additionalAuthoritative}` — the
    3 finer levels (`primaryZone`/`zoneTransfer`/`gluePrimary`) are authoritative-server-only and never
    produced. And on that 4-element set `αCred` is an order-reversing bijection onto `Cred.rank`
    (`αCred_order_used`). Hence for **any** two credibilities the resolver can assign, the model's
    coarse rank order coincides with the impl's full `toCode` order — the model is *not* weaker than the
    RFC for the resolver's behaviour. (Modelling the 3 authoritative-only levels would only add
    precision the resolver never exercises.) -/
theorem cred_ranking_faithful_for_resolver
    (aa1 aa2 : Bool) (c1 c2 : Trustworthiness)
    (h1 : c1 = Resolver.credAnswer aa1 ∨ c1 = Resolver.credAuthority aa1 ∨ c1 = Resolver.credAdditional)
    (h2 : c2 = Resolver.credAnswer aa2 ∨ c2 = Resolver.credAuthority aa2 ∨ c2 = Resolver.credAdditional) :
    (c1.toCode ≤ c2.toCode)
      ↔ (VeriDNS.Spec.Net.Cred.rank (αCred c2) ≤ VeriDNS.Spec.Net.Cred.rank (αCred c1)) := by
  apply αCred_order_used
  · rcases h1 with rfl | rfl | rfl
    · exact cred_used_credAnswer aa1
    · exact cred_used_credAuthority aa1
    · exact cred_used_credAdditional
  · rcases h2 with rfl | rfl | rfl
    · exact cred_used_credAnswer aa2
    · exact cred_used_credAuthority aa2
    · exact cred_used_credAdditional

theorem αCred_credAnswer (aa : Bool) :
    αCred (Resolver.credAnswer aa)
      = (if aa then VeriDNS.Spec.Net.Cred.authoritative else VeriDNS.Spec.Net.Cred.glue) := by
  cases aa <;> rfl

theorem αCred_credAuthority (aa : Bool) :
    αCred (Resolver.credAuthority aa)
      = (if aa then VeriDNS.Spec.Net.Cred.authority else VeriDNS.Spec.Net.Cred.additional) := by
  cases aa <;> rfl

theorem αCred_credAdditional :
    αCred Resolver.credAdditional = VeriDNS.Spec.Net.Cred.additional := rfl

def αRCode : VeriDNS.Spec.Rcode → VeriDNS.Spec.Net.RCode
  | .noError => .noError
  | .nameError => .nameError
  | _ => .servFail

def αIPv4 (rdata : ByteArray) : Option VeriDNS.Spec.Net.IPv4 :=
  if rdata.size = 4 then
    some ⟨rdata.data[0]!, rdata.data[1]!, rdata.data[2]!, rdata.data[3]!⟩
  else none

def αRData (type : BitVec 16) (rdata : ByteArray) : Option VeriDNS.Spec.Net.RData :=
  match type.toNat with
  | 1 => (αIPv4 rdata).map .a
  | 2 => (αName rdata).map .ns
  | 5 => (αName rdata).map .cname
  | 12 => (αName rdata).map .ptr
  | _ => none

def αRR (rr : VeriDNS.Spec.ResourceRecord) : Option VeriDNS.Spec.Net.RR :=
  match αName rr.name, αRData rr.type rr.rdata, αClass rr.class with
  | some owner, some rdata, some cls =>
    some { owner := owner, ttl := rr.ttl.toNat, rdata := rdata, cls := cls }
  | _, _, _ => none

theorem αRData_rtype (type : BitVec 16) (rdata : ByteArray) (rd : VeriDNS.Spec.Net.RData)
    (h : αRData type rdata = some rd) : αType type = some rd.rtype := by
  unfold αRData at h
  unfold αType
  split at h <;> rename_i heq <;>
    first
    | (rw [Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h; simp [heq, VeriDNS.Spec.Net.RData.rtype])
    | simp at h

theorem αRR_rtype (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : αRR rr = some r) : αType rr.type = some r.rdata.rtype := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    rw [← Option.some.inj h]
    exact αRData_rtype rr.type rr.rdata rdata hrd
  · exact absurd h (by simp)

theorem αRR_fields (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : αRR rr = some r) :
    αName rr.name = some r.owner ∧ r.ttl = rr.ttl.toNat ∧ αClass rr.class = some r.cls := by
  unfold αRR at h
  split at h
  · rename_i owner rdata cls hn hrd hcl
    obtain rfl := Option.some.inj h
    exact ⟨hn, rfl, hcl⟩
  · exact absurd h (by simp)

/-- **Bailiwick correspondence (the bailiwick half of the Phase-3 `hcorr`).** A raw kept by the impl
    `bailiwickRaws bw` filter, parsed and abstracted to a model record `r`, has its owner inside the model
    bailiwick `bwN` (`isAncestor bwN r.owner`). Composes `bailiwickRaws_owner_inBailiwick` (impl
    `isAncestorB`) with `isAncestorB_isAncestor` (the impl↔model bailiwick bridge) and `αRR_fields` (owner
    abstraction). This is what lines up the impl's `bailiwickRaws`-filtered referral records with the model
    `absorb`'s `keep = isAncestor bw`-filtered sections. -/
theorem bailiwickRaws_owner_model (bw : ByteArray) (raws : Array ByteArray) {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR} {bwN : VeriDNS.Spec.Net.Name}
    (hb : b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws).toList)
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hαr : αRR rr = some r) (hbwN : αName bw = some bwN) :
    VeriDNS.Spec.Net.isAncestor bwN r.owner = true := by
  have him : Resolver.isAncestorB bw (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr)
      = true := Resolver.bailiwickRaws_owner_inBailiwick bw raws hb hpr
  have hname : αName rr.name = some r.owner := (αRR_fields rr r hαr).1
  have hrn : VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr = rr.name := rfl
  rw [hrn] at him
  exact isAncestorB_isAncestor bw rr.name bwN r.owner hbwN hname him

/-- **Reverse `bailiwickRaws` inclusion**: an in-bailiwick parseable raw *is* kept by the filter. Together
    with `bailiwickRaws_subset`/`_owner_inBailiwick` (forward), this characterizes `bailiwickRaws`
    membership both ways — what the Phase-3 `hcorr` multiset `Perm` needs (the impl keeps exactly the
    in-bailiwick records, mirroring the model `absorb`'s `keep`). -/
theorem mem_bailiwickRaws (bw : ByteArray) (raws : Array ByteArray) {b : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord}
    (hb : b ∈ raws.toList) (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr)
    (hbail : Resolver.isAncestorB bw (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr)
        = true) :
    b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws).toList := by
  have hb' : b ∈ raws := Array.mem_def.mpr hb
  have hmem : b ∈ Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw raws := by
    unfold Resolver.bailiwickRaws
    rw [Array.mem_filter]
    exact ⟨hb', by simp only [hpr]; exact hbail⟩
  exact Array.mem_def.mp hmem

def αSection (rrs : Array ByteArray) : List VeriDNS.Spec.Net.RR :=
  rrs.toList.filterMap fun b =>
    match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | some rr => αRR rr
    | none => none

/-- **Forward section inclusion (the forward half of `hcorr`'s section correspondence).** Every record in
    the impl's bailiwick-filtered section (abstracted via `αSection`) is in the abstracted full section AND
    in the model bailiwick `bwN`. Composes `bailiwickRaws_subset` + `bailiwickRaws_owner_model`; no canonicity
    needed. The *reverse* inclusion (model keep ⟹ impl kept) needs the canonical-name reverse correspondence
    (`nameEqCI_of_αName_canonical`-style, under the `WfRR` invariant) — the same dependency the hhit
    *read*-path completeness half had; `hcorr`'s full multiset `Perm` is thus the write-path analogue of the
    hhit development. -/
theorem mem_αSection_bailiwickRaws {bw : ByteArray} {section_ : Array ByteArray}
    {r : VeriDNS.Spec.Net.RR} {bwN : VeriDNS.Spec.Net.Name} (hbwN : αName bw = some bwN)
    (hr : r ∈ αSection (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw section_)) :
    r ∈ αSection section_ ∧ VeriDNS.Spec.Net.isAncestor bwN r.owner = true := by
  unfold αSection at hr ⊢
  rw [List.mem_filterMap] at hr ⊢
  obtain ⟨b, hb, hg⟩ := hr
  have hbsec : b ∈ section_.toList :=
    Resolver.bailiwickRaws_subset (RR := VeriDNS.Spec.ResourceRecord) bw section_ hb
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hg; simp at hg
  | some rr =>
    rw [hpr] at hg
    exact ⟨⟨b, hbsec, by rw [hpr]; exact hg⟩, bailiwickRaws_owner_model bw section_ hb hpr hg hbwN⟩

/-- The bailiwick test as a **Bool equality** (both directions combined): under name
    canonicity, the impl byte-level `isAncestorB` agrees with the model `isAncestor` on
    the abstracted names. -/
theorem isAncestorB_eq (bw owner : ByteArray) (bwN ownerN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (hown : αName owner = some ownerN) :
    Resolver.isAncestorB bw owner = VeriDNS.Spec.Net.isAncestor bwN ownerN := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h; exact isAncestorB_isAncestor bw owner bwN ownerN hbw hown h
  · intro h; exact isAncestor_isAncestorB bw owner bwN ownerN hbw hown h

/-- Commute `filter` past `filterMap` when the predicates agree on every produced element:
    `(l.filter p).filterMap g = (l.filterMap g).filter q` provided `g a = some b → p a = q b`. -/
theorem filter_filterMap_comm {α β : Type} (l : List α) (p : α → Bool)
    (g : α → Option β) (q : β → Bool)
    (h : ∀ a b, g a = some b → p a = q b) :
    (l.filter p).filterMap g = (l.filterMap g).filter q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hg : g a with
    | none =>
      cases hp : p a with
      | true => simp [hp, hg, ih]
      | false => simp [hp, hg, ih]
    | some b =>
      have hpq := h a b hg
      cases hp : p a with
      | true =>
        have hq : q b = true := by rw [← hpq]; exact hp
        simp [hp, hg, hq, ih]
      | false =>
        have hq : q b = false := by rw [hp] at hpq; exact hpq.symm
        simp [hp, hg, hq, ih]

/-- **Section-filter LIST equality (the write-path mirror of the hhit read-path).** The impl's
    bailiwick-filtered, abstracted section equals the abstracted full section model-filtered by
    `isAncestor bwN`. Because `αRR` already canonicalizes the owner via `αName`, the per-element
    bailiwick correspondence (`isAncestorB_eq`) needs *no* extra `WfRR` hypothesis. This collapses
    `hcorr`'s `topServed` Perm to the fresh-push case covered by `store_push_records`/`topOf_perm`. -/
theorem αSection_bailiwickRaws_eq (bw : ByteArray) (bwN : VeriDNS.Spec.Net.Name)
    (section_ : Array ByteArray) (hbw : αName bw = some bwN) :
    αSection (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw section_)
      = (αSection section_).filter (fun r => VeriDNS.Spec.Net.isAncestor bwN r.owner) := by
  unfold αSection Resolver.bailiwickRaws
  rw [Array.toList_filter]
  apply filter_filterMap_comm
  intro b r hg
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hpr] at hg; simp at hg
  | some rr =>
    rw [hpr] at hg
    obtain ⟨hn, _, _⟩ := αRR_fields rr r hg
    show Resolver.isAncestorB bw (VeriDNS.Spec.RRParse.rrName rr)
      = VeriDNS.Spec.Net.isAncestor bwN r.owner
    exact isAncestorB_eq bw rr.name bwN r.owner hbw hn

def αResp (f : VeriDNS.Spec.Format) : VeriDNS.Spec.Net.Response :=
  { aa := f.header.aa == 1
    rcode := αRCode f.header.rcode
    answer := αSection f.answer
    authority := αSection f.authority
    additional := αSection f.additional
    ra := f.header.ra == 1
    tc := f.header.tc == 1 }

theorem αResp_components (f : VeriDNS.Spec.Format) :
    (αResp f).rcode = αRCode f.header.rcode
      ∧ (αResp f).answer = αSection f.answer
      ∧ (αResp f).authority = αSection f.authority
      ∧ (αResp f).additional = αSection f.additional
      ∧ (αResp f).aa = (f.header.aa == 1)
      ∧ (αResp f).tc = (f.header.tc == 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Query-side abstraction (the query analogue of `αResp`).** Abstract a wire `Format`'s first
    question to the model `Query`: name/type/class through `αName`/`αQType`/`αClass`, plus the header
    RD bit. `none` if there is no question or any field is unmodelled. This is the first C1 building
    block for the `WorldModels` environment-consistency relation (GAP 1): the recursive-totality
    induction abstracts each query the resolver sends through `αQuery` to instantiate the model server
    derivation that justifies the oracle's reply. -/
def αQuery (f : VeriDNS.Spec.Format) : Option VeriDNS.Spec.Net.Query :=
  match f.question[0]? with
  | none => none
  | some qu =>
    match αName qu.qname, αQType qu.qtype, αClass qu.qclass with
    | some n, some qt, some qc =>
      some { qname := n, qtype := qt, qclass := qc, rd := f.header.rd == 1 }
    | _, _, _ => none

/-- `αQuery` reads question[0] and abstracts its fields (the field-projection lemma, mirroring
    `αRR_fields`). -/
theorem αQuery_fields {f : VeriDNS.Spec.Format} {q : VeriDNS.Spec.Net.Query}
    (h : αQuery f = some q) :
    ∃ qu, f.question[0]? = some qu ∧ αName qu.qname = some q.qname
      ∧ αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by
  unfold αQuery at h
  split at h
  · exact absurd h (by simp)
  · rename_i qu hqu
    split at h
    · rename_i n qt qc hn hqt hqc
      injection h with h; subst h
      exact ⟨qu, hqu, hn, hqt, hqc⟩
    · exact absurd h (by simp)

/-- **The sub-query abstracts to the model query** (answer-terminal prerequisite). `buildSubQuery` forms a
    fresh non-recursive (`rd = 0`) query for `state.resources.sname` carrying the original query's
    type/class. Given the name correspondence (from `StateModels`), the type/class correspondence (the
    driver's query-type invariant), and `q.rd = false` (the network sub-run is iterative), `αQuery` of the
    sub-query is exactly the model query `q`. This is what lets `WorldModels` (keyed by `αQuery`) apply at
    the answer terminal. -/
theorem αQuery_buildSubQuery
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {q : VeriDNS.Spec.Net.Query} {sub : VeriDNS.Spec.Format}
    (hbuild : Resolver.buildSubQuery state = some sub)
    (hsname : αName state.resources.sname = some q.qname)
    (hqt : ∀ qu : VeriDNS.Spec.Question,
        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
        αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass)
    (hrd : q.rd = false) :
    αQuery sub = some q := by
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i q₀ hlq
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu hqu
      injection hbuild with hb
      subst hb
      obtain ⟨hqt', hqc'⟩ := hqt qu ⟨q₀, hlq, hqu⟩
      unfold αQuery
      rw [show (#[{ qname := state.resources.sname, qtype := qu.qtype, qclass := qu.qclass }]
          : Array VeriDNS.Spec.Question)[0]? = some
          { qname := state.resources.sname, qtype := qu.qtype, qclass := qu.qclass } from rfl]
      dsimp only
      rw [hsname, hqt', hqc']
      dsimp only
      cases q; simp_all

/-- **Address-side bridge (C1, GAP 1).** Decode the model `String` server address from the oracle's
    6-byte key (the `ipv4ToAddr` form: 4 IP octets + 2 port bytes) as the dotted-decimal of the first
    four octets. The `WorldModels` relation keys oracle exchanges by these byte addresses, while the
    model's `serverAt`/`Server.addr` use `String`s — this resolves that impedance (impl `BitVec 32`/byte
    IPs ↔ model `String`s). -/
def byteAddrToModel (ab : ByteArray) : String :=
  s!"{ab.get! 0 |>.toNat}.{ab.get! 1 |>.toNat}.{ab.get! 2 |>.toNat}.{ab.get! 3 |>.toNat}"

/-- The address bridge is consistent with the model's `IPv4.toDotted`: decoding the oracle key built
    from an IP (`ipv4ToAddr`) yields exactly the dotted string the model uses for that IP's `A`-record
    address. So a glue `A`-record's model address and the byte address the resolver actually queries
    name the *same* server — the consistency `WorldModels` needs to line up `serverAt net (byteAddrToModel
    ab)` with the impl's query target. -/
theorem byteAddrToModel_ipv4ToAddr (ip : BitVec 32) (port : UInt16) :
    byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr ip port)
      = (VeriDNS.Spec.Net.IPv4.toDotted
          ⟨(ip >>> 24).toNat.toUInt8, ((ip >>> 16) &&& 0xFF).toNat.toUInt8,
           ((ip >>> 8) &&& 0xFF).toNat.toUInt8, (ip &&& 0xFF).toNat.toUInt8⟩) :=
  rfl

/-- Truncating a `BitVec 32` to a `UInt8` (via `toNat`) keeps exactly the low 8 bits — the bridge that lets
    `bv_decide` see through the `UInt8`/`Nat` round-trip in the glue address recovery. -/
theorem toNat_toUInt8_toBitVec (x : BitVec 32) : (x.toNat.toUInt8).toBitVec = x.setWidth 8 :=
  UInt8.toBitVec_ofBitVec (BitVec.ofNat 8 x.toNat)

/-- `getLsbD` of the `0xFF` mask over `BitVec 32`: true exactly on the low byte (`i < 8`). Axiom-clean
    (`Nat.testBit_two_pow_sub_one`), replacing a `bv_decide` mask fact in the IPv4 byte-unpack. -/
theorem getLsbD_0xFF_32 (i : Nat) : (0xFF : BitVec 32).getLsbD i = decide (i < 8) := by
  rw [show (0xFF : BitVec 32) = BitVec.ofNat 32 (2^8 - 1) from rfl,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp [h, (by omega : i < 32)]
  · simp only [decide_eq_false (show ¬ i < 8 from by omega), Bool.and_false]

/-- **IPv4 big-endian pack/unpack round-trip, axiom-clean `getLsbD` bit-blast** (no `bv_decide` native LRAT
    axiom). Each byte extracted from the packed 32-bit address (`>>> 24` top; `>>> 16/8` + `&&& 0xFF`; low
    `&&& 0xFF`) recovers the original. Per conjunct: more-significant bytes vanish via the shift gate
    `decide (k+i < s) = true`, less-significant via `getLsbD_of_ge` (index ≥ 8 of a `BitVec 8`). -/
theorem ipv4_unpack (b0 b1 b2 b3 : UInt8) (packed : BitVec 32)
    (hp : packed = BitVec.setWidth 32 b0.toBitVec <<< 24 ||| BitVec.setWidth 32 b1.toBitVec <<< 16 |||
        BitVec.setWidth 32 b2.toBitVec <<< 8 ||| BitVec.setWidth 32 b3.toBitVec) :
    (BitVec.setWidth 8 (packed >>> 24) = b0.toBitVec)
      ∧ (BitVec.setWidth 8 ((packed >>> 16) &&& 0xFF) = b1.toBitVec)
      ∧ (BitVec.setWidth 8 ((packed >>> 8) &&& 0xFF) = b2.toBitVec)
      ∧ (BitVec.setWidth 8 (packed &&& 0xFF) = b3.toBitVec) := by
  subst hp
  have z1 : ∀ k, 8 ≤ k → b1.toBitVec.getLsbD k = false := fun k h => BitVec.getLsbD_of_ge _ _ h
  have z2 : ∀ k, 8 ≤ k → b2.toBitVec.getLsbD k = false := fun k h => BitVec.getLsbD_of_ge _ _ h
  have z3 : ∀ k, 8 ≤ k → b3.toBitVec.getLsbD k = false := fun k h => BitVec.getLsbD_of_ge _ _ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    rw [show 24 + i - 24 = i from by omega, z1 (24+i-16) (by omega), z2 (24+i-8) (by omega), z3 (24+i) (by omega)]
    simp [hi, decide_eq_false (show ¬ 24+i < 24 from by omega), decide_eq_false (show ¬ 24+i < 16 from by omega),
      decide_eq_false (show ¬ 24+i < 8 from by omega), (show 24+i < 32 from by omega), (show i < 32 from by omega)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_and, getLsbD_0xFF_32]
    rw [show 16 + i - 16 = i from by omega, z2 (16+i-8) (by omega), z3 (16+i) (by omega)]
    simp [hi, decide_eq_false (show ¬ 16+i < 16 from by omega), (show 16+i < 24 from by omega),
      (show 16+i < 32 from by omega), (show i < 32 from by omega), (show i < 8 from hi)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_and, getLsbD_0xFF_32]
    rw [show 8 + i - 8 = i from by omega, z3 (8+i) (by omega)]
    simp [hi, decide_eq_false (show ¬ 8+i < 8 from by omega), (show 8+i < 16 from by omega),
      (show 8+i < 24 from by omega), (show 8+i < 32 from by omega), (show i < 32 from by omega), (show i < 8 from hi)]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_and, getLsbD_0xFF_32]
    simp [hi, (show i < 8 from hi), (show i < 16 from by omega), (show i < 24 from by omega), (show i < 32 from by omega)]

/-- **The 4-byte glue address packs and unpacks faithfully.** The impl's `extractGlueRecords` packs an `A`
    record's 4 rdata bytes into a `BitVec 32` (`b0<<<24 ||| b1<<<16 ||| b2<<<8 ||| b3`); `ipv4ToAddr` then
    unpacks them back. So the recovered octets are exactly the originals — the BV-level core of the referral
    SLIST connector's glue address abstraction (`addr ↔ αIPv4`): the impl's packed glue address names the same
    IPv4 the model's `αIPv4` reads off the same rdata. Now axiom-clean via `ipv4_unpack` (no `bv_decide`). -/
theorem ipv4_pack_unpack (b0 b1 b2 b3 : UInt8) :
    ((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) >>> 24).toNat.toUInt8 = b0)
      ∧ (((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) >>> 16) &&& 0xFF).toNat.toUInt8 = b1)
      ∧ (((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) >>> 8) &&& 0xFF).toNat.toUInt8 = b2)
      ∧ ((((b0.toBitVec.setWidth 32 <<< 24) ||| (b1.toBitVec.setWidth 32 <<< 16) |||
        (b2.toBitVec.setWidth 32 <<< 8) ||| b3.toBitVec.setWidth 32) &&& 0xFF).toNat.toUInt8 = b3) := by
  have h := ipv4_unpack b0 b1 b2 b3 _ rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.1
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.2.1
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.2.2.1
  · apply UInt8.toBitVec_inj.1; rw [toNat_toUInt8_toBitVec]; exact h.2.2.2

/-- The referral SLIST installed by `setUpAddresses … mc` reports `matchCount = mc` (definitional). One half
    of the `currentCloser = false` fact that pins `stepFindServers` to the cache-re-derive branch after a
    referral (the installed `matchCount` is the delegation match count `mc`, not deeper than `walkNs`'s). -/
theorem matchCount_setUpAddresses (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    VeriDNS.Spec.SlistFromNameSpec.matchCount (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
      (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) names glue mc) = mc :=
  rfl

/-- **`fromNsWithGlueAll` is empty iff there are no NS names** — the `searchFails` law for the all-addresses
    SLIST (each NS host yields ≥1 entry: a glued host its addresses, a glueless host one address-less entry). The
    `flatMap` analogue of the old `map`-based proof; `stepFindServers`'s `currentCloser` still detects the
    nonempty re-derived SLIST. -/
theorem searchFails_fromNsWithGlueAll (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc).servers.isEmpty = names.isEmpty := by
  unfold VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll
  rw [Bool.eq_iff_iff, Array.isEmpty_iff, Array.isEmpty_iff, Array.flatMap_eq_empty_iff]
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Array.exists_mem_of_ne_empty names hne
    have hgx := h x hx
    by_cases he : (glue.filterMap (fun gp =>
        if DomainName.foldNameCase gp.1 == DomainName.foldNameCase x then some gp.2 else none)).isEmpty = true
    · rw [if_pos he] at hgx; simp at hgx
    · rw [if_neg he, Array.map_eq_empty_iff] at hgx
      exact he (by rw [Array.isEmpty_iff]; exact hgx)
  · rintro rfl
    intro x hx
    exact absurd hx (by simp)

theorem searchFails_setUpAddresses (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    VeriDNS.Spec.SlistFromNameSpec.searchFails (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
      (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) names glue mc)
      = names.isEmpty :=
  searchFails_fromNsWithGlueAll names glue mc

/-- **`currentCloser` is `false` after a referral** (modulo `walkMc ≥ mc`). `stepFindServers`'s `currentCloser
    walkMc := !searchFails slist && walkMc < matchCount slist` is `false` for the just-installed referral slist
    (`setUpAddresses names glue mc`, `names ≠ #[]`) whenever `walkMc ≥ mc` — so the impl takes the cache-
    RE-DERIVE branch. Assembles `searchFails_setUpAddresses` + `matchCount_setUpAddresses` + the inequality; the
    remaining `walkMc ≥ mc` (= `delegationMatchCount ≤ walkNs`'s cut depth) is the gating `walkNs`-trace fact. -/
theorem currentCloser_false_of_ge (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc walkMc : Nat)
    (hne : names.isEmpty = false) (hge : mc ≤ walkMc) :
    (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := VeriDNS.Impl.SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry) names glue mc)
      && decide (walkMc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := VeriDNS.Impl.SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := VeriDNS.Impl.SList.DnsSList)
            (NS := VeriDNS.Spec.SlistEntry) names glue mc))) = false := by
  rw [searchFails_setUpAddresses, matchCount_setUpAddresses, hne]
  simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt]
  exact hge

/-- **`walkNs` terminal: NS records cached at `name` ⟹ stop here.** When the cache holds NS records for
    `name` (`lookup … ≠ ∅`), `stepFindServers`'s `walkNs` returns immediately the NS-name set and the match
    count `= name`'s label depth — no walk to the parent. The base case of the referral `.continue` inversion's
    `walkNs` cache-trace (the walk reaches the delegation cut `zone`, where the just-absorbed NS RRset lives,
    and stops with `mc = labels.size zone`). -/
theorem walkNs_base {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (name : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (fuel : Nat)
    (h : (VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now : Array RR).isEmpty = false) :
    Resolver.stepFindServers.walkNs (RR := RR) name cache nsType inClass now (fuel + 1)
      = some ((VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now).filterMap (fun (rr : RR) =>
          if VeriDNS.Spec.RRParse.rrType (RR := RR) rr == nsType
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr) else none),
        (match DomainName.wireFormatToLabels name with | .ok labels => labels.size | .error _ => 0)) := by
  unfold Resolver.stepFindServers.walkNs
  simp only [h, Bool.false_eq_true, if_false]
  rfl

/-- **`walkNs` step: no NS cached at `name`, walk to the parent.** When the cache holds no NS RRset for
    `name` (`lookup … = ∅`) and `name` has a parent, `walkNs` recurses upward (consuming one fuel). With
    `walkNs_base` this characterizes the full ascent from `sname` to the delegation cut `zone` — the
    structural skeleton of the referral `.continue` inversion's `walkNs` cache-trace. -/
theorem walkNs_step {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (name : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (fuel : Nat)
    (parent : ByteArray)
    (h : (VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now : Array RR).isEmpty = true)
    (hp : DomainName.parentDomainWire name = some parent) :
    Resolver.stepFindServers.walkNs (RR := RR) name cache nsType inClass now (fuel + 1)
      = Resolver.stepFindServers.walkNs (RR := RR) parent cache nsType inClass now fuel := by
  rw [Resolver.stepFindServers.walkNs]
  simp only [h, if_true, hp]

/-- **`walkNs` one-hop ascent** (`walkNs_step` then `walkNs_base`): no NS at `name`, but the parent (the
    delegation cut) has the cached NS RRset — `walkNs` ascends once and stops there, returning the parent's
    NS-name set and label-depth match count. The common single-label delegation case of the referral
    `.continue` inversion's cache-trace. -/
theorem walkNs_one_hop {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (name parent : ByteArray) (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (fuel : Nat)
    (h1 : (VeriDNS.Spec.CacheSpec.lookupTopCred cache name nsType inClass now : Array RR).isEmpty = true)
    (hp : DomainName.parentDomainWire name = some parent)
    (h2 : (VeriDNS.Spec.CacheSpec.lookupTopCred cache parent nsType inClass now : Array RR).isEmpty = false) :
    Resolver.stepFindServers.walkNs (RR := RR) name cache nsType inClass now (fuel + 2)
      = some ((VeriDNS.Spec.CacheSpec.lookupTopCred cache parent nsType inClass now).filterMap (fun (rr : RR) =>
          if VeriDNS.Spec.RRParse.rrType (RR := RR) rr == nsType
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr) else none),
        (match DomainName.wireFormatToLabels parent with | .ok labels => labels.size | .error _ => 0)) := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl,
     walkNs_step name cache nsType inClass now (fuel + 1) parent h1 hp]
  exact walkNs_base parent cache nsType inClass now fuel h2

/-- **`walkNs` multi-hop ascent.** Given a parent-chain of `inter`mediate names from `start` up to the
    delegation cut `zone`, each with an empty NS cache and `zone` holding the NS RRset, `walkNs start` (with
    enough fuel) ascends the whole chain and returns the same result as `walkNs zone` — pinning the referral
    `.continue` inversion's `walkNs` to the cut, independent of delegation depth. Structural induction over
    `inter` (the cache-state path itself is the driver's obligation, discharged via the absorb round-trip). -/
theorem walkNs_ascend {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (cache : C) (nsType inClass : BitVec 16) (now : UInt32) (zone : ByteArray)
    (h2 : (VeriDNS.Spec.CacheSpec.lookupTopCred cache zone nsType inClass now : Array RR).isEmpty = false) :
    ∀ (inter : List ByteArray) (start : ByteArray) (fuel : Nat),
      inter.length + 2 ≤ fuel →
      List.Chain (fun a b => DomainName.parentDomainWire a = some b) start (inter ++ [zone]) →
      (∀ m ∈ start :: inter,
        (VeriDNS.Spec.CacheSpec.lookupTopCred cache m nsType inClass now : Array RR).isEmpty = true) →
      Resolver.stepFindServers.walkNs (RR := RR) start cache nsType inClass now fuel
        = Resolver.stepFindServers.walkNs (RR := RR) zone cache nsType inClass now 1 := by
  intro inter
  induction inter with
  | nil =>
    intro start fuel hf hchain hempty
    obtain ⟨hps, _⟩ := List.chain_cons.mp hchain
    have hes := hempty start (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    rw [show f + 2 = (f + 1) + 1 from rfl,
       walkNs_step start cache nsType inClass now (f + 1) zone hes hps,
       walkNs_base zone cache nsType inClass now f h2,
       walkNs_base zone cache nsType inClass now 0 h2]
  | cons m rest ih =>
    intro start fuel hf hchain hempty
    obtain ⟨hps, hchain'⟩ := List.chain_cons.mp hchain
    have hes := hempty start (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [walkNs_step start cache nsType inClass now f m hes hps]
    exact ih m f (by simpa using hf) hchain' (fun x hx => hempty x (List.mem_cons_of_mem start hx))

/-- **`walkNs` success inversion.** From `walkNs sname = some (nsNames, mc)`, recover the delegation cut: EITHER
    NS is cached at `sname` itself (the base — `cut = sname`, handled by `keystone_at_cut` directly) OR `walkNs`
    ASCENDED a `parentDomainWire`-chain `sname → … → cut` of empty intermediate nodes to a cut with cached NS (the
    `full_walk_keystone`/`refer_continue_keystone` case). This is the structural fact the `.continue` refer driver
    needs: its actual `walkNs` result determines the cut + chain + empties, so the keystone's walk hypotheses are
    DISCHARGED from the run itself (no oracle). -/
theorem walkNs_some_inversion {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (cache : C) (nsType inClass : BitVec 16) (now : UInt32) :
    ∀ (fuel : Nat) (sname : ByteArray) (nsNames : Array ByteArray) (mc : Nat),
      Resolver.stepFindServers.walkNs (RR := RR) sname cache nsType inClass now fuel = some (nsNames, mc) →
      (VeriDNS.Spec.CacheSpec.lookupTopCred cache sname nsType inClass now : Array RR).isEmpty = false
      ∨ ∃ cut inter, List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut])
          ∧ (∀ m ∈ sname :: inter,
              (VeriDNS.Spec.CacheSpec.lookupTopCred cache m nsType inClass now : Array RR).isEmpty = true)
          ∧ (VeriDNS.Spec.CacheSpec.lookupTopCred cache cut nsType inClass now : Array RR).isEmpty = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname nsNames mc h
    rw [Resolver.stepFindServers.walkNs] at h
    exact absurd h (by simp)
  | succ f ih =>
    intro sname nsNames mc h
    by_cases he : (VeriDNS.Spec.CacheSpec.lookupTopCred cache sname nsType inClass now : Array RR).isEmpty = true
    · right
      cases hp : DomainName.parentDomainWire sname with
      | none =>
        rw [Resolver.stepFindServers.walkNs] at h
        simp only [he, if_true, hp] at h
        exact absurd h (by simp)
      | some parent =>
        rw [walkNs_step sname cache nsType inClass now f parent he hp] at h
        rcases ih parent nsNames mc h with hbase | ⟨cut, inter, hchain, hempty, hcut_ne⟩
        · exact ⟨parent, [], List.Chain.cons hp List.Chain.nil,
            fun m hm => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; exact he, hbase⟩
        · refine ⟨cut, parent :: inter, ?_, ?_, hcut_ne⟩
          · rw [List.cons_append]; exact List.Chain.cons hp hchain
          · intro m hm
            rcases List.mem_cons.mp hm with rfl | hm'
            · exact he
            · exact hempty m hm'
    · left; simpa using he

/-- **`lookup` respects `nameEqCI`.** `liveEntry` matches the query name case-insensitively (`nameEqCI`), and the
    returned RR (`{e.rr with ttl := …}`) is independent of the query name — so two `nameEqCI`-equal names produce
    the *same* lookup result. This is the algebraic fact behind `findSome?_const_on_pred`'s `hconst` for the glue
    round-trip: all `nameEqCI`-variants of an NS host yield the same cache-A address. -/
theorem lookup_nameEqCI_congr (c : Cache.DnsCache) (m n : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (h : nameEqCI m n = true) :
    c.lookup m qt qc now = c.lookup n qt qc now := by
  have hfold : DomainName.foldNameCase m = DomainName.foldNameCase n := by
    have h'' : ByteArray.beq (DomainName.foldNameCase m) (DomainName.foldNameCase n) = true := h
    unfold ByteArray.beq at h''
    exact ByteArray.ext (eq_of_beq h'')
  unfold Cache.DnsCache.lookup
  congr 1
  funext e
  have hle : Cache.liveEntry e m qt qc now = Cache.liveEntry e n qt qc now := by
    unfold Cache.liveEntry nameEqCI; rw [hfold]
  rw [hle]

/-- **A live cache entry's (TTL-aged) record IS in the lookup result.** The read-side membership: `lookup`
    returns the aged copy of every live matching entry. The VALUE-level basis of the referral cache round-trip
    read — after the absorb stores the cut's NS RRset, each absorbed NS record (aged, `rdata` preserved) appears
    in `lookup cut nsType`, so `stepFindServers`'s re-derived `nsNames = (lookup cut nsType).filterMap rrRdata`
    contains the referral's NS names. Strengthens `lookup_nonempty_of_mem` (which is the `≠ ∅` corollary). -/
theorem mem_lookup_of_live (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hlive : Cache.liveEntry e name qtype qclass now = true) :
    ({ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } : VeriDNS.Spec.ResourceRecord)
      ∈ c.lookup name qtype qclass now := by
  unfold Cache.DnsCache.lookup
  rw [Array.mem_filterMap]
  exact ⟨e, he, by simp only [hlive, if_true]⟩

/-- **Every lookup result comes from a live cache record** (the converse-read provenance). A record in
    `lookup name qtype qclass now` is the TTL-aged copy of some `liveEntry` in `c.records`. With
    `mem_cacheRRs_records` + the cache-miss invariant (no prior NS at the cut), this pins the post-absorb
    `lookup cut nsType` to EXACTLY the absorbed delegation NS — the converse half of the cache round-trip read
    (`nsNames ⊆ absorbed`), completing the set-level `nsNames = extractNsNames` correspondence for a cold cut. -/
theorem mem_records_of_mem_lookup (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (r : VeriDNS.Spec.ResourceRecord) (hr : r ∈ c.lookup name qtype qclass now) :
    ∃ e ∈ c.records, Cache.liveEntry e name qtype qclass now = true
      ∧ r = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold Cache.DnsCache.lookup at hr
  rw [Array.mem_filterMap] at hr
  obtain ⟨e, he, hmap⟩ := hr
  split at hmap
  · next hl => exact ⟨e, he, hl, (Option.some.inj hmap).symm⟩
  · simp at hmap

/-- **An absorbed NS record's rdata is in `walkNs`'s re-derived `nsNames`.** `walkNs` (stepFindServers) sets
    `nsNames := (lookup name nsType inClass).filterMap (fun rr => if rrType==nsType then some (rrRdata) else none)`;
    by `mem_lookup_of_live` the live NS entry's aged copy is in the lookup (type/rdata preserved by aging), so it
    survives the filter. The forward half of the referral cache round-trip read: every absorbed delegation NS
    name reappears in the re-derived SLIST's NS-name list. -/
theorem mem_walkNs_nsNames_of_live (c : Cache.DnsCache) (name : ByteArray) (nsType inClass : BitVec 16)
    (now : UInt32) (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hlive : Cache.liveEntry e name nsType inClass now = true) :
    e.rr.rdata ∈ (c.lookup name nsType inClass now).filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == nsType
        then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) := by
  have htype : (e.rr.type == nsType) = true := by
    have h := hlive; simp only [Cache.liveEntry, Bool.and_eq_true] at h; exact h.1.1.2
  rw [Array.mem_filterMap]
  refine ⟨{ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat },
    mem_lookup_of_live c name nsType inClass now e he hlive, ?_⟩
  simp only [VeriDNS.Spec.RRParse.rrType, VeriDNS.Spec.RRParse.rrRdata, htype, if_true]

/-- **Converse cache-read (cold cut): a re-derived NS name was actually in the referral's authority.** For a
    cut with no prior live NS (`hmiss`, the cache-miss invariant), every NS name `stepFindServers` re-derives
    from `lookup cut` after the absorb `cacheRRs c (bailiwickRaws cut authority)` is the rdata of a real NS RR
    of `authority` — so it's in `extractNsNames authority`. Composes `mem_records_of_mem_lookup` +
    `mem_cacheRRs_records` (provenance) + `bailiwickRaws_subset`. With `mem_walkNs_nsNames_of_live` (forward),
    this is the SET-level `nsNames = extractNsNames` for a cold cut (multiset/order is the dedup layer). -/
theorem nsName_mem_extractNsNames_of_rederived (c : Cache.DnsCache) (cut : ByteArray)
    (authority : Array ByteArray) (cred : Trustworthiness) (now : UInt32) (nm : ByteArray)
    (hmiss : ∀ e ∈ c.records,
      Cache.liveEntry e cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now = false)
    (hmem : nm ∈ ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut authority) cred now).lookup
        cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)) :
    nm ∈ Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) authority := by
  rw [Array.mem_filterMap] at hmem
  obtain ⟨r, hrlook, hrf⟩ := hmem
  obtain ⟨e, he, hlive, hre⟩ :=
    mem_records_of_mem_lookup _ cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now r hrlook
  rw [hre] at hrf
  simp only [VeriDNS.Spec.RRParse.rrType, VeriDNS.Spec.RRParse.rrRdata] at hrf
  split at hrf
  · next htype =>
    obtain rfl : e.rr.rdata = nm := Option.some.inj hrf
    rcases mem_cacheRRs_records _ cred now c he with hcmem | ⟨b, hb, hpb⟩
    · simp [hmiss e hcmem] at hlive
    · have hbauth : b ∈ authority.toList :=
        Resolver.bailiwickRaws_subset (RR := VeriDNS.Spec.ResourceRecord) cut authority hb
      unfold Resolver.extractNsNames
      rw [Array.mem_filterMap]
      refine ⟨b, Array.mem_def.mpr hbauth, ?_⟩
      simp only [hpb, VeriDNS.Spec.RRParse.rrType, VeriDNS.Spec.RRParse.rrRdata, htype, if_true]
  · exact absurd hrf (by simp)

theorem lookup_nonempty_of_mem (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hlive : Cache.liveEntry e name qtype qclass now = true) :
    (c.lookup name qtype qclass now).isEmpty = false := by
  have hmem := mem_lookup_of_live c name qtype qclass now e he hlive
  by_contra h
  rw [Bool.not_eq_false, Array.isEmpty_iff] at h
  rw [h] at hmem
  simp at hmem

/-- **The referral cache write makes the NS-owner key live (`lookup ≠ ∅`).** Composes
    `mem_cacheRRs_live_of_split` (the just-stored NS entry is present and live) with `lookup_nonempty_of_mem`.
    This is `walkNs_ascend`'s `h2` for the honest-referral threading: after the impl absorbs the delegation's
    NS RRset (`cacheRRs` over the bailiwick authority raws, the cut's NS RR split out as `nsRaw`), a `lookup`
    at the cut returns it — so `walkNs` halts at the cut rather than ascending past it. -/
theorem lookup_nonempty_after_cacheRRs (c : Cache.DnsCache) (pre post : Array ByteArray)
    (nsRaw : ByteArray) (nsRR : VeriDNS.Spec.ResourceRecord) (cred : Trustworthiness) (now : UInt32)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) nsRaw = some nsRR)
    (hnz : (nsRR.ttl == 0) = false)
    (hbetter : ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c pre cred now).records.any
      fun e => DomainName.nameEqCI e.rr.name nsRR.name && e.rr.type == nsRR.type && e.rr.class == nsRR.class
        && (e.expiry > now || e.expiry == now + nsRR.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false)
    (hfresh : Cache.CacheEntry.fresh ⟨nsRR, now + nsRR.ttl.toNat.toUInt32, false, cred⟩ now = true)
    (hpost : ∀ b ∈ post, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (DomainName.nameEqCI nsRR.name rr.name && nsRR.type == rr.type && nsRR.class == rr.class
        && (now + nsRR.ttl.toNat.toUInt32 != now + rr.ttl.toNat.toUInt32 || nsRR.rdata == rr.rdata)) = false) :
    ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (pre ++ #[nsRaw] ++ post) cred now).lookup nsRR.name nsRR.type nsRR.class now).isEmpty = false := by
  obtain ⟨e, hmem, hlive⟩ :=
    mem_cacheRRs_live_of_split c pre post nsRaw nsRR cred now hp hnz hbetter hfresh hpost
  exact lookup_nonempty_of_mem _ nsRR.name nsRR.type nsRR.class now e hmem hlive

/-- **No live matching cache entry makes `lookup` empty.** The converse of `lookup_nonempty_of_mem`: if NO
    record matches the key `(name, qtype, qclass)` live, `DnsCache.lookup` returns `∅`. The walk-up half of
    the referral cache round-trip: above the cut (where the absorb stored nothing, and the driver's cache-miss
    invariant holds) `lookup … nsType inClass = ∅` (discharging `walkNs_ascend`'s `hempty` chain). -/
theorem lookup_empty_of_no_mem (c : Cache.DnsCache) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) (hno : ∀ e ∈ c.records, Cache.liveEntry e name qtype qclass now = false) :
    (c.lookup name qtype qclass now).isEmpty = true := by
  rw [Array.isEmpty_iff]
  unfold Cache.DnsCache.lookup
  rw [Array.filterMap_eq_empty_iff]
  intro e he
  simp only [hno e he, Bool.false_eq_true, if_false]

/-- **A `lookup` at an intermediate (non-cut) name stays empty after the referral absorb (`walkNs_ascend`'s
    `hempty`).** `cacheRRs` over the bailiwick raws (`cacheRRs_bailiwick_owner`) only adds entries whose owner is
    at/below the cut; `hbwlive` says none of those is `liveEntry` for `(m, qtype, qclass)` (the absorbed NS RRset
    sits at the cut, owner ≠ `m`; absorbed *glue* is type `A`, so it fails an NS-`qtype` `lookup` on the type
    check even if its owner = `m`), and the original cache had no live match (`hc`, the cache-miss invariant).
    So `lookup m … = ∅` — the intermediates between `sname` and the cut have no NS, so `walkNs` ascends to the
    cut. (Per-entry `liveEntry`-false, not name-only, so the glue type-mismatch case is handled.) -/
theorem lookup_empty_after_cacheRRs (c : Cache.DnsCache) (cut : ByteArray) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) (m : ByteArray) (qtype qclass : BitVec 16)
    (hc : ∀ e ∈ c.records, Cache.liveEntry e m qtype qclass now = false)
    (hbwlive : ∀ e, Resolver.isAncestorB cut e.rr.name = true → Cache.liveEntry e m qtype qclass now = false) :
    ((Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut raws) cred now).lookup
        m qtype qclass now).isEmpty = true := by
  apply lookup_empty_of_no_mem
  intro e he
  rcases cacheRRs_bailiwick_owner c cut raws cred now he with hcmem | hbw
  · exact hc e hcmem
  · exact hbwlive e hbw

/-- **`store` creates a live entry for the record's own key.** Storing `rr` (with a `fresh` expiry) leaves a
    cache entry that matches `(rr.name, rr.type, rr.class)` live — the absorb (store) side of the referral
    cache round-trip: absorbing the cut's NS RRset makes `lookup zone nsType inClass ≠ ∅`
    (via `lookup_nonempty_of_mem`). The `fresh` premise is discharged from `rr.ttl > 0`. -/
theorem store_self_live (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : Trustworthiness)
    (hfresh : Cache.CacheEntry.fresh ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ now = true) :
    ∃ e ∈ (c.store rr now cred).records, Cache.liveEntry e rr.name rr.type rr.class now = true := by
  refine ⟨⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩, ?_, ?_⟩
  · unfold Cache.DnsCache.store
    exact Array.mem_push.mpr (Or.inr rfl)
  · simp only [Cache.liveEntry, VeriDNS.Proof.NameTree.nameEqCI_refl, beq_self_eq_true, hfresh,
      Bool.and_self]

/-- **`storeChecked` creates a live entry when it actually stores** (`ttl ≠ 0` and no higher-cred incumbent).
    The `storeChecked` analogue of `store_self_live` — the form the `cacheRRs` absorb fold uses. For the
    referral NS RRset at the cut, `ttl > 0` and (by the driver's cache-miss invariant) no higher-cred
    incumbent, so the absorb genuinely stores a live NS entry. -/
theorem storeChecked_self_live (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord) (now : UInt32)
    (cred : Trustworthiness)
    (hnz : (rr.ttl == 0) = false)
    (hbetter : (c.records.any fun e =>
      DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
        && (e.expiry > now || e.expiry == now + rr.ttl.toNat.toUInt32)
        && e.credibility.toCode < cred.toCode) = false)
    (hfresh : Cache.CacheEntry.fresh ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ now = true) :
    ∃ e ∈ (c.storeChecked rr cred now).records, Cache.liveEntry e rr.name rr.type rr.class now = true := by
  simp only [Cache.DnsCache.storeChecked, hnz, Bool.false_eq_true, if_false, hbetter]
  exact store_self_live c rr now cred hfresh

/-- **The impl's packed glue address names exactly the model `αIPv4`'s server.** Combines `ipv4_pack_unpack`
    (the octets recover) with `byteAddrToModel_ipv4ToAddr` (the dotted-string bridge): the byte address the
    resolver queries for an `extractGlueRecords` entry equals the dotted string the model's `αIPv4` gives for
    the same `A`-record rdata. The address-value half of the referral SLIST connector's glue correspondence —
    `byteAddrToModel (ipv4ToAddr (impl-packed addr)) = (αIPv4 rdata).toDotted`. -/
theorem extractGlue_addr_αIPv4 (rd : ByteArray) (a : VeriDNS.Spec.Net.IPv4) (ha : αIPv4 rd = some a) :
    byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr
      ((rd.data[0]!.toBitVec.setWidth 32 <<< 24) ||| (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
       (rd.data[2]!.toBitVec.setWidth 32 <<< 8) ||| rd.data[3]!.toBitVec.setWidth 32))
      = a.toDotted := by
  rw [byteAddrToModel_ipv4ToAddr]
  obtain ⟨h0, h1, h2, h3⟩ := ipv4_pack_unpack rd.data[0]! rd.data[1]! rd.data[2]! rd.data[3]!
  rw [h0, h1, h2, h3]
  unfold αIPv4 at ha
  split at ha
  · rw [← Option.some.inj ha]
  · exact absurd ha (by simp)

/-- **A-record glue extraction reconciliation.** The impl's glue extraction (`if rdata.size == 4 then
    some (pack-then-model) else none`) equals the model's (`(αIPv4 rdata).map toDotted`): `αIPv4` is `some` iff
    `rdata.size = 4`, and on a size-4 rdata `extractGlue_addr_αIPv4` gives `byteAddrToModel (ipv4ToAddr pack) =
    (αIPv4 rdata).toDotted`. The per-record value bridge that turns the impl all-pairs glue's addresses into the
    model `glueAddrsAt` strings. -/
theorem a_extract_reconcile (rd : ByteArray) :
    (αIPv4 rd).map (fun ip => ip.toDotted)
      = if rd.size == 4 then some (byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr
          ((rd.data[0]!.toBitVec.setWidth 32 <<< 24) ||| (rd.data[1]!.toBitVec.setWidth 32 <<< 16) |||
           (rd.data[2]!.toBitVec.setWidth 32 <<< 8) ||| rd.data[3]!.toBitVec.setWidth 32))) else none := by
  cases ha : αIPv4 rd with
  | some a =>
    have hsz : (rd.size == 4) = true := by
      by_contra hc
      unfold αIPv4 at ha
      rw [if_neg (fun h => hc (by simp [h]))] at ha
      exact absurd ha (by simp)
    rw [if_pos hsz, Option.map_some, extractGlue_addr_αIPv4 rd a ha]
  | none =>
    have hsz : (rd.size == 4) = false := by
      by_contra hc
      simp only [Bool.not_eq_false, beq_iff_eq] at hc
      unfold αIPv4 at ha
      rw [if_pos hc] at ha
      exact absurd ha (by simp)
    rw [if_neg (by simp [hsz]), Option.map_none]

/-- **The model image of the implementation's SLIST.** Each addressed `SlistEntry` (a server whose glue
    address is known) maps to the model address string the resolution would query (`byteAddrToModel` of the
    `ipv4ToAddr` byte form); glueless entries (`address = none`, resolved separately via `gluelessNs`) drop
    out. This is the list the strengthened driver conclusion pins the existential model SLIST to (`∃ s,
    HasVerdict … s … ∧ s.Perm (modelSlistOf state.resources.slist)`): the retry branches preserve it (the
    impl retries on `markQueried`, which only bumps a transmission counter — `modelSlistOf_markQueried`),
    and the referral branch relates `modelSlistOf (fromNsWithGlue …)` to `sortByRtt (glueEntries rttOf ref)`
    by permutation, bridged to the model `refer` rule's pinned SLIST through `chooseServer`. -/
def modelSlistOf (s : VeriDNS.Impl.SList.DnsSList) : List String :=
  s.servers.toList.filterMap (fun e =>
    e.address.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))

/-- **Structural unfold of `modelSlistOf` on a `fromNsWithGlue` SLIST.** `fromNsWithGlue` builds one entry
    per NS host, looking up that host's first matching glue address (`glue.findSome?`); `modelSlistOf` then
    keeps the addressed ones and maps to the model string. So the model image is exactly the per-NS-host glue
    lookup mapped through `byteAddrToModel ∘ ipv4ToAddr`. The stepping stone for the SLIST connector's glue
    correspondence (step 4c): it exposes `modelSlistOf (fromNsWithGlue …)` as a `filterMap` over the NS names,
    ready to pair with the model's `glueAddresses` (which `findSome?`-deduplication makes a permutation). -/
theorem modelSlistOf_fromNsWithGlue (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)
      = names.toList.filterMap (fun n =>
          (glue.findSome? (fun (gn, ga) =>
              if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none)).map
            (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.fromNsWithGlue
  rw [Array.toList_map, List.filterMap_map]
  rfl

/-- **Membership in the model SLIST image of `fromNsWithGlue`.** `s` is in `modelSlistOf (fromNsWithGlue names
    glue mc)` iff some NS name `n` has a matching glue address `a` (model `byteAddrToModel (ipv4ToAddr a) = s`).
    A name with no matching glue contributes nothing (the `filterMap` drops `none`). Lets the `modelSlistOf(re-
    derived) = modelSlistOf(installed)` bridge be proved by membership: an out-of-bailiwick installed NS name has
    no in-bailiwick glue (`nameEqCI_false_of_isAncestorB_ne`) so it's absent from both. -/
theorem mem_modelSlistOf_fromNsWithGlue (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) (s : String) :
    s ∈ modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc) ↔
    ∃ n ∈ names.toList, ∃ a, glue.findSome? (fun (gn, ga) =>
        if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none) = some a
      ∧ s = byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a) := by
  rw [modelSlistOf_fromNsWithGlue, List.mem_filterMap]
  constructor
  · rintro ⟨n, hn, hmap⟩
    rw [Option.map_eq_some_iff] at hmap
    obtain ⟨a, ha, hs⟩ := hmap
    exact ⟨n, hn, a, ha, hs.symm⟩
  · rintro ⟨n, hn, a, ha, hs⟩
    exact ⟨n, hn, by rw [ha, Option.map_some, hs]⟩

/-- **`filterMap` is unchanged by filtering out elements that map to `none`.** If every `¬p`-element maps to
    `none`, then `l.filterMap f = (l.filter p).filterMap f`. With `glue_findSome_none_of_out_of_bailiwick`
    (out-of-bailiwick names → no glue → `none`), this gives `modelSlistOf(installed all-NS) = modelSlistOf(
    in-bailiwick NS)` — the in-bailiwick reduction bridging to `referral_slist_eq`. -/
theorem filterMap_filter_of_none {α β : Type} (p : α → Bool) (f : α → Option β) (l : List α)
    (h : ∀ x ∈ l, p x = false → f x = none) :
    l.filterMap f = (l.filter p).filterMap f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun x hx hpx => h x (List.mem_cons_of_mem a hx) hpx)
    cases hpa : p a with
    | true => rw [List.filter_cons_of_pos hpa, List.filterMap_cons, List.filterMap_cons, ih']
    | false =>
      rw [List.filter_cons_of_neg (by simp [hpa]), List.filterMap_cons,
          h a (List.mem_cons_self ..) hpa, ih']

/-- **`modelSlistOf` respects a permutation of the NS-name list** (with the same glue). Since `modelSlistOf
    (fromNsWithGlue names glue)` is `names.toList.filterMap (per-host glue)` and is `matchCount`-independent, a
    `Perm` of the names lifts (via `List.Perm.filterMap`) to a `Perm` of the model SLIST. The keystone's
    Perm-propagation: `nsNames(re-derived).Perm extractNsNames(in-bailiwick)` ⟹ the slist `Perm` that
    `refer_hasVerdict_perm` consumes (addresses may repeat, so this is `Perm`, not `=`). -/
theorem modelSlistOf_perm_of_names_perm {names names' : Array ByteArray}
    (glue : Array (ByteArray × BitVec 32)) (mc mc' : Nat)
    (h : names.toList.Perm names'.toList) :
    (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)).Perm
      (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names' glue mc')) := by
  rw [modelSlistOf_fromNsWithGlue, modelSlistOf_fromNsWithGlue]
  exact h.filterMap _

/-- **`modelSlistOf` drops out-of-bailiwick NS names** (when all glue owners are in-bailiwick). Filtering the
    name list to in-bailiwick names leaves `modelSlistOf` unchanged, since out-of-bailiwick names get no glue
    (`glue_findSome_none_of_out_of_bailiwick`) and so contribute nothing (`filterMap_filter_of_none`). This is
    the in-bailiwick reduction `modelSlistOf(installed all-NS) = modelSlistOf(installed in-bailiwick-NS)` — half
    of the `modelSlistOf(re-derived) = modelSlistOf(installed)` bridge (the re-derived slist only has in-bailiwick
    NS, so this aligns the installed slist to it before chaining `referral_slist_eq`). -/
theorem modelSlistOf_filter_inBailiwick (cut : ByteArray) (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (hglue : ∀ gp ∈ glue, Resolver.isAncestorB cut gp.1 = true) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)
      = modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue
          (names.filter (fun n => Resolver.isAncestorB cut n)) glue mc) := by
  rw [modelSlistOf_fromNsWithGlue, modelSlistOf_fromNsWithGlue, Array.toList_filter]
  apply filterMap_filter_of_none
  intro n _ hp
  rw [glue_findSome_none_of_out_of_bailiwick cut n glue hp hglue, Option.map_none]

/-- `markQueried` only increments a server's transmission counter — it never changes any address — so the
    model image of the SLIST is invariant under it. This is what lets the strengthened driver conclusion's
    `s.Perm (modelSlistOf state)` clause thread through every retry hop (`timeout`/`skipMissing`/`rejectSpoof`/
    `badResponse`/`unfollowableReferral`), which all recurse on `markQueried state`, by `List.Perm.refl`. -/
theorem modelSlistOf_markQueried (s : VeriDNS.Impl.SList.DnsSList) (nm : ByteArray) :
    modelSlistOf (s.markQueried nm) = modelSlistOf s := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.markQueried
  rw [Array.toList_map, List.filterMap_map]
  congr 1
  funext e
  dsimp only [Function.comp]
  split <;> rfl

/-- **`filterMap` distributes over a `filter`/`filter-not` partition, up to permutation.** Splitting a list
    by a predicate `p` and mapping each part is a permutation of mapping the whole. The combinatorial core of
    the timeout/bizarre leaf: `modelSlistOf` (a `filterMap`) over the full SLIST permutes to the removed
    servers' addresses ++ the surviving SLIST's, so each removed address can be discharged by a
    `Resolves.timeout` hop (`Transit.lost` is unconditional) atop the surviving-SLIST verdict. -/
theorem filterMap_partition_perm {α β : Type} (l : List α) (p : α → Bool) (f : α → Option β) :
    (l.filterMap f).Perm ((l.filter p).filterMap f ++ (l.filter (fun x => !p x)).filterMap f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons]
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hp]), List.filterMap_cons]
      cases f a with
      | none => exact ih
      | some b => exact ih.cons b
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos (by simp [hp]),
        List.filterMap_cons]
      cases f a with
      | none => exact ih
      | some b => exact (ih.cons b).trans List.perm_middle.symm

/-- **`removeServer` shrinks the model SLIST to a sublist.** `DnsSList.removeServer` filters out the entries
    named `name`; `modelSlistOf` is a `filterMap` over the server list, and `filterMap` preserves the
    `Sublist` relation. The bizarre-response `.continue` retry (`dropIfBizarre` = `removeServer` of the queried
    NS) drops the just-queried server, so its re-derived model SLIST is a sublist of the original — the slist
    step for the timeout/bizarre leaf of the `.continue` capstone (paired with a `Resolves.timeout` hop that
    re-adds the queried address for the full-SLIST verdict). -/
theorem modelSlistOf_removeServer_sublist (s : VeriDNS.Impl.SList.DnsSList) (name : ByteArray) :
    List.Sublist (modelSlistOf (s.removeServer name)) (modelSlistOf s) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.removeServer
  have hsub : List.Sublist (s.servers.filter (fun e => e.name != name)).toList s.servers.toList := by
    rw [Array.toList_filter]; exact List.filter_sublist
  exact hsub.filterMap _

/-- **The full `removeServer` model-SLIST partition, up to permutation.** `modelSlistOf s` permutes to the
    removed servers' addresses (`filter (·.name == name)`) followed by the surviving SLIST's addresses
    (`modelSlistOf (removeServer …)`). Instantiates `filterMap_partition_perm`. This is the exact bridge for
    the timeout/bizarre leaf: the model discharges each removed address with a `Resolves.timeout` hop
    (`Transit.lost` needs no reachability), building the full-SLIST verdict from the surviving-SLIST IH
    verdict — no SLIST name-uniqueness needed (each removed sibling gets its own free timeout). -/
theorem modelSlistOf_removeServer_perm (s : VeriDNS.Impl.SList.DnsSList) (name : ByteArray) :
    (modelSlistOf s).Perm
      ((s.servers.toList.filter (fun e => e.name == name)).filterMap
          (fun e => e.address.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))
        ++ modelSlistOf (s.removeServer name)) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.removeServer
  rw [Array.toList_filter]
  exact filterMap_partition_perm s.servers.toList (fun e => e.name == name) _

/-- `pickBest` either picks the new candidate `x` (with its concrete address) or keeps the running best
    `acc` unchanged. A single-step inversion feeding the `foldl` invariant below. -/
theorem pickBest_some {acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32)}
    {x e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32}
    (h : VeriDNS.Impl.SList.DnsSList.pickBest acc x = some (e, addr)) :
    (e = x ∧ x.address = some addr) ∨ acc = some (e, addr) := by
  unfold VeriDNS.Impl.SList.DnsSList.pickBest at h
  repeat' split at h
  all_goals simp_all [Option.some.injEq, Prod.mk.injEq]

/-- `bestWithAddress`'s `foldl` invariant: the chosen entry is a real member of the (processed) servers and
    carries exactly the returned address. -/
theorem foldl_pickBest_some (l : List VeriDNS.Spec.SlistEntry)
    (acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32)) {e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32}
    (h : l.foldl VeriDNS.Impl.SList.DnsSList.pickBest acc = some (e, addr)) :
    acc = some (e, addr) ∨ (e ∈ l ∧ e.address = some addr) := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil] at h; exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · rcases pickBest_some h1 with ⟨rfl, ha⟩ | h2
      · exact Or.inr ⟨List.mem_cons_self, ha⟩
      · exact Or.inl h2
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩

/-- `pickBest acc x = none` only when the accumulator was already `none` AND `x` carries no address —
    `pickBest` never discards an address. -/
theorem pickBest_eq_none {acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32)} {x : VeriDNS.Spec.SlistEntry}
    (h : VeriDNS.Impl.SList.DnsSList.pickBest acc x = none) : acc = none ∧ x.address = none := by
  unfold VeriDNS.Impl.SList.DnsSList.pickBest at h
  split at h
  · next heq => exact ⟨h, heq⟩
  · next addr heq =>
    repeat' split at h
    all_goals simp at h

/-- A `foldl pickBest` returning `none` forces the seed `none` and an address-free server list. -/
theorem foldl_pickBest_eq_none (l : List VeriDNS.Spec.SlistEntry)
    (acc : Option (VeriDNS.Spec.SlistEntry × BitVec 32))
    (h : l.foldl VeriDNS.Impl.SList.DnsSList.pickBest acc = none) :
    acc = none ∧ ∀ e ∈ l, e.address = none := by
  induction l generalizing acc with
  | nil => exact ⟨by simpa using h, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨hpb, hxs⟩ := ih _ h
    obtain ⟨hacc, hxaddr⟩ := pickBest_eq_none hpb
    refine ⟨hacc, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hxaddr
    · exact hxs e he'

/-- **Glueless precondition: no addressed server ⟹ empty model SLIST.** When `bestWithAddress = none` (the
    impl has NS names but no glue addresses — the `gluelessNs` branch resolves an NS address separately),
    every SLIST entry is address-free, so `modelSlistOf s = []`. This is the `Or.inr (modelSlistOf … = [])`
    witness the strengthened driver conclusion's `Perm`-clause disjunction takes in the glueless case. -/
theorem modelSlistOf_nil_of_bestWithAddress_none (s : VeriDNS.Impl.SList.DnsSList)
    (h : s.bestWithAddress = none) : modelSlistOf s = [] := by
  unfold VeriDNS.Impl.SList.DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  obtain ⟨-, haddr⟩ := foldl_pickBest_eq_none s.servers.toList none h
  unfold modelSlistOf
  rw [List.filterMap_eq_nil_iff]
  intro e he
  rw [haddr e he]; rfl

/-- **`bestWithAddress`'s address is in the model SLIST.** The server the resolver actually queries (the
    lowest-transmission addressed entry) maps to a member of `modelSlistOf` — so the answer/referral
    terminals can present `byteAddrToModel (ipv4ToAddr addr) :: rest` as a *permutation* of the model SLIST
    (`List.perm_cons_erase`), discharging the strengthened conclusion's `Perm` clause. -/
theorem bestWithAddress_mem_modelSlistOf (s : VeriDNS.Impl.SList.DnsSList)
    {e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32}
    (h : s.bestWithAddress = some (e, addr)) :
    byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr addr) ∈ modelSlistOf s := by
  unfold VeriDNS.Impl.SList.DnsSList.bestWithAddress at h
  rw [← Array.foldl_toList] at h
  rcases foldl_pickBest_some _ none h with h1 | ⟨hmem, haddr⟩
  · exact absurd h1 (by simp)
  · unfold modelSlistOf
    rw [List.mem_filterMap]
    exact ⟨e, hmem, by simp [haddr]⟩

/-- **An addressed server ⟹ non-empty model SLIST** (the complement of `modelSlistOf_nil_of_bestWithAddress_
    none`). When `bestWithAddress = some …` (an addressed server exists — the answer/referral/cname branches),
    `modelSlistOf s ≠ []`, so the strengthened driver conclusion takes the `Or.inl` (`Perm`) disjunct. The
    refer case needs this to pick `Or.inl` from `glue ≠ []`. -/
theorem modelSlistOf_ne_nil_of_bestWithAddress_some (s : VeriDNS.Impl.SList.DnsSList)
    {e : VeriDNS.Spec.SlistEntry} {addr : BitVec 32} (h : s.bestWithAddress = some (e, addr)) :
    modelSlistOf s ≠ [] :=
  List.ne_nil_of_mem (bestWithAddress_mem_modelSlistOf s h)

def αRRType (bytes : ByteArray) : Option RRType :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
  | some rr => αType (VeriDNS.Spec.RRParse.rrType rr)
  | none => none

theorem hasRRTypeIn_corr (rrs : Array ByteArray) (code : BitVec 16) (rt : RRType)
    (hc : αType code = some rt) :
    Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) rrs code = true
      ↔ ∃ b ∈ rrs, αRRType b = some rt := by
  unfold Resolver.hasRRTypeIn αRRType
  constructor
  · intro h
    obtain ⟨i, hi, hcond⟩ := Array.any_eq_true.mp h
    refine ⟨rrs[i], Array.getElem_mem hi, ?_⟩
    revert hcond
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rrs[i] with
    | none => intro hcond; exact absurd hcond (by simp)
    | some rr =>
      intro hcond
      have heq : VeriDNS.Spec.RRParse.rrType rr = code := by simpa using hcond
      simp only [heq, hc]
  · rintro ⟨b, hbmem, hcond⟩
    obtain ⟨i, hi, hib⟩ := Array.getElem_of_mem hbmem
    subst hib
    apply Array.any_eq_true.mpr
    refine ⟨i, hi, ?_⟩
    revert hcond
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) rrs[i] with
    | none => intro hcond; exact absurd hcond (by simp)
    | some rr =>
      intro hcond
      have heq : VeriDNS.Spec.RRParse.rrType rr = code := αType_injective hcond hc
      simp [heq]

theorem answersQueryB_corr (resp : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qt : RRType)
    (hq : resp.question[0]? = some qu) (hqt : αType qu.qtype = some qt) :
    Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true
      ↔ ∃ b ∈ resp.answer, αRRType b = some qt := by
  unfold Resolver.answersQueryB
  rw [hq]
  exact hasRRTypeIn_corr resp.answer qu.qtype qt hqt

theorem delegationShapedB_authority_has_ns (resp : VeriDNS.Spec.Format)
    (h : Server.delegationShapedB resp = true) :
    ∃ b ∈ resp.authority, αRRType b = some RRType.ns := by
  unfold Server.delegationShapedB at h
  simp only [Bool.and_eq_true] at h
  exact (hasRRTypeIn_corr resp.authority 2 RRType.ns (by rfl)).mp h.1.1.1

open VeriDNS.Spec.Net (Time)

def αTime (t : UInt32) : Time := t.toNat

theorem fresh_corr (e : Cache.CacheEntry) (now : UInt32)
    (insertedAt ttl : Time) (h : e.expiry.toNat = insertedAt + ttl) :
    e.fresh now = Nat.blt (αTime now) (insertedAt + ttl) := by
  unfold Cache.CacheEntry.fresh αTime
  rw [← h, Bool.eq_iff_iff]
  simp [UInt32.lt_iff_toNat_lt, Nat.blt_eq]

theorem agedTtl_corr (e : Cache.CacheEntry) (now : UInt32)
    (insertedAt ttl : Nat) (hexp : e.expiry.toNat = insertedAt + ttl)
    (hfresh : e.fresh now = true) (hins : insertedAt ≤ now.toNat) :
    (e.expiry - now).toNat = ttl - (now.toNat - insertedAt) := by
  have hlt : now < e.expiry := by
    have hb := hfresh; unfold Cache.CacheEntry.fresh at hb; simpa using hb
  have hle : now ≤ e.expiry := UInt32.le_of_lt hlt
  rw [UInt32.toNat_sub_of_le e.expiry now hle, hexp]
  omega

def αCacheRR (e : Cache.CacheEntry) : Option VeriDNS.Spec.Net.CacheRR :=
  (αRR e.rr).map fun r =>
    { rr := r, insertedAt := e.expiry.toNat - e.rr.ttl.toNat, cred := αCred e.credibility }

/-- The abstracted cache entry's **record** is the bare record abstraction (`αRR e.rr`). Foundational for
    the Phase-3 `hcorr` correspondence: it relates the impl's pushed bailiwick entries to the model
    `absorb`'s answer/authority/additional records. -/
theorem αCacheRR_rr {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR} (h : αCacheRR e = some ce) :
    αRR e.rr = some ce.rr := by
  unfold αCacheRR at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, hce⟩ := h
  rw [← hce]; exact hr

/-- **The abstracted entry's model expiry recovers the impl entry's expiry.** `αCacheRR` sets `insertedAt =
    expiry − ttl` and (via `αRR`) `ttl = rr.ttl.toNat`, so `insertedAt + ttl = expiry.toNat` under no underflow
    (`CacheWf`'s sane-ttl clause). The bridge that lets `ModelOneExpiry` (one model-expiry per key) descend from the
    impl `OneExpiryPerKey` (one impl-expiry per key). -/
theorem αCacheRR_expiry {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR} (hα : αCacheRR e = some ce)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat) :
    ce.insertedAt + ce.rr.ttl = e.expiry.toNat := by
  have hrttl : ce.rr.ttl = e.rr.ttl.toNat := (αRR_fields e.rr ce.rr (αCacheRR_rr hα)).2.1
  unfold αCacheRR at hα
  rw [Option.map_eq_some_iff] at hα
  obtain ⟨r, hr, hceeq⟩ := hα
  have hins : ce.insertedAt = e.expiry.toNat - e.rr.ttl.toNat := by rw [← hceeq]
  rw [hins, hrttl, Nat.sub_add_cancel hle]

/-- The abstracted cache entry's **credibility** is `αCred` of the stored credibility — the per-key-max
    (`topServed`) side of the `hcorr` correspondence (the model `absorb` assigns `ansCred`/`authCred`/`glue`
    matching the impl `credAnswer`/`credAuthority`/`credAdditional` under `αCred`). -/
theorem αCacheRR_cred {e : Cache.CacheEntry} {ce : VeriDNS.Spec.Net.CacheRR} (h : αCacheRR e = some ce) :
    ce.cred = αCred e.credibility := by
  unfold αCacheRR at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, hce⟩ := h
  rw [← hce]

/-- **Per-record push correspondence (the atom of the Phase-3 `extra ~ N` structural match).** Abstracting
    the exact entry the impl `store` pushes — `⟨rr, now + ttl, false, cred⟩` (from `store_push_records`) —
    yields precisely the model `CacheRR` that `Cache.insert now (αCred cred) (αRR rr)` prepends:
    `⟨r, now.toNat, αCred cred⟩`. The `insertedAt` aligns because `(now+ttl).toNat - ttl = now.toNat` under the
    no-overflow hypothesis `hno` (dischargeable from the TTL cap, see `Proof/TtlCap.lean`), and the credibility
    via `αCred`. This is what lifts the section-filter list equality `αSection_bailiwickRaws_eq` to a
    `CacheRR`-level correspondence between the impl's pushed `extra` and the model `absorb`'s inserted `N`. -/
theorem αCacheRR_push (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (now : UInt32) (cred : VeriDNS.Spec.Trustworthiness)
    (hr : αRR rr = some r)
    (hno : (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩
      = some ⟨r, now.toNat, αCred cred⟩ := by
  unfold αCacheRR
  rw [hr, Option.map_some]
  congr 1
  rw [hno]
  simp

/-- **`cacheable` alignment — impl and model drop the SAME records.** For an abstracting record, the model's
    cacheability gate `cacheable r = (0 < r.ttl)` equals the negation of the impl's zero-TTL skip
    `rr.ttl == 0`. Both `DnsCache.storeChecked` (impl, `if rr.ttl == 0 then c else …`) and `Cache.insert`
    (model, `if cacheable r then …`) therefore drop exactly the `ttl=0` records — so the refer-path `extra`
    (impl `cacheRRs`→`storeChecked` pushes) and `N` (model `absorb`→`insert`) agree on which records are
    kept, with no `ttl=0` surplus on either side. (The earlier `not_fresh_of_ttl_zero` wash-out is thus a
    backstop, not needed on the refer path: the impl never even pushes a `ttl=0` referral record.) -/
theorem cacheable_corr {rr : VeriDNS.Spec.ResourceRecord} {r : VeriDNS.Spec.Net.RR}
    (h : αRR rr = some r) :
    VeriDNS.Spec.Net.cacheable r = !(rr.ttl == 0) := by
  have htt : r.ttl = rr.ttl.toNat := (αRR_fields rr r h).2.1
  have hz : (rr.ttl.toNat = 0) ↔ (rr.ttl = 0) := by
    constructor
    · intro hh; exact BitVec.toNat_inj.mp (by rw [hh]; rfl)
    · intro hh; rw [hh]; rfl
  unfold VeriDNS.Spec.Net.cacheable
  rw [htt]
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.blt_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, ← hz]
  omega

/-- **Abstracting the concrete `extra`.** `filterMap αCacheRR` commutes past the `flatMap pushOf` of
    `foldl_storeChecked_concrete`: the abstracted impl-pushed records are exactly the per-raw `αCacheRR` of the
    cacheable parse (parse-fail/`ttl=0` drop to `none`). Composing this with `foldl_storeChecked_concrete`
    gives the concrete abstracted `extra` — `(αCache (cacheRRs c raws cred now)).pos = (αCache c).pos ++
    raws.toList.filterMap (parse → cacheable → αCacheRR entry)` — the list the bridge's `extra ~ N` Perm
    consumes. Instance-free (pure list manipulation), so it sidesteps the `acceptRrset`/`storeChecked`
    projection-defeq plumbing. -/
theorem flatMap_pushOf_filterMap (l : List ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    (l.flatMap (pushOf cred now)).filterMap αCacheRR
      = l.filterMap (fun b =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
          | some rr => if rr.ttl == 0 then none else αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩
          | none => none) := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih, List.filterMap_cons]
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => rw [pushOf_none cred now hpr]; simp only [hpr, List.filterMap_nil, List.nil_append]
    | some rr =>
      by_cases htt : (rr.ttl == 0) = true
      · rw [pushOf_zero cred now hpr htt]
        simp only [hpr, htt, if_true, List.filterMap_nil, List.nil_append]
      · have htf : (rr.ttl == 0) = false := by simpa using htt
        rw [pushOf_pos cred now hpr htf]
        simp only [hpr, htf, Bool.false_eq_true, if_false]
        cases hac : αCacheRR ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ with
        | none => simp only [hac, List.filterMap_cons, List.filterMap_nil, List.nil_append]
        | some ce => simp only [hac, List.filterMap_cons, List.filterMap_nil, List.cons_append,
            List.nil_append]

theorem αCacheRR_fresh (e : Cache.CacheEntry) (r : VeriDNS.Spec.Net.CacheRR) (now : UInt32)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (h : αCacheRR e = some r) : e.fresh now = r.fresh now.toNat := by
  unfold αCacheRR at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r', hrr, rfl⟩ := h
  have hfields := αRR_fields e.rr r' hrr
  have hexp : e.expiry.toNat = (e.expiry.toNat - e.rr.ttl.toNat) + e.rr.ttl.toNat := by omega
  rw [fresh_corr e now (e.expiry.toNat - e.rr.ttl.toNat) e.rr.ttl.toNat hexp]
  simp only [αTime, VeriDNS.Spec.Net.CacheRR.fresh, hfields.2.1]

/-- `αRR` ignores the TTL field (it only reads name/rdata/class), carrying the new TTL through. -/
theorem αRR_setTtl (rr : VeriDNS.Spec.ResourceRecord) (X : BitVec 32) :
    αRR { rr with ttl := X }
      = (αRR rr).map (fun r => { r with ttl := X.toNat }) := by
  unfold αRR
  cases h : αName rr.name <;> cases h2 : αRData rr.type rr.rdata <;> cases h3 : αClass rr.class <;>
    simp [h, h2, h3]

/-- **Aged-record value correspondence.** The impl's TTL-aged served record (`{e.rr with ttl :=
    e.expiry - now}`) abstracts to the model's TTL-aged served record (`{a.rr with ttl := a.rr.ttl -
    (now - a.insertedAt)}`) — the produced-value half of `hhit`/`Cache.hit`. -/
theorem αRR_aged (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR) (now : UInt32)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat) (hfresh : e.fresh now = true)
    (hmono : e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (ha : αCacheRR e = some a) :
    αRR { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
      = some { a.rr with ttl := a.rr.ttl - (now.toNat - a.insertedAt) } := by
  unfold αCacheRR at ha
  rw [Option.map_eq_some_iff] at ha
  obtain ⟨r, hr, rfl⟩ := ha
  have hf := αRR_fields e.rr r hr
  have hins : e.expiry.toNat = (e.expiry.toNat - e.rr.ttl.toNat) + e.rr.ttl.toNat :=
    (Nat.sub_add_cancel hle).symm
  have haged := agedTtl_corr e now (e.expiry.toNat - e.rr.ttl.toNat) e.rr.ttl.toNat hins hfresh hmono
  have hb : (BitVec.ofNat 32 (e.expiry - now).toNat).toNat = (e.expiry - now).toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (UInt32.toNat_lt _)
  rw [αRR_setTtl, hr, Option.map_some, hb, haged, hf.2.1]

/-- **Local answerable↔matching correspondence (the last local piece of `hhit`).** An impl
    `answerableEntry` (fresh, name/type/class match, below the trustworthiness floor) abstracts to a
    model entry satisfying `Cache.matching`'s predicate (fresh, name match, qtype covers, class) and
    `Cred.usable`. So the impl's per-entry answerability gate *is* the model's `matching ∩ usable`
    gate. Composes the name (`αName_of_nameEqCI`), type (`αRR_rtype`), class (`αRR_fields`),
    freshness (`αCacheRR_fresh`) and credibility (`αCred_usable`) correspondences. -/
theorem answerableEntry_matching (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (hans : Cache.answerableEntry e name qt qc now = true)
    (ha : αCacheRR e = some a) :
    a.fresh (αTime now) = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true
      ∧ q.qtype.covers a.rr.rtype = true ∧ (a.rr.cls == q.qclass) = true
      ∧ a.cred.usable = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hcr : a.cred = αCred e.credibility := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; rfl
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.answerableEntry Cache.liveEntry at hans
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hans
  obtain ⟨⟨⟨⟨hnm, htype⟩, hcls⟩, hfr⟩, hcred⟩ := hans
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show αTime now = now.toNat from rfl, ← αCacheRR_fresh e a now hle ha]; exact hfr
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm hqn
    rw [hfields.1] at hna; injection hna with hna; subst hna; exact hne
  · have htypeq : e.rr.type = qt := eq_of_beq htype
    have hrtt0 : αType e.rr.type = some t := by rw [htypeq]; exact ht
    rw [hrt] at hrtt0
    have hrtt : a.rr.rdata.rtype = t := by injection hrtt0
    rw [hqq]
    show (VeriDNS.Spec.Net.QType.rr t).covers a.rr.rdata.rtype = true
    rw [hrtt]
    cases t <;> rfl
  · have hclseq : e.rr.class = qc := eq_of_beq hcls
    have hcc : αClass e.rr.class = some q.qclass := by rw [hclseq]; exact hqc
    rw [hfields.2.2] at hcc; injection hcc with hcc
    rw [hcc]; cases q.qclass <;> rfl
  · rw [hcr, αCred_usable]; exact decide_eq_true hcred

/-- **`liveEntry`↔`matching` correspondence (the SLIST-read analogue of `answerableEntry_matching`).** A live
    impl cache entry `e` matching the query, abstracting to model `a`, gives that `a` satisfies `Cache.matching`'s
    predicate (fresh, `nameEq` owner, qtype covers, class) — WITHOUT the `usable` clause (SLIST building uses
    `topServed`/`matching`, not the answerable `usable` gate). The grounding for `maxRankForKey ↔ topServed`. -/
theorem liveEntry_matching (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (hlive : Cache.liveEntry e name qt qc now = true)
    (ha : αCacheRR e = some a) :
    a.fresh (αTime now) = true ∧ VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true
      ∧ q.qtype.covers a.rr.rtype = true ∧ (a.rr.cls == q.qclass) = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.liveEntry at hlive
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlive
  obtain ⟨⟨⟨hnm, htype⟩, hcls⟩, hfr⟩ := hlive
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show αTime now = now.toNat from rfl, ← αCacheRR_fresh e a now hle ha]; exact hfr
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm hqn
    rw [hfields.1] at hna; injection hna with hna; subst hna; exact hne
  · have htypeq : e.rr.type = qt := eq_of_beq htype
    have hrtt0 : αType e.rr.type = some t := by rw [htypeq]; exact ht
    rw [hrt] at hrtt0
    have hrtt : a.rr.rdata.rtype = t := by injection hrtt0
    rw [hqq]
    show (VeriDNS.Spec.Net.QType.rr t).covers a.rr.rdata.rtype = true
    rw [hrtt]
    cases t <;> rfl
  · have hclseq : e.rr.class = qc := eq_of_beq hcls
    have hcc : αClass e.rr.class = some q.qclass := by rw [hclseq]; exact hqc
    rw [hfields.2.2] at hcc; injection hcc with hcc
    rw [hcc]; cases q.qclass <;> rfl

/-- **Reverse local answerable↔matching correspondence (the COMPLETENESS-direction converse of
    `answerableEntry_matching`).** A model cache entry `a` satisfying `Cache.matching`'s predicate
    (fresh, `nameEq` owner, qtype covers, class) *and* `Cred.usable`, whose stored impl source `e`
    abstracts to it (`αCacheRR e = some a`), is itself an impl `answerableEntry`. This is the piece
    needed for `hit ⊆ lookupAnswerable` (so the resolver serves *everything* the model would, not just
    a subset). Unlike the forward direction it requires the **canonicity** of the wire names (`e.rr.name`
    and `name` are the literal `labelsToWireFormatGo` encodings of their abstractions, with ≤63-byte
    labels — the `WfRR` cache invariant): the reverse name correspondence `nameEqCI_of_αName_canonical`
    is false for non-canonical names (`αName` ignores post-null trailing bytes that `nameEqCI` folds).
    Composes `nameEqCI_of_αName_canonical` (name), `eq_of_αType_beq`+`αType_injective` (type),
    `eq_of_αClass_beq`+`αClass_inj` (class), `αCacheRR_fresh` (freshness) and `αCred_usable`
    (credibility). -/
theorem matching_answerableEntry (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (ha : αCacheRR e = some a)
    (hcanE : e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname)
    (hvE : ∀ x ∈ a.rr.owner, x.size ≤ 63) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hfr : a.fresh (αTime now) = true)
    (hnm : VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
    (hcov : q.qtype.covers a.rr.rtype = true)
    (hcls : (a.rr.cls == q.qclass) = true)
    (hu : a.cred.usable = true) :
    Cache.answerableEntry e name qt qc now = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hcr : a.cred = αCred e.credibility := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; rfl
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.answerableEntry Cache.liveEntry
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN
  · rw [hqq] at hcov
    have hbeq : (t == a.rr.rtype) = true := hcov
    have heqt : t = a.rr.rdata.rtype := eq_of_αType_beq ht hrt hbeq
    have hqte : qt = e.rr.type := αType_injective ht (by rw [hrt, heqt])
    rw [hqte]; exact beq_self_eq_true _
  · have heqc : a.rr.cls = q.qclass := eq_of_αClass_beq hfields.2.2 hqc hcls
    have hqce : qc = e.rr.class := αClass_inj hqc (by rw [hfields.2.2, heqc])
    rw [hqce]; exact beq_self_eq_true _
  · rw [αCacheRR_fresh e a now hle ha]
    rwa [show αTime now = now.toNat from rfl] at hfr
  · rw [hcr, αCred_usable] at hu; exact hu

/-- **Reverse `matching`→`liveEntry` correspondence (SLIST analogue of `matching_answerableEntry`, minus
    `usable`).** A model record `a` satisfying `Cache.matching`'s predicate, whose impl source `e` abstracts to
    it, is an impl `liveEntry` for the query. The reverse predicate half of the `lookupTopCred ↔ topServed`
    per-element gate equality (`cond_eq_top`). -/
theorem matching_liveEntry (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hle : e.rr.ttl.toNat ≤ e.expiry.toNat)
    (ha : αCacheRR e = some a)
    (hcanE : e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname)
    (hvE : ∀ x ∈ a.rr.owner, x.size ≤ 63) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hfr : a.fresh (αTime now) = true)
    (hnm : VeriDNS.Spec.Net.nameEq a.rr.owner q.qname = true)
    (hcov : q.qtype.covers a.rr.rtype = true)
    (hcls : (a.rr.cls == q.qclass) = true) :
    Cache.liveEntry e name qt qc now = true := by
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
    obtain ⟨r, hr, rfl⟩ := ha; exact hr
  have hfields := αRR_fields e.rr a.rr harr
  have hrt := αRR_rtype e.rr a.rr harr
  unfold Cache.liveEntry
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN
  · rw [hqq] at hcov
    have hbeq : (t == a.rr.rtype) = true := hcov
    have heqt : t = a.rr.rdata.rtype := eq_of_αType_beq ht hrt hbeq
    have hqte : qt = e.rr.type := αType_injective ht (by rw [hrt, heqt])
    rw [hqte]; exact beq_self_eq_true _
  · have heqc : a.rr.cls = q.qclass := eq_of_αClass_beq hfields.2.2 hqc hcls
    have hqce : qc = e.rr.class := αClass_inj hqc (by rw [hfields.2.2, heqc])
    rw [hqce]; exact beq_self_eq_true _
  · rw [αCacheRR_fresh e a now hle ha]
    rwa [show αTime now = now.toNat from rfl] at hfr

/-- `==` is reflexive on `RRType` — needed because `RRType` is `deriving BEq` without `LawfulBEq`, so
    the generic `beq_self_eq_true` (which wants `ReflBEq`) is unavailable; a 62-way case split gives it
    directly. -/
theorem rrtype_beq_self (x : RRType) : (x == x) = true := by cases x <;> rfl

/-- `==` is reflexive on `RRClass` (the class analogue of `rrtype_beq_self`). -/
theorem rrclass_beq_self (x : RRClass) : (x == x) = true := by cases x <;> rfl

/-- **Same-RRset-key correspondence (forward).** The impl's `sameRRKey` (owner case-insensitively
    equal, type and class `==`-equal) implies the model's `CacheRR.sameKey` on the abstractions. The
    per-RRset-key grouping the impl uses for its `maxCredForKey` gate coincides with the model's
    `sameKey` grouping in `Cache.served`'s per-key maximality — the bridge that lets the
    `maxCredForKey ↔ served`-maximality reconciliation (the last step of `hhit` completeness) transport
    the impl's credibility comparison into the model's `Cred.rank` comparison via `αCred_order_used`.
    Forward only (no canonicity): owner uses `αName_of_nameEqCI`, type/class use the lawful BitVec
    `eq_of_beq` then `αRR_rtype`/`αRR_fields`. -/
theorem αRR_sameKey (e2 e : Cache.CacheEntry) (a2 a : VeriDNS.Spec.Net.CacheRR)
    (h2 : αCacheRR e2 = some a2) (ha : αCacheRR e = some a)
    (h : Cache.sameRRKey e2 e = true) :
    a2.sameKey a.rr = true := by
  have harr2 : αRR e2.rr = some a2.rr := by
    unfold αCacheRR at h2; rw [Option.map_eq_some_iff] at h2; obtain ⟨r, hr, rfl⟩ := h2; exact hr
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha; obtain ⟨r, hr, rfl⟩ := ha; exact hr
  unfold Cache.sameRRKey at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold VeriDNS.Spec.Net.CacheRR.sameKey
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm (αRR_fields e.rr a.rr harr).1
    rw [(αRR_fields e2.rr a2.rr harr2).1] at hna; injection hna with hna; subst hna; exact hne
  · have ht2 : e2.rr.type = e.rr.type := eq_of_beq htype
    have hx := αRR_rtype e2.rr a2.rr harr2
    rw [ht2, αRR_rtype e.rr a.rr harr] at hx
    injection hx with hx
    show (a2.rr.rdata.rtype == a.rr.rdata.rtype) = true
    rw [← hx]; exact rrtype_beq_self _
  · have hc2 : e2.rr.class = e.rr.class := eq_of_beq hcls
    have hx := (αRR_fields e2.rr a2.rr harr2).2.2
    rw [hc2, (αRR_fields e.rr a.rr harr).2.2] at hx
    injection hx with hx
    rw [← hx]; exact rrclass_beq_self _

/-- **Same-RRset-key correspondence (reverse, under canonicity).** The converse of `αRR_sameKey`: the
    model's `CacheRR.sameKey` on the abstractions implies the impl's `sameRRKey` on the canonical
    sources. Needed for the *forward* `maxCredForKey ⟹ served`-maximality reconciliation (the direction
    that, in the `hhit` *list* equality, shows a record the impl's max-cred gate *rejects* is one the
    model's per-key maximality also rejects). The name part requires canonicity
    (`nameEqCI_of_αName_canonical`); type/class use the image-restricted `eq_of_αType_beq` /
    `eq_of_αClass_beq` then `αType_injective` / `αClass_inj`. Together with `αRR_sameKey` this gives the
    *bidirectional* RRset-key correspondence the per-element option equality of `hhit` rests on. -/
theorem sameKey_sameRRKey (e2 e : Cache.CacheEntry) (a2 a : VeriDNS.Spec.Net.CacheRR)
    (h2 : αCacheRR e2 = some a2) (ha : αCacheRR e = some a)
    (hcan2 : e2.rr.name = DomainName.labelsToWireFormatGo a2.rr.owner)
    (hcanE : e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner)
    (hv2 : ∀ x ∈ a2.rr.owner, x.size ≤ 63) (hvE : ∀ x ∈ a.rr.owner, x.size ≤ 63)
    (h : a2.sameKey a.rr = true) :
    Cache.sameRRKey e2 e = true := by
  have harr2 : αRR e2.rr = some a2.rr := by
    unfold αCacheRR at h2; rw [Option.map_eq_some_iff] at h2; obtain ⟨r, hr, rfl⟩ := h2; exact hr
  have harr : αRR e.rr = some a.rr := by
    unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha; obtain ⟨r, hr, rfl⟩ := ha; exact hr
  unfold VeriDNS.Spec.Net.CacheRR.sameKey at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold Cache.sameRRKey
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcan2 hcanE hv2 hvE
  · have heqt : a2.rr.rdata.rtype = a.rr.rdata.rtype :=
      eq_of_αType_beq (αRR_rtype e2.rr a2.rr harr2) (αRR_rtype e.rr a.rr harr) htype
    have hte := αType_injective (αRR_rtype e2.rr a2.rr harr2)
      (by rw [αRR_rtype e.rr a.rr harr, ← heqt] : αType e.rr.type = some a2.rr.rdata.rtype)
    rw [hte]; exact beq_self_eq_true _
  · have heqc : a2.rr.cls = a.rr.cls :=
      eq_of_αClass_beq (αRR_fields e2.rr a2.rr harr2).2.2 (αRR_fields e.rr a.rr harr).2.2 hcls
    have hce := αClass_inj (αRR_fields e2.rr a2.rr harr2).2.2
      (by rw [(αRR_fields e.rr a.rr harr).2.2, ← heqc] : αClass e.rr.class = some a2.rr.cls)
    rw [hce]; exact beq_self_eq_true _

/-! ### RRset TTL-normalization correspondence (`αSection (normRaws R) = normalizeTTL (αSection R)`)

    The keystone that lets the impl's re-serialized min-TTL section (`Cache.normRaws`) refine the model's
    normalized `absorb` section (`Net.normalizeTTL`): abstracting the impl-normalized section equals
    model-normalizing the abstracted section. Both apply the same per-key minimum, and the impl/model
    keys + TTLs correspond through `αRR`. Requires α-mappability (`hval`) so no record is dropped
    (dropping one would let it perturb only one side's per-key minimum). -/

/-- `αRR` changes only `ttl` under a `ttl` update (mappability is owner/rdata/class-determined). -/
theorem αRR_set_ttl (rr : VeriDNS.Spec.ResourceRecord) (t : BitVec 32) :
    αRR { rr with ttl := t } = (αRR rr).map (fun mr => { mr with ttl := t.toNat }) := by
  unfold αRR
  cases hn : αName rr.name <;> cases hrd : αRData rr.type rr.rdata <;> cases hcl : αClass rr.class <;>
    simp [hn, hrd, hcl]

/-- **Key correspondence (forward).** The impl's `rrSameKeyB` implies the model's `rrKeyEq` on the
    abstractions (bare-RR analogue of `αRR_sameKey`). -/
theorem rrSameKeyB_rrKeyEq (a b : VeriDNS.Spec.ResourceRecord) (ma mb : VeriDNS.Spec.Net.RR)
    (hma : αRR a = some ma) (hmb : αRR b = some mb)
    (h : Cache.rrSameKeyB a b = true) : VeriDNS.Spec.Net.rrKeyEq ma mb = true := by
  unfold Cache.rrSameKeyB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold VeriDNS.Spec.Net.rrKeyEq
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨na, hna, hne⟩ := αName_of_nameEqCI hnm (αRR_fields b mb hmb).1
    rw [(αRR_fields a ma hma).1] at hna; injection hna with hna; subst hna; exact hne
  · have ht2 : a.type = b.type := eq_of_beq htype
    have hx := αRR_rtype a ma hma
    rw [ht2, αRR_rtype b mb hmb] at hx
    injection hx with hx
    show (ma.rdata.rtype == mb.rdata.rtype) = true
    rw [← hx]; exact rrtype_beq_self _
  · have hc2 : a.class = b.class := eq_of_beq hcls
    have hx := (αRR_fields a ma hma).2.2
    rw [hc2, (αRR_fields b mb hmb).2.2] at hx
    injection hx with hx
    show (ma.cls == mb.cls) = true
    rw [← hx]; exact rrclass_beq_self _

/-- **Key correspondence (reverse, under canonicity).** Model `rrKeyEq` on the abstractions implies impl
    `rrSameKeyB` on the canonical sources (bare-RR analogue of `sameKey_sameRRKey`). -/
theorem rrKeyEq_rrSameKeyB (a b : VeriDNS.Spec.ResourceRecord) (ma mb : VeriDNS.Spec.Net.RR)
    (hma : αRR a = some ma) (hmb : αRR b = some mb)
    (hcan_a : a.name = DomainName.labelsToWireFormatGo ma.owner)
    (hcan_b : b.name = DomainName.labelsToWireFormatGo mb.owner)
    (hv_a : ∀ x ∈ ma.owner, x.size ≤ 63) (hv_b : ∀ x ∈ mb.owner, x.size ≤ 63)
    (h : VeriDNS.Spec.Net.rrKeyEq ma mb = true) : Cache.rrSameKeyB a b = true := by
  unfold VeriDNS.Spec.Net.rrKeyEq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hnm, htype⟩, hcls⟩ := h
  unfold Cache.rrSameKeyB
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact nameEqCI_of_αName_canonical hnm hcan_a hcan_b hv_a hv_b
  · have heqt : ma.rdata.rtype = mb.rdata.rtype :=
      eq_of_αType_beq (αRR_rtype a ma hma) (αRR_rtype b mb hmb) htype
    have hte := αType_injective (αRR_rtype a ma hma)
      (by rw [αRR_rtype b mb hmb, ← heqt] : αType b.type = some ma.rdata.rtype)
    rw [hte]; exact beq_self_eq_true _
  · have heqc : ma.cls = mb.cls :=
      eq_of_αClass_beq (αRR_fields a ma hma).2.2 (αRR_fields b mb hmb).2.2 hcls
    have hce := αClass_inj (αRR_fields a ma hma).2.2
      (by rw [(αRR_fields b mb hmb).2.2, ← heqc] : αClass b.class = some ma.cls)
    rw [hce]; exact beq_self_eq_true _

/-- Key correspondence as a `Bool` equality (both directions, under canonicity). -/
theorem rrSameKeyB_eq_rrKeyEq (a b : VeriDNS.Spec.ResourceRecord) (ma mb : VeriDNS.Spec.Net.RR)
    (hma : αRR a = some ma) (hmb : αRR b = some mb)
    (hcan_a : a.name = DomainName.labelsToWireFormatGo ma.owner)
    (hcan_b : b.name = DomainName.labelsToWireFormatGo mb.owner)
    (hv_a : ∀ x ∈ ma.owner, x.size ≤ 63) (hv_b : ∀ x ∈ mb.owner, x.size ≤ 63) :
    Cache.rrSameKeyB a b = VeriDNS.Spec.Net.rrKeyEq ma mb := by
  rw [Bool.eq_iff_iff]
  exact ⟨fun h => rrSameKeyB_rrKeyEq a b ma mb hma hmb h,
         fun h => rrKeyEq_rrSameKeyB a b ma mb hma hmb hcan_a hcan_b hv_a hv_b h⟩

theorem minTtlB_toNat_eq (x y : BitVec 32) : (Cache.minTtlB x y).toNat = min x.toNat y.toNat := by
  simp only [Cache.minTtlB]; split <;> omega

theorem filterMap_congr' {α β : Type} {L : List α} {f g : α → Option β}
    (h : ∀ a ∈ L, f a = g a) : L.filterMap f = L.filterMap g := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Canonical + α-mappable predicate for a parsed impl record (as `parseRaw_name_canonical` + `hval`
    supply it): the record abstracts, and its wire name is the canonical encoding of the model owner. -/
def RRCanonMappable (e : VeriDNS.Spec.ResourceRecord) : Prop :=
  ∃ me, αRR e = some me ∧ e.name = DomainName.labelsToWireFormatGo me.owner
    ∧ ∀ x ∈ me.owner, x.size ≤ 63

/-- **The group-min fold correspondence.** Impl `groupMinTtl` (per-key min over `L`, `BitVec`) and model
    `rrGroupMin` (per-key min over `L.filterMap αRR`, `Nat`) compute the same value through `αRR`, because
    keys + TTLs correspond and (under `RRCanonMappable`) no record is dropped. Seed-generalized for the
    induction. -/
theorem groupMin_fold_corr (r0 : VeriDNS.Spec.ResourceRecord) (mr : VeriDNS.Spec.Net.RR)
    (hr0 : αRR r0 = some mr) (hcan0 : r0.name = DomainName.labelsToWireFormatGo mr.owner)
    (hv0 : ∀ x ∈ mr.owner, x.size ≤ 63) :
    ∀ (L : List VeriDNS.Spec.ResourceRecord), (∀ e ∈ L, RRCanonMappable e) →
    ∀ (s : BitVec 32) (sm : Nat), s.toNat = sm →
    (L.foldl (fun acc e => if Cache.rrSameKeyB e r0 then Cache.minTtlB acc e.ttl else acc) s).toNat
      = (L.filterMap αRR).foldl
          (fun acc me => if VeriDNS.Spec.Net.rrKeyEq me mr then min acc me.ttl else acc) sm := by
  intro L
  induction L with
  | nil => intro _ s sm hs; simpa using hs
  | cons e L' ih =>
    intro hL s sm hs
    obtain ⟨me, hme, hcane, hve⟩ := hL e (List.mem_cons_self ..)
    rw [List.filterMap_cons, hme]
    simp only [List.foldl_cons]
    have hkey : Cache.rrSameKeyB e r0 = VeriDNS.Spec.Net.rrKeyEq me mr :=
      rrSameKeyB_eq_rrKeyEq e r0 me mr hme hr0 hcane hcan0 hve hv0
    have httl : e.ttl.toNat = me.ttl := ((αRR_fields e me hme).2.1).symm
    refine ih (fun x hx => hL x (List.mem_cons_of_mem e hx)) _ _ ?_
    rw [hkey]
    by_cases hk : VeriDNS.Spec.Net.rrKeyEq me mr = true
    · simp only [hk, if_true]; rw [minTtlB_toNat_eq, hs, httl]
    · simp only [hk, Bool.false_eq_true, if_false]; exact hs

/-- The per-record group-min correspondence (seeds resolved: `r0.ttl.toNat = mr.ttl`). -/
theorem groupMin_corr (L : List VeriDNS.Spec.ResourceRecord) (hL : ∀ e ∈ L, RRCanonMappable e)
    (r0 : VeriDNS.Spec.ResourceRecord) (mr : VeriDNS.Spec.Net.RR) (hr0 : αRR r0 = some mr)
    (hcan0 : r0.name = DomainName.labelsToWireFormatGo mr.owner) (hv0 : ∀ x ∈ mr.owner, x.size ≤ 63) :
    (Cache.groupMinTtl L r0).toNat = VeriDNS.Spec.Net.rrGroupMin (L.filterMap αRR) mr := by
  unfold Cache.groupMinTtl VeriDNS.Spec.Net.rrGroupMin
  exact groupMin_fold_corr r0 mr hr0 hcan0 hv0 L hL r0.ttl mr.ttl ((αRR_fields r0 mr hr0).2.1).symm

/-- General list bridge: `filterMap` of an option-map equals `map` of the `filterMap`, when the two
    per-element functions agree on every mapped element. -/
theorem filterMap_optionMap_eq {α β : Type} (L : List α) (f : α → Option β)
    (g : α → β → β) (h : β → β) (hyp : ∀ a ∈ L, ∀ b, f a = some b → g a b = h b) :
    L.filterMap (fun a => (f a).map (g a)) = (L.filterMap f).map h := by
  induction L with
  | nil => rfl
  | cons a L' ih =>
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => simp only [hfa, Option.map_none]; rw [List.filterMap_cons, hfa]; exact ih (fun x hx b hb => hyp x (List.mem_cons_of_mem a hx) b hb)
    | some b =>
      simp only [hfa, Option.map_some]
      rw [List.filterMap_cons, hfa, List.map_cons, hyp a (List.mem_cons_self ..) b hfa]
      exact congrArg _ (ih (fun x hx b hb => hyp x (List.mem_cons_of_mem a hx) b hb))

/-- **The crux.** Abstracting the impl's re-serialized min-TTL section equals model-normalizing the
    abstracted section — under `RRCanonMappable` on every parsed record. -/
theorem αSection_normRaws (R : Array ByteArray) (hwf : ∀ e ∈ Cache.rrsOf R, RRCanonMappable e) :
    αSection (Cache.normRaws R) = VeriDNS.Spec.Net.normalizeTTL (αSection R) := by
  have hαsec : αSection R = (Cache.rrsOf R).filterMap αRR := by
    unfold αSection Cache.rrsOf
    rw [List.filterMap_filterMap]
    congr 1
    funext b
    show (match (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
          | .ok (rr, _) => some rr | .error _ => none) with
        | some rr => αRR rr | none => none)
      = (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
          | .ok (rr, _) => some rr | .error _ => none).bind αRR
    cases DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
    | error e => rfl
    | ok v => obtain ⟨rr, pos⟩ := v; rfl
  -- WfRR for every parsed record (from `parseRaw`), lifted to the ttl-normalized image.
  have hround : ∀ r0 ∈ Cache.rrsOf R,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
          { r0 with ttl := Cache.groupMinTtl (Cache.rrsOf R) r0 })
        = some { r0 with ttl := Cache.groupMinTtl (Cache.rrsOf R) r0 } := by
    intro r0 hr0
    obtain ⟨b, _, hpb⟩ := List.mem_filterMap.mp hr0
    exact VeriDNS.Proof.NameTree.parseRaw_rrBytes_of_wf
      (VeriDNS.Proof.NameTree.wfRR_set_ttl (VeriDNS.Proof.NameTree.wfRR_of_parseRaw hpb) _)
  -- LHS reduces to a filterMap over rrsOf R.
  have hLHS : αSection (Cache.normRaws R)
      = (Cache.rrsOf R).filterMap (fun r0 => (αRR r0).map
          (fun mr => { mr with ttl := (Cache.groupMinTtl (Cache.rrsOf R) r0).toNat })) := by
    unfold αSection Cache.normRaws Cache.normalizeRRsetTtls
    rw [List.toList_toArray, List.map_map, List.filterMap_map]
    apply filterMap_congr'
    intro r0 hr0
    show (match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
          { r0 with ttl := Cache.groupMinTtl (Cache.rrsOf R) r0 }) with
        | some rr => αRR rr | none => none)
      = (αRR r0).map (fun mr => { mr with ttl := (Cache.groupMinTtl (Cache.rrsOf R) r0).toNat })
    rw [hround r0 hr0]; exact αRR_set_ttl r0 _
  rw [hLHS, hαsec]
  unfold VeriDNS.Spec.Net.normalizeTTL
  refine filterMap_optionMap_eq (Cache.rrsOf R) αRR _ _ ?_
  intro r0 hr0 mr hmr
  obtain ⟨me', hme', hc', hv'⟩ := hwf r0 hr0
  rw [hmr] at hme'; obtain rfl := Option.some.inj hme'
  have hgm := groupMin_corr (Cache.rrsOf R) hwf r0 mr hmr hc' hv'
  rw [hgm]

def αNegRR (e : Cache.NegativeEntry) : Option VeriDNS.Spec.Net.NegRR :=
  match αName e.name with
  | none => none
  | some n =>
    if e.rcode == VeriDNS.Spec.Rcode.nameError then
      some { qname := n, qtype := none, insertedAt := 0, ttl := e.expiry.toNat }
    else
      match αType e.qtype with
      | some t => some { qname := n, qtype := some (.rr t), insertedAt := 0, ttl := e.expiry.toNat }
      | none => none

def αCache (c : Cache.DnsCache) : VeriDNS.Spec.Net.Cache :=
  { pos := c.records.toList.filterMap αCacheRR
    neg := c.negatives.toList.filterMap αNegRR }

/-- **The cache abstraction is unchanged by `boundExpiryClasses` below capacity.** When the (just-absorbed)
    cache fits its 4096-entry capacity — true of any realistic referral resolution, since `store` deduplicates
    per key and a single hop adds only a referral's worth of records — `boundStateCache`'s `boundExpiryClasses`
    wrap is the identity, so the model image of the impl's `.continue` state cache (`afterResume_referral_continue_struct`)
    is EXACTLY the model `absorb` writes, with no eviction to reconcile in `StateModels_refer_preserve`. The
    over-capacity case (4096+ distinct live keys) is pathological and out of scope: there the bounded impl
    genuinely evicts a fresh entry the unbounded model keeps (a one-directional `served_impl ⊆ served_model`
    refinement would be the faithful general fix). This lemma discharges the reconciliation under the realistic
    capacity-headroom hypothesis. -/
theorem αCache_boundExpiryClasses_noop (c : Cache.DnsCache)
    (h : c.records.size ≤ Cache.DnsCache.capacity) :
    αCache c.boundExpiryClasses = αCache c := by
  rw [VeriDNS.Proof.Cache.boundExpiryClasses_noop c h]

/-- **`boundExpiryClasses` only removes records** (eviction is a filter), so the abstracted evicted cache is a
    SUB-cache of the original: every model `pos` entry of `αCache c.boundExpiryClasses` is one of `αCache c`. The
    one-directional refinement foundation for reconciling the impl's bounded cache with the model — the impl never
    invents a cache entry by evicting, so any model rule grounded in the evicted cache is grounded in the full one. -/
theorem αCache_boundExpiryClasses_pos_subset (c : Cache.DnsCache) {e : VeriDNS.Spec.Net.CacheRR}
    (he : e ∈ (αCache c.boundExpiryClasses).pos) : e ∈ (αCache c).pos := by
  simp only [αCache, List.mem_filterMap] at he ⊢
  obtain ⟨entry, hmem, hα⟩ := he
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at hmem
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at hmem
  exact ⟨entry, hmem.1, hα⟩

/-- **`filter` commutes with `filterMap`** when the source predicate `r` factors through `f` as an output
    predicate `q`. The engine for the eviction/`αCache` commutation: the impl's `evictClasses` is a `filter` by
    expiry (`evictClasses_filter_form`), and that expiry predicate factors through `αCacheRR` (which preserves
    `expiry = insertedAt + ttl`), so the abstracted evicted cache is the abstracted cache filtered by the
    corresponding model-side expiry predicate — i.e. a model expiry-class eviction. -/
theorem filterMap_filter_comm {α β : Type} (l : List α) (r : α → Bool) (f : α → Option β) (q : β → Bool)
    (h : ∀ x ∈ l, ∀ y, f x = some y → r x = q y) :
    (l.filter r).filterMap f = (l.filterMap f).filter q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [List.filter_cons]
    cases hf : f a with
    | none =>
      by_cases hr : r a = true
      · rw [if_pos hr, List.filterMap_cons, hf, List.filterMap_cons, hf, ih']
      · rw [if_neg hr, List.filterMap_cons, hf, ih']
    | some b =>
      have hqb : q b = r a := (h a (List.mem_cons_self ..) b hf).symm
      by_cases hr : r a = true
      · rw [if_pos hr, List.filterMap_cons, hf, List.filterMap_cons, hf, List.filter_cons,
          if_pos (by rw [hqb]; exact hr), ih']
      · rw [if_neg hr, List.filterMap_cons, hf, List.filter_cons,
          if_neg (by rw [hqb]; exact hr), ih']

/-- **The impl's `boundExpiryClasses` is a model expiry-class eviction under abstraction.** Since `evictClasses`
    is a filter by `expiry` (`evictClasses_filter_form`) and `αCacheRR` preserves `expiry = insertedAt + ttl`
    (`αRR` keeps `ttl`, and `CacheWf` gives no underflow), the abstracted evicted cache is the abstracted cache
    filtered by the corresponding model expiry predicate — so model-side eviction matches the impl exactly. -/
theorem αCache_boundExpiryClasses_pos_filter (c : Cache.DnsCache)
    (hwf : ∀ e ∈ c.records.toList, e.rr.ttl.toNat ≤ e.expiry.toNat) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      (αCache c.boundExpiryClasses).pos = (αCache c).pos.filter qf
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.insertedAt + ce₁.rr.ttl = ce₂.insertedAt + ce₂.rr.ttl → qf ce₁ = qf ce₂) := by
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  refine ⟨fun ce => p (UInt32.ofNat (ce.insertedAt + ce.rr.ttl)), ?_,
    fun ce₁ ce₂ hexp => by simp only [hexp]⟩
  show (c.boundExpiryClasses.records).toList.filterMap αCacheRR
      = ((c.records).toList.filterMap αCacheRR).filter _
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses
  rw [hp, Array.toList_filter]
  apply filterMap_filter_comm
  intro entry hentry ce hce
  have httl := hwf entry hentry
  unfold αCacheRR at hce
  rw [Option.map_eq_some_iff] at hce
  obtain ⟨r, hr, hceeq⟩ := hce
  have hrttl : r.ttl = entry.rr.ttl.toNat := by
    unfold αRR at hr
    split at hr
    · rw [← Option.some.inj hr]
    · simp at hr
  show p entry.expiry = p (UInt32.ofNat (ce.insertedAt + ce.rr.ttl))
  congr 1
  rw [← hceeq]
  show entry.expiry = UInt32.ofNat ((entry.expiry.toNat - entry.rr.ttl.toNat) + r.ttl)
  rw [hrttl, Nat.sub_add_cancel httl]
  simp

/-- **The impl's `boundExpiryClasses`, abstracted, is the model cache with its positives expiry-filtered and its
    negatives untouched.** The full-cache form of `αCache_boundExpiryClasses_pos_filter` (eviction touches only
    `records`, never `negatives`). This is exactly the model-side eviction the refer rule's recursive cache needs:
    `(c.absorb …)` filtered by `qf` matches the impl's `boundStateCache`-wrapped cache under abstraction. -/
theorem αCache_boundExpiryClasses_eq (c : Cache.DnsCache)
    (hwf : ∀ e ∈ c.records.toList, e.rr.ttl.toNat ≤ e.expiry.toNat) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      αCache c.boundExpiryClasses
        = { pos := (αCache c).pos.filter qf, neg := (αCache c).neg }
      ∧ (∀ ce₁ ce₂ : VeriDNS.Spec.Net.CacheRR,
          ce₁.insertedAt + ce₁.rr.ttl = ce₂.insertedAt + ce₂.rr.ttl → qf ce₁ = qf ce₂) := by
  obtain ⟨qf, hpos, hexp⟩ := αCache_boundExpiryClasses_pos_filter c hwf
  refine ⟨qf, ?_, hexp⟩
  have hneg : (αCache c.boundExpiryClasses).neg = (αCache c).neg := rfl
  cases hαbe : αCache c.boundExpiryClasses with
  | mk pos neg =>
    have hp : pos = (αCache c).pos.filter qf := by rw [← hpos, hαbe]
    have hn : neg = (αCache c).neg := by rw [← hneg, hαbe]
    rw [hp, hn]

/-- **The section write, abstracted to `αCache.pos` (the refer-hop write-path keystone).** A single
    `cacheRRs c raws cred now` write (one referral section) maps, under the abstraction, to appending the
    concrete pushed records: `(αCache (cacheRRs c raws cred now)).pos = (αCache c).pos ++ (raws.toList.flatMap
    pushOf).filterMap αCacheRR`. Composes `foldl_storeChecked_concrete` (concrete `extra`) with `αCache`'s
    `filterMap` over `toList` and `List.filterMap_append`. The `acceptRrset`→`storeChecked` instance-projection
    defeq barrier is crossed via `congr 1` + an inline `funext`/`cases`/`rfl` (which reduces the fold function
    equality to per-branch single applications, where the projection DOES reduce — unlike under `List.foldl`,
    where `rfl`/`exact`/`rw` all stall on the match-auxiliary). This is the in-context bridge the plan flagged;
    `flatMap_pushOf_filterMap` then rewrites the appended term to the per-raw `αCacheRR`-of-cacheable form. -/
theorem cacheRRs_αCache_pos (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) (c : Cache.DnsCache)
    (h : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord), b ∈ raws.toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (rr.ttl == 0) = false →
        (acc.storeChecked rr cred now).records
          = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩) :
    (αCache (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c raws cred now)).pos
      = (αCache c).pos ++ (raws.toList.flatMap (pushOf cred now)).filterMap αCacheRR := by
  have hrec : (Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c raws cred now).records.toList
      = c.records.toList ++ raws.toList.flatMap (pushOf cred now) := by
    have he : Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) c raws cred now
        = raws.toList.foldl (fun (acc : Cache.DnsCache) b =>
            match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
            | some rr => acc.storeChecked rr cred now | none => acc) c := by
      unfold Resolver.cacheRRs
      rw [array_foldl_toList]
      congr 1
      funext acc b
      cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => rfl
      | some rr => rfl
    rw [he]
    exact foldl_storeChecked_concrete cred now raws.toList c h
  unfold αCache
  rw [hrec, List.filterMap_append]

/-- `cacheUnlessTruncated` is `cacheRRs` when the response is not truncated (`htc`). The refer rule supplies
    this via its `tc = false` premise — a truncated referral is never cached. -/
theorem cacheUnlessTruncated_untruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (htc : (resp.header.tc == 1) = false) :
    Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache resp raws cred now
      = Resolver.cacheRRs (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache (Cache.normRaws raws) cred now := by
  unfold Resolver.cacheUnlessTruncated
  rw [htc]; rfl

/-- A `cacheUnlessTruncated` write leaves the negative cache untouched (both branches: truncated → `c`;
    untruncated → `cacheRRs`, which only mutates `records`). The impl-side input to the refer-hop
    `MatchMaxEquiv`'s negHit/negHitNx clauses: a referral write changes only positives, so the abstracted
    negatives — hence `negHit`/`negHitNx` — are preserved, matching the model `absorb` (`absorb_neg`). -/
theorem cacheUnlessTruncated_negatives (c : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    (Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now).negatives = c.negatives := by
  unfold Resolver.cacheUnlessTruncated
  split
  · rfl
  · exact cacheRRs_negatives _ cred now c

/-- **The two-section refer write, abstracted to `αCache.pos`.** The refer branch caches authority then
    additional via two `cacheUnlessTruncated` writes. Under untruncated (`htc`) and the per-section push
    hypotheses (`h1`, `h2`), composing `cacheRRs_αCache_pos` twice gives `(αCache cache'').pos = (αCache
    cache).pos ++ raws1-pushes ++ raws2-pushes` — the impl's full referral `extra` (both sections), abstracted,
    ready to match the model `absorb`'s `N`. This is the first composition the named `pushOf` unblocks: both
    `cacheRRs_αCache_pos` outputs and this conclusion share the one `pushOf` constant, so the rewrites land. -/
theorem two_section_αCache_pos (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws1 raws2 : Array ByteArray) (cred1 cred2 : VeriDNS.Spec.Trustworthiness) (now : UInt32)
    (htc : (resp.header.tc == 1) = false)
    (h1 : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (Cache.normRaws raws1).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr cred1 now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred1⟩)
    (h2 : ∀ (acc : Cache.DnsCache) (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord),
        b ∈ (Cache.normRaws raws2).toList →
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → (rr.ttl == 0) = false →
        (acc.storeChecked rr cred2 now).records = acc.records.push ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred2⟩) :
    (αCache (Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache resp raws1 cred1 now) resp raws2 cred2 now)).pos
      = (αCache cache).pos
        ++ ((Cache.normRaws raws1).toList.flatMap (pushOf cred1 now)).filterMap αCacheRR
        ++ ((Cache.normRaws raws2).toList.flatMap (pushOf cred2 now)).filterMap αCacheRR := by
  rw [cacheUnlessTruncated_untruncated _ _ _ _ _ htc, cacheUnlessTruncated_untruncated _ _ _ _ _ htc,
    cacheRRs_αCache_pos (Cache.normRaws raws2) cred2 now _ h2,
    cacheRRs_αCache_pos (Cache.normRaws raws1) cred1 now cache h1]

theorem mem_αCache_pos (c : Cache.DnsCache) (a : VeriDNS.Spec.Net.CacheRR)
    (h : a ∈ (αCache c).pos) : ∃ e ∈ c.records, αCacheRR e = some a := by
  unfold αCache at h
  simp only [List.mem_filterMap] at h
  obtain ⟨e, he, ha⟩ := h
  exact ⟨e, Array.mem_def.mpr he, ha⟩

/-- **`αCache` neg-grounding** (the negative-cache analogue of `mem_αCache_pos`): every negative
    entry of the abstracted cache is the abstraction of a real stored negative entry. A foundation
    lemma for the Step-3 `negHit` simulation branch (`resolveWithIO` negative-cache resolution ⊑
    `Net.Resolves.negHit`). -/
theorem mem_αCache_neg (c : Cache.DnsCache) (a : VeriDNS.Spec.Net.NegRR)
    (h : a ∈ (αCache c).neg) : ∃ e ∈ c.negatives, αNegRR e = some a := by
  unfold αCache at h
  simp only [List.mem_filterMap] at h
  obtain ⟨e, he, ha⟩ := h
  exact ⟨e, Array.mem_def.mpr he, ha⟩

/-- An abstracted negative entry has `insertedAt = 0` and `ttl = expiry` (both `αNegRR` branches). -/
theorem αNegRR_fields {e : Cache.NegativeEntry} {a : VeriDNS.Spec.Net.NegRR}
    (h : αNegRR e = some a) : a.insertedAt = 0 ∧ a.ttl = e.expiry.toNat := by
  unfold αNegRR at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · split at h
      · injection h with h; subst h; exact ⟨rfl, rfl⟩
      · exact absurd h (by simp)

/-- **negHit cache refinement (Step-3 `negHit` branch core).** A fresh stored impl negative entry
    that abstracts and matches the query forces the model's `Cache.negHit` to hold on `αCache c`. So
    the executable negative-cache hit is a `Net.Resolves.negHit` precondition — the impl negative
    cache refines the model's. -/
theorem αCache_negHit (c : Cache.DnsCache) (now : UInt32) (q : VeriDNS.Spec.Net.Query)
    (e : Cache.NegativeEntry) (a : VeriDNS.Spec.Net.NegRR)
    (he : e ∈ c.negatives) (hα : αNegRR e = some a) (hfresh : now < e.expiry)
    (hname : VeriDNS.Spec.Net.nameEq a.qname q.qname = true)
    (hqt : (match a.qtype with | none => true | some t => t == q.qtype) = true) :
    (αCache c).negHit (αTime now) q = true := by
  unfold VeriDNS.Spec.Net.Cache.negHit
  apply List.any_eq_true.mpr
  refine ⟨a, ?_, ?_⟩
  · unfold αCache
    simp only [List.mem_filterMap]
    exact ⟨e, Array.mem_def.mp he, hα⟩
  · simp only [Bool.and_eq_true]
    obtain ⟨h0, htt⟩ := αNegRR_fields hα
    refine ⟨⟨?_, hname⟩, hqt⟩
    unfold VeriDNS.Spec.Net.NegRR.fresh αTime
    rw [h0, htt, Nat.zero_add]
    exact Nat.blt_eq.mpr (UInt32.lt_iff_toNat_lt.mp hfresh)

/-- **negHit precondition (Step-3 `negHit` branch).** Inverting the impl negative lookup (the `<|>`
    of the NXDOMAIN and NODATA `findSome?`s): if `lookupNegative` succeeds for a specific-type query
    whose name/type abstract, the model's `Cache.negHit` holds on `αCache c`. So the executable
    negative-cache hit licenses `Net.Resolves.negHit`. -/
theorem lookupNegative_negHit (cache : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rc : VeriDNS.Spec.Rcode) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hlk : cache.lookupNegative name qt qc now = some rc)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) :
    (αCache cache).negHit (αTime now) q = true := by
  have rcodeEq : ∀ a : VeriDNS.Spec.Rcode,
      (a == VeriDNS.Spec.Rcode.nameError) = true → a = VeriDNS.Spec.Rcode.nameError := by
    intro a h; cases a <;> first | rfl | exact absurd h (by decide)
  have go : ∀ e ∈ cache.negatives,
      VeriDNS.Impl.DomainName.nameEqCI e.name name = true → now < e.expiry →
      (e.rcode = VeriDNS.Spec.Rcode.nameError ∨ e.qtype = qt) →
      (αCache cache).negHit (αTime now) q = true := by
    intro e hemem hname hfresh hkind
    obtain ⟨na, hna, hnameq⟩ := αName_of_nameEqCI hname hqn
    by_cases hnx : e.rcode = VeriDNS.Spec.Rcode.nameError
    · refine αCache_negHit cache now q e ⟨na, none, 0, e.expiry.toNat⟩ hemem ?_ hfresh hnameq rfl
      unfold αNegRR; rw [hna]; rw [hnx]; rfl
    · have heqt : e.qtype = qt := hkind.resolve_left hnx
      have hrcf : (e.rcode == VeriDNS.Spec.Rcode.nameError) = false := by
        cases hc : e.rcode == VeriDNS.Spec.Rcode.nameError
        · rfl
        · exact absurd (rcodeEq _ hc) hnx
      refine αCache_negHit cache now q e
        ⟨na, some (VeriDNS.Spec.Net.QType.rr t), 0, e.expiry.toNat⟩ hemem ?_ hfresh hnameq ?_
      · unfold αNegRR; rw [hna]; simp [hrcf, heqt, ht]
      · simp only [hqq]; cases t <;> rfl
  unfold Cache.DnsCache.lookupNegative at hlk
  cases hnxr : cache.lookupNxdomain name qc now with
  | some rc' =>
    unfold Cache.DnsCache.lookupNxdomain at hnxr
    obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some hnxr
    split at hef
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcond
      exact go e hemem hcond.1.1.1 hcond.1.2 (Or.inl (rcodeEq _ hcond.2))
    · exact absurd hef (by simp)
  | none =>
    rw [hnxr] at hlk
    obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some hlk
    split at hef
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcond
      exact go e hemem hcond.1.1.1 hcond.2 (Or.inr (eq_of_beq hcond.1.1.2))
    · exact absurd hef (by simp)

/-- **negHitNx cache refinement.** The NXDOMAIN analogue of `αCache_negHit`: a fresh stored impl
    negative entry that abstracts to a `qtype = none` (NXDOMAIN) model entry whose name matches the
    query forces the model's `Cache.negHitNx` — the model's "this is a name error, answer NXDOMAIN"
    gate. -/
theorem αCache_negHitNx (c : Cache.DnsCache) (now : UInt32) (q : VeriDNS.Spec.Net.Query)
    (e : Cache.NegativeEntry) (a : VeriDNS.Spec.Net.NegRR)
    (he : e ∈ c.negatives) (hα : αNegRR e = some a) (hfresh : now < e.expiry)
    (hname : VeriDNS.Spec.Net.nameEq a.qname q.qname = true)
    (hnone : a.qtype.isNone = true) :
    (αCache c).negHitNx (αTime now) q = true := by
  unfold VeriDNS.Spec.Net.Cache.negHitNx
  apply List.any_eq_true.mpr
  refine ⟨a, ?_, ?_⟩
  · unfold αCache
    simp only [List.mem_filterMap]
    exact ⟨e, Array.mem_def.mp he, hα⟩
  · simp only [Bool.and_eq_true]
    obtain ⟨h0, htt⟩ := αNegRR_fields hα
    refine ⟨⟨?_, hname⟩, hnone⟩
    unfold VeriDNS.Spec.Net.NegRR.fresh αTime
    rw [h0, htt, Nat.zero_add]
    exact Nat.blt_eq.mpr (UInt32.lt_iff_toNat_lt.mp hfresh)

/-- An impl NXDOMAIN cache hit always carries `Rcode.nameError` (the lookup's guard forces it). -/
theorem lookupNxdomain_nameError (c : Cache.DnsCache) (name : ByteArray) (qc : BitVec 16)
    (now : UInt32) (rc : VeriDNS.Spec.Rcode)
    (h : c.lookupNxdomain name qc now = some rc) : rc = VeriDNS.Spec.Rcode.nameError := by
  have hrcodeEq : ∀ a : VeriDNS.Spec.Rcode,
      (a == VeriDNS.Spec.Rcode.nameError) = true → a = VeriDNS.Spec.Rcode.nameError :=
    fun a h => by cases a <;> first | rfl | exact absurd h (by decide)
  unfold Cache.DnsCache.lookupNxdomain at h
  obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some h
  split at hef
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    have hrc : e.rcode = rc := by injection hef
    rw [← hrc]; exact hrcodeEq _ hcond.2
  · exact absurd hef (by simp)

/-- An impl NXDOMAIN cache hit forces the model's `Cache.negHitNx` on the abstracted cache: the
    executable NXDOMAIN cache is sound for the model's name-error gate. -/
theorem lookupNxdomain_negHitNx (c : Cache.DnsCache) (name : ByteArray) (qc : BitVec 16)
    (now : UInt32) (rc : VeriDNS.Spec.Rcode) (q : VeriDNS.Spec.Net.Query)
    (h : c.lookupNxdomain name qc now = some rc) (hqn : αName name = some q.qname) :
    (αCache c).negHitNx (αTime now) q = true := by
  unfold Cache.DnsCache.lookupNxdomain at h
  obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some h
  split at hef
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at hcond
    obtain ⟨na, hna, hnameq⟩ := αName_of_nameEqCI hcond.1.1.1 hqn
    refine αCache_negHitNx c now q e ⟨na, none, 0, e.expiry.toNat⟩ hemem ?_ hcond.1.2 hnameq rfl
    unfold αNegRR; rw [hna]; rw [hcond.2]; rfl
  · exact absurd hef (by simp)

/-- The impl `localAnswer` returns `.negative` exactly when the negative cache hits: a fresh
    `lookupNegative` short-circuits the CNAME/answer search at the current name. -/
theorem localAnswer_negative (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray) (rc : VeriDNS.Spec.Rcode)
    (h : cache.lookupNegative sname qt qc now = some rc) :
    Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection
          (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now) chain := by
  simp only [Resolver.localAnswer]
  rw [show VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now
      = cache.lookupNegative sname qt qc now from rfl, h]

/-- The impl `localAnswer` returns `.answerHit` at the current name when the negative cache misses
    and the positive cache yields a non-empty answer set — the direct (no CNAME chase) cache hit. -/
theorem localAnswer_answerHit (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hneg : cache.lookupNegative sname qt qc now = none)
    (hans : VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now = rrs)
    (hne : rrs.isEmpty = false) :
    Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited
      = .answerHit sname chain rrs := by
  simp only [Resolver.localAnswer]
  rw [show VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now
      = cache.lookupNegative sname qt qc now from rfl, hneg, hans]
  simp only [hne, Bool.false_eq_true, if_false]

/-- **Inversion of `localAnswer = .answerHit`** — recovers, at the *resolved* name `sname` (after any
    cache-internal CNAME hops the recursion followed), that the served set `rrs` is exactly the cache's
    answerable set there, non-empty, with no overriding negative entry. The impl-side input to the
    cache-hit model bridge (`lookupAnswerable_αRR_eq_hit` then pins `rrs` to the model's `Cache.hit`). Proven
    by induction on `fuel`: the `.negative`/`.miss` leaves are distinct constructors; each cache-CNAME hop
    recurses (`ih`); the terminal `.answerHit` leaf reads off the branch conditions. -/
theorem localAnswer_answerHit_inv (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname0 : ByteArray) (chain0 visited0 : Array ByteArray)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (h : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname0 chain0 visited0 = .answerHit sname chain rrs) :
    cache.lookupNegative sname qt qc now = none
      ∧ VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now = rrs
      ∧ rrs.isEmpty = false := by
  induction fuel generalizing sname0 chain0 visited0 with
  | zero => simp only [Resolver.localAnswer] at h; exact absurd h (by simp)
  | succ n ih =>
    simp only [Resolver.localAnswer] at h
    split at h
    · exact absurd h (by simp)
    · next hneg =>
      split at h
      · split at h
        · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · exact ih _ _ _ h
          · exact absurd h (by simp)
      · next hne =>
        injection h with hs hc hr
        subst sname0
        refine ⟨?_, hr, by rw [← hr]; simpa using hne⟩
        rw [show cache.lookupNegative sname qt qc now
          = VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now from rfl]
        exact hneg

/-- **The impl `localAnswer` CNAME-follow step** — the executable analogue of the model's
    `cacheCname` recursion. When the negative cache misses, the positive cache has no records of the
    queried type (and the query is not itself for CNAME), but a cached CNAME exists at `sname`,
    `localAnswer` restarts at the CNAME target, accumulating the CNAME into the chain. This is the
    single recursive step the `cacheCname` simulation branch composes over a CNAME chain. -/
theorem localAnswer_cname_step (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
    (crr : VeriDNS.Spec.ResourceRecord)
    (hneg : cache.lookupNegative sname qt qc now = none)
    (hempty : (VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true)
    (hnt5 : (qt == (5 : BitVec 16)) = false)
    (hcn : (VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache sname (5 : BitVec 16) qc now)[0]? = some crr)
    (hnrev : (visited.any (fun v =>
        VeriDNS.Impl.DomainName.nameEqCI v (VeriDNS.Spec.RRParse.rrRdata crr))) = false) :
    Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now (fuel + 1) sname chain visited
      = Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qt qc now fuel (VeriDNS.Spec.RRParse.rrRdata crr)
          (chain.push (VeriDNS.Spec.RRParse.rrBytes crr))
          (visited.push (VeriDNS.Spec.RRParse.rrRdata crr)) := by
  simp only [Resolver.localAnswer]
  rw [show VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now
      = cache.lookupNegative sname qt qc now from rfl, hneg]
  simp only [hempty, hnt5, hcn, hnrev, if_true, Bool.false_eq_true, if_false]

/-- **Observable verdict agreement.** Two responses agree on the client-observable verdict — the
    response code and the answer section — the parts the model `Net.Resolves` pins. (The impl
    additionally carries the RFC 2308 SOA in `authority`, which the model's negative responses
    elide; that extra hint is not part of the observable verdict.) -/
def RespAgree (a b : VeriDNS.Spec.Net.Response) : Prop :=
  a.rcode = b.rcode ∧ a.answer.Perm b.answer

/-- An exact answer match (the common construction site) is a `RespAgree`: `Perm` is reflexive. -/
theorem RespAgree.of_eq {a b : VeriDNS.Spec.Net.Response}
    (hrc : a.rcode = b.rcode) (han : a.answer = b.answer) : RespAgree a b :=
  ⟨hrc, han ▸ List.Perm.refl _⟩

theorem RespAgree.refl (a : VeriDNS.Spec.Net.Response) : RespAgree a a := ⟨rfl, List.Perm.refl _⟩

theorem RespAgree.trans {a b c : VeriDNS.Spec.Net.Response}
    (h1 : RespAgree a b) (h2 : RespAgree b c) : RespAgree a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- **The model admits a verdict.** There is a `Net.Resolves` derivation from the given configuration
    whose response observably agrees (`RespAgree`) with `v`. This is the simulation's right-hand side:
    the executable verdict `v` is *justified by the model*. The trace, returned path, end time, and
    output cache are existentially closed — what the client observes is the verdict, and what the
    forward simulation guarantees is that *some* valid model derivation produces it. -/
def HasVerdict (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : VeriDNS.Spec.Net.Time) (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name)
    (c : VeriDNS.Spec.Net.Cache) (slist : List String) (q : VeriDNS.Spec.Net.Query)
    (v : VeriDNS.Spec.Net.Response) : Prop :=
  ∃ tr sp tEnd cout resp,
    VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q
      tr sp tEnd cout resp
    ∧ RespAgree v resp

/-- **`HasVerdict` with the model's output cache exported** — identical to `HasVerdict` except the
    derivation's output cache `coutM` is a *parameter* instead of existentially closed. This is the
    conclusion form a CALLER that re-enters the resolution loop on the run's output cache needs (the
    `gluelessNs` sub-run composition: the model rule continues on the sub-run's output cache `c2`,
    so the sub-run's soundness must name it and tie it to the impl's output cache). `HasVerdictAt.toHasVerdict`
    recovers the plain form. -/
def HasVerdictAt (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (now : VeriDNS.Spec.Net.Time) (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name)
    (c : VeriDNS.Spec.Net.Cache) (slist : List String) (q : VeriDNS.Spec.Net.Query)
    (v : VeriDNS.Spec.Net.Response) (coutM : VeriDNS.Spec.Net.Cache) : Prop :=
  ∃ tr sp tEnd resp,
    VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q
      tr sp tEnd coutM resp
    ∧ RespAgree v resp

/-- Trivial repack: forgetting the exported output cache gives the plain `HasVerdict`. -/
theorem HasVerdictAt.toHasVerdict
    {net : VeriDNS.Spec.Net.Network} {ns : VeriDNS.Spec.Net.NetState}
    {resolverAddr : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : VeriDNS.Spec.Net.Time} {nseen seen : List VeriDNS.Spec.Net.Name}
    {c : VeriDNS.Spec.Net.Cache} {slist : List String} {q : VeriDNS.Spec.Net.Query}
    {v : VeriDNS.Spec.Net.Response} {coutM : VeriDNS.Spec.Net.Cache}
    (h : HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v coutM) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v := by
  obtain ⟨tr, sp, tEnd, resp, hres, hag⟩ := h
  exact ⟨tr, sp, tEnd, coutM, resp, hres, hag⟩

/-- **Step 2 capstone — write-side anti-poison refinement (the impl analogue of
`Net.absorb_pos_in_bailiwick`).** Every positive entry of the executable cache *after* a
bailiwick-filtered write of *any* response section (`sect`) is either one already present, or one
whose owner is in the model bailiwick `bwN` (`Net.isAncestor`). So the real cache write provably
admits only in-bailiwick records — an out-of-bailiwick RR a server injects (in the answer **or the
referral authority/additional**) cannot enter the cache. This is the model's
`absorb_pos_in_bailiwick` guarantee transported to the implementation through the `isAncestorB ⟹
Net.isAncestor` bridge and the `store`/`cacheRRs` provenance lemmas — the poisoning bug class (both
the answer-section write and the referral writes at `stepAnalyzeResponse` 4b) is now foreclosed *by
the model*, not by an ad-hoc filter. Generalising over `sect` is what makes it cover the referral
authority/additional writes, not just the answer section. -/
theorem cacheWrite_pos_in_bailiwick (c : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (sect : Array ByteArray)
    (bw : ByteArray) (cred : Trustworthiness) (now : UInt32) (bwN : VeriDNS.Spec.Net.Name)
    (hbw : αName bw = some bwN) (a : VeriDNS.Spec.Net.CacheRR)
    (ha : a ∈ (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        c resp (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw sect)
        cred now)).pos) :
    a ∈ (αCache c).pos ∨ VeriDNS.Spec.Net.isAncestor bwN a.rr.owner = true := by
  obtain ⟨e, he, hae⟩ := mem_αCache_pos _ a ha
  have hαrr : αRR e.rr = some a.rr := by
    unfold αCacheRR at hae
    rw [Option.map_eq_some_iff] at hae
    obtain ⟨r, hr, rfl⟩ := hae
    exact hr
  have hown : αName e.rr.name = some a.rr.owner := (αRR_fields e.rr a.rr hαrr).1
  have hpos : e ∈ c.records → a ∈ (αCache c).pos := by
    intro hec
    unfold αCache
    simp only [List.mem_filterMap]
    exact ⟨e, Array.mem_def.mp hec, hae⟩
  unfold Resolver.cacheUnlessTruncated at he
  split at he
  · exact Or.inl (hpos he)
  · rcases mem_cacheRRs_records _ cred now c he with hec | ⟨b, hb, hpb⟩
    · exact Or.inl (hpos hec)
    · right
      obtain ⟨r, hr, hrreq⟩ := VeriDNS.Proof.NameTree.parseRaw_mem_normRaws hb hpb
      obtain ⟨b', hb', hpb'⟩ := List.mem_filterMap.mp hr
      have hpb'' : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b' = some r := hpb'
      have hname : e.rr.name = r.name := by rw [hrreq]
      have hanc : Resolver.isAncestorB bw e.rr.name = true := by
        rw [hname]; exact Resolver.bailiwickRaws_owner_inBailiwick bw sect hb' hpb''
      exact isAncestorB_isAncestor bw e.rr.name bwN a.rr.owner hbw hown hanc

/-- **Referral write anti-poison (adversarial, both sections).** Composing the generic
`cacheWrite_pos_in_bailiwick` over the two referral cache writes (authority then additional, both
bailiwick-filtered to the delegation cut): *for an arbitrary, possibly adversarial `resp`*, every
positive entry after the `stepAnalyzeResponse` 4b referral write is either pre-existing or in the
model bailiwick `cutN` (`Net.isAncestor`). This is the proof that locks out the cache-poisoning bug
that lived in the referral path — an off-bailiwick record a malicious server stuffs into the
authority or additional section *cannot* enter the cache. No well-formedness/`ResponseConsistent`
hypothesis on `resp`: the guarantee holds against any input. -/
theorem referralCacheWrite_pos_in_bailiwick (c : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (cred1 cred2 : Trustworthiness) (now : UInt32) (cutN : VeriDNS.Spec.Net.Name)
    (hcut : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
        = some cutN)
    (a : VeriDNS.Spec.Net.CacheRR)
    (ha : a ∈ (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) c resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
          cred1 now)
        resp
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
        cred2 now)).pos) :
    a ∈ (αCache c).pos ∨ VeriDNS.Spec.Net.isAncestor cutN a.rr.owner = true := by
  rcases cacheWrite_pos_in_bailiwick _ resp resp.additional _ cred2 now cutN hcut a ha with hinner | hbail
  · rcases cacheWrite_pos_in_bailiwick c resp resp.authority _ cred1 now cutN hcut a hinner with
      horig | hbail2
    · exact Or.inl horig
    · exact Or.inr hbail2
  · exact Or.inr hbail

theorem lookupAnswerable_no_stale (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupAnswerable name qt qc now) : 0 < rr.ttl.toNat := by
  unfold Cache.DnsCache.lookupAnswerable at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, _, hsome⟩ := h
  split at hsome
  · rename_i hans

    have hfresh : e.fresh now = true := by
      rw [Bool.and_eq_true] at hans
      obtain ⟨hans, _⟩ := hans
      unfold Cache.answerableEntry Cache.liveEntry at hans
      simp only [Bool.and_eq_true] at hans
      obtain ⟨⟨⟨⟨_, _⟩, _⟩, hf⟩, _⟩ := hans
      exact hf
    have hlt : now < e.expiry := by
      have hb := hfresh; unfold Cache.CacheEntry.fresh at hb; simpa using hb
    have hpos : 0 < (e.expiry - now).toNat := by
      rw [UInt32.toNat_sub_of_le e.expiry now (UInt32.le_of_lt hlt)]
      have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    obtain rfl : rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
      injection hsome with h'; exact h'.symm
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
    exact hpos
  · exact absurd hsome (by simp)

theorem lookupAnswerable_grounded (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupAnswerable name qt qc now) :
    ∃ e ∈ c.records, rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold Cache.DnsCache.lookupAnswerable at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  refine ⟨e, he, ?_⟩
  split at hsome
  · injection hsome with h'; exact h'.symm
  · exact absurd hsome (by simp)

/-- **`lookupTopCred` results come from cache records** (SLIST-read analogue of `lookupAnswerable_grounded`).
    Every record returned by the credibility-aware SLIST lookup is the TTL-aged copy of some `c.records` entry —
    the grounding step for the `lookupTopCred ↔ topServed` correspondence (chunk 2d of the cache-re-derived
    referral SLIST). -/
theorem lookupTopCred_grounded (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred name qt qc now) :
    ∃ e ∈ c.records, rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  refine ⟨e, he, ?_⟩
  split at hsome
  · injection hsome with h'; exact h'.symm
  · exact absurd hsome (by simp)

/-- **Every `lookupTopCred name qt` result has `rrType == qt`** — the `liveEntry` gate filters on `type == qt`,
    and TTL-aging preserves the type. Lets the redundant `rrType == 1` guard be dropped from
    `lookupTopCred_a_eq_glueAddrsAt` so the impl glue chain (`impl_glue_per_name_model`, no guard) joins it. -/
theorem mem_lookupTopCred_rrType (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord) (h : rr ∈ c.lookupTopCred name qt qc now) :
    (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == qt) = true := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, _, hsome⟩ := h
  split at hsome
  · rename_i hgate
    rw [Bool.and_eq_true] at hgate
    have hl := hgate.1
    unfold Cache.liveEntry at hl
    simp only [Bool.and_eq_true] at hl
    obtain ⟨⟨⟨_, htype⟩, _⟩, _⟩ := hl
    injection hsome with hsome
    rw [← hsome]
    exact htype
  · exact absurd hsome (by simp)

/-- **A `lookupTopCred` record shares its rdata with a cache entry.** `lookupTopCred` is `records.filterMap` of a
    TTL-adjusting copy (`{e.rr with ttl := …}`), so every returned `rr` is some live entry `e`'s record with only
    the TTL changed — hence identical rdata. Lets `CacheWf` (over `c.records`) reach into `lookupTopCred`'s output:
    if every stored record abstracts, so does every NS host name extracted at the cut. -/
theorem mem_lookupTopCred_entry (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord) (h : rr ∈ c.lookupTopCred name qt qc now) :
    ∃ e ∈ c.records, VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
      = VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) e.rr
      ∧ VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
        = VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) e.rr := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, he, hsome⟩ := h
  refine ⟨e, he, ?_, ?_⟩
  all_goals
    split at hsome
    · rw [Option.some.injEq] at hsome; subst hsome; rfl
    · exact absurd hsome (by simp)

/-- **Every `lookupTopCred`-NS record extracts to `some` NS name** — the `walkNs` NS extraction drops nothing
    (each record has `rrType == NS`, so the `if rrType == NS` guard always fires). The all-`some` fact that, via
    `isEmpty_filterMap_of_all_isSome`, makes the impl `walkNs` stop condition (`lookup ≠ ∅`) match the model's
    (`nsHostsAt ≠ ∅`) — the walk-recursion alignment. -/
theorem ns_extract_isSome (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now) :
    (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
      then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none).isSome = true := by
  rw [if_pos (mem_lookupTopCred_rrType c cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now rr h)]
  rfl

/-- **`lookupTopCred` never returns stale records** (SLIST-read analogue of `lookupAnswerable_no_stale`). The
    `liveEntry` gate forces `now < e.expiry`, so the aged TTL is strictly positive. -/
theorem lookupTopCred_no_stale (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (rr : VeriDNS.Spec.ResourceRecord)
    (h : rr ∈ c.lookupTopCred name qt qc now) : 0 < rr.ttl.toNat := by
  unfold Cache.DnsCache.lookupTopCred at h
  rw [Array.mem_filterMap] at h
  obtain ⟨e, _, hsome⟩ := h
  split at hsome
  · rename_i hgate
    have hfresh : e.fresh now = true := by
      rw [Bool.and_eq_true] at hgate
      obtain ⟨hlive, _⟩ := hgate
      unfold Cache.liveEntry at hlive
      simp only [Bool.and_eq_true] at hlive
      obtain ⟨⟨⟨_, _⟩, _⟩, hf⟩ := hlive
      exact hf
    have hlt : now < e.expiry := by
      have hb := hfresh; unfold Cache.CacheEntry.fresh at hb; simpa using hb
    have hpos : 0 < (e.expiry - now).toNat := by
      rw [UInt32.toNat_sub_of_le e.expiry now (UInt32.le_of_lt hlt)]
      have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    obtain rfl : rr = { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
      injection hsome with h'; exact h'.symm
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
    exact hpos
  · exact absurd hsome (by simp)

/-- **`lookupTopCred` filterMap fusion.** Mapping `g` over `lookupTopCred`'s result is mapping, over all cache
    records, the gate `liveEntry e && maxRankForKey e` then `g` of the TTL-aged record. The mechanical impl-side
    step for the `lookupTopCred ↔ topServed` extraction correspondence (both the NS and glue extractions reduce
    to a `filterMap` over `c.records` via this). -/
theorem lookupTopCred_toList_filterMap {β : Type} (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (g : VeriDNS.Spec.ResourceRecord → Option β) :
    (c.lookupTopCred name qt qc now).toList.filterMap g
      = c.records.toList.filterMap (fun e =>
          if Cache.liveEntry e name qt qc now && c.maxRankForKey e now
          then g { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } else none) := by
  unfold Cache.DnsCache.lookupTopCred
  rw [Array.toList_filterMap, List.filterMap_filterMap]
  congr 1
  funext e
  cases hg : (Cache.liveEntry e name qt qc now && c.maxRankForKey e now) <;> simp [hg]

/-- **`αSection` of re-serialized records is the record-set abstraction** — the codec round-trip
    discharged inside the cache→answer abstraction. For well-formed records (`WfRR`, the cache
    invariant: valid labels + consistent rdlength, established when they were parsed from the wire),
    `αSection (rrs.map rrBytes) = rrs.toList.filterMap αRR`: re-encoding then re-parsing is the
    identity, so abstracting the served byte-section equals abstracting the records directly. This is
    the round-trip half of `hhit`; what remains is the served↔`lookupAnswerable` set correspondence
    (keyed on `αCred_order_used`). -/
theorem αSection_map_rrBytes_wf (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hwf : ∀ rr ∈ rrs, VeriDNS.Proof.NameTree.WfRR rr) :
    αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
      = rrs.toList.filterMap αRR := by
  unfold αSection
  rw [Array.toList_map, List.filterMap_map]
  have key : ∀ l : List VeriDNS.Spec.ResourceRecord,
      (∀ rr ∈ l, VeriDNS.Proof.NameTree.WfRR rr) →
      l.filterMap ((fun b => match VeriDNS.Spec.RRParse.parseRaw
            (RR := VeriDNS.Spec.ResourceRecord) b with
          | some rr => αRR rr | none => none) ∘ VeriDNS.Spec.RRParse.rrBytes)
        = l.filterMap αRR := by
    intro l hl
    induction l with
    | nil => rfl
    | cons rr rest ih =>
      simp only [List.filterMap_cons, Function.comp_apply,
        VeriDNS.Proof.NameTree.parseRaw_rrBytes_of_wf (hl rr (List.mem_cons_self ..))]
      rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  exact key rrs.toList (fun rr hrr => hwf rr (Array.mem_def.mpr hrr))

theorem served_is_per_key_maximal (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (e e2 : Cache.CacheEntry)
    (hmax : c.maxCredForKey e name qt qc now = true)
    (h2 : e2 ∈ c.records) (hans2 : Cache.answerableEntry e2 name qt qc now = true)
    (hkey : Cache.sameRRKey e2 e = true) :
    e.credibility.toCode ≤ e2.credibility.toCode := by
  unfold Cache.DnsCache.maxCredForKey at hmax
  obtain ⟨i, hi, hgi⟩ := Array.getElem_of_mem h2
  have hbody := Array.all_eq_true.mp hmax i hi
  rw [hgi] at hbody
  simp only [hans2, hkey, Bool.and_true, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at hbody
  exact hbody

/-! ### List-fusion helpers for the `hhit` list equality

  Three general `List` identities used to fuse the nested `filter`/`map`/`filterMap` of
  `Cache.hit = ((matching.filter served).map aging)` and `lookupAnswerable = records.filterMap …` into
  a common `c.records.toList.filterMap _` shape, where `filterMap_congr_mem` then reduces the list
  equality to the per-element option equality (`cond_eq` below). -/

/-- `(l.filter p).map f` as a single `filterMap`. -/
theorem filter_map_eq_filterMap {α β} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f = l.filterMap (fun a => bif p a then some (f a) else none) := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.filter_cons]; cases hx : p x <;> simp [hx, List.filterMap_cons, ih]

/-- `(l.filter p).filterMap g` as a single `filterMap`. -/
theorem filter_filterMap_eq {α β} (l : List α) (p : α → Bool) (g : α → Option β) :
    (l.filter p).filterMap g = l.filterMap (fun a => bif p a then g a else none) := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.filter_cons]; cases hx : p x <;> simp [hx, List.filterMap_cons, ih]

/-- Pointwise congruence for `filterMap` over a fixed list. -/
theorem filterMap_congr_mem {α β} (l : List α) (f g : α → Option β) (h : ∀ a ∈ l, f a = g a) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h x (by simp), ih (fun a ha => h a (by simp [ha]))]

/-- Pointwise congruence for `flatMap` over a fixed list — needed for the keystone-at-a-cut, where each NS host
    summand is rewritten by `per_host_glue` (whose hypotheses depend on the host, so plain `funext` won't do). -/
theorem flatMap_congr_mem {α β} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih (fun a ha => h a (by simp [ha]))]

/-- **`hhit` soundness direction (the security-relevant half): `lookupAnswerable ⊆ Cache.hit`.**
    Every record the executable resolver serves from its positive cache abstracts to a member of the
    model's `Cache.hit` — so the impl *never serves a record the model wouldn't*. Composes the forward
    correspondences (`answerableEntry_matching`, `αRR_aged`) with `αCache` grounding. Needs the cache
    abstraction to succeed (`hwf`: each entry abstracts, with `ttl ≤ expiry` and `insertedAt ≤ now`)
    and a per-key-uniform-rank invariant (`hmaxrank`: every `matching` entry is rank-maximal among its
    key — true of caches the resolver builds, since `store` keeps one credibility per RRset key), which
    trivialises the model's `maxrank` gate. NO reverse/canonicity needed — this is the soundness
    (anti-mis-answer) direction. -/
theorem lookupAnswerable_subset_hit (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hmaxrank : ∀ a ∈ (αCache c).matching (αTime now) q,
        ((αCache c).matching (αTime now) q).all
          (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true)
    (rr : VeriDNS.Spec.ResourceRecord) (hrr : rr ∈ c.lookupAnswerable name qt qc now) :
    ∃ rm, αRR rr = some rm ∧ rm ∈ (αCache c).hit (αTime now) q := by
  unfold Cache.DnsCache.lookupAnswerable at hrr
  rw [Array.mem_filterMap] at hrr
  obtain ⟨e, hemem, hsome⟩ := hrr
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hans, _hmax⟩ := hcond
    injection hsome with hsome
    obtain ⟨hane, hle, hmono⟩ := hwf e hemem
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
    have hfr : e.fresh now = true := by
      unfold Cache.answerableEntry Cache.liveEntry at hans
      simp only [Bool.and_eq_true] at hans
      exact hans.1.2
    obtain ⟨hf, hne, hcov, hcl, hus⟩ :=
      answerableEntry_matching e a name qt qc now q t hqn ht hqq hqc hle hans ha
    have hmatch : a ∈ (αCache c).matching (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.matching
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold αCache; simp only [List.mem_filterMap]
        exact ⟨e, Array.mem_def.mp hemem, ha⟩
      · simp only [Bool.and_eq_true]; exact ⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩
    have hserved : a ∈ (αCache c).served (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.served
      rw [List.mem_filter]
      refine ⟨hmatch, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hus, hmaxrank a hmatch⟩
    refine ⟨{ a.rr with ttl := a.rr.ttl - (now.toNat - a.insertedAt) }, ?_, ?_⟩
    · rw [← hsome]; exact αRR_aged e a now hle hfr hmono ha
    · unfold VeriDNS.Spec.Net.Cache.hit
      rw [List.mem_map]
      exact ⟨a, hserved, rfl⟩
  · exact absurd hsome (by simp)

/-- **`maxCredForKey ↔ served`-maximality reconciliation (the `hhit`-completeness keystone).** If the
    abstraction `a` of a stored entry `e` is rank-maximal among its RRset key within the model's
    `matching` set (`hmax` — exactly the per-key gate of `Cache.served`), then `e` passes the impl's
    `maxCredForKey` gate. This is the credibility half of the COMPLETENESS direction (`hit ⊆
    lookupAnswerable`): it transports the model's `Cred.rank`-maximality back to the impl's
    `toCode`-minimality. For each same-key answerable competitor `e2 ∈ c.records` it routes through
    `answerableEntry_matching` (so `e2`'s abstraction is `matching`), `αRR_sameKey` (same RRset key),
    `hmax` (so `a2.cred.rank ≤ a.cred.rank`), and finally `αCred_order_used` (the order-reversing
    `rank ↔ toCode` bijection on the used-credibility set) to conclude `e.toCode ≤ e2.toCode`. The
    `hused` hypothesis — every record's credibility is one the resolver actually stores
    (`authoritativeSection`/`authoritySection`/`sectionNonauthoritative`/`additionalAuthoritative`) —
    is what makes `αCred_order_used` applicable; it holds of every cache the resolver builds. Forward
    correspondences only (no canonicity). -/
theorem maxCredForKey_of_served_maximal (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hmax : ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true) :
    c.maxCredForKey e name qt qc now = true := by
  unfold Cache.DnsCache.maxCredForKey
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro e2 he2
  by_cases hcond : (Cache.answerableEntry e2 name qt qc now && Cache.sameRRKey e2 e) = true
  · rw [hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hans2, hsame2⟩ := hcond
    obtain ⟨hane2, hle2, _hmono2⟩ := hwf e2 he2
    obtain ⟨a2, ha2⟩ := Option.isSome_iff_exists.mp hane2
    obtain ⟨hf2, hne2, hcov2, hcl2, _hus2⟩ :=
      answerableEntry_matching e2 a2 name qt qc now q t hqn ht hqq hqc hle2 hans2 ha2
    have hmatch2 : a2 ∈ (αCache c).matching (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.matching
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold αCache; simp only [List.mem_filterMap]; exact ⟨e2, Array.mem_def.mp he2, ha2⟩
      · simp only [Bool.and_eq_true]; exact ⟨⟨⟨hf2, hne2⟩, hcov2⟩, hcl2⟩
    have hsk : a2.sameKey a.rr = true := αRR_sameKey e2 e a2 a ha2 ha hsame2
    have hmaxp := (List.all_eq_true.mp hmax) a2 hmatch2
    simp only [hsk, Bool.not_true, Bool.false_or] at hmaxp
    have hrank : a2.cred.rank ≤ a.cred.rank := Nat.le_of_ble_eq_true hmaxp
    have hce : αCred e.credibility = a.cred := by
      have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hce2 : αCred e2.credibility = a2.cred := by
      have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
    rw [hce, hce2] at hord
    exact hord.mpr hrank
  · rw [Bool.not_eq_true] at hcond
    rw [hcond]; rfl

/-- **`maxRankForKey` from per-key `topServed`-maximality (SLIST analogue of `maxCredForKey_of_served_maximal`).**
    If model `a` is per-key rank-maximal among `matching` (the `topServed` gate), then the impl's `maxRankForKey`
    holds for its source `e` — every live same-key impl record `e2` is no more credible (`e.toCode ≤ e2.toCode`,
    via the order-reversing `αCred_order_used`). The gate domain is `fresh ∧ sameRRKey` (no answer floor), so
    `e2` ranges over ALL live same-key records, reaching `matching` via `liveEntry_matching` + `nameEqCI_trans`.
    The impl half of the `lookupTopCred ↔ topServed` correspondence (chunk 2d). -/
theorem maxRankForKey_of_topServed_maximal (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hlive : Cache.liveEntry e name qt qc now = true)
    (hmax : ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true) :
    c.maxRankForKey e now = true := by
  unfold Cache.DnsCache.maxRankForKey
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro e2 he2
  by_cases hcond : (e2.fresh now && Cache.sameRRKey e2 e) = true
  · rw [hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hfresh2, hsame2⟩ := hcond
    obtain ⟨hane2, hle2, _hmono2⟩ := hwf e2 he2
    obtain ⟨a2, ha2⟩ := Option.isSome_iff_exists.mp hane2
    have hlive2 : Cache.liveEntry e2 name qt qc now = true := by
      have hsk := hsame2
      unfold Cache.sameRRKey at hsk
      simp only [Bool.and_eq_true] at hsk
      obtain ⟨⟨hnm2, htype2⟩, hcls2⟩ := hsk
      have hlv := hlive
      unfold Cache.liveEntry at hlv ⊢
      simp only [Bool.and_eq_true] at hlv ⊢
      obtain ⟨⟨⟨hnm, htype⟩, hcls⟩, _⟩ := hlv
      refine ⟨⟨⟨VeriDNS.Proof.NameTree.nameEqCI_trans hnm2 hnm, ?_⟩, ?_⟩, hfresh2⟩
      · rw [beq_iff_eq] at htype2 htype ⊢; rw [htype2, htype]
      · rw [beq_iff_eq] at hcls2 hcls ⊢; rw [hcls2, hcls]
    obtain ⟨hf2, hne2, hcov2, hcl2⟩ :=
      liveEntry_matching e2 a2 name qt qc now q t hqn ht hqq hqc hle2 hlive2 ha2
    have hmatch2 : a2 ∈ (αCache c).matching (αTime now) q := by
      unfold VeriDNS.Spec.Net.Cache.matching
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold αCache; simp only [List.mem_filterMap]; exact ⟨e2, Array.mem_def.mp he2, ha2⟩
      · simp only [Bool.and_eq_true]; exact ⟨⟨⟨hf2, hne2⟩, hcov2⟩, hcl2⟩
    have hsk : a2.sameKey a.rr = true := αRR_sameKey e2 e a2 a ha2 ha hsame2
    have hmaxp := (List.all_eq_true.mp hmax) a2 hmatch2
    simp only [hsk, Bool.not_true, Bool.false_or] at hmaxp
    have hrank : a2.cred.rank ≤ a.cred.rank := Nat.le_of_ble_eq_true hmaxp
    have hce : αCred e.credibility = a.cred := by
      have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hce2 : αCred e2.credibility = a2.cred := by
      have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
    rw [hce, hce2] at hord
    exact hord.mpr hrank
  · rw [Bool.not_eq_true] at hcond
    rw [hcond]; rfl

/-- **The forward reconciliation: `maxCredForKey ⟹ served`-maximality** (the mirror of
    `maxCredForKey_of_served_maximal`). If a stored entry `e` passes the impl's `maxCredForKey` gate
    then its abstraction `a` is `Cred.rank`-maximal among its RRset key in the model's `matching` set —
    exactly the per-key clause of `Cache.served`. For each same-key `a2 ∈ matching`: if `a2` is *not*
    usable it is `Cred.additional` (rank 0), so maximality is automatic; if it *is* usable then its
    source `e2` is an impl `answerableEntry` (`matching_answerableEntry`) with the same `sameRRKey`
    (`sameKey_sameRRKey`), so `maxCredForKey` forces `e.toCode ≤ e2.toCode`, which `αCred_order_used`
    turns into `a2.rank ≤ a.rank`. Together with `maxCredForKey_of_served_maximal` this is the
    *bidirectional* credibility reconciliation the per-element option equality of the full `hhit` list
    equality rests on. Needs the canonicity invariant (for the reverse predicate/same-key bridges). -/
theorem served_maximal_of_maxCredForKey (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hmaxc : c.maxCredForKey e name qt qc now = true) :
    ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true := by
  rw [List.all_eq_true]
  intro a2 ha2mem
  by_cases hsk : a2.sameKey a.rr = true
  · simp only [hsk, Bool.not_true, Bool.false_or]
    unfold VeriDNS.Spec.Net.Cache.matching at ha2mem
    rw [List.mem_filter] at ha2mem
    obtain ⟨hpos2, hpred2⟩ := ha2mem
    obtain ⟨e2, he2, ha2⟩ := mem_αCache_pos c a2 hpos2
    obtain ⟨hane2, hle2, _hmono2⟩ := hwf e2 he2
    by_cases hu2 : a2.cred.usable = true
    · obtain ⟨hcanE2, hvE2⟩ := hcanon e2 he2 a2 ha2
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred2
      obtain ⟨⟨⟨hf2, hne2⟩, hcov2⟩, hcl2⟩ := hpred2
      have hans2 : Cache.answerableEntry e2 name qt qc now = true :=
        matching_answerableEntry e2 a2 name qt qc now q t ht hqq hqc hle2 ha2 hcanE2 hcanN hvE2 hvN
          hf2 hne2 hcov2 hcl2 hu2
      have hsame2 : Cache.sameRRKey e2 e = true := by
        obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
        exact sameKey_sameRRKey e2 e a2 a ha2 ha hcanE2 hcanE hvE2 hvE hsk
      have hmcp := Array.all_eq_true_iff_forall_mem.mp hmaxc e2 he2
      rw [hans2, hsame2, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hmcp
      have hce : αCred e.credibility = a.cred := by
        have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h; rfl
      have hce2 : αCred e2.credibility = a2.cred := by
        have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h; rfl
      have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
      rw [hce, hce2] at hord
      exact Nat.ble_eq.mpr (hord.mp hmcp)
    · have hadd : a2.cred = VeriDNS.Spec.Net.Cred.additional := by
        cases hc : a2.cred with
        | additional => rfl
        | glue => simp [hc, VeriDNS.Spec.Net.Cred.usable] at hu2
        | authority => simp [hc, VeriDNS.Spec.Net.Cred.usable] at hu2
        | authoritative => simp [hc, VeriDNS.Spec.Net.Cred.usable] at hu2
      rw [hadd]; exact Nat.ble_eq.mpr (Nat.zero_le _)
  · rw [Bool.not_eq_true] at hsk
    simp only [hsk, Bool.not_false, Bool.true_or]

/-- **`topServed`-maximality from `maxRankForKey` (SLIST reverse direction; mirror of
    `served_maximal_of_maxCredForKey`).** If a stored entry `e` passes the impl's `maxRankForKey` gate, its
    abstraction `a` is per-key rank-maximal among the model's `matching` set — so the impl's `lookupTopCred`
    selects exactly the model's `topServed` records. SIMPLER than the `served` version: `maxRankForKey` has no
    answer floor, so it bounds EVERY live same-key record (no `usable`/additional-tier case split). -/
theorem topServed_maximal_of_maxRankForKey (c : Cache.DnsCache)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (a : VeriDNS.Spec.Net.CacheRR)
    (he : e ∈ c.records) (ha : αCacheRR e = some a)
    (hmaxr : c.maxRankForKey e now = true) :
    ((αCache c).matching (αTime now) q).all
        (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank) = true := by
  rw [List.all_eq_true]
  intro a2 ha2mem
  by_cases hsk : a2.sameKey a.rr = true
  · simp only [hsk, Bool.not_true, Bool.false_or]
    unfold VeriDNS.Spec.Net.Cache.matching at ha2mem
    rw [List.mem_filter] at ha2mem
    obtain ⟨hpos2, hpred2⟩ := ha2mem
    obtain ⟨e2, he2, ha2⟩ := mem_αCache_pos c a2 hpos2
    obtain ⟨_hane2, hle2, _hmono2⟩ := hwf e2 he2
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred2
    obtain ⟨⟨⟨hf2, _hne2⟩, _hcov2⟩, _hcl2⟩ := hpred2
    have hfresh2 : e2.fresh now = true := (αCacheRR_fresh e2 a2 now hle2 ha2).trans hf2
    have hsame2 : Cache.sameRRKey e2 e = true := by
      obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
      obtain ⟨hcanE2, hvE2⟩ := hcanon e2 he2 a2 ha2
      exact sameKey_sameRRKey e2 e a2 a ha2 ha hcanE2 hcanE hvE2 hvE hsk
    have hmrp := Array.all_eq_true_iff_forall_mem.mp hmaxr e2 he2
    rw [show (e2.fresh now && Cache.sameRRKey e2 e) = true from by rw [hfresh2, hsame2]; rfl,
        Bool.not_true, Bool.false_or, decide_eq_true_eq] at hmrp
    have hce : αCred e.credibility = a.cred := by
      have h := ha; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hce2 : αCred e2.credibility = a2.cred := by
      have h := ha2; unfold αCacheRR at h; rw [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h; rfl
    have hord := αCred_order_used e.credibility e2.credibility (hused e he) (hused e2 he2)
    rw [hce, hce2] at hord
    exact Nat.ble_eq.mpr (hord.mp hmrp)
  · rw [Bool.not_eq_true] at hsk
    simp only [hsk, Bool.not_false, Bool.true_or]

/-- **Per-element gate equality (the semantic crux of the `hhit` list equality).** For a stored entry
    `e` abstracting to `a`, the impl's serve-gate `answerableEntry e && maxCredForKey e` equals the
    model's serve-gate `matching-predicate(a) && (usable ∧ per-key-max)` — i.e. the impl serves `e`
    *iff* the model serves `a`. The forward half uses `answerableEntry_matching` (predicate) and
    `served_maximal_of_maxCredForKey` (credibility); the reverse half uses `matching_answerableEntry`
    and `maxCredForKey_of_served_maximal`. This is the per-element input to `filterMap_congr_mem` that
    assembles the full list equality `(lookupAnswerable …).toList.filterMap αRR = Cache.hit` (together
    with `αRR_aged` for the produced value). It packages the entire bidirectional set-of-bridges into
    one Boolean identity. -/
theorem cond_eq (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (he : e ∈ c.records) (a : VeriDNS.Spec.Net.CacheRR) (ha : αCacheRR e = some a) :
    (Cache.answerableEntry e name qt qc now && c.maxCredForKey e name qt qc now)
      = ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
            && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && (a.cred.usable && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank))) := by
  obtain ⟨hane, hle, hmono⟩ := hwf e he
  obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hans, hmaxc⟩
    obtain ⟨hf, hne, hcov, hcl, hus⟩ :=
      answerableEntry_matching e a name qt qc now q t hqn ht hqq hqc hle hans ha
    exact ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩, hus, served_maximal_of_maxCredForKey c name qt qc now q t ht hqq
      hqc hcanN hvN hwf hcanon hused e a he ha hmaxc⟩
  · rintro ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩, hus, hmax⟩
    exact ⟨matching_answerableEntry e a name qt qc now q t ht hqq hqc hle ha hcanE hcanN hvE hvN
        hf hne hcov hcl hus,
      maxCredForKey_of_served_maximal c name qt qc now q t hqn ht hqq hqc hwf hused e a he ha hmax⟩

/-- **Per-element SLIST gate equality (the semantic crux of the `lookupTopCred` list equality; analogue of
    `cond_eq`, minus `usable`).** For a stored `e` abstracting to `a`, the impl's SLIST gate
    `liveEntry e && maxRankForKey e` equals the model's `topServed` gate `matching-predicate(a) && per-key-max`
    — the impl puts `e` in the SLIST read iff the model puts `a` in `topServed`. Composes the four directions
    (`liveEntry_matching`/`matching_liveEntry` for the predicate, `*_maximal_of_*` for the rank gate). -/
theorem cond_eq_top (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (e : Cache.CacheEntry) (he : e ∈ c.records) (a : VeriDNS.Spec.Net.CacheRR) (ha : αCacheRR e = some a) :
    (Cache.liveEntry e name qt qc now && c.maxRankForKey e now)
      = ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
            && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) := by
  obtain ⟨hane, hle, hmono⟩ := hwf e he
  obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hlive, hmaxr⟩
    obtain ⟨hf, hne, hcov, hcl⟩ :=
      liveEntry_matching e a name qt qc now q t hqn ht hqq hqc hle hlive ha
    exact ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩,
      topServed_maximal_of_maxRankForKey c now q hwf hcanon hused e a he ha hmaxr⟩
  · rintro ⟨⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩, hmax⟩
    have hlive := matching_liveEntry e a name qt qc now q t ht hqq hqc hle ha hcanE hcanN hvE hvN
      hf hne hcov hcl
    exact ⟨hlive,
      maxRankForKey_of_topServed_maximal c name qt qc now q t hqn ht hqq hqc hwf hused e a he ha hlive hmax⟩

/-- **NS-rdata abstraction bridge.** If an impl record `rr` abstracts to a model `r` whose rdata is `.ns h`,
    then the impl's rdata bytes `rrRdata rr` `αName`-abstract to `h`. (`αRData` of an NS record is
    `(αName rdata).map .ns`, so the `.ns h` result pins `αName rdata = some h`.) The value-level half of the
    `walkNs`-NS ↔ `nsHostsAt` extraction correspondence: the impl's extracted NS-name bytes map to the model's
    NS host name. -/
theorem αName_rrRdata_of_ns (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (h : VeriDNS.Spec.Net.Name)
    (harr : αRR rr = some r) (hns : r.rdata = VeriDNS.Spec.Net.RData.ns h) :
    αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some h := by
  unfold αRR at harr
  split at harr
  · rename_i owner rdata cls hn hrd hcl
    injection harr with harr
    have hrdata : rdata = VeriDNS.Spec.Net.RData.ns h := by rw [← harr] at hns; exact hns
    rw [hrdata] at hrd
    show αName rr.rdata = some h
    unfold αRData at hrd
    split at hrd
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨na, hna, hx⟩ := hrd
      injection hx with hx; subst hx; exact hna
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · simp at hrd
  · simp at harr

/-- **The keystone's `hone` discharges from `CacheWf` + a non-empty cut.** When the cut has a cached NS RRset
    (`hcut_ne`), there is an NS record whose rdata (target name) abstracts — because `CacheWf` (`hwf`) makes EVERY
    stored record abstract (`αCacheRR` is `some` ⟹ `αRR` is `some` ⟹ for an NS record, `αName(rdata)` is `some`).
    Composes `mem_lookupTopCred_rrType`/`mem_lookupTopCred_entry`/`αCacheRR_rr`/`αRR_rtype`/`αName_rrRdata_of_ns`.
    So the model `nsHostsAt cut` is non-empty — the model walk stops where the impl `walkNs` does. -/
theorem hone_of_CacheWf (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcut_ne : (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = false) :
    ∃ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
      (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none := by
  obtain ⟨rr, hrr⟩ := Array.exists_mem_of_ne_empty
    (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now) (by simpa using hcut_ne)
  have hns := mem_lookupTopCred_rrType c cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now rr hrr
  obtain ⟨e, he, hrd, htp⟩ := mem_lookupTopCred_entry c cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now rr hrr
  obtain ⟨ce, hce⟩ := Option.isSome_iff_exists.mp (hwf e he).1
  have harr := αCacheRR_rr hce
  have hrt := αRR_rtype e.rr ce.rr harr
  have hetype : e.rr.type = BitVec.ofNat 16 2 := by
    have h2 : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) e.rr == BitVec.ofNat 16 2) = true := by
      rw [← htp]; exact hns
    exact eq_of_beq h2
  have hrtns : ce.rr.rdata.rtype = RRType.ns := by
    rw [hetype] at hrt
    exact (Option.some.inj hrt).symm
  obtain ⟨h, hh⟩ : ∃ h, ce.rr.rdata = VeriDNS.Spec.Net.RData.ns h := by
    cases hrd' : ce.rr.rdata with
    | ns h => exact ⟨h, rfl⟩
    | _ => rw [hrd'] at hrtns; simp [VeriDNS.Spec.Net.RData.rtype] at hrtns
  refine ⟨rr, by simpa using hrr, ?_⟩
  rw [if_pos hns, hrd, αName_rrRdata_of_ns e.rr ce.rr h harr hh]
  simp

/-- **The keystone's `hhost` is the per-record NS-rdata canonicity, lifted to the extraction.** `hhost` asks each
    extracted NS host name (`lookupTopCred cut` filtered to NS rdata) to be a canonical wire name; this is exactly
    the per-record hypothesis `hrdcanon` (each cached NS record's rdata target is `labelsToWireFormatGo` of its
    abstraction) mapped over the `filterMap`. Unlike owner canonicity (`CacheWf.hcanon`), NS-RDATA canonicity is a
    SEPARATE honest-cache property — it holds because the referral's NS targets are canonical wire (the honest
    `hwmApp` disjunct's `hvalid`), and must be threaded like `CacheWf`. This lemma isolates that one assumption. -/
theorem hhost_of_rdata_canonical (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (hrdcanon : ∀ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2) = true →
        ∃ na, αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some na
          ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
            = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    ∀ n ∈ ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).toList,
      ∃ qn, αName n = some qn ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63)
        ∧ qn.length ≤ 127 := by
  intro n hn
  rw [Array.toList_filterMap, List.mem_filterMap] at hn
  obtain ⟨rr, hrr, hsome⟩ := hn
  split at hsome
  · rename_i hns'
    rw [Option.some.injEq] at hsome
    subst hsome
    exact hrdcanon rr hrr hns'
  · exact absurd hsome (by simp)

/-- **The NS-rdata-canonical cache invariant.** Every cached NS record's stored rdata is a canonical wire name.
    The impl `DnsCache` stores PARSED `ResourceRecord`s, and an NS record absorbed from a `decodeRRCanonical`
    response blob has canonical rdata (`canonicalRR_nsRdata_canonical`) — so this invariant is maintainable and,
    unlike the honest-disjunct NS canonicity, holds for warm caches and adversarial responses (a codec guarantee). -/
def CacheNsCanon (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.records.toList, e.rr.type = BitVec.ofNat 16 2 →
    ∃ na, αName e.rr.rdata = some na
      ∧ e.rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
      ∧ na.length ≤ 127

/-- **`CacheNsCanon` discharges the keystone's `hrdcanon`** (over `lookupTopCred`). `lookupTopCred` returns the
    matching cached records (with adjusted TTL — rdata unchanged), so per-record NS-rdata canonicity lifts
    directly. Composes with `hhost_of_rdata_canonical` to give the full-walk keystone's `hhost`/`hnd`. -/
theorem hrdcanon_of_CacheNsCanon (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (h : CacheNsCanon c) :
    ∀ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
      (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2) = true →
      ∃ na, αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some na
        ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
            = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127 := by
  intro rr hmem hns
  rw [Cache.DnsCache.lookupTopCred, Array.toList_filterMap, List.mem_filterMap] at hmem
  obtain ⟨e, he, hsome⟩ := hmem
  split at hsome
  · rw [Option.some.injEq] at hsome
    subst hsome
    have hb : (e.rr.type == BitVec.ofNat 16 2) = true := hns
    have htype : e.rr.type = BitVec.ofNat 16 2 := by simpa using hb
    exact h e he htype
  · exact absurd hsome (by simp)

/-- **The CNAME-rdata-canonical cache invariant** — the type-5 twin of `CacheNsCanon`. Every cached CNAME
    record's stored rdata is a canonical wire name. A CNAME record absorbed from a `decodeRRCanonical`
    response blob has canonical rdata (`CanonicalRdata.nameType` covers `t = 5` exactly as it covers
    `t = 2`), so this invariant is maintainable for warm caches and adversarial responses alike. -/
def CacheCnameCanon (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.records.toList, e.rr.type = BitVec.ofNat 16 5 →
    ∃ na, αName e.rr.rdata = some na
      ∧ e.rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
      ∧ na.length ≤ 127

/-- **`CacheCnameCanon` discharges rdata canonicity over the ANSWERABLE lookup**
    (`TrustworthinessSpec.answers` for `DnsCache` is `lookupAnswerable` by the instance). `lookupAnswerable`
    returns matching cache entries' records with adjusted TTL — rdata and type unchanged — and the answerable
    filter pins each entry's type to the queried type 5, so per-entry CNAME-rdata canonicity lifts directly.
    The `answers`-side companion of `hrdcanon_of_CacheNsCanon`. -/
theorem cname_rdata_canonical_of_CacheCnameCanon (c : Cache.DnsCache) (sname : ByteArray)
    (qc : BitVec 16) (now : UInt32) (h : CacheCnameCanon c) :
    ∀ rr ∈ (VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) c sname (5 : BitVec 16) qc now).toList,
      ∃ na, αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some na
        ∧ VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr
            = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127 := by
  intro rr hmem
  rw [show VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) c sname (5 : BitVec 16) qc now
      = c.lookupAnswerable sname (5 : BitVec 16) qc now from rfl,
    Cache.DnsCache.lookupAnswerable, Array.toList_filterMap, List.mem_filterMap] at hmem
  obtain ⟨e, he, hsome⟩ := hmem
  split at hsome
  · rename_i hcond
    rw [Option.some.injEq] at hsome
    subst hsome
    have hcond' := hcond
    unfold VeriDNS.Impl.Cache.answerableEntry VeriDNS.Impl.Cache.liveEntry at hcond'
    simp only [Bool.and_eq_true] at hcond'
    have htyb : (e.rr.type == (5 : BitVec 16)) = true := hcond'.1.1.1.1.2
    have htype : e.rr.type = BitVec.ofNat 16 5 := by simpa using htyb
    exact h e he htype
  · exact absurd hsome (by simp)

/-- **`CacheNsCanon` preserved by `storeChecked`.** `storeChecked` is a no-op or a `store` (filter old + push new);
    old NS records keep canonicity (downward-closed under the filter), and the new record's NS-rdata canonicity is the
    per-record hypothesis `hnew` (discharged in the absorb caller from `canonicalRR_nsRdata_canonical`). -/
theorem CacheNsCanon_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsCanon c)
    (hnew : rr.type = BitVec.ofNat 16 2 →
      ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127) :
    CacheNsCanon (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := rfl
    intro e he hetype
    rw [hrec, Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [Array.toList_filter] at he
      exact h e (List.mem_filter.mp he).1 hetype
    · exact hnew hetype

/-- **`CacheCnameCanon` preserved by `storeChecked`** — the type-5 twin of `CacheNsCanon_storeChecked`.
    Old CNAME records keep canonicity (downward-closed under the store filter); the new record's CNAME-rdata
    canonicity is the per-record hypothesis `hnew` (dischargeable from `CanonicalRR` via the `t = 5` disjunct
    of `CanonicalRdata.nameType`). -/
theorem CacheCnameCanon_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheCnameCanon c)
    (hnew : rr.type = BitVec.ofNat 16 5 →
      ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
        ∧ na.length ≤ 127) :
    CacheCnameCanon (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := rfl
    intro e he hetype
    rw [hrec, Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [Array.toList_filter] at he
      exact h e (List.mem_filter.mp he).1 hetype
    · exact hnew hetype

/-- **`CacheNsCanon` preserved by a `parse-then-storeChecked` fold** (the list core of `absorb` preservation). -/
theorem CacheNsCanon_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheNsCanon cache →
      (∀ bytes ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 2 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) →
      CacheNsCanon (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) := by
  intro l
  induction l with
  | nil => intro cache hc _; exact hc
  | cons b bs ih =>
    intro cache hc hraw
    rw [List.foldl_cons]
    apply ih
    · cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => simp only [hp]; exact hc
      | some rr =>
        simp only [hp]
        exact CacheNsCanon_storeChecked cache rr cred now hc (hraw b (List.mem_cons_self ..) rr hp)
    · intro bytes hb rr hp; exact hraw bytes (List.mem_cons_of_mem _ hb) rr hp

/-- **`CacheCnameCanon` preserved by a `parse-then-storeChecked` fold** — the type-5 twin of
    `CacheNsCanon_foldl_storeChecked`. -/
theorem CacheCnameCanon_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheCnameCanon cache →
      (∀ bytes ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 5 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) →
      CacheCnameCanon (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) := by
  intro l
  induction l with
  | nil => intro cache hc _; exact hc
  | cons b bs ih =>
    intro cache hc hraw
    rw [List.foldl_cons]
    apply ih
    · cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => simp only [hp]; exact hc
      | some rr =>
        simp only [hp]
        exact CacheCnameCanon_storeChecked cache rr cred now hc (hraw b (List.mem_cons_self ..) rr hp)
    · intro bytes hb rr hp; exact hraw bytes (List.mem_cons_of_mem _ hb) rr hp

/-- **`CacheNsCanon` preserved by `cacheRRs`** (one section write). Bridges to the fold via `Array.foldl_toList`. -/
theorem CacheNsCanon_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 2 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheNsCanon (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheNsCanon_foldl_storeChecked cred now raws.toList cache h hraw

/-- **`CacheCnameCanon` preserved by `cacheRRs`** (one section write) — the type-5 twin of
    `CacheNsCanon_cacheRRs`. Bridges to the fold via `Array.foldl_toList`. -/
theorem CacheCnameCanon_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheCnameCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 5 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheCnameCanon (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheCnameCanon_foldl_storeChecked cred now raws.toList cache h hraw

/-- **`CacheNsCanon` preserved by `cacheUnlessTruncated`** — no-op (truncated) or a `cacheRRs` write. -/
theorem CacheNsCanon_cacheUnlessTruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 2 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheNsCanon (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]
    exact CacheNsCanon_cacheRRs cache _ cred now h
      (VeriDNS.Proof.NameTree.normRaws_forall_transfer (fun _ _ hP => hP) hraw)

/-- **`CacheCnameCanon` preserved by `cacheUnlessTruncated`** — the type-5 twin of
    `CacheNsCanon_cacheUnlessTruncated`: no-op (truncated) or a `cacheRRs` write. -/
theorem CacheCnameCanon_cacheUnlessTruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheCnameCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        rr.type = BitVec.ofNat 16 5 →
        ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63)
          ∧ na.length ≤ 127) :
    CacheCnameCanon (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]
    exact CacheCnameCanon_cacheRRs cache _ cred now h
      (VeriDNS.Proof.NameTree.normRaws_forall_transfer (fun _ _ hP => hP) hraw)

/-- **The NS-rdata-distinctness cache invariant.** No two cached records share an NS key (type 2, same owner CI +
    class) and the same rdata. The impl `store` dedups exactly this (its filter drops same-key-same-rdata entries
    before pushing), so it is maintainable — and it is what makes the cut's NS-rdata list `Nodup` (the keystone's
    `hnd`), the structural companion to `CacheNsCanon`'s canonicity. -/
def CacheNsDistinct (c : Cache.DnsCache) : Prop :=
  c.records.toList.Pairwise (fun e1 e2 =>
    ¬(e1.rr.type = BitVec.ofNat 16 2 ∧ e2.rr.type = BitVec.ofNat 16 2
      ∧ (VeriDNS.Impl.DomainName.nameEqCI e1.rr.name e2.rr.name) = true
      ∧ e1.rr.class = e2.rr.class ∧ e1.rr.rdata = e2.rr.rdata))

/-- **`CacheNsDistinct` preserved by `storeChecked`.** Either a no-op, or `filter old + push new`: the filter is a
    sublist (Pairwise preserved) and any kept same-NS-key entry has different rdata from the new record (else the
    store filter would have dropped it), so the appended record is distinct from all survivors. -/
theorem CacheNsDistinct_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsDistinct c) :
    CacheNsDistinct (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
            && (decide (e.expiry > now) || e.expiry == now + rr.ttl.toNat.toUInt32)
            && decide (e.credibility.toCode < cred.toCode)) = true
      · exact Or.inl (if_pos hb)
      · exact Or.inr (if_neg hb)
  rcases hcase with hc | hc
  · rw [hc]; exact h
  · rw [hc]
    have hrec : (c.store rr now cred).records
        = (c.records.filter fun e => !(VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name
            && e.rr.type == rr.type && e.rr.class == rr.class
            && (e.expiry != now + rr.ttl.toNat.toUInt32 || e.rr.rdata == rr.rdata))).push
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred⟩ := rfl
    show (((c.store rr now cred).records).toList).Pairwise _
    rw [hrec, Array.toList_push, List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [Array.toList_filter]
      exact h.filter _
    · intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      rw [Array.toList_filter, List.mem_filter] at ha
      obtain ⟨_, hap⟩ := ha
      rintro ⟨ht_a, ht_rr, hname, hclass, hrdata⟩
      have e1 : VeriDNS.Impl.DomainName.nameEqCI a.rr.name rr.name = true := hname
      have e2 : a.rr.type = rr.type := ht_a.trans ht_rr.symm
      have e3 : a.rr.class = rr.class := hclass
      have e4 : a.rr.rdata = rr.rdata := hrdata
      rw [e1, e2, e3, e4] at hap
      simp at hap
      have hself : (rr.rdata == rr.rdata) = true := by
        show ByteArray.beq rr.rdata rr.rdata = true
        unfold ByteArray.beq; simp
      rw [hself] at hap
      exact absurd hap.2 (by simp)

/-- **`CacheNsDistinct` preserved by a `parse-then-storeChecked` fold** — unconditional (the dedup is automatic). -/
theorem CacheNsDistinct_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheNsDistinct cache →
      CacheNsDistinct (l.foldl (fun c bytes =>
        match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
        | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
        | none => c) cache) := by
  intro l
  induction l with
  | nil => intro cache hc; exact hc
  | cons b bs ih =>
    intro cache hc
    rw [List.foldl_cons]
    apply ih
    cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none => simp only [hp]; exact hc
    | some rr => simp only [hp]; exact CacheNsDistinct_storeChecked cache rr cred now hc

/-- **`CacheNsDistinct` preserved by `cacheRRs`** (unconditional). -/
theorem CacheNsDistinct_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsDistinct cache) :
    CacheNsDistinct (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord) cache raws cred now
      = raws.toList.foldl (fun c bytes =>
          match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
          | some rr => VeriDNS.Impl.Cache.DnsCache.storeChecked c rr cred now
          | none => c) cache := by
    unfold VeriDNS.Impl.Resolver.cacheRRs
    rw [← Array.foldl_toList]
    congr 1
    funext c' b
    cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
  rw [heq]
  exact CacheNsDistinct_foldl_storeChecked cred now raws.toList cache h

/-- **`CacheNsDistinct` preserved by `cacheUnlessTruncated`** (unconditional). -/
theorem CacheNsDistinct_cacheUnlessTruncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheNsDistinct cache) :
    CacheNsDistinct (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]; exact CacheNsDistinct_cacheRRs cache _ cred now h

/-- **`CacheNsDistinct` preserved by a referral `absorb`** — unconditional (no provenance needed; the store's dedup
    maintains NS-rdata distinctness for any input). Threads the `hnd` invariant through the referral cache write. -/
theorem CacheNsDistinct_absorb (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray) (now : UInt32)
    (h : CacheNsDistinct cache) :
    CacheNsDistinct (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
        (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
        (VeriDNS.Impl.Resolver.credAuthority (resp.header.aa == 1)) now)
      resp (VeriDNS.Impl.Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
      VeriDNS.Impl.Resolver.credAdditional now) :=
  CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _
    (CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ h)

/-- **`filterMap` is `Nodup` when no two list elements map to the same `Some` value** (a `Pairwise` condition). -/
theorem nodup_filterMap_of_pairwise {α β : Type} (l : List α) (f : α → Option β)
    (h : l.Pairwise (fun a b => ∀ x, f a = some x → f b = some x → False)) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hhead, htail⟩ := h
    cases hfa : f a with
    | none => simp only [List.filterMap_cons, hfa]; exact ih htail
    | some b =>
      simp only [List.filterMap_cons, hfa, List.nodup_cons]
      refine ⟨?_, ih htail⟩
      intro hmem
      rw [List.mem_filterMap] at hmem
      obtain ⟨a', ha', hfa'⟩ := hmem
      exact hhead a' ha' b hfa hfa'

/-- **`CacheNsDistinct` discharges the keystone's `hnd`.** The cut's NS-rdata list (from `lookupTopCred`) is
    `Nodup`: composing the two `filterMap`s collapses to a single one over `c.records`; two surviving entries with
    the same rdata would both match the cut's NS key, so `CacheNsDistinct`'s `Pairwise` forbids it
    (`nodup_filterMap_of_pairwise`). The structural companion to `hrdcanon_of_CacheNsCanon`. -/
theorem hnd_of_CacheNsDistinct (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32)
    (h : CacheNsDistinct c) :
    ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).toList.Nodup := by
  rw [Array.toList_filterMap, Cache.DnsCache.lookupTopCred, Array.toList_filterMap,
      List.filterMap_filterMap]
  apply nodup_filterMap_of_pairwise
  have unpack : ∀ e : Cache.CacheEntry, ∀ y,
      ((if VeriDNS.Impl.Cache.liveEntry e cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
            && c.maxRankForKey e now then
          some { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } else none).bind
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)) = some y →
      VeriDNS.Impl.DomainName.nameEqCI e.rr.name cut = true ∧ e.rr.type = BitVec.ofNat 16 2
        ∧ e.rr.class = BitVec.ofNat 16 1 ∧ y = e.rr.rdata := by
    intro e y hy
    by_cases hcond : (VeriDNS.Impl.Cache.liveEntry e cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
        && c.maxRankForKey e now) = true
    · rw [if_pos hcond, Option.bind_some] at hy
      rw [Bool.and_eq_true] at hcond
      obtain ⟨hlive, _⟩ := hcond
      unfold VeriDNS.Impl.Cache.liveEntry at hlive
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hlive
      obtain ⟨⟨⟨hn, ht⟩, hcl⟩, _⟩ := hlive
      have hte : e.rr.type = BitVec.ofNat 16 2 := by simpa using ht
      have hcle : e.rr.class = BitVec.ofNat 16 1 := by simpa using hcl
      rw [if_pos (by show (e.rr.type == BitVec.ofNat 16 2) = true; rw [hte]; simp)] at hy
      rw [Option.some.injEq] at hy
      exact ⟨hn, hte, hcle, hy.symm⟩
    · rw [if_neg hcond, Option.bind_none] at hy
      exact absurd hy (by simp)
  refine List.Pairwise.imp ?_ h
  intro e1 e2 hne x hx1 hx2
  obtain ⟨hn1, ht1, hcl1, hy1⟩ := unpack e1 x hx1
  obtain ⟨hn2, ht2, hcl2, hy2⟩ := unpack e2 x hx2
  exact hne ⟨ht1, ht2, VeriDNS.Proof.NameTree.nameEqCI_trans hn1 (VeriDNS.Proof.NameTree.nameEqCI_symm hn2), hcl1.trans hcl2.symm, hy1 ▸ hy2⟩

/-- The empty cache satisfies `CacheNsCanon` (vacuously — no records). The cold-start base case for the driver. -/
theorem CacheNsCanon_empty : CacheNsCanon Cache.DnsCache.empty := by
  intro e he _
  simp [Cache.DnsCache.empty] at he

/-- The empty cache satisfies `CacheCnameCanon` (vacuously — no records). The type-5 twin of
    `CacheNsCanon_empty`; the cold-start base case for the driver. -/
theorem CacheCnameCanon_empty : CacheCnameCanon Cache.DnsCache.empty := by
  intro e he _
  simp [Cache.DnsCache.empty] at he

/-- The empty cache satisfies `CacheNsDistinct` (vacuously — the record list is empty). -/
theorem CacheNsDistinct_empty : CacheNsDistinct Cache.DnsCache.empty := by
  show (Cache.DnsCache.empty.records.toList).Pairwise _
  simp [Cache.DnsCache.empty]

/-- **`CacheNsCanon` preserved by `boundExpiryClasses`** (capacity eviction = a filter of the records, downward-
    closed). Needed because `afterResume` wraps the absorbed state in `boundStateCache` before recursing. -/
theorem CacheNsCanon_boundExpiryClasses (c : Cache.DnsCache) (h : CacheNsCanon c) :
    CacheNsCanon c.boundExpiryClasses := by
  intro e he htype
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1 htype

/-- **`CacheCnameCanon` preserved by `boundExpiryClasses`** — the type-5 twin of
    `CacheNsCanon_boundExpiryClasses` (capacity eviction = a filter of the records, downward-closed). -/
theorem CacheCnameCanon_boundExpiryClasses (c : Cache.DnsCache) (h : CacheCnameCanon c) :
    CacheCnameCanon c.boundExpiryClasses := by
  intro e he htype
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1 htype

/-- **`CacheNsDistinct` preserved by `boundExpiryClasses`** (eviction is a filter ⟹ a sublist; `Pairwise` survives). -/
theorem CacheNsDistinct_boundExpiryClasses (c : Cache.DnsCache) (h : CacheNsDistinct c) :
    CacheNsDistinct c.boundExpiryClasses := by
  show (c.boundExpiryClasses.records.toList).Pairwise _
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter]
  exact h.filter _

/-- **`filterMap` preserves emptiness when nothing is dropped.** If every element maps to `some`, then
    `(l.filterMap f).isEmpty = l.isEmpty`. The `walkNs` stop-condition ↔ `referralSlist` recursion alignment: the
    impl ascends when its NS lookup is empty, the model when `nsHostsAt` is empty; since every cached NS record
    abstracts (`αName` of its rdata is `some`, by the cache `WfRR` invariant), the two emptiness tests agree. -/
theorem isEmpty_filterMap_of_all_isSome {α β : Type} (l : List α) (f : α → Option β)
    (h : ∀ x ∈ l, (f x).isSome = true) : (l.filterMap f).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons a t =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    simp [List.filterMap_cons, hb]

/-- **`filterMap` distributes over `flatMap`** (no Mathlib here, proved from core). `(l.flatMap g).filterMap h
    = l.flatMap (fun x => (g x).filterMap h)`. Used to unfold `modelSlistOf` of the all-addresses `fromNsWithGlueAll`
    SLIST (a `flatMap` over NS names) into a per-name `flatMap`, matching the model `referralSlist`. -/
theorem filterMap_flatMap {α β γ : Type} (l : List α) (g : α → List β) (h : β → Option γ) :
    (l.flatMap g).filterMap h = l.flatMap (fun x => (g x).filterMap h) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, List.filterMap_append, ih]

/-- **`filterMap` then `flatMap` is a single `flatMap` over `Option.elim`.** `(l.filterMap f).flatMap g =
    l.flatMap (fun x => (f x).elim [] g)`. The keystone's NS-name `flatMap` bridge: `referralSlist`'s `flatMap` of
    `glueAddrsAt` over `nsHostsAt = nsNames.filterMap αName` equals the impl SLIST's per-`walkNs`-name `flatMap`. -/
theorem filterMap_then_flatMap {α β γ : Type} (l : List α) (f : α → Option β) (g : β → List γ) :
    (l.filterMap f).flatMap g = l.flatMap (fun x => (f x).elim [] g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hf : f a with
    | none => simp [List.filterMap_cons, hf, List.flatMap_cons, ih]
    | some b => simp [List.filterMap_cons, hf, List.flatMap_cons, ih]

/-- **`map` commutes through `filterMap`** — `(l.filterMap f).map g = l.filterMap (fun x => (f x).map g)`. Turns
    the impl per-host glue chain (`filterMap` size-4 pairs, then `map Prod.snd`, then `map` to the model string)
    into a single `filterMap`, ready to reconcile with `glueAddrsAt` via `a_extract_reconcile`. -/
theorem filterMap_map_comm {α β γ : Type} (l : List α) (f : α → Option β) (g : β → γ) :
    (l.filterMap f).map g = l.filterMap (fun x => (f x).map g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hf : f a with
    | none => simp [List.filterMap_cons, hf, ih]
    | some b => simp [List.filterMap_cons, hf, ih]

/-- **The impl all-pairs glue per source NS name is keyed by that name** — every pair `stepFindServers` emits
    for host `m` has first component `m`. The `hkey` hypothesis of `keyed_glue_filterMap_self` for the impl glue. -/
theorem mkGlue_keyed (aRRs : Array VeriDNS.Spec.ResourceRecord) (m : ByteArray) :
    ∀ gp ∈ ((aRRs.filterMap (fun rr =>
        if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
          some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
            (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
        else none)).toList), gp.1 = m := by
  intro gp hgp
  rw [Array.toList_filterMap, List.mem_filterMap] at hgp
  obtain ⟨rr, _, heq⟩ := hgp
  by_cases hsz : ((VeriDNS.Spec.RRParse.rrRdata rr).size == 4) = true
  · rw [if_pos hsz] at heq; injection heq with heq; rw [← heq]
  · rw [if_neg hsz] at heq; exact absurd heq.symm (by simp)

/-- **Per-host impl glue addresses = the model `αIPv4`/`toDotted` extraction.** The impl's all-pairs glue for one
    NS host is `aRRs.filterMap (size4 → (n, pack))`; taking `Prod.snd` and mapping to the model string equals
    `aRRs.filterMap (αIPv4 rdata |>.map toDotted)` — the model `glueAddrsAt`-shaped extraction. Composes
    `filterMap_map_comm` (collapse the map chain) with the per-record bridge `a_extract_reconcile`. -/
theorem impl_glue_per_name_model (aRRs : Array VeriDNS.Spec.ResourceRecord) (n : ByteArray) :
    (((aRRs.filterMap (fun rr =>
        if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
          some (n, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
            ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
            (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
        else none)).toList.map Prod.snd).map
      (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))
      = aRRs.toList.filterMap (fun rr =>
          (αIPv4 (VeriDNS.Spec.RRParse.rrRdata rr)).map (fun ip => ip.toDotted)) := by
  rw [Array.toList_filterMap, List.map_map, filterMap_map_comm]
  apply filterMap_congr_mem
  intro rr _
  rw [a_extract_reconcile]
  by_cases hsz : ((VeriDNS.Spec.RRParse.rrRdata rr).size == 4) = true
  · simp [hsz, Function.comp_apply]
  · simp only [Bool.not_eq_true] at hsz; simp [hsz]

/-- **`ByteArray` `==` reflects `=`** (public version of `NameTreeComplete.byteArray_beq_iff`). `ByteArray` has no
    `LawfulBEq` instance, but its `BEq` (over `.data`, an `Array UInt8` with `LawfulBEq`) is lawful — provable via
    `ByteArray.ext`. Supplies the `hbeq` hypothesis of `keyed_glue_filterMap_self`/`flatMap_indicator_self` for the
    exact-keyed glue. -/
theorem byteArray_beq_iff_eq {a b : ByteArray} : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    apply ByteArray.ext
    show a.data = b.data
    have : ByteArray.beq a b = true := h
    unfold ByteArray.beq at this
    simpa using this
  · intro h
    subst h
    show ByteArray.beq a a = true
    unfold ByteArray.beq
    simp

/-- **`flatMap` of an exact-match indicator collapses to the matched element** (under `Nodup`). For `n ∈ l` with
    `l` nodup, `l.flatMap (fun m => if m == n then g m else []) = g n` — every other element fails the exact match
    and contributes `[]`. The per-host keystone extraction: the all-pairs glue, keyed by exact NS name, yields a
    given host its own addresses ONCE (no over-count) when the NS-name list is duplicate-free. `==`↔`=` is taken
    as a hypothesis (`ByteArray` is provably lawful via `ByteArray.ext`, but has no `LawfulBEq` instance). -/
theorem flatMap_indicator_self {α β : Type} [BEq α] (l : List α) (n : α) (g : α → List β)
    (hbeq : ∀ a b : α, (a == b) = true ↔ a = b) (hn : n ∈ l) (hnd : l.Nodup) :
    l.flatMap (fun m => if m == n then g m else []) = g n := by
  induction l with
  | nil => exact absurd hn (by simp)
  | cons a t ih =>
    obtain ⟨hat, hnt'⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp hn with rfl | hnt
    · rw [if_pos ((hbeq n n).mpr rfl)]
      have htail : t.flatMap (fun m => if m == n then g m else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro m hm
        rw [if_neg (fun hc => hat (((hbeq m n).mp hc) ▸ hm))]
      rw [htail, List.append_nil]
    · rw [if_neg (fun hc => hat (((hbeq a n).mp hc) ▸ hnt)), List.nil_append]
      exact ih hnt hnt'

/-- **Per-host extraction from the keyed all-pairs glue** (the keystone's per-host collapse). The impl all-pairs
    glue is `names.flatMap h` where `h m` is keyed by `m` (`gp.1 = m`); filtering for host `n` (exact `==`) under
    `Nodup names` with `n ∈ names` yields exactly `n`'s own glue values, once. Composes `filterMap_flatMap` (split
    the flatMap), the per-source constant-condition reduction (`hkey`), and `flatMap_indicator_self` (`Nodup`
    collapse). This is what turns `modelSlistOf(fromNsWithGlueAll)`'s per-name glue into the host's cache-A set. -/
theorem keyed_glue_filterMap_self {β : Type} (names : Array ByteArray) (n : ByteArray)
    (h : ByteArray → Array (ByteArray × β))
    (hkey : ∀ m, ∀ gp ∈ (h m).toList, gp.1 = m)
    (hbeq : ∀ a b : ByteArray, (a == b) = true ↔ a = b)
    (hn : n ∈ names.toList) (hnd : names.toList.Nodup) :
    ((names.flatMap h).filterMap (fun gp => if gp.1 == n then some gp.2 else none)).toList
      = (h n).toList.map Prod.snd := by
  rw [Array.toList_filterMap, Array.toList_flatMap, filterMap_flatMap]
  have hperm : (fun m => (h m).toList.filterMap (fun gp => if gp.1 == n then some gp.2 else none))
      = (fun m => if m == n then (h m).toList.map Prod.snd else []) := by
    funext m
    by_cases hmn : (m == n) = true
    · rw [if_pos hmn, ← List.filterMap_eq_map]
      apply filterMap_congr_mem
      intro gp hgp
      simp [hkey m gp hgp, hmn, Function.comp_apply]
    · rw [if_neg hmn]
      apply List.filterMap_eq_nil_iff.mpr
      intro gp hgp
      rw [hkey m gp hgp, if_neg hmn]
  rw [hperm]
  exact flatMap_indicator_self names.toList n (fun m => (h m).toList.map Prod.snd) hbeq hn hnd

/-- **Per-host filter of a keyed all-pairs glue list reduces to a per-source `flatMap`.** The impl's all-pairs
    glue (`stepFindServers`) is `nsNames.flatMap (mkGlue)` where every pair `mkGlue m` produces is keyed by `m`
    (`gp.1 = key m`). Filtering for host `n` (`nameEqCI gp.1 n`) therefore collects, per source `m`, all of `m`'s
    glue values exactly when `nameEqCI (key m) n` — the all-pairs analogue of `rederived_glue_keyed`. -/
theorem flatMap_glue_keyed {α β : Type} (l : List α) (h : α → List (ByteArray × β)) (n : ByteArray)
    (key : α → ByteArray) (hkey : ∀ m, ∀ gp ∈ h m, gp.1 = key m) :
    (l.flatMap h).filterMap (fun gp => if VeriDNS.Impl.DomainName.nameEqCI gp.1 n then some gp.2 else none)
      = l.flatMap (fun m =>
          if VeriDNS.Impl.DomainName.nameEqCI (key m) n then (h m).map Prod.snd else []) := by
  rw [filterMap_flatMap]
  congr 1
  funext m
  by_cases hk : VeriDNS.Impl.DomainName.nameEqCI (key m) n = true
  · rw [if_pos hk, ← List.filterMap_eq_map]
    apply filterMap_congr_mem
    intro gp hgp
    rw [hkey m gp hgp]; simp [hk]
  · rw [if_neg hk]
    apply List.filterMap_eq_nil_iff.mpr
    intro gp hgp
    rw [hkey m gp hgp]
    simp only [Bool.not_eq_true] at hk
    simp [hk]

/-- The byte-`==`-keyed per-host glue flatMap — the OLD `modelSlistOf (fromNsWithGlueAll …)` shape, before
    the case-fold fix. Kept as an explicit expression so the keystone chain (which reasons about the per-host
    byte-exact glue) is unchanged, and only a Subperm bridge (`nsGlueByteFlat_sublist_fold`) connects it to the
    new case-insensitive `modelSlistOf`. -/
def nsGlueByteFlat (names : Array ByteArray) (glue : Array (ByteArray × BitVec 32)) : List String :=
  names.toList.flatMap (fun n =>
    (glue.filterMap (fun gp => if gp.1 == n then some gp.2 else none)).toList.map
      (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)))

/-- **Structural unfold of `modelSlistOf` on a `fromNsWithGlueAll` SLIST** (all-addresses, now case-folded
    per host). -/
theorem modelSlistOf_fromNsWithGlueAll (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc)
      = names.toList.flatMap (fun n =>
          (glue.filterMap (fun gp => if DomainName.foldNameCase gp.1 == DomainName.foldNameCase n then some gp.2 else none)).toList.map
            (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))) := by
  unfold modelSlistOf VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll
  dsimp only
  rw [Array.toList_flatMap, filterMap_flatMap]
  congr 1
  funext n
  by_cases hemp : (glue.filterMap (fun gp =>
      if DomainName.foldNameCase gp.1 == DomainName.foldNameCase n then some gp.2 else none)).isEmpty = true
  · rw [if_pos hemp]; simp [Array.isEmpty_iff.mp hemp]
  · rw [if_neg hemp, Array.toList_map, List.filterMap_map]; simp [Function.comp_def]

/-- **Byte-keyed glue ⊆ case-folded glue** (per host `n`): a byte-`==` glue match implies the case-folded
    match (`foldNameCase` is a function), so the old byte-exact per-host glue is a `Sublist` of the new
    case-insensitive `modelSlistOf`. This is all the driver needs: `referralSlist = nsGlueByteFlat ⊆
    modelSlistOf(fold)`, so the model SLIST is a Subperm of the impl's — the case-fold fix only ADDS
    (never drops) glue, preserving the refinement. -/
theorem nsGlueByteFlat_sublist_fold (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    (nsGlueByteFlat names glue).Sublist (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc)) := by
  rw [modelSlistOf_fromNsWithGlueAll]
  unfold nsGlueByteFlat

  have hflat : ∀ (l : List ByteArray) (F G : ByteArray → List String),
      (∀ x ∈ l, (F x).Sublist (G x)) → (l.flatMap F).Sublist (l.flatMap G) := by
    intro l F G h
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons]
      exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))
  have hfm : ∀ {α β : Type} (P Q : α → Option β) (l : List α),
      (∀ a b, P a = some b → Q a = some b) → (List.filterMap P l).Sublist (List.filterMap Q l) := by
    intro α β P Q l h
    induction l with
    | nil => simp
    | cons a t ih =>
      cases hp : P a with
      | none =>
        rw [List.filterMap_cons_none hp]
        cases hq : Q a with
        | none => rw [List.filterMap_cons_none hq]; exact ih
        | some b => rw [List.filterMap_cons_some hq]; exact ih.cons _
      | some b =>
        rw [List.filterMap_cons_some hp, List.filterMap_cons_some (h a b hp)]
        exact ih.cons_cons _
  apply hflat
  intro n _
  refine List.Sublist.map _ ?_
  rw [Array.toList_filterMap, Array.toList_filterMap]
  apply hfm
  intro gp b hgp
  by_cases hbe : (gp.1 == n) = true
  · have heq : gp.1 = n := byteArray_beq_iff_eq.mp hbe
    rw [if_pos hbe] at hgp
    injection hgp with hgpb
    rw [heq, hgpb, if_pos (byteArray_beq_iff_eq.mpr rfl)]
  · rw [if_neg hbe] at hgp; exact absurd hgp (by simp)

/-- `findSome?`'s single result is a `Sublist` of `filterMap`'s full list (same predicate): the first `some`
    is the head of the collected `some`s. -/
theorem findSome?_toList_sublist_filterMap {α β : Type} (p : α → Option β) (l : List α) :
    (l.findSome? p).toList.Sublist (l.filterMap p) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.findSome?_cons, List.filterMap_cons]
    cases hp : p a with
    | none => simp only [hp]; exact ih
    | some b => simp only [hp, Option.toList_some]; exact (List.nil_sublist _).cons_cons b

/-- `filterMap` as a `flatMap` of the per-element option's `toList`. -/
theorem filterMap_eq_flatMap_toList {α β : Type} (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap (fun a => (f a).toList) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons, List.flatMap_cons, ih]
    cases f a <;> simp

/-- **`fromNsWithGlue` (one address per host) refines `fromNsWithGlueAll` (all addresses per host).** Both use
    the SAME case-insensitive glue match (`nameEqCI` = `foldNameCase ==` definitionally); the `findSome?`-first
    picks one of the `filterMap`-all matches, so the one-per-host model SLIST is a `Subperm` of the all-addresses
    one. This is what lets the response-transient (ttl-0) SLIST — `fromNsWithGlueAll` — refine the model
    `glueAddresses` (one-per-host): `glueAddresses = modelSlistOf(fromNsWithGlue) ⊆ modelSlistOf(fromNsWithGlueAll)`. -/
theorem modelSlistOf_fromNsWithGlue_subperm_all (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc mc' : Nat) :
    (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glue mc)).Subperm
      (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll names glue mc')) := by
  rw [modelSlistOf_fromNsWithGlue, modelSlistOf_fromNsWithGlueAll, filterMap_eq_flatMap_toList]
  refine List.Sublist.subperm ?_
  have hflat : ∀ (l : List ByteArray) (F G : ByteArray → List String),
      (∀ x ∈ l, (F x).Sublist (G x)) → (l.flatMap F).Sublist (l.flatMap G) := by
    intro l F G h
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons]
      exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))
  apply hflat
  intro n _

  have hP : (fun (gp : ByteArray × BitVec 32) =>
      if VeriDNS.Impl.DomainName.nameEqCI gp.1 n then some gp.2 else none)
      = (fun gp => if DomainName.foldNameCase gp.1 == DomainName.foldNameCase n then some gp.2 else none) := rfl
  have hom : ∀ (o : Option (BitVec 32)),
      (o.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))).toList
        = o.toList.map (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a)) := by
    intro o; cases o <;> rfl
  rw [hP, hom, ← Array.findSome?_toList, Array.toList_filterMap]
  refine List.Sublist.map _ ?_
  exact findSome?_toList_sublist_filterMap _ _

/-- **A-rdata (glue) abstraction bridge.** If an impl record `rr` abstracts to a model `r` whose rdata is
    `.a addr`, then the impl's rdata bytes `rrRdata rr` `αIPv4`-abstract to `addr`. The value-level half of the
    glue extraction correspondence (`walkNs`-glue ↔ `glueAddrsAt`), parallel to `αName_rrRdata_of_ns`. -/
theorem αIPv4_rrRdata_of_a (rr : VeriDNS.Spec.ResourceRecord) (r : VeriDNS.Spec.Net.RR)
    (addr : VeriDNS.Spec.Net.IPv4)
    (harr : αRR rr = some r) (ha : r.rdata = VeriDNS.Spec.Net.RData.a addr) :
    αIPv4 (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) = some addr := by
  unfold αRR at harr
  split at harr
  · rename_i owner rdata cls hn hrd hcl
    injection harr with harr
    have hrdata : rdata = VeriDNS.Spec.Net.RData.a addr := by rw [← harr] at ha; exact ha
    rw [hrdata] at hrd
    show αIPv4 rr.rdata = some addr
    unfold αRData at hrd
    split at hrd
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, hx1, hx⟩ := hrd
      injection hx with hx; subst hx; exact hx1
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · rw [Option.map_eq_some_iff] at hrd; obtain ⟨x, _, hx⟩ := hrd; exact absurd hx (by simp)
    · simp at hrd
  · simp at harr

/-- **NS extraction correspondence (`lookupTopCred`-NS ↔ `nsHostsAt`).** The impl's cred-aware SLIST NS read,
    with each selected record's rdata abstracted via `αName`, equals the model's `nsHostsAt` (the cache-re-derived
    NS host set). Composes the impl-side fusion (`lookupTopCred_toList_filterMap`), the per-element gate equality
    (`cond_eq_top`), and the NS-rdata value bridge (`αName_rrRdata_of_ns`) — the SLIST analogue of
    `lookupAnswerable_αRR_eq_hit`, at the rdata (ttl-irrelevant) level. -/
theorem lookupTopCred_ns_eq_nsHostsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns,
      RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList.filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)
      = (αCache c).nsHostsAt (αTime now) q.qname := by
  have ht : αType (BitVec.ofNat 16 2) = some RRType.ns := rfl
  have hqq : q.qtype = VeriDNS.Spec.Net.QType.rr RRType.ns := by rw [hq4]
  have hqc : αClass (BitVec.ofNat 16 1) = some q.qclass := by rw [hq4]; rfl
  rw [lookupTopCred_toList_filterMap]
  unfold VeriDNS.Spec.Net.Cache.nsHostsAt
  rw [show (⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns,
        RRClass.in, false⟩ : VeriDNS.Spec.Net.Query) = q from hq4.symm,
      VeriDNS.Spec.Net.Cache.topServed]
  generalize hsp : (fun (e : VeriDNS.Spec.Net.CacheRR) =>
      ((αCache c).matching (αTime now) q).all
        (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) = sp
  rw [filter_filterMap_eq, VeriDNS.Spec.Net.Cache.matching,
      filter_filterMap_eq, show (αCache c).pos = c.records.toList.filterMap αCacheRR from rfl,
      List.filterMap_filterMap]
  subst hsp
  apply filterMap_congr_mem
  intro e he
  have he' : e ∈ c.records := Array.mem_def.mpr he
  obtain ⟨hane, hle, hmono⟩ := hwf e he'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
  rw [ha, Option.bind_some]
  have hce := cond_eq_top c name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now q
    RRType.ns hqn ht hqq hqc hcanN hvN hwf hcanon hused e he' a ha
  by_cases hgate : (Cache.liveEntry e name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now
      && c.maxRankForKey e now) = true
  ·
    have htype : (e.rr.type == BitVec.ofNat 16 2) = true := by
      rw [Bool.and_eq_true] at hgate
      have hl := hgate.1; unfold Cache.liveEntry at hl
      simp only [Bool.and_eq_true] at hl; exact hl.1.1.2

    have harr : αRR e.rr = some a.rr := by
      unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
      obtain ⟨r, hr, rfl⟩ := ha; exact hr
    have hrt := αRR_rtype e.rr a.rr harr
    have hnsrd : ∃ h, a.rr.rdata = VeriDNS.Spec.Net.RData.ns h := by
      have hrtns : a.rr.rdata.rtype = RRType.ns := by
        have heqt : e.rr.type = BitVec.ofNat 16 2 := eq_of_beq htype
        rw [heqt, ht] at hrt
        exact (Option.some.inj hrt).symm
      cases hrd : a.rr.rdata with
      | ns h => exact ⟨h, rfl⟩
      | _ => rw [hrd] at hrtns; simp [VeriDNS.Spec.Net.RData.rtype] at hrtns
    obtain ⟨h, hh⟩ := hnsrd
    rw [if_pos hgate, if_pos (show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord)
          { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } == BitVec.ofNat 16 2)
        = true from htype)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = true := hce ▸ hgate
    rw [Bool.and_eq_true] at hmodel
    obtain ⟨hmp, hsp⟩ := hmodel
    simp only [hmp, hsp, cond_true, hh]
    exact αName_rrRdata_of_ns e.rr a.rr h harr hh
  · rw [Bool.not_eq_true] at hgate
    rw [if_neg (by rw [hgate]; simp)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = false := hce ▸ hgate
    rcases Bool.and_eq_false_iff.mp hmodel with h | h <;> simp [h]

/-- **Intermediate-node empty correspondence** (the chain-alignment half of the full-walk keystone). When the
    impl's credibility-aware NS read is empty at `name` (so `walkNs` ASCENDS past it), the model's `nsHostsAt` is
    also empty there (so the model `referralSlist` ascends too) — both walks skip the same intermediate nodes.
    Immediate from `lookupTopCred_ns_eq_nsHostsAt`: `nsHostsAt = (empty array).toList.filterMap … = []`. This
    translates `walkNs_ascend`'s impl-side empties into `referralSlist_ascend`'s model-side empties, the bridge
    that lets the per-cut `keystone_at_cut` lift through the full delegation-depth ascent. -/
theorem nsHostsAt_empty_of_lookupTopCred_empty (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (he : (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true) :
    ((αCache c).nsHostsAt (αTime now) q.qname).isEmpty = true := by
  have heq := lookupTopCred_ns_eq_nsHostsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused
  rw [← heq]
  have hnil : (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now) = #[] := by
    simpa using he
  rw [hnil]
  rfl

/-- **Cut-node non-empty correspondence** (the dual of `nsHostsAt_empty_of_lookupTopCred_empty`, for
    `referralSlist_ascend`'s `hcut`). If some cached NS record at the cut has an abstracting target name (`hone`
    — true at a real delegation cut whose NS hosts are canonical, RFC 1035 wire), the model `nsHostsAt` there is
    non-empty, so the model walk STOPS at the same cut the impl `walkNs` does. With the intermediate-empty bridge
    this pins both walks to the identical cut. -/
theorem nsHostsAt_nonempty_of_lookupTopCred (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hone : ∃ rr ∈ (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none) :
    ((αCache c).nsHostsAt (αTime now) q.qname).isEmpty = false := by
  have heq := lookupTopCred_ns_eq_nsHostsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused
  rw [← heq]
  obtain ⟨rr, hrr, hg⟩ := hone
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hg
  have hmem : b ∈ (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList.filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) :=
    List.mem_filterMap.mpr ⟨rr, hrr, hb⟩
  cases hl : (c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList.filterMap
      (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
        then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) with
  | nil => rw [hl] at hmem; exact absurd hmem (by simp)
  | cons x xs => rfl

/-- **Model-walk empties from impl-walk empties** (maps `nsHostsAt_empty_of_lookupTopCred_empty` over the chain's
    intermediate nodes). Each impl node `m` with an empty NS read and canonical name abstracts to a model node
    `(αName m).getD []` with empty `nsHostsAt`. So `walkNs_ascend`'s impl intermediates become
    `referralSlist_ascend`'s model intermediates wholesale. -/
theorem model_empties_of_impl (c : Cache.DnsCache) (now : UInt32)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (nodes : List ByteArray)
    (hcanonNode : ∀ m ∈ nodes, ∃ na, αName m = some na ∧ m = DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63))
    (himpl_empty : ∀ m ∈ nodes,
        (c.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true) :
    ∀ mm ∈ nodes.map (fun w => (αName w).getD []),
      ((αCache c).nsHostsAt (αTime now) mm).isEmpty = true := by
  intro mm hmm
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hmm
  obtain ⟨na, hαm, hcanM, hvM⟩ := hcanonNode m hm
  rw [show (αName m).getD [] = na from by simp [hαm]]
  exact nsHostsAt_empty_of_lookupTopCred_empty c m now
    ⟨na, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩ hαm rfl hcanM hvM hwf hcanon hused
    (himpl_empty m hm)

/-- **`walkNs` NS-name list abstracts to `nsHostsAt`.** The impl's extracted NS names — `lookupTopCred cut NS`
    filtered to NS records' rdata — `αName`-abstract (as a list) to the model's `nsHostsAt`. Composes the
    `filterMap`/`bind` fusion with `lookupTopCred_ns_eq_nsHostsAt`. This is the NS-name half of the keystone:
    `referralSlist`'s `flatMap` over `nsHostsAt` = the impl SLIST's `flatMap` over `walkNs` names (mapped through
    `αName`), so the two SLISTs coincide. -/
theorem walkNs_nsNames_αName_eq_nsHostsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (((c.lookupTopCred name (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.filterMap αName)
      = (αCache c).nsHostsAt (αTime now) q.qname := by
  rw [Array.toList_filterMap, List.filterMap_filterMap,
      ← lookupTopCred_ns_eq_nsHostsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused]
  apply filterMap_congr_mem
  intro rr _
  by_cases hrt : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2) = true
  · simp [hrt]
  · simp only [Bool.not_eq_true] at hrt; simp [hrt]

/-- **Glue extraction correspondence (`lookupTopCred`-A ↔ `glueAddrsAt`).** The `αIPv4`/`toDotted` analog of
    `lookupTopCred_ns_eq_nsHostsAt`: the impl's cred-aware SLIST A read, each selected record's rdata abstracted
    via `αIPv4` then `toDotted`, equals the model's `glueAddrsAt` (all cached glue addresses per host, at per-key
    max credibility). Same structure as the NS correspondence, via `cond_eq_top` + `αIPv4_rrRdata_of_a`. -/
theorem lookupTopCred_a_eq_glueAddrsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupTopCred name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).toList.filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 1
          then (αIPv4 (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)).map
            (fun ip => ip.toDotted)
          else none)
      = (αCache c).glueAddrsAt (αTime now) q.qname := by
  have ht : αType (BitVec.ofNat 16 1) = some RRType.a := rfl
  have hqq : q.qtype = VeriDNS.Spec.Net.QType.rr RRType.a := by rw [hq4]
  have hqc : αClass (BitVec.ofNat 16 1) = some q.qclass := by rw [hq4]; rfl
  rw [lookupTopCred_toList_filterMap]
  unfold VeriDNS.Spec.Net.Cache.glueAddrsAt
  rw [show (⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩
        : VeriDNS.Spec.Net.Query) = q from hq4.symm, VeriDNS.Spec.Net.Cache.topServed]
  generalize hsp : (fun (e : VeriDNS.Spec.Net.CacheRR) =>
      ((αCache c).matching (αTime now) q).all
        (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank)) = sp
  rw [filter_filterMap_eq, VeriDNS.Spec.Net.Cache.matching,
      filter_filterMap_eq, show (αCache c).pos = c.records.toList.filterMap αCacheRR from rfl,
      List.filterMap_filterMap]
  subst hsp
  apply filterMap_congr_mem
  intro e he
  have he' : e ∈ c.records := Array.mem_def.mpr he
  obtain ⟨hane, hle, hmono⟩ := hwf e he'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
  rw [ha, Option.bind_some]
  have hce := cond_eq_top c name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now q
    RRType.a hqn ht hqq hqc hcanN hvN hwf hcanon hused e he' a ha
  by_cases hgate : (Cache.liveEntry e name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now
      && c.maxRankForKey e now) = true
  · have htype : (e.rr.type == BitVec.ofNat 16 1) = true := by
      rw [Bool.and_eq_true] at hgate
      have hl := hgate.1; unfold Cache.liveEntry at hl
      simp only [Bool.and_eq_true] at hl; exact hl.1.1.2
    have harr : αRR e.rr = some a.rr := by
      unfold αCacheRR at ha; rw [Option.map_eq_some_iff] at ha
      obtain ⟨r, hr, rfl⟩ := ha; exact hr
    have hrt := αRR_rtype e.rr a.rr harr
    have hard : ∃ addr, a.rr.rdata = VeriDNS.Spec.Net.RData.a addr := by
      have hrta : a.rr.rdata.rtype = RRType.a := by
        have heqt : e.rr.type = BitVec.ofNat 16 1 := eq_of_beq htype
        rw [heqt, ht] at hrt
        exact (Option.some.inj hrt).symm
      cases hrd : a.rr.rdata with
      | a addr => exact ⟨addr, rfl⟩
      | _ => rw [hrd] at hrta; simp [VeriDNS.Spec.Net.RData.rtype] at hrta
    obtain ⟨addr, hh⟩ := hard
    rw [if_pos hgate, if_pos (show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord)
          { e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } == BitVec.ofNat 16 1)
        = true from htype)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = true := hce ▸ hgate
    rw [Bool.and_eq_true] at hmodel
    obtain ⟨hmp, hsp⟩ := hmodel
    simp only [hmp, hsp, cond_true, hh]
    show (αIPv4 (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) e.rr)).map
        (fun ip => ip.toDotted) = some addr.toDotted
    rw [αIPv4_rrRdata_of_a e.rr a.rr addr harr hh]; rfl
  · rw [Bool.not_eq_true] at hgate
    rw [if_neg (by rw [hgate]; simp)]
    have hmodel : ((a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass))
          && ((αCache c).matching (αTime now) q).all
            (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank)) = false := hce ▸ hgate
    rcases Bool.and_eq_false_iff.mp hmodel with h | h <;> simp [h]

/-- **Glue extraction correspondence WITHOUT the `rrType==1` guard** — the form the impl all-pairs glue chain
    produces. Every `lookupTopCred`-A record has `rrType == 1` (`mem_lookupTopCred_rrType`), so the guard is
    redundant; dropping it joins `impl_glue_per_name_model` to `lookupTopCred_a_eq_glueAddrsAt`. -/
theorem lookupTopCred_a_noguard_eq_glueAddrsAt (c : Cache.DnsCache) (name : ByteArray) (now : UInt32)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName name = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupTopCred name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).toList.filterMap
        (fun rr => (αIPv4 (VeriDNS.Spec.RRParse.rrRdata rr)).map (fun ip => ip.toDotted))
      = (αCache c).glueAddrsAt (αTime now) q.qname := by
  rw [← lookupTopCred_a_eq_glueAddrsAt c name now q hqn hq4 hcanN hvN hwf hcanon hused]
  apply filterMap_congr_mem
  intro rr hrr
  rw [if_pos (mem_lookupTopCred_rrType c name (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now rr
    (Array.mem_def.mpr hrr))]

/-- **Per-host glue keystone.** For one NS host `n` (in the `Nodup` `walkNs` name list), the impl all-pairs glue
    filtered to `n`, mapped to model strings, equals the model `glueAddrsAt(αName n)`. Composes the per-host
    collapse (`keyed_glue_filterMap_self`, discharging `hkey` via `mkGlue_keyed` and `hbeq` via
    `byteArray_beq_iff_eq`), the glue value chain (`impl_glue_per_name_model`), and the guard-dropped extraction
    correspondence (`lookupTopCred_a_noguard_eq_glueAddrsAt`). One `flatMap` summand of the keystone-at-a-cut. -/
theorem per_host_glue (c : Cache.DnsCache) (now : UInt32) (nsNames : Array ByteArray) (n : ByteArray)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName n = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩)
    (hcanN : n = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hn : n ∈ nsNames.toList) (hnd : nsNames.toList.Nodup) :
    ((nsNames.flatMap (fun m =>
        (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
          if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
            some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
              (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
          else none))).filterMap
        (fun gp => if gp.1 == n then some gp.2 else none)).toList.map
      (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))
      = (αCache c).glueAddrsAt (αTime now) q.qname := by
  rw [keyed_glue_filterMap_self nsNames n
        (fun m => (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
          if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
            some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
              ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
              (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
          else none))
        (fun m => mkGlue_keyed _ m) (fun _ _ => byteArray_beq_iff_eq) hn hnd,
      impl_glue_per_name_model (c.lookupTopCred n (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now) n]
  exact lookupTopCred_a_noguard_eq_glueAddrsAt c n now q hqn hq4 hcanN hvN hwf hcanon hused

/-- **Keystone glue assembly.** The model image of the impl re-derived SLIST (`fromNsWithGlueAll` of the
    `Nodup` `walkNs` names + their all-pairs glue) equals `(nsNames.filterMap αName).flatMap glueAddrsAt` — i.e.
    the model `referralSlist`'s `flatMap glueAddrsAt` over the abstracted NS hosts. Composes
    `modelSlistOf_fromNsWithGlueAll`, `filterMap_then_flatMap`, and `per_host_glue` per host (via
    `flatMap_congr_mem`). The `hhost` hypothesis bundles the per-host abstractability + canonicity. -/
theorem keystone_glue_assembly (c : Cache.DnsCache) (now : UInt32) (nsNames : Array ByteArray) (mc : Nat)
    (hnd : nsNames.toList.Nodup)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hhost : ∀ n ∈ nsNames.toList, ∃ qn, αName n = some qn
        ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63)) :
    nsGlueByteFlat nsNames
        (nsNames.flatMap (fun m =>
          (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
            if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
              some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
                (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
            else none)))
      = (nsNames.toList.filterMap αName).flatMap ((αCache c).glueAddrsAt (αTime now)) := by
  unfold nsGlueByteFlat
  rw [filterMap_then_flatMap]
  apply flatMap_congr_mem
  intro n hn
  obtain ⟨qn, hqn, hcanN, hvN⟩ := hhost n hn
  rw [hqn]
  exact per_host_glue c now nsNames n ⟨qn, VeriDNS.Spec.Net.QType.rr RRType.a, RRClass.in, false⟩
    hqn rfl hcanN hvN hwf hcanon hused hn hnd

/-- **Model `referralSlist` base case.** At a cut with cached NS (`nsHostsAt` nonempty), the model walk stops
    and returns `nsHostsAt.flatMap glueAddrsAt` — exactly `keystone_at_cut`'s RHS. The model-side companion that
    lets the per-cut keystone conclude `modelSlistOf(impl re-derived) = referralSlist(c, cut, fuel+1)`. -/
theorem referralSlist_base (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (nm : VeriDNS.Spec.Net.Name) (fuel : Nat) (h : (c.nsHostsAt now nm).isEmpty = false) :
    c.referralSlist now nm (fuel + 1) = (c.nsHostsAt now nm).flatMap (c.glueAddrsAt now) := by
  unfold VeriDNS.Spec.Net.Cache.referralSlist
  rw [if_neg (by rw [h]; simp)]

/-- **Model `referralSlist` one-hop ascent.** When `start` has no cached NS but its parent (`tail`) `cut` does,
    the model walk ascends once and returns `nsHostsAt(cut).flatMap glueAddrsAt`. Because the RHS is the base
    `flatMap` (not a `referralSlist` call), `unfold` only touches the LHS — sidestepping the WF folded/unfolded
    mismatch. The model analog of `walkNs_one_hop`; the inductive step of the full walk ascent. -/
theorem referralSlist_one_hop (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (start cut : VeriDNS.Spec.Net.Name) (fuel : Nat)
    (htail : start.tail = cut) (hstart_ne : start ≠ [])
    (hstart_empty : (c.nsHostsAt now start).isEmpty = true)
    (hcut : (c.nsHostsAt now cut).isEmpty = false) :
    c.referralSlist now start (fuel + 2) = (c.nsHostsAt now cut).flatMap (c.glueAddrsAt now) := by
  obtain ⟨sh, st, rfl⟩ := List.exists_cons_of_ne_nil hstart_ne
  simp only [List.tail_cons] at htail
  subst htail
  unfold VeriDNS.Spec.Net.Cache.referralSlist
  rw [if_pos hstart_empty]
  show c.referralSlist now st (fuel + 1) = (c.nsHostsAt now st).flatMap (c.glueAddrsAt now)
  exact referralSlist_base c now st fuel hcut

/-- **Model `referralSlist` multi-hop ascent** (model analog of `walkNs_ascend`). Given a parent-chain of
    intermediate names from `start` up to the cut, each with empty `nsHostsAt` and the cut with cached NS, the
    model walk (with enough fuel) ascends the whole chain and returns `nsHostsAt(cut).flatMap glueAddrsAt`. The
    RHS being the base `flatMap` (not a `referralSlist` call) keeps `unfold` LHS-only at each step. With
    `keystone_at_cut` this lifts the per-cut keystone through the full delegation-depth ascent. -/
theorem referralSlist_ascend (c : VeriDNS.Spec.Net.Cache) (now : VeriDNS.Spec.Net.Time)
    (cut : VeriDNS.Spec.Net.Name) (hcut : (c.nsHostsAt now cut).isEmpty = false) :
    ∀ (inter : List VeriDNS.Spec.Net.Name) (start : VeriDNS.Spec.Net.Name) (fuel : Nat),
      inter.length + 2 ≤ fuel →
      List.Chain (fun a b => a ≠ [] ∧ a.tail = b) start (inter ++ [cut]) →
      (∀ m ∈ start :: inter, (c.nsHostsAt now m).isEmpty = true) →
      c.referralSlist now start fuel = (c.nsHostsAt now cut).flatMap (c.glueAddrsAt now) := by
  intro inter
  induction inter with
  | nil =>
    intro start fuel hfuel hchain hempty
    rw [List.nil_append] at hchain
    obtain ⟨⟨hne, htail⟩, _⟩ := List.chain_cons.mp hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    exact referralSlist_one_hop c now start cut f htail hne (hempty start (by simp)) hcut
  | cons m rest ih =>
    intro start fuel hfuel hchain hempty
    obtain ⟨⟨hne, htail⟩, hchain'⟩ := List.chain_cons.mp hchain
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    obtain ⟨sh, st, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.tail_cons] at htail
    subst htail
    unfold VeriDNS.Spec.Net.Cache.referralSlist
    rw [if_pos (hempty (sh :: st) (by simp))]
    show c.referralSlist now st f = (c.nsHostsAt now cut).flatMap (c.glueAddrsAt now)
    exact ih st f (by simp at hfuel; omega) hchain' (fun k hk => hempty k (List.mem_cons_of_mem _ hk))

/-- **Keystone-at-a-cut.** When `walkNs` finds NS records at the cut, the model image of the impl re-derived
    SLIST equals `nsHostsAt.flatMap glueAddrsAt` — the model `referralSlist`'s base case (`walkNs` and the model
    walk both stop at the cut where NS is cached). Chains `keystone_glue_assembly` (glue side) with
    `walkNs_nsNames_αName_eq_nsHostsAt` (NS-name side). `hnd` (the cut's cached NS names are duplicate-free) and
    `hhost` (each is abstractable + canonical) are the per-cut well-formedness, dischargeable in the driver. -/
theorem keystone_at_cut (c : Cache.DnsCache) (cut : ByteArray) (now : UInt32) (mc : Nat)
    (q : VeriDNS.Spec.Net.Query)
    (hqn : αName cut = some q.qname)
    (hq4 : q = ⟨q.qname, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩)
    (hcanN : cut = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hnd : ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.Nodup)
    (hhost : ∀ n ∈ ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList, ∃ qn, αName n = some qn
            ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63)) :
    nsGlueByteFlat
        ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none))
        (((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)).flatMap
          (fun m => (c.lookupTopCred m (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap (fun rr =>
            if (VeriDNS.Spec.RRParse.rrRdata rr).size == 4 then
              some (m, ((VeriDNS.Spec.RRParse.rrRdata rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
                ((VeriDNS.Spec.RRParse.rrRdata rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
                (VeriDNS.Spec.RRParse.rrRdata rr).data[3]!.toBitVec.setWidth 32)
            else none)))
      = ((αCache c).nsHostsAt (αTime now) q.qname).flatMap ((αCache c).glueAddrsAt (αTime now)) := by
  rw [keystone_glue_assembly c now _ mc hnd hwf hcanon hused hhost,
      walkNs_nsNames_αName_eq_nsHostsAt c cut now q hqn hq4 hcanN hvN hwf hcanon hused]

/-- **Half-B of the full-walk keystone: the model `referralSlist` from `sname` reaches the cut.** Composing the
    chain alignment (`parentDomainWire_chain_αName`), the model empties (`model_empties_of_impl`), and the cut
    non-empty (`nsHostsAt_nonempty_of_lookupTopCred`) into `referralSlist_ascend`: the model walk from `sname`'s
    abstraction ascends the same delegation chain the impl `walkNs` does and stops at the cut, yielding
    `nsHostsAt(cut).flatMap glueAddrsAt`. With Half-A (the impl side via `keystone_at_cut`) this is the full-walk
    keystone `modelSlistOf(impl) = referralSlist`. -/
theorem referralSlist_eq_nsHostsAt_at_cut (c : Cache.DnsCache) (now : UInt32)
    (sname cut : ByteArray) (sname_lab : Array ByteArray) (cutNa : VeriDNS.Spec.Net.Name)
    (inter : List ByteArray) (fuel' : Nat)
    (hsna : DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hcutNa : αName cut = some cutNa)
    (hcut_canN : cut = DomainName.labelsToWireFormatGo cutNa) (hcut_vN : ∀ x ∈ cutNa, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (himpl_chain : List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut]))
    (himpl_empty : ∀ m ∈ sname :: inter,
        (c.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true)
    (hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63))
    (hone : ∃ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none)
    (hfuel : inter.length + 2 ≤ fuel') :
    (αCache c).referralSlist (αTime now) sname_lab.toList fuel'
      = ((αCache c).nsHostsAt (αTime now) cutNa).flatMap ((αCache c).glueAddrsAt (αTime now)) := by
  have hmchain := parentDomainWire_chain_αName (inter ++ [cut]) sname sname_lab hsna hsnav himpl_chain
  simp only [List.map_append, List.map_cons, List.map_nil] at hmchain
  rw [show (αName cut).getD [] = cutNa from by simp [hcutNa]] at hmchain
  have hmempty := model_empties_of_impl c now hwf hcanon hused (sname :: inter) hcanonNode himpl_empty
  simp only [List.map_cons] at hmempty
  rw [show (αName sname).getD [] = sname_lab.toList from by simp [αName, hsna]] at hmempty
  have hcutNe : ((αCache c).nsHostsAt (αTime now) cutNa).isEmpty = false := by
    have := nsHostsAt_nonempty_of_lookupTopCred c cut now ⟨cutNa, VeriDNS.Spec.Net.QType.rr RRType.ns,
      RRClass.in, false⟩ hcutNa rfl hcut_canN hcut_vN hwf hcanon hused hone
    exact this
  exact referralSlist_ascend (αCache c) (αTime now) cutNa hcutNe
    (inter.map (fun w => (αName w).getD [])) sname_lab.toList fuel' (by rwa [List.length_map]) hmchain hmempty

/-- **The cache-re-derived referral glue** (the all-addresses glue `stepFindServers` installs): one `(host,addr)`
    pair per cached A address of each NS host. Naming it (rather than leaving it existential) lets the SLIST
    inversion expose `state''.slist` CONCRETELY, so it matches `full_walk_keystone`'s glue (definitionally equal —
    same `lookupTopCred`-`filterMap`-pack — at the `DnsCache` instance). -/
def reGlue {C RR : Type} [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (cache : C) (now : UInt32) (nsNames : Array ByteArray) : Array (ByteArray × BitVec 32) :=
  nsNames.flatMap fun nsName =>
    (VeriDNS.Spec.CacheSpec.lookupTopCred cache nsName (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now).filterMap
      fun rr =>
        if (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).size == 4 then
          some (nsName, ((VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[0]!.toBitVec.setWidth 32 <<< 24) |||
            ((VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[1]!.toBitVec.setWidth 32 <<< 16) |||
            ((VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[2]!.toBitVec.setWidth 32 <<< 8) |||
            (VeriDNS.Spec.RRParse.rrRdata (RR := RR) rr).data[3]!.toBitVec.setWidth 32)
        else none

set_option maxHeartbeats 1000000 in
/-- **THE FULL-WALK KEYSTONE.** The model image of the impl's cache-re-derived referral SLIST (built at the
    delegation cut `walkNs` reaches from `sname`) equals the model `referralSlist` that ascends from `sname`'s
    abstraction. Combines Half-A (`keystone_at_cut`: the per-cut `modelSlistOf = nsHostsAt(cut).flatMap`) with
    Half-B (`referralSlist_eq_nsHostsAt_at_cut`: the model walk reaches that same cut). This is exactly the `hgl`
    the forward-simulation `refer` step needs (the impl re-derives the SLIST from cache; the model `referralSlist`
    is its faithful image), discharged with NO oracle premise — the referral-poisoning fix made provable. -/
theorem full_walk_keystone (c : Cache.DnsCache) (now : UInt32)
    (sname cut : ByteArray) (sname_lab : Array ByteArray) (cutNa : VeriDNS.Spec.Net.Name)
    (inter : List ByteArray) (mc : Nat) (fuel' : Nat)
    (hsna : DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hcutNa : αName cut = some cutNa)
    (hcut_canN : cut = DomainName.labelsToWireFormatGo cutNa) (hcut_vN : ∀ x ∈ cutNa, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hnd : ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.Nodup)
    (hhost : ∀ n ∈ ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList, ∃ qn, αName n = some qn
            ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63))
    (himpl_chain : List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut]))
    (himpl_empty : ∀ m ∈ sname :: inter,
        (c.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true)
    (hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63))
    (hone : ∃ rr ∈ (c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none)
    (hfuel : inter.length + 2 ≤ fuel') :
    nsGlueByteFlat
        ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
          (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
            then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none))
        (reGlue (RR := VeriDNS.Spec.ResourceRecord) c now
          ((c.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
            (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
              then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none)))
      = (αCache c).referralSlist (αTime now) sname_lab.toList fuel' := by
  have hA := keystone_at_cut c cut now mc ⟨cutNa, VeriDNS.Spec.Net.QType.rr RRType.ns, RRClass.in, false⟩
    hcutNa rfl hcut_canN hcut_vN hwf hcanon hused hnd hhost
  have hB := referralSlist_eq_nsHostsAt_at_cut c now sname cut sname_lab cutNa inter fuel' hsna hsnav
    hcutNa hcut_canN hcut_vN hwf hcanon hused himpl_chain himpl_empty hcanonNode hone hfuel
  exact hA.trans hB.symm

set_option maxHeartbeats 1000000 in
/-- **Driver `hgl` from the cache-re-derived SLIST.** Pins `walkNs sname` to the delegation cut (`walkNs_ascend`
    + `walkNs_base`), so the impl's `setUpAddresses nsNames (reGlue …) mc` SLIST IS `full_walk_keystone`'s LHS,
    yielding `modelSlistOf(state''.slist) = referralSlist`. The `.continue` refer driver feeds this its actual
    `walkNs` result and the delegation structure (from the absorbed referral NS at the cut). -/
theorem refer_continue_keystone (cache : Cache.DnsCache) (sname cut : ByteArray)
    (sname_lab : Array ByteArray) (cutNa : VeriDNS.Spec.Net.Name) (inter : List ByteArray)
    (nsNames : Array ByteArray) (mc : Nat) (now : UInt32) (fuel' : Nat)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) sname cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 128 = some (nsNames, mc))
    (himpl_chain : List.Chain (fun a b => DomainName.parentDomainWire a = some b) sname (inter ++ [cut]))
    (himpl_empty : ∀ m ∈ sname :: inter,
        (cache.lookupTopCred m (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = true)
    (hcut_ne_impl : (cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).isEmpty = false)
    (hfuel128 : inter.length + 2 ≤ 128)
    (hsna : DomainName.wireFormatToLabels sname = .ok sname_lab)
    (hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab)
    (hcutNa : αName cut = some cutNa)
    (hcut_canN : cut = DomainName.labelsToWireFormatGo cutNa) (hcut_vN : ∀ x ∈ cutNa, x.size ≤ 63)
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ cache.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hnd : ((cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList.Nodup)
    (hhost : ∀ n ∈ ((cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).filterMap
        (fun rr => if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then some (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr)
          else none)).toList, ∃ qn, αName n = some qn
            ∧ n = DomainName.labelsToWireFormatGo qn ∧ (∀ x ∈ qn, x.size ≤ 63))
    (hcanonNode : ∀ m ∈ sname :: inter, ∃ na, αName m = some na
        ∧ m = DomainName.labelsToWireFormatGo na ∧ (∀ x ∈ na, x.size ≤ 63))
    (hone : ∃ rr ∈ (cache.lookupTopCred cut (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now).toList,
        (if VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == BitVec.ofNat 16 2
          then αName (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) else none) ≠ none)
    (hfuel : inter.length + 2 ≤ fuel') :
    ((αCache cache).referralSlist (αTime now) sname_lab.toList fuel').Subperm
      (modelSlistOf (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList)
        (NS := VeriDNS.Spec.SlistEntry) nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now nsNames) mc)) := by
  have hasc := walkNs_ascend cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now cut hcut_ne_impl
    inter sname 128 hfuel128 himpl_chain himpl_empty
  have hbase := walkNs_base cut cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now 0 hcut_ne_impl
  rw [hasc, hbase] at hwalk
  have heq := Option.some.inj hwalk
  rw [Prod.mk.injEq] at heq
  obtain ⟨hnn, hmm⟩ := heq
  subst hnn; subst hmm
  have hfull := full_walk_keystone cache now sname cut sname_lab cutNa inter 0 fuel' hsna hsnav hcutNa
    hcut_canN hcut_vN hwf hcanon hused hnd hhost himpl_chain himpl_empty hcanonNode hone hfuel

  rw [← hfull]
  exact (nsGlueByteFlat_sublist_fold _ _ _).subperm

/-- **`hhit` completeness direction: `Cache.hit ⊆ lookupAnswerable`.** Every record the *model* would
    serve from cache (`Cache.hit`) is actually served by the executable resolver — so the impl serves
    *everything the model promises*, not merely a safe subset. The membership converse of
    `lookupAnswerable_subset_hit`; together they pin the impl's cache-served set to the model's exactly.
    Composes the reverse predicate correspondence `matching_answerableEntry` (so the source entry is an
    impl `answerableEntry`), the credibility reconciliation `maxCredForKey_of_served_maximal` (so it
    survives the per-key max-credibility gate), and the value correspondence `αRR_aged` (so the
    TTL-aged served record abstracts back). Needs the cache canonicity invariant `hcanon` (each stored
    owner is the literal `labelsToWireFormatGo` of its abstraction with ≤63-byte labels) and `hcanN`
    for the query name — the reverse name correspondence requires it (`αName` ignores post-null
    trailing bytes that `nameEqCI` folds). These are the `WfRR` cache invariants. -/
theorem hit_subset_lookupAnswerable (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (rm : VeriDNS.Spec.Net.RR) (hrm : rm ∈ (αCache c).hit (αTime now) q) :
    ∃ rr, rr ∈ c.lookupAnswerable name qt qc now ∧ αRR rr = some rm := by
  unfold VeriDNS.Spec.Net.Cache.hit at hrm
  rw [List.mem_map] at hrm
  obtain ⟨a, hserved, rfl⟩ := hrm
  unfold VeriDNS.Spec.Net.Cache.served at hserved
  rw [List.mem_filter] at hserved
  obtain ⟨hmatch, hsfilt⟩ := hserved
  rw [Bool.and_eq_true] at hsfilt
  obtain ⟨hus, hmaxpred⟩ := hsfilt
  unfold VeriDNS.Spec.Net.Cache.matching at hmatch
  rw [List.mem_filter] at hmatch
  obtain ⟨hpos, hpred⟩ := hmatch
  obtain ⟨e, he, ha⟩ := mem_αCache_pos c a hpos
  obtain ⟨hane, hle, hmono⟩ := hwf e he
  obtain ⟨hcanE, hvE⟩ := hcanon e he a ha
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hpred
  obtain ⟨⟨⟨hf, hne⟩, hcov⟩, hcl⟩ := hpred
  have hfr : e.fresh now = true := by
    rw [αCacheRR_fresh e a now hle ha]; exact hf
  have hans : Cache.answerableEntry e name qt qc now = true :=
    matching_answerableEntry e a name qt qc now q t ht hqq hqc hle ha hcanE hcanN hvE hvN
      hf hne hcov hcl hus
  have hmaxc : c.maxCredForKey e name qt qc now = true :=
    maxCredForKey_of_served_maximal c name qt qc now q t hqn ht hqq hqc hwf hused e a he ha hmaxpred
  refine ⟨{ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }, ?_, ?_⟩
  · unfold Cache.DnsCache.lookupAnswerable
    rw [Array.mem_filterMap]
    exact ⟨e, he, by rw [hans, hmaxc]; rfl⟩
  · exact αRR_aged e a now hle hfr hmono ha

/-- **`hhit` as a theorem — the cache-served LIST equality, in full.** The abstraction of the impl's
    selected answer set (`lookupAnswerable`, i.e. `TrustworthinessSpec.answers`) equals, *as a list*,
    the model's `Cache.hit`. This discharges the `hhit` hypothesis that `resolveWithIO_cacheHit_simulates`
    assumed: under the standard cache well-formedness invariants (every record abstracts with
    `ttl ≤ expiry` and `insertedAt ≤ now`, canonical owner names, and a per-key-uniform stored
    credibility), the executable cache lookup serves *exactly* the records the model would — same set,
    same order, same TTL-aging. The proof fuses both sides to a common `c.records.toList.filterMap`
    (via `filter_map_eq_filterMap`/`filter_filterMap_eq`/`List.filterMap_filterMap`, the inner
    `matching` kept folded by `generalize`-ing the served predicate) and closes the per-element option
    equality with `cond_eq` (gate equality, packaging every bidirectional bridge) and `αRR_aged`
    (produced value). Combined with `αSection_map_rrBytes_wf` (the codec round-trip) this turns the
    cache-hit branch of the forward simulation into an *unconditional* refinement — no assumed
    served-set equality. -/
theorem lookupAnswerable_αRR_eq_hit (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    (c.lookupAnswerable name qt qc now).toList.filterMap αRR = (αCache c).hit (αTime now) q := by
  rw [Cache.DnsCache.lookupAnswerable, Array.toList_filterMap, List.filterMap_filterMap]
  rw [VeriDNS.Spec.Net.Cache.hit, VeriDNS.Spec.Net.Cache.served]
  generalize hsp : (fun e : VeriDNS.Spec.Net.CacheRR => e.cred.usable
      && ((αCache c).matching (αTime now) q).all
          (fun e2 => !e2.sameKey e.rr || Nat.ble e2.cred.rank e.cred.rank)) = sp
  rw [filter_map_eq_filterMap, VeriDNS.Spec.Net.Cache.matching, filter_filterMap_eq,
      show (αCache c).pos = c.records.toList.filterMap αCacheRR from rfl, List.filterMap_filterMap]
  subst hsp
  apply filterMap_congr_mem
  intro e he
  have he' : e ∈ c.records := Array.mem_def.mpr he
  obtain ⟨hane, hle, hmono⟩ := hwf e he'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hane
  have hce := cond_eq c name qt qc now q t hqn ht hqq hqc hcanN hvN hwf hcanon hused e he' a ha
  rw [ha, Option.bind_some]
  by_cases hcl : (Cache.answerableEntry e name qt qc now && c.maxCredForKey e name qt qc now) = true
  · have hfr : e.fresh now = true := by
      unfold Cache.answerableEntry Cache.liveEntry at hcl
      simp only [Bool.and_eq_true] at hcl; exact hcl.1.1.2
    have hcond : (a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)
          && (a.cred.usable && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank))) = true := hce ▸ hcl
    obtain ⟨hmp, hspa⟩ := Bool.and_eq_true_iff.mp hcond
    rw [if_pos hcl]
    simp only [hmp, hspa, cond_true]
    exact αRR_aged e a now hle hfr hmono ha
  · rw [Bool.not_eq_true] at hcl
    have hcond : (a.fresh (αTime now) && VeriDNS.Spec.Net.nameEq a.rr.owner q.qname
        && q.qtype.covers a.rr.rtype && (a.rr.cls == q.qclass)
          && (a.cred.usable && ((αCache c).matching (αTime now) q).all
              (fun a2 => !(a2.sameKey a.rr) || Nat.ble a2.cred.rank a.cred.rank))) = false := hce ▸ hcl
    rw [if_neg (by rw [hcl]; simp)]
    rcases Bool.and_eq_false_iff.mp hcond with h | h <;> simp [h]

/-- **`hhit` discharged — the served-set equality is no longer an oracle premise.** This is the *exact*
    statement `resolveWithIO_cacheHit_simulates` previously *assumed* as its `hhit` hypothesis
    (`αSection ((answers).map rrBytes) = Cache.hit`, where `TrustworthinessSpec.answers = lookupAnswerable`),
    now *proven* from the cache well-formedness invariants by composing the codec round-trip
    `αSection_map_rrBytes_wf` with the list equality `lookupAnswerable_αRR_eq_hit`. So the positive
    cache-hit branch of the forward simulation refines the model *unconditionally* (given only that the
    cache is well-formed — records abstract, canonical owner names, per-key-uniform credibility, and
    well-formed wire records — all invariants the resolver's `store`/`sweep` maintain), closing the
    last assumed hypothesis of GAP 2 on the read path. -/
theorem hhit_of_invariants (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ c.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ c.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ c.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative)
    (hwfrr : ∀ rr ∈ c.lookupAnswerable name qt qc now, VeriDNS.Proof.NameTree.WfRR rr) :
    αSection ((c.lookupAnswerable name qt qc now).map
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
      = (αCache c).hit (αTime now) q := by
  rw [αSection_map_rrBytes_wf _ hwfrr,
      lookupAnswerable_αRR_eq_hit c name qt qc now q t hqn ht hqq hqc hcanN hvN hwf hcanon hused]

/-- **The CNAME-chase cache-hit bridge** — the impl `.answerHit` served set abstracts to the model's
    `Cache.hit`. Composes `localAnswer_answerHit_inv` (the served set is `answers` at the resolved name
    `sname`) with `lookupAnswerable_αRR_eq_hit` (`answers = lookupAnswerable`; the served-set/`Cache.hit`
    equality under cache well-formedness). The impl half of part (c): with `cacheHit_hasVerdict` it makes the
    chased target's cache hit a model verdict, the recursive `hrec` of `answerCname`. -/
theorem localAnswer_answerHit_hit (cache : Cache.DnsCache) (qt qc : BitVec 16) (now : UInt32)
    (fuel : Nat) (sname0 : ByteArray) (chain0 visited0 : Array ByteArray)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (h : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname0 chain0 visited0 = .answerHit sname chain rrs)
    (hqn : αName sname = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : sname = DomainName.labelsToWireFormatGo q.qname) (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : ∀ e ∈ cache.records, (αCacheRR e).isSome ∧ e.rr.ttl.toNat ≤ e.expiry.toNat
            ∧ e.expiry.toNat - e.rr.ttl.toNat ≤ now.toNat)
    (hcanon : ∀ e ∈ cache.records, ∀ a, αCacheRR e = some a →
        e.rr.name = DomainName.labelsToWireFormatGo a.rr.owner ∧ (∀ x ∈ a.rr.owner, x.size ≤ 63))
    (hused : ∀ e ∈ cache.records, e.credibility = Trustworthiness.authoritativeSection
            ∨ e.credibility = Trustworthiness.authoritySection
            ∨ e.credibility = Trustworthiness.sectionNonauthoritative
            ∨ e.credibility = Trustworthiness.additionalAuthoritative) :
    rrs.toList.filterMap αRR = (αCache cache).hit (αTime now) q := by
  obtain ⟨-, hans, -⟩ :=
    localAnswer_answerHit_inv cache qt qc now fuel sname0 chain0 visited0 sname chain rrs h
  rw [← hans]
  exact lookupAnswerable_αRR_eq_hit cache sname qt qc now q t hqn ht hqq hqc hcanN hvN hwf hcanon hused

theorem findNegative_fresh (c : Cache.DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (e : Cache.NegativeEntry)
    (h : c.findNegative name qt qc now = some e) : now < e.expiry := by
  have hpred : ∀ x : Cache.NegativeEntry, decide (x.expiry > now) = true → now < x.expiry :=
    fun x hx => of_decide_eq_true hx
  unfold Cache.DnsCache.findNegative at h
  cases hf1 : c.negatives.find? (fun y => nameEqCI y.name name && y.qclass == qc
      && y.expiry > now && y.rcode == VeriDNS.Spec.Rcode.nameError) with
  | some a =>
    rw [hf1] at h
    change some a = some e at h
    have hae : a = e := Option.some.inj h
    have hp := Array.find?_some hf1
    simp only [Bool.and_eq_true] at hp
    rw [hae] at hp
    exact hpred e hp.1.2
  | none =>
    rw [hf1] at h
    change c.negatives.find? (fun y => nameEqCI y.name name && y.qtype == qt
        && y.qclass == qc && y.expiry > now) = some e at h
    have hp := Array.find?_some h
    simp only [Bool.and_eq_true] at hp
    exact hpred e hp.2

theorem computeNegativeTtl_eq_min (soa : VeriDNS.Spec.RData.Soa.SoaRdata) (ttl : BitVec 32) :
    (Server.computeNegativeTtl soa ttl).toNat = min soa.minimum.toNat ttl.toNat := by
  unfold Server.computeNegativeTtl
  by_cases h : soa.minimum ≤ ttl
  · simp only [if_pos h]
    have : soa.minimum.toNat ≤ ttl.toNat := BitVec.le_def.mp h
    omega
  · simp only [if_neg h]
    have : ¬ soa.minimum.toNat ≤ ttl.toNat := fun hc => h (BitVec.le_def.mpr hc)
    omega

theorem negativelyCacheable_iff_absorbNeg_trigger (resp : VeriDNS.Spec.Format)
    (htc : resp.header.tc = 0) :
    Server.negativelyCacheable resp = true
      ↔ (αRCode resp.header.rcode = VeriDNS.Spec.Net.RCode.nameError
          ∨ (αRCode resp.header.rcode = VeriDNS.Spec.Net.RCode.noError
              ∧ resp.answer.isEmpty = true)) := by
  unfold Server.negativelyCacheable αRCode
  rw [htc]
  cases resp.header.rcode <;> simp_all +decide

theorem cacheUnlessTruncated_truncated (cache : Cache.DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : Trustworthiness) (now : UInt32)
    (h : resp.header.tc = 1) :
    Resolver.cacheUnlessTruncated (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache resp raws cred now = cache := by
  simp [Resolver.cacheUnlessTruncated, h]

theorem buildSubQuery_clears_rd
    (s : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (sub : VeriDNS.Spec.Format)
    (h : Resolver.buildSubQuery s = some sub) : sub.header.rd = 0 := by
  unfold Resolver.buildSubQuery at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rw [← Option.some.inj h]

theorem cnameToChase_some (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (h : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target) :
    Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false
      ∧ Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) resp.answer = some target := by
  unfold Resolver.cnameToChase at h
  split at h
  · exact absurd h (by simp)
  · rename_i hni
    exact ⟨by simpa using hni, h⟩

theorem mkAddressQuery_spec (name : ByteArray) :
    (Server.mkAddressQuery name).header.rd = 0
      ∧ (Server.mkAddressQuery name).question
        = #[{ qname := name, qtype := (1 : BitVec 16), qclass := (1 : BitVec 16) }]
      ∧ αType 1 = some RRType.a ∧ αClass 1 = some RRClass.in :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem αResp_negativeResponse {RR : Type} [VeriDNS.Spec.RRParse RR]
    (q : VeriDNS.Spec.Format) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR) :
    (αResp (Resolver.negativeResponse (RR := RR) q rc soaAuth)).answer = []
      ∧ (αResp (Resolver.negativeResponse (RR := RR) q rc soaAuth)).rcode
        = αRCode rc := by
  refine ⟨?_, rfl⟩
  simp [αResp, αSection, Resolver.negativeResponse]

theorem αResp_cacheResponse {RR : Type} [VeriDNS.Spec.RRParse RR]
    (q : VeriDNS.Spec.Format) (rrs : Array RR) :
    (αResp (Resolver.cacheResponse (RR := RR) q rrs)).rcode
      = VeriDNS.Spec.Net.RCode.noError := rfl

theorem αSection_append (a b : Array ByteArray) :
    αSection (a ++ b) = αSection a ++ αSection b := by
  unfold αSection
  rw [Array.toList_append, List.filterMap_append]

theorem αSection_empty_of_isEmpty {a : Array ByteArray} (h : a.isEmpty = true) :
    αSection a = [] := by
  rw [Array.isEmpty_iff] at h; subst h; rfl

theorem prependChain_answer (chain : Array ByteArray) (resp : VeriDNS.Spec.Format) :
    (Resolver.prependChain chain resp).answer
      = (if chain.isEmpty then resp.answer else chain ++ resp.answer) := by
  unfold Resolver.prependChain; split <;> rfl

theorem finalizeAnswer_answer {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s resp).answer = (Resolver.prependChain s.cnameChain resp).answer := by
  unfold Resolver.finalizeAnswer; cases s.lastQuery <;> rfl

theorem αSection_prependChain (chain : Array ByteArray) (resp : VeriDNS.Spec.Format) :
    αSection (Resolver.prependChain chain resp).answer
      = αSection chain ++ αSection resp.answer := by
  rw [prependChain_answer]
  by_cases h : chain.isEmpty
  · rw [if_pos h, αSection_empty_of_isEmpty h, List.nil_append]
  · rw [if_neg h, αSection_append]

/-- **The CNAME chain-link abstracts to exactly the model CNAME** (`[cn]`). When the impl appends the chased
    CNAME record (`prependCnameLink`, the answer-injection-hardened chain step), the abstracted chain gains
    exactly the single model CNAME `cn` — matching `Resolves.answerCname`'s `cn :: …` prepend. The chain-
    structure half of the CNAME-chase `v`-agreement: `αResp (finalizeAnswer …) = αSection chain ++ [cn] ++
    αSection (cacheResponse …)` lines up with the model verdict `cn :: vsub.answer`. -/
theorem αSection_prependCnameLink (chain answer : Array ByteArray) (cnBytes : ByteArray)
    (rr : VeriDNS.Spec.ResourceRecord) (cn : VeriDNS.Spec.Net.RR)
    (hext : Resolver.extractCnameRR (RR := VeriDNS.Spec.ResourceRecord) answer = some cnBytes)
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) cnBytes = some rr)
    (har : αRR rr = some cn) :
    αSection (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) chain answer)
      = αSection chain ++ [cn] := by
  simp only [Resolver.prependCnameLink, hext]
  unfold αSection
  rw [Array.toList_push, List.filterMap_append]
  simp only [List.filterMap_cons, hp, har, List.filterMap_nil]

theorem finalizeAnswer_rcode {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) :
    (Resolver.finalizeAnswer s resp).header.rcode = resp.header.rcode := by
  unfold Resolver.finalizeAnswer Resolver.prependChain
  split <;> split <;> rfl

theorem finalizeAnswer_abstracts_rcode {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) :
    (αResp (Resolver.finalizeAnswer s resp)).rcode = αRCode resp.header.rcode := by
  rw [(αResp_components _).1, finalizeAnswer_rcode]

/-- A chain-free (`cnameChain = #[]`) finalized negative delivery abstracts exactly like the bare
    `negativeResponse`: empty answer, `αRCode rc`. The entry-point (`initFromQuery`) shape of the
    RFC 2308 §2.1 chain-including negative delivery. -/
theorem αResp_finalizeAnswer_negativeResponse {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.RRParse RR]
    (st : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (rc : VeriDNS.Spec.Rcode)
    (soaAuth : Array RR) (hcc : st.cnameChain = #[]) :
    (αResp (Resolver.finalizeAnswer st (Resolver.negativeResponse (RR := RR) q rc soaAuth))).answer = []
      ∧ (αResp (Resolver.finalizeAnswer st (Resolver.negativeResponse (RR := RR) q rc soaAuth))).rcode
        = αRCode rc := by
  constructor
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hcc]
    rw [show αSection (Resolver.negativeResponse (RR := RR) q rc soaAuth).answer = []
        from (αResp_negativeResponse q rc soaAuth).1, List.append_nil]
    rfl
  · rw [finalizeAnswer_abstracts_rcode]
    rfl

theorem stepCheckLocal_negHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR) (chain : Array ByteArray)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .negative rc soaAuth chain) :
    Resolver.stepCheckLocal s
      = .answer (Resolver.finalizeAnswer { s with cnameChain := chain }
          (Resolver.negativeResponse q rc soaAuth))
          { s with cnameChain := chain } := by
  simp only [Resolver.stepCheckLocal, hq, hqu, hneg]

theorem stepCheckLocal_answerHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .answerHit sname chain rrs) :
    Resolver.stepCheckLocal s
      = .answer (Resolver.finalizeAnswer { s with cnameChain := chain } (Resolver.cacheResponse q rrs))
          { s with cnameChain := chain } := by
  simp only [Resolver.stepCheckLocal, hq, hqu, hhit]

/-- **One `resolve.loop` step from `.checkAnswer` with a cached positive answer reaches `.done`.** When the
    resolver is at `checkAnswer` and `localAnswer` yields an `answerHit` (the cache serves the queried name,
    credibility-gated), the step is `.answer`, so the loop terminates with the finalized answer. The second
    step of the CNAME-chase `.finished` inversion (the first being `stepAnalyzeResponse_cname`'s retarget to
    the canonical name): a cached chase target resolves here without a network round. -/
theorem loop_checkAnswer_answerHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .answerHit sname chain rrs)
    (n : Nat) :
    Resolver.resolve.loop X (n + 1)
      = .ok (.done (Resolver.finalizeAnswer { X with cnameChain := chain } (Resolver.cacheResponse q rrs))
          { X with cnameChain := chain }) := by
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, hcs, stepCheckLocal_answerHit X q qu sname chain rrs hq hqu hhit]

/-- **One `resolve.loop` step from `.checkAnswer` with a cached *negative* answer reaches `.done`.** The
    `negHit` sibling of `loop_checkAnswer_answerHit`: a fresh negative cache entry (NXDOMAIN/NODATA) for the
    queried name terminates the loop with the synthesized negative response. The negative branch of the
    CNAME-chase `.finished` inversion (a chased CNAME whose target is cached as a denial). -/
theorem loop_checkAnswer_negHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR) (chain : Array ByteArray)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .negative rc soaAuth chain)
    (n : Nat) :
    Resolver.resolve.loop X (n + 1)
      = .ok (.done (Resolver.finalizeAnswer { X with cnameChain := chain }
          (Resolver.negativeResponse q rc soaAuth))
          { X with cnameChain := chain }) := by
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, hcs, stepCheckLocal_negHit X q qu rc soaAuth chain hq hqu hneg]

/-- **`stepCheckLocal` on a chain-cap abort fails the query.** The CNAME chase exceeded the impl's chain
    cap (`localAnswer` fuel), so the resolver SERVFAILs (real-resolver behavior: BIND's max-cname-chain)
    rather than querying the network for a name whose cached data was never consulted. -/
theorem stepCheckLocal_abort {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (habort : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .abort) :
    Resolver.stepCheckLocal s = .error "cname chain too long" := by
  simp only [Resolver.stepCheckLocal, hq, hqu, habort]

/-- One `resolve.loop` step from `.checkAnswer` on a chain-cap abort is the SERVFAIL error terminal. -/
theorem loop_checkAnswer_abort {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (habort : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .abort)
    (n : Nat) :
    Resolver.resolve.loop X (n + 1) = .error "cname chain too long" := by
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, hcs, stepCheckLocal_abort X q qu hq hqu habort]

/-- **`stepCheckLocal` with a cache *miss* goes to `.findServers`** (preserving `lastResponse`). When the
    queried name is not cacheable-answered, the resolver advances to find servers (either keeping the SLIST or,
    on a CNAME-target change, retargeting). The `lastResponse` is unchanged, so the subsequent send pauses. -/
theorem stepCheckLocal_miss_goto {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname' : ByteArray) (chain : Array ByteArray)
    (hq : s.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := C) (RR := RR) s.resources.cache qu.qtype qu.qclass
        s.now 8 s.resources.sname s.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname s.cnameChain) = .miss sname' chain) :
    ∃ s', Resolver.stepCheckLocal s = .goto .findServers s' ∧ s'.lastResponse = s.lastResponse := by
  simp only [Resolver.stepCheckLocal, hq, hqu, hmiss]
  split <;> exact ⟨_, rfl, rfl⟩

theorem stepAnalyzeResponse_cname {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false) :
    Resolver.stepAnalyzeResponse s = .goto .checkAnswer { s with
      resources := { s.resources with
        sname := target
        cache := Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
          (Resolver.bailiwickRaws (RR := RR) s.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) s.now
        slist := default }
      cnameChain := Resolver.prependCnameLink (RR := RR) s.cnameChain resp.answer
      lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname, htc, hnrev,
    Bool.false_eq_true, if_false]

/-- **`stepAnalyzeResponse` on a REVISITING CNAME chase fails the query** (RFC 1034 §3.6.2 loop
    detection): a chased canonical name already in the visited set drives the
    `.error "cname loop detected"` terminal. The contrapositive is how the driver's CNAME arms
    DERIVE the guard fact `hnrev`: an `.ok`/`.continue` resume outcome forces the guard to have
    passed. -/
theorem stepAnalyzeResponse_cname_revisit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hrev : ((Resolver.cnameChaseVisited (RR := RR)
        ((s.lastQuery.bind (fun q => q.question[0]?)).elim s.resources.sname (fun qu => qu.qname))
        s.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true) :
    Resolver.stepAnalyzeResponse s = .error "cname loop detected" := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname, htc, hrev,
    Bool.false_eq_true, if_false, if_true]

theorem stepAnalyzeResponse_bizarre {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    Resolver.stepAnalyzeResponse s = .goto .sendQueries { s with lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname]
  rw [if_pos hbiz]

theorem answersQueryB_nonempty {RR : Type} [VeriDNS.Spec.RRParse RR] (resp : VeriDNS.Spec.Format)
    (h : Resolver.answersQueryB (RR := RR) resp = true) : resp.answer.isEmpty = false := by
  unfold Resolver.answersQueryB at h
  split at h
  · unfold Resolver.hasRRTypeIn at h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, _⟩ := h
    simp only [Array.isEmpty_eq_false_iff_exists_mem]
    exact ⟨resp.answer[i], resp.answer.getElem_mem hi⟩
  · exact absurd h (by simp)

theorem stepAnalyzeResponse_answer {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := RR) resp = true) :
    Resolver.stepAnalyzeResponse s = .answer (Resolver.finalizeAnswer s resp)
      { s with resources := { s.resources with
          cache := Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
            (Resolver.bailiwickRaws (RR := RR) s.resources.sname resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) s.now } } := by
  have hne : resp.answer.isEmpty = false := answersQueryB_nonempty resp hans
  simp [Resolver.stepAnalyzeResponse, hresp, hcname, hsf, hcls, hans, hne]

theorem stepAnalyzeResponse_nameError {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := RR) resp = false) :
    Resolver.stepAnalyzeResponse s = .answer (Resolver.finalizeAnswer s resp) s := by
  simp [Resolver.stepAnalyzeResponse, hresp, hcname, hsf, hcls, hnerr, hans]

theorem stepAnalyzeResponse_referral {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := RR) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := RR) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := RR) resp.authority 6 = false) :
    Resolver.stepAnalyzeResponse s = .goto .findServers
      { s with
        resources := { s.resources with
          slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (NS := NS)
            (Resolver.extractNsNames (RR := RR) resp.authority)
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := RR)
              (Resolver.referralCutRaw (RR := RR) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := RR) resp.authority s.resources.sname),
          cache := Resolver.cacheUnlessTruncated (RR := RR)
            (Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
              (Resolver.bailiwickRaws (RR := RR)
                (Resolver.referralCutRaw (RR := RR) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) s.now)
            resp
            (Resolver.bailiwickRaws (RR := RR)
              (Resolver.referralCutRaw (RR := RR) resp.authority) resp.additional)
            Resolver.credAdditional s.now }
        lastResponse := none } := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname]
  rw [if_neg (by simp [hbiz]), if_pos (by simp [hans, hnerr, hansEmpty, hauth]),
    if_pos (by simp only [hns, haa, hrc, hsoa, Bool.not_false, Bool.and_true, Bool.true_and])]

/-- **Any `.answer` outcome of `stepAnalyzeResponse` with `answersQueryB = false` carries the
    `finalizeAnswer` payload and the UNCHANGED state** (pure, loop-free). Splitting the
    post-`cnameToChase = none` if-chain: with the query not answered, the positive-answer WRITE arm
    is unreachable, so every `.answer` leaf (NXDOMAIN, junk-answer, NODATA, TC) returns
    `finalizeAnswer s resp` and the state verbatim; the `.goto`/`.error` leaves are not `.answer`
    (distinct constructors). -/
theorem stepAnalyzeResponse_answer_payload_neg {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp X : VeriDNS.Spec.Format)
    (Xst : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hans : Resolver.answersQueryB (RR := RR) resp = false)
    (hsa : Resolver.stepAnalyzeResponse s = .answer X Xst) :
    X = Resolver.finalizeAnswer s resp ∧ Xst = s := by
  unfold Resolver.stepAnalyzeResponse at hsa
  rw [hresp] at hsa
  simp only [hcname, hans, Bool.false_eq_true, if_false] at hsa
  repeat' split at hsa
  all_goals simp_all
  all_goals exact (hsa.2 ▸ hsa.1).symm

/-- The positive sibling of `stepAnalyzeResponse_answer_payload_neg`: with `answersQueryB = true`
    (and no CNAME to chase), the ONLY `.answer` leaf is the hardened positive-answer WRITE arm —
    the payload is `finalizeAnswer s resp` and the carried state holds the answer-section write
    (RFC 1034 caching of delivered answers). -/
theorem stepAnalyzeResponse_answer_payload_pos {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp X : VeriDNS.Spec.Format)
    (Xst : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hans : Resolver.answersQueryB (RR := RR) resp = true)
    (hsa : Resolver.stepAnalyzeResponse s = .answer X Xst) :
    X = Resolver.finalizeAnswer s resp
      ∧ Xst = { s with resources := { s.resources with
          cache := Resolver.cacheUnlessTruncated (RR := RR) s.resources.cache resp
            (Resolver.bailiwickRaws (RR := RR) s.resources.sname resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) s.now } } := by
  by_cases hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = true
  · rw [stepAnalyzeResponse_bizarre s resp hresp hcname (by rw [hsf]; rfl)] at hsa
    exact absurd hsa (by simp)
  · by_cases hcls : Resolver.classifiableB resp = true
    · rw [stepAnalyzeResponse_answer s resp hresp hcname
        (Bool.eq_false_iff.mpr hsf) hcls hans] at hsa
      injection hsa with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    · rw [stepAnalyzeResponse_bizarre s resp hresp hcname
        (by rw [Bool.eq_false_iff.mpr hcls]; simp)] at hsa
      exact absurd hsa (by simp)

/-- **A `.goto` outcome of `stepAnalyzeResponse` (post-`cnameToChase = none`) is the referral descent.**
    With no CNAME to chase, the only `.goto` leaf is the referral `.goto .findServers` whose state has
    `lastResponse := none`. Lets the answer-terminal inversion drive that branch to `.paused`. -/
theorem stepAnalyzeResponse_goto_shape {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (ns : VeriDNS.Spec.AlgorithmStep)
    (s' : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hsa : Resolver.stepAnalyzeResponse s = .goto ns s') :
    ns = .findServers ∧ s'.lastResponse = none := by
  unfold Resolver.stepAnalyzeResponse at hsa
  rw [hresp] at hsa
  simp only [hcname] at hsa
  repeat' split at hsa
  all_goals simp_all
  rw [← hsa.2]

/-- **A `.goto` from `stepAnalyzeResponse` (non-bizarre, no CNAME) is a referral, and exposes its full shape.**
    With `cnameToChase = none` and not-bizarre, the ONLY `stepAnalyzeResponse` branch producing `.goto` is the
    referral one (every other branch is `.answer`/`.error`), firing exactly under the impl's referral guard:
    empty answer, `rcode ≠ nameError`, non-empty authority carrying an NS record, and the query not directly
    answered. So `.goto` inverts to those five facts — the classification the driver's `.continue` honest-refer
    arm needs to feed the positive `isReferral` bridge (→ `href`) and `referral_bailiwick_desc`. -/
theorem stepAnalyzeResponse_goto_referral {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (resp : VeriDNS.Spec.Format) (ns : VeriDNS.Spec.AlgorithmStep)
    (s' : Resolver.State S C NS RR)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := RR) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hsa : Resolver.stepAnalyzeResponse s = .goto ns s') :
    Resolver.answersQueryB (RR := RR) resp = false
      ∧ (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false
      ∧ resp.answer.isEmpty = true ∧ resp.authority.isEmpty = false
      ∧ Resolver.hasRRTypeIn (RR := RR) resp.authority 2 = true
      ∧ (resp.header.aa == 0) = true
      ∧ (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true
      ∧ Resolver.hasRRTypeIn (RR := RR) resp.authority 6 = false := by
  unfold Resolver.stepAnalyzeResponse at hsa
  rw [hresp] at hsa
  simp only [hcname] at hsa
  split at hsa
  · rename_i hbz; simp [hbiz] at hbz
  · split at hsa
    · rename_i hcond
      split at hsa
      · rename_i hhns
        simp only [Bool.and_eq_true] at hcond hhns
        exact ⟨by simpa using hcond.1.1.1, by simpa using hcond.1.1.2, hcond.1.2,
          by simpa using hcond.2, hhns.1.1.1, hhns.1.1.2, hhns.1.2, by simpa using hhns.2⟩
      · rename_i hhns
        repeat' split at hsa
        all_goals simp_all
    · rename_i hcond
      repeat' split at hsa
      all_goals simp_all

/-- **`afterResume = .continue` inverts to `stepAnalyzeResponse = .goto`** (non-bizarre, no CNAME). The
    resume loop reaches `.paused` (→ `afterResume = .continue`) only through the referral `.goto .findServers`
    step; the `.answer` terminal gives `.done` (→ `.finished`), contradicting `.continue`. Mirrors
    `afterResume_finished_payload`'s resume unfold, extracting the `.goto` in the productive `.paused` case.
    Chains with `stepAnalyzeResponse_goto_referral` to hand the driver's `.continue` honest-refer arm the full
    referral classification (`hns`/`hansEmpty`/…) from `afterResume = .continue` alone. -/
theorem afterResume_continue_stepAnalyze_goto
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA : VeriDNS.Spec.Format)
    (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hAR : Server.afterResume state entryName respA = .continue st) :
    ∃ ns s', Resolver.stepAnalyzeResponse
      ({ state with lastResponse := some respA, currentStep := .analyzeResponse } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      = .goto ns s' := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  unfold Server.afterResume at hAR
  rw [hdrop, Resolver.resume] at hAR
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step, hstep, Resolver.stepSendQueries] at hAR
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step] at hAR
  split at hAR
  · exact absurd hAR (by simp)
  · rename_i X heq
    split at heq
    · exact absurd heq (by simp)
    · rename_i ns s' heq2; exact ⟨ns, s', heq2⟩
    ·
      rename_i s'x heqio
      simp only [Resolver.stepAnalyzeResponse, hcname] at heqio
      repeat' split at heqio
      all_goals simp_all
    · exact absurd heq (by simp)
  · exact absurd hAR (by simp)

theorem respInBailiwick_sound (sname : ByteArray) (resp : VeriDNS.Spec.Format)
    (hb : Server.respInBailiwick sname resp = true)
    (i : Nat) (hi : i < resp.authority.size)
    (rr : VeriDNS.Spec.ResourceRecord)
    (hparse : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        resp.authority[i] = some rr)
    (hns : (VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)) = true)
    (ownerLabels snameLabels : Array ByteArray)
    (ho : DomainName.wireFormatToLabels (VeriDNS.Spec.RRParse.rrName rr) = .ok ownerLabels)
    (hsn : DomainName.wireFormatToLabels sname = .ok snameLabels) :
    Resolver.suffixMatchCount snameLabels ownerLabels = ownerLabels.size := by
  unfold Server.respInBailiwick at hb
  rw [Array.all_eq_true] at hb
  have hp := hb i hi
  rw [hparse] at hp
  simp only [hns, if_true, ho, hsn] at hp
  simpa using hp

/-- **A *followable* delegation is in-bailiwick** (`¬ unfollowableDelegationB` + `delegationShapedB` ⟹
    `respInBailiwick`). Pure Bool decomposition of `unfollowableDelegationB = bogus || (shaped && !inBail)`:
    if the referral is delegation-shaped and not unfollowable, then it is in-bailiwick. The impl-side
    extraction the driver's `.continue` refer case uses (with `hunf : ¬ unfollowable`) to feed the model
    `hbail` (via `respInBailiwick_sound`). -/
theorem respInBailiwick_of_not_unfollowable (slist : SList.DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hunf : Server.unfollowableDelegationB slist sname resp = false)
    (hdel : Server.delegationShapedB resp = true) :
    Server.respInBailiwick sname resp = true := by
  unfold Server.unfollowableDelegationB at hunf
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, hdel, Bool.true_eq_false, false_or] at hunf
  simpa using hunf.2

/-- **A referral is delegation-shaped.** The impl's `delegationShapedB` is exactly the referral
    classification conjunction (has-NS-authority ∧ ¬answers-query ∧ ¬NXDOMAIN ∧ no-CNAME-to-chase), so the
    driver's refer `.continue` case (which has all four) gets `delegationShapedB = true` to feed
    `respInBailiwick_of_not_unfollowable`. -/
theorem delegationShapedB_of (resp : VeriDNS.Spec.Format)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none) :
    Server.delegationShapedB resp = true := by
  unfold Server.delegationShapedB
  simp only [hns, hans, hnerr, hcn, Bool.not_false, Bool.true_and, Bool.and_true,
    Option.isNone_none]

/-- **A *followable* delegation is strictly closer than the current SLIST** (`¬unfollowableDelegationB` +
    `delegationShapedB` ⟹ `delegationCloserB`). Pure Bool decomposition of `unfollowableDelegationB =
    (shaped && !closer) || (shaped && !inBailiwick)`: if the referral is delegation-shaped and not unfollowable,
    then `delegationCloserB slist sname resp = true` — i.e. `searchFails slist ∨ delegationMatchCount authority
    sname > matchCount slist`. The impl-side source of the refer-descent "cut strictly deeper than the frontier"
    fact the driver bridges to `pc.length < d.subapex.length` for `serverBailiwick_ge_priorCut`. -/
theorem delegationCloserB_of_not_unfollowable (slist : SList.DnsSList) (sname : ByteArray)
    (resp : VeriDNS.Spec.Format)
    (hunf : Server.unfollowableDelegationB slist sname resp = false)
    (hdel : Server.delegationShapedB resp = true) :
    Server.delegationCloserB slist sname resp = true := by
  unfold Server.unfollowableDelegationB Server.bogusDelegationB at hunf
  rw [Bool.or_eq_false_iff] at hunf
  have h1 := hunf.1
  rw [hdel, Bool.true_and] at h1
  simpa using h1

theorem respInBailiwick_complete (sname : ByteArray) (resp : VeriDNS.Spec.Format)
    (h : ∀ (i : Nat) (_ : i < resp.authority.size),
       ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
           resp.authority[i] = some rr ∧
         ((VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)) = true →
           ∃ ownerLabels snameLabels,
             DomainName.wireFormatToLabels (VeriDNS.Spec.RRParse.rrName rr) = .ok ownerLabels ∧
             DomainName.wireFormatToLabels sname = .ok snameLabels ∧
             Resolver.suffixMatchCount snameLabels ownerLabels = ownerLabels.size)) :
    Server.respInBailiwick sname resp = true := by
  unfold Server.respInBailiwick
  rw [Array.all_eq_true]
  intro i hi
  obtain ⟨rr, hparse, hns⟩ := h i hi
  simp only [hparse]
  split
  · rename_i hisns
    obtain ⟨ol, sl, ho, hsn, hsuf⟩ := hns hisns
    simp only [ho, hsn]
    simpa using hsuf
  · rfl

theorem resolve_negHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR)
    (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .negative rc soaAuth chain) :
    Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
      = (.ok (.done (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain })
          : Except String (Resolver.ResolveYield S C NS RR)) := by
  have hsname : (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache).resources.sname = qu.qname := by
    simp only [Resolver.initFromQuery, hqu]
  have hstep : Resolver.step (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache)
      = .answer (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain } := by
    unfold Resolver.step
    show Resolver.stepCheckLocal _ = _
    apply stepCheckLocal_negHit (qu := qu)
    · rfl
    · exact hqu
    · show Resolver.localAnswer cache qu.qtype qu.qclass now 8 _ #[]
          (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = _
      rw [hsname]; exact hneg
  unfold Resolver.resolve
  show Resolver.resolve.loop _ (n + 1) = _
  rw [Resolver.resolve.loop, hstep]

theorem resolve_answerHit {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .answerHit sname chain rrs) :
    Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
      = (.ok (.done (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain })
          : Except String (Resolver.ResolveYield S C NS RR)) := by
  have hsname : (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache).resources.sname
      = qu.qname := by simp only [Resolver.initFromQuery, hqu]
  have hstep : Resolver.step (Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache)
      = .answer (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs))
          { Resolver.initFromQuery (NS := NS) (RR := RR) query sbelt now cache with cnameChain := chain } := by
    unfold Resolver.step
    show Resolver.stepCheckLocal _ = _
    apply stepCheckLocal_answerHit (qu := qu) (sname := sname)
    · rfl
    · exact hqu
    · show Resolver.localAnswer cache qu.qtype qu.qclass now 8 _ #[]
          (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = _
      rw [hsname]; exact hhit
  unfold Resolver.resolve
  show Resolver.resolve.loop _ (n + 1) = _
  rw [Resolver.resolve.loop, hstep]

theorem resolve_negHit_abstracts {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array RR)
    (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .negative rc soaAuth chain) :
    ∃ resp stF, Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
        = (.ok (.done resp stF) : Except String (Resolver.ResolveYield S C NS RR))
      ∧ (αResp resp).answer = αSection chain
      ∧ (αResp resp).rcode = αRCode rc := by
  refine ⟨_, _, resolve_negHit query sbelt n now cache qu rc soaAuth chain hqu hneg, ?_, ?_⟩
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
    rw [show αSection (Resolver.negativeResponse (RR := RR) query rc soaAuth).answer = []
        from (αResp_negativeResponse query rc soaAuth).1, List.append_nil]
  · rw [finalizeAnswer_abstracts_rcode]
    rfl

theorem resolve_answerHit_abstracts {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (query : VeriDNS.Spec.Format) (sbelt : S) (n : Nat) (now : UInt32) (cache : C)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray) (rrs : Array RR)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := C) (RR := RR) cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := RR) qu.qname #[]) = .answerHit sname chain rrs) :
    ∃ resp stF, Resolver.resolve (NS := NS) (RR := RR) query sbelt (n + 1) now cache
        = (.ok (.done resp stF) : Except String (Resolver.ResolveYield S C NS RR))
      ∧ (αResp resp).rcode = VeriDNS.Spec.Net.RCode.noError
      ∧ (αResp resp).answer
          = αSection chain ++ αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := RR))) := by
  refine ⟨_, _, resolve_answerHit query sbelt n now cache qu sname chain rrs hqu hhit, ?_, ?_⟩
  · show αRCode (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs)).header.rcode = _
    rw [finalizeAnswer_rcode]
    rfl
  · show (αResp (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs))).answer = _
    rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
    rfl

theorem resolveWithIO_negHit {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (soaAuth : Array VeriDNS.Spec.ResourceRecord) (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .negative rc soaAuth chain) :
    Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
      = pure (.ok (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
              query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth)), cache) := by
  unfold Server.resolveWithIO
  rw [show (64 : Nat) = 63 + 1 from rfl,
    resolve_negHit query sbelt 63 now cache qu rc soaAuth chain hqu hneg]

theorem resolveWithIO_answerHit {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
      = pure (.ok (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
              query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs)), cache) := by
  unfold Server.resolveWithIO
  rw [show (64 : Nat) = 63 + 1 from rfl,
    resolve_answerHit query sbelt 63 now cache qu sname chain rrs hqu hhit]

theorem resolveWithIO_answerHit_payload {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    ∃ resp, Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ (αResp resp).rcode = VeriDNS.Spec.Net.RCode.noError
      ∧ (αResp resp).answer
          = αSection chain ++ αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes
              (RR := VeriDNS.Spec.ResourceRecord))) := by
  refine ⟨_, resolveWithIO_answerHit query sbelt cache now fuel depth budget qu sname chain rrs
    hqu hhit, ?_, ?_⟩
  · show αRCode (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs)).header.rcode = _
    rw [finalizeAnswer_rcode]
    rfl
  · show (αResp (Resolver.finalizeAnswer _ (Resolver.cacheResponse query rrs))).answer = _
    rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
    rfl

theorem afterResume_answer
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    Server.afterResume state entryName resp
      = .finished (.ok (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp))

          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              state.resources.sname resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundExpiryClasses := by
  have hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB resp) = false := by rw [hsf, hcls]; rfl
  have hne : resp.answer.isEmpty = false := answersQueryB_nonempty resp hans
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hsa : Resolver.stepAnalyzeResponse
      { state with lastResponse := some resp, currentStep := .analyzeResponse }
      = .answer (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp)
          { { state with lastResponse := some resp, currentStep := .analyzeResponse } with
            resources := { state.resources with
              cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                state.resources.cache resp
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  state.resources.sname resp.answer)
                (Resolver.credAnswer (resp.header.aa == 1)) state.now } } := by
    apply stepAnalyzeResponse_answer <;> first | rfl | assumption
  unfold Server.afterResume
  rw [hdrop, Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]
  rfl

theorem afterResume_answer_payload
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    ∃ out cout, Server.afterResume state entryName resp = .finished (.ok out) cout
      ∧ (αResp out).rcode = αRCode resp.header.rcode
      ∧ (αResp out).answer = αSection state.cnameChain ++ αSection resp.answer := by
  refine ⟨_, _, afterResume_answer state entryName resp hstep hcname hsf hcls hans, ?_, ?_⟩
  · exact finalizeAnswer_abstracts_rcode _ resp
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]

/-- **The answer-terminal RespAgree bridge** (driver answer-terminal glue). The driver's verdict is
    `αResp resp` where `resp` is `afterResume`'s `.finished .ok` output (= `finalizeAnswer` of the accepted
    `respA`); `WorldModels` supplies `RespAgree (αResp respA) ref`. For an empty CNAME chain (the direct
    answer), `afterResume_answer_payload` gives `αResp resp` and `αResp respA` the same rcode + answer, so
    the agreement transfers to the verdict (the `aa` flip is invisible to `RespAgree`, which compares only
    rcode + answer-permutation). This is what feeds `serverAnswer_hasVerdict`/`trustedReply_hasVerdict`. -/
theorem respAgree_answer_bridge
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA resp : VeriDNS.Spec.Format} {ref : VeriDNS.Spec.Net.Response}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok resp) cout)
    (hchain : state.cnameChain = #[])
    (hragA : RespAgree (αResp respA) ref) :
    RespAgree (αResp resp) { ref with aa := false } := by
  obtain ⟨out, cout', hout, hrc, han⟩ :=
    afterResume_answer_payload state entryName respA hstep hcname hsf hcls hans
  rw [hAR] at hout
  injection hout with ho hco; injection ho with ho; subst ho
  rw [hchain] at han
  refine RespAgree.trans (RespAgree.of_eq ?_ ?_) hragA
  · rw [hrc, (αResp_components respA).1]
  · rw [han, (αResp_components respA).2.1]
    simp [αSection]

/-- **The delivered CNAME-chase answer splits as accumulated-chain ++ chased-answer.** Exposes the chain
    structure of `αResp (finalizeAnswer st (cacheResponse q rrs)).answer` for ANY `st.cnameChain` (not just the
    single-link `#[cnBytes]`): it is the abstracted accumulated chain followed by the abstracted cache answer.
    The shape the `cnameChain ≠ #[]` loop-invariant case needs — the prior chain `αSection st.cnameChain`
    corresponds to the model's outer `answerCname`/`cacheCname` prepends, which the driver must track across
    iterations (the loop invariant `αSection state.cnameChain = <model chain consumed so far>`). -/
theorem αSection_finalizeAnswer_cacheResponse
    (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Format) (rrs : Array VeriDNS.Spec.ResourceRecord) :
    αSection (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)).answer
      = αSection st.cnameChain ++ αSection (Resolver.cacheResponse q rrs).answer := by
  rw [finalizeAnswer_answer, αSection_prependChain]

/-- **CNAME-chase `v`-agreement (the assembly capstone).** The impl's delivered answer for a CNAME chase whose
    target is a cache hit (`out = finalizeAnswer st (cacheResponse q rrs)`, with the hardened single-link chain
    `st.cnameChain = #[cnBytes]`) abstracts to a `RespAgree` of the model `answerCname` verdict
    `{ final with answer := cn :: final.answer }`. Composes the chain-structure refinement
    (`αSection_prependChain` + `αSection_prependCnameLink`: the chain abstracts to exactly `[cn]`) with the
    served-set ↔ model-hit `Perm` (`hperm`, from `localAnswer_answerHit_modelHit_perm`). The last glue the
    `cnameToChase=some` driver terminal needs — Perm-tolerant, so it feeds the non-`_hv` `answerCname`/
    `cacheCname` producers (which take the `RespAgree` bridge directly). -/
theorem respAgree_cname_finished_bridge
    (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q : VeriDNS.Spec.Format) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (cnBytes : ByteArray) (rr : VeriDNS.Spec.ResourceRecord) (cn : VeriDNS.Spec.Net.RR)
    (final : VeriDNS.Spec.Net.Response)
    (hstchain : st.cnameChain = #[cnBytes])
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) cnBytes = some rr)
    (har : αRR rr = some cn)
    (hperm : (αSection (Resolver.cacheResponse q rrs).answer).Perm final.answer)
    (hfinrc : final.rcode = VeriDNS.Spec.Net.RCode.noError) :
    RespAgree (αResp (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)))
      { final with answer := cn :: final.answer } := by
  refine ⟨?_, ?_⟩
  · rw [(αResp_components _).1, finalizeAnswer_rcode]
    show αRCode (Resolver.cacheResponse q rrs).header.rcode = final.rcode
    rw [hfinrc]; rfl
  · rw [(αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hstchain]
    have hcn1 : αSection #[cnBytes] = [cn] := by
      unfold αSection
      rw [show #[cnBytes].toList = [cnBytes] from rfl]
      simp only [List.filterMap_cons, hp, har, List.filterMap_nil]
    rw [hcn1, List.singleton_append]
    exact List.Perm.cons cn hperm

theorem afterResume_nameError
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false) :
    Server.afterResume state entryName resp
      = .finished (.ok (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp))
          (Server.boundStateCache
            { state with lastResponse := some resp, currentStep := .analyzeResponse }).resources.cache := by
  have hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB resp) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hsa : Resolver.stepAnalyzeResponse
      { state with lastResponse := some resp, currentStep := .analyzeResponse }
      = .answer (Resolver.finalizeAnswer
          { state with lastResponse := some resp, currentStep := .analyzeResponse } resp)
          { state with lastResponse := some resp, currentStep := .analyzeResponse } := by
    apply stepAnalyzeResponse_nameError <;> first | rfl | assumption
  unfold Server.afterResume
  rw [hdrop, Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]

theorem afterResume_bizarre
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    Server.afterResume state entryName resp
      = .continue (Server.boundStateCache
          { Server.dropIfBizarre state entryName resp with
            lastResponse := none, currentStep := .sendQueries }) := by
  have hcs : (Server.dropIfBizarre state entryName resp).currentStep = .sendQueries := by
    unfold Server.dropIfBizarre; split <;> exact hstep
  have hsa : Resolver.stepAnalyzeResponse
      { Server.dropIfBizarre state entryName resp with
        lastResponse := some resp, currentStep := .analyzeResponse }
      = .goto .sendQueries
          { { Server.dropIfBizarre state entryName resp with
              lastResponse := some resp, currentStep := .analyzeResponse } with
            lastResponse := none } := by
    apply stepAnalyzeResponse_bizarre <;> first | rfl | assumption
  unfold Server.afterResume
  rw [Resolver.resume]
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hsa]
  rw [show (62 : Nat) = 61 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, Resolver.stepSendQueries]

theorem stepFindServers_goto {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) :
    ∃ s', Resolver.stepFindServers s = .goto .sendQueries s' ∧ s'.lastResponse = s.lastResponse := by
  unfold Resolver.stepFindServers; dsimp only
  split <;> [split; split] <;> exact ⟨_, rfl, rfl⟩

/-- **`stepFindServers` is a SLIST-only step.** Whichever branch it takes (cache-re-derived glue SLIST, "still
    closer" no-op, or fall-back to `sbelt`), it touches ONLY `resources.slist` — the cache, query name, clock,
    cname chain, last query/response and step are all frame-preserved. This is the frame half of the referral
    `.continue` state inversion: combined with `stepAnalyzeResponse_referral` (which fixes the post-absorb
    cache) it pins `state''.cache`/`.sname`/`.now` for `StateModels_refer_preserve`, leaving only the SLIST for
    the keystone correspondence. -/
theorem stepFindServers_frame {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s s' : Resolver.State S C NS RR)
    (h : Resolver.stepFindServers s = .goto .sendQueries s') :
    s'.resources.cache = s.resources.cache ∧ s'.resources.sname = s.resources.sname
      ∧ s'.now = s.now ∧ s'.cnameChain = s.cnameChain ∧ s'.lastQuery = s.lastQuery
      ∧ s'.lastResponse = s.lastResponse ∧ s'.currentStep = s.currentStep := by
  unfold Resolver.stepFindServers at h; dsimp only at h
  split at h <;> split at h <;>
    (injection h with _ h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem stepFindServers_rebuild {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) (nsNames : Array ByteArray) (mc : Nat)
    (hwalk : Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = false) :
    Resolver.stepFindServers s = .goto .sendQueries
      { s with resources := { s.resources with
          slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
            (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } } := by
  unfold Resolver.stepFindServers
  dsimp only
  rw [hwalk]
  simp only [hclose, if_false, Bool.false_eq_true]
  rfl

/-- **`stepFindServers` KEEPS the current (transient) SLIST when it is already closer.** The dual of
    `stepFindServers_rebuild`: whenever `currentCloser` holds — the transient SLIST outranks whatever
    `walkNs` finds in the cache (`hclose = true`), which covers BOTH `walkNs = some` with a shallower cut
    AND `walkNs = none` with a positive transient match-count — the resolver reuses `s.resources.slist`
    unchanged. This is the branch a resolver takes for a delegation it does not cache (RFC 2181: a zero-TTL
    NS is used for the current query but not stored), following the referral's own bailiwick-filtered glue. -/
theorem stepFindServers_keep {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR)
    (hkeep : ∀ walkMc : Nat,
        (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
          && decide (walkMc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = true) :
    Resolver.stepFindServers s = .goto .sendQueries s := by
  unfold Resolver.stepFindServers
  dsimp only
  cases hw : Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
  | none =>
    simp only [hkeep 0, if_true]
  | some p =>
    obtain ⟨nsNames, mc⟩ := p
    simp only [hkeep mc, if_true]

/-- **Full `stepFindServers` post-referral case analysis.** Whichever branch it takes, `stepFindServers`
    `goto .sendQueries`s a frame-preserving state whose SLIST is one of three forms: (K) the current
    transient SLIST kept unchanged (the delegation was already closer — a resolver following the referral's
    own glue without caching it); (R) rebuilt from the cache (`setUpAddresses nsNames (reGlue …) mc`, the
    `walkNs` cut is at-or-below the frontier); (B) the safety belt (both prior failed). The (R)/(B) disjuncts
    carry the deciding `currentCloser` value so the driver can select the matching model rule and rule out
    the belt for a genuine referral. -/
theorem stepFindServers_cases {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (s : Resolver.State S C NS RR) :
    ∃ s', Resolver.stepFindServers s = .goto .sendQueries s'
      ∧ s'.resources.cache = s.resources.cache ∧ s'.resources.sname = s.resources.sname
      ∧ s'.now = s.now ∧ s'.cnameChain = s.cnameChain ∧ s'.lastQuery = s.lastQuery
      ∧ s'.lastResponse = s.lastResponse
      ∧ s'.resources.sbelt = s.resources.sbelt
      ∧ ( s'.resources.slist = s.resources.slist
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
                (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = false
              ∧ s'.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
                  (reGlue (RR := RR) s.resources.cache s.now nsNames) mc)
          ∨ (s'.resources.slist = s.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = false) ) := by
  have hunf : Resolver.stepFindServers s = (
      match Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
          (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
      | some (nsNames, mc) =>
        if (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
            && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) then
          .goto .sendQueries s
        else
          .goto .sendQueries { s with resources := { s.resources with
            slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
              (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } }
      | none =>
        if (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
            && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) then
          .goto .sendQueries s
        else
          .goto .sendQueries { s with resources := { s.resources with slist := s.resources.sbelt } }) := rfl
  rw [hunf]
  cases hw : Resolver.stepFindServers.walkNs (RR := RR) s.resources.sname s.resources.cache
      (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) s.now 128 with
  | none =>
    dsimp only
    by_cases hc : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
        && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = true
    · refine ⟨s, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
      rw [if_pos hc]
    · rw [Bool.not_eq_true] at hc
      refine ⟨{ s with resources := { s.resources with slist := s.resources.sbelt } },
        ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, hc⟩)⟩
      rw [if_neg (by rw [hc]; simp)]
  | some p =>
    obtain ⟨nsNames, mc⟩ := p
    dsimp only
    by_cases hc : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) s.resources.slist
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) s.resources.slist)) = true
    · refine ⟨s, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
      rw [if_pos hc]
    · rw [Bool.not_eq_true] at hc
      refine ⟨{ s with resources := { s.resources with
          slist := VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
            (reGlue (RR := RR) s.resources.cache s.now nsNames) mc } },
        ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨nsNames, mc, rfl, hc, rfl⟩)⟩
      rw [if_neg (by rw [hc]; simp)]

theorem loop_findServers_paused {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st) := by
  obtain ⟨s', hfs, hs'⟩ := stepFindServers_goto X
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  have : s'.lastResponse = none := hs'.trans hlr
  simp only [Resolver.step, Resolver.stepSendQueries, this]
  exact ⟨_, rfl⟩

/-- **Structural form of `loop_findServers_paused`** — exposes the paused state's frame fields. The paused
    `st` is `{s' with currentStep := .sendQueries}` where `s'` is `stepFindServers`'s output, so by
    `stepFindServers_frame` its cache/query-name/clock/cname-chain are exactly `X`'s. This is the inversion
    that pins `state''.cache`/`.sname`/`.now` for the driver's `.continue` referral case (the SLIST is left to
    the keystone correspondence). -/
theorem loop_findServers_paused_struct {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st)
      ∧ st.resources.cache = X.resources.cache ∧ st.resources.sname = X.resources.sname
      ∧ st.now = X.now ∧ st.cnameChain = X.cnameChain ∧ st.currentStep = .sendQueries := by
  obtain ⟨s', hfs, hs'⟩ := stepFindServers_goto X
  obtain ⟨hc, hsn, hnw, hcc, _, _, _⟩ := stepFindServers_frame X s' hfs
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  have hlr' : s'.lastResponse = none := hs'.trans hlr
  simp only [Resolver.step, Resolver.stepSendQueries, hlr']
  exact ⟨_, rfl, hc, hsn, hnw, hcc, rfl⟩

/-- **SLIST-exposing form of the referral `.continue` loop inversion.** Like `loop_findServers_paused_struct`
    but, given the `walkNs` cache result and `currentCloser = false` (the cache-re-derive branch), it ALSO pins
    the paused state's SLIST to `setUpAddresses nsNames glue mc` — the exact form the keystone correspondence
    (`modelSlistOf (setUpAddresses …) .Perm referralSlist`) consumes. Threads `stepFindServers_rebuild`. -/
theorem loop_findServers_paused_slist {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (nsNames : Array ByteArray) (mc : Nat)
    (hwalk : Resolver.stepFindServers.walkNs (RR := RR) X.resources.sname X.resources.cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) X.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) X.resources.slist
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) X.resources.slist)) = false)
    (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st)
      ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
          (reGlue (RR := RR) X.resources.cache X.now nsNames) mc
      ∧ st.resources.cache = X.resources.cache ∧ st.resources.sname = X.resources.sname
      ∧ st.now = X.now ∧ st.cnameChain = X.cnameChain ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = X.lastQuery := by
  have hfs := stepFindServers_rebuild X nsNames mc hwalk hclose
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  simp only [Resolver.step, Resolver.stepSendQueries, hlr]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Case-analysing form of the referral `.continue` loop inversion.** Like `loop_findServers_paused_slist`
    but WITHOUT the `walkNs`/`currentCloser` hypotheses: it exposes the paused state's SLIST as the full
    three-way `stepFindServers_cases` disjunction (kept-transient / cache-rebuilt / safety-belt). This is what
    the driver consumes to handle BOTH the cache-rebuild branch (ttl > 0 delegations) and the transient-keep
    branch (ttl = 0 delegations, followed via the response's own bailiwick-filtered glue). -/
theorem loop_findServers_paused_cases {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (hcs : X.currentStep = .findServers)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 2) = .ok (.paused st)
      ∧ st.resources.cache = X.resources.cache ∧ st.resources.sname = X.resources.sname
      ∧ st.now = X.now ∧ st.cnameChain = X.cnameChain ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = X.lastQuery
      ∧ st.resources.sbelt = X.resources.sbelt
      ∧ ( st.resources.slist = X.resources.slist
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := RR) X.resources.sname X.resources.cache
                (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) X.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) X.resources.slist
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) X.resources.slist)) = false
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := S) (NS := NS) nsNames
                  (reGlue (RR := RR) X.resources.cache X.now nsNames) mc)
          ∨ (st.resources.slist = X.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := S) (NS := NS) X.resources.slist
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := S) (NS := NS) X.resources.slist)) = false) ) := by
  obtain ⟨s', hfs, hc, hsn, hnw, hcc, hlq, hlrs, hsb, hdisj⟩ := stepFindServers_cases X
  rw [show n + 2 = (n + 1) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hfs]
  rw [Resolver.resolve.loop]
  have hlr' : s'.lastResponse = none := hlrs.trans hlr
  simp only [Resolver.step, Resolver.stepSendQueries, hlr']
  refine ⟨_, rfl, hc, hsn, hnw, hcc, rfl, hlq, hsb, ?_⟩
  exact hdisj

/-- **One-plus-two `resolve.loop` steps from `.checkAnswer` with a cache *miss* reach `.paused`.** The miss
    branch of the CNAME-chase inversion: a chase target NOT in the cache drives checkAnswer → findServers →
    sendQueries → `.paused` (a `.continue`, NOT `.finished`) — so from a `.finished` outcome the target must
    have been cached (answerHit/negHit). Composes `stepCheckLocal_miss_goto` with `loop_findServers_paused`. -/
theorem loop_checkAnswer_miss {S C NS RR : Type}
    [VeriDNS.Spec.SlistSpec S NS] [VeriDNS.Spec.SlistFromNameSpec S NS]
    [VeriDNS.Spec.CacheSpec C RR] [VeriDNS.Spec.TrustworthinessSpec C RR]
    [VeriDNS.Spec.NegativeAuthoritySpec C RR] [VeriDNS.Spec.NegativeCacheSpec C]
    [VeriDNS.Spec.RRParse RR] [Inhabited S] [Inhabited C]
    (X : Resolver.State S C NS RR) (q : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname' : ByteArray) (chain : Array ByteArray)
    (hcs : X.currentStep = .checkAnswer)
    (hq : X.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := C) (RR := RR) X.resources.cache qu.qtype qu.qclass
        X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := RR) qu.qname X.cnameChain) = .miss sname' chain)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st, Resolver.resolve.loop X (n + 3) = .ok (.paused st) := by
  obtain ⟨s', hsc, hs'⟩ := stepCheckLocal_miss_goto X q qu sname' chain hq hqu hmiss
  rw [show n + 3 = (n + 2) + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcs, hsc]
  exact loop_findServers_paused { s' with currentStep := .findServers } rfl (hs'.trans hlr) n

theorem resume_referral_paused
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st) := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused _ rfl rfl 60

/-- **Structural form of `resume_referral_paused`** — exposes the paused state's frame fields and the
    post-absorb cache. A referral `resume` pauses in a state whose cache is exactly the two
    `cacheUnlessTruncated` writes (authority then additional, both bailiwick-filtered at the
    `referralCutRaw`), with the query name, clock and cname chain unchanged and `currentStep = .sendQueries`.
    This pins `StateModels_refer_preserve`'s `hcache`/`hsname`/`hnowB` for the driver's `.continue` case; the
    SLIST (rebuilt by `stepFindServers`) is handled separately by the keystone correspondence. -/
theorem resume_referral_paused_struct
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st)
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) state.now)
            resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
            Resolver.credAdditional state.now
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused_struct _ rfl rfl 60

/-- **SLIST-exposing form of `resume_referral_paused_struct`.** Given that `walkNs` over the post-absorb cache
    finds a cached NS RRset (`hwalk`) and the just-installed transient referral SLIST is not already closer
    (`hclose`, the cache-re-derive gate), the paused state's SLIST is `setUpAddresses nsNames glue mc` — the
    keystone-correspondence input. The `hwalk`/`hclose` are phrased over the explicit post-analyze cache/SLIST
    (the two `cacheUnlessTruncated` writes / `setUpAddresses (extractNsNames …) …`), which the driver discharges
    from the walk-trace (NS absorbed at the referral cut) and `currentCloser_false_of_ge`. -/
theorem resume_referral_paused_slist
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (nsNames : Array ByteArray) (mc : Nat)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st)
      ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry) nsNames
          (reGlue (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
                (Resolver.credAuthority (resp.header.aa == 1)) state.now)
              resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
              Resolver.credAdditional state.now)
            state.now nsNames) mc
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) state.now)
            resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
            Resolver.credAdditional state.now
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused_slist _ rfl rfl nsNames mc hwalk hclose 60

/-- **Case-analysing `resume` referral inversion.** Like `resume_referral_paused_slist` but WITHOUT the
    `walkNs`/`currentCloser` hypotheses — it returns the full `stepFindServers_cases` SLIST disjunction
    (kept-transient / cache-rebuilt / belt), the ONE inversion that covers both ttl>0 (rebuild) and ttl=0
    (transient-keep, followed via the response's bailiwick-filtered glue) delegations. -/
theorem resume_referral_paused_cases
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Resolver.resume state resp 64 = .ok (.paused st)
      ∧ st.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery
      ∧ st.resources.sbelt = state.resources.sbelt
      ∧ ( st.resources.slist = (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) nsNames
                  (reGlue (RR := VeriDNS.Spec.ResourceRecord) (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now) state.now nsNames) mc)
          ∨ (st.resources.slist = state.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false) ) := by
  have href := stepAnalyzeResponse_referral
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp rfl hcname hbiz
    hans hnerr hansEmpty hauth hns haa hrc hsoa
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, href]
  rw [show (62 : Nat) = 60 + 2 from rfl]
  exact loop_findServers_paused_cases _ rfl rfl 60

/-- **`resume` for a CNAME chase whose target is a cached positive answer reaches `.done`** (the CNAME
    analogue of `resume_referral_paused`). Assembles the three step lemmas — `stepSendQueries` (lastResponse
    present ⟹ analyze), `stepAnalyzeResponse_cname` (cache, retarget `sname := target`, append the CNAME to
    `cnameChain`, go checkAnswer), `loop_checkAnswer_answerHit` (cached target ⟹ `.done`). The returned
    state's `cnameChain` is exactly `localAnswer`'s `chain`, so `finalizeAnswer` prepends the followed CNAME(s)
    — the impl image of the model `cacheCname`/`answerCname`. All cache reads are credibility-gated (`served`/
    `cnameServed`, tracked by `MatchMaxEquiv`) — no referral glue wall. -/
theorem resume_cname_answerHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer)) = .answerHit sname chain rrs) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Resolver.resume state resp 64
        = .ok (.done (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)) st)
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  refine ⟨{ ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      with cnameChain := chain }, ?_, rfl, rfl⟩
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 61 + 1 from rfl]
  exact loop_checkAnswer_answerHit
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer })
    q qu sname chain rrs rfl hq hqu hhit 61

/-- **`afterResume` for a CNAME chase whose target is a cached positive answer is `.finished`.** Wraps
    `resume_cname_answerHit` through `afterResume`: a non-bizarre CNAME response (`rcode ≠ servFail`,
    classifiable) is not dropped (`dropIfBizarre = state`), so `afterResume` returns the `.done` payload as
    `.finished (.ok …)`. Combined with the driver's `afterResume … = .finished (.ok out)` (injectivity of
    `.finished`/`.ok`), this pins `out` to the chain-prepended cached answer — the impl image of `cacheCname`. -/
theorem afterResume_cname_answerHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (sname : ByteArray) (chain : Array ByteArray)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer)) = .answerHit sname chain rrs) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Server.afterResume state entryName respA
        = .finished (.ok (Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs)))
            (Server.boundStateCache st).resources.cache
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hrs, hcc, hca⟩ :=
    resume_cname_answerHit state respA target q qu sname chain rrs hstep hcn htc hnrev hq hqu hhit
  refine ⟨st, ?_, hcc, hca⟩
  unfold Server.afterResume
  rw [hdrop, hrs]

/-- **The `negHit` sibling of `resume_cname_answerHit`.** A CNAME chase whose target is a cached *negative*
    (NXDOMAIN/NODATA) entry terminates `resume` with the synthesized `negativeResponse`. Same 3-iteration
    trace (sendQueries → analyzeResponse[cname] → checkAnswer) but the checkAnswer step dispatches `negHit`. -/
theorem resume_cname_negHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
    (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer)) = .negative rc soaAuth chain) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Resolver.resume state resp 64
        = .ok (.done (Resolver.finalizeAnswer st (Resolver.negativeResponse q rc soaAuth)) st)
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  refine ⟨{ ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      with cnameChain := chain }, ?_, rfl, rfl⟩
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 61 + 1 from rfl]
  exact loop_checkAnswer_negHit
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer })
    q qu rc soaAuth chain rfl hq hqu hneg 61

/-- **`afterResume` for a CNAME chase whose target is a cached negative answer is `.finished`.** Wraps
    `resume_cname_negHit` through `afterResume` (non-bizarre ⟹ `dropIfBizarre = state`). -/
theorem afterResume_cname_negHit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
    (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer)) = .negative rc soaAuth chain) :
    ∃ st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Server.afterResume state entryName respA
        = .finished (.ok (Resolver.finalizeAnswer st (Resolver.negativeResponse q rc soaAuth)))
            (Server.boundStateCache st).resources.cache
      ∧ st.cnameChain = chain
      ∧ st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hrs, hcc, hca⟩ :=
    resume_cname_negHit state respA target q qu rc soaAuth chain hstep hcn htc hnrev hq hqu hneg
  refine ⟨st, ?_, hcc, hca⟩
  unfold Server.afterResume
  rw [hdrop, hrs]

/-- **The `miss` sibling: a CNAME chase whose target is NOT cached drives `resume` to `.paused`** (a
    `.continue`, not `.finished`). The checkAnswer step misses → findServers → sendQueries → IO pause. -/
theorem resume_cname_miss
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question) (sname' : ByteArray) (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer)) = .miss sname' chain) :
    ∃ st', Resolver.resume state resp 64 = .ok (.paused st') := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 59 + 3 from rfl]
  exact loop_checkAnswer_miss
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer })
    q qu sname' chain rfl hq hqu hmiss rfl 59

/-- **`resume` on a CNAME chase that exceeds the chain cap is the SERVFAIL error terminal.** The chased
    target's `localAnswer` aborts (fuel exhausted after 8 cached links), so the resume loop fails the
    query — it never reaches `.done`/`.paused`. Makes the chain-cap sub-case of the driver's CNAME arms
    vacuous under an `.ok` run. -/
theorem resume_cname_abort
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (q : VeriDNS.Spec.Format)
    (qu : VeriDNS.Spec.Question)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (habort : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer)) = .abort) :
    Resolver.resume state resp 64 = .error "cname chain too long" := by
  have hcname_step := stepAnalyzeResponse_cname
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hnrev
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]
  rw [show (62 : Nat) = 61 + 1 from rfl]
  exact loop_checkAnswer_abort
    ({ state with
      resources := { state.resources with
        sname := target,
        slist := default,
        cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname resp.answer)
          (Resolver.credAnswer (resp.header.aa == 1)) state.now },
      currentStep := .checkAnswer,
      lastResponse := none,
      cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain resp.answer })
    q qu rfl hq hqu habort 61

/-- **`resume` on a REVISITING CNAME chase is the loop-detection error terminal** (RFC 1034 §3.6.2).
    The contrapositive supplies the driver arms' `hnrev`: a `.paused`/`.ok` resume outcome forces the
    revisit guard to have passed. -/
theorem resume_cname_revisit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = false)
    (hrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true) :
    Resolver.resume state resp 64 = .error "cname loop detected" := by
  have hcname_step := stepAnalyzeResponse_cname_revisit
    { state with lastResponse := some resp, currentStep := .analyzeResponse } resp target rfl hcn htc hrev
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]

/-- **`afterResume` on a REVISITING CNAME chase is the loop-detection error** — never `.finished (.ok _)`
    and never `.continue`. The driver's CNAME arms case on the guard and use this for the revisit side. -/
theorem afterResume_cname_revisit
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA : VeriDNS.Spec.Format) (target : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true) :
    Server.afterResume state entryName respA
      = .finished (.error "cname loop detected") state.resources.cache := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  unfold Server.afterResume
  rw [hdrop, resume_cname_revisit state respA target hstep hcn htc hrev]

/-- **`afterResume` for a CNAME chase whose target is uncached is `.continue`.** Wraps `resume_cname_miss`:
    the impl pauses for the chased query's IO, so this is a `.continue`, never a `.finished`. -/
theorem afterResume_cname_miss
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (sname' : ByteArray) (chain : Array ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer)) = .miss sname' chain) :
    ∃ st', Server.afterResume state entryName respA = .continue st' := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st', hrs⟩ := resume_cname_miss state respA target q qu sname' chain hstep hcn htc hnrev hq hqu hmiss
  refine ⟨Server.boundStateCache st', ?_⟩
  unfold Server.afterResume
  rw [hdrop, hrs]

/-- **The CNAME-chase `.finished` inversion.** Given the driver's `afterResume … = .finished (.ok out)` with
    a chased CNAME (`cnameToChase respA = some target`) and a non-bizarre response, the cached chase target
    must have been a positive (`answerHit`) or negative (`negHit`) hit — a cache *miss* would have driven the
    impl to `.continue` (`afterResume_cname_miss`), contradicting `.finished`. So `out` is pinned to either the
    chain-prepended cached answer (`finalizeAnswer st (cacheResponse q rrs)` — the impl image of a positive
    `cacheCname`) or the synthesized denial (`negativeResponse q rc soaAuth` — the negative `cacheCname`). -/
theorem afterResume_cname_finished_inv
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA q : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q => q.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hq : state.lastQuery = some q) (hqu : q.question[0]? = some qu)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    (∃ (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
        (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
      Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer)) = .answerHit sname chain rrs ∧
      out = Resolver.finalizeAnswer st (Resolver.cacheResponse q rrs) ∧ st.cnameChain = chain ∧
      cout = (Server.boundStateCache st).resources.cache) ∨
    (∃ (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
        (chain : Array ByteArray)
        (st : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
      Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer)) = .negative rc soaAuth chain ∧
      out = Resolver.finalizeAnswer st (Resolver.negativeResponse q rc soaAuth) ∧ st.cnameChain = chain ∧
      cout = (Server.boundStateCache st).resources.cache) := by
  cases hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname respA.answer)
        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
      qu.qtype qu.qclass state.now 8 target (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer) (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA.answer)) with
  | answerHit sname chain rrs =>
    obtain ⟨st, hAR', hcc, -⟩ :=
      afterResume_cname_answerHit state entryName respA q target qu sname chain rrs hstep hcn htc hnrev hsf hcls hq hqu hla
    have he := hAR.symm.trans hAR'
    simp only [Server.IoStep.finished.injEq, Except.ok.injEq] at he
    exact Or.inl ⟨sname, chain, rrs, st, rfl, he.1, hcc, he.2⟩
  | negative rc soaAuth chain =>
    obtain ⟨st, hAR', hcc, -⟩ :=
      afterResume_cname_negHit state entryName respA q target qu rc soaAuth chain hstep hcn htc hnrev hsf hcls hq hqu hla
    have he := hAR.symm.trans hAR'
    simp only [Server.IoStep.finished.injEq, Except.ok.injEq] at he
    exact Or.inr ⟨rc, soaAuth, chain, st, rfl, he.1, hcc, he.2⟩
  | miss sname' chain =>
    obtain ⟨st', hAR'⟩ :=
      afterResume_cname_miss state entryName respA q target qu sname' chain hstep hcn htc hnrev hsf hcls hq hqu hla
    exact absurd (hAR.symm.trans hAR') (by simp)
  | abort =>
    have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
    have hdrop : Server.dropIfBizarre state entryName respA = state := by
      unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
    have hres := resume_cname_abort state respA target q qu hstep hcn htc hnrev hq hqu hla
    unfold Server.afterResume at hAR
    rw [hdrop, hres] at hAR
    exact absurd hAR (by simp)

/-- **Every `.finished (.ok out)` carries the `finalizeAnswer` payload** (answer-terminal inversion).
    Generalizes `afterResume_answer`/`afterResume_nameError` past the positive/NXDOMAIN branches to
    NODATA and every other `.answer` leaf. The resume loop's only `.ok (.done _)` outcome is the
    `stepAnalyzeResponse = .answer` leaf (the referral `.goto .findServers` drives to `.paused`; the
    other constructors map to `.continue`/`.error`), so `out` is `finalizeAnswer` of the accepted
    response. Feeds the *negative*-answer RespAgree bridge, where `answersQueryB respA = false` and
    `afterResume_answer_payload` (which needs `answersQueryB`) does not apply. -/
theorem afterResume_finished_payload_neg
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    out = Resolver.finalizeAnswer
      { state with lastResponse := some respA, currentStep := .analyzeResponse } respA ∧
    cout = (Server.boundStateCache
      { state with lastResponse := some respA, currentStep := .analyzeResponse }).resources.cache := by
  have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
      || !Resolver.classifiableB respA) = false := by rw [hsf, hcls]; rfl
  have hdrop : Server.dropIfBizarre state entryName respA = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  have hresp1 :
      ({ state with lastResponse := some respA, currentStep := .analyzeResponse } :
        Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
          VeriDNS.Spec.ResourceRecord).lastResponse = some respA := rfl
  unfold Server.afterResume at hAR
  rw [hdrop, Resolver.resume] at hAR
  rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step, hstep, Resolver.stepSendQueries] at hAR
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop] at hAR
  simp only [Resolver.step] at hAR

  split at hAR
  ·
    rename_i X Xst heq
    injection hAR with h hcout
    injection h with h
    split at heq
    ·
      rename_i resp rst heq2
      have hpay := stepAnalyzeResponse_answer_payload_neg _ respA resp rst hresp1 hcname hans heq2
      injection heq with he
      injection he with he hst
      constructor
      · rw [← h, ← he]; exact hpay.1
      · rw [← hcout, ← hst, hpay.2]
    ·
      rename_i ns s' heq2
      obtain ⟨hns, hlr⟩ := stepAnalyzeResponse_goto_shape _ respA ns s' hresp1 hcname hbiz heq2
      subst hns
      rw [show (62 : Nat) = 60 + 2 from rfl] at heq
      obtain ⟨st, hp⟩ := loop_findServers_paused
        ({ s' with currentStep := VeriDNS.Spec.AlgorithmStep.findServers }) rfl hlr 60
      rw [hp] at heq; exact absurd heq (by simp)
    ·
      exact absurd heq (by simp)
    ·
      exact absurd heq (by simp)
  ·
    exact absurd hAR (by simp)
  ·
    exact absurd hAR (by simp)

/-- The positive (`answersQueryB = true`) sibling of `afterResume_finished_payload_neg`: the
    delivery WRITES the answer section first (RFC 1034 caching of delivered answers), so the
    returned output cache is the bounded WRITTEN cache. -/
theorem afterResume_finished_payload_pos
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    out = Resolver.finalizeAnswer
      { state with lastResponse := some respA, currentStep := .analyzeResponse } respA ∧
    cout = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      state.resources.cache respA
      (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
        state.resources.sname respA.answer)
      (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundExpiryClasses := by
  rw [afterResume_answer state entryName respA hstep hcname hsf hcls hans] at hAR
  injection hAR with h hcout
  injection h with h
  exact ⟨h.symm, hcout.symm⟩

/-- **Every `.finished (.ok out)` carries the `finalizeAnswer` payload** — the hans-free output
    form (the returned CACHE differs between the positive/negative deliveries; use the `_pos`/
    `_neg` variants to pin it). Feeds `respAgree_finished_bridge`, which needs only the output. -/
theorem afterResume_finished_payload_out
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    out = Resolver.finalizeAnswer
      { state with lastResponse := some respA, currentStep := .analyzeResponse } respA := by
  by_cases hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true
  · exact (afterResume_finished_payload_pos state entryName respA out
      hstep hcname hsf hcls hans hAR).1
  · exact (afterResume_finished_payload_neg state entryName respA out
      hstep hcname hsf hcls (Bool.eq_false_iff.mpr hans) hAR).1

/-- **The answer-terminal RespAgree bridge, negative case** (NODATA / NXDOMAIN). The sibling of
    `respAgree_answer_bridge` that drops the `answersQueryB = true` premise: it pins the delivered
    output via `afterResume_finished_payload` (which holds for *any* `.finished (.ok _)`), so the
    rcode + answer agreement transfers to the verdict whether the accepted response was a positive
    answer or a negative one. For an empty CNAME chain the `aa`-flip is invisible to `RespAgree`. -/
theorem respAgree_finished_bridge
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA resp : VeriDNS.Spec.Format} {ref : VeriDNS.Spec.Net.Response}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB respA = true)
    {cout : Cache.DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok resp) cout)
    (hchain : state.cnameChain = #[])
    (hragA : RespAgree (αResp respA) ref) :
    RespAgree (αResp resp) { ref with aa := false } := by
  have hpay := afterResume_finished_payload_out state entryName respA resp
    hstep hcname hsf hcls hAR
  have hrc : (αResp resp).rcode = αRCode respA.header.rcode := by
    rw [hpay]; exact finalizeAnswer_abstracts_rcode _ respA
  have han : (αResp resp).answer = αSection state.cnameChain ++ αSection respA.answer := by
    rw [hpay, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
  rw [hchain] at han
  refine RespAgree.trans (RespAgree.of_eq ?_ ?_) hragA
  · rw [hrc, (αResp_components respA).1]
  · rw [han, (αResp_components respA).2.1]
    simp [αSection]

/-- **`.finished` excludes a bizarre response** (answer-terminal dispatch helper). If `afterResume` reaches
    `.finished` (with `cnameToChase = none`), the response was NOT server-failure / unclassifiable — because
    `afterResume_bizarre` would otherwise have yielded `.continue` (the resolver retries bizarre responses).
    Discharges `serverAnswer_hasVerdict`'s `hsf`/`hcls` obligations at the driver's answer terminal. -/
theorem afterResume_finished_not_bizarre
    {state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA : VeriDNS.Spec.Format} {result : Except String VeriDNS.Spec.Format}
    {cout : Cache.DnsCache}
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hAR : Server.afterResume state entryName respA = .finished result cout) :
    (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
      ∧ Resolver.classifiableB respA = true := by
  by_cases hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false
  · by_cases hcls : Resolver.classifiableB respA = true
    · exact ⟨hsf, hcls⟩
    · exfalso
      have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
          || !Resolver.classifiableB respA) = true := by
        simp only [Bool.not_eq_true] at hcls; rw [hcls]; simp
      rw [afterResume_bizarre state entryName respA hstep hcname hbiz] at hAR
      exact Server.IoStep.noConfusion hAR
  · exfalso
    have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = true := by
      simp only [Bool.not_eq_false] at hsf; rw [hsf]; simp
    rw [afterResume_bizarre state entryName respA hstep hcname hbiz] at hAR
    exact Server.IoStep.noConfusion hAR

/-- **A response classified as a referral has a non-empty NS-name list.** `hasRRTypeIn authority 2` (an NS
    record parses out of the authority section) forces `extractNsNames authority ≠ #[]` — the witnessing raw
    RR maps to `some (rrRdata rr)` under the `filterMap`. So the implementation's post-referral SLIST
    (`setUpAddresses (extractNsNames …) …`) has at least one server (`searchFails = false`): the referral is
    followable. A building block for the `afterResume = .continue` referral inversion (the SLIST connector). -/
theorem extractNsNames_ne_of_hasRRTypeIn {RR : Type} [VeriDNS.Spec.RRParse RR]
    (authority : Array ByteArray)
    (h : Resolver.hasRRTypeIn (RR := RR) authority 2 = true) :
    Resolver.extractNsNames (RR := RR) authority ≠ #[] := by
  unfold Resolver.hasRRTypeIn at h
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, hp⟩ := h
  have hmem : authority[i] ∈ authority := Array.getElem_mem hi
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := RR) authority[i] with
  | none => rw [hpr] at hp; exact absurd hp (by simp)
  | some rr =>
    simp only [hpr] at hp
    intro hempty
    have hmemNs : VeriDNS.Spec.RRParse.rrRdata rr ∈ Resolver.extractNsNames (RR := RR) authority := by
      unfold Resolver.extractNsNames
      rw [Array.mem_filterMap]
      refine ⟨authority[i], hmem, ?_⟩
      simp only [hpr]
      split
      · rfl
      · rename_i hne; exact absurd hp hne
    rw [hempty] at hmemNs
    exact absurd hmemNs (by simp)

/-- **`hclose` discharge for the referral `.continue` SLIST inversion.** Packages `currentCloser_false_of_ge`
    with the NS-nonempty fact (`extractNsNames_ne_of_hasRRTypeIn`): a referral whose authority carries NS records
    (`hns`) and whose delegation match-count is `≤` the `walkNs` cut depth (`hge`, the walk-trace fact) yields
    `currentCloser = false` — so `stepFindServers` takes the cache-RE-DERIVE branch. The driver supplies `hns`
    from the classifier and `hge` from the `walkNs` trace; this discharges `afterResume_referral_continue_slist`'s
    `hclose` hypothesis. -/
theorem currentCloser_false_referral (resp : VeriDNS.Spec.Format) (walkMc : Nat) (sname : ByteArray)
    (glue : Array (ByteArray × BitVec 32))
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname ≤ walkMc) :
    (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority) glue
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname))
      && decide (walkMc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority) glue
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority sname)))) = false := by
  apply currentCloser_false_of_ge
  · have hne := extractNsNames_ne_of_hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority hns
    simpa using hne
  · exact hge

/-- **Each `extractNsNames` element comes from a raw NS (`type 2`) record in the authority section.** The
    membership-inversion building block for the referral SLIST connector (step 4c): the impl's NS-host list
    `extractNsNames resp.authority` (the names `fromNsWithGlue` seeds the SLIST from) is exactly the rdata of
    the authority's NS records, so under decode-validity it abstracts to the model's `referredServers (αResp
    resp)` (each NS rdata `αName`s to a model host). Mirrors `extractCname_some`. -/
theorem mem_extractNsNames {RR : Type} [VeriDNS.Spec.RRParse RR] (authority : Array ByteArray) (b : ByteArray)
    (h : b ∈ Resolver.extractNsNames (RR := RR) authority) :
    ∃ raw ∈ authority, ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := RR) raw = some rr
      ∧ (VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)) = true
      ∧ VeriDNS.Spec.RRParse.rrRdata rr = b := by
  simp only [Resolver.extractNsNames, Array.mem_filterMap] at h
  obtain ⟨raw, hraw, hcond⟩ := h
  cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := RR) raw with
  | none => rw [hpr] at hcond; simp at hcond
  | some rr =>
    simp only [hpr] at hcond
    split at hcond
    · next hty => exact ⟨raw, hraw, rr, hpr, hty, Option.some.inj hcond⟩
    · simp at hcond

/-- **Each `extractGlueRecords` entry comes from a raw 4-byte `A` (`type 1`) record in the additional section.**
    The glue-side membership-inversion building block (parallel to `mem_extractNsNames`): the impl's glue
    `(name, addr)` pairs — the addresses `fromNsWithGlue` seeds the SLIST with — are exactly the additional
    section's A records (owner `name`, 4-byte rdata). The structural half of the referral SLIST connector's
    glue correspondence (step 4c (ii)); the address-value abstraction (`addr ↔ αIPv4`) is the BV-level remainder. -/
theorem mem_extractGlueRecords (additional : Array ByteArray) (name : ByteArray) (addr : BitVec 32)
    (h : (name, addr) ∈ Resolver.extractGlueRecords additional) :
    ∃ raw ∈ additional, ∃ rr off, DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw = .ok (rr, off)
      ∧ (rr.type == (1 : BitVec 16)) = true ∧ (rr.rdata.size == 4) = true ∧ rr.name = name := by
  simp only [Resolver.extractGlueRecords, Array.mem_filterMap] at h
  obtain ⟨raw, hraw, hcond⟩ := h
  cases hpr : DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw with
  | error e => simp only [hpr] at hcond; simp at hcond
  | ok p =>
    obtain ⟨rr, off⟩ := p
    simp only [hpr] at hcond
    split at hcond
    · next hc =>
      rw [Bool.and_eq_true] at hc
      refine ⟨raw, hraw, rr, off, hpr, hc.1, hc.2, ?_⟩
      exact (Prod.mk.inj (Option.some.inj hcond)).1
    · simp at hcond

/-- **Glue pair ↔ model `A`-record address.** Each impl glue `(name, addr)` from `extractGlueRecords` comes
    from a decoded 4-byte `A` record whose model address (`αIPv4 rr.rdata`) the impl's queried byte address
    names exactly: `byteAddrToModel (ipv4ToAddr addr) = a.toDotted`. Combines `mem_extractGlueRecords` (the
    record), the `αIPv4` size-4 hit, and `extractGlue_addr_αIPv4` (the BV address round-trip). The glue
    address half of the referral SLIST connector's correspondence (step 4c (ii)), ready to compose with the
    cache round-trip (the absorbed cache stores exactly these glue records, retrieved by `findServers`). -/
theorem extractGlueRecords_model_addr (additional : Array ByteArray) (name : ByteArray) (addr : BitVec 32)
    (h : (name, addr) ∈ Resolver.extractGlueRecords additional) :
    ∃ raw ∈ additional, ∃ rr off a, DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw = .ok (rr, off)
      ∧ (rr.type == (1 : BitVec 16)) = true ∧ rr.name = name ∧ αIPv4 rr.rdata = some a
      ∧ byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr addr) = a.toDotted := by
  simp only [Resolver.extractGlueRecords, Array.mem_filterMap] at h
  obtain ⟨raw, hraw, hcond⟩ := h
  cases hpr : DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw with
  | error e => simp only [hpr] at hcond; simp at hcond
  | ok p =>
    obtain ⟨rr, off⟩ := p
    simp only [hpr] at hcond
    split at hcond
    · next hc =>
      rw [Bool.and_eq_true] at hc
      obtain ⟨hname, haddr⟩ := Prod.mk.inj (Option.some.inj hcond)
      have hsz : rr.rdata.size = 4 := by simpa using hc.2
      have ha : αIPv4 rr.rdata
          = some ⟨rr.rdata.data[0]!, rr.rdata.data[1]!, rr.rdata.data[2]!, rr.rdata.data[3]!⟩ := by
        unfold αIPv4; rw [if_pos hsz]
      refine ⟨raw, hraw, rr, off, _, hpr, hc.1, hname, ha, ?_⟩
      rw [← haddr]
      exact extractGlue_addr_αIPv4 rr.rdata _ ha
    · simp at hcond

/-- **Every referral-SLIST address (from direct glue) is a model `A`-record address from the additional
    section.** The impl seeds its referral SLIST via `fromNsWithGlue names (extractGlueRecords additional)`;
    each resulting model-image address (`modelSlistOf`) is the dotted form of an `αIPv4`-abstracted A record
    in `additional`. Composes `modelSlistOf_fromNsWithGlue` (per-host `findSome?`) with
    `extractGlueRecords_model_addr` (glue pair → model A). The address-set ⊆ direction of the referral SLIST
    connector (step 4c); pairs with the cache round-trip (the absorbed cache stores exactly this glue) and the
    per-host dedup `Perm` to `glueAddresses`. -/
theorem modelSlistOf_fromNsWithGlue_model (names additional : Array ByteArray) (mc : Nat) (s : String)
    (h : s ∈ modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names
        (Resolver.extractGlueRecords additional) mc)) :
    ∃ raw ∈ additional, ∃ rr off a, DnsParser.run VeriDNS.Impl.ResourceRecord.decode raw = .ok (rr, off)
      ∧ (rr.type == (1 : BitVec 16)) = true ∧ αIPv4 rr.rdata = some a ∧ s = a.toDotted := by
  rw [modelSlistOf_fromNsWithGlue, List.mem_filterMap] at h
  obtain ⟨n, _, hmap⟩ := h
  rw [Option.map_eq_some_iff] at hmap
  obtain ⟨ga, hga, hs⟩ := hmap
  obtain ⟨p, hmem, hpred⟩ := Array.exists_of_findSome?_eq_some hga
  obtain ⟨gn, ga'⟩ := p
  simp only [] at hpred
  have hga'eq : ga' = ga := by
    split at hpred
    · exact Option.some.inj hpred
    · simp at hpred
  subst ga'
  obtain ⟨raw, hraw, rr, off, a, hdec, htype, _, hαiv, haddr⟩ :=
    extractGlueRecords_model_addr additional gn ga hmem
  exact ⟨raw, hraw, rr, off, a, hdec, htype, hαiv, by rw [← hs, haddr]⟩

/-- **Referral SLIST connector — the reduction.** The impl's post-referral model SLIST
    (`modelSlistOf (fromNsWithGlue names glueRaw mc)`) EQUALS the model `glueAddresses ref`, given (a) the
    ordered host-list correspondence `names.toList.filterMap αName = referredServers ref` (discharged by
    `extractNsNames_referredServers_αResp`) and (b) the per-host glue agreement `hpoint`: for each raw NS name
    `n`, the impl's first matching glue address abstracts to the model's first in-bailiwick `A` glue for the
    abstract host. Both `glueAddresses` and `modelSlistOf_fromNsWithGlue` are `hosts.filterMap (per-host)`, so
    this is a `filterMap` fusion + congruence. Equality ⟹ the `Perm` that `refer_hasVerdict_perm` consumes —
    isolating the ENTIRE remaining refer-connector obligation into the single pointwise fact `hpoint`. -/
theorem modelSlistOf_referral_eq_glueAddresses
    (names : Array ByteArray) (glueRaw : Array (ByteArray × BitVec 32)) (mc : Nat)
    (ref : VeriDNS.Spec.Net.Response)
    (hhosts : names.toList.filterMap αName = VeriDNS.Spec.Net.referredServers ref)
    (hpoint : ∀ n ∈ names.toList,
        (glueRaw.findSome? (fun (gn, ga) =>
            if VeriDNS.Impl.DomainName.nameEqCI gn n then some ga else none)).map
            (fun a => byteAddrToModel (VeriDNS.Impl.Server.ipv4ToAddr a))
          = (αName n).bind (fun h =>
              (ref.additional.find? (fun r =>
                  (match r.rdata with | VeriDNS.Spec.Net.RData.a _ => true | _ => false)
                    && VeriDNS.Spec.Net.nameEq h r.owner
                    && VeriDNS.Spec.Net.isAncestor (VeriDNS.Spec.Net.referralCut ref) r.owner)).bind
                (fun r => match r.rdata with
                  | VeriDNS.Spec.Net.RData.a a => some a.toDotted | _ => none))) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue names glueRaw mc)
      = VeriDNS.Spec.Net.glueAddresses ref := by
  rw [modelSlistOf_fromNsWithGlue]
  unfold VeriDNS.Spec.Net.glueAddresses
  rw [← hhosts, List.filterMap_filterMap]
  exact filterMap_congr_mem _ _ _ hpoint

/-- **Glue-extraction / bailiwick-filter fusion.** `extractGlueRecords (bailiwickRaws cut additional)` is a
    SINGLE pass over `additional`: keep a record iff it is in-bailiwick AND a 4-byte `A`. Fuses the impl's
    `filter`-then-`filterMap` via `Array.filterMap_filter` — the structural handle that lets `hpoint`'s
    per-host `findSome?` be compared to the model's `find?` by one induction over `additional` (rather than
    over the doubly-transformed intermediate). -/
theorem extractGlueRecords_bailiwickRaws_fused (cut : ByteArray) (additional : Array ByteArray) :
    Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut additional)
      = additional.filterMap (fun bytes =>
          if (match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
                | some rr => Resolver.isAncestorB cut
                    (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr)
                | none => false)
          then (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode bytes with
                | .ok (rr, _) =>
                  if rr.type == BitVec.ofNat 16 1 && rr.rdata.size == 4 then
                    some (rr.name,
                      (rr.rdata.data[0]!.toBitVec.setWidth 32 <<< 24) |||
                      (rr.rdata.data[1]!.toBitVec.setWidth 32 <<< 16) |||
                      (rr.rdata.data[2]!.toBitVec.setWidth 32 <<< 8) |||
                      rr.rdata.data[3]!.toBitVec.setWidth 32)
                  else none
                | .error _ => none)
          else none) := by
  unfold Resolver.extractGlueRecords Resolver.bailiwickRaws
  rw [Array.filterMap_filter]
  congr 1
  funext bytes
  cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes <;> rfl

/-- **`findSome?` over `filterMap` fuses** (the missing core companion to `List.find?_filterMap`): scanning
    `l.filterMap f` for the first `p`-hit is scanning `l` for the first `(f ·).bind p`-hit. With
    `extractGlueRecords_bailiwickRaws_fused` this turns `hpoint`'s impl-side per-host `findSome?` into a
    single scan over `additional`, matching the model's `find?` over the same section. -/
theorem findSome?_filterMap_list {α β γ : Type} (f : α → Option β) (p : β → Option γ) (l : List α) :
    (l.filterMap f).findSome? p = l.findSome? (fun x => (f x).bind p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hfa : f a with
    | none => simp_all [List.filterMap_cons]
    | some b =>
      cases hpb : p b with
      | none => simp_all [List.filterMap_cons]
      | some c => simp_all [List.filterMap_cons]

/-- **`findSome?` respects pointwise-equal option-functions on the list** — the congruence that lets `hpoint`
    conclude its two reduced `findSome?` scans (impl glue vs model glue, both over `additional`) are equal once
    their per-element option functions are shown to agree via the name/bailiwick/address bridges. -/
theorem findSome?_congr_pred {α β : Type} (l : List α) (f g : α → Option β) (h : ∀ x ∈ l, f x = g x) :
    l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a (List.mem_cons_self ..)]
    cases g a with
    | none => exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | some b => rfl

/-- **Two `Nodup` lists with the same membership are permutations.** Via `perm_iff_count` + `Nodup.count`
    (nodup ⟹ `count = mem-indicator`). The multiset-layer tool for honest-refer: the cache-re-derived `nsNames`
    (deduped by `cacheRRs`) and `extractNsNames` (no-dup under the well-formedness conjunct) are both nodup with
    equal membership (set-level cache round-trip), hence `Perm` — which `refer_hasVerdict_perm` accepts. -/
theorem perm_of_nodup_mem {α : Type} [BEq α] [LawfulBEq α] {l l' : List α}
    (h : l.Nodup) (h' : l'.Nodup) (hmem : ∀ a, a ∈ l ↔ a ∈ l') : l.Perm l' := by
  rw [List.perm_iff_count]
  intro a
  rw [List.Nodup.count h, List.Nodup.count h']
  simp only [hmem a]

/-- **`find?` respects pointwise-equal predicates on the list** — the scan-congruence step `hpoint` uses to
    conclude the impl and model glue `find?` scans return the SAME element once their per-element predicates
    are shown to agree (via the name/bailiwick/address bridges). General, dependency-free. -/
theorem find?_congr_pred {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..)]
    cases hq : q a with
    | true => rfl
    | false => exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- **`Option.map` commutes through `findSome?`** — `(l.findSome? f).map g = l.findSome? (fun x => (f x).map g)`.
    Lets `hpoint` push the impl glue scan's outer `byteAddrToModel∘ipv4ToAddr` map inside the `findSome?`, so
    both sides become a single `findSome?` over `additional` with per-element option functions to equate. -/
theorem findSome?_map_comm {α β γ : Type} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.findSome? f).map g = l.findSome? (fun x => (f x).map g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hfa : f a with
    | none =>
      rw [List.findSome?_cons_of_isNone (by simp [hfa]),
          List.findSome?_cons_of_isNone (by simp [hfa])]
      exact ih
    | some b =>
      rw [List.findSome?_cons_of_isSome (by simp [hfa]),
          List.findSome?_cons_of_isSome (by simp [hfa])]

/-- **`(find? p).bind g` is a `findSome?`** when `g` never fails on a `p`-hit — the model-side unification that
    turns `glueAddresses`' `find? (A ∧ owner ∧ bailiwick) >>= (·.rdata.toDotted)` into a `findSome?` matching the
    impl glue scan's shape (the `A`-predicate guarantees `.rdata = .a a`, so the extract is always `some`). -/
theorem find?_bind_eq_findSome? {α β : Type} (p : α → Bool) (g : α → Option β) (l : List α)
    (h : ∀ x ∈ l, p x = true → (g x).isSome = true) :
    (l.find? p).bind g = l.findSome? (fun x => if p x then g x else none) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hpa : p a with
    | false =>
      simp only [List.find?_cons, hpa, Bool.false_eq_true, if_false]
      rw [List.findSome?_cons_of_isNone (by simp [hpa])]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | true =>
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..) hpa)
      simp [List.find?_cons, hpa, hc]

/-- **`findSome?` of an `if p then some (h ·) else none` is `(find? p).map h`** — the impl glue scan
    `glue.findSome? (fun (gn,ga) => if nameEqCI gn n then some ga else none)` is `(glue.find? (nameEqCI ·.1
    n)).map (·.2)`, i.e. "first owner-matching glue pair, take its address". Since the picked option is always
    `some`, no `isSome` side-condition is needed (unlike the general `find? · >>= g`). Puts `hpoint`'s impl
    side into the same `find?`-over-`additional` shape as the model's `glueAddresses`. -/
theorem findSome?_ite_some {α β : Type} (p : α → Bool) (h : α → β) (l : List α) :
    l.findSome? (fun x => if p x then some (h x) else none) = (l.find? p).map h := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hpa : p a with
    | true => simp_all [List.find?_cons]
    | false => simp_all [List.find?_cons]

/-- **Re-derived glue scan reduces to an NS-name scan.** `stepFindServers` builds glue as
    `nsNames.filterMap (fun m => (lookup m A).findSome? (size4 → some (m, addr)))` — each entry keyed by its
    source NS name `m`. So the per-host glue scan `findSome? (nameEqCI gp.1 n)` collapses to a scan over the NS
    names for the first `nameEqCI`-match that has glue. This is the structural first step of the glue round-trip:
    it turns the re-derived `gluePerHost` into a clean `nsNames`-indexed lookup, ready to match against the
    cache round-trip (`lookup m A` = the absorbed response glue for `m`). -/
theorem rederived_glue_keyed {β : Type} (nsNames : List ByteArray) (n : ByteArray)
    (hglue : ByteArray → Option (ByteArray × β))
    (hkey : ∀ m, ∀ gp ∈ hglue m, gp.1 = m) :
    (nsNames.filterMap hglue).findSome? (fun gp => if DomainName.nameEqCI gp.1 n then some gp.2 else none)
      = nsNames.findSome? (fun m => if DomainName.nameEqCI m n then (hglue m).map Prod.snd else none) := by
  rw [findSome?_filterMap_list]
  apply findSome?_congr_pred
  intro m _
  cases hgm : hglue m with
  | none => simp
  | some gp =>
    have hk : gp.1 = m := hkey m gp (Option.mem_def.mpr hgm)
    simp only [Option.bind_some, hk, Option.map_some]

/-- **A `findSome?` scan whose matching elements all map to the same value `v` returns `v`** (given at least one
    match). The cache lookup respects `nameEqCI` (`liveEntry` matches case-insensitively), so every NS name that
    is `nameEqCI`-equal to host `n` yields the *same* cache-A address. Combined with `rederived_glue_keyed`, this
    pins the re-derived `gluePerHost n` to `(lookup n A).findSome? (size4 → pack)` — the cache-side glue for `n`,
    independent of which `nameEqCI`-variant the scan happens to hit first. -/
theorem findSome?_const_on_pred {α β : Type} (l : List α) (p : α → Bool) (g : α → Option β) (v : Option β)
    (hconst : ∀ m ∈ l, p m = true → g m = v) (hex : ∃ m ∈ l, p m = true) :
    l.findSome? (fun m => if p m then g m else none) = v := by
  cases v with
  | none =>
    rw [List.findSome?_eq_none_iff]
    intro m hm
    show (if p m then g m else none) = none
    by_cases hp : p m
    · rw [if_pos hp, hconst m hm hp]
    · rw [if_neg hp]
  | some w =>
    induction l with
    | nil => exact absurd hex (by simp)
    | cons a t ih =>
      by_cases hp : p a
      · have hfa : (if p a then g a else none) = some w := by
          rw [if_pos hp, hconst a (List.mem_cons_self ..) hp]
        rw [List.findSome?_cons, hfa]
      · have hfa : (if p a then g a else none) = none := by rw [if_neg hp]
        rw [List.findSome?_cons, hfa]
        exact ih
          (by obtain ⟨m, hm, hpm⟩ := hex
              rcases List.mem_cons.mp hm with rfl | hmt
              · exact absurd hpm hp
              · exact ⟨m, hmt, hpm⟩)
          (fun m hm hpm => hconst m (List.mem_cons_of_mem a hm) hpm)

/-- **The re-derived per-host glue collapses to the host's own cache-A lookup.** Assembling the three glue
    round-trip pieces: `rederived_glue_keyed` (the keyed glue scan → an NS-name scan), then `findSome?_const_on_pred`
    (matching elements all give the same value, since `aGlue` respects `nameEqCI`), with the match witness from
    `nameEqCI_refl` + `n ∈ nsNames`. So `modelSlistOf`'s `gluePerHost n` over the re-derived glue equals `aGlue n`
    — the cache-A lookup for `n` itself. The `hresp` hypothesis (`aGlue` respects `nameEqCI`) is discharged by
    `lookup_nameEqCI_congr` at use. This isolates the remaining work to the cache round-trip: `aGlue n` = the
    absorbed `respA` glue for `n` (matching `glue_per_host_eq`'s model side). -/
theorem gluePerHost_rederived {β : Type} (nsNames : List ByteArray) (n : ByteArray)
    (aGlue : ByteArray → Option β) (hn : n ∈ nsNames)
    (hresp : ∀ m ∈ nsNames, nameEqCI m n = true → aGlue m = aGlue n) :
    (nsNames.filterMap (fun m => (aGlue m).map (Prod.mk m))).findSome?
        (fun gp => if nameEqCI gp.1 n then some gp.2 else none)
      = aGlue n := by
  have hkey : ∀ m, ∀ gp ∈ (fun m => (aGlue m).map (Prod.mk m)) m, gp.1 = m := by
    intro m gp hgp
    change gp ∈ (aGlue m).map (Prod.mk m) at hgp
    cases hag : aGlue m with
    | none => rw [hag] at hgp; simp at hgp
    | some a => rw [hag] at hgp; simp only [Option.map_some, Option.mem_some_iff] at hgp; subst hgp; rfl
  rw [rederived_glue_keyed nsNames n (fun m => (aGlue m).map (Prod.mk m)) hkey]
  have hmap : ∀ m, ((aGlue m).map (Prod.mk m)).map Prod.snd = aGlue m := by
    intro m; cases aGlue m <;> rfl
  simp only [hmap]
  exact findSome?_const_on_pred nsNames (fun m => nameEqCI m n) aGlue (aGlue n)
    (fun m hm hpm => hresp m hm hpm) ⟨n, hn, VeriDNS.Proof.NameTree.nameEqCI_refl n⟩

theorem afterResume_referral_continues
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp⟩ := resume_referral_paused state resp hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  unfold Server.afterResume
  rw [hdrop, hp]
  exact ⟨_, rfl⟩

/-- **Structural `afterResume` referral inversion** — the driver-facing form. When a followable referral
    `afterResume`s to `.continue st`, `st`'s cache is the two bailiwick-filtered `cacheUnlessTruncated` writes
    over the input cache, with the query name / clock / cname chain unchanged and `currentStep = .sendQueries`.
    Together with `stepFindServers_frame` (already inside, via `resume_referral_paused_struct`) this discharges
    `StateModels_refer_preserve`'s `hcache`/`hsname`/`hnowB` and the IH's `currentStep = .sendQueries` for the
    `.continue` referral case. -/
theorem afterResume_referral_continue_struct
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
              (Resolver.credAuthority (resp.header.aa == 1)) state.now)
            resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
            Resolver.credAdditional state.now).boundExpiryClasses
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp, hc, hsn, hnw, hcc, hcs⟩ :=
    resume_referral_paused_struct state resp hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  unfold Server.afterResume
  rw [hdrop, hp]
  refine ⟨Server.boundStateCache st, rfl, ?_, hsn, hnw, hcc, hcs⟩
  show (st.resources.cache).boundExpiryClasses = _
  rw [hc]

/-- **Case-analysing driver-facing referral `.continue` inversion.** The `boundStateCache`-wrapped analogue of
    `afterResume_referral_continue_slist` that drops the `walkNs`/`currentCloser` hypotheses and returns the
    full SLIST disjunction. `boundStateCache` touches only the cache (wrapping it in `boundExpiryClasses`), so
    the SLIST disjunction passes through unchanged. This is the single inversion the driver's honest-referral
    arm consumes to route the cache-rebuild branch (ttl>0) to the model's cache-re-derived SLIST and the
    transient-keep branch (ttl=0) to the response's bailiwick-filtered glue. -/
theorem afterResume_referral_continue_cases
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now).boundExpiryClasses
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery
      ∧ st.resources.sbelt = state.resources.sbelt
      ∧ ( st.resources.slist = (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc)
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) nsNames
                  (reGlue (RR := VeriDNS.Spec.ResourceRecord) (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now) state.now nsNames) mc)
          ∨ (st.resources.slist = state.resources.sbelt
              ∧ (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
                  && decide (0 < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry) (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false) ) := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp, hcache, hsn, hnw, hcc, hcs, hlq, hsb, hdisj⟩ :=
    resume_referral_paused_cases state resp hstep hcname hbiz hans hnerr hansEmpty hauth hns haa hrc hsoa
  unfold Server.afterResume
  rw [hdrop, hp]
  refine ⟨Server.boundStateCache st, rfl, ?_, hsn, hnw, hcc, hcs, hlq, ?_, ?_⟩
  · show (st.resources.cache).boundExpiryClasses = _
    rw [hcache]
  · exact hsb
  · exact hdisj

/-- **SLIST-exposing driver-facing referral `.continue` inversion.** Extends `afterResume_referral_continue_struct`
    with the rebuilt SLIST: given the `walkNs` cache-trace (`hwalk`) and the not-already-closer gate (`hclose`),
    `state''.slist = setUpAddresses nsNames glue mc` (the keystone input). `boundStateCache` touches only the
    cache, so the SLIST passes through the wrap unchanged. The last structural ingredient before the keystone
    `hgl` discharge. -/
theorem afterResume_referral_continue_slist
    (state : Resolver.State SList.DnsSList Cache.DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (resp : VeriDNS.Spec.Format) (nsNames : Array ByteArray) (mc : Nat)
    (hstep : state.currentStep = .sendQueries)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = false)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = false)
    (hansEmpty : resp.answer.isEmpty = true)
    (hauth : resp.authority.isEmpty = false)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 2 = true)
    (haa : (resp.header.aa == 0) = true)
    (hrc : (resp.header.rcode == VeriDNS.Spec.Rcode.noError) = true)
    (hsoa : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) resp.authority 6 = false)
    (hwalk : Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) state.resources.sname
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
            (Resolver.credAuthority (resp.header.aa == 1)) state.now)
          resp
          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
          Resolver.credAdditional state.now)
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc))
    (hclose : (!VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
        (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
          (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
          (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname))
        && decide (mc < VeriDNS.Spec.SlistFromNameSpec.matchCount (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority)
            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional))
            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) resp.authority state.resources.sname)))) = false) :
    ∃ st, Server.afterResume state entryName resp = .continue st
      ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList)
          (NS := VeriDNS.Spec.SlistEntry) nsNames
          (reGlue (RR := VeriDNS.Spec.ResourceRecord)
            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache resp
                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.authority)
                (Resolver.credAuthority (resp.header.aa == 1)) state.now)
              resp
              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) resp.authority) resp.additional)
              Resolver.credAdditional state.now)
            state.now nsNames) mc
      ∧ st.resources.sname = state.resources.sname
      ∧ st.now = state.now
      ∧ st.cnameChain = state.cnameChain
      ∧ st.currentStep = .sendQueries
      ∧ st.lastQuery = state.lastQuery := by
  have hdrop : Server.dropIfBizarre state entryName resp = state := by
    unfold Server.dropIfBizarre; rw [if_neg (by simp [hbiz])]
  obtain ⟨st, hp, hsl, _hc, hsn, hnw, hcc, hcs, hlq⟩ :=
    resume_referral_paused_slist state resp nsNames mc hstep hcname hbiz hans hnerr hansEmpty hauth hns
      haa hrc hsoa hwalk hclose
  unfold Server.afterResume
  rw [hdrop, hp]
  exact ⟨Server.boundStateCache st, rfl, hsl, hsn, hnw, hcc, hcs, hlq⟩

theorem storeChecked_ttl_zero (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32) (h : rr.ttl = 0) :
    c.storeChecked rr cred now = c := by
  unfold Cache.DnsCache.storeChecked
  simp [h]

theorem storeChecked_blocks_weaker (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : Trustworthiness) (now : UInt32)
    (e : Cache.CacheEntry) (he : e ∈ c.records)
    (hname : DomainName.nameEqCI e.rr.name rr.name = true)
    (htype : (e.rr.type == rr.type) = true) (hclass : (e.rr.class == rr.class) = true)
    (hfresh : e.expiry > now)
    (hbetter : e.credibility.toCode < cred.toCode)
    (hnz : rr.ttl ≠ 0) :
    c.storeChecked rr cred now = c := by
  obtain ⟨i, hi, hei⟩ := Array.getElem_of_mem he
  have hz : (rr.ttl == 0) = false := by rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; exact hnz
  have hcond : (c.records.any fun e2 =>
      DomainName.nameEqCI e2.rr.name rr.name && e2.rr.type == rr.type && e2.rr.class == rr.class
        && (e2.expiry > now || e2.expiry == now + rr.ttl.toNat.toUInt32)
        && e2.credibility.toCode < cred.toCode) = true := by
    rw [Array.any_eq_true]
    exact ⟨i, hi, by rw [hei]; simp [hname, htype, hclass, hfresh, hbetter]⟩
  unfold Cache.DnsCache.storeChecked
  simp only [hz, hcond, if_false, if_true, Bool.false_eq_true]

theorem finalizeForClient_flags (resp : VeriDNS.Spec.Format) :
    (Server.finalizeForClient resp).header.qr = 1
      ∧ (Server.finalizeForClient resp).header.aa = 0
      ∧ (Server.finalizeForClient resp).header.ra = 1
      ∧ (Server.finalizeForClient resp).header.z = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem acceptResponse_requires_match (sent resp : VeriDNS.Spec.Format)
    (h : Server.acceptResponse sent resp = some resp) :
    (resp.header.id == sent.header.id) = true
      ∧ Server.questionMatches resp.question sent.question = true := by
  unfold Server.acceptResponse at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    exact hcond
  · exact absurd h (by simp)

/-- **negHit simulation branch (NXDOMAIN).** When the executable resolver finds a fresh NXDOMAIN
    entry for the query name in its negative cache, `resolveWithIO` returns a response whose
    observable verdict (`RespAgree`) is exactly the model's `Cache.negResponse`, and the run is a
    valid `Net.Resolves.negHit` derivation against the abstracted cache. The impl's negative-cache
    short-circuit *is* the model's `negHit` constructor — for any network, server set, slist, and
    visited sets (the constructor is independent of them). This is the first fully-assembled forward
    simulation branch of `resolveWithIO ⊑ Net.Resolves`. -/
theorem resolveWithIO_negHit_nx_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqu : query.question[0]? = some qu)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t)
    (hnx : cache.lookupNxdomain qu.qname qu.qclass now = some rc) :
    ∃ resp,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ RespAgree (αResp resp) ((αCache cache).negResponse (αTime now) q)
      ∧ VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q
          ((αCache cache).negTrace (αTime now) q) [] (αTime now) (αCache cache)
          ((αCache cache).negResponse (αTime now) q) := by
  have hlk : cache.lookupNegative qu.qname qu.qtype qu.qclass now = some rc := by
    unfold Cache.DnsCache.lookupNegative; rw [hnx]; rfl
  have hneg : (αCache cache).negHit (αTime now) q = true :=
    lookupNegative_negHit cache qu.qname qu.qtype qu.qclass now rc q t hlk hqn ht hqq
  have hnxName : rc = VeriDNS.Spec.Rcode.nameError :=
    lookupNxdomain_nameError cache qu.qname qu.qclass now rc hnx
  have hnxnx : (αCache cache).negHitNx (αTime now) q = true :=
    lookupNxdomain_negHitNx cache qu.qname qu.qclass now rc q hnx hqn
  have hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection
          (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qu.qname qu.qtype qu.qclass now) #[] :=
    localAnswer_negative cache qu.qtype qu.qclass now 7 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) rc hlk
  refine ⟨_, resolveWithIO_negHit query sbelt cache now fuel depth budget qu rc _ #[] hqu hla, ?_, ?_⟩
  · refine RespAgree.of_eq ?_ ?_
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).2]
      simp only [VeriDNS.Spec.Net.Cache.negResponse, hnxnx, hnxName]
      rfl
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).1]
      simp only [VeriDNS.Spec.Net.Cache.negResponse]
  · exact VeriDNS.Spec.Net.Resolves.negHit (αCache cache) slist q hneg

/-- **negHit simulation branch (NODATA).** The NODATA companion of `resolveWithIO_negHit_nx_simulates`:
    when the negative cache yields a fresh type-specific NODATA entry, the resolver answers `noError`
    with an empty answer, matching the model's `Cache.negResponse` verdict, via `Net.Resolves.negHit`.

    Two hypotheses make the model/impl boundary explicit (both discharged in the final composition
    from a single-class, well-formed-negatives cache invariant): `hnodata` — the model sees no
    NXDOMAIN entry for the name (the model's `NegRR` carries no `qclass`, so it cannot itself rule out
    a same-name NX entry of another class that the impl's class-checked `lookupNxdomain` skips); and
    `hrc` — a NODATA entry carries `Rcode.noError` (the impl never files `servFail` negatives, which
    the abstract `NegRR` does not record). -/
theorem resolveWithIO_negHit_nodata_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqu : query.question[0]? = some qu)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t)
    (hlk : cache.lookupNegative qu.qname qu.qtype qu.qclass now = some rc)
    (hnodata : (αCache cache).negHitNx (αTime now) q = false)
    (hrc : rc = VeriDNS.Spec.Rcode.noError) :
    ∃ resp,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ RespAgree (αResp resp) ((αCache cache).negResponse (αTime now) q)
      ∧ VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q
          ((αCache cache).negTrace (αTime now) q) [] (αTime now) (αCache cache)
          ((αCache cache).negResponse (αTime now) q) := by
  have hneg : (αCache cache).negHit (αTime now) q = true :=
    lookupNegative_negHit cache qu.qname qu.qtype qu.qclass now rc q t hlk hqn ht hqq
  have hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .negative rc (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection
          (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qu.qname qu.qtype qu.qclass now) #[] :=
    localAnswer_negative cache qu.qtype qu.qclass now 7 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) rc hlk
  refine ⟨_, resolveWithIO_negHit query sbelt cache now fuel depth budget qu rc _ #[] hqu hla, ?_, ?_⟩
  · refine RespAgree.of_eq ?_ ?_
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).2]
      simp only [VeriDNS.Spec.Net.Cache.negResponse, hnodata, hrc]
      rfl
    · rw [(αResp_finalizeAnswer_negativeResponse
        { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
            query sbelt now cache with cnameChain := #[] } query rc _ rfl).1]
      simp only [VeriDNS.Spec.Net.Cache.negResponse]
  · exact VeriDNS.Spec.Net.Resolves.negHit (αCache cache) slist q hneg

/-- **cacheHit simulation branch.** When the executable resolver answers directly from its positive
    cache (negative miss, non-empty answerable set, no CNAME chase), `resolveWithIO` returns a
    `noError` response whose answer section is exactly the model's `Cache.hit`, and the run is a valid
    `Net.Resolves.cacheHit` derivation — independent of network/server-set/slist/visited-sets.

    `hhit` (the served-set abstraction equality `αSection (impl answerable set) = (αCache c).hit`) is
    the one remaining cache obligation, taken here as a hypothesis: the impl's `lookupAnswerable`
    (per-key max-credibility, freshness, exact-type, below-`untrustworthyFloor`) refines the model's
    `served` (usable, per-key max `cred.rank` of `matching`). The **RFC 2181 §5.4.1 floor gap is now
    closed**: `Cache.served` carries the `Cred.usable` gate and `αCred_usable` proves it is the *same*
    gate as the impl's `answerableEntry` floor. Two obstacles to a full discharge remain: (i)
    exact-type vs `QType.covers` (holds for `q.qtype = .rr t`, excludes ANY); (ii) **credibility
    granularity** — the model's 4-tier `Cred.rank` is coarser than the impl's 7-level
    `Trustworthiness.toCode`, so within a tier (e.g. `primaryZone`/`zoneTransfer`/`authoritativeSection`
    all abstract to `authoritative`) the impl prefers the strictly-more-credible entry while the model
    treats them as tied. A full discharge needs `Cred.rank` to mirror the whole §5.4.1 ranking plus the
    `filterMap`/`maxCredForKey`↔`served` correspondence. `hne` is the constructor's non-emptiness
    side-condition. -/
theorem resolveWithIO_cacheHit_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (q : VeriDNS.Spec.Net.Query)
    (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hnoneg : cache.lookupNegative qu.qname qu.qtype qu.qclass now = none)
    (hans : VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
        (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now = rrs)
    (hrne : rrs.isEmpty = false)
    (hhit : αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
        = (αCache cache).hit (αTime now) q)
    (hne : 0 < ((αCache cache).hit (αTime now) q).length) :
    ∃ resp,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cache)
      ∧ RespAgree (αResp resp)
          { aa := false, rcode := VeriDNS.Spec.Net.RCode.noError,
            answer := (αCache cache).hit (αTime now) q, authority := [], additional := [] }
      ∧ VeriDNS.Spec.Net.Resolves net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q
          [VeriDNS.Spec.Net.Step.fromCache] [] (αTime now) (αCache cache)
          { aa := false, rcode := VeriDNS.Spec.Net.RCode.noError,
            answer := (αCache cache).hit (αTime now) q, authority := [], additional := [] } := by
  have hla : Resolver.localAnswer (C := Cache.DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qu.qtype qu.qclass now 8 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
      = .answerHit qu.qname #[] rrs :=
    localAnswer_answerHit cache qu.qtype qu.qclass now 7 qu.qname #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[]) rrs hnoneg hans hrne
  obtain ⟨resp, hresp, hrc, hansr⟩ :=
    resolveWithIO_answerHit_payload (M := M) (Sock := Sock)
      query sbelt cache now fuel depth budget qu qu.qname #[] rrs hqu hla
  refine ⟨resp, hresp, ⟨hrc, ?_⟩, ?_⟩
  · rw [hansr, show αSection #[] = [] from rfl, List.nil_append, hhit]
  · exact VeriDNS.Spec.Net.Resolves.cacheHit (αCache cache) slist q
      ((αCache cache).hit (αTime now) q) rfl hne

section NetworkBranches
open VeriDNS.Spec.Net

/-- **`answer` branch as a `HasVerdict` producer.** Given the model's single-hop authoritative-answer
    obligations (server found, `ServerAnswers`, in-transit, accepted, on-wire, not a referral/CNAME,
    untruncated) and the abstraction bridge `RespAgree v {reply.msg with aa := false}`, the model
    admits verdict `v`. The premise set is exactly `Net.Resolves.answer`'s; the FreeIO `World` round
    `run_resolveWithIO_networkAnswer` is what supplies these concretely on the impl side. -/
theorem answer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step)
    (resp : Response) (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr resp)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q)
        (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
    (hnr : reply.msg.isReferral = false)
    (hnc : cnameRR reply.msg.answer = none ∨ q.qtype.covers RRType.cname = true
            ∨ (∃ rr ∈ reply.msg.answer, q.qtype.covers rr.rdata.rtype = true))
    (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply
     htrans hacc hwire hnr hnc htc, hbridge⟩

/-- **`trustedReply` branch as a `HasVerdict` producer** — the off-path/spoofed accepted answer (RFC 5452
    threat model). Any delivered `accepts`-passing reply (origin need not be the queried server) justifies
    the returned verdict via `Net.Resolves.trustedReply`. Used by the driver's answer terminal when
    `WorldModels` reports the SPOOFED disjunct (the honest disjunct goes through `serverAnswer_hasVerdict`). -/
theorem trustedReply_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hnr : reply.msg.isReferral = false) (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false })

    (cf0 : Cache)
    (hcf0 : WriteRefines now cf0 (c.absorb now q.qname { reply.msg with authority := [], additional := [] })
            ∨ cf0 = c)
    (cf : Cache) (hcf : WriteRefines now cf cf0) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc
     cf0 hcf0 cf hcf, hbridge⟩

/-- **`trustedReferral` branch as a `HasVerdict` producer** — the off-path/spoofed *cache-writing* referral
    (RFC 5452). Any delivered `accepts`-passing reply the resolver classifies as a referral and follows
    justifies the verdict via `Net.Resolves.trustedReferral`: it caches the reply's bailiwick-filtered records
    (bounded to the query-ancestor `referralCut`, `hcut`) and rebuilds the SLIST, then recurses (`hrec`). Used
    by the driver's referral terminal when `WorldModels` reports the SPOOFED disjunct (the honest disjunct goes
    through `serverReferForget_hasVerdict`). -/
theorem trustedReferral_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (frontier : Name)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hcut : isAncestor (referralCut reply.msg) q.qname = true)
    (hdesc : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String) (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick frontier (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨ftr, rpath, tEnd, cout, final, hres, hbridge⟩ := hrec
  exact ⟨_, _, _, _, _,
    Resolves.trustedReferral addr origin rest q frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hres,
    hbridge⟩

/-- **`refer` branch as a `HasVerdict` producer** (glued referral descent; the recursive sub-run's
    derivation `hrec` is threaded, as the inductive composition would supply it). -/
theorem refer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
    (id srcPort : Nat) (c cout : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hglue : glueAddresses reply.msg ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now')
    (sl : List String)
    (hsl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm sl)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg)
        sl q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.refer addr rest q srv tr ref ftr rpath tEnd final id srcPort c cout
     hmiss hnmiss hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec,
   hbridge⟩

/-- **`referForget` branch as a `HasVerdict` producer** — identical to `refer_hasVerdict` except the recursive
    resolution runs over the resolver's own continuation caches: `cf0` (the post-referral-write cache image,
    write-refining the model absorb from the continuation time — `hcf0`) and `cf` (`cf0` after the RFC 1035
    §7.4 capacity eviction — `hcf`), with the recursive SLIST re-derived from `cf0` (`hsl`).
    `WriteRefines.refl` recovers the exact-cache case; the forward simulation supplies
    `cf0 = αCache(post-write cache)`, `cf = αCache(boundStateCache …)`, `hcf0` from the warm-write refinement,
    and `hcf` from the eviction refinement. -/
theorem referForget_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
    (id srcPort : Nat) (c cout : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now')
    (sl : List String)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache)
    (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        cf sl q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.referForget addr rest q srv tr ref ftr rpath tEnd final id srcPort c cout
     hmiss hnmiss hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec,
   hbridge⟩

/-- **`answerCname` branch as a `HasVerdict` producer** (network CNAME chase; output prepends the
    CNAME RR to the recursive run's answer). -/
theorem answerCname_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (resp : Response)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr resp)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q)
        (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
    (hcn : cnameRR reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname { reply.msg with authority := [], additional := [] }))
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
     hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

/-- **`trustedCname` branch as a `HasVerdict` producer** (the spoofed CNAME chase — an `accepts`-passing
    forgery followed exactly as the impl does; the RFC 5452 threat-model escape for the cname arms). -/
theorem trustedCname_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hcn : cnameRR reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname { reply.msg with authority := [], additional := [] }))
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
     hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

/-- **`cacheCname` branch as a `HasVerdict` producer** (cached CNAME chase). -/
theorem cacheCname_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (slist : List String) (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen)
    (cf : Cache) (hcf : CacheRefines cf c)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
        { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v :=
  ⟨_, _, _, _, _,
   Resolves.cacheCname slist q cn target c nsl ftr rpath tEnd cout final
     hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec, hbridge⟩

/-- **HasVerdict-threading form of `cacheCname_hasVerdict`** (the cached CNAME chase, verdict-transforming).
    Like `answerCname_hasVerdict_hv` but for the cache-hit branch (no network round): destructure the IH's
    `HasVerdict` for the sub-query at `qname := target`, prepend the cached CNAME RR to the verdict
    (`hva : v.answer = cn :: vsub.answer`), and rebuild via `Resolves.cacheCname`. Completes the `_hv` wrapper
    set the `(depth,fuel)` induction needs for the cache-hit CNAME branch. -/
theorem cacheCname_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (slist : List String) (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen)
    (cf : Cache) (hcf : CacheRefines cf c)
    (vsub v : Response) (hrc : v.rcode = vsub.rcode) (hva : v.answer = cn :: vsub.answer)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
        { q with qname := target } vsub) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v := by
  obtain ⟨tr', sp', tEnd', cout', resp', hres, hag⟩ := hrec
  refine ⟨_, _, _, _, _, Resolves.cacheCname slist q cn target c nsl tr' sp' tEnd' cout' resp'
    hmiss hnmiss hcn hqt htgt hfresh cf hcf hres, ?_⟩
  exact ⟨hrc.trans hag.1, by rw [hva]; exact List.Perm.cons cn hag.2⟩

/-- **`cacheHit` branch as a `HasVerdict` producer** (the answer is already in the cache; no network round).
    Wraps `Resolves.cacheHit`: a non-empty positive cache hit for `q` yields the served-from-cache response.
    The terminal of a CNAME chase whose target's records are cached (`answerCname`'s recursive `hrec`), and
    of the initial direct cache hit. -/
theorem cacheHit_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query) (here : List RR)
    (hhit : c.hit now q = here) (hne : 0 < here.length)
    (v : Response)
    (hbridge : RespAgree v (VeriDNS.Spec.Net.Response.mk false VeriDNS.Spec.Net.RCode.noError here [] [] false false)) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v :=
  ⟨_, _, _, _, _, Resolves.cacheHit c slist q here hhit hne, hbridge⟩

/-- **`negHit` branch as a `HasVerdict` producer** (the denial is already in the negative cache; no network
    round). Wraps `Resolves.negHit`: a fresh negative cache entry for `q` yields the synthesized negative
    response. The negative-target terminal of a CNAME chase whose target is cached as a denial. -/
theorem negHit_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query)
    (hneg : c.negHit now q = true)
    (v : Response) (hbridge : RespAgree v (c.negResponse now q)) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v :=
  ⟨_, _, _, _, _, Resolves.negHit c slist q hneg, hbridge⟩

/-- **`timeout` branch as a `HasVerdict` producer** (dropped datagram; retry the rest of the slist). -/
theorem timeout_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache) (d : Datagram)
    (hdrop : Transit (linkReach net ns resolverAddr) addr resolverAddr d none)
    (hmono : now ≤ now')
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _, Resolves.timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec, hbridge⟩

/-- **Prepend a run of timeouts to a `HasVerdict`.** Any list `L` of addresses can be skipped ahead of an
    existing verdict at `rest`, since `Transit.lost` needs no reachability precondition — each address gets its
    own free `Resolves.timeout` hop (at the same clock, `le_refl`). This is the model side of the bizarre/
    timeout leaf: the impl's `dropIfBizarre = removeServer` drops the whole queried NS (all its addresses,
    queried or not), and the model discharges every dropped address as a lost datagram, rebuilding the
    full-SLIST verdict from the surviving-SLIST IH verdict (via `modelSlistOf_removeServer_perm`). -/
theorem hasVerdict_timeout_prepend
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (q : Query) (v : Response) (L : List String) {rest : List String}
    (h : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (L ++ rest) q v := by
  induction L with
  | nil => simpa using h
  | cons a t ih =>
    obtain ⟨tr, sp, tEnd, cout, resp, hres, hrag⟩ := ih
    exact ⟨_, _, _, _, _,
      Resolves.timeout a (t ++ rest) q tr sp tEnd resp c cout default
        (Transit.lost a resolverAddr default) (Nat.le_refl now) hres, hrag⟩

/-- **`skipMissing` branch as a `HasVerdict` producer** (unknown server address; skip it). -/
theorem skipMissing_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache)
    (hfind : serverAt net addr = none)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _, Resolves.skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec, hbridge⟩

/-- **`gluelessNs` branch as a `HasVerdict` producer** (no addressed SLIST candidates; resolve the
    address of a cache-derived NS host at an enclosing cut first, then continue at a SLIST
    containing the learned address — the address-resolution half of the old fused `referNoGlue`,
    whose receipt half is `refer`/`referForget`). -/
theorem gluelessNs_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now1 : Time} {nseen : List Name} {seen : List Name}
    (q : Query) (zone : Name) (nsHost : Name) (nsAddr : String)
    (nsNseen nsSeen : List Name) (nsSlist : List String) (nsTr : List Step)
    (nsPath : List String) (nsEnd : Time) (nsResp : Response)
    (slist2 : List String) (ftr : List Step) (rpath : List String) (tEnd : Time)
    (final : Response) (c c2 cout : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hanc : isAncestor zone q.qname = true)
    (cprov : Cache)
    (hns : nsHost ∈ cprov.nsHostsAt now zone)
    (hmono1 : now ≤ now1)
    (hnsres : Resolves net ns resolverAddr ednsBuf rttOf now1 nsNseen nsSeen c nsSlist
        ⟨nsHost, QType.rr RRType.a, RRClass.in, false⟩ nsTr nsPath nsEnd c2 nsResp)
    (hnsaddr : addressOf nsResp = some nsAddr)
    (hmem : nsAddr ∈ slist2)
    (c2f : Cache) (hc2f : CacheRefines c2f c2)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c2f slist2 q
        ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c [] q v :=
  ⟨_, _, _, _, _,
   Resolves.gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
     slist2 ftr rpath tEnd final c c2 cout hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem
     c2f hc2f hrec,
   hbridge⟩

/-- **`rejectSpoof` branch as a `HasVerdict` producer** (off-path / spoofed reply rejected by
    `accepts`; continue with the rest of the slist — the RFC 5452 anti-spoof guard). -/
theorem rejectSpoof_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache) (id srcPort : Nat) (reply : Datagram)
    (hreject : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = false)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.rejectSpoof addr rest q ftr rpath tEnd final c cout id srcPort reply hreject hrec, hbridge⟩

/-- **`exhausted` branch as a `HasVerdict` producer** (empty slist ⟹ SERVFAIL; no oracle needed). -/
theorem exhausted_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (q : Query)
    (v : Response)
    (hbridge : RespAgree v
      { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c [] q v :=
  ⟨_, _, _, _, _, Resolves.exhausted c q, hbridge⟩

/-- **`chooseServer` branch as a `HasVerdict` producer** (server selection is a free choice ⟹ the verdict
    is invariant under SLIST reordering; RFC 1034 §5.3.3/§7.2). This is the bridge that closes the
    forward-simulation *order* gap: the implementation seeds its SLIST from referral glue in NS-name/array
    order and queries by `transmissionCount` (never reading the abstract `rttOf`), whereas the model
    `refer` rule pins the recursive SLIST to `sortByRtt (glueEntries rttOf …)`. The two are never *equal*
    for an abstract `rttOf`, but are always *permutations* of the same glue-address set — so the driver's
    recursive `HasVerdict` (on the impl's SLIST order) reroutes to the model's `sortByRtt` order through
    this producer, the `Perm` discharged by the glue-set correspondence. Output-preserving: same `cout`/
    verdict, so cache anti-poison is unaffected. -/
theorem chooseServer_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name} (slist slist' : List String) (q : Query)
    (c : Cache) (v : Response)
    (hperm : slist'.Perm slist)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist' q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v := by
  obtain ⟨tr, sp, tEnd, cout, resp, hres, hag⟩ := hrec
  exact ⟨tr, sp, tEnd, cout, resp, Resolves.chooseServer slist slist' q tr sp tEnd resp c cout hperm hres, hag⟩

/-! ### HasVerdict-threading forms of the recursive steps

  The `*_hasVerdict` step lemmas above take the recursive sub-resolution as a *raw* `Resolves` with a
  specific trace/path/end-time/output-cache. But the `ioResumeLoop` induction that will *reach* these
  branches produces its recursive result as a `HasVerdict` — the trace etc. existentially closed (what
  the induction hypothesis yields is "the sub-run has *some* model-justified verdict", not a named
  derivation). These threading wrappers bridge the two: destructure the IH's `HasVerdict`, then apply
  the step lemma to the witnessed derivation. They cover the **output-preserving** recursive branches
  (the outer verdict equals the sub-run's verdict unchanged): `refer` (the bug's branch), `timeout`,
  `skipMissing`, `rejectSpoof`. With these, the eventual `resolveWithIO_total` induction composes
  uniformly — each recursive impl step maps to a threading wrapper, no oracle premise. (The CNAME
  branches transform the verdict by prepending the CNAME RR, so they thread the sub-*response*
  explicitly rather than collapsing to `RespAgree`; `gluelessNs` carries a *second* sub-resolution
  for the NS address whose `nsResp` is constrained by `addressOf` — both handled directly in the
  induction.) -/

/-- HasVerdict-threading form of `refer_hasVerdict` (see section note). -/
theorem refer_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hglue : glueAddresses reply.msg ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String)
    (hsl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm sl)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg)
        sl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact refer_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref _ _ _ _ id srcPort
    c _ hmiss hnmiss hfind hans reply htrans hacc hwire href hbail hdesc frontier hdescF hglue hfresh hmono sl hsl hres v hag

/-- HasVerdict-threading form of `referForget_hasVerdict` — the eviction analogue of `refer_hasVerdict_hv`.
    The recursion runs over a cache `cf` that `CacheRefines` the post-absorb cache (the resolver evicted before
    recursing); `CacheRefines.refl` recovers `refer_hasVerdict_hv`. -/
theorem referForget_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache)
    (hcf : WriteRefines now' cf cf0)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact referForget_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref _ _ _ _ id srcPort
    c _ hmiss hnmiss hfind hans reply htrans hacc hwire href hbail hdesc frontier hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hres v hag

/-- **`refer` threading form accepting the recursion on ANY permutation of the glue addresses** (the SLIST
    connector's consumer form). The model `refer` rule pins the recursive SLIST to `sortByRtt (glueEntries
    rttOf reply.msg)`, but the implementation seeds its SLIST from referral glue in a different (NS-name/array,
    `transmissionCount`) order — never reading `rttOf`. This wrapper lets the driver hand in the recursive
    `HasVerdict` on the implementation's actual model SLIST `gl` (any `Perm` of `glueAddresses reply.msg`):
    `sortByRtt_glueEntries_perm` shows the model's pinned SLIST is itself a `Perm` of `glueAddresses`, so
    `gl.Perm (sortByRtt …)` follows by transitivity and `chooseServer_hasVerdict` reroutes the verdict to the
    pinned order. With the (forthcoming) `modelSlistOf (fromNsWithGlue …) .Perm glueAddresses` correspondence
    discharging `hgl`, this closes the refer step of the forward simulation with no oracle premise. -/
theorem refer_hasVerdict_perm
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hans : ServerAnswers srv now [] true q tr ref)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) ref reply)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
    (frontier : Name)
    (hdescF : reply.msg.descendsBelow frontier = true)
    (hglue : glueAddresses reply.msg ≠ [])
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (gl : List String)
    (hgl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm gl)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
        (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass)
          (referralCut reply.msg)) reply.msg)
        gl q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=

  refer_hasVerdict_hv net ns resolverAddr ednsBuf rttOf addr rest q srv tr ref id srcPort c
    hmiss hnmiss hfind hans reply htrans hacc hwire href hbail hdesc frontier hdescF hglue hfresh hmono v gl hgl hrec

/-- HasVerdict-threading form of `timeout_hasVerdict` (see section note). -/
theorem timeout_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache) (d : Datagram)
    (hdrop : Transit (linkReach net ns resolverAddr) addr resolverAddr d none)
    (hmono : now ≤ now') (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now' nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact timeout_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ d hdrop hmono
    hres v hag

/-- HasVerdict-threading form of `skipMissing_hasVerdict` (see section note). -/
theorem skipMissing_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache)
    (hfind : serverAt net addr = none) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact skipMissing_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ hfind hres v hag

/-- HasVerdict-threading form of `rejectSpoof_hasVerdict` (see section note). -/
theorem rejectSpoof_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache) (id srcPort : Nat) (reply : Datagram)
    (hreject : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = false) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact rejectSpoof_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ id srcPort
    reply hreject hres v hag

/-- **`badResponse` branch as a `HasVerdict` producer** (accepted-but-SERVFAIL reply ⟹ retry the rest;
    the model image of the impl's `dropIfBizarre` retry). Output-preserving like `timeout`/`rejectSpoof`. -/
theorem badResponse_hasVerdict
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (ftr : List Step) (rpath : List String)
    (tEnd : Time) (final : Response) (c cout : Cache) (id srcPort : Nat) (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hbad : reply.msg.rcode = RCode.servFail)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v final) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v :=
  ⟨_, _, _, _, _,
   Resolves.badResponse addr rest q ftr rpath tEnd final c cout id srcPort reply htrans hacc hbad hrec,
   hbridge⟩

/-- HasVerdict-threading form of `badResponse_hasVerdict` (the bizarre-retry branch of the C3 induction;
    the model image of `dropIfBizarre`). -/
theorem badResponse_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (c : Cache) (id srcPort : Nat) (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hbad : reply.msg.rcode = RCode.servFail) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact badResponse_hasVerdict net ns resolverAddr ednsBuf rttOf addr rest q _ _ _ _ c _ id srcPort
    reply htrans hacc hbad hres v hag

/-- HasVerdict-threading form of the `unfollowableReferral` branch (the bailiwick-drop of an
    out-of-bailiwick/not-closer delegation; output-preserving — the verdict comes from the retry on
    `rest`). The C3 classifier for the security-relevant unfollowable-delegation branch. -/
theorem unfollowableReferral_hasVerdict_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr : String) (rest : List String) (q : Query) (srv : Server) (tr : List Step) (ref : Response)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv) (hans : ServerAnswers srv now [] true q tr ref)
    (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (href : reply.msg.isReferral = true)
    (hunfollow : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = false) (v : Response)
    (hrec : HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v) :
    HasVerdict net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v := by
  obtain ⟨_, _, _, _, _, hres, hag⟩ := hrec
  exact ⟨_, _, _, _, _,
    Resolves.unfollowableReferral addr rest q srv tr ref id srcPort _ _ _ _ c _ reply hmiss hnmiss
      hfind hans htrans hacc href hunfollow hres, hag⟩

/-! ### `HasVerdictAt` producers — the cout-exporting forms of the driver's step lemmas

  The soundness driver `ioResumeLoop_sound` co-exports the model derivation's output cache
  (`HasVerdictAt`) so a caller can re-enter the loop on the run's output cache (the `gluelessNs`
  composition). These are the At-forms of exactly the producers the driver's conclusion sites use:
  each is the same proof term as its `HasVerdict` sibling with the output cache named instead of
  existentially closed. TERMINAL producers pin `coutM` to the rule's output cache (`c` for the
  no-write `trustedReply`/`cacheHit`/`negHit` rules); RECURSIVE producers thread the continuation's
  `coutM` through unchanged (`Resolves` referral/cname/timeout hops return the recursion's `cout`). -/

/-- `trustedReply` as a `HasVerdictAt` producer: the rule's output cache is its write slot `cf`
    (the delivered-answer write, RFC 1034); the no-write deliveries instantiate `cf0 := c`
    (`Or.inr rfl`) + `cf := c` (`WriteRefines.refl`), recovering the old `coutM = c` form. -/
theorem trustedReply_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hnr : reply.msg.isReferral = false) (htc : reply.msg.tc = false)
    (v : Response) (hbridge : RespAgree v { reply.msg with aa := false })
    (cf0 : Cache)
    (hcf0 : WriteRefines now cf0 (c.absorb now q.qname { reply.msg with authority := [], additional := [] })
            ∨ cf0 = c)
    (cf : Cache) (hcf : WriteRefines now cf cf0) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v cf :=
  ⟨_, _, _, _,
   Resolves.trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc
     cf0 hcf0 cf hcf, hbridge⟩

/-- `trustedReferral` as a `HasVerdictAt` producer: the hop returns the recursion's output cache. -/
theorem trustedReferral_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query) (frontier : Name)
    (id srcPort : Nat) (c : Cache) (reply : Datagram)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (href : reply.msg.isReferral = true)
    (hbail : reply.msg.inBailiwick q.qname = true)
    (hcut : isAncestor (referralCut reply.msg) q.qname = true)
    (hdesc : reply.msg.descendsBelow frontier = true)
    (hfresh : frontier ∉ seen) (hmono : now ≤ now') (v : Response)
    (sl : List String) (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick frontier (referralCut reply.msg)) reply.msg))
    (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
            ∨ (glueAddresses reply.msg).Subperm sl)
    (cf : Cache) (hcf : WriteRefines now' cf cf0) (coutM : Cache)
    (hrec : HasVerdictAt net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen) cf sl q v coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v coutM := by
  obtain ⟨ftr, rpath, tEnd, final, hres, hbridge⟩ := hrec
  exact ⟨_, _, _, _,
    Resolves.trustedReferral addr origin rest q frontier ftr rpath tEnd final id srcPort c coutM
      hmiss hnmiss reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hres,
    hbridge⟩

/-- `trustedCname` as a `HasVerdictAt` producer: the hop returns the recursion's output cache
    (the explicit `cout` parameter it already takes). -/
theorem trustedCname_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now now' : Time} {nseen : List Name} {seen : List Name}
    (addr origin : String) (rest : List String) (q : Query)
    (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
    (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (reply : Datagram)
    (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
    (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
    (hcn : cnameRR reply.msg.answer = some cn)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen) (hmono : now ≤ now')
    (htc : reply.msg.tc = false)
    (cf0 : Cache)
    (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname { reply.msg with authority := [], additional := [] }))
    (cf : Cache) (hcf : WriteRefines now' cf cf0)
    (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
        cf nsl { q with qname := target } ftr rpath tEnd cout final)
    (v : Response) (hbridge : RespAgree v { final with answer := cn :: final.answer }) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q v cout :=
  ⟨_, _, _, _,
   Resolves.trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
     hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec, hbridge⟩

/-- `cacheCname` (verdict-threading form) as a `HasVerdictAt` producer: the hop returns the
    continuation's output cache. -/
theorem cacheCname_hasVerdictAt_hv
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (slist : List String) (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
    (hqt : q.qtype.covers RRType.cname = false)
    (htgt : cn.rdata = RData.cname target)
    (hfresh : target ∉ q.qname :: nseen)
    (cf : Cache) (hcf : CacheRefines cf c)
    (vsub v : Response) (hrc : v.rcode = vsub.rcode) (hva : v.answer = cn :: vsub.answer)
    (coutM : Cache)
    (hrec : HasVerdictAt net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
        { q with qname := target } vsub coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v coutM := by
  obtain ⟨tr', sp', tEnd', resp', hres, hag⟩ := hrec
  refine ⟨_, _, _, _, Resolves.cacheCname slist q cn target c nsl tr' sp' tEnd' coutM resp'
    hmiss hnmiss hcn hqt htgt hfresh cf hcf hres, ?_⟩
  exact ⟨hrc.trans hag.1, by rw [hva]; exact List.Perm.cons cn hag.2⟩

/-- `cacheHit` as a `HasVerdictAt` producer: the rule writes NO cache, so `coutM = c`. -/
theorem cacheHit_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query) (here : List RR)
    (hhit : c.hit now q = here) (hne : 0 < here.length)
    (v : Response)
    (hbridge : RespAgree v (VeriDNS.Spec.Net.Response.mk false VeriDNS.Spec.Net.RCode.noError here [] [] false false)) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v c :=
  ⟨_, _, _, _, Resolves.cacheHit c slist q here hhit hne, hbridge⟩

/-- `negHit` as a `HasVerdictAt` producer: the rule writes NO cache, so `coutM = c`. -/
theorem negHit_hasVerdictAt
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (slist : List String) (q : Query)
    (hneg : c.negHit now q = true)
    (v : Response) (hbridge : RespAgree v (c.negResponse now q)) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c slist q v c :=
  ⟨_, _, _, _, Resolves.negHit c slist q hneg, hbridge⟩

/-- Prepend a run of timeouts to a `HasVerdictAt` — the At-form of `hasVerdict_timeout_prepend`
    (each dropped address is a free `Resolves.timeout` hop; the output cache is untouched). -/
theorem hasVerdictAt_timeout_prepend
    (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    {now : Time} {nseen : List Name} {seen : List Name}
    (c : Cache) (q : Query) (v : Response) (coutM : Cache) (L : List String) {rest : List String}
    (h : HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c rest q v coutM) :
    HasVerdictAt net ns resolverAddr ednsBuf rttOf now nseen seen c (L ++ rest) q v coutM := by
  induction L with
  | nil => simpa using h
  | cons a t ih =>
    obtain ⟨tr, sp, tEnd, resp, hres, hrag⟩ := ih
    exact ⟨_, _, _, _,
      Resolves.timeout a (t ++ rest) q tr sp tEnd resp c coutM default
        (Transit.lost a resolverAddr default) (Nat.le_refl now) hres, hrag⟩

end NetworkBranches

/-- **Entry establishment for the network induction** — the initial loop state's `StateModels` fields.
    `resolveWithIO` enters `ioResumeLoop` with the state from `Resolver.resolve` (which starts at
    `initFromQuery`); these pin the initial state's cache, clock, and query name — the structural inputs to
    `StateModels` (cache `= αCache initCache` ⟹ `MatchMaxEquiv.refl`; sname `= qu.qname` ⟹ `αName sname =
    some q.qname` via `hqn`; clock `= now`). The pre-pause steps (checkAnswer→sendQueries) don't touch
    cache/sname, so `StateModels_frame` carries the invariant to the paused state the loop receives. -/
theorem initFromQuery_cache (q : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (now : UInt32)
    (initCache : Cache.DnsCache) :
    (Resolver.initFromQuery (S := SList.DnsSList) (C := Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
      (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache).resources.cache = initCache := rfl

theorem initFromQuery_now (q : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (now : UInt32)
    (initCache : Cache.DnsCache) :
    (Resolver.initFromQuery (S := SList.DnsSList) (C := Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
      (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache).now = now := rfl

theorem initFromQuery_sname (q : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (now : UInt32)
    (initCache : Cache.DnsCache) (qu : VeriDNS.Spec.Question) (hqu : q.question[0]? = some qu) :
    (Resolver.initFromQuery (S := SList.DnsSList) (C := Cache.DnsCache) (NS := VeriDNS.Spec.SlistEntry)
      (RR := VeriDNS.Spec.ResourceRecord) q sbelt now initCache).resources.sname = qu.qname := by
  unfold Resolver.initFromQuery
  simp only [hqu]

/-- **End-to-end forward simulation — `resolveWithIO ⊑ Net.Resolves`.**

    For *every* outcome the executable resolver can produce, its abstracted verdict is justified by
    the model: there is a `Net.Resolves` derivation whose response observably agrees with what
    `resolveWithIO` returns (`HasVerdict`). This is the capstone the whole refinement was built for —
    the model's safety theorems (`offpath_cannot_cache`, `no_servfail_direct`,
    `resolves_nxdomain_justified`, `resolves_answer_authoritative`, …) thereby transfer to the running
    resolver as corollaries.

    The outcome hypothesis `houtcome` enumerates the resolver's resolution modes:

    1. **NXDOMAIN cache hit** — fully discharged by `resolveWithIO_negHit_nx_simulates`
       (unconditional; `Net.Resolves.negHit`).
    2. **NODATA cache hit** — discharged by `resolveWithIO_negHit_nodata_simulates` under its two
       model-boundary conditions (`negHitNx = false`, `rc = noError`).
    3. **Positive cache hit** — discharged by `resolveWithIO_cacheHit_simulates` under the served-set
       abstraction equality (`Net.Resolves.cacheHit`).
    4. **Network resolution** (answer / referral / CNAME-chase / retry / failure) — supplied as a
       `HasVerdict` for the network sub-run. This is the forward simulation's *oracle* premise: the
       model constructors for these modes (`answer`, `refer`, `answerCname`, `cacheCname`, `timeout`,
       `skipMissing`, `gluelessNs`, `rejectSpoof`, `exhausted`) carry transport obligations
       (`ServerAnswers`, `Transit`, `OnWire`, `accepts`) that are precisely the conditions under which
       the concrete network behaved consistently with the abstract `net` — established at the FreeIO
       `Prog`/`World` instantiation by `run_resolveWithIO_networkAnswer` and its siblings
       (`Proof/FreeIO.lean`), which discharge the transport concretely rather than axiomatically. A
       forward simulation over an environment is, by construction, parameterized on that environment
       behaving per the model; this disjunct is that parameterization. -/
theorem resolveWithIO_simulates {M : Type → Type} {Sock : Type} [Monad M]
    [VeriDNS.Spec.UdpSocket M Sock ByteArray]
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState)
    (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (query : VeriDNS.Spec.Format) (sbelt : SList.DnsSList) (cache : Cache.DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32)
    (qu : VeriDNS.Spec.Question) (q : VeriDNS.Spec.Net.Query) (t : RRType)
    (hqu : query.question[0]? = some qu)
    (hqn : αName qu.qname = some q.qname) (ht : αType qu.qtype = some t)
    (hqq : q.qtype = VeriDNS.Spec.Net.QType.rr t)
    (houtcome :
      (∃ rc, cache.lookupNxdomain qu.qname qu.qclass now = some rc)
      ∨ (∃ rc, cache.lookupNegative qu.qname qu.qtype qu.qclass now = some rc
            ∧ (αCache cache).negHitNx (αTime now) q = false ∧ rc = VeriDNS.Spec.Rcode.noError)
      ∨ (∃ rrs, cache.lookupNegative qu.qname qu.qtype qu.qclass now = none
            ∧ VeriDNS.Spec.TrustworthinessSpec.answers (C := Cache.DnsCache)
                (RR := VeriDNS.Spec.ResourceRecord) cache qu.qname qu.qtype qu.qclass now = rrs
            ∧ rrs.isEmpty = false
            ∧ αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
                = (αCache cache).hit (αTime now) q
            ∧ 0 < ((αCache cache).hit (αTime now) q).length)
      ∨ (∃ resp cout,
            Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
              = pure (.ok resp, cout)
            ∧ HasVerdict net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
                (αCache cache) slist q (αResp resp))) :
    ∃ resp cout,
      Server.resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        = pure (.ok resp, cout)
      ∧ HasVerdict net ns resolverAddr ednsBuf rttOf (αTime now) nseen seen
          (αCache cache) slist q (αResp resp) := by
  rcases houtcome with ⟨rc, hnx⟩ | ⟨rc, hlk, hnodata, hrc⟩ | ⟨rrs, hnoneg, hans, hrne, hhit, hne⟩ | hnet
  ·
    obtain ⟨resp, hrun, hagree, hres⟩ := resolveWithIO_negHit_nx_simulates (M := M) (Sock := Sock)
      net ns resolverAddr
      ednsBuf rttOf nseen seen slist query sbelt cache now fuel depth budget qu rc q t
      hqu hqn ht hqq hnx
    exact ⟨resp, cache, hrun, _, _, _, _, _, hres, hagree⟩
  ·
    obtain ⟨resp, hrun, hagree, hres⟩ := resolveWithIO_negHit_nodata_simulates (M := M) (Sock := Sock)
      net ns resolverAddr
      ednsBuf rttOf nseen seen slist query sbelt cache now fuel depth budget qu rc q t
      hqu hqn ht hqq hlk hnodata hrc
    exact ⟨resp, cache, hrun, _, _, _, _, _, hres, hagree⟩
  ·
    obtain ⟨resp, hrun, hagree, hres⟩ := resolveWithIO_cacheHit_simulates (M := M) (Sock := Sock)
      net ns resolverAddr
      ednsBuf rttOf nseen seen slist query sbelt cache now fuel depth budget qu q rrs
      hqu hnoneg hans hrne hhit hne
    exact ⟨resp, cache, hrun, _, _, _, _, _, hres, hagree⟩
  ·
    obtain ⟨resp, cout, hrun, hverdict⟩ := hnet
    exact ⟨resp, cout, hrun, hverdict⟩

end VeriDNS.Proof.Refinement

rfc_proves VeriDNS.Proof.Refinement.served_is_per_key_maximal [1035][2589:2591]

rfc_proves VeriDNS.Proof.Refinement.acceptResponse_requires_match [5452][349:353]
