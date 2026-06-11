import VeriDNS.Impl.NameTree
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Cache
import VeriDNS.Impl.Server
import VeriDNS.Spec.ServerAlgorithm
import VeriDNS.Proof.DomainName
import VeriDNS.Proof.ResourceRecord

/-!
# Network consistency and the semantic refinement statement

The semantic theorems are conditional on an honesty oracle: the resolver
can only be as truthful as the servers it queries. The oracle here is the
WEAK form the rest of the verification effort buys:

- it constrains ONLY responses the resolver accepts — RFC 5452 response
  matching (`acceptResponse`), per-exchange connected sockets, and random
  query IDs already keep off-path traffic out, so spoofed datagrams need
  no honesty assumption;
- within an accepted response, every resource record in any section must
  be data the global tree actually holds at its owner node (in-bailiwick
  truthfulness), a name error must be deserved (the queried node really is
  absent), and an answer must be complete for its RRset (RFC 2181 §5.2:
  RRsets are indivisible).

`ResponseConsistent` packages this per response; the refinement statement
(`AnswersFromTree`) says the client-visible response carries `treeResolve`'s
verdict: every answered RR is the tree's data at the node QNAME (after
CNAME chasing) names, and rcode is NXDOMAIN exactly when that node is
missing.
-/

namespace VeriDNS.Proof.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.NameTree
open VeriDNS.Impl.DomainName (nameEqCI)

variable {RR : Type}

/-- TTL-insensitive record-data identity: cached copies tick their TTL
    down; the tree's records are timeless. -/
def sameData (a b : ResourceRecord) : Bool :=
  nameEqCI a.name b.name && a.type == b.type && a.class == b.class &&
    a.rdata == b.rdata

/-- A record is tree data: its owner node exists in the tree and holds it
    (up to TTL). -/
def RRInTree (T : Node ResourceRecord) (rr : ResourceRecord) : Prop :=
  ∃ n, nodeAtName T rr.name = some n ∧
    ∃ rr' ∈ n.resourceSet.toList, sameData rr' rr = true

/-- The tree holds no record of the queried type at the name (vacuously
    true for missing nodes — NXDOMAIN is the stronger condition). -/
def NoRecordOfType (T : Node ResourceRecord) (name : ByteArray)
    (qtype : BitVec 16) : Prop :=
  ∀ n, nodeAtName T name = some n →
    ∀ rr ∈ n.resourceSet.toList, ¬ rr.type == qtype

/-- One wire RR agrees with the tree: it parses, and the parsed record is
    tree data (up to TTL) at its owner node. Unparseable bytes are
    semantically inert and agree vacuously with nothing — they can never
    introduce false data. -/
def RRAgrees (root : Node ResourceRecord) (bytes : ByteArray) : Prop :=
  ∃ rr, RRParse.parseRaw (RR := ResourceRecord) bytes = some rr ∧
    RRInTree root rr

/-- Every RR of a message section agrees with the tree. -/
def SectionAgrees (root : Node ResourceRecord) (rrs : Array ByteArray) : Prop :=
  ∀ b ∈ rrs.toList, RRAgrees root b

/-- An RRset is served whole (RFC 2181 §5.2): if the response answers the
    question, every record of the queried type at the queried node appears
    in the answer section (up to TTL). -/
def AnswerComplete (root : Node ResourceRecord) (resp : Format) : Prop :=
  ∀ qu ∈ resp.question.toList,
    ∀ n, nodeAtName root qu.qname = some n →
      (∃ b ∈ resp.answer.toList, ∃ rr,
        RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
        rr.type == qu.qtype) →
      ∀ rr ∈ n.resourceSet.toList, rr.type == qu.qtype →
        ∃ b ∈ resp.answer.toList, ∃ rr',
          RRParse.parseRaw (RR := ResourceRecord) b = some rr' ∧
          sameData rr' rr = true

/-- The honesty oracle for ONE accepted response. Everything the resolver
    will consume from the response — answers, authority (delegations,
    negative SOAs), additional (glue) — is tree data at its owner node; a
    name error is deserved; an answer is RRset-complete. Responses that
    fail `acceptResponse` (spoofs, mismatched questions) are NOT
    constrained anywhere: RFC 5452 matching plus connected per-exchange
    sockets and unpredictable IDs keep them from ever reaching the
    resolver, so the oracle's domain is exactly the traffic those
    mechanisms admit. -/
structure ResponseConsistent (root : Node ResourceRecord) (resp : Format) : Prop where
  answer : SectionAgrees root resp.answer
  authority : SectionAgrees root resp.authority
  additional : SectionAgrees root resp.additional
  nameErrorDeserved : resp.header.rcode = Rcode.nameError →
    ∀ qu ∈ resp.question.toList, nodeAtName root qu.qname = none
  complete : AnswerComplete root resp

/-- The semantic verdict carried by a client-visible response, relative to
    the chased denotation. Soundness: every answer-section RR is tree data
    at its owner. Rcode fidelity: NXDOMAIN is returned iff the chase ends
    at a missing node. Completeness: a positive verdict's RRset is served
    whole (up to TTL). This is the refinement statement instantiated by
    the resolver theorems. -/
def AnswersFromTree (root : Node ResourceRecord) (qname : ByteArray)
    (qtype : BitVec 16) (fuel : Nat) (resp : Format) : Prop :=
  SectionAgrees root resp.answer ∧
  (match treeResolve root qtype fuel qname #[] with
   | some (_, .nameError) => resp.header.rcode = Rcode.nameError
   | some (_, .answer rrs) =>
     resp.header.rcode = Rcode.noError ∧
     ∀ rr ∈ rrs.toList, ∃ b ∈ resp.answer.toList, ∃ rr',
       RRParse.parseRaw (RR := ResourceRecord) b = some rr' ∧
       sameData rr' rr = true
   | some (_, .nodata) =>
     resp.header.rcode = Rcode.noError ∧
     ¬ ∃ b ∈ resp.answer.toList, ∃ rr,
       RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧
       rr.type == qtype
   | _ => True)

-- ============================================================
-- Tree-level lemmas: the denotation behaves as stated
-- ============================================================

/-- A verdict at an existing node is never NXDOMAIN. -/
theorem lookupAt_ne_nameError [RRParse RR] (n : Node RR) (qtype : BitVec 16) :
    lookupAt n qtype ≠ .nameError := by
  unfold lookupAt
  by_cases hpos :
      (n.resourceSet.filter (fun rr => RRParse.rrType rr == qtype)).size > 0
  · simp [hpos]
  · cases hf : n.resourceSet.find?
        (fun rr => RRParse.rrType rr == cnameType) with
    | none => simp [hpos, hf]
    | some rr =>
      simp [hpos]
      intro hcontra
      split at hcontra <;> simp at hcontra

/-- NXDOMAIN is the verdict exactly for missing nodes. -/
theorem treeLookup_nameError_iff [RRParse RR] (root : Node RR)
    (qname : ByteArray) (qtype : BitVec 16) :
    treeLookup root qname qtype = .nameError ↔ nodeAtName root qname = none := by
  unfold treeLookup
  cases hcase : nodeAtName root qname with
  | none => simp
  | some n =>
    simp only []
    exact ⟨fun h => absurd h (lookupAt_ne_nameError n qtype),
           fun h => by cases h⟩

/-- An `answer` verdict returns precisely the node's records of the
    queried type. -/
theorem treeLookup_answer_sound [RRParse RR] (root : Node RR)
    (qname : ByteArray) (qtype : BitVec 16) (rrs : Array RR)
    (h : treeLookup root qname qtype = .answer rrs) :
    ∃ n, nodeAtName root qname = some n ∧
      rrs = n.resourceSet.filter (fun rr => RRParse.rrType rr == qtype) := by
  unfold treeLookup at h
  cases hcase : nodeAtName root qname with
  | none => rw [hcase] at h; simp at h
  | some n =>
    rw [hcase] at h
    refine ⟨n, rfl, ?_⟩
    unfold lookupAt at h
    by_cases hpos :
        (n.resourceSet.filter (fun rr => RRParse.rrType rr == qtype)).size > 0
    · simp [hpos] at h
      exact h.symm
    · exfalso
      simp [hpos] at h
      split at h
      · split at h <;> simp at h
      · simp at h

/-- A NODATA verdict means the node exists and holds no record of the
    queried type. -/
theorem treeLookup_nodata_sound [RRParse RR] (root : Node RR)
    (qname : ByteArray) (qtype : BitVec 16)
    (h : treeLookup root qname qtype = .nodata) :
    ∃ n, nodeAtName root qname = some n ∧
      ∀ rr ∈ n.resourceSet.toList, ¬ RRParse.rrType rr == qtype := by
  unfold treeLookup at h
  cases hcase : nodeAtName root qname with
  | none => rw [hcase] at h; simp at h
  | some n =>
    rw [hcase] at h
    refine ⟨n, rfl, ?_⟩
    intro rr hmem hty
    have hfmem : rr ∈ n.resourceSet.filter
        (fun rr => RRParse.rrType rr == qtype) :=
      Array.mem_filter.mpr ⟨by simpa using hmem, hty⟩
    have hpos : (n.resourceSet.filter
        (fun rr => RRParse.rrType rr == qtype)).size > 0 := by

      have hne : n.resourceSet.filter
          (fun rr => RRParse.rrType rr == qtype) ≠ #[] := by
        intro hempty
        rw [hempty] at hfmem
        exact Array.not_mem_empty rr hfmem
      exact Array.size_pos_iff.mpr hne
    unfold lookupAt at h
    simp [hpos] at h

-- ============================================================
-- RFC 1034 §4.3.2 obligations, instantiated by the denotation
-- ============================================================

/-- The abstract state σ of the §4.3.2 match-down obligations: one lookup
    against the tree, with the CNAME chain followed so far (3c's "the
    original QNAME ... or a name we have followed due to a CNAME"). -/
structure LookupScenario (RR : Type) where
  root : Node RR
  qname : ByteArray
  qtype : BitVec 16
  chain : Array RR := #[]

namespace LookupScenario

variable [RRParse RR]

/-- §4.3.2 3a guard: "the whole of QNAME is matched" — descent reaches a
    node. -/
def wholeOfQNAMEMatched (s : LookupScenario RR) : Bool :=
  (nodeAtName s.root s.qname).isSome

/-- §4.3.2 3a guard: "the data at the node is a CNAME" — the node's data
    collectively IS a CNAME (a CNAME node carries no other data,
    RFC 1034 §3.6.2). -/
def dataAtNodeCNAME (s : LookupScenario RR) : Bool :=
  match nodeAtName s.root s.qname with
  | some n =>
    n.resourceSet.size > 0 &&
    n.resourceSet.all (fun rr => RRParse.rrType rr == cnameType)
  | none => false

/-- §4.3.2 3a guard: "QTYPE doesn't match CNAME". -/
def qtypeNotMatchCNAME (s : LookupScenario RR) : Bool :=
  s.qtype != cnameType

/-- §4.3.2 3c guard: "a match is impossible (i.e., the corresponding
    label does not exist)". -/
def matchImpossible (s : LookupScenario RR) : Bool :=
  (nodeAtName s.root s.qname).isNone

/-- §4.3.2 3c guard: "the name ... is the original QNAME in the query"
    (no CNAME followed yet). -/
def nameOriginal (s : LookupScenario RR) : Bool :=
  s.chain.isEmpty

end LookupScenario

open LookupScenario

/-- CNAME exclusivity (RFC 1034 §3.6.2): a node with a CNAME carries no
    other data. The §4.3.2 obligations quantify over lookups against
    trees honoring this — the abstract σ is the subtype below, following
    the project convention of instantiating obligations over the subtype
    that passed earlier checks. -/
def CnameExclusive [RRParse RR] (root : Node RR) : Prop :=
  ∀ qname n, nodeAtName root qname = some n →
    (∃ rr ∈ n.resourceSet.toList, RRParse.rrType rr == cnameType) →
    ∀ rr ∈ n.resourceSet.toList, RRParse.rrType rr == cnameType

/-- Lookup scenarios against a §3.6.2-conformant tree. -/
abbrev Scenario (RR : Type) [RRParse RR] : Type :=
  { s : LookupScenario RR // CnameExclusive s.root }

/-- §4.3.2 3a, "Otherwise, copy all RRs which match QTYPE into the answer
    section": with the node found and outside the CNAME case, the verdict
    is exactly the QTYPE-matching RRs (NODATA when there are none —
    copying all of zero RRs). Instantiates the generated
    `obligation_copyRRsMatchQTYPE`. -/
theorem treeLookup_obligation_copyRRsMatchQTYPE (RR : Type) [RRParse RR] :
    ServerLookup.obligation_copyRRsMatchQTYPE (Scenario RR)
      (fun s => wholeOfQNAMEMatched s.val)
      (fun s => dataAtNodeCNAME s.val)
      (fun s => qtypeNotMatchCNAME s.val)
      (fun s =>
        ∀ n, nodeAtName s.val.root s.val.qname = some n →
          treeLookup s.val.root s.val.qname s.val.qtype =
            (let m := n.resourceSet.filter
              (fun rr => RRParse.rrType rr == s.val.qtype)
             if m.size > 0 then .answer m else .nodata)) := by
  intro s _ hncname n hn
  unfold treeLookup
  rw [hn]
  unfold lookupAt
  by_cases hpos : (n.resourceSet.filter
      (fun rr => RRParse.rrType rr == s.val.qtype)).size > 0
  · simp [hpos]
  · simp only [hpos, if_false, gt_iff_lt, Nat.lt_irrefl]
    simp [hpos]
    split
    · next rr hf =>
      split
      · rfl
      · next hq =>
        -- qtype ≠ 5 and a CNAME is present: by exclusivity the data IS a
        -- CNAME, contradicting ¬(CNAME case)
        exfalso
        apply hncname
        have hmem : rr ∈ n.resourceSet := Array.mem_of_find?_eq_some hf
        have hty := Array.find?_some
          (p := fun r => RRParse.rrType r == cnameType) hf
        have hall := s.property s.val.qname n hn
          ⟨rr, by simpa using hmem, hty⟩
        refine ⟨?_, ?_⟩
        · show LookupScenario.dataAtNodeCNAME s.val = true
          simp only [LookupScenario.dataAtNodeCNAME]
          rw [hn]
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            Array.all_eq_true_iff_forall_mem]
          exact ⟨Array.size_pos_iff.mpr
              (fun he => Array.not_mem_empty rr (he ▸ hmem)),
            fun x hx => hall x (by simpa using hx)⟩
        · show LookupScenario.qtypeNotMatchCNAME s.val = true
          simp only [LookupScenario.qtypeNotMatchCNAME]
          simpa using hq
    · rfl

/-- §4.3.2 3a, the CNAME case: "copy the CNAME RR into the answer
    section ..., change QNAME to the canonical name in the CNAME RR".
    With the node found, its data a CNAME, and QTYPE ≠ CNAME, the verdict
    MUST be a redirect carrying one of the node's CNAME RRs, restarting
    at that RR's canonical name. Instantiates BOTH
    `obligation_copyCNAMERRIntoAnswerSection` (the served RR is the
    node's CNAME) and `obligation_changeQNAMEToCanonicalName` (the
    restart name is its RDATA). -/
theorem treeLookup_obligation_cnameCase (RR : Type) [RRParse RR] :
    ServerLookup.obligation_changeQNAMEToCanonicalName (Scenario RR)
      (fun s => wholeOfQNAMEMatched s.val)
      (fun s => dataAtNodeCNAME s.val)
      (fun s => qtypeNotMatchCNAME s.val)
      (fun s =>
        ∀ n, nodeAtName s.val.root s.val.qname = some n →
          ∃ rr, rr ∈ n.resourceSet.toList ∧
            RRParse.rrType rr == cnameType ∧
            treeLookup s.val.root s.val.qname s.val.qtype =
              .redirect rr (RRParse.rrRdata rr)) := by
  intro s _ hcname hq5 n hn
  simp only [LookupScenario.dataAtNodeCNAME] at hcname
  rw [hn] at hcname
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true_iff_forall_mem] at hcname
  obtain ⟨hpos, hall⟩ := hcname
  simp only [LookupScenario.qtypeNotMatchCNAME] at hq5
  have hq5' : ¬ s.val.qtype = cnameType := by simpa using hq5
  -- the QTYPE filter is empty: every RR is a CNAME and qtype ≠ 5
  have hpos' : ¬ (n.resourceSet.filter
      (fun rr => RRParse.rrType rr == s.val.qtype)).size > 0 := by
    intro hgt
    obtain ⟨x, hx⟩ := Array.exists_mem_of_size_pos hgt
    obtain ⟨hxm, hxt⟩ := Array.mem_filter.mp hx
    have h5 := hall x (by simpa using hxm)
    simp only [beq_iff_eq] at hxt h5
    exact hq5' (by rw [← hxt]; exact h5)
  -- find? returns a CNAME: the set is nonempty and all-CNAME
  have hfsome : (n.resourceSet.find?
      (fun rr => RRParse.rrType rr == cnameType)).isSome = true := by
    rw [Array.find?_isSome]
    obtain ⟨x, hx⟩ := Array.exists_mem_of_size_pos hpos
    exact ⟨x, hx, hall x (by simpa using hx)⟩
  obtain ⟨rr, hrr⟩ := Option.isSome_iff_exists.mp hfsome
  refine ⟨rr, by simpa using Array.mem_of_find?_eq_some hrr,
    Array.find?_some (p := fun r => RRParse.rrType r == cnameType) hrr, ?_⟩
  unfold treeLookup
  rw [hn]
  unfold lookupAt
  simp [hpos']
  split
  · next rr' hf' =>
    rw [hrr] at hf'
    cases hf'
    rw [if_neg hq5']
  · next hf' =>
    rw [hrr] at hf'
    cases hf'

/-- The copy-CNAME obligation has the same guards and is discharged by the
    same redirect fact: the served RR IS the node's CNAME. -/
theorem treeLookup_obligation_copyCNAME (RR : Type) [RRParse RR] :
    ServerLookup.obligation_copyCNAMERRIntoAnswerSection (Scenario RR)
      (fun s => wholeOfQNAMEMatched s.val)
      (fun s => dataAtNodeCNAME s.val)
      (fun s => qtypeNotMatchCNAME s.val)
      (fun s =>
        ∀ n, nodeAtName s.val.root s.val.qname = some n →
          ∃ rr, rr ∈ n.resourceSet.toList ∧
            RRParse.rrType rr == cnameType ∧
            treeLookup s.val.root s.val.qname s.val.qtype =
              .redirect rr (RRParse.rrRdata rr)) :=
  treeLookup_obligation_cnameCase RR

/-- §4.3.2 3c: "If the name is original, set an authoritative name error
    in the response": a label match being impossible means the node does
    not exist, and the verdict is NXDOMAIN. Instantiates the generated
    `obligation_setAuthoritativeNameErrorInResponse` (the wildcard
    qualifier drops out — the model tree carries no `*` nodes). -/
theorem treeLookup_obligation_nameError (RR : Type) [RRParse RR] :
    ServerLookup.obligation_setAuthoritativeNameErrorInResponse (Scenario RR)
      (fun s => matchImpossible s.val)
      (fun s => nameOriginal s.val)
      (fun s => treeLookup s.val.root s.val.qname s.val.qtype = .nameError) := by
  intro s himp _
  simp only [LookupScenario.matchImpossible,
    Option.isNone_iff_eq_none] at himp
  exact (treeLookup_nameError_iff ..).mpr himp

-- ============================================================
-- Case-insensitivity congruence: CI-equal names reach the same node
-- ============================================================

section CICongruence

open VeriDNS.Impl.DomainName

/-- `foldCaseByte` in `toNat` form, for omega-style reasoning. -/
theorem foldCaseByte_toNat (b : UInt8) :
    (foldCaseByte b).toNat =
      if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b.toNat + 32 else b.toNat := by
  unfold foldCaseByte
  by_cases h : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · rw [if_pos (by simp [UInt8.le_iff_toNat_le]; omega), if_pos h,
      UInt8.toNat_add]
    have h32 : (32 : UInt8).toNat = 32 := rfl
    rw [h32]
    omega
  · rw [if_neg (by simp [UInt8.le_iff_toNat_le]; omega), if_neg h]

theorem foldCaseByte_idem (b : UInt8) :
    foldCaseByte (foldCaseByte b) = foldCaseByte b := by
  apply UInt8.toNat_inj.mp
  rw [foldCaseByte_toNat (foldCaseByte b), foldCaseByte_toNat b]
  by_cases h : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · simp only [if_pos h]
    rw [if_neg (by omega)]
  · simp only [if_neg h]

theorem foldNameCase_size (w : ByteArray) :
    (foldNameCase w).size = w.size := by
  unfold foldNameCase
  show (w.data.map foldCaseByte).size = w.data.size
  exact Array.size_map

theorem foldNameCase_data_getElem (w : ByteArray) (i : Nat)
    (h : i < w.data.size) (h' : i < (foldNameCase w).data.size) :
    (foldNameCase w).data[i] = foldCaseByte w.data[i] := by
  show (w.data.map foldCaseByte)[i]'h' = foldCaseByte w.data[i]
  exact Array.getElem_map foldCaseByte h'

theorem foldNameCase_idem (w : ByteArray) :
    foldNameCase (foldNameCase w) = foldNameCase w := by
  apply ByteArray.ext
  show (w.data.map foldCaseByte).map foldCaseByte = w.data.map foldCaseByte
  rw [Array.map_map]
  congr 1
  funext b
  show foldCaseByte (foldCaseByte b) = foldCaseByte b
  exact foldCaseByte_idem b

theorem foldNameCase_extract (w : ByteArray) (a b : Nat) :
    (foldNameCase w).extract a b = foldNameCase (w.extract a b) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  show (w.data.map foldCaseByte).extract a b
    = (w.extract a b).data.map foldCaseByte
  rw [ByteArray.data_extract]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

/-- Case folding commutes with a successful label decomposition: the
    parse takes the same branches at every position (length bytes below
    64 fold to themselves), and each produced label folds. -/
theorem wireFormatToLabelsGo_fold_ok (w : ByteArray) (pos : Nat)
    (ls : List ByteArray)
    (hw : wireFormatToLabelsGo w pos = .ok ls) :
    wireFormatToLabelsGo (foldNameCase w) pos = .ok (ls.map foldNameCase) := by
  unfold wireFormatToLabelsGo at hw ⊢
  by_cases hpos : pos < w.size
  · have hpos' : pos < (foldNameCase w).size := by
      rw [foldNameCase_size]; exact hpos
    have hpd : pos < w.data.size := hpos
    have hpd' : pos < (foldNameCase w).data.size := hpos'
    rw [dif_pos hpd] at hw
    rw [dif_pos hpd']
    dsimp only [] at hw ⊢
    have hb : (foldNameCase w).data[pos]'hpd' = foldCaseByte (w.data[pos]'hpd) :=
      foldNameCase_data_getElem w pos hpd hpd'
    have hrel := foldCaseByte_toNat (w.data[pos]'hpd)
    split at hw
    · next hzero =>
      cases hw
      rw [dif_pos (show ((foldNameCase w).data[pos]'hpd').toNat = 0 by
        rw [hb, hrel, if_neg (by omega)]; exact hzero)]
      rfl
    · next hzero =>
      split at hw
      · exact absurd hw (by simp)
      · next hbig =>
        rw [dif_neg (show ¬ ((foldNameCase w).data[pos]'hpd').toNat = 0 by
          rw [hb, hrel]; split <;> omega)]
        rw [dif_neg (show ¬ ((foldNameCase w).data[pos]'hpd').toNat > 63 by
          rw [hb, hrel]; split <;> omega)]
        have hleneq : ((foldNameCase w).data[pos]'hpd').toNat =
            (w.data[pos]'hpd).toNat := by
          rw [hb, hrel, if_neg (by omega)]
        rw [hleneq]
        split at hw
        · next hroom =>
          rw [dif_pos (show pos + 1 + (w.data[pos]'hpd).toNat ≤
              (foldNameCase w).size by rw [foldNameCase_size]; exact hroom)]
          split at hw
          · next rest hrec =>
            cases hw
            rw [wireFormatToLabelsGo_fold_ok w _ rest hrec]
            rw [foldNameCase_extract]
            rfl
          · next => exact absurd hw (by simp)
        · next => exact absurd hw (by simp)
  · rw [dif_neg (show ¬ pos < w.data.size from hpos)] at hw
    cases hw
    rw [dif_neg (show ¬ pos < (foldNameCase w).data.size by
      have h1 : (foldNameCase w).data.size = w.size := foldNameCase_size w
      omega)]
    rfl
termination_by w.size - pos
decreasing_by omega

/-- Case folding preserves parse failure: a wire name whose decomposition
    errors still errors after folding (the offending branch is taken at
    the same position). -/
theorem wireFormatToLabelsGo_fold_error (w : ByteArray) (pos : Nat)
    (e : String) (hw : wireFormatToLabelsGo w pos = .error e) :
    ∃ e', wireFormatToLabelsGo (foldNameCase w) pos = .error e' := by
  unfold wireFormatToLabelsGo at hw ⊢
  by_cases hpos : pos < w.size
  · have hpos' : pos < (foldNameCase w).size := by
      rw [foldNameCase_size]; exact hpos
    have hpd : pos < w.data.size := hpos
    have hpd' : pos < (foldNameCase w).data.size := hpos'
    rw [dif_pos hpd] at hw
    rw [dif_pos hpd']
    dsimp only [] at hw ⊢
    have hb : (foldNameCase w).data[pos]'hpd' = foldCaseByte (w.data[pos]'hpd) :=
      foldNameCase_data_getElem w pos hpd hpd'
    have hrel := foldCaseByte_toNat (w.data[pos]'hpd)
    split at hw
    · exact absurd hw (by simp)
    · next hzero =>
      rw [dif_neg (show ¬ ((foldNameCase w).data[pos]'hpd').toNat = 0 by
        rw [hb, hrel]; split <;> omega)]
      split at hw
      · next hbig =>
        rw [dif_pos (show ((foldNameCase w).data[pos]'hpd').toNat > 63 by
          rw [hb, hrel]; split <;> omega)]
        exact ⟨_, rfl⟩
      · next hbig =>
        rw [dif_neg (show ¬ ((foldNameCase w).data[pos]'hpd').toNat > 63 by
          rw [hb, hrel]; split <;> omega)]
        have hleneq : ((foldNameCase w).data[pos]'hpd').toNat =
            (w.data[pos]'hpd).toNat := by
          rw [hb, hrel, if_neg (by omega)]
        rw [hleneq]
        split at hw
        · next hroom =>
          rw [dif_pos (show pos + 1 + (w.data[pos]'hpd).toNat ≤
              (foldNameCase w).size by rw [foldNameCase_size]; exact hroom)]
          split at hw
          · next => exact absurd hw (by simp)
          · next e' hrec =>
            obtain ⟨e'', h⟩ := wireFormatToLabelsGo_fold_error w _ e' hrec
            rw [h]
            exact ⟨e'', rfl⟩
        · next hroom =>
          rw [dif_neg (show ¬ pos + 1 + (w.data[pos]'hpd).toNat ≤
              (foldNameCase w).size by rw [foldNameCase_size]; exact hroom)]
          exact ⟨_, rfl⟩
  · rw [dif_neg (show ¬ pos < w.data.size from hpos)] at hw
    exact absurd hw (by simp)
termination_by w.size - pos
decreasing_by omega

theorem wireFormatToLabels_fold_ok (w : ByteArray) (ls : Array ByteArray)
    (hw : wireFormatToLabels w = .ok ls) :
    wireFormatToLabels (foldNameCase w) = .ok (ls.map foldNameCase) := by
  unfold wireFormatToLabels at hw ⊢
  split at hw
  · next ls0 hgo =>
    cases hw
    rw [wireFormatToLabelsGo_fold_ok w 0 ls0 hgo]
    simp [List.map_toArray]
  · exact absurd hw (by simp)

theorem wireFormatToLabels_fold_error (w : ByteArray) (e : String)
    (hw : wireFormatToLabels w = .error e) :
    ∃ e', wireFormatToLabels (foldNameCase w) = .error e' := by
  unfold wireFormatToLabels at hw ⊢
  split at hw
  · exact absurd hw (by simp)
  · next e0 hgo =>
    obtain ⟨e', h⟩ := wireFormatToLabelsGo_fold_error w 0 e0 hgo
    rw [h]
    exact ⟨e', rfl⟩

theorem labelEqCI_fold_right (a l : ByteArray) :
    labelEqCI a (foldNameCase l) = labelEqCI a l := by
  unfold labelEqCI
  rw [foldNameCase_idem]

theorem findChild_fold {RR : Type} (n : Node RR) (l : ByteArray) :
    findChild n (foldNameCase l) = findChild n l := by
  unfold findChild
  congr 1
  funext c
  exact labelEqCI_fold_right c.label l

theorem nodeAt_fold {RR : Type} (root : Node RR) (ls : List ByteArray) :
    nodeAt root (ls.map foldNameCase) = nodeAt root ls := by
  induction ls generalizing root with
  | nil => rfl
  | cons l rest ih =>
    show nodeAt root (foldNameCase l :: rest.map foldNameCase) = _
    unfold nodeAt
    rw [findChild_fold]
    cases findChild root l with
    | some c => exact ih c
    | none => rfl

/-- Folding a queried name's case does not change the node it reaches. -/
theorem nodeAtName_fold {RR : Type} (root : Node RR) (q : ByteArray) :
    nodeAtName root (foldNameCase q) = nodeAtName root q := by
  unfold nodeAtName
  cases hq : wireFormatToLabels q with
  | ok ls =>
    rw [wireFormatToLabels_fold_ok q ls hq]
    show nodeAt root (ls.map foldNameCase).toList.reverse
      = nodeAt root ls.toList.reverse
    have : (ls.map foldNameCase).toList.reverse
        = (ls.toList.reverse).map foldNameCase := by
      simp [List.map_reverse]
    rw [this, nodeAt_fold]
  | error e =>
    obtain ⟨e', h⟩ := wireFormatToLabels_fold_error q e hq
    rw [h]

/-- THE case-insensitivity congruence (RFC 1035 §3.1 meets the §3.1 tree):
    CI-equal names name the same node — `EXAMPLE.COM` and `example.com`
    reach the same point of the tree, exist together, and are absent
    together. -/
theorem nodeAtName_congrCI {RR : Type} (root : Node RR) {a b : ByteArray}
    (h : nameEqCI a b = true) :
    nodeAtName root a = nodeAtName root b := by
  have hfold : foldNameCase a = foldNameCase b := by
    have h'' : ByteArray.beq (foldNameCase a) (foldNameCase b) = true := h
    unfold ByteArray.beq at h''
    exact ByteArray.ext (eq_of_beq h'')
  rw [← nodeAtName_fold root a, ← nodeAtName_fold root b, hfold]

end CICongruence

-- ============================================================
-- Wire fidelity: parsed records re-encode to themselves
-- ============================================================

section WireFidelity

open VeriDNS.Impl
open VeriDNS.Impl.DomainName (decodeNameAux decodeName labelsToWireFormat)

/-- One decoded label is well-sized: nonempty (the byte was not the
    terminator) and ≤ 63 (checked). -/
private theorem validLabels_cons (l : ByteArray) (rest : Array ByteArray)
    (hl : 0 < l.size ∧ l.size ≤ 63)
    (hr : Proof.DomainName.ValidLabels rest) :
    Proof.DomainName.ValidLabels (#[l] ++ rest) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simpa using hl
  · have hi' : i - 1 < rest.size := by
      simp only [Array.size_append, Array.size_singleton] at hi  -- hmm name
      omega
    have hres := hr (i - 1) hi'
    rw [Array.getElem_append_right (by simp; omega)]
    simpa using hres

/-- `decodeNameAux` only ever returns valid labels (RFC 1035 §2.3.1:
    1–63 octets each). -/
theorem decodeNameAux_valid (buf : ByteArray) :
    ∀ (fuel pos : Nat) (fep : Option Nat) (labels : Array ByteArray)
      (endPos : Nat),
    decodeNameAux buf pos fuel fep = .ok (labels, endPos) →
    Proof.DomainName.ValidLabels labels := by
  intro fuel
  induction fuel with
  | zero => intro pos fep labels endPos h; cases h
  | succ fuel ih =>
    intro pos fep labels endPos h
    unfold decodeNameAux at h
    split at h
    · next hlt =>
      dsimp only [] at h
      split at h
      · -- terminator: empty label list
        cases h
        intro i hi
        simp at hi
      · next hb0 =>
        split at h
        · -- compression pointer: labels come from the target
          split at h
          · split at h
            · next labs ep hrec =>
              cases h
              exact ih _ _ _ _ hrec
            · cases h
          · cases h
        · -- plain label
          split at h
          · cases h
          · next hlen63 =>
            split at h
            · next hroom =>
              split at h
              · next rest ep hrec =>
                cases h
                refine validLabels_cons _ _ ⟨?_, ?_⟩ (ih _ _ _ _ hrec)
                · have hsz : (buf.extract (pos + 1)
                      (pos + 1 + (buf.data[pos]'hlt).toNat)).size
                      = (buf.data[pos]'hlt).toNat := by
                    rw [ByteArray.size_extract]
                    have : pos + 1 + (buf.data[pos]'hlt).toNat ≤ buf.size := hroom
                    omega
                  rw [hsz]
                  have hne : (buf.data[pos]'hlt) ≠ 0 := by simpa using hb0
                  have hnz : (buf.data[pos]'hlt).toNat ≠ 0 := fun hz =>
                    hne (UInt8.toNat_inj.mp (by simpa using hz))
                  omega
                · have hsz : (buf.extract (pos + 1)
                      (pos + 1 + (buf.data[pos]'hlt).toNat)).size
                      = (buf.data[pos]'hlt).toNat := by
                    rw [ByteArray.size_extract]
                    have : pos + 1 + (buf.data[pos]'hlt).toNat ≤ buf.size := hroom
                    omega
                  rw [hsz]
                  omega
              · cases h
            · cases h
    · cases h

/-- `decodeName` only ever returns valid labels. -/
theorem decodeName_valid (buf : ByteArray) (pos : Nat)
    (labels : Array ByteArray) (endPos : Nat)
    (h : DnsParser.run decodeName buf pos = .ok (labels, endPos)) :
    Proof.DomainName.ValidLabels labels := by
  unfold decodeName at h
  simp only [Proof.Primitives.run_bind, Proof.Primitives.run_getBuffer,
    Proof.Primitives.run_getPos] at h
  split at h
  · next ls ep haux =>
    simp only [Proof.Primitives.run_bind, Proof.Primitives.run_setPos,
      Proof.Primitives.run_pure] at h
    cases h
    exact decodeNameAux_valid buf _ _ _ _ _ haux
  · next e haux =>
    exact absurd h (by simp [DnsParser.fail])

/-- Shape of a decoded resource record: its name is the wire encoding of
    a valid label array, and its RDLENGTH matches its RDATA. These are
    exactly the side conditions of the roundtrip theorem. -/
theorem decode_shape (bytes : ByteArray) (rr : VeriDNS.Spec.ResourceRecord)
    (n : Nat)
    (h : DnsParser.run ResourceRecord.decode bytes = .ok (rr, n)) :
    (∃ labels, Proof.DomainName.ValidLabels labels ∧
      rr.name = labelsToWireFormat labels) ∧
    rr.rdlength.toNat = rr.rdata.size := by
  unfold ResourceRecord.decode at h
  simp only [Proof.Primitives.run_bind] at h
  split at h
  · next labels pos1 hname =>
    simp only [Proof.Primitives.run_readBV16, Proof.Primitives.run_readBV32] at h
    split at h
    · split at h
      · split at h
        · split at h
          · simp only [Proof.Primitives.run_bind,
              Proof.Primitives.run_readBytes] at h
            split at h
            · next rdat pos6 hrd =>
              simp only [Proof.Primitives.run_pure] at h
              cases h
              refine ⟨⟨labels, decodeName_valid bytes 0 labels pos1 hname, rfl⟩, ?_⟩
              dsimp only []
              split at hrd
              · next hroom =>
                cases hrd
                rw [ByteArray.size_extract]
                omega
              · cases hrd
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A well-formed record: its name is the wire encoding of valid labels
    and its RDLENGTH matches its RDATA — exactly the conditions under
    which decode ∘ encode is the identity. Decoded records are well-formed
    (`wfRR_of_parseRaw`), and well-formedness survives the TTL rewrites
    cache lookups perform. -/
def WfRR (rr : VeriDNS.Spec.ResourceRecord) : Prop :=
  (∃ labels, Proof.DomainName.ValidLabels labels ∧
    rr.name = labelsToWireFormat labels) ∧
  rr.rdlength.toNat = rr.rdata.size

theorem wfRR_of_parseRaw {bytes : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (h : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr) :
    WfRR rr := by
  simp only [RRParse.parseRaw, Cache.instRRParseResourceRecord] at h
  split at h
  · next rr' n hrun =>
    cases h
    exact decode_shape bytes rr n hrun
  · cases h

theorem wfRR_set_ttl {rr : VeriDNS.Spec.ResourceRecord} (h : WfRR rr)
    (ttl : BitVec 32) : WfRR { rr with ttl := ttl } := h

/-- The canonical fixed point: a well-formed record re-encodes to bytes
    that parse back to the SAME record. This is what lets a cached record
    be served byte-for-byte honestly. -/
theorem parseRaw_rrBytes_of_wf {rr : VeriDNS.Spec.ResourceRecord}
    (h : WfRR rr) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (RRParse.rrBytes rr) = some rr := by
  obtain ⟨⟨labels, hv, hqn⟩, hrl⟩ := h
  simp only [RRParse.parseRaw, RRParse.rrBytes,
    Cache.instRRParseResourceRecord]
  rw [Proof.ResourceRecord.decode_encode rr labels hv hqn.symm hrl]

end WireFidelity

-- ============================================================
-- Cache soundness: the cache is a sound partial view of the tree
-- ============================================================

open VeriDNS.Impl.Cache

/-- `RRInTree` only looks at name/type/class/rdata, so the TTL rewrite a
    cache lookup performs preserves it. -/
theorem rrInTree_set_ttl {T : Node ResourceRecord} {rr : ResourceRecord}
    (h : RRInTree T rr) (ttl : BitVec 32) :
    RRInTree T { rr with ttl := ttl } := by
  obtain ⟨n, hn, rr', hmem, hdata⟩ := h
  exact ⟨n, hn, rr', hmem, by simpa [sameData] using hdata⟩

/-- `sameData` is reflexive (`nameEqCI` identifies a name with itself via
    the §3.1 fold-invariance conformance). -/
theorem sameData_refl (rr : ResourceRecord) : sameData rr rr = true := by
  unfold sameData
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨VeriDNS.Proof.DomainName.nameEqCI_conforms rr.name rr.name rfl,
    by simp⟩, by simp⟩, ?_⟩
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp

/-- The bridge from the response oracle to the cache invariant: a wire RR
    that agrees with the tree parses to a record that IS tree data. -/
theorem rrInTree_of_rrAgrees {T : Node ResourceRecord} {bytes : ByteArray}
    {rr : ResourceRecord} (h : RRAgrees T bytes)
    (hp : RRParse.parseRaw (RR := ResourceRecord) bytes = some rr) :
    RRInTree T rr := by
  obtain ⟨rr', hparse, hin⟩ := h
  rw [hp] at hparse
  cases hparse
  exact hin

/-- The cache agrees with the tree: every positive entry's record is tree
    data at its owner node; an NXDOMAIN entry's node is really absent;
    every negative entry's ⟨name, qtype⟩ really has no data. Expiry and
    credibility are irrelevant to agreement — stale or untrustworthy
    entries are invisible to the relevant lookups, but they still never
    DISAGREE with the tree. This is the semantic non-poisoning invariant:
    under it, nothing the cache can ever serve is outside the tree. -/
structure CacheAgrees (T : Node ResourceRecord) (c : DnsCache) : Prop where
  positives : ∀ e ∈ c.records, RRInTree T e.rr ∧ WfRR e.rr
  nxdomainDeserved : ∀ ne ∈ c.negatives,
    ne.rcode = Rcode.nameError → nodeAtName T ne.name = none
  negativesDeserved : ∀ ne ∈ c.negatives,
    NoRecordOfType T ne.name ne.qtype

theorem cacheAgrees_empty (T : Node ResourceRecord) :
    CacheAgrees T DnsCache.empty := by
  refine ⟨?_, ?_, ?_⟩ <;> intro e he <;>
    simp [DnsCache.empty] at he

/-- `store` preserves agreement when the stored record is tree data:
    surviving entries are a filter (and FIFO-eviction) subset, and the
    pushed entry carries the new record. -/
theorem cacheAgrees_store {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {rr : ResourceRecord}
    (hrr : RRInTree T rr) (hwf : WfRR rr)
    (now : UInt32) (cred : Trustworthiness) :
    CacheAgrees T (c.store rr now cred) := by
  refine ⟨?_, h.nxdomainDeserved, h.negativesDeserved⟩
  intro e he
  simp only [DnsCache.store] at he
  rcases Array.mem_push.mp he with hmem | heq
  · exact h.positives e (Array.mem_filter.mp (mem_of_mem_boundFifo hmem)).1
  · subst heq
    exact ⟨hrr, hwf⟩

/-- `storeChecked` preserves agreement under the same hypothesis (it is a
    no-op or a `store`). -/
theorem cacheAgrees_storeChecked {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {rr : ResourceRecord}
    (hrr : RRInTree T rr) (hwf : WfRR rr)
    (cred : Trustworthiness) (now : UInt32) :
    CacheAgrees T (c.storeChecked rr cred now) := by
  simp only [DnsCache.storeChecked]
  split
  · exact h
  · exact cacheAgrees_store h hrr hwf now cred

/-- A missing node trivially has no record of any type. -/
theorem noRecordOfType_of_absent {T : Node ResourceRecord} {name : ByteArray}
    (h : nodeAtName T name = none) (qtype : BitVec 16) :
    NoRecordOfType T name qtype := by
  intro n hn
  rw [h] at hn
  cases hn

/-- `storeNegative` preserves agreement when the negative verdict is
    deserved by the tree. -/
theorem cacheAgrees_storeNegative {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {name : ByteArray} {qtype qclass : BitVec 16}
    {rcode : Rcode} {soa : Option ResourceRecord} {expiry : UInt32}
    (hnx : rcode = Rcode.nameError → nodeAtName T name = none)
    (hnod : NoRecordOfType T name qtype) :
    CacheAgrees T (c.storeNegative name qtype qclass rcode soa expiry) := by
  refine ⟨h.positives, ?_, ?_⟩ <;> intro ne hne
  · simp only [DnsCache.storeNegative] at hne
    rcases Array.mem_push.mp hne with hmem | heq
    · exact h.nxdomainDeserved ne
        (Array.mem_filter.mp (mem_of_mem_boundFifo hmem)).1
    · subst heq
      exact hnx
  · simp only [DnsCache.storeNegative] at hne
    rcases Array.mem_push.mp hne with hmem | heq
    · exact h.negativesDeserved ne
        (Array.mem_filter.mp (mem_of_mem_boundFifo hmem)).1
    · subst heq
      exact hnod

/-- `sweep` preserves agreement (it only removes entries). -/
theorem cacheAgrees_sweep {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (now : UInt32) :
    CacheAgrees T (c.sweep now) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro e he
  · exact h.positives e (Array.mem_filter.mp he).1
  · exact h.nxdomainDeserved e (Array.mem_filter.mp he).1
  · exact h.negativesDeserved e (Array.mem_filter.mp he).1

/-- Everything `lookup` returns is tree data. With `CacheAgrees` as the
    standing invariant, the resolver can only ever serve the tree's
    records — the semantic strengthening of poisoning resistance. -/
theorem lookup_agrees {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) :
    ∀ rr ∈ c.lookup name qtype qclass now, RRInTree T rr ∧ WfRR rr := by
  intro rr hrr
  obtain ⟨e, hmem, heq⟩ := Array.mem_filterMap.mp hrr
  split at heq
  · cases heq
    exact ⟨rrInTree_set_ttl (h.positives e hmem).1 _,
      wfRR_set_ttl (h.positives e hmem).2 _⟩
  · cases heq

/-- Everything `lookupAnswerable` returns is tree data (it returns a
    subset of `lookup`'s view). -/
theorem lookupAnswerable_agrees {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) :
    ∀ rr ∈ c.lookupAnswerable name qtype qclass now,
      RRInTree T rr ∧ WfRR rr := by
  intro rr hrr
  obtain ⟨e, hmem, heq⟩ := Array.mem_filterMap.mp hrr
  split at heq
  · cases heq
    exact ⟨rrInTree_set_ttl (h.positives e hmem).1 _,
      wfRR_set_ttl (h.positives e hmem).2 _⟩
  · cases heq


-- ============================================================
-- Resolver bridge: caching consumes the oracle, serving emits it
-- ============================================================

section ResolverBridge

open VeriDNS.Impl.Resolver

/-- Caching a T-consistent message section preserves the invariant:
    `cacheRRs` parses each wire RR and runs the credibility-checked store,
    and every parse of an agreeing byte string is tree data (and decoded,
    hence well-formed). -/
private theorem cacheAgrees_foldStore {T : Node ResourceRecord}
    (f : DnsCache → ByteArray → DnsCache)
    (hstep : ∀ c b, CacheAgrees T c → RRAgrees T b → CacheAgrees T (f c b))
    (hskip : ∀ c b, CacheAgrees T c →
      RRParse.parseRaw (RR := ResourceRecord) b = none → CacheAgrees T (f c b)) :
    ∀ (l : List ByteArray) (c : DnsCache), CacheAgrees T c →
    (∀ b ∈ l, RRAgrees T b ∨
      RRParse.parseRaw (RR := ResourceRecord) b = none) →
    CacheAgrees T (l.foldl f c)
  | [], _, h, _ => h
  | b :: rest, c, h, hsec => by
    rw [List.foldl_cons]
    refine cacheAgrees_foldStore f hstep hskip rest _ ?_
      (fun b' hb' => hsec b' (List.mem_cons_of_mem b hb'))
    rcases hsec b List.mem_cons_self with hb | hb
    · exact hstep c b h hb
    · exact hskip c b h hb

theorem cacheAgrees_cacheRRs {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {raws : Array ByteArray}
    (hsec : SectionAgrees T raws) (cred : Trustworthiness) (now : UInt32) :
    CacheAgrees T (cacheRRs (C := DnsCache) (RR := ResourceRecord)
      c raws cred now) := by
  unfold cacheRRs
  rw [← Array.foldl_toList]
  refine cacheAgrees_foldStore _ ?_ ?_ raws.toList c h
    (fun b hb => Or.inl (hsec b hb))
  · intro c' b hc hb
    obtain ⟨rr, hp, hin⟩ := hb
    have hwf : WfRR rr := wfRR_of_parseRaw hp
    simp only [hp]
    exact cacheAgrees_storeChecked hc hin hwf cred now
  · intro c' b hc hp
    simp only [hp]
    exact hc

/-- A response synthesized from tree-data records has a T-consistent
    answer section: each served byte string is the canonical re-encoding
    of a well-formed record, which parses back to that record. -/
theorem cacheResponse_agrees {T : Node ResourceRecord} {rrs : Array ResourceRecord}
    (hrrs : ∀ rr ∈ rrs, RRInTree T rr ∧ WfRR rr) (q : Format) :
    SectionAgrees T (cacheResponse (RR := ResourceRecord) q rrs).answer := by
  intro b hb
  simp only [cacheResponse] at hb
  obtain ⟨rr, hmem, hbytes⟩ := Array.mem_map.mp (by simpa using hb)
  obtain ⟨hin, hwf⟩ := hrrs rr hmem
  exact ⟨rr, hbytes ▸ parseRaw_rrBytes_of_wf hwf, hin⟩

/-- A negative response carries no answer-section data at all, so its
    answer section agrees vacuously. -/
theorem negativeResponse_answer_agrees {T : Node ResourceRecord}
    (q : Format) (rc : Rcode) (soaAuth : Array ResourceRecord) :
    SectionAgrees T (negativeResponse (RR := ResourceRecord) q rc soaAuth).answer := by
  intro b hb
  simp [negativeResponse] at hb

/-- The CLIENT-FACING soundness of the step-1 cache hit: whatever
    `cacheResponse` serves from `lookupAnswerable` results under the
    `CacheAgrees` invariant is tree data. The cache CANNOT serve anything
    the tree does not hold — semantic non-poisoning at the serving edge. -/
theorem cacheHit_serves_tree {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (q : Format) (name : ByteArray)
    (qtype qclass : BitVec 16) (now : UInt32) :
    SectionAgrees T (cacheResponse (RR := ResourceRecord) q
      (c.lookupAnswerable name qtype qclass now)).answer :=
  cacheResponse_agrees
    (fun rr hmem => lookupAnswerable_agrees h name qtype qclass now rr hmem) q

end ResolverBridge

-- ============================================================
-- Step and loop soundness: the resolver only ever answers tree data
-- ============================================================

section StepSoundness

open VeriDNS.Impl.Resolver

variable {S NS : Type} [SlistSpec S NS] [SlistFromNameSpec S NS] [Inhabited S]

/-- The resolver-state invariant: the cache is a sound view of the tree
    and every accumulated CNAME-chain element agrees with it. -/
structure StateAgrees (T : Node ResourceRecord)
    (s : State S DnsCache NS ResourceRecord) : Prop where
  cache : CacheAgrees T s.resources.cache
  chain : ∀ b ∈ s.cnameChain.toList, RRAgrees T b

/-- `cacheUnlessTruncated` preserves agreement for T-consistent sections
    (a truncated response is not cached at all, §7.4). -/
theorem cacheAgrees_cacheUnlessTruncated {T : Node ResourceRecord}
    {c : DnsCache} (h : CacheAgrees T c) (resp : Format)
    {raws : Array ByteArray} (hsec : SectionAgrees T raws)
    (cred : Trustworthiness) (now : UInt32) :
    CacheAgrees T (cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
      c resp raws cred now) := by
  unfold cacheUnlessTruncated
  split
  · exact h
  · exact cacheAgrees_cacheRRs h hsec cred now

/-- `finalizeAnswer` serves the accumulated chain plus the response's
    answer section; both agree, so the finalized answer agrees. The
    question restoration does not touch the answer section. -/
theorem finalizeAnswer_answer_agrees {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} {resp : Format}
    (hchain : ∀ b ∈ s.cnameChain.toList, RRAgrees T b)
    (hans : SectionAgrees T resp.answer) :
    SectionAgrees T (finalizeAnswer s resp).answer := by
  intro b hb
  unfold finalizeAnswer prependChain at hb
  rcases hq : s.lastQuery with _ | q <;> rw [hq] at hb <;>
    dsimp only [] at hb <;>
    split at hb
  · exact hans b hb
  · rcases Array.mem_append.mp (Array.mem_def.mpr hb) with hl | hr
    · exact hchain b (Array.mem_def.mp hl)
    · exact hans b (Array.mem_def.mp hr)
  · exact hans b hb
  · rcases Array.mem_append.mp (Array.mem_def.mpr hb) with hl | hr
    · exact hchain b (Array.mem_def.mp hl)
    · exact hans b (Array.mem_def.mp hr)

/-- `localAnswer` only ever serves and accumulates tree data: an answer
    hit's records all agree (they pass the answer-grade lookup), and the
    chain only grows by canonical re-encodings of cached (hence agreeing,
    well-formed) CNAME records. -/
theorem localAnswer_sound {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ (fuel : Nat) (sname : ByteArray) (chain : Array ByteArray),
    (∀ b ∈ chain.toList, RRAgrees T b) →
    (match localAnswer (C := DnsCache) (RR := ResourceRecord)
        c qtype qclass now fuel sname chain with
     | .answerHit _ chain' rrs =>
       (∀ b ∈ chain'.toList, RRAgrees T b) ∧
       ∀ rr ∈ rrs, RRInTree T rr ∧ WfRR rr
     | .miss _ chain' => ∀ b ∈ chain'.toList, RRAgrees T b
     | .negative _ _ => True)
  | 0, _, _, hchain => hchain
  | fuel + 1, sname, chain, hchain => by
    unfold localAnswer
    split
    · -- answerHit
      next sname' chain' rrs heq =>
      split at heq
      · cases heq
      · dsimp only [] at heq
        split at heq
        · split at heq
          · cases heq
          · split at heq
            · next crr hcrr =>
              have hmem : crr ∈ (TrustworthinessSpec.answers (C := DnsCache)
                  c sname (5 : BitVec 16) qclass now : Array ResourceRecord) :=
                Array.mem_of_getElem? hcrr
              have hcrrIn : RRInTree T crr ∧ WfRR crr :=
                lookupAnswerable_agrees h sname (5 : BitVec 16) qclass now crr hmem
              have ihres := localAnswer_sound h qtype qclass now fuel
                (RRParse.rrRdata crr) (chain.push (RRParse.rrBytes crr)) (by
                  intro b hb
                  rcases Array.mem_push.mp (Array.mem_def.mpr hb) with hl | rfl
                  · exact hchain b (Array.mem_def.mp hl)
                  · exact ⟨crr, parseRaw_rrBytes_of_wf hcrrIn.2, hcrrIn.1⟩)
              rw [heq] at ihres
              exact ihres
            · cases heq
        · cases heq
          refine ⟨hchain, ?_⟩
          intro rr hmem
          exact lookupAnswerable_agrees h sname qtype qclass now rr hmem
    · -- miss
      next sname' chain' heq =>
      split at heq
      · cases heq
      · dsimp only [] at heq
        split at heq
        · split at heq
          · cases heq
            exact hchain
          · split at heq
            · next crr hcrr =>
              have hmem : crr ∈ (TrustworthinessSpec.answers (C := DnsCache)
                  c sname (5 : BitVec 16) qclass now : Array ResourceRecord) :=
                Array.mem_of_getElem? hcrr
              have hcrrIn : RRInTree T crr ∧ WfRR crr :=
                lookupAnswerable_agrees h sname (5 : BitVec 16) qclass now crr hmem
              have ihres := localAnswer_sound h qtype qclass now fuel
                (RRParse.rrRdata crr) (chain.push (RRParse.rrBytes crr)) (by
                  intro b hb
                  rcases Array.mem_push.mp (Array.mem_def.mpr hb) with hl | rfl
                  · exact hchain b (Array.mem_def.mp hl)
                  · exact ⟨crr, parseRaw_rrBytes_of_wf hcrrIn.2, hcrrIn.1⟩)
              rw [heq] at ihres
              exact ihres
            · cases heq
              exact hchain
        · cases heq
    · -- negative
      trivial

/-- Step 1 only ever answers tree data, and its goto states keep the
    invariant (the chain may grow by cached-CNAME re-encodings). -/
theorem stepCheckLocal_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s) :
    (∀ r, stepCheckLocal s = .answer r → SectionAgrees T r.answer) ∧
    (∀ st s', stepCheckLocal s = .goto st s' →
      StateAgrees T s' ∧ s'.lastResponse = s.lastResponse) := by
  constructor
  · intro r hr
    unfold stepCheckLocal at hr
    split at hr
    · cases hr
    · split at hr
      · cases hr
      · next qu _ =>
        have hl := localAnswer_sound hs.cache qu.qtype qu.qclass s.now 8
          s.resources.sname s.cnameChain hs.chain
        split at hr
        · next rc soaAuth heqL =>
          cases hr
          exact negativeResponse_answer_agrees _ _ _
        · next sname' chain' rrs heqL =>
          cases hr
          rw [heqL] at hl
          exact finalizeAnswer_answer_agrees hl.1
            (cacheResponse_agrees (fun rr hm => hl.2 rr hm) _)
        · next sname' chain' heqL =>
          split at hr <;> cases hr
  · intro st s' hgo
    unfold stepCheckLocal at hgo
    split at hgo
    · cases hgo; exact ⟨hs, rfl⟩
    · split at hgo
      · cases hgo; exact ⟨hs, rfl⟩
      · next qu _ =>
        have hl := localAnswer_sound hs.cache qu.qtype qu.qclass s.now 8
          s.resources.sname s.cnameChain hs.chain
        split at hgo
        · cases hgo
        · cases hgo
        · next sname' chain' heqL =>
          rw [heqL] at hl
          split at hgo
          · cases hgo; exact ⟨hs, rfl⟩
          · cases hgo
            exact ⟨⟨hs.cache, hl⟩, rfl⟩

/-- Step 4 only ever answers tree data (4a/NODATA/TC: the chain plus the
    consistent response's answer), and every goto keeps the invariant
    (4c grows the chain by the response's answer RRs and caches them; 4b
    caches authority and glue; 4d changes nothing). All gotos clear the
    analyzed response. -/
theorem stepAnalyzeResponse_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s)
    (hresp : ∀ r, s.lastResponse = some r → ResponseConsistent T r) :
    (∀ r, stepAnalyzeResponse s = .answer r → SectionAgrees T r.answer) ∧
    (∀ st s', stepAnalyzeResponse s = .goto st s' →
      StateAgrees T s' ∧ s'.lastResponse = none) := by
  constructor
  · intro r hr
    unfold stepAnalyzeResponse at hr
    split at hr
    · cases hr
    · next resp heq =>
      have hcons := hresp resp heq
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · split at hr
            · cases hr
            · split at hr
              · cases hr
                exact finalizeAnswer_answer_agrees hs.chain hcons.answer
              · cases hr
          · split at hr
            · cases hr
              exact finalizeAnswer_answer_agrees hs.chain hcons.answer
            · split at hr
              · cases hr
                exact finalizeAnswer_answer_agrees hs.chain hcons.answer
              · split at hr
                · cases hr
                  exact finalizeAnswer_answer_agrees hs.chain hcons.answer
                · cases hr
  · intro st s' hgo
    unfold stepAnalyzeResponse at hgo
    split at hgo
    · cases hgo
    · next resp heq =>
      have hcons := hresp resp heq
      split at hgo
      · -- 4c: chase — cache the answer, extend the chain
        cases hgo
        refine ⟨⟨?_, ?_⟩, rfl⟩
        · exact cacheAgrees_cacheUnlessTruncated hs.cache resp
            hcons.answer _ s.now
        · intro b hb
          rcases Array.mem_append.mp (Array.mem_def.mpr hb) with hl | hr'
          · exact hs.chain b (Array.mem_def.mp hl)
          · exact hcons.answer b (Array.mem_def.mp hr')
      · split at hgo
        · -- 4d: retry
          cases hgo
          exact ⟨⟨hs.cache, hs.chain⟩, rfl⟩
        · split at hgo
          · split at hgo
            · -- 4b: delegation — cache authority + additional
              cases hgo
              refine ⟨⟨?_, hs.chain⟩, rfl⟩
              exact cacheAgrees_cacheUnlessTruncated
                (cacheAgrees_cacheUnlessTruncated hs.cache resp
                  hcons.authority _ s.now)
                resp hcons.additional _ s.now
            · split at hgo <;> cases hgo
          · split at hgo
            · cases hgo
            · split at hgo
              · cases hgo
              · split at hgo <;> cases hgo

/-- One `step` only ever answers tree data and preserves the invariant:
    the response-consistency premise survives every goto (the analyzed
    response is cleared; other steps do not touch `lastResponse`). -/
theorem step_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s)
    (hresp : ∀ r, s.lastResponse = some r → ResponseConsistent T r) :
    (∀ r, step s = .answer r → SectionAgrees T r.answer) ∧
    (∀ st s', step s = .goto st s' → StateAgrees T s' ∧
      (∀ r, s'.lastResponse = some r → ResponseConsistent T r)) ∧
    (∀ s', step s = .needsIO s' → StateAgrees T s') := by
  unfold step
  split
  · -- checkAnswer
    obtain ⟨ha, hg⟩ := stepCheckLocal_sound (s := s) hs
    refine ⟨ha, ?_, ?_⟩
    · intro st s' h
      obtain ⟨hs', heq⟩ := hg st s' h
      exact ⟨hs', fun r hr => hresp r (heq ▸ hr)⟩
    · intro s' h
      unfold stepCheckLocal at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> first | cases h | (split at h <;> cases h)
  · -- findServers: slist-only updates
    refine ⟨?_, ?_, ?_⟩
    · intro r h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> cases h
      · split at h <;> cases h
    · intro st s' h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> cases h <;>
          exact ⟨⟨hs.cache, hs.chain⟩, hresp⟩
      · split at h <;> cases h <;>
          exact ⟨⟨hs.cache, hs.chain⟩, hresp⟩
    · intro s' h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> cases h
      · split at h <;> cases h
  · -- sendQueries
    refine ⟨?_, ?_, ?_⟩
    · intro r h
      unfold stepSendQueries at h
      split at h <;> cases h
    · intro st s' h
      unfold stepSendQueries at h
      split at h
      · cases h; exact ⟨hs, hresp⟩
      · cases h
    · intro s' h
      unfold stepSendQueries at h
      split at h
      · cases h
      · cases h; exact hs
  · -- analyzeResponse
    obtain ⟨ha, hg⟩ := stepAnalyzeResponse_sound (s := s) hs hresp
    refine ⟨ha, ?_, ?_⟩
    · intro st s' h
      obtain ⟨hs', hnone⟩ := hg st s' h
      exact ⟨hs', fun r hr => by rw [hnone] at hr; cases hr⟩
    · intro s' h
      unfold stepAnalyzeResponse at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · split at h <;> cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · split at h <;> cases h

/-- THE pure-resolver soundness theorem: starting from an agreeing state,
    with every injected response T-consistent, the resolve loop only ever
    completes with answers made of tree data, and pauses preserve the
    invariant. The cache can be poisoned by nothing; the client can be
    told nothing the tree does not hold. -/
theorem resolveLoop_sound {T : Node ResourceRecord} :
    ∀ (fuel : Nat) (s : State S DnsCache NS ResourceRecord),
    StateAgrees T s →
    (∀ r, s.lastResponse = some r → ResponseConsistent T r) →
    (match resolve.loop (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) s fuel with
     | .ok (.done resp) => SectionAgrees T resp.answer
     | .ok (.paused s') => StateAgrees T s'
     | .error _ => True)
  | 0, _, _, _ => trivial
  | fuel + 1, s, hs, hresp => by
    unfold resolve.loop
    obtain ⟨ha, hg, hio⟩ := step_sound (s := s) hs hresp
    split
    · -- completed with an answer
      next resp heq =>
      split at heq
      · next r hstep =>
        cases heq
        exact ha resp hstep
      · next st s' hstep =>
        obtain ⟨hs', hresp'⟩ := hg st s' hstep
        have ih := resolveLoop_sound fuel { s' with currentStep := st }
          ⟨hs'.cache, hs'.chain⟩ hresp'
        rw [heq] at ih
        exact ih
      · next s' hstep => exact absurd heq (by simp)
      · next msg hstep => cases heq
    · -- paused for IO
      next s' heq =>
      split at heq
      · next r hstep => exact absurd heq (by simp)
      · next st s'' hstep =>
        obtain ⟨hs'', hresp''⟩ := hg st s'' hstep
        have ih := resolveLoop_sound fuel { s'' with currentStep := st }
          ⟨hs''.cache, hs''.chain⟩ hresp''
        rw [heq] at ih
        exact ih
      · next s'' hstep =>
        cases heq
        exact hio s' hstep
      · next msg hstep => cases heq
    · trivial

/-- `resume` with a T-consistent response keeps the loop sound: this is
    the per-exchange composition point for the IO shim — each accepted
    upstream response re-enters the pure loop under the oracle. -/
theorem resume_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s)
    {resp : Format} (hcons : ResponseConsistent T resp) (fuel : Nat) :
    (match resume (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) s resp fuel with
     | .ok (.done r) => SectionAgrees T r.answer
     | .ok (.paused s') => StateAgrees T s'
     | .error _ => True) := by
  unfold resume
  exact resolveLoop_sound fuel _ ⟨hs.cache, hs.chain⟩
    (fun r hr => by cases hr; exact hcons)

/-- Soundness from the entry point: resolving a fresh query over an
    agreeing cache (e.g. the empty one) is sound — the initial state has
    an empty chain and no pending response. -/
theorem resolve_sound {T : Node ResourceRecord} (query : Format) (sbelt : S)
    (fuel : Nat) (now : UInt32) {initCache : DnsCache}
    (hc : CacheAgrees T initCache) :
    (match resolve (S := S) (C := DnsCache) (NS := NS) (RR := ResourceRecord)
        query sbelt fuel now initCache with
     | .ok (.done resp) => SectionAgrees T resp.answer
     | .ok (.paused s') => StateAgrees T s'
     | .error _ => True) := by
  unfold resolve
  refine resolveLoop_sound fuel _ ⟨hc, ?_⟩ ?_
  · intro b hb
    simp [initFromQuery] at hb
  · intro r hr
    simp [initFromQuery] at hr

/-- Negative-path fidelity at the serving edge: any negative rcode the
    cache serves for a query key is DESERVED by the tree — an NXDOMAIN
    only for genuinely missing nodes, and (for any served negative) no
    record of the queried type exists. The cache entry's key matches the
    query case-insensitively; `nodeAtName_congrCI` transfers the stored
    deservedness to the queried spelling. -/
theorem lookupNegative_deserved {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (name : ByteArray) (qtype qclass : BitVec 16)
    (now : UInt32) {rc : Rcode}
    (hl : DnsCache.lookupNegative c name qtype qclass now = some rc) :
    (rc = Rcode.nameError → nodeAtName T name = none) ∧
    NoRecordOfType T name qtype := by
  unfold DnsCache.lookupNegative DnsCache.lookupNxdomain at hl
  rcases hor : c.negatives.findSome? (fun e =>
      if nameEqCI e.name name && e.qclass == qclass && e.expiry > now
          && e.rcode == Rcode.nameError then some e.rcode else none) with _ | rc0
  · -- no NXDOMAIN entry: the per-type negative entry fired
    rw [hor] at hl
    simp at hl
    obtain ⟨e, hmem, hcond⟩ := Array.exists_of_findSome?_eq_some hl
    split at hcond
    · next hkey =>
      cases hcond
      try simp only [Bool.and_eq_true] at hkey
      have hci : nameEqCI e.name name = true := hkey.1.1.1
      have hnodes : nodeAtName T e.name = nodeAtName T name :=
        nodeAtName_congrCI T hci
      have hqt : e.qtype = qtype := by
        have h2 := hkey.1.1.2
        first | exact h2 | exact eq_of_beq h2
      constructor
      · intro hrc
        have := h.nxdomainDeserved e hmem hrc
        rw [← hnodes]
        exact this
      · intro n hn rr hmemr hty
        have := h.negativesDeserved e hmem n (by rw [hnodes]; exact hn) rr hmemr
        rw [hqt] at this
        exact this hty
    · cases hcond
  · -- NXDOMAIN entry fired (rc = its rcode, necessarily nameError)
    rw [hor] at hl
    simp at hl
    cases hl
    obtain ⟨e, hmem, hcond⟩ := Array.exists_of_findSome?_eq_some hor
    split at hcond
    · next hkey =>
      cases hcond
      try simp only [Bool.and_eq_true] at hkey
      have hci : nameEqCI e.name name = true := hkey.1.1.1
      have hnodes : nodeAtName T e.name = nodeAtName T name :=
        nodeAtName_congrCI T hci
      have hrcE : e.rcode = Rcode.nameError := by
        have h2 := hkey.2
        first
        | exact h2
        | (revert h2; cases e.rcode <;> intro h2 <;>
            first | rfl | exact absurd h2 (by decide))
      have habs : nodeAtName T name = none := by
        rw [← hnodes]
        exact h.nxdomainDeserved e hmem hrcE
      exact ⟨fun _ => habs, noRecordOfType_of_absent habs qtype⟩
    · cases hcond

end StepSoundness

-- ============================================================
-- Shim soundness: the IO loop under the weakened oracle
-- ============================================================

section ShimSoundness

open VeriDNS.Impl.Server VeriDNS.Impl.Resolver VeriDNS.Impl.SList
open VeriDNS.Impl.Cache (DnsCache)

/-- Every monadic value satisfies the trivial postcondition. -/
private theorem satisfiesM_true {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (x : m α) : SatisfiesM (fun _ => True) x :=
  ⟨(fun a => ⟨a, trivial⟩) <$> x, by simp [Functor.map_map]⟩

variable {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
  [UdpSocket M Sock ByteArray]

/-- The weakened oracle, operationally: whatever the network transport
    delivers, any response that survives `forwardQuery`'s datagram gate
    AND the RFC 5452 `acceptResponse` match is consistent with the tree.
    Spoofs, mismatches, undecodable datagrams, and timeouts are entirely
    unconstrained. -/
def NetworkConsistent (T : Node ResourceRecord) (M : Type → Type) (Sock : Type)
    [Monad M] [UdpSocket M Sock ByteArray] : Prop :=
  ∀ (q : Format) (addr : ByteArray),
    SatisfiesM (m := M)
      (fun ro => ∀ resp₀ resp, ro = some resp₀ →
        acceptResponse q resp₀ = some resp → ResponseConsistent T resp)
      (forwardQuery (M := M) (Sock := Sock) q addr)

/-- The result postcondition: a completed response's answer section is
    tree data, and the returned cache still agrees. -/
def ShimSound (T : Node ResourceRecord)
    (rc : Except String Format × DnsCache) : Prop :=
  (∀ f, rc.1 = .ok f → SectionAgrees T f.answer) ∧ CacheAgrees T rc.2

/-- THE shim-soundness theorem: under the weakened oracle, the IO resume
    loop — upstream exchanges, RFC 5452 gating, bogus-delegation
    filtering, glueless NS sub-resolution, retries, deadlines — only ever
    completes with answers made of tree data, and the cache it returns
    still agrees with the tree. Composes `resume_sound` (the pure loop)
    through every monadic round. -/
theorem ioResumeLoop_sound (T : Node ResourceRecord)
    (hnet : NetworkConsistent T M Sock) (sbelt : DnsSList) :
    ∀ (depth fuel : Nat)
      (state : State DnsSList DnsCache SlistEntry ResourceRecord)
      (deadline : UInt32),
    StateAgrees T state →
    SatisfiesM (ShimSound T)
      (ioResumeLoop (M := M) (Sock := Sock) sbelt state deadline depth fuel)
  | depth, 0, state, deadline, hs => by
    rw [ioResumeLoop.eq_def]
    exact SatisfiesM.pure (p := ShimSound T) ⟨(fun _ h => nomatch h), hs.cache⟩
  | depth, fuel' + 1, state, deadline, hs => by
    rw [ioResumeLoop.eq_def]
    dsimp only []
    refine SatisfiesM.bind (satisfiesM_true _) ?_
    intro t _
    split
    · -- deadline exceeded
      exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
    · refine SatisfiesM.bind (satisfiesM_true _) ?_
      intro _ _
      split
      · -- no server with an address
        split
        · -- glueless sub-resolution (depth = depth' + 1)
          next _ _ depth' nsName _ =>
          refine SatisfiesM.bind (satisfiesM_true _) ?_
          intro _ _
          split
          · -- sub-resolve completed purely
            refine SatisfiesM.bind
              (SatisfiesM.pure (p := fun y => y.2 = state.resources.cache) rfl) ?_
            intro y hy
            split
            · split
              · refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                  ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
              · refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                  ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
            · refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
          · -- sub-resolve paused: inner IO recursion at depth'
            next st hres =>
            refine SatisfiesM.bind
              (ioResumeLoop_sound T hnet sbelt depth' fuel' st deadline (by
                have h := resolve_sound (S := DnsSList) (NS := SlistEntry)
                  (T := T) (mkAddressQuery nsName)
                  sbelt 64 state.now (cacheAgrees_empty T)
                rw [hres] at h
                exact h)) ?_
            intro _ _
            refine SatisfiesM.bind
              (SatisfiesM.pure (p := fun y => y.2 = state.resources.cache) rfl) ?_
            intro y hy
            split
            · split
              · refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                  ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
              · refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                  ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
            · refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
          · -- sub-resolve failed purely
            refine SatisfiesM.bind
              (SatisfiesM.pure (p := fun y => y.2 = state.resources.cache) rfl) ?_
            intro y hy
            split
            · split
              · refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                  ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
              · refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                  ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
            · refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet sbelt depth' fuel' _ _
                ⟨(show CacheAgrees T y.snd by rw [hy]; exact hs.cache), hs.chain⟩
        · -- no glueless target
          exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
      · -- a server with a known address
        next entry ipAddr _ =>
        split
        · -- no sub-query buildable
          exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
        · next subQuery₀ _ =>
          refine SatisfiesM.bind (satisfiesM_true _) ?_
          intro _ _
          refine SatisfiesM.bind (satisfiesM_true _) ?_
          intro rid _
          refine SatisfiesM.bind (hnet _ _) ?_
          intro upstreamResp hup
          split
          · -- timeout: retry next candidate
            exact ioResumeLoop_sound T hnet sbelt depth fuel' _ _
              ⟨hs.cache, hs.chain⟩
          · next resp₀ =>
            split
            · -- RFC 5452 mismatch: dropped
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet sbelt depth fuel' _ _
                ⟨hs.cache, hs.chain⟩
            · next resp hacc =>
              have hcons : ResponseConsistent T resp :=
                hup resp₀ resp rfl hacc
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              split
              · -- bogus delegation: ignored
                refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet sbelt depth fuel' _ _
                  ⟨hs.cache, hs.chain⟩
              · -- accepted: the pure loop takes over
                split
                · -- completed
                  next finalResp hdone =>
                  have hres := resume_sound (S := DnsSList) (NS := SlistEntry)
                    (T := T)
                    (s := if (resp.header.rcode == Rcode.serverFailure
                        || !classifiableB resp) = true then
                      { state with resources := { state.resources with
                          slist := (state.resources.slist.markQueried
                            entry.name).removeServer entry.name } }
                    else
                      { state with resources := { state.resources with
                          slist := state.resources.slist.markQueried
                            entry.name } })
                    (by split <;> exact ⟨hs.cache, hs.chain⟩) hcons 64
                  rw [hdone] at hres
                  exact SatisfiesM.pure ⟨(fun f hf => by cases hf; exact hres),
                    (by split <;> exact hs.cache)⟩
                · -- paused: continue the IO loop
                  next state' hpause =>
                  have hres := resume_sound (S := DnsSList) (NS := SlistEntry)
                    (T := T)
                    (s := if (resp.header.rcode == Rcode.serverFailure
                        || !classifiableB resp) = true then
                      { state with resources := { state.resources with
                          slist := (state.resources.slist.markQueried
                            entry.name).removeServer entry.name } }
                    else
                      { state with resources := { state.resources with
                          slist := state.resources.slist.markQueried
                            entry.name } })
                    (by split <;> exact ⟨hs.cache, hs.chain⟩) hcons 64
                  rw [hpause] at hres
                  exact ioResumeLoop_sound T hnet sbelt depth fuel' state' deadline hres
                · -- resume error
                  refine SatisfiesM.bind (satisfiesM_true _) ?_
                  intro _ _
                  exact SatisfiesM.pure ⟨(fun _ h => nomatch h),
                    (by split <;> exact hs.cache)⟩
  termination_by depth fuel => (depth, fuel)
  decreasing_by all_goals
    (first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega))

/-- THE end-to-end soundness theorem at the public entry point: starting
    from an agreeing persistent cache, under the weakened network oracle,
    a full `resolveWithIO` run — pure resolution, every upstream exchange,
    every retry — only ever completes with an answer made of tree data,
    and hands back a cache that still agrees with the tree. -/
theorem resolveWithIO_sound (T : Node ResourceRecord)
    (hnet : NetworkConsistent T M Sock) (query : Format) (sbelt : DnsSList)
    {cache : DnsCache} (hc : CacheAgrees T cache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) :
    SatisfiesM (ShimSound T)
      (resolveWithIO (M := M) (Sock := Sock) query sbelt cache now
        fuel depth budget) := by
  unfold resolveWithIO
  have h := resolve_sound (S := DnsSList) (NS := SlistEntry) (T := T)
    query sbelt 64 now hc
  split
  · next resp hdone =>
    rw [hdone] at h
    exact SatisfiesM.pure ⟨(fun f hf => by cases hf; exact h), hc⟩
  · next st hpause =>
    rw [hpause] at h
    exact ioResumeLoop_sound T hnet sbelt depth fuel st (now + budget) h
  · exact SatisfiesM.pure ⟨(fun _ hf => nomatch hf), hc⟩

end ShimSoundness

end VeriDNS.Proof.NameTree
