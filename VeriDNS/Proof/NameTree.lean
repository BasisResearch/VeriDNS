import VeriDNS.Impl.NameTree
import VeriDNS.Impl.Resolver
import VeriDNS.Impl.Cache
import VeriDNS.Impl.Server
import VeriDNS.Spec.ServerAlgorithm
import VeriDNS.Proof.DomainName
import VeriDNS.Proof.ResourceRecord

namespace VeriDNS.Proof.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.NameTree
open VeriDNS.Impl.DomainName (nameEqCI)

variable {RR : Type}

/-- Same logical RR data: key equality plus rdata identity modulo 0x20 case in
embedded domain names (RFC 4343 §3) — the member identity used by the cache
write-boundary dedup (finding 053). -/
def sameData (a b : ResourceRecord) : Bool :=
  nameEqCI a.name b.name && a.type == b.type && a.class == b.class &&
    VeriDNS.Impl.Cache.rdataEqCI b.type a.rdata b.rdata

def RRInTree (T : Node ResourceRecord) (rr : ResourceRecord) : Prop :=
  ∃ n, nodeAtName T rr.name = some n ∧
    ∃ rr' ∈ n.resourceSet.toList, sameData rr' rr = true

def NoRecordOfType (T : Node ResourceRecord) (name : ByteArray)
    (qtype : BitVec 16) : Prop :=
  ∀ n, nodeAtName T name = some n →
    ∀ rr ∈ n.resourceSet.toList, ¬ rr.type == qtype

def RRAgrees (root : Node ResourceRecord) (bytes : ByteArray) : Prop :=
  ∃ rr, RRParse.parseRaw (RR := ResourceRecord) bytes = some rr ∧
    RRInTree root rr

def SectionAgrees (root : Node ResourceRecord) (rrs : Array ByteArray) : Prop :=
  ∀ b ∈ rrs.toList, RRAgrees root b

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

inductive Reaches (T : Node ResourceRecord) (qtype : BitVec 16) :
    ByteArray → ByteArray → Prop where
  | refl {q s : ByteArray} :
      VeriDNS.Impl.DomainName.nameEqCI q s = true → Reaches T qtype q s
  | step {q s t : ByteArray} {rr : ResourceRecord} {c : ByteArray} :
      Reaches T qtype q s →
      treeLookup T s qtype = .redirect rr c →
      VeriDNS.Impl.DomainName.nameEqCI c t = true →
      Reaches T qtype q t

def HasType (rrs : Array ByteArray) (t : BitVec 16) : Prop :=
  ∃ b ∈ rrs.toList, ∃ rr,
    RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧ rr.type = t

def HasOwnedCname (qname : ByteArray) (rrs : Array ByteArray) : Prop :=
  ∃ b ∈ rrs.toList, ∃ rr,
    RRParse.parseRaw (RR := ResourceRecord) b = some rr ∧ rr.type = cnameType ∧
    VeriDNS.Impl.DomainName.nameEqCI rr.name qname = true

def SectionWhole (root : Node ResourceRecord) (rrs : Array ByteArray) : Prop :=
  ∀ b ∈ rrs.toList, ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr →
    ∀ n, nodeAtName root rr.name = some n →
      ∀ trr ∈ n.resourceSet.toList, trr.type = rr.type →
        ∃ b' ∈ rrs.toList, ∃ rr',
          RRParse.parseRaw (RR := ResourceRecord) b' = some rr' ∧
          sameData rr' trr = true

def TtlUniform (rrs : Array ByteArray) : Prop :=
  ∀ b₁ ∈ rrs.toList, ∀ b₂ ∈ rrs.toList, ∀ r₁ r₂,
    RRParse.parseRaw (RR := ResourceRecord) b₁ = some r₁ →
    RRParse.parseRaw (RR := ResourceRecord) b₂ = some r₂ →
    VeriDNS.Impl.DomainName.nameEqCI r₁.name r₂.name = true →
    r₁.type = r₂.type → r₁.class = r₂.class →
    r₁.ttl = r₂.ttl

structure ResponseConsistent (root : Node ResourceRecord) (resp : Format) : Prop where
  answer : SectionAgrees root resp.answer
  authority : SectionAgrees root resp.authority
  additional : SectionAgrees root resp.additional
  nameErrorDeserved : resp.header.rcode = Rcode.nameError →
    ∀ qu ∈ resp.question.toList, nodeAtName root qu.qname = none
  complete : AnswerComplete root resp
  answerWhole : resp.header.tc = 0 → SectionWhole root resp.answer
  authorityWhole : resp.header.tc = 0 → SectionWhole root resp.authority
  additionalWhole : resp.header.tc = 0 → SectionWhole root resp.additional
  answerTtlUniform : resp.header.tc = 0 → TtlUniform resp.answer
  authorityTtlUniform : resp.header.tc = 0 → TtlUniform resp.authority
  additionalTtlUniform : resp.header.tc = 0 → TtlUniform resp.additional

  rcodeFaithful : resp.answer.size > 0 →
    resp.header.rcode = Rcode.noError ∨ resp.header.rcode = Rcode.nameError

  answerShape : ∀ qu ∈ resp.question.toList, resp.header.tc = 0 →
    resp.header.rcode = Rcode.noError → resp.answer.size > 0 →
    HasType resp.answer qu.qtype ∨ HasOwnedCname qu.qname resp.answer

  answersFaithful : ∀ qu ∈ resp.question.toList, resp.header.tc = 0 →
    resp.header.rcode = Rcode.noError →
    HasType resp.answer qu.qtype →
    ∃ k chain rrsT,
      treeResolve root qu.qtype k qu.qname #[] = some (chain, .answer rrsT) ∧
      ∀ trr ∈ rrsT.toList, ∃ b ∈ resp.answer.toList, ∃ rr',
        RRParse.parseRaw (RR := ResourceRecord) b = some rr' ∧
        sameData rr' trr = true

  redirectsOnPath : ∀ qu ∈ resp.question.toList,
    ¬ HasType resp.answer qu.qtype →
    ∀ b ∈ resp.answer.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr →
      rr.type = cnameType →
      Reaches root qu.qtype qu.qname rr.rdata

  nodataDeserved : ∀ qu ∈ resp.question.toList, resp.header.tc = 0 →
    resp.header.rcode = Rcode.noError → resp.answer.isEmpty = true →
    ¬ (HasType resp.authority (2 : BitVec 16) ∧ resp.header.aa = 0
        ∧ ¬ HasType resp.authority (6 : BitVec 16)) →
    treeLookup root qu.qname qu.qtype = .nodata

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

structure LookupScenario (RR : Type) where
  root : Node RR
  qname : ByteArray
  qtype : BitVec 16
  chain : Array RR := #[]

namespace LookupScenario

variable [RRParse RR]

def wholeOfQNAMEMatched (s : LookupScenario RR) : Bool :=
  (nodeAtName s.root s.qname).isSome

def dataAtNodeCNAME (s : LookupScenario RR) : Bool :=
  match nodeAtName s.root s.qname with
  | some n =>
    n.resourceSet.size > 0 &&
    n.resourceSet.all (fun rr => RRParse.rrType rr == cnameType)
  | none => false

def qtypeNotMatchCNAME (s : LookupScenario RR) : Bool :=
  s.qtype != cnameType

def matchImpossible (s : LookupScenario RR) : Bool :=
  (nodeAtName s.root s.qname).isNone

def nameOriginal (s : LookupScenario RR) : Bool :=
  s.chain.isEmpty

end LookupScenario

open LookupScenario

def CnameExclusive [RRParse RR] (root : Node RR) : Prop :=
  ∀ qname n, nodeAtName root qname = some n →
    (∃ rr ∈ n.resourceSet.toList, RRParse.rrType rr == cnameType) →
    ∀ rr ∈ n.resourceSet.toList, RRParse.rrType rr == cnameType

abbrev Scenario (RR : Type) [RRParse RR] : Type :=
  { s : LookupScenario RR // CnameExclusive s.root }

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

  have hpos' : ¬ (n.resourceSet.filter
      (fun rr => RRParse.rrType rr == s.val.qtype)).size > 0 := by
    intro hgt
    obtain ⟨x, hx⟩ := Array.exists_mem_of_size_pos hgt
    obtain ⟨hxm, hxt⟩ := Array.mem_filter.mp hx
    have h5 := hall x (by simpa using hxm)
    simp only [beq_iff_eq] at hxt h5
    exact hq5' (by rw [← hxt]; exact h5)

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

theorem treeLookup_obligation_nameError (RR : Type) [RRParse RR] :
    ServerLookup.obligation_setAuthoritativeNameErrorInResponse (Scenario RR)
      (fun s => matchImpossible s.val)
      (fun s => nameOriginal s.val)
      (fun s => treeLookup s.val.root s.val.qname s.val.qtype = .nameError) := by
  intro s himp _
  simp only [LookupScenario.matchImpossible,
    Option.isNone_iff_eq_none] at himp
  exact (treeLookup_nameError_iff ..).mpr himp

section CICongruence

open VeriDNS.Impl.DomainName

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

theorem toggleCaseByte_toNat (b : UInt8) :
    (toggleCaseByte b).toNat =
      if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b.toNat + 32
      else if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then b.toNat - 32
      else b.toNat := by
  unfold toggleCaseByte
  by_cases h1 : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · rw [if_pos (by simp [UInt8.le_iff_toNat_le]; omega), if_pos h1,
      UInt8.toNat_add]
    have h32 : (32 : UInt8).toNat = 32 := rfl
    rw [h32]
    omega
  · rw [if_neg (by simp [UInt8.le_iff_toNat_le]; omega), if_neg h1]
    by_cases h2 : 97 ≤ b.toNat ∧ b.toNat ≤ 122
    · rw [if_pos (by simp [UInt8.le_iff_toNat_le]; omega), if_pos h2,
        UInt8.toNat_sub_of_le _ _ (by
          rw [UInt8.le_iff_toNat_le]
          have h32 : (32 : UInt8).toNat = 32 := rfl
          rw [h32]; omega)]
      rfl
    · rw [if_neg (by simp [UInt8.le_iff_toNat_le]; omega), if_neg h2]

theorem foldCaseByte_toggleCaseByte (b : UInt8) :
    foldCaseByte (toggleCaseByte b) = foldCaseByte b := by
  apply UInt8.toNat_inj.mp
  rw [foldCaseByte_toNat (toggleCaseByte b), foldCaseByte_toNat b,
    toggleCaseByte_toNat b]
  by_cases h1 : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · simp only [if_pos h1]
    rw [if_neg (by omega)]
  · simp only [if_neg h1]
    by_cases h2 : 97 ≤ b.toNat ∧ b.toNat ≤ 122
    · simp only [if_pos h2]
      rw [if_pos (by omega)]
      omega
    · simp only [if_neg h2]
      rw [if_neg h1]

theorem randomizeCase_foldNameCase (seed : UInt16) (n : ByteArray) :
    foldNameCase (randomizeCase seed n) = foldNameCase n := by
  unfold foldNameCase randomizeCase
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_mapIdx]
    split
    · exact foldCaseByte_toggleCaseByte _
    · rfl

theorem randomizeCase_nameEqCI (seed : UInt16) (n : ByteArray) :
    nameEqCI (randomizeCase seed n) n = true := by
  unfold nameEqCI
  rw [randomizeCase_foldNameCase]
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp

theorem randomizeCase_size (seed : UInt16) (n : ByteArray) :
    (randomizeCase seed n).size = n.size := by
  show (n.data.mapIdx _).size = n.data.size
  simp

theorem nameEqCI_of_beq {a b : ByteArray} (h : (a == b) = true) :
    nameEqCI a b = true := by
  have hab : a = b := by
    apply ByteArray.ext
    show a.data = b.data
    have h' : ByteArray.beq a b = true := h
    unfold ByteArray.beq at h'
    simpa using h'
  subst hab
  unfold nameEqCI
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp

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

theorem nodeAtName_congrCI {RR : Type} (root : Node RR) {a b : ByteArray}
    (h : nameEqCI a b = true) :
    nodeAtName root a = nodeAtName root b := by
  have hfold : foldNameCase a = foldNameCase b := by
    have h'' : ByteArray.beq (foldNameCase a) (foldNameCase b) = true := h
    unfold ByteArray.beq at h''
    exact ByteArray.ext (eq_of_beq h'')
  rw [← nodeAtName_fold root a, ← nodeAtName_fold root b, hfold]

end CICongruence

section WireFidelity

open VeriDNS.Impl
open VeriDNS.Impl.DomainName (decodeNameAux decodeName labelsToWireFormat)

private theorem validLabels_cons (l : ByteArray) (rest : Array ByteArray)
    (hl : 0 < l.size ∧ l.size ≤ 63)
    (hr : Proof.DomainName.ValidLabels rest) :
    Proof.DomainName.ValidLabels (#[l] ++ rest) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simpa using hl
  · have hi' : i - 1 < rest.size := by
      simp only [Array.size_append, Array.size_singleton] at hi
      omega
    have hres := hr (i - 1) hi'
    rw [Array.getElem_append_right (by simp; omega)]
    simpa using hres

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
      ·
        cases h
        intro i hi
        simp at hi
      · next hb0 =>
        split at h
        ·
          split at h
          · split at h
            · split at h
              · next labs ep hrec =>
                cases h
                exact ih _ _ _ _ hrec
              · cases h
            · cases h
          · cases h
        ·
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

theorem decodeName_valid (buf : ByteArray) (pos : Nat)
    (labels : Array ByteArray) (endPos : Nat)
    (h : DnsParser.run decodeName buf pos = .ok (labels, endPos)) :
    Proof.DomainName.ValidLabels labels := by
  unfold decodeName at h
  simp only [Proof.Primitives.run_bind, Proof.Primitives.run_getBuffer,
    Proof.Primitives.run_getPos] at h
  split at h
  · next ls ep haux =>
    split at h
    · simp only [Proof.Primitives.run_bind, Proof.Primitives.run_setPos,
        Proof.Primitives.run_pure] at h
      cases h
      exact decodeNameAux_valid buf _ _ _ _ _ haux
    · exact absurd h (by simp [DnsParser.fail])
  · next e haux =>
    exact absurd h (by simp [DnsParser.fail])

theorem decode_shape (bytes : ByteArray) (rr : VeriDNS.Spec.ResourceRecord)
    (n : Nat)
    (h : DnsParser.run ResourceRecord.decode bytes = .ok (rr, n)) :
    (∃ labels, Proof.DomainName.ValidLabels labels ∧
      (labelsToWireFormat labels).size ≤ 255 ∧
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
              refine ⟨⟨labels, decodeName_valid bytes 0 labels pos1 hname,
                Proof.DomainName.run_decodeName_le255 _ _ _ _ hname, rfl⟩, ?_⟩
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

def WfRR (rr : VeriDNS.Spec.ResourceRecord) : Prop :=
  (∃ labels, Proof.DomainName.ValidLabels labels ∧
    (labelsToWireFormat labels).size ≤ 255 ∧
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

theorem parseRaw_rrBytes_of_wf {rr : VeriDNS.Spec.ResourceRecord}
    (h : WfRR rr) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (RRParse.rrBytes rr) = some rr := by
  obtain ⟨⟨labels, hv, hle, hqn⟩, hrl⟩ := h
  simp only [RRParse.parseRaw, RRParse.rrBytes,
    Cache.instRRParseResourceRecord]
  rw [Proof.ResourceRecord.decode_encode rr labels hv hle hqn.symm hrl]

end WireFidelity

open VeriDNS.Impl.Cache

theorem rrInTree_set_ttl {T : Node ResourceRecord} {rr : ResourceRecord}
    (h : RRInTree T rr) (ttl : BitVec 32) :
    RRInTree T { rr with ttl := ttl } := by
  obtain ⟨n, hn, rr', hmem, hdata⟩ := h
  exact ⟨n, hn, rr', hmem, by simpa [sameData] using hdata⟩

theorem sameData_refl (rr : ResourceRecord) : sameData rr rr = true := by
  unfold sameData
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨VeriDNS.Proof.DomainName.nameEqCI_conforms rr.name rr.name rfl,
    by simp⟩, by simp⟩, ?_⟩
  show ByteArray.beq _ _ = true
  unfold ByteArray.beq
  simp

theorem rrInTree_of_rrAgrees {T : Node ResourceRecord} {bytes : ByteArray}
    {rr : ResourceRecord} (h : RRAgrees T bytes)
    (hp : RRParse.parseRaw (RR := ResourceRecord) bytes = some rr) :
    RRInTree T rr := by
  obtain ⟨rr', hparse, hin⟩ := h
  rw [hp] at hparse
  cases hparse
  exact hin

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

theorem cacheAgrees_store {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {rr : ResourceRecord}
    (hrr : RRInTree T rr) (hwf : WfRR rr)
    (now : UInt32) (cred : Trustworthiness) :
    CacheAgrees T (c.store rr now cred) := by
  refine ⟨?_, h.nxdomainDeserved, h.negativesDeserved⟩
  intro e he
  simp only [DnsCache.store] at he
  rcases Array.mem_push.mp he with hmem | heq
  · exact h.positives e (Array.mem_filter.mp hmem).1
  · subst heq
    exact ⟨hrr, hwf⟩

theorem cacheAgrees_storeChecked {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {rr : ResourceRecord}
    (hrr : RRInTree T rr) (hwf : WfRR rr)
    (cred : Trustworthiness) (now : UInt32) :
    CacheAgrees T (c.storeChecked rr cred now) := by
  simp only [DnsCache.storeChecked]
  split
  · exact h
  · split
    · exact h
    · exact cacheAgrees_store h hrr hwf now cred

theorem noRecordOfType_of_absent {T : Node ResourceRecord} {name : ByteArray}
    (h : nodeAtName T name = none) (qtype : BitVec 16) :
    NoRecordOfType T name qtype := by
  intro n hn
  rw [h] at hn
  cases hn

theorem cacheAgrees_storeNegative {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {name : ByteArray} {qtype qclass : BitVec 16}
    {rcode : Rcode} {soa : Option ResourceRecord} {expiry now : UInt32}
    (hnx : rcode = Rcode.nameError → nodeAtName T name = none)
    (hnod : NoRecordOfType T name qtype) :
    CacheAgrees T (c.storeNegative name qtype qclass rcode soa expiry now) := by
  refine ⟨h.positives, ?_, ?_⟩ <;> intro ne hne
  · simp only [DnsCache.storeNegative] at hne
    rcases Array.mem_push.mp hne with hmem | heq
    · exact h.nxdomainDeserved ne
        (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hmem)).1
    · subst heq
      exact hnx
  · simp only [DnsCache.storeNegative] at hne
    rcases Array.mem_push.mp hne with hmem | heq
    · exact h.negativesDeserved ne
        (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hmem)).1
    · subst heq
      exact hnod

theorem cacheAgrees_sweep {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (now : UInt32) :
    CacheAgrees T (c.sweep now) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro e he
  · exact h.positives e (Array.mem_filter.mp he).1
  · exact h.nxdomainDeserved e (Array.mem_filter.mp he).1
  · exact h.negativesDeserved e (Array.mem_filter.mp he).1

theorem cacheAgrees_bound {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) : CacheAgrees T c.boundExpiryClasses := by
  refine ⟨?_, h.nxdomainDeserved, h.negativesDeserved⟩
  intro e he
  exact h.positives e (mem_of_mem_evictClasses he)

theorem cacheAgrees_touchKeys {T : Node ResourceRecord} {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (h : CacheAgrees T c) : CacheAgrees T (c.touchKeys ks tnow) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro e he
  · rw [touchKeys_records] at he
    obtain ⟨e₀, he₀, heq⟩ := Array.mem_map.mp he
    subst heq
    rw [touchEntry_rr]
    exact h.positives e₀ he₀
  · rw [touchKeys_negatives] at he
    obtain ⟨e₀, he₀, heq⟩ := Array.mem_map.mp he
    subst heq
    rw [touchNegEntry_rcode, touchNegEntry_name]
    exact h.nxdomainDeserved e₀ he₀
  · rw [touchKeys_negatives] at he
    obtain ⟨e₀, he₀, heq⟩ := Array.mem_map.mp he
    subst heq
    rw [touchNegEntry_name, touchNegEntry_qtype]
    exact h.negativesDeserved e₀ he₀

theorem cacheAgrees_boundLruKeys {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) : CacheAgrees T c.boundLruKeys := by
  refine ⟨?_, h.nxdomainDeserved, h.negativesDeserved⟩
  intro e he
  exact h.positives e (mem_of_mem_evictLruKeys he)

theorem cacheAgrees_boundLru {T : Node ResourceRecord} {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (h : CacheAgrees T c) : CacheAgrees T (c.boundLru ks tnow) :=
  cacheAgrees_boundLruKeys (cacheAgrees_touchKeys ks tnow h)

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



theorem mem_normRaws {raws : Array ByteArray} {bn : ByteArray}
    (h : bn ∈ (normRaws raws).toList) :
    ∃ r ∈ rrsOf raws, bn = RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
        { r with ttl := groupMinTtl (rrsOf raws) r } := by
  simp only [normRaws, normalizeRRsetTtls, List.toList_toArray, List.mem_map] at h
  obtain ⟨nr, ⟨r, hr, hnr⟩, hbn⟩ := h
  exact ⟨r, hr, by rw [← hnr] at hbn; exact hbn.symm⟩

theorem mem_normRaws_of {raws : Array ByteArray} {r : VeriDNS.Spec.ResourceRecord}
    (hr : r ∈ rrsOf raws) :
    RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) { r with ttl := groupMinTtl (rrsOf raws) r }
      ∈ (normRaws raws).toList := by
  simp only [normRaws, normalizeRRsetTtls, List.toList_toArray, List.mem_map]
  exact ⟨_, ⟨r, hr, rfl⟩, rfl⟩

theorem parseRaw_normMember {raws : Array ByteArray} {r : VeriDNS.Spec.ResourceRecord}
    (hr : r ∈ rrsOf raws) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        (RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
          { r with ttl := groupMinTtl (rrsOf raws) r })
      = some { r with ttl := groupMinTtl (rrsOf raws) r } := by
  obtain ⟨bb, _, hpp⟩ := List.mem_filterMap.mp hr
  exact parseRaw_rrBytes_of_wf (wfRR_set_ttl (wfRR_of_parseRaw hpp) _)

theorem parseRaw_mem_normRaws {raws : Array ByteArray} {bn : ByteArray}
    (h : bn ∈ (normRaws raws).toList) {rr' : VeriDNS.Spec.ResourceRecord}
    (hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bn = some rr') :
    ∃ r ∈ rrsOf raws, rr' = { r with ttl := groupMinTtl (rrsOf raws) r } := by
  obtain ⟨r, hr, hbn⟩ := mem_normRaws h
  rw [hbn, parseRaw_normMember hr] at hp
  exact ⟨r, hr, (Option.some.inj hp).symm⟩

theorem normRaws_forall_transfer {raws : Array ByteArray}
    {P : VeriDNS.Spec.ResourceRecord → Prop}
    (hPttl : ∀ (r : VeriDNS.Spec.ResourceRecord) (t : BitVec 32), P r → P { r with ttl := t })
    (hraws : ∀ b ∈ raws.toList, ∀ rr,
      RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → P rr) :
    ∀ bn ∈ (normRaws raws).toList, ∀ rr',
      RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bn = some rr' → P rr' := by
  intro bn hbn rr' hp
  obtain ⟨r, hr, rfl⟩ := parseRaw_mem_normRaws hbn hp
  obtain ⟨b, hb, hpb⟩ := List.mem_filterMap.mp hr
  exact hPttl r _ (hraws b hb r hpb)

theorem sectionAgrees_normRaws {T : Node ResourceRecord} {raws : Array ByteArray}
    (h : SectionAgrees T raws) : SectionAgrees T (normRaws raws) := by
  intro bn hbn
  obtain ⟨r, hr, hbneq⟩ := mem_normRaws hbn
  refine ⟨{ r with ttl := groupMinTtl (rrsOf raws) r },
    by rw [hbneq]; exact parseRaw_normMember hr, ?_⟩
  obtain ⟨b, hb, hpb⟩ := List.mem_filterMap.mp hr
  obtain ⟨rr, hparse, htree⟩ := h b hb
  have hpb' : RRParse.parseRaw (RR := ResourceRecord) b = some r := hpb
  obtain rfl := Option.some.inj (hparse.symm.trans hpb')
  exact rrInTree_set_ttl htree _

section ResolverBridge

open VeriDNS.Impl.Resolver

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

theorem cacheResponse_agrees {T : Node ResourceRecord} {rrs : Array ResourceRecord}
    (hrrs : ∀ rr ∈ rrs, RRInTree T rr ∧ WfRR rr) (q : Format) :
    SectionAgrees T (cacheResponse (RR := ResourceRecord) q rrs).answer := by
  intro b hb
  simp only [cacheResponse] at hb
  obtain ⟨rr, hmem, hbytes⟩ := Array.mem_map.mp (by simpa using hb)
  obtain ⟨hin, hwf⟩ := hrrs rr hmem
  exact ⟨rr, hbytes ▸ parseRaw_rrBytes_of_wf hwf, hin⟩

theorem negativeResponse_answer_agrees {T : Node ResourceRecord}
    (q : Format) (rc : Rcode) (soaAuth : Array ResourceRecord) :
    SectionAgrees T (negativeResponse (RR := ResourceRecord) q rc soaAuth).answer := by
  intro b hb
  simp [negativeResponse] at hb

theorem cacheHit_serves_tree {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (q : Format) (name : ByteArray)
    (qtype qclass : BitVec 16) (now : UInt32) :
    SectionAgrees T (cacheResponse (RR := ResourceRecord) q
      (c.lookupAnswerable name qtype qclass now)).answer :=
  cacheResponse_agrees
    (fun rr hmem => lookupAnswerable_agrees h name qtype qclass now rr hmem) q

end ResolverBridge

section StepSoundness

open VeriDNS.Impl.Resolver

variable {S NS : Type} [SlistSpec S NS] [SlistFromNameSpec S NS] [Inhabited S]

structure StateAgrees (T : Node ResourceRecord)
    (s : State S DnsCache NS ResourceRecord) : Prop where
  cache : CacheAgrees T s.resources.cache
  chain : ∀ b ∈ s.cnameChain.toList, RRAgrees T b

theorem cacheAgrees_cacheUnlessTruncated {T : Node ResourceRecord}
    {c : DnsCache} (h : CacheAgrees T c) (resp : Format)
    {raws : Array ByteArray} (hsec : SectionAgrees T raws)
    (cred : Trustworthiness) (now : UInt32) :
    CacheAgrees T (cacheUnlessTruncated (C := DnsCache) (RR := ResourceRecord)
      c resp raws cred now) := by
  unfold cacheUnlessTruncated
  split
  · exact h
  · exact cacheAgrees_cacheRRs h (sectionAgrees_normRaws hsec) cred now

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

theorem localAnswer_sound {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) (qtype qclass : BitVec 16) (now : UInt32) :
    ∀ (fuel : Nat) (sname : ByteArray) (chain : Array ByteArray) (visited : Array ByteArray),
    (∀ b ∈ chain.toList, RRAgrees T b) →
    (match localAnswer (C := DnsCache) (RR := ResourceRecord)
        c qtype qclass now fuel sname chain visited with
     | .answerHit _ chain' rrs =>
       (∀ b ∈ chain'.toList, RRAgrees T b) ∧
       ∀ rr ∈ rrs, RRInTree T rr ∧ WfRR rr
     | .miss _ chain' => ∀ b ∈ chain'.toList, RRAgrees T b
     | .negative _ _ chain' => ∀ b ∈ chain'.toList, RRAgrees T b
     | .abort => True)
  | 0, _, _, _, _hchain => trivial
  | fuel + 1, sname, chain, visited, hchain => by
    unfold localAnswer
    split
    ·
      next sname' chain' rrs heq =>
      split at heq
      · cases heq
      · dsimp only [] at heq
        split at heq
        · split at heq
          · cases heq
          · split at heq
            · next crr hcrr =>
              split at heq
              · cases heq
              · next hrev =>
                have hmem : crr ∈ (TrustworthinessSpec.answers (C := DnsCache)
                    c sname (5 : BitVec 16) qclass now : Array ResourceRecord) :=
                  Array.mem_of_getElem? hcrr
                have hcrrIn : RRInTree T crr ∧ WfRR crr :=
                  lookupAnswerable_agrees h sname (5 : BitVec 16) qclass now crr hmem
                have ihres := localAnswer_sound h qtype qclass now fuel
                  (RRParse.rrRdata crr) (chain.push (RRParse.rrBytes crr))
                  (visited.push (RRParse.rrRdata crr)) (by
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
    ·
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
              split at heq
              · cases heq
                exact hchain
              · next hrev =>
                have hmem : crr ∈ (TrustworthinessSpec.answers (C := DnsCache)
                    c sname (5 : BitVec 16) qclass now : Array ResourceRecord) :=
                  Array.mem_of_getElem? hcrr
                have hcrrIn : RRInTree T crr ∧ WfRR crr :=
                  lookupAnswerable_agrees h sname (5 : BitVec 16) qclass now crr hmem
                have ihres := localAnswer_sound h qtype qclass now fuel
                  (RRParse.rrRdata crr) (chain.push (RRParse.rrBytes crr))
                  (visited.push (RRParse.rrRdata crr)) (by
                    intro b hb
                    rcases Array.mem_push.mp (Array.mem_def.mpr hb) with hl | rfl
                    · exact hchain b (Array.mem_def.mp hl)
                    · exact ⟨crr, parseRaw_rrBytes_of_wf hcrrIn.2, hcrrIn.1⟩)
                rw [heq] at ihres
                exact ihres
            · cases heq
              exact hchain
        · cases heq
    ·
      next rc soaAuth chain' heq =>
      split at heq
      · cases heq
        exact hchain
      · dsimp only [] at heq
        split at heq
        · split at heq
          · cases heq
          · split at heq
            · next crr hcrr =>
              split at heq
              · cases heq
              · next hrev =>
                have hmem : crr ∈ (TrustworthinessSpec.answers (C := DnsCache)
                    c sname (5 : BitVec 16) qclass now : Array ResourceRecord) :=
                  Array.mem_of_getElem? hcrr
                have hcrrIn : RRInTree T crr ∧ WfRR crr :=
                  lookupAnswerable_agrees h sname (5 : BitVec 16) qclass now crr hmem
                have ihres := localAnswer_sound h qtype qclass now fuel
                  (RRParse.rrRdata crr) (chain.push (RRParse.rrBytes crr))
                  (visited.push (RRParse.rrRdata crr)) (by
                    intro b hb
                    rcases Array.mem_push.mp (Array.mem_def.mpr hb) with hl | rfl
                    · exact hchain b (Array.mem_def.mp hl)
                    · exact ⟨crr, parseRaw_rrBytes_of_wf hcrrIn.2, hcrrIn.1⟩)
                rw [heq] at ihres
                exact ihres
            · cases heq
        · cases heq
    ·
      trivial

theorem stepCheckLocal_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s) :
    (∀ r rst, stepCheckLocal s = .answer r rst →
      SectionAgrees T r.answer ∧ StateAgrees T rst) ∧
    (∀ st s', stepCheckLocal s = .goto st s' →
      StateAgrees T s' ∧ s'.lastResponse = s.lastResponse) := by
  constructor
  · intro r rst hr
    unfold stepCheckLocal at hr
    split at hr
    · cases hr
    · split at hr
      · cases hr
      · next qu _ =>
        have hl := localAnswer_sound hs.cache qu.qtype qu.qclass s.now 8
          s.resources.sname s.cnameChain
          (cnameChaseVisited (RR := ResourceRecord) qu.qname s.cnameChain) hs.chain
        split at hr
        · next rc soaAuth chain' heqL =>
          cases hr
          rw [heqL] at hl
          exact ⟨finalizeAnswer_answer_agrees hl (negativeResponse_answer_agrees _ _ _),
            ⟨hs.cache, hl⟩⟩
        · next sname' chain' rrs heqL =>
          cases hr
          rw [heqL] at hl
          exact ⟨finalizeAnswer_answer_agrees hl.1
            (cacheResponse_agrees (fun rr hm => hl.2 rr hm) _),
            ⟨hs.cache, hl.1⟩⟩
        · next sname' chain' heqL =>
          split at hr <;> cases hr
        · cases hr
  · intro st s' hgo
    unfold stepCheckLocal at hgo
    split at hgo
    · cases hgo; exact ⟨hs, rfl⟩
    · split at hgo
      · cases hgo; exact ⟨hs, rfl⟩
      · next qu _ =>
        have hl := localAnswer_sound hs.cache qu.qtype qu.qclass s.now 8
          s.resources.sname s.cnameChain
          (cnameChaseVisited (RR := ResourceRecord) qu.qname s.cnameChain) hs.chain
        split at hgo
        · cases hgo
        · cases hgo
        · next sname' chain' heqL =>
          rw [heqL] at hl
          split at hgo
          · cases hgo; exact ⟨hs, rfl⟩
          · cases hgo
            exact ⟨⟨hs.cache, hl⟩, rfl⟩
        · cases hgo

theorem stepAnalyzeResponse_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s)
    (hresp : ∀ r, s.lastResponse = some r → ResponseConsistent T r) :
    (∀ r rst, stepAnalyzeResponse s = .answer r rst →
      SectionAgrees T r.answer ∧ StateAgrees T rst) ∧
    (∀ st s', stepAnalyzeResponse s = .goto st s' →
      StateAgrees T s' ∧ s'.lastResponse = none) := by
  constructor
  · intro r rst hr
    unfold stepAnalyzeResponse at hr
    split at hr
    · cases hr
    · next resp heq =>
      have hcons := hresp resp heq
      split at hr
      · simp only [] at hr
        split at hr
        · cases hr
          exact ⟨finalizeAnswer_answer_agrees hs.chain hcons.answer, hs⟩
        · split at hr <;> cases hr
      · split at hr
        · cases hr
        · split at hr
          · split at hr
            · cases hr
            · split at hr
              · cases hr
                exact ⟨finalizeAnswer_answer_agrees hs.chain hcons.answer, hs⟩
              · cases hr
          · split at hr
            ·

              simp only [] at hr
              cases hr
              exact ⟨finalizeAnswer_answer_agrees hs.chain hcons.answer,
                ⟨cacheAgrees_cacheUnlessTruncated hs.cache resp
                  (fun b hb => hcons.answer b (ownerRaws_subset _ _ hb)) _ s.now,
                 hs.chain⟩⟩
            · split at hr
              · cases hr
                exact ⟨finalizeAnswer_answer_agrees hs.chain hcons.answer, hs⟩
              · split at hr
                · cases hr
                  exact ⟨finalizeAnswer_answer_agrees hs.chain hcons.answer, hs⟩
                · split at hr
                  · cases hr
                    exact ⟨finalizeAnswer_answer_agrees hs.chain hcons.answer, hs⟩
                  · cases hr
  · intro st s' hgo
    unfold stepAnalyzeResponse at hgo
    split at hgo
    · cases hgo
    · next resp heq =>
      have hcons := hresp resp heq
      split at hgo
      ·
        simp only [] at hgo
        split at hgo
        · cases hgo
        split at hgo
        · cases hgo
        cases hgo
        refine ⟨⟨?_, ?_⟩, rfl⟩
        · exact cacheAgrees_cacheUnlessTruncated hs.cache resp
            (fun b hb => hcons.answer b (cnameRaws_subset _ _ hb)) _ s.now
        · intro b hb
          cases hq : resp.question[0]? with
          | none =>
            simp only [prependCnameLink, hq] at hb
            exact hs.chain b hb
          | some qu =>
            cases hext : extractCnameRR (RR := ResourceRecord) qu.qname resp.answer with
            | none =>
              simp only [prependCnameLink, hq, hext] at hb
              exact hs.chain b hb
            | some cnBytes =>
              simp only [prependCnameLink, hq, hext, Array.toList_push, List.mem_append,
                List.mem_singleton] at hb
              rcases hb with hl | hr'
              · exact hs.chain b hl
              · subst b
                exact hcons.answer cnBytes (Array.mem_def.mp (Array.mem_of_find?_eq_some hext))
      · split at hgo
        ·
          cases hgo
          exact ⟨⟨hs.cache, hs.chain⟩, rfl⟩
        · split at hgo
          · split at hgo
            ·
              cases hgo
              refine ⟨⟨?_, hs.chain⟩, rfl⟩
              exact cacheAgrees_cacheUnlessTruncated
                (cacheAgrees_cacheUnlessTruncated hs.cache resp
                  (fun b hb => hcons.authority b (bailiwickRaws_subset _ _ hb)) _ s.now)
                resp (fun b hb => hcons.additional b (bailiwickRaws_subset _ _ hb)) _ s.now
            · split at hgo
              · cases hgo
              ·
                cases hgo
                exact ⟨⟨hs.cache, hs.chain⟩, rfl⟩
          · split at hgo
            ·
              simp only [] at hgo; cases hgo
            · split at hgo
              · cases hgo
              · split at hgo
                · cases hgo
                · split at hgo
                  · cases hgo
                  · -- else: bizarre / foreign response ⇒ retry (goto sendQueries)
                    cases hgo
                    exact ⟨⟨hs.cache, hs.chain⟩, rfl⟩

theorem step_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s)
    (hresp : ∀ r, s.lastResponse = some r → ResponseConsistent T r) :
    (∀ r rst, step s = .answer r rst →
      SectionAgrees T r.answer ∧ StateAgrees T rst) ∧
    (∀ st s', step s = .goto st s' → StateAgrees T s' ∧
      (∀ r, s'.lastResponse = some r → ResponseConsistent T r)) ∧
    (∀ s', step s = .needsIO s' → StateAgrees T s') := by
  unfold step
  split
  ·
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
  ·
    refine ⟨?_, ?_, ?_⟩
    · intro r rst h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> (try split at h) <;> cases h
      · split at h <;> cases h
    · intro st s' h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> (try split at h) <;> cases h <;>
          exact ⟨⟨hs.cache, hs.chain⟩, hresp⟩
      · split at h <;> cases h <;>
          exact ⟨⟨hs.cache, hs.chain⟩, hresp⟩
    · intro s' h
      unfold stepFindServers at h
      dsimp only [] at h
      split at h
      · split at h <;> (try split at h) <;> cases h
      · split at h <;> cases h
  ·
    refine ⟨?_, ?_, ?_⟩
    · intro r rst h
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
  ·
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
        · simp only [] at h; split at h <;> (try split at h) <;> cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · split at h <;> cases h
            · split at h
              ·
                simp only [] at h; cases h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · split at h <;> (try split at h) <;> cases h

theorem resolveLoop_sound {T : Node ResourceRecord} :
    ∀ (fuel : Nat) (s : State S DnsCache NS ResourceRecord),
    StateAgrees T s →
    (∀ r, s.lastResponse = some r → ResponseConsistent T r) →
    (match resolve.loop (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) s fuel with
     | .ok (.done resp stF) => SectionAgrees T resp.answer ∧ StateAgrees T stF
     | .ok (.paused s') => StateAgrees T s'
     | .error _ => True)
  | 0, _, _, _ => trivial
  | fuel + 1, s, hs, hresp => by
    unfold resolve.loop
    obtain ⟨ha, hg, hio⟩ := step_sound (s := s) hs hresp
    split
    ·
      next resp stF heq =>
      split at heq
      · next r rst hstep =>
        cases heq
        exact ha _ _ hstep
      · next st s' hstep =>
        obtain ⟨hs', hresp'⟩ := hg st s' hstep
        have ih := resolveLoop_sound fuel { s' with currentStep := st }
          ⟨hs'.cache, hs'.chain⟩ hresp'
        rw [heq] at ih
        exact ih
      · next s' hstep => exact absurd heq (by simp)
      · next msg hstep => cases heq
    ·
      next s' heq =>
      split at heq
      · next r rst hstep => exact absurd heq (by simp)
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

theorem resume_sound {T : Node ResourceRecord}
    {s : State S DnsCache NS ResourceRecord} (hs : StateAgrees T s)
    {resp : Format} (hcons : ResponseConsistent T resp) (fuel : Nat) :
    (match resume (S := S) (C := DnsCache) (NS := NS)
        (RR := ResourceRecord) s resp fuel with
     | .ok (.done r stF) => SectionAgrees T r.answer ∧ StateAgrees T stF
     | .ok (.paused s') => StateAgrees T s'
     | .error _ => True) := by
  unfold resume
  exact resolveLoop_sound fuel _ ⟨hs.cache, hs.chain⟩
    (fun r hr => by cases hr; exact hcons)

theorem resolve_sound {T : Node ResourceRecord} (query : Format) (sbelt : S)
    (fuel : Nat) (now : UInt32) {initCache : DnsCache}
    (hc : CacheAgrees T initCache) :
    (match resolve (S := S) (C := DnsCache) (NS := NS) (RR := ResourceRecord)
        query sbelt fuel now initCache with
     | .ok (.done resp stF) => SectionAgrees T resp.answer ∧ StateAgrees T stF
     | .ok (.paused s') => StateAgrees T s'
     | .error _ => True) := by
  unfold resolve
  refine resolveLoop_sound fuel _ ⟨hc, ?_⟩ ?_
  · intro b hb
    simp [initFromQuery] at hb
  · intro r hr
    simp [initFromQuery] at hr

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
  ·
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
  ·
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

section ShimSoundness

open VeriDNS.Impl.Server VeriDNS.Impl.Resolver VeriDNS.Impl.SList
open VeriDNS.Impl.Cache (DnsCache)

private theorem satisfiesM_true {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (x : m α) : SatisfiesM (fun _ => True) x :=
  ⟨(fun a => ⟨a, trivial⟩) <$> x, by simp [Functor.map_map]⟩

variable {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
  [UdpSocket M Sock ByteArray]

def NetworkConsistent (T : Node ResourceRecord) (M : Type → Type) (Sock : Type)
    [Monad M] [UdpSocket M Sock ByteArray] : Prop :=
  ∀ (q : Format) (addr : ByteArray),
    SatisfiesM (m := M)
      (fun ro => ∀ resp₀ resp, ro = some resp₀ →
        acceptResponse q resp₀ = some resp → ResponseConsistent T resp)
      (forwardQuery (M := M) (Sock := Sock) q addr)

def NetworkConsistentTcp (T : Node ResourceRecord) (M : Type → Type) (Sock : Type)
    [Monad M] [UdpSocket M Sock ByteArray] : Prop :=
  ∀ (q : Format) (addr : ByteArray),
    SatisfiesM (m := M)
      (fun ro => ∀ resp₀ resp, ro = some resp₀ →
        acceptResponse q resp₀ = some resp → ResponseConsistent T resp)
      (tcpForward (M := M) (Sock := Sock) q addr)

def ShimSound (T : Node ResourceRecord)
    (rc : Except String Format × DnsCache) : Prop :=
  (∀ f, rc.1 = .ok f → SectionAgrees T f.answer) ∧ CacheAgrees T rc.2

theorem afterResume_sound (T : Node ResourceRecord)
    {state : State DnsSList DnsCache SlistEntry ResourceRecord}
    (entryName : ByteArray) {resp : Format}
    (hs : StateAgrees T state) (hcons : ResponseConsistent T resp) :
    (match afterResume state entryName resp with
     | .finished result cout =>
       (∀ f, result = .ok f → SectionAgrees T f.answer) ∧ CacheAgrees T cout
     | .continue st => StateAgrees T st) := by
  have hr := resume_sound (S := DnsSList) (NS := SlistEntry) (T := T)
    (s := dropIfBizarre state entryName resp)
    (by unfold dropIfBizarre; split <;> exact ⟨hs.cache, hs.chain⟩) hcons 64
  unfold afterResume
  split at hr <;> rename_i h <;> rw [h]
  · exact ⟨fun f hf => by cases hf; exact hr.1, cacheAgrees_boundLru _ _ hr.2.cache⟩
  · exact ⟨cacheAgrees_boundLru _ _ hr.cache, hr.chain⟩
  · exact ⟨(fun f hf => nomatch hf), hs.cache⟩

theorem gluelessRecheck_sound {T : Node ResourceRecord}
    {state : State DnsSList DnsCache SlistEntry ResourceRecord} {subCache : DnsCache}
    (hchain : ∀ b ∈ state.cnameChain.toList, RRAgrees T b)
    (hc : CacheAgrees T subCache) :
    ∀ hit, gluelessRecheck state subCache = some hit → SectionAgrees T hit.answer := by
  intro hit hr
  unfold gluelessRecheck at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr
    · split at hr
      · cases hr
        exact finalizeAnswer_answer_agrees hchain (negativeResponse_answer_agrees _ _ _)
      · dsimp only [] at hr
        split at hr
        · cases hr
        · cases hr
          exact finalizeAnswer_answer_agrees hchain
            (cacheResponse_agrees (fun rr hm =>
              lookupAnswerable_agrees hc _ _ _ _ rr hm) _)

private theorem rcode_eq_of_beq' {a b : Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem acceptResponse_facts' {sent resp₀ resp : Format}
    (h : acceptResponse sent resp₀ = some resp) :
    resp₀ = resp ∧ questionMatches resp.question sent.question = true := by
  unfold acceptResponse at h
  split at h
  · next hcond =>
    cases h
    simp only [Bool.and_eq_true] at hcond
    exact ⟨rfl, hcond.1.1.2⟩
  · cases h

private theorem questionMatches_qnameCI {a b : Array VeriDNS.Spec.Question}
    (h : questionMatches a b = true) :
    ∃ qa qb, a[0]? = some qa ∧ b[0]? = some qb ∧
      nameEqCI qa.qname qb.qname = true := by
  unfold questionMatches at h
  split at h
  · next qa qb ha hb =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨qa, qb, ha, hb, nameEqCI_of_beq h.1.1⟩
  · cases h

theorem strictDenialB_rcode {resp : Format}
    (h : strictDenialB resp = true) : resp.header.rcode = Rcode.nameError := by
  unfold strictDenialB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact rcode_eq_of_beq' h.1.2

theorem cacheAgrees_storeProbeNegative {T : Node ResourceRecord} {c : DnsCache}
    (h : CacheAgrees T c) {sub resp : Format} {now : UInt32}
    (habsent : ∀ qu, sub.question[0]? = some qu → nodeAtName T qu.qname = none) :
    CacheAgrees T (storeProbeNegative c sub resp now) := by
  unfold storeProbeNegative
  split
  · next qu hq =>
    split
    · exact cacheAgrees_storeNegative h (fun _ => habsent qu hq)
        (noRecordOfType_of_absent (habsent qu hq) _)
    · exact h
  · exact h

theorem probeAbsent_of_strictDenial {T : Node ResourceRecord}
    {subQuery₀ resp₀ resp : Format} {rid cid : UInt16}
    (hacc : acceptResponse (withSecrets subQuery₀ rid cid) resp₀ = some resp)
    (hcons : ResponseConsistent T resp)
    (hrc : resp.header.rcode = Rcode.nameError) :
    ∀ qu, subQuery₀.question[0]? = some qu → nodeAtName T qu.qname = none := by
  intro qu hq
  obtain ⟨-, hqm⟩ := acceptResponse_facts' hacc
  obtain ⟨qa, qb, hqa, hqb, hci⟩ := questionMatches_qnameCI hqm
  have hqb' : qb = { qu with qname := VeriDNS.Impl.DomainName.randomizeCase cid qu.qname } := by
    have : (withSecrets subQuery₀ rid cid).question[0]?
        = some { qu with qname := VeriDNS.Impl.DomainName.randomizeCase cid qu.qname } := by
      show ((withRandomId subQuery₀ rid).question.map _)[0]? = _
      rw [show (withRandomId subQuery₀ rid).question = subQuery₀.question from rfl,
        Array.getElem?_map, hq]
      rfl
    rw [this] at hqb
    exact (Option.some.injEq _ _ ▸ hqb).symm
  have hnone : nodeAtName T qa.qname = none :=
    hcons.nameErrorDeserved hrc qa (Array.mem_def.mp (Array.mem_of_getElem? hqa))
  calc nodeAtName T qu.qname
      = nodeAtName T (VeriDNS.Impl.DomainName.randomizeCase cid qu.qname) :=
        (nodeAtName_congrCI T (randomizeCase_nameEqCI cid qu.qname)).symm
    _ = nodeAtName T qb.qname := by rw [hqb']
    _ = nodeAtName T qa.qname := (nodeAtName_congrCI T hci).symm
    _ = none := hnone

theorem ioResumeLoop_sound (T : Node ResourceRecord)
    (hnet : NetworkConsistent T M Sock) (hnetTcp : NetworkConsistentTcp T M Sock) (sbelt : DnsSList) :
    ∀ (depth fuel : Nat)
      (state : State DnsSList DnsCache SlistEntry ResourceRecord)
      (deadline : UInt32) (revealed : Nat),
    StateAgrees T state →
    SatisfiesM (ShimSound T)
      (ioResumeLoop (M := M) (Sock := Sock) sbelt state deadline depth fuel revealed)
  | depth, 0, state, deadline, revealed, hs => by
    rw [ioResumeLoop.eq_def]
    exact SatisfiesM.pure (p := ShimSound T) ⟨(fun _ h => nomatch h), hs.cache⟩
  | depth, fuel' + 1, state, deadline, revealed, hs => by
    rw [ioResumeLoop.eq_def]
    dsimp only []
    refine SatisfiesM.bind (satisfiesM_true _) ?_
    intro t _
    split
    ·
      exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
    · refine SatisfiesM.bind (satisfiesM_true _) ?_
      intro _ _
      split
      ·
        split
        ·
          next nsName _ =>
          split
          ·
            next depth' =>
            refine SatisfiesM.bind (satisfiesM_true _) ?_
            intro _ _

            have hrs := resolve_sound (S := DnsSList) (NS := SlistEntry) (T := T)
              (mkAddressQuery nsName) sbelt 64 state.now hs.cache
            split <;> rename_i h <;> rw [h] at hrs
            ·
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet hnetTcp sbelt depth' fuel' _ _ _ ⟨hs.cache, hs.chain⟩
            ·
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet hnetTcp sbelt depth' fuel' _ _ _ ⟨hs.cache, hs.chain⟩
            ·

              refine SatisfiesM.bind
                (ioResumeLoop_sound T hnet hnetTcp sbelt depth' fuel' _ deadline _ hrs) ?_
              intro y hy
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              split
              ·
                split
                ·
                  split
                  · next hit hre =>
                    exact SatisfiesM.pure
                      ⟨fun f hf => by cases hf; exact gluelessRecheck_sound hs.chain hy.2 hit hre,
                        cacheAgrees_touchKeys _ _ hy.2⟩
                  · exact ioResumeLoop_sound T hnet hnetTcp sbelt depth' fuel' _ _ _
                      ⟨cacheAgrees_touchKeys _ _ hy.2, hs.chain⟩
                ·
                  exact ioResumeLoop_sound T hnet hnetTcp sbelt depth' fuel' _ _ _ ⟨hs.cache, hs.chain⟩
              ·
                exact ioResumeLoop_sound T hnet hnetTcp sbelt depth' fuel' _ _ _ ⟨hs.cache, hs.chain⟩
          ·
            exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
        ·
          exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
      ·
        next entry ipAddr _ =>
        split
        ·
          next subQuery₀ _ =>
          refine SatisfiesM.bind (satisfiesM_true _) ?_
          intro _ _
          refine SatisfiesM.bind (satisfiesM_true _) ?_
          intro rid _
          refine SatisfiesM.bind (satisfiesM_true _) ?_
          intro cid _
          split
          ·
            refine SatisfiesM.bind (satisfiesM_true _) ?_
            intro _ _
            rw [pure_bind]
            exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _ ⟨hs.cache, hs.chain⟩
          refine SatisfiesM.bind (hnet _ _) ?_
          intro upstreamResp hup
          split
          ·
            next resp₀ =>
            split
            ·
              next resp hacc =>
              have hconsU : ResponseConsistent T resp :=
                hup resp₀ resp rfl hacc
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              refine SatisfiesM.bind
                (p := fun ro => ∀ r', ro = some r' →
                  ResponseConsistent T r'
                    ∧ ∃ src, acceptResponse (withSecrets subQuery₀ rid cid) src = some r')
                ?tcguard ?_
              case tcguard =>
                split
                ·
                  refine SatisfiesM.bind (satisfiesM_true _) ?_
                  intro _ _
                  refine SatisfiesM.bind (hnetTcp _ _) ?_
                  intro tcpRo htcp
                  cases tcpRo with
                  | none => exact SatisfiesM.pure (fun r' h => nomatch h)
                  | some tcpResp =>
                    dsimp only []
                    split
                    · exact SatisfiesM.pure (m := M) (fun r' h => nomatch h)
                    · next tcpRespA hacctcp =>
                      refine SatisfiesM.pure (m := M) ?_
                      intro r' hr'
                      split at hr'
                      · exact absurd hr' (by simp)
                      · cases hr'
                        exact ⟨htcp tcpResp tcpRespA rfl hacctcp, tcpResp, hacctcp⟩
                ·
                  exact SatisfiesM.pure (fun r' hr' => by cases hr'; exact ⟨hconsU, resp₀, hacc⟩)
              intro ro hro
              cases ro with
              | none =>
                dsimp only []
                refine SatisfiesM.bind (satisfiesM_true _) ?_
                intro _ _
                exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
                  ⟨hs.cache, hs.chain⟩
              | some resp =>
                obtain ⟨hcons, srcResp, hacc⟩ := hro resp rfl
                dsimp only []
                split
                ·
                  refine SatisfiesM.bind (satisfiesM_true _) ?_
                  intro _ _
                  exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
                    ⟨hs.cache, hs.chain⟩
                ·
                  split
                  · -- 055 (RFC 6891 §6.2.2): FORMERR to an OPT-bearing sub-query — the
                    -- loop retries without EDNS (noEdns flag); plain recursion.
                    refine SatisfiesM.bind (satisfiesM_true _) ?_
                    intro _ _
                    exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
                      ⟨hs.cache, hs.chain⟩
                  ·
                    split
                    · -- 051/064: the probe-NXDOMAIN arm now recurses (full-qname
                      -- fallback, RFC 9156 §2.3) instead of delivering.
                      refine SatisfiesM.bind (satisfiesM_true _) ?_
                      intro _ _
                      exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
                        ⟨hs.cache, hs.chain⟩
                    ·
                      split
                      ·
                        refine SatisfiesM.bind (satisfiesM_true _) ?_
                        intro _ _
                        exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
                          ⟨hs.cache, hs.chain⟩
                      ·
                        have ha := afterResume_sound (T := T) (entryName := entry.name)
                          (state := { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } })
                          ⟨hs.cache, hs.chain⟩ hcons
                        split <;> rename_i h <;> rw [h] at ha
                        ·
                          exact SatisfiesM.pure ⟨ha.1, ha.2⟩
                        ·
                          exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _ ha
            ·
              refine SatisfiesM.bind (satisfiesM_true _) ?_
              intro _ _
              exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
                ⟨hs.cache, hs.chain⟩
          ·
            exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel' _ _ _
              ⟨hs.cache, hs.chain⟩
        ·
          exact SatisfiesM.pure ⟨(fun _ h => nomatch h), hs.cache⟩
  termination_by depth fuel => (depth, fuel)
  decreasing_by all_goals
    (first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega))

theorem resolveWithIO_sound (T : Node ResourceRecord)
    (hnet : NetworkConsistent T M Sock) (hnetTcp : NetworkConsistentTcp T M Sock)
    (query : Format) (sbelt : DnsSList)
    {cache : DnsCache} (hc : CacheAgrees T cache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) :
    SatisfiesM (ShimSound T)
      (resolveWithIO (M := M) (Sock := Sock) query sbelt cache now
        fuel depth budget) := by
  unfold resolveWithIO
  have h := resolve_sound (S := DnsSList) (NS := SlistEntry) (T := T)
    query sbelt 64 now hc
  split
  · next resp stF hdone =>
    rw [hdone] at h
    exact SatisfiesM.pure ⟨(fun f hf => by cases hf; exact h.1), hc⟩
  · next st hpause =>
    rw [hpause] at h
    exact ioResumeLoop_sound T hnet hnetTcp sbelt depth fuel st (now + budget) (seedRevealed st) h
  · exact SatisfiesM.pure ⟨(fun _ hf => nomatch hf), hc⟩

end ShimSoundness

end VeriDNS.Proof.NameTree
