import VeriDNS.Spec.NetworkModel
import VeriDNS.Spec.NetworkTraces
import VeriDNS.Spec.AnswerAuthenticity
import VeriDNS.RFC.Check

namespace VeriDNS.Spec.Net

open VeriDNS.Spec (RRType RRClass)

def Response.isReferral (r : Response) : Bool :=
  r.answer.isEmpty && r.aa == false && r.rcode == RCode.noError
    && r.authority.any (fun rr => rr.rdata.rtype == RRType.ns)
    && !r.authority.any (fun rr => rr.rdata.rtype == RRType.soa)
rfc_proves VeriDNS.Spec.Net.Response.isReferral [1034][1319:1330]

theorem isReferral_false_of_answer_ne_nil (r : Response) (h : r.answer ≠ []) :
    r.isReferral = false := by
  unfold Response.isReferral
  cases hr : r.answer with
  | nil => exact absurd hr h
  | cons a as => simp [hr]

theorem isReferral_false_of_aa (r : Response) (h : r.aa = true) :
    r.isReferral = false := by
  unfold Response.isReferral
  simp [h]

theorem isReferral_false_of_authority_nil (r : Response) (h : r.authority = []) :
    r.isReferral = false := by
  unfold Response.isReferral
  simp [h]

theorem isReferral_of_shape {r : Response}
    (hempty : r.answer = []) (haa : r.aa = false) (hrc : r.rcode = RCode.noError)
    (hns : r.authority.any (fun rr => rr.rdata.rtype == RRType.ns) = true)
    (hnosoa : r.authority.any (fun rr => rr.rdata.rtype == RRType.soa) = false) :
    r.isReferral = true := by
  unfold Response.isReferral
  rw [hempty, haa, hrc, hns, hnosoa]
  decide

def referredServers (r : Response) : List Name :=
  r.authority.filterMap (fun rr => match rr.rdata with | .ns h => some h | _ => none)
rfc_proves VeriDNS.Spec.Net.referredServers [1034][1319:1330]

def Response.inBailiwick (r : Response) (qname : Name) : Bool :=
  r.authority.all (fun rr => !(rr.rdata.rtype == RRType.ns) || isAncestor rr.owner qname)
rfc_proves VeriDNS.Spec.Net.Response.inBailiwick [1034][1319:1330]

theorem inBailiwick_iff (r : Response) (qname : Name) :
    r.inBailiwick qname = true
      ↔ ∀ rr ∈ r.authority, (rr.rdata.rtype == RRType.ns) = true → isAncestor rr.owner qname = true := by
  simp only [Response.inBailiwick, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  constructor
  · intro h rr hrr hns; rcases h rr hrr with h' | h'
    · rw [hns] at h'; exact absurd h' (by decide)
    · exact h'
  · intro h rr hrr
    cases hns : (rr.rdata.rtype == RRType.ns) with
    | false => exact Or.inl rfl
    | true => exact Or.inr (h rr hrr hns)

theorem cachedDelegation_inBailiwick (s : Server) (now : Time) (qname : Name) (qcls : RRClass)
    {ref : Response} (hauth : ref.authority = cachedDelegation s now qname qcls) :
    ref.inBailiwick qname = true := by
  rw [inBailiwick_iff]
  intro rr hrr _
  rw [hauth] at hrr
  unfold cachedDelegation at hrr
  have hp := (List.mem_filter.mp ((List.mem_filter.mp hrr).1)).2
  cases hc : isAncestor rr.owner qname with
  | true => rfl
  | false => rw [hc] at hp; simp at hp

theorem referral_classified :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["BRL","MIL"], .rr .a, .«in», false⟩ tr resp
      ∧ resp.isReferral = true := by
  refine ⟨_, _, ServerAnswers.referral _ rootZone _ rfl rfl rfl, by decide⟩
rfc_proves VeriDNS.Spec.Net.referral_classified [1034][1319:1330]

theorem referralCacheAnswer_classified :
    ∃ tr resp, ServerReplies referCacheServer 50 ⟨N ["X","SUB"], .rr .a, .«in», false⟩ tr resp
      ∧ resp.isReferral = false := by
  refine ⟨_, _, ServerAnswers.referralCacheAnswer _ _ _ [ rr ["X","SUB"] 50 (.a ⟨5, 5, 5, 5⟩) ]
    rfl rfl rfl (List.cons_ne_nil _ _), by decide⟩
rfc_proves VeriDNS.Spec.Net.referralCacheAnswer_classified [1034][1354:1364]

theorem referral_in_bailiwick :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["BRL","MIL"], .rr .a, .«in», false⟩ tr resp
      ∧ resp.inBailiwick (N ["BRL","MIL"]) = true := by
  refine ⟨_, _, ServerAnswers.referral _ rootZone _ rfl rfl rfl, by decide⟩
rfc_proves VeriDNS.Spec.Net.referral_in_bailiwick [1034][1319:1330]

def allUp : NetState := { status := fun _ => Status.up }

structure Datagram where
  id : Nat
  srcAddr : String
  dstAddr : String
  srcPort : Nat
  dstPort : Nat

  rd : Bool := false
  qname : Name
  qtype : QType

  qclass : RRClass := RRClass.in

  udpPayload : Nat := 512
  msg : Response := default
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Datagram [1035][1404:1420]

def udpMax : Nat := 512
rfc_proves VeriDNS.Spec.Net.udpMax [1035][1756:1766]

def overUdp (sizeOctets : Nat) : Bool := Nat.blt udpMax sizeOctets
rfc_proves VeriDNS.Spec.Net.overUdp [1035][1756:1766]

def truncateUdp (sizeOctets : Nat) (r : Response) : Response × Bool :=
  if overUdp sizeOctets then
    ({ r with answer := [], authority := [], additional := [], tc := true }, true)
  else (r, false)
rfc_proves VeriDNS.Spec.Net.truncateUdp [1035][1414:1420]

theorem big_response_truncated (sz : Nat) (r : Response) (h : overUdp sz = true) :
    (truncateUdp sz r).2 = true ∧ (truncateUdp sz r).1.tc = true := by
  simp [truncateUdp, h]
rfc_proves VeriDNS.Spec.Net.big_response_truncated [1035][1414:1420]

def accepts (out reply : Datagram) : Bool :=
  (out.id == reply.id)
    && (out.srcAddr == reply.dstAddr) && (out.dstAddr == reply.srcAddr)
    && (out.srcPort == reply.dstPort) && (out.dstPort == reply.srcPort)
    && nameEqCS out.qname reply.qname && (out.qtype == reply.qtype)
    && (out.qclass == reply.qclass)
rfc_proves VeriDNS.Spec.Net.accepts [5452][258:278]

inductive Transit (reach : String → Bool) : String → String → Datagram → Option Datagram → Prop where
  | deliver (a b : String) (d : Datagram) :
      reach a = true → reach b = true → Transit reach a b d (some d)
  | lost (a b : String) (d : Datagram) :
      Transit reach a b d none
  | partitioned (a b : String) (d : Datagram) :
      reach b = false → Transit reach a b d none
rfc_proves VeriDNS.Spec.Net.Transit [5452][375:382]

def queryDatagram (id : Nat) (srcAddr dstAddr : String) (srcPort : Nat) (ednsBuf : Nat) (q : Query) : Datagram :=
  { id := id, srcAddr := srcAddr, dstAddr := dstAddr, srcPort := srcPort, dstPort := 53,
    rd := false, qname := q.qname, qtype := q.qtype, qclass := q.qclass, udpPayload := ednsBuf }
rfc_proves VeriDNS.Spec.Net.queryDatagram [5452][258:278]

theorem queryDatagram_clears_rd (id : Nat) (srcAddr dstAddr : String) (srcPort ednsBuf : Nat)
    (q : Query) : (queryDatagram id srcAddr dstAddr srcPort ednsBuf q).rd = false := rfl
rfc_proves VeriDNS.Spec.Net.queryDatagram_clears_rd [1034][1212:1248]

def replyDatagram (out : Datagram) (resp : Response) : Datagram :=
  { out with srcAddr := out.dstAddr, dstAddr := out.srcAddr,
             srcPort := out.dstPort, dstPort := out.srcPort, msg := resp }
rfc_proves VeriDNS.Spec.Net.replyDatagram [5452][258:278]

theorem accepts_reply (id : Nat) (srcAddr dstAddr : String) (srcPort : Nat) (ednsBuf : Nat) (q : Query)
    (resp : Response) :
    accepts (queryDatagram id srcAddr dstAddr srcPort ednsBuf q)
            (replyDatagram (queryDatagram id srcAddr dstAddr srcPort ednsBuf q) resp) = true := by
  have hq : (q.qtype == q.qtype) = true := by
    cases q.qtype with
    | star => rfl
    | rr t => cases t <;> first
        | rfl
        | (rename_i c; show (c == c) = true; exact beq_self_eq_true c)
  have hcl : (q.qclass == q.qclass) = true := by cases q.qclass <;> rfl
  simp [accepts, queryDatagram, replyDatagram, nameEqCS_refl, hq, hcl]

theorem accepts_requires_match (out reply : Datagram) (h : accepts out reply = true) :
    (out.id == reply.id) = true ∧ (out.dstAddr == reply.srcAddr) = true
      ∧ (out.srcPort == reply.dstPort) = true
      ∧ (out.dstPort == reply.srcPort) = true ∧ nameEq out.qname reply.qname = true
      ∧ (out.qtype == reply.qtype) = true ∧ (out.qclass == reply.qclass) = true := by
  simp only [accepts, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2,
    nameEq_of_nameEqCS h.1.1.2, h.1.2, h.2⟩

theorem accepts_requires_qname_cs (out reply : Datagram) (h : accepts out reply = true) :
    nameEqCS out.qname reply.qname = true := by
  simp only [accepts, Bool.and_eq_true] at h
  exact h.1.1.2
rfc_proves VeriDNS.Spec.Net.accepts_requires_match [5452][258:278]

inductive OnWire (out : Datagram) (honest : Response) : Datagram → Prop where
  | fromServer : OnWire out honest (replyDatagram out honest)
  | offPath (d : Datagram)
      (hblind : (out.id == d.id) = false ∨ (out.srcPort == d.dstPort) = false
        ∨ nameEqCS out.qname d.qname = false) :
      OnWire out honest d
rfc_proves VeriDNS.Spec.Net.OnWire [5452][258:278]

def labelsWire (labels : Name) : Nat := (labels.map (fun l => 1 + l.size)).sum
rfc_proves VeriDNS.Spec.Net.labelsWire [1035][541:546]

def nameWire (n : Name) : Nat := labelsWire n + 1
rfc_proves VeriDNS.Spec.Net.nameWire [1035][541:546]

def ptrMax : Nat := 16383
rfc_proves VeriDNS.Spec.Net.ptrMax [1035][1634:1738]

def nameSuffixesAt (off : Nat) : Name → List (Name × Nat)
  | [] => []
  | l :: rest => (l :: rest, off) :: nameSuffixesAt (off + 1 + l.size) rest

def nameWireC (seen : List (Name × Nat)) : Name → Nat
  | [] => 1
  | l :: rest =>
    if seen.any (fun p => p.1 == (l :: rest) && Nat.ble p.2 ptrMax) then 2
    else (1 + l.size) + nameWireC seen rest
rfc_proves VeriDNS.Spec.Net.nameWireC [1035][1634:1738]

def emitName (st : Nat × List (Name × Nat)) (n : Name) : Nat × List (Name × Nat) :=
  (st.1 + nameWireC st.2 n, nameSuffixesAt st.1 n ++ st.2)

def rdataNames : RData → List Name
  | .a _ => []
  | .ns h => [h]
  | .cname t => [t]
  | .soa m r .. => [m, r]
  | .mx _ e => [e]
  | .hinfo _ _ => []
  | .ptr t => [t]
  | .generic _ _ => []

def rdataFixed : RData → Nat
  | .a _ => 4
  | .ns _ => 0
  | .cname _ => 0
  | .soa .. => 20
  | .mx _ _ => 2
  | .hinfo c o => c.length + o.length + 2
  | .ptr _ => 0
  | .generic _ d => d.size
rfc_proves VeriDNS.Spec.Net.rdataFixed [1035][1572:1632]

def emitRData (st : Nat × List (Name × Nat)) : RData → Nat × List (Name × Nat)
  | .a _ => (st.1 + 4, st.2)
  | .ns h => emitName st h
  | .cname t => emitName st t
  | .soa m r _ _ _ _ _ =>
    let st1 := emitName st m
    let st2 := emitName st1 r
    (st2.1 + 20, st2.2)
  | .mx _ e => emitName (st.1 + 2, st.2) e
  | .hinfo c o => (st.1 + (c.length + 1) + (o.length + 1), st.2)
  | .ptr t => emitName st t
  | .generic _ d => (st.1 + d.size, st.2)

def emitRR (st : Nat × List (Name × Nat)) (r : RR) : Nat × List (Name × Nat) :=
  let st1 := emitName st r.owner
  emitRData (st1.1 + 10, st1.2) r.rdata

def msgHdrQ (q : Query) : Nat × List (Name × Nat) :=
  let s := emitName (12, []) q.qname
  (s.1 + 4, s.2)

def messageWire (q : Query) (resp : Response) : Nat :=
  let stA  := resp.answer.foldl emitRR (msgHdrQ q)
  let stAu := resp.authority.foldl emitRR stA
  (resp.additional.foldl emitRR stAu).1
rfc_proves VeriDNS.Spec.Net.messageWire [1035][1634:1738]

theorem nameWireC_nil (n : Name) : nameWireC [] n = nameWire n := by
  induction n with
  | nil => rfl
  | cons l rest ih =>
    have hc : (([] : List (Name × Nat)).any (fun p => p.1 == (l :: rest) && Nat.ble p.2 ptrMax))
        = false := rfl
    simp only [nameWireC, hc, Bool.false_eq_true, if_false, ih, nameWire, labelsWire,
      List.map_cons, List.sum_cons]
    omega

theorem nameWire_pos (n : Name) : 1 ≤ nameWire n := by simp only [nameWire]; omega

theorem nameWireC_le_nameWire (seen : List (Name × Nat)) (n : Name) :
    nameWireC seen n ≤ nameWire n := by
  induction n with
  | nil => simp only [nameWireC, nameWire, labelsWire, List.map_nil, List.sum_nil]; omega
  | cons l rest ih =>
    have hrest : 1 ≤ nameWire rest := nameWire_pos rest
    have hnw : nameWire (l :: rest) = (1 + l.size) + nameWire rest := by
      simp only [nameWire, labelsWire, List.map_cons, List.sum_cons]; omega
    simp only [nameWireC]
    split
    · rw [hnw]; omega
    · rw [hnw]; omega

theorem nameWireC_ptr_ceiling :
    nameWireC [(N ["WIDE","EXAMPLE","ARPA"], ptrMax)] (N ["WIDE","EXAMPLE","ARPA"]) = 2
  ∧ nameWireC [(N ["WIDE","EXAMPLE","ARPA"], ptrMax + 1)] (N ["WIDE","EXAMPLE","ARPA"])
      = nameWire (N ["WIDE","EXAMPLE","ARPA"]) := by
  refine ⟨by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.nameWireC_ptr_ceiling [1035][1634:1738]

theorem nameWireC_pos (seen : List (Name × Nat)) (n : Name) : 1 ≤ nameWireC seen n := by
  cases n with
  | nil => exact Nat.le_refl 1
  | cons l rest =>
      unfold nameWireC
      split
      · exact Nat.le_succ 1
      · omega

theorem emitName_lb (st : Nat × List (Name × Nat)) (n : Name) :
    st.1 + 1 ≤ (emitName st n).1 :=
  Nat.add_le_add_left (nameWireC_pos st.2 n) st.1

theorem foldl_emitName_mono (names : List Name) (st : Nat × List (Name × Nat)) :
    st.1 ≤ (names.foldl emitName st).1 := by
  induction names generalizing st with
  | nil => exact Nat.le_refl _
  | cons n ns ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (by have := emitName_lb st n; omega) (ih (emitName st n))

theorem emitRData_lb (st : Nat × List (Name × Nat)) (rd : RData) :
    st.1 + rdataFixed rd ≤ (emitRData st rd).1 := by
  cases rd with
  | a _ => simp only [emitRData, rdataFixed]; omega
  | ns h => simp only [emitRData, emitName, rdataFixed]; have := nameWireC_pos st.2 h; omega
  | cname t => simp only [emitRData, emitName, rdataFixed]; have := nameWireC_pos st.2 t; omega
  | soa m r _ _ _ _ _ =>
      simp only [emitRData, emitName, rdataFixed]
      have h1 := nameWireC_pos st.2 m
      have h2 := nameWireC_pos (nameSuffixesAt st.1 m ++ st.2) r
      omega
  | mx _ e => simp only [emitRData, emitName, rdataFixed]; have := nameWireC_pos st.2 e; omega
  | hinfo c o => simp only [emitRData, rdataFixed]; omega
  | ptr t => simp only [emitRData, emitName, rdataFixed]; have := nameWireC_pos st.2 t; omega
  | generic t d => simp only [emitRData, rdataFixed]; omega

theorem emitRR_lb (st : Nat × List (Name × Nat)) (r : RR) :
    st.1 + 11 + rdataFixed r.rdata ≤ (emitRR st r).1 := by
  have h1 := emitName_lb st r.owner
  have h2 := emitRData_lb ((emitName st r.owner).1 + 10, (emitName st r.owner).2) r.rdata
  simp only [emitRR]
  omega

theorem foldl_emitRR_lb (xs : List RR) (st : Nat × List (Name × Nat)) :
    st.1 + (xs.map (fun r => 11 + rdataFixed r.rdata)).sum ≤ (xs.foldl emitRR st).1 := by
  induction xs generalizing st with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have h := emitRR_lb st r
      have ih' := ih (emitRR st r)
      omega

def messageFloor (q : Query) (resp : Response) : Nat :=
  17 + ((resp.answer ++ resp.authority ++ resp.additional).map
          (fun r => 11 + rdataFixed r.rdata)).sum
rfc_proves VeriDNS.Spec.Net.messageFloor [1035][1634:1738]

theorem messageWire_lb (q : Query) (resp : Response) :
    messageFloor q resp ≤ messageWire q resp := by
  have hmw : messageWire q resp
      = (resp.additional.foldl emitRR
          (resp.authority.foldl emitRR (resp.answer.foldl emitRR (msgHdrQ q)))).1 := rfl
  have hH : 17 ≤ (msgHdrQ q).1 := by
    have := emitName_lb (12, ([] : List (Name × Nat))) q.qname
    simp only [msgHdrQ]; omega
  have hA := foldl_emitRR_lb resp.answer (msgHdrQ q)
  have hAu := foldl_emitRR_lb resp.authority (resp.answer.foldl emitRR (msgHdrQ q))
  have hAd := foldl_emitRR_lb resp.additional
    (resp.authority.foldl emitRR (resp.answer.foldl emitRR (msgHdrQ q)))
  rw [hmw]
  simp only [messageFloor, List.map_append, List.sum_append]
  omega
rfc_proves VeriDNS.Spec.Net.messageWire_lb [1035][1634:1738]

def packFit (budget : Nat) (st : Nat × List (Name × Nat)) : List RR → List RR
  | [] => []
  | r :: rs =>
    let st' := emitRR st r
    if Nat.ble st'.1 budget then r :: packFit budget st' rs else []
rfc_proves VeriDNS.Spec.Net.packFit [1035][1414:1420]

def truncateToUdp (q : Query) (resp : Response) : Response × Bool :=
  if overUdp (messageWire q resp) then
    ({ resp with answer := packFit udpMax (msgHdrQ q) resp.answer,
                 authority := [], additional := [], tc := true }, true)
  else (resp, false)
rfc_proves VeriDNS.Spec.Net.truncateToUdp [1035][1414:1420]

theorem big_message_truncated (q : Query) (resp : Response)
    (h : overUdp (messageWire q resp) = true) :
    (truncateToUdp q resp).2 = true ∧ (truncateToUdp q resp).1.tc = true := by
  simp [truncateToUdp, h]
rfc_proves VeriDNS.Spec.Net.big_message_truncated [1035][1414:1420]

theorem packFit_fold_le (budget : Nat) :
    ∀ (xs : List RR) (st : Nat × List (Name × Nat)), st.1 ≤ budget →
      ((packFit budget st xs).foldl emitRR st).1 ≤ budget
  | [], st, h => h
  | r :: rs, st, h => by
      simp only [packFit]
      split
      · rename_i hb
        have hst' : (emitRR st r).1 ≤ budget := Nat.le_of_ble_eq_true hb
        simpa [List.foldl_cons] using packFit_fold_le budget rs (emitRR st r) hst'
      · simpa using h

theorem messageWire_truncated (q : Query) (resp : Response) :
    messageWire q { resp with answer := packFit udpMax (msgHdrQ q) resp.answer,
                              authority := [], additional := [], tc := true }
      = ((packFit udpMax (msgHdrQ q) resp.answer).foldl emitRR (msgHdrQ q)).1 := rfl

theorem truncateToUdp_fits (q : Query) (resp : Response) (hq : (msgHdrQ q).1 ≤ udpMax) :
    messageWire q (truncateToUdp q resp).1 ≤ udpMax := by
  unfold truncateToUdp
  split
  · rw [messageWire_truncated]
    exact packFit_fold_le udpMax resp.answer (msgHdrQ q) hq
  · rename_i h
    have : ¬ udpMax < messageWire q resp := by simpa [overUdp, Nat.blt_eq] using h
    exact Nat.le_of_not_lt this

def negotiatedUdp (advertised : Nat) : Nat := max udpMax advertised
rfc_proves VeriDNS.Spec.Net.negotiatedUdp [1035][1756:1766]

theorem negotiatedUdp_floor (a : Nat) : udpMax ≤ negotiatedUdp a := Nat.le_max_left _ _

theorem negotiatedUdp_eq_of_large {a : Nat} (h : udpMax ≤ a) : negotiatedUdp a = a := by
  simp only [negotiatedUdp]; omega

theorem negotiatedUdp_default : negotiatedUdp udpMax = udpMax := by simp only [negotiatedUdp]; omega

def Datagram.cap (d : Datagram) : Nat := negotiatedUdp d.udpPayload
rfc_proves VeriDNS.Spec.Net.Datagram.cap [1035][1756:1766]

theorem queryDatagram_cap (id : Nat) (srcAddr dstAddr : String) (srcPort ednsBuf : Nat) (q : Query) :
    (queryDatagram id srcAddr dstAddr srcPort ednsBuf q).cap = negotiatedUdp ednsBuf := by
  simp only [Datagram.cap, queryDatagram]

def truncateToCap (cap : Nat) (q : Query) (resp : Response) : Response × Bool :=
  if Nat.blt cap (messageWire q resp) then
    ({ resp with answer := packFit cap (msgHdrQ q) resp.answer,
                 authority := [], additional := [], tc := true }, true)
  else (resp, false)
rfc_proves VeriDNS.Spec.Net.truncateToCap [1035][1414:1420]

theorem truncateToUdp_eq_cap (q : Query) (resp : Response) :
    truncateToUdp q resp = truncateToCap udpMax q resp := rfl

theorem messageWire_packed (cap : Nat) (q : Query) (resp : Response) :
    messageWire q { resp with answer := packFit cap (msgHdrQ q) resp.answer,
                              authority := [], additional := [], tc := true }
      = ((packFit cap (msgHdrQ q) resp.answer).foldl emitRR (msgHdrQ q)).1 := rfl

theorem truncateToCap_fits (cap : Nat) (q : Query) (resp : Response) (hq : (msgHdrQ q).1 ≤ cap) :
    messageWire q (truncateToCap cap q resp).1 ≤ cap := by
  unfold truncateToCap
  split
  · rw [messageWire_packed]
    exact packFit_fold_le cap resp.answer (msgHdrQ q) hq
  · rename_i h
    have : ¬ cap < messageWire q resp := by simpa [Nat.blt_eq] using h
    exact Nat.le_of_not_lt this

inductive Cred where
  | glue
  | authority
  | authoritative
  | additional
  deriving BEq, DecidableEq, Inhabited
rfc_proves VeriDNS.Spec.Net.Cred [2181][343:383]

def Cred.rank : Cred → Nat
  | .additional => 0
  | .glue => 1
  | .authority => 2
  | .authoritative => 3
rfc_proves VeriDNS.Spec.Net.Cred.rank [2181][343:383]

def Cred.usable : Cred → Bool
  | .additional => false
  | _ => true
rfc_proves VeriDNS.Spec.Net.Cred.usable [2181][343:383]

structure CacheRR where
  rr : RR
  insertedAt : Time
  cred : Cred
  deriving Inhabited, DecidableEq
rfc_proves VeriDNS.Spec.Net.CacheRR [2181][343:383]

structure NegRR where
  qname : Name
  qtype : Option QType
  insertedAt : Time
  ttl : Nat
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.NegRR [2308][464:471]

structure Cache where
  pos : List CacheRR
  neg : List NegRR
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Cache [2308][464:471]

def Cache.empty : Cache := { pos := [], neg := [] }

def CacheRR.fresh (e : CacheRR) (now : Time) : Bool := Nat.blt now (e.insertedAt + e.rr.ttl)
rfc_proves VeriDNS.Spec.Net.CacheRR.fresh [1035][1602:1614]

def NegRR.fresh (e : NegRR) (now : Time) : Bool := Nat.blt now (e.insertedAt + e.ttl)
rfc_proves VeriDNS.Spec.Net.NegRR.fresh [2308][464:471]

def CacheRR.sameKey (e : CacheRR) (r : RR) : Bool :=
  nameEq e.rr.owner r.owner && (e.rr.rtype == r.rtype) && (e.rr.cls == r.cls)
rfc_proves VeriDNS.Spec.Net.CacheRR.sameKey [2181][343:383]

def Cache.matching (c : Cache) (now : Time) (q : Query) : List CacheRR :=
  c.pos.filter (fun e => e.fresh now && nameEq e.rr.owner q.qname
                          && q.qtype.covers e.rr.rtype && (e.rr.cls == q.qclass))
rfc_proves VeriDNS.Spec.Net.Cache.matching [1035][1602:1614]

def Cache.served (c : Cache) (now : Time) (q : Query) : List CacheRR :=
  (c.matching now q).filter (fun e => e.cred.usable && (c.matching now q).all
    (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))
rfc_proves VeriDNS.Spec.Net.Cache.served [2181][343:383]

def Cache.hit (c : Cache) (now : Time) (q : Query) : List RR :=
  (c.served now q).map (fun e => { e.rr with ttl := e.rr.ttl - (now - e.insertedAt) })
rfc_proves VeriDNS.Spec.Net.Cache.hit [1035][1602:1614]

def dedup : List CacheRR → List CacheRR
  | [] => []
  | a :: as => if a ∈ dedup as then dedup as else a :: dedup as

theorem mem_dedup {a : CacheRR} : ∀ {l : List CacheRR}, a ∈ dedup l ↔ a ∈ l
  | [] => by simp [dedup]
  | b :: as => by
    unfold dedup
    by_cases hb : b ∈ dedup as
    · simp only [hb, if_true, List.mem_cons]
      constructor
      · intro h; exact Or.inr (mem_dedup.mp h)
      · rintro (rfl | h)
        · exact hb
        · exact mem_dedup.mpr h
    · simp only [hb, if_false, List.mem_cons]
      rw [mem_dedup]

theorem nodup_dedup : ∀ (l : List CacheRR), (dedup l).Nodup
  | [] => by simp [dedup]
  | a :: as => by
    unfold dedup
    by_cases ha : a ∈ dedup as
    · simp only [ha, if_true]; exact nodup_dedup as
    · simp only [ha, if_false]
      exact List.nodup_cons.mpr ⟨ha, nodup_dedup as⟩

theorem dedup_perm {l1 l2 : List CacheRR} (h : l1.Perm l2) : (dedup l1).Perm (dedup l2) :=
  List.Subperm.antisymm
    (List.subperm_of_subset (nodup_dedup l1)
      (fun a ha => mem_dedup.mpr (h.mem_iff.mp (mem_dedup.mp ha))))
    (List.subperm_of_subset (nodup_dedup l2)
      (fun a ha => mem_dedup.mpr (h.mem_iff.mpr (mem_dedup.mp ha))))

def Cache.topServed (c : Cache) (now : Time) (q : Query) : List CacheRR :=
  (c.matching now q).filter (fun e => (c.matching now q).all
    (fun e2 => !(e2.sameKey e.rr) || Nat.ble e2.cred.rank e.cred.rank))

theorem Cache.served_eq_topServed_filter (c : Cache) (now : Time) (q : Query) :
    c.served now q = (c.topServed now q).filter (fun e => e.cred.usable) := by
  unfold Cache.served Cache.topServed
  rw [List.filter_filter]

theorem Cache.hit_eq_of_topServed_eq {c c' : Cache} {now : Time} {q : Query}
    (h : c.topServed now q = c'.topServed now q) : c.hit now q = c'.hit now q := by
  unfold Cache.hit
  rw [c.served_eq_topServed_filter, c'.served_eq_topServed_filter, h]

def Cache.cnameAt (c : Cache) (now : Time) (qname : Name) (qcls : RRClass := RRClass.in) : Option RR :=
  (c.pos.filter (fun e => e.fresh now && nameEq e.rr.owner qname
                  && e.rr.rdata.rtype == RRType.cname && e.rr.cls == qcls)).head?.map
    (fun e => { e.rr with ttl := e.rr.ttl - (now - e.insertedAt) })
rfc_proves VeriDNS.Spec.Net.Cache.cnameAt [1034][1311:1318]

def Cache.cnameServed (c : Cache) (now : Time) (qname : Name) (qcls : RRClass := RRClass.in) : List RR :=
  (c.served now ⟨qname, QType.rr RRType.cname, qcls, false⟩).filterMap (fun e =>
    if e.rr.rdata.rtype == RRType.cname then
      some { e.rr with ttl := e.rr.ttl - (now - e.insertedAt) } else none)

def Cache.negHit (c : Cache) (now : Time) (q : Query) : Bool :=
  c.neg.any (fun e => e.fresh now && nameEq e.qname q.qname
              && (match e.qtype with | none => true | some t => t == q.qtype))
rfc_proves VeriDNS.Spec.Net.Cache.negHit [2308][464:471]

def Cache.negHitNx (c : Cache) (now : Time) (q : Query) : Bool :=
  c.neg.any (fun e => e.fresh now && nameEq e.qname q.qname && e.qtype.isNone)
rfc_proves VeriDNS.Spec.Net.Cache.negHitNx [2308][274:292]

def Cache.negResponse (c : Cache) (now : Time) (q : Query) : Response :=
  { aa := false, answer := [], authority := [], additional := [],
    rcode := if c.negHitNx now q then RCode.nameError else RCode.noError }
rfc_proves VeriDNS.Spec.Net.Cache.negResponse [2308][274:471]

def Cache.negTrace (c : Cache) (now : Time) (q : Query) : List Step :=
  [Step.fromCache, if c.negHitNx now q then Step.nameError else Step.noData]
rfc_proves VeriDNS.Spec.Net.Cache.negTrace [2308][274:471]

def Cache.insert (c : Cache) (now : Time) (cred : Cred) (r : RR) : Cache :=
  if cacheable r then { c with pos := ⟨r, now, cred⟩ :: c.pos } else c
rfc_proves VeriDNS.Spec.Net.Cache.insert [1035][1602:1614]

def rrKeyEq (a b : RR) : Bool := nameEq a.owner b.owner && (a.rtype == b.rtype) && (a.cls == b.cls)

def rrGroupMin (rrs : List RR) (r : RR) : Nat :=
  rrs.foldl (fun acc e => if rrKeyEq e r then min acc e.ttl else acc) r.ttl

def normalizeTTL (rrs : List RR) : List RR :=
  rrs.map (fun r => { r with ttl := rrGroupMin rrs r })

def Cache.absorb (c : Cache) (now : Time) (bw : Name) (resp : Response) : Cache :=
  let keep := fun (r : RR) => isAncestor bw r.owner

  let ansCred := if resp.aa then Cred.authoritative else Cred.glue

  let authCred := if resp.aa then Cred.authority else Cred.additional

  let authData := resp.authority.filter (fun r => r.rdata.rtype != RRType.soa)
  let c1 := (normalizeTTL (resp.additional.filter keep)).foldl (fun a r => a.insert now Cred.additional r) c
  let c2 := (normalizeTTL (authData.filter keep)).foldl (fun a r => a.insert now authCred r) c1
  (normalizeTTL (resp.answer.filter keep)).foldl (fun a r => a.insert now ansCred r) c2
rfc_proves VeriDNS.Spec.Net.Cache.absorb [2181][343:383]

def Response.answerOwned (qname : Name) (r : Response) : Response :=
  { r with answer := r.answer.filter (fun rr => nameEq rr.owner qname)
           authority := []
           additional := [] }
rfc_proves VeriDNS.Spec.Net.Response.answerOwned [1034][1862:1864]

@[simp] theorem Response.answerOwned_answer (qname : Name) (r : Response) :
    (r.answerOwned qname).answer = r.answer.filter (fun rr => nameEq rr.owner qname) := rfl
@[simp] theorem Response.answerOwned_authority (qname : Name) (r : Response) :
    (r.answerOwned qname).authority = [] := rfl
@[simp] theorem Response.answerOwned_additional (qname : Name) (r : Response) :
    (r.answerOwned qname).additional = [] := rfl
@[simp] theorem Response.answerOwned_aa (qname : Name) (r : Response) :
    (r.answerOwned qname).aa = r.aa := rfl

theorem Response.answerOwned_congr {qn qn' : Name} (h : nameEq qn qn' = true) (r : Response) :
    r.answerOwned qn = r.answerOwned qn' := by
  unfold Response.answerOwned
  have hf : r.answer.filter (fun rr => nameEq rr.owner qn)
      = r.answer.filter (fun rr => nameEq rr.owner qn') := by
    apply List.filter_congr
    intro rr _
    cases ho : nameEq rr.owner qn with
    | true => exact (nameEq_trans ho h).symm
    | false =>
      cases ho' : nameEq rr.owner qn' with
      | false => rfl
      | true =>
        have hqq : nameEq rr.owner qn = true :=
          nameEq_trans ho' (by rw [nameEq_symm]; exact h)
        rw [hqq] at ho; exact ho.symm
  rw [hf]

/-- Finding 019: the cache slice of a chased-CNAME response — ONLY the
qname-owned CNAME records (the chase link, `cnameRR`'s predicate).  A
same-owner record of any OTHER type riding a CNAME response must not enter
the cache through the chase arm; this mirrors the delivery side, which
prepends only the chased link. -/
def Response.cnameOwned (qname : Name) (r : Response) : Response :=
  { r with answer := r.answer.filter
             (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qname)
           authority := []
           additional := [] }

@[simp] theorem Response.cnameOwned_answer (qname : Name) (r : Response) :
    (r.cnameOwned qname).answer = r.answer.filter
      (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qname) := rfl
@[simp] theorem Response.cnameOwned_authority (qname : Name) (r : Response) :
    (r.cnameOwned qname).authority = [] := rfl
@[simp] theorem Response.cnameOwned_additional (qname : Name) (r : Response) :
    (r.cnameOwned qname).additional = [] := rfl
@[simp] theorem Response.cnameOwned_aa (qname : Name) (r : Response) :
    (r.cnameOwned qname).aa = r.aa := rfl

theorem Response.cnameOwned_congr {qn qn' : Name} (h : nameEq qn qn' = true) (r : Response) :
    r.cnameOwned qn = r.cnameOwned qn' := by
  unfold Response.cnameOwned
  have hf : r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qn)
      = r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qn') := by
    apply List.filter_congr
    intro rr _
    have howner : nameEq rr.owner qn = nameEq rr.owner qn' := by
      cases ho : nameEq rr.owner qn with
      | true => exact (nameEq_trans ho h).symm
      | false =>
        cases ho' : nameEq rr.owner qn' with
        | false => rfl
        | true =>
          have hqq : nameEq rr.owner qn = true :=
            nameEq_trans ho' (by rw [nameEq_symm]; exact h)
          rw [hqq] at ho; exact ho.symm
    rw [howner]
  rw [hf]

theorem absorb_answerOwned_congr (c : Cache) (now : Time) {qa qb : Name}
    (h : nameEq qa qb = true) (r : Response) :
    c.absorb now qa (r.answerOwned qa) = c.absorb now qb (r.answerOwned qb) := by
  have hcoll : ∀ (qn : Name),
      ((r.answerOwned qn).answer).filter (fun x => isAncestor qn x.owner)
        = r.answer.filter (fun rr => nameEq rr.owner qn) := by
    intro qn
    rw [Response.answerOwned_answer]
    exact List.filter_eq_self.mpr (fun x hx => isAncestor_of_nameEq (List.mem_filter.mp hx).2)
  have hfa : r.answer.filter (fun rr => nameEq rr.owner qa)
      = r.answer.filter (fun rr => nameEq rr.owner qb) := by
    have := congrArg (fun (x : Response) => x.answer) (Response.answerOwned_congr h r)
    simpa only [Response.answerOwned_answer] using this
  unfold Cache.absorb
  simp only [Response.answerOwned_answer, Response.answerOwned_authority,
    Response.answerOwned_additional, Response.answerOwned_aa, List.filter_nil,
    show normalizeTTL ([] : List RR) = [] from rfl, List.foldl_nil]
  rw [show (r.answer.filter (fun rr => nameEq rr.owner qa)).filter (fun x => isAncestor qa x.owner)
        = r.answer.filter (fun rr => nameEq rr.owner qa) from hcoll qa,
      show (r.answer.filter (fun rr => nameEq rr.owner qb)).filter (fun x => isAncestor qb x.owner)
        = r.answer.filter (fun rr => nameEq rr.owner qb) from hcoll qb,
      hfa]
  rfl

theorem absorb_cnameOwned_congr (c : Cache) (now : Time) {qa qb : Name}
    (h : nameEq qa qb = true) (r : Response) :
    c.absorb now qa (r.cnameOwned qa) = c.absorb now qb (r.cnameOwned qb) := by
  have hcoll : ∀ (qn : Name),
      ((r.cnameOwned qn).answer).filter (fun x => isAncestor qn x.owner)
        = r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qn) := by
    intro qn
    rw [Response.cnameOwned_answer]
    exact List.filter_eq_self.mpr (fun x hx =>
      isAncestor_of_nameEq (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hx).2).2)
  have hfa : r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qa)
      = r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qb) := by
    have := congrArg (fun (x : Response) => x.answer) (Response.cnameOwned_congr h r)
    simpa only [Response.cnameOwned_answer] using this
  unfold Cache.absorb
  simp only [Response.cnameOwned_answer, Response.cnameOwned_authority,
    Response.cnameOwned_additional, Response.cnameOwned_aa, List.filter_nil,
    show normalizeTTL ([] : List RR) = [] from rfl, List.foldl_nil]
  rw [show (r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qa)).filter
          (fun x => isAncestor qa x.owner)
        = r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qa) from hcoll qa,
      show (r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qb)).filter
          (fun x => isAncestor qb x.owner)
        = r.answer.filter (fun rr => rr.rdata.rtype == RRType.cname && nameEq rr.owner qb) from hcoll qb,
      hfa]
  rfl


theorem mem_normalizeTTL {x : RR} {L : List RR} :
    x ∈ normalizeTTL L ↔ ∃ r ∈ L, x = { r with ttl := rrGroupMin L r } := by
  unfold normalizeTTL; rw [List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩

theorem fields_of_mem_normalizeTTL {x : RR} {L : List RR} (h : x ∈ normalizeTTL L) :
    ∃ r ∈ L, x.owner = r.owner ∧ x.rdata = r.rdata ∧ x.cls = r.cls := by
  obtain ⟨r, hr, rfl⟩ := mem_normalizeTTL.mp h
  exact ⟨r, hr, rfl, rfl, rfl⟩

theorem mem_foldl_insert_pos {e : CacheRR} {now : Time} {cr : Cred} :
    ∀ (ys : List RR) (acc : Cache),
    e ∈ (ys.foldl (fun a r => a.insert now cr r) acc).pos →
    e ∈ acc.pos ∨ e.rr ∈ ys := by
  intro ys
  induction ys with
  | nil => intro acc h; exact Or.inl h
  | cons r rs ih =>
      intro acc h
      rw [List.foldl_cons] at h
      rcases ih _ h with h' | h'
      · unfold Cache.insert at h'
        by_cases hc : cacheable r
        · rw [if_pos hc] at h'
          rcases List.mem_cons.mp h' with rfl | h''
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h''
        · rw [if_neg hc] at h'; exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_foldl_insert_mono {e : CacheRR} {now : Time} {cr : Cred} :
    ∀ (ys : List RR) (acc : Cache), e ∈ acc.pos →
    e ∈ (ys.foldl (fun a r => a.insert now cr r) acc).pos := by
  intro ys
  induction ys with
  | nil => intro acc h; exact h
  | cons r rs ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      unfold Cache.insert
      by_cases hc : cacheable r
      · rw [if_pos hc]; exact List.mem_cons_of_mem _ h
      · rw [if_neg hc]; exact h

theorem absorb_pos_in_bailiwick (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (e : CacheRR) (he : e ∈ (c.absorb now bw resp).pos) :
    e ∈ c.pos ∨ isAncestor bw e.rr.owner = true := by
  have step : ∀ (xs : List RR) (cr : Cred) (acc : Cache),
      e ∈ ((normalizeTTL (xs.filter (fun r => isAncestor bw r.owner))).foldl
            (fun a r => a.insert now cr r) acc).pos →
      e ∈ acc.pos ∨ isAncestor bw e.rr.owner = true := by
    intro xs cr acc h
    rcases mem_foldl_insert_pos _ acc h with h' | h'
    · exact Or.inl h'
    · obtain ⟨r, hr, hown, _, _⟩ := fields_of_mem_normalizeTTL h'
      rw [hown]; exact Or.inr (List.mem_filter.mp hr).2
  unfold Cache.absorb at he
  rcases step _ _ _ he with h2 | h2
  · rcases step _ _ _ h2 with h1 | h1
    · rcases step _ _ _ h1 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0
    · exact Or.inr h1
  · exact Or.inr h2
rfc_proves VeriDNS.Spec.Net.absorb_pos_in_bailiwick [2181][343:383]

theorem absorb_answerOwned_pos_owner (c : Cache) (now : Time) (qn : Name) (resp : Response)
    (e : CacheRR) (he : e ∈ (c.absorb now qn (resp.answerOwned qn)).pos) :
    e ∈ c.pos ∨ nameEq e.rr.owner qn = true := by
  unfold Cache.absorb at he
  simp only [Response.answerOwned_answer, Response.answerOwned_authority,
    Response.answerOwned_additional, List.filter_nil,
    show normalizeTTL ([] : List RR) = [] from rfl, List.foldl_nil] at he
  rcases mem_foldl_insert_pos _ _ he with h' | h'
  · exact Or.inl h'
  · obtain ⟨r, hr, hown, -, -⟩ := fields_of_mem_normalizeTTL h'
    rw [hown]
    exact Or.inr (List.mem_filter.mp (List.mem_filter.mp hr).1).2

theorem absorb_cnameOwned_pos_owner (c : Cache) (now : Time) (qn : Name) (resp : Response)
    (e : CacheRR) (he : e ∈ (c.absorb now qn (resp.cnameOwned qn)).pos) :
    e ∈ c.pos ∨ nameEq e.rr.owner qn = true := by
  unfold Cache.absorb at he
  simp only [Response.cnameOwned_answer, Response.cnameOwned_authority,
    Response.cnameOwned_additional, List.filter_nil,
    show normalizeTTL ([] : List RR) = [] from rfl, List.foldl_nil] at he
  rcases mem_foldl_insert_pos _ _ he with h' | h'
  · exact Or.inl h'
  · obtain ⟨r, hr, hown, -, -⟩ := fields_of_mem_normalizeTTL h'
    rw [hown]
    exact Or.inr
      (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp (List.mem_filter.mp hr).1).2).2

theorem absorb_pos_mono (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (e : CacheRR) (he : e ∈ c.pos) : e ∈ (c.absorb now bw resp).pos := by
  unfold Cache.absorb
  exact mem_foldl_insert_mono _ _ (mem_foldl_insert_mono _ _ (mem_foldl_insert_mono _ _ he))

theorem absorb_topServed_in_bailiwick (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (now' : Time) (q' : Query) (e : CacheRR)
    (he : e ∈ (c.absorb now bw resp).topServed now' q') :
    e ∈ c.topServed now' q' ∨ isAncestor bw e.rr.owner = true := by
  unfold Cache.topServed at he
  rw [List.mem_filter] at he
  obtain ⟨hmem, hmax⟩ := he
  have hpos : e ∈ (c.absorb now bw resp).pos := (List.mem_filter.mp hmem).1
  rcases absorb_pos_in_bailiwick c now bw resp e hpos with hc | hbw
  · left
    have hkey := (List.mem_filter.mp hmem).2
    have hcm : e ∈ c.matching now' q' := by
      unfold Cache.matching; rw [List.mem_filter]; exact ⟨hc, hkey⟩
    have hsub : ∀ x ∈ c.matching now' q', x ∈ (c.absorb now bw resp).matching now' q' := by
      intro x hx
      have hx' := List.mem_filter.mp hx
      unfold Cache.matching; rw [List.mem_filter]
      exact ⟨absorb_pos_mono c now bw resp x hx'.1, hx'.2⟩
    unfold Cache.topServed
    rw [List.mem_filter]
    refine ⟨hcm, ?_⟩
    simp only [List.all_eq_true] at hmax ⊢
    intro x hx
    exact hmax x (hsub x hx)
  · exact Or.inr hbw

theorem absorb_answerOwned_topServed_owner (c : Cache) (now : Time) (qn : Name) (resp : Response)
    (now' : Time) (q' : Query) (e : CacheRR)
    (he : e ∈ (c.absorb now qn (resp.answerOwned qn)).topServed now' q') :
    e ∈ c.topServed now' q' ∨ nameEq e.rr.owner qn = true := by
  unfold Cache.topServed at he
  rw [List.mem_filter] at he
  obtain ⟨hmem, hmax⟩ := he
  have hpos : e ∈ (c.absorb now qn (resp.answerOwned qn)).pos := (List.mem_filter.mp hmem).1
  rcases absorb_answerOwned_pos_owner c now qn resp e hpos with hc | hown
  · left
    have hkey := (List.mem_filter.mp hmem).2
    have hcm : e ∈ c.matching now' q' := by
      unfold Cache.matching; rw [List.mem_filter]; exact ⟨hc, hkey⟩
    have hsub : ∀ x ∈ c.matching now' q',
        x ∈ ((c.absorb now qn (resp.answerOwned qn)).matching now' q') := by
      intro x hx
      have hx' := List.mem_filter.mp hx
      unfold Cache.matching; rw [List.mem_filter]
      exact ⟨absorb_pos_mono c now qn (resp.answerOwned qn) x hx'.1, hx'.2⟩
    unfold Cache.topServed
    rw [List.mem_filter]
    refine ⟨hcm, ?_⟩
    simp only [List.all_eq_true] at hmax ⊢
    intro x hx
    exact hmax x (hsub x hx)
  · exact Or.inr hown

theorem absorb_cnameOwned_topServed_owner (c : Cache) (now : Time) (qn : Name) (resp : Response)
    (now' : Time) (q' : Query) (e : CacheRR)
    (he : e ∈ (c.absorb now qn (resp.cnameOwned qn)).topServed now' q') :
    e ∈ c.topServed now' q' ∨ nameEq e.rr.owner qn = true := by
  unfold Cache.topServed at he
  rw [List.mem_filter] at he
  obtain ⟨hmem, hmax⟩ := he
  have hpos : e ∈ (c.absorb now qn (resp.cnameOwned qn)).pos := (List.mem_filter.mp hmem).1
  rcases absorb_cnameOwned_pos_owner c now qn resp e hpos with hc | hown
  · left
    have hkey := (List.mem_filter.mp hmem).2
    have hcm : e ∈ c.matching now' q' := by
      unfold Cache.matching; rw [List.mem_filter]; exact ⟨hc, hkey⟩
    have hsub : ∀ x ∈ c.matching now' q',
        x ∈ ((c.absorb now qn (resp.cnameOwned qn)).matching now' q') := by
      intro x hx
      have hx' := List.mem_filter.mp hx
      unfold Cache.matching; rw [List.mem_filter]
      exact ⟨absorb_pos_mono c now qn (resp.cnameOwned qn) x hx'.1, hx'.2⟩
    unfold Cache.topServed
    rw [List.mem_filter]
    refine ⟨hcm, ?_⟩
    simp only [List.all_eq_true] at hmax ⊢
    intro x hx
    exact hmax x (hsub x hx)
  · exact Or.inr hown

def soaNegTtl (qname : Name) (resp : Response) : Option Nat :=
  resp.authority.findSome? (fun r => match r.rdata with
    | .soa _ _ _ _ _ _ m => if isAncestor r.owner qname then some (min r.ttl m) else none
    | _ => none)
rfc_proves VeriDNS.Spec.Net.soaNegTtl [2308][465:472]

def maxNegativeTtl : Nat := 10800
rfc_proves VeriDNS.Spec.Net.maxNegativeTtl [2308][515:521]

/-- Negative-cache absorption (RFC 2308 §5).  Both arms require an EMPTY
    answer section (finding 039, RFC 6604 §3): an NXDOMAIN that terminates a
    CNAME chain arrives with the chain in the answer section and denies only
    the CHAIN-FINAL target, so it must NOT plant a name-wide negative at the
    original query name (which exists — it owns a CNAME).  A genuine
    NXDOMAIN/NODATA for `q.qname` itself has no answer records. -/
def Cache.absorbNeg (c : Cache) (now : Time) (q : Query) (resp : Response) : Cache :=
  match soaNegTtl q.qname resp with
  | none => c
  | some ttl =>
    if resp.rcode == RCode.nameError && resp.answer.isEmpty then
      { c with neg := ⟨q.qname, none, now, min ttl maxNegativeTtl⟩ :: c.neg }
    else if resp.rcode == RCode.noError && resp.answer.isEmpty then
      { c with neg := ⟨q.qname, some q.qtype, now, min ttl maxNegativeTtl⟩ :: c.neg }
    else c
rfc_proves VeriDNS.Spec.Net.Cache.absorbNeg [2308][465:472]
rfc_proves VeriDNS.Spec.Net.Cache.absorbNeg [2308][515:521]

theorem absorbNeg_ttl_is_soa_minimum (c : Cache) (now : Time) (q : Query) (resp : Response)
    (m : Nat) (hrc : resp.rcode = RCode.nameError) (hempty : resp.answer = [])
    (hm : soaNegTtl q.qname resp = some m) :
    (c.absorbNeg now q resp).neg = ⟨q.qname, none, now, min m maxNegativeTtl⟩ :: c.neg := by
  have hb : (RCode.nameError == RCode.nameError) = true := rfl
  simp [Cache.absorbNeg, hrc, hm, hb, hempty]
rfc_proves VeriDNS.Spec.Net.absorbNeg_ttl_is_soa_minimum [2308][465:472]

/-- Finding 039 dual (RFC 6604 §3): a chained NXDOMAIN — nonempty answer
    section — writes NO negative entry.  A name-wide negative for `q.qname`
    can only arise from an answerless NXDOMAIN. -/
theorem absorbNeg_chained_nxdomain (c : Cache) (now : Time) (q : Query) (resp : Response)
    (hrc : resp.rcode = RCode.nameError) (hne : resp.answer ≠ []) :
    c.absorbNeg now q resp = c := by
  unfold Cache.absorbNeg
  cases hs : soaNegTtl q.qname resp with
  | none => rfl
  | some ttl =>
    have hemp : resp.answer.isEmpty = false := by
      cases ha : resp.answer with
      | nil => exact absurd ha hne
      | cons a as => rfl
    have hb2 : (RCode.nameError == RCode.noError) = false := rfl
    rw [hrc]
    simp [hemp, hb2]

theorem absorbNeg_nodata_typed (c : Cache) (now : Time) (q : Query) (resp : Response)
    (m : Nat) (hrc : resp.rcode = RCode.noError) (hempty : resp.answer = [])
    (hm : soaNegTtl q.qname resp = some m) :
    (c.absorbNeg now q resp).neg = ⟨q.qname, some q.qtype, now, min m maxNegativeTtl⟩ :: c.neg := by
  have hne : (RCode.noError == RCode.nameError) = false := rfl
  have hno : (RCode.noError == RCode.noError) = true := rfl
  simp [Cache.absorbNeg, hrc, hm, hne, hno, hempty]
rfc_proves VeriDNS.Spec.Net.absorbNeg_nodata_typed [2308][274:376]

theorem cache_no_stale (c : Cache) (now : Time) (q : Query) (r : RR)
    (hr : r ∈ c.hit now q) : ∃ e ∈ c.pos, e.fresh now = true := by
  unfold Cache.hit Cache.served Cache.matching at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, _⟩ := hr
  rw [List.mem_filter, List.mem_filter] at he
  refine ⟨e, he.1.1, ?_⟩
  have h := he.1.2
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1
rfc_proves VeriDNS.Spec.Net.cache_no_stale [1035][1602:1614]

def Cache.size (c : Cache) : Nat := c.pos.length + c.neg.length
rfc_proves VeriDNS.Spec.Net.Cache.size [1035][1602:1614]

def Cache.cap (c : Cache) (capPos capNeg : Nat) : Cache :=
  { pos := c.pos.take capPos, neg := c.neg.take capNeg }
rfc_proves VeriDNS.Spec.Net.Cache.cap [1035][1602:1614]

def Cache.filterPos (c : Cache) (qf : CacheRR → Bool) : Cache :=
  { c with pos := c.pos.filter qf }

theorem Cache.filterPos_negHit (c : Cache) (qf : CacheRR → Bool) (now : Time) (q : Query) :
    (c.filterPos qf).negHit now q = c.negHit now q := rfl

theorem Cache.filterPos_negHitNx (c : Cache) (qf : CacheRR → Bool) (now : Time) (q : Query) :
    (c.filterPos qf).negHitNx now q = c.negHitNx now q := rfl

theorem Cache.filterPos_matching (c : Cache) (qf : CacheRR → Bool) (now : Time) (q : Query) :
    (c.filterPos qf).matching now q = (c.matching now q).filter qf := by
  unfold Cache.filterPos Cache.matching
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm _ _

def CacheRefines (cf c' : Cache) : Prop :=
  (∀ now q, (cf.topServed now q).Subperm (c'.topServed now q))
  ∧ (∀ now q, cf.negHit now q = c'.negHit now q)
  ∧ (∀ now q, cf.negHitNx now q = c'.negHitNx now q)

theorem CacheRefines.refl (c : Cache) : CacheRefines c c :=
  ⟨fun _ _ => List.Subperm.refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem CacheRefines.trans {a b c : Cache} (h : CacheRefines a b) (h' : CacheRefines b c) :
    CacheRefines a c :=
  ⟨fun n q => (h.1 n q).trans (h'.1 n q), fun n q => (h.2.1 n q).trans (h'.2.1 n q),
   fun n q => (h.2.2 n q).trans (h'.2.2 n q)⟩

theorem CacheRefines.trans_perm {a b c : Cache}
    (h : CacheRefines a b)
    (hp : ∀ now q, (b.topServed now q).Perm (c.topServed now q))
    (hn1 : ∀ now q, b.negHit now q = c.negHit now q)
    (hn2 : ∀ now q, b.negHitNx now q = c.negHitNx now q) : CacheRefines a c :=
  ⟨fun n q => (h.1 n q).trans (hp n q).subperm,
   fun n q => (h.2.1 n q).trans (hn1 n q),
   fun n q => (h.2.2 n q).trans (hn2 n q)⟩

def CacheRefinesFrom (t : Time) (cf c' : Cache) : Prop :=
  (∀ now, t ≤ now → ∀ q, (cf.topServed now q).Subperm (c'.topServed now q))
  ∧ (∀ now q, cf.negHit now q = c'.negHit now q)
  ∧ (∀ now q, cf.negHitNx now q = c'.negHitNx now q)

theorem CacheRefines.from {cf c' : Cache} (h : CacheRefines cf c') (t : Time) :
    CacheRefinesFrom t cf c' :=
  ⟨fun n _ q => h.1 n q, h.2.1, h.2.2⟩

theorem CacheRefinesFrom.refl (t : Time) (c : Cache) : CacheRefinesFrom t c c :=
  (CacheRefines.refl c).from t

theorem CacheRefinesFrom.trans {t : Time} {a b c : Cache}
    (h : CacheRefinesFrom t a b) (h' : CacheRefinesFrom t b c) : CacheRefinesFrom t a c :=
  ⟨fun n hn q => (h.1 n hn q).trans (h'.1 n hn q), fun n q => (h.2.1 n q).trans (h'.2.1 n q),
   fun n q => (h.2.2 n q).trans (h'.2.2 n q)⟩

theorem CacheRefinesFrom.trans_cacheRefines {t : Time} {a b c : Cache}
    (h : CacheRefinesFrom t a b) (h' : CacheRefines b c) : CacheRefinesFrom t a c :=
  h.trans (h'.from t)

theorem CacheRefines.trans_from {t : Time} {a b c : Cache}
    (h : CacheRefines a b) (h' : CacheRefinesFrom t b c) : CacheRefinesFrom t a c :=
  (h.from t).trans h'

def WriteRefines (t : Time) (cf c' : Cache) : Prop :=
  (∀ now, t ≤ now → ∀ q, (cf.topServed now q).Subperm (c'.topServed now q))
  ∧ (∀ now q, ∀ e ∈ cf.topServed now q, ∃ now2, e ∈ c'.topServed now2 q)
  ∧ (∀ now q, cf.negHit now q = c'.negHit now q)
  ∧ (∀ now q, cf.negHitNx now q = c'.negHitNx now q)

theorem CacheRefines.writeRefines {cf c' : Cache} (h : CacheRefines cf c') (t : Time) :
    WriteRefines t cf c' :=
  ⟨fun n _ q => h.1 n q, fun n q e he => ⟨n, (h.1 n q).subset he⟩, h.2.1, h.2.2⟩

theorem WriteRefines.refl (t : Time) (c : Cache) : WriteRefines t c c :=
  (CacheRefines.refl c).writeRefines t

theorem WriteRefines.trans {t : Time} {a b c : Cache}
    (h : WriteRefines t a b) (h' : WriteRefines t b c) : WriteRefines t a c :=
  ⟨fun n hn q => (h.1 n hn q).trans (h'.1 n hn q),
   fun n q e he => by
     obtain ⟨n2, he2⟩ := h.2.1 n q e he
     exact h'.2.1 n2 q e he2,
   fun n q => (h.2.2.1 n q).trans (h'.2.2.1 n q),
   fun n q => (h.2.2.2 n q).trans (h'.2.2.2 n q)⟩

theorem WriteRefines.trans_perm {t : Time} {a b c : Cache}
    (h : WriteRefines t a b)
    (hp : ∀ now q, (b.topServed now q).Perm (c.topServed now q))
    (hn1 : ∀ now q, b.negHit now q = c.negHit now q)
    (hn2 : ∀ now q, b.negHitNx now q = c.negHitNx now q) : WriteRefines t a c :=
  ⟨fun n hn q => (h.1 n hn q).trans (hp n q).subperm,
   fun n q e he => by
     obtain ⟨n2, he2⟩ := h.2.1 n q e he
     exact ⟨n2, (hp n2 q).subset he2⟩,
   fun n q => (h.2.2.1 n q).trans (hn1 n q),
   fun n q => (h.2.2.2 n q).trans (hn2 n q)⟩

theorem CacheRefines.trans_writeRefines {t : Time} {a b c : Cache}
    (h : CacheRefines a b) (h' : WriteRefines t b c) : WriteRefines t a c :=
  (h.writeRefines t).trans h'

def NegWriteRefines (t : Time) (cf c' : Cache) : Prop :=
  (∀ now, t ≤ now → ∀ q, (cf.topServed now q).Subperm (c'.topServed now q))
  ∧ (∀ now q, ∀ e ∈ cf.topServed now q, ∃ now2, e ∈ c'.topServed now2 q)
  ∧ (∀ now q, cf.negHit now q = true → c'.negHit now q = true)
  ∧ (∀ now q, cf.negHitNx now q = true → c'.negHitNx now q = true)
rfc_proves VeriDNS.Spec.Net.NegWriteRefines [2308][515:521]

theorem WriteRefines.negWriteRefines {t : Time} {cf c' : Cache} (h : WriteRefines t cf c') :
    NegWriteRefines t cf c' :=
  ⟨h.1, h.2.1, fun n q hq => (h.2.2.1 n q) ▸ hq, fun n q hq => (h.2.2.2 n q) ▸ hq⟩

theorem NegWriteRefines.refl (t : Time) (c : Cache) : NegWriteRefines t c c :=
  (WriteRefines.refl t c).negWriteRefines

theorem NegWriteRefines.trans_perm {t : Time} {a b c : Cache}
    (h : NegWriteRefines t a b)
    (hp : ∀ now q, (b.topServed now q).Perm (c.topServed now q))
    (hn1 : ∀ now q, b.negHit now q = c.negHit now q)
    (hn2 : ∀ now q, b.negHitNx now q = c.negHitNx now q) : NegWriteRefines t a c :=
  ⟨fun n hn q => (h.1 n hn q).trans (hp n q).subperm,
   fun n q e he => by
     obtain ⟨n2, he2⟩ := h.2.1 n q e he
     exact ⟨n2, (hp n2 q).subset he2⟩,
   fun n q hq => (hn1 n q) ▸ h.2.2.1 n q hq,
   fun n q hq => (hn2 n q) ▸ h.2.2.2 n q hq⟩

theorem WriteRefines.hit_nil {t : Time} {cf c' : Cache} (h : WriteRefines t cf c')
    {now : Time} (hle : t ≤ now) {q : Query} (hnil : c'.hit now q = []) :
    cf.hit now q = [] := by
  have hserved : c'.served now q = [] := by
    unfold Cache.hit at hnil
    exact List.map_eq_nil_iff.mp hnil
  have htop : (cf.served now q).Subperm (c'.served now q) := by
    rw [cf.served_eq_topServed_filter, c'.served_eq_topServed_filter]
    exact List.Subperm.filter _ (h.1 now hle q)
  rw [hserved] at htop
  unfold Cache.hit
  rw [List.subperm_nil.mp htop]
  rfl

theorem absorb_resp_congr (c : Cache) (now : Time) (bw : Name) {r₁ r₂ : Response}
    (haa : r₁.aa = r₂.aa) (hans : r₁.answer = r₂.answer)
    (hauth : r₁.authority = r₂.authority) (hadd : r₁.additional = r₂.additional) :
    c.absorb now bw r₁ = c.absorb now bw r₂ := by
  unfold Cache.absorb
  rw [haa, hans, hauth, hadd]

theorem Response.isReferral_answer_nil {r : Response} (h : r.isReferral = true) : r.answer = [] := by
  unfold Response.isReferral at h
  simp only [Bool.and_eq_true] at h
  exact List.isEmpty_iff.mp h.1.1.1.1

theorem Response.isReferral_aa_false {r : Response} (h : r.isReferral = true) : r.aa = false := by
  unfold Response.isReferral at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact h.1.1.1.2

theorem Cache.cap_size_le (c : Cache) (capPos capNeg : Nat) :
    (c.cap capPos capNeg).size ≤ capPos + capNeg := by
  simp only [Cache.cap, Cache.size, List.length_take]
  omega

theorem Cache.cap_pos_subset (c : Cache) (capPos capNeg : Nat) (e : CacheRR)
    (he : e ∈ (c.cap capPos capNeg).pos) : e ∈ c.pos :=
  List.take_subset _ _ he

theorem Cache.cap_neg_subset (c : Cache) (capPos capNeg : Nat) (e : NegRR)
    (he : e ∈ (c.cap capPos capNeg).neg) : e ∈ c.neg :=
  List.take_subset _ _ he

theorem Cache.cap_no_stale (c : Cache) (now : Time) (q : Query) (capPos capNeg : Nat) (r : RR)
    (hr : r ∈ (c.cap capPos capNeg).hit now q) : ∃ e ∈ c.pos, e.fresh now = true := by
  obtain ⟨e, he, hf⟩ := cache_no_stale (c.cap capPos capNeg) now q r hr
  exact ⟨e, Cache.cap_pos_subset c capPos capNeg e he, hf⟩

theorem ex_cache_eviction :
    let c : Cache :=
      ((Cache.empty.insert 0 Cred.authoritative (rr ["old","X"] 100 (.a ⟨1,1,1,1⟩))).insert
        10 Cred.authoritative (rr ["mid","X"] 100 (.a ⟨2,2,2,2⟩))).insert
        20 Cred.authoritative (rr ["new","X"] 100 (.a ⟨3,3,3,3⟩))
    (c.cap 2 0).size ≤ 2
      ∧ (c.cap 2 0).pos.any (fun e => nameEq e.rr.owner (N ["new","X"])) = true
      ∧ (c.cap 2 0).pos.any (fun e => nameEq e.rr.owner (N ["old","X"])) = false := by
  refine ⟨?_, by decide, by decide⟩
  exact Cache.cap_size_le _ 2 0
rfc_proves VeriDNS.Spec.Net.ex_cache_eviction [1035][1602:1614]

def moreCredible (a b : CacheRR) : CacheRR :=
  if Nat.blt a.cred.rank b.cred.rank then b else a
rfc_proves VeriDNS.Spec.Net.moreCredible [2181][343:383]

theorem authoritative_beats_glue (a b : CacheRR)
    (ha : a.cred = Cred.glue) (hb : b.cred = Cred.authoritative) :
    moreCredible a b = b := by
  simp [moreCredible, ha, hb, Cred.rank]
rfc_proves VeriDNS.Spec.Net.authoritative_beats_glue [2181][343:383]

theorem served_excludes_dominated (c : Cache) (now : Time) (q : Query) (eg ea : CacheRR)
    (hea : ea ∈ c.matching now q) (hkey : ea.sameKey eg.rr = true)
    (hlt : eg.cred.rank < ea.cred.rank) :
    eg ∉ c.served now q := by
  simp only [Cache.served, List.mem_filter, not_and]
  intro _ hall
  rw [Bool.and_eq_true, List.all_eq_true] at hall
  have hcontra := hall.2 ea hea
  simp only [hkey, Bool.not_true, Bool.false_or, Nat.ble_eq] at hcontra
  omega
rfc_proves VeriDNS.Spec.Net.served_excludes_dominated [2181][343:383]

theorem served_glue_yields_to_authoritative (c : Cache) (now : Time) (q : Query) (eg ea : CacheRR)
    (hea : ea ∈ c.matching now q) (hkey : ea.sameKey eg.rr = true)
    (hg : eg.cred = Cred.glue) (ha : ea.cred = Cred.authoritative) :
    eg ∉ c.served now q :=
  served_excludes_dominated c now q eg ea hea hkey (by rw [hg, ha]; decide)
rfc_proves VeriDNS.Spec.Net.served_glue_yields_to_authoritative [2181][343:383]

def poisonCache : Cache :=
  { pos := [ ⟨rr ["NS1","SUB"] 100 (.a ⟨1,2,3,4⟩), 0, Cred.authoritative⟩,
             ⟨rr ["NS1","SUB"] 100 (.a ⟨6,6,6,6⟩), 0, Cred.glue⟩ ], neg := [] }

theorem hit_drops_poison_glue :
    (⟨rr ["NS1","SUB"] 100 (.a ⟨6,6,6,6⟩), 0, Cred.glue⟩ : CacheRR)
      ∉ poisonCache.served 0 ⟨N ["NS1","SUB"], .rr .a, .«in», false⟩ := by
  refine served_glue_yields_to_authoritative poisonCache 0 _ _
    ⟨rr ["NS1","SUB"] 100 (.a ⟨1,2,3,4⟩), 0, Cred.authoritative⟩ ?_ (by decide) rfl rfl
  rw [Cache.matching, List.mem_filter]
  exact ⟨List.mem_cons_self, by decide⟩
rfc_proves VeriDNS.Spec.Net.hit_drops_poison_glue [2181][343:383]

structure SlistEntry where
  addr : String
  rtt : Nat
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.SlistEntry [1034][1934:1939]

def rttLe (a b : SlistEntry) : Prop := a.rtt ≤ b.rtt

def insertByRtt (x : SlistEntry) : List SlistEntry → List SlistEntry
  | [] => [x]
  | y :: ys => if x.rtt ≤ y.rtt then x :: y :: ys else y :: insertByRtt x ys

def sortedByRtt (es : List SlistEntry) : List SlistEntry := es.foldr insertByRtt []

def sortByRtt (es : List SlistEntry) : List String := (sortedByRtt es).map (·.addr)
rfc_proves VeriDNS.Spec.Net.sortByRtt [1034][1934:1939]

def serverAt (net : Network) (addr : String) : Option Server :=
  net.servers.find? (fun s => s.addr == addr)
rfc_proves VeriDNS.Spec.Net.serverAt [1034][1319:1330]

theorem serverAt_mem {net : Network} {addr : String} {srv : Server}
    (h : serverAt net addr = some srv) : srv ∈ net.servers :=
  List.mem_of_find?_eq_some h

def serverBailiwick (srv : Server) (qname : Name) (qcls : RRClass := RRClass.in) : Name :=
  (bestZone srv qname qcls).elim qname (·.apex)
rfc_proves VeriDNS.Spec.Net.serverBailiwick [1034][1319:1330]

theorem serverBailiwick_covers_qname (srv : Server) (qname : Name) (qcls : RRClass) :
    isAncestor (serverBailiwick srv qname qcls) qname = true := by
  unfold serverBailiwick
  rcases h : bestZone srv qname qcls with _ | z
  · simp only [Option.elim]; exact isAncestor_refl _
  · simp only [Option.elim]

    unfold bestZone at h
    have hgen : ∀ (l : List Zone) (acc : Option Zone),
        (l.foldl (fun acc z => match acc with
          | none => some z
          | some z' => if z'.apex.length < z.apex.length then some z else some z') acc = some z) →
        (acc = some z ∨ z ∈ l) := by
      intro l
      induction l with
      | nil => intro acc h; exact Or.inl h
      | cons x xs ih =>
          intro acc h
          rcases ih _ h with h' | h'
          · cases acc with
            | none => simp only [Option.some.injEq] at h'; exact Or.inr (h' ▸ List.mem_cons_self)
            | some a =>
                by_cases hc : a.apex.length < x.apex.length
                · simp only [hc, if_true, Option.some.injEq] at h'
                  exact Or.inr (h' ▸ List.mem_cons_self)
                · simp only [hc, if_false, Option.some.injEq] at h'
                  exact Or.inl (congrArg some h')
          · exact Or.inr (List.mem_cons_of_mem _ h')
    have hmem : z ∈ srv.zones.filter (fun z => z.cls == qcls && isAncestor z.apex qname) := by
      rcases hgen _ none h with h' | h'
      · exact absurd h' (by simp)
      · exact h'
    have hf := (List.mem_filter.mp hmem).2
    simp only [Bool.and_eq_true] at hf
    exact hf.2

def referralCut (resp : Response) : Name :=
  (resp.authority.find? (fun r => r.rdata.rtype == RRType.ns)).elim [] (·.owner)
rfc_proves VeriDNS.Spec.Net.referralCut [1034][1319:1330]

def Response.descendsBelow (resp : Response) (apex : Name) : Bool :=
  isAncestor apex (referralCut resp) && Nat.blt apex.length (referralCut resp).length
rfc_proves VeriDNS.Spec.Net.Response.descendsBelow [1034][1319:1330]

theorem descendsBelow_strict {resp : Response} {apex : Name} (h : resp.descendsBelow apex = true) :
    isAncestor apex (referralCut resp) = true ∧ apex.length < (referralCut resp).length := by
  simp only [Response.descendsBelow, Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem descendsBelow_of_strict {resp : Response} {apex : Name}
    (hanc : isAncestor apex (referralCut resp) = true)
    (hlt : apex.length < (referralCut resp).length) :
    resp.descendsBelow apex = true := by
  simp only [Response.descendsBelow, Bool.and_eq_true, Nat.blt_eq]
  exact ⟨hanc, hlt⟩

theorem isAncestor_referralCut_of_inBailiwick {r : Response} {qname : Name}
    (h : r.inBailiwick qname = true) : isAncestor (referralCut r) qname = true := by
  unfold referralCut
  cases hfd : r.authority.find? (fun rr => rr.rdata.rtype == RRType.ns) with
  | none =>
    simp only [Option.elim]
    unfold isAncestor
    simp [nameEq_refl]
  | some rr₀ =>
    simp only [Option.elim]
    have hp := List.find?_some hfd
    exact (inBailiwick_iff r qname).mp h rr₀ (List.mem_of_find?_eq_some hfd) hp

theorem referral_descends_strictly :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["BRL","MIL"], .rr .a, .«in», false⟩ tr resp
      ∧ resp.descendsBelow (serverBailiwick cISI (N ["BRL","MIL"]) RRClass.in) = true := by
  refine ⟨_, _, ServerAnswers.referral _ rootZone _ rfl rfl rfl, by decide⟩
rfc_proves VeriDNS.Spec.Net.referral_descends_strictly [1034][1319:1330]

def absorbBailiwick (srvApex cut : Name) : Name :=
  if isAncestor srvApex cut && Nat.blt srvApex.length cut.length then cut else srvApex

theorem isAncestor_absorbBailiwick (srvApex cut : Name) :
    isAncestor srvApex (absorbBailiwick srvApex cut) = true := by
  unfold absorbBailiwick
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact h.1
  · exact isAncestor_refl _

theorem absorbBailiwick_of_descendsBelow (srvApex : Name) (resp : Response)
    (h : resp.descendsBelow srvApex = true) :
    absorbBailiwick srvApex (referralCut resp) = referralCut resp := by
  show (if resp.descendsBelow srvApex then referralCut resp else srvApex) = referralCut resp
  rw [h]; simp

/-- The NS hosts of the delegation AT the referral cut: only NS records
owned (case-insensitively) at the delegation point contribute referred
servers. An NS record owned ABOVE the cut smuggled into the authority
section is NOT part of the delegation — real resolvers (unbound's
scrubber) delete such off-cut NS records (RFC 2181 §5.4.1). -/
def cutServers (r : Response) : List Name :=
  (r.authority.filter (fun rr => nameEq rr.owner (referralCut r))).filterMap
    (fun rr => match rr.rdata with | .ns h => some h | _ => none)
rfc_proves VeriDNS.Spec.Net.cutServers [1034][1319:1330]

def glueAddresses (ref : Response) : List String :=

  (cutServers ref).filterMap (fun h =>
    (ref.additional.find? (fun r =>
        (match r.rdata with | .a _ => true | _ => false)
          && nameEq h r.owner && isAncestor (referralCut ref) r.owner)).bind
      (fun r => match r.rdata with | .a a => some a.toDotted | _ => none))
rfc_proves VeriDNS.Spec.Net.glueAddresses [1034][1319:1330]

theorem mem_glueAddresses (ref : Response) (s : String) :
    s ∈ glueAddresses ref ↔ ∃ h ∈ cutServers ref, ∃ r a,
      ref.additional.find? (fun r => (match r.rdata with | .a _ => true | _ => false)
          && nameEq h r.owner && isAncestor (referralCut ref) r.owner) = some r
        ∧ r.rdata = RData.a a ∧ a.toDotted = s := by
  unfold glueAddresses
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, hg⟩
    rw [Option.bind_eq_some_iff] at hg
    obtain ⟨r, hfind, hext⟩ := hg
    split at hext
    · rename_i a heq
      exact ⟨h, hh, r, a, hfind, heq, by injection hext⟩
    · exact absurd hext (by simp)
  · rintro ⟨h, hh, r, a, hfind, hrd, hs⟩
    refine ⟨h, hh, ?_⟩
    rw [Option.bind_eq_some_iff]
    exact ⟨r, hfind, by rw [hrd]; simp [hs]⟩

def glueEntries (rttOf : String → Nat) (ref : Response) : List SlistEntry :=
  (glueAddresses ref).map (fun a => ⟨a, rttOf a⟩)
rfc_proves VeriDNS.Spec.Net.glueEntries [1034][1934:1939]

def Cache.nsHostsAt (c : Cache) (now : Time) (nm : Name) : List Name :=
  (c.topServed now ⟨nm, QType.rr RRType.ns, RRClass.in, false⟩).filterMap (fun e =>
    match e.rr.rdata with | .ns h => some h | _ => none)

def Cache.glueAddrsAt (c : Cache) (now : Time) (h : Name) : List String :=
  (c.topServed now ⟨h, QType.rr RRType.a, RRClass.in, false⟩).filterMap (fun e =>
    match e.rr.rdata with | .a a => some a.toDotted | _ => none)

def Cache.referralSlist (c : Cache) (now : Time) : Name → Nat → List String
  | _, 0 => []
  | nm, fuel + 1 =>
    if (c.nsHostsAt now nm).isEmpty then
      match nm with
      | [] => []
      | _ :: parent => c.referralSlist now parent fuel
    else
      (c.nsHostsAt now nm).flatMap (fun h => c.glueAddrsAt now h)

def Cache.referralEntries (rttOf : String → Nat) (c : Cache) (now : Time) (nm : Name)
    (fuel : Nat) : List SlistEntry :=
  (c.referralSlist now nm fuel).map (fun a => ⟨a, rttOf a⟩)

theorem glue_ignores_non_ns_address :
    glueAddresses
        { aa := false, rcode := RCode.noError, answer := [],
          authority := [ rr ["SUB"] 100 (.ns (N ["NS1","SUB"])) ],
          additional := [ rr ["NS1","SUB"] 100 (.a ⟨7,7,7,7⟩),
                          rr ["EVIL","COM"] 100 (.a ⟨6,6,6,6⟩) ] }
      = ["7.7.7.7"] := by decide
rfc_proves VeriDNS.Spec.Net.glue_ignores_non_ns_address [1034][1319:1330]

theorem out_of_bailiwick_glue_rejected :
    glueAddresses
        { aa := false, rcode := RCode.noError, answer := [],
          authority := [ rr ["SUB"] 100 (.ns (N ["NS1","SUB"])),
                         rr ["SUB"] 100 (.ns (N ["EVIL","COM"])) ],
          additional := [ rr ["NS1","SUB"] 100 (.a ⟨7,7,7,7⟩),
                          rr ["EVIL","COM"] 100 (.a ⟨6,6,6,6⟩) ] }
      = ["7.7.7.7"] := by decide
rfc_proves VeriDNS.Spec.Net.out_of_bailiwick_glue_rejected [1034][1319:1330]

def ipKey (ip : IPv4) : Nat :=
  ip.o0.toNat * 16777216 + ip.o1.toNat * 65536 + ip.o2.toNat * 256 + ip.o3.toNat

def ipMinOpt (acc : Option IPv4) (ip : IPv4) : Option IPv4 :=
  match acc with | none => some ip | some b => some (if ipKey ip < ipKey b then ip else b)

/-- The per-record picker for `addressOf`: the A-record payload, but only
when the record's owner lies in the entitled name set `reach`. -/
def aRecordOf (reach : List Name) (r : RR) : Option IPv4 :=
  if reach.any (fun n => nameEq r.owner n) then
    match r.rdata with | .a a => some a | _ => none
  else none

/-- The address pick for a glueless NS host's sub-resolution verdict.
Only A records whose owner lies on the CNAME chain rooted at `owner` (the
NS host being resolved) are considered — an off-owner A record planted in
the answer section must not redirect the NS-probe target (RFC 2181
§5.4.1; unbound harvests target addresses only at the target name). -/
def addressOf (owner : Name) (resp : Response) : Option String :=
  ((resp.answer.filterMap (aRecordOf (reachableNames owner resp.answer))).foldl
    ipMinOpt none).map IPv4.toDotted
rfc_proves VeriDNS.Spec.Net.addressOf [1034][1319:1330]

def reachOf (net : Network) (ns : NetState) (addr : String) : Bool :=
  net.servers.any (fun s => (s.addr == addr) && ns.isUp s.name)
rfc_proves VeriDNS.Spec.Net.reachOf [1034][1012:1018]

def linkReach (net : Network) (ns : NetState) (resolverAddr : String) : String → Bool :=
  fun a => (a == resolverAddr) || reachOf net ns a
rfc_proves VeriDNS.Spec.Net.linkReach [1034][1012:1018]

def StrictProbe (pq q : Query) : Prop :=
  (∃ cut, ProbeFor pq.qname q.qname cut = true)
    ∧ pq.qtype = QType.rr RRType.a ∧ pq.qclass = q.qclass
rfc_proves VeriDNS.Spec.Net.StrictProbe [9156][136:168]

def ProbeQuery (pq q : Query) : Prop :=
  (pq.qname = q.qname ∧ pq.qtype = q.qtype ∧ pq.qclass = q.qclass) ∨ StrictProbe pq q
rfc_proves VeriDNS.Spec.Net.ProbeQuery [9156][194:207]

theorem ProbeQuery.refl (q : Query) : ProbeQuery q q := Or.inl ⟨rfl, rfl, rfl⟩

def LameReply (m : Response) : Prop :=
  m.rcode ≠ RCode.noError ∧ m.rcode ≠ RCode.nameError

/-- Justification for a give-up (SERVFAIL) verdict, per RFC 1034 §5.3.3: a resolver
may return a server-failure answer only when resolution genuinely could not proceed.

Both modes require the mandatory cache-miss facts (RFC 1034 §5.3.1 step 1: the local
cache is always consulted first, so a give-up can never shadow a cached answer —
positive or negative). The modes mirror the concrete implementation failure paths:

* `serversExhausted` — the SLIST is empty: every candidate server was consumed
  (timeout, lame reply, spoof rejection, unfollowable referral, …) without an answer.
  This is §5.3.3's "exhausted the servers" arm; it also covers the address-less-SLIST
  and glueless-depth give-ups, whose model SLIST abstraction is empty.
* `outOfBudget` — the per-query work budget elapsed (query deadline / IO-round fuel),
  §5.3.3's batch-timeout arm. The model does not index derivations by a work budget,
  so this mode records only the mandatory cache-miss facts; indexing `Resolves` by a
  time/work budget is a recorded follow-up. -/
inductive GaveUpWitness (now : Time) (c : Cache) (slist : List String) (q : Query) : Prop where
  | serversExhausted
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hnoServers : slist = [])
  | outOfBudget
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)

theorem GaveUpWitness.hit_nil {now : Time} {c : Cache} {slist : List String} {q : Query}
    (hw : GaveUpWitness now c slist q) : c.hit now q = [] := by
  cases hw with
  | serversExhausted hmiss _ _ => exact hmiss
  | outOfBudget hmiss _ => exact hmiss

theorem GaveUpWitness.negHit_false {now : Time} {c : Cache} {slist : List String} {q : Query}
    (hw : GaveUpWitness now c slist q) : c.negHit now q = false := by
  cases hw with
  | serversExhausted _ hnmiss _ => exact hnmiss
  | outOfBudget _ hnmiss => exact hnmiss

/-- The give-up witness never inspects the recursion-desired bit. -/
theorem GaveUpWitness.rd {now : Time} {c : Cache} {slist : List String} {q : Query} (b : Bool)
    (hw : GaveUpWitness now c slist q) : GaveUpWitness now c slist { q with rd := b } := by
  cases hw with
  | serversExhausted hmiss hnmiss hns => exact .serversExhausted hmiss hnmiss hns
  | outOfBudget hmiss hnmiss => exact .outOfBudget hmiss hnmiss

inductive Resolves (net : Network) (ns : NetState) (resolverAddr : String) (ednsBuf : Nat) (rttOf : String → Nat) :
    Time → List Name → List Name → Cache → List String → Query → List Step → List String →
    Time → Cache → Response → Prop where

  | cacheHit {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (slist : List String)
      (q : Query) (here : List RR)
      (hhit : c.hit now q = here) (hne : 0 < here.length) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q [Step.fromCache] [] now c
        { aa := false, rcode := RCode.noError, answer := here, authority := [], additional := [] }

  | negHit {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (slist : List String)
      (q : Query) (hneg : c.negHit now q = true) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q
        (c.negTrace now q) [] now c (c.negResponse now q)

  | answer {now : Time} {nseen : List Name} {seen : List Name} (addr : String) (rest : List String)
      (q : Query) (srv : Server) (tr : List Step) (resp : Response) (id srcPort : Nat) (c : Cache)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hfind : serverAt net addr = some srv)
      (hans : ServerAnswers srv now [] true q tr resp)
      (reply : Datagram)
      (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
      (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
      (hnr : reply.msg.isReferral = false)

      (hnc : cnameRR q.qname reply.msg.answer = none ∨ q.qtype.covers RRType.cname = true
              ∨ (∃ rr ∈ reply.msg.answer, q.qtype.covers rr.rdata.rtype = true))

      (htc : reply.msg.tc = false) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q tr [] now
        ((c.absorb now (serverBailiwick srv q.qname q.qclass) reply.msg).absorbNeg now q reply.msg)
        { reply.msg with aa := false }

  | trustedReply {now : Time} {nseen : List Name} {seen : List Name} (addr origin : String)
      (rest : List String) (q : Query) (id srcPort : Nat) (c : Cache) (reply : Datagram)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
      (hnr : reply.msg.isReferral = false) (htc : reply.msg.tc = false)
      (cf0 : Cache)
      (hcf0 : WriteRefines now cf0 (c.absorb now q.qname (reply.msg.answerOwned q.qname))
              ∨ cf0 = c)
      (cf : Cache)
      (hcf : WriteRefines now cf cf0) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q [] [] now cf
        { reply.msg with aa := false }

  | refer {now now' : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q pq : Query) (srv : Server) (tr : List Step) (ref : Response)
      (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
      (id srcPort : Nat) (c cout : Cache)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hprobe : ProbeQuery pq q)
      (hfind : serverAt net addr = some srv)
      (hans : ServerAnswers srv now [] true pq tr ref)
      (reply : Datagram)
      (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
      (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf pq) ref reply)
      (href : reply.msg.isReferral = true)
      (hbail : reply.msg.inBailiwick q.qname = true)

      (frontier : Name)
      (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
      (hdescF : reply.msg.descendsBelow frontier = true)
      (hglue : glueAddresses reply.msg ≠ [])
      (hfresh : frontier ∉ seen)
      (hmono : now ≤ now')

      (sl : List String)
      (hsl : ((c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut reply.msg)) reply.msg).referralSlist now' q.qname (q.qname.length + 1)).Subperm sl)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
                (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut reply.msg)) reply.msg)
                sl q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q (tr ++ ftr)
        (addr :: rpath) tEnd cout final

  | referForget {now now' : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q pq : Query) (srv : Server) (tr : List Step) (ref : Response)
      (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
      (id srcPort : Nat) (c cout : Cache)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hprobe : ProbeQuery pq q)
      (hfind : serverAt net addr = some srv)
      (hans : ServerAnswers srv now [] true pq tr ref)
      (reply : Datagram)
      (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
      (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf pq) ref reply)
      (href : reply.msg.isReferral = true)
      (hbail : reply.msg.inBailiwick q.qname = true)

      (frontier : Name)
      (hdesc : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = true)
      (hdescF : reply.msg.descendsBelow frontier = true)
      (hfresh : frontier ∉ seen)
      (hmono : now ≤ now')
      (sl : List String)
      (cf0 : Cache)
      (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut reply.msg)) reply.msg))

      (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
              ∨ (glueAddresses reply.msg).Subperm sl)
      (cf : Cache)
      (hcf : WriteRefines now' cf cf0)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
                cf sl q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q (tr ++ ftr)
        (addr :: rpath) tEnd cout final

  | trustedReferral {now now' : Time} {nseen : List Name} {seen : List Name} (addr origin : String)
      (rest : List String) (q pq : Query) (frontier : Name)
      (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
      (id srcPort : Nat) (c cout : Cache)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hprobe : ProbeQuery pq q)
      (reply : Datagram)
      (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
      (href : reply.msg.isReferral = true)
      (hbail : reply.msg.inBailiwick q.qname = true)

      (hcut : isAncestor (referralCut reply.msg) pq.qname = true)
      (hdesc : reply.msg.descendsBelow frontier = true)
      (hfresh : frontier ∉ seen)
      (hmono : now ≤ now')
      (sl : List String)
      (cf0 : Cache)
      (hcf0 : WriteRefines now' cf0 (c.absorb now (absorbBailiwick frontier (referralCut reply.msg)) reply.msg))
      (hsl : (cf0.referralSlist now' q.qname (q.qname.length + 1)).Subperm sl
              ∨ (glueAddresses reply.msg).Subperm sl)
      (cf : Cache)
      (hcf : WriteRefines now' cf cf0)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen (frontier :: seen)
                cf sl q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q ftr
        (addr :: rpath) tEnd cout final

  | answerCname {now now' : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q : Query) (srv : Server) (tr : List Step) (resp : Response)
      (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
      (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hfind : serverAt net addr = some srv)
      (hans : ServerAnswers srv now [] true q tr resp)
      (reply : Datagram)
      (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
      (hwire : OnWire (queryDatagram id resolverAddr addr srcPort ednsBuf q) (truncateToCap (negotiatedUdp ednsBuf) q resp).1 reply)
      (hcn : cnameRR q.qname reply.msg.answer = some cn)
      (hqt : q.qtype.covers RRType.cname = false)
      (htgt : cn.rdata = RData.cname target)
      (hfresh : target ∉ q.qname :: nseen)
      (hmono : now ≤ now')

      (htc : reply.msg.tc = false)

      (cf0 : Cache)
      (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname (reply.msg.cnameOwned q.qname)))
      (cf : Cache)
      (hcf : WriteRefines now' cf cf0)

      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
                cf nsl { q with qname := target } ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q
        (tr ++ Step.followCNAME target :: ftr) rpath tEnd cout
        { final with answer := cn :: final.answer }

  | trustedCname {now now' : Time} {nseen : List Name} {seen : List Name} (addr origin : String)
      (rest : List String) (q : Query)
      (cn : RR) (target : Name) (id srcPort : Nat) (c : Cache) (nsl : List String)
      (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (reply : Datagram)
      (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf q) reply = true)
      (hcn : cnameRR q.qname reply.msg.answer = some cn)
      (hqt : q.qtype.covers RRType.cname = false)
      (htgt : cn.rdata = RData.cname target)
      (hfresh : target ∉ q.qname :: nseen)
      (hmono : now ≤ now')
      (htc : reply.msg.tc = false)
      (cf0 : Cache)
      (hcf0 : WriteRefines now' cf0 (c.absorb now q.qname (reply.msg.cnameOwned q.qname)))
      (cf : Cache)
      (hcf : WriteRefines now' cf cf0)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' (q.qname :: nseen) []
                cf nsl { q with qname := target } ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q
        (Step.followCNAME target :: ftr) rpath tEnd cout
        { final with answer := cn :: final.answer }

  | cacheCname {now : Time} {nseen : List Name} {seen : List Name} (slist : List String)
      (q : Query) (cn : RR) (target : Name) (c : Cache) (nsl : List String)
      (ftr : List Step) (rpath : List String) (tEnd : Time) (cout : Cache) (final : Response)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hcn : cn ∈ c.cnameServed now q.qname q.qclass)
      (hqt : q.qtype.covers RRType.cname = false)
      (htgt : cn.rdata = RData.cname target)
      (hfresh : target ∉ q.qname :: nseen)

      (cf : Cache)
      (hcf : CacheRefines cf c)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now (q.qname :: nseen) seen cf nsl
                { q with qname := target } ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q
        (Step.fromCache :: Step.followCNAME target :: ftr) rpath tEnd cout
        { final with answer := cn :: final.answer }

  | timeout {now now' : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q : Query) (ftr : List Step) (rpath : List String) (tEnd : Time)
      (final : Response) (c cout : Cache) (d : Datagram)
      (hdrop : Transit (linkReach net ns resolverAddr) addr resolverAddr d none)
      (hmono : now ≤ now')
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now' nseen seen c rest q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q ftr rpath tEnd cout final

  | skipMissing {now : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q : Query) (ftr : List Step) (rpath : List String) (tEnd : Time)
      (final : Response) (c cout : Cache)
      (hfind : serverAt net addr = none)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q ftr rpath tEnd cout final


  | gluelessNs {now now1 : Time} {nseen : List Name} {seen : List Name}
      (q : Query) (zone : Name) (nsHost : Name) (nsAddr : String)
      (nsNseen nsSeen : List Name) (nsSlist : List String) (nsTr : List Step)
      (nsPath : List String) (nsEnd : Time) (nsResp : Response)
      (slist2 : List String) (ftr : List Step) (rpath : List String) (tEnd : Time)
      (final : Response) (c c2 cout : Cache)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hanc : isAncestor zone q.qname = true)
      (cprov : Cache)
      (hns : nsHost ∈ cprov.nsHostsAt now zone)
      (hmono1 : now ≤ now1)
      (hnsres : Resolves net ns resolverAddr ednsBuf rttOf now1 nsNseen nsSeen c nsSlist
                  ⟨nsHost, QType.rr RRType.a, RRClass.in, false⟩ nsTr nsPath nsEnd c2 nsResp)
      (hnsaddr : addressOf nsHost nsResp = some nsAddr)
      (hmem : nsAddr ∈ slist2)

      (c2f : Cache)
      (hc2f : CacheRefines c2f c2)

      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c2f slist2 q
                ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c [] q ftr rpath tEnd cout final

  | rejectSpoof {now : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q pq : Query) (ftr : List Step) (rpath : List String) (tEnd : Time)
      (final : Response) (c cout : Cache) (id srcPort : Nat) (reply : Datagram)
      (hprobe : ProbeQuery pq q)
      (hreject : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = false)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q ftr rpath tEnd cout final

  | badResponse {now : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q pq : Query) (ftr : List Step) (rpath : List String) (tEnd : Time)
      (final : Response) (c cout : Cache) (id srcPort : Nat) (reply : Datagram)
      (hprobe : ProbeQuery pq q)
      (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
      (hbad : reply.msg.rcode = RCode.servFail ∨ LameReply reply.msg ∨ StrictProbe pq q)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q ftr rpath tEnd cout final

  | unfollowableReferral {now : Time} {nseen : List Name} {seen : List Name} (addr : String)
      (rest : List String) (q pq : Query) (srv : Server) (tr : List Step) (ref : Response)
      (id srcPort : Nat) (ftr : List Step) (rpath : List String) (tEnd : Time) (final : Response)
      (c cout : Cache) (reply : Datagram)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hprobe : ProbeQuery pq q)
      (hfind : serverAt net addr = some srv)
      (hans : ServerAnswers srv now [] true pq tr ref)
      (htrans : Transit (linkReach net ns resolverAddr) addr resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
      (href : reply.msg.isReferral = true)
      (hunfollow : reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass) = false)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c rest q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q ftr rpath tEnd cout final

  | ancestorDenied {now : Time} {nseen : List Name} {seen : List Name} (addr origin : String)
      (rest : List String) (q pq : Query) (id srcPort : Nat) (c : Cache) (reply : Datagram)
      (hmiss : c.hit now q = [])
      (hnmiss : c.negHit now q = false)
      (hprobe : StrictProbe pq q)
      (htrans : Transit (linkReach net ns resolverAddr) origin resolverAddr reply (some reply))
      (hacc : accepts (queryDatagram id resolverAddr addr srcPort ednsBuf pq) reply = true)
      (hrc : reply.msg.rcode = RCode.nameError)
      (htc : reply.msg.tc = false)
      (cf0 : Cache)
      (hcf0 : WriteRefines now cf0 (c.absorbNeg now pq reply.msg) ∨ cf0 = c)
      (cf : Cache)
      (hcf : NegWriteRefines now cf cf0) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c (addr :: rest) q [] [] now cf
        { reply.msg with aa := false }

  | exhausted {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (q : Query) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c [] q [] [] now c
        { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }

  | gaveUp {now : Time} {nseen : List Name} {seen : List Name} (c : Cache) (slist : List String)
      (q : Query)
      (hw : GaveUpWitness now c slist q) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q [] [] now c
        { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }

  | loopDetected {now : Time} {nseen : List Name} {seen : List Name} (c : Cache)
      (slist : List String) (q : Query) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q [] [] now c
        { aa := false, rcode := RCode.servFail, answer := [], authority := [], additional := [] }

  | chooseServer {now : Time} {nseen : List Name} {seen : List Name}
      (slist slist' : List String) (q : Query) (ftr : List Step) (rpath : List String)
      (tEnd : Time) (final : Response) (c cout : Cache)
      (hperm : slist'.Perm slist)
      (hrec : Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist' q ftr rpath tEnd cout final) :
      Resolves net ns resolverAddr ednsBuf rttOf now nseen seen c slist q ftr rpath tEnd cout final
rfc_proves VeriDNS.Spec.Net.Resolves [1034][2565:2707]
rfc_proves VeriDNS.Spec.Net.Resolves [9156][342:350]
rfc_proves VeriDNS.Spec.Net.Resolves [8020][159:165]

theorem resolves_time_monotone {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat} {now : Time}
    {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) : now ≤ tEnd := by
  induction h with
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hmsg href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      exact Nat.le_trans hmono ih
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hmsg href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      exact Nat.le_trans hmono ih
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hmsg hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      exact Nat.le_trans hmono ih
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      exact Nat.le_trans hmono ih
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih =>
      exact Nat.le_trans hmono ih
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      exact ihRec
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih => exact ih
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      exact Nat.le_trans hmono ih
  | _ => exact Nat.le_refl _

theorem delegation_bailiwick_fresh {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat} {now : Time}
    {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    now ≤ tEnd := resolves_time_monotone h
rfc_proves VeriDNS.Spec.Net.delegation_bailiwick_fresh [1034][1705:1712]

theorem resolves_rd_irrelevant {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} (b : Bool) {now : Time} {nseen : List Name} {seen : List Name}
    {c : Cache} {slist : List String} {q : Query} {tr : List Step} {path : List String}
    {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    Resolves net ns ra ednsBuf rttOf now nseen seen c slist {q with rd := b} tr path tEnd cout resp := by
  induction h with
  | cacheHit c slist q here hhit hne => exact Resolves.cacheHit c slist {q with rd := b} here hhit hne
  | negHit c slist q hneg => exact Resolves.negHit c slist {q with rd := b} hneg
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>
      exact Resolves.trustedReply addr origin rest {q with rd := b} id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      exact Resolves.answer addr rest {q with rd := b} srv tr resp id srcPort c hmiss hnmiss hfind
        (serverAnswers_rd_irrelevant b hans) reply htrans hacc hwire hnr hnc htc
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      exact Resolves.refer addr rest {q with rd := b} pq srv tr ref ftr rpath tEnd final id srcPort c cout
        hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail
        frontier hdesc hdescF hglue hfresh hmono sl hsl ih
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      exact Resolves.referForget addr rest {q with rd := b} pq srv tr ref ftr rpath tEnd final id srcPort c cout
        hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail
        frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf ih
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      exact Resolves.trustedReferral addr origin rest {q with rd := b} pq frontier ftr rpath tEnd final id srcPort c cout
        hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf ih
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      exact Resolves.answerCname addr rest {q with rd := b} srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
        hmiss hnmiss hfind (serverAnswers_rd_irrelevant b hans) reply htrans hacc hwire hcn hqt htgt
        hfresh hmono htc cf0 hcf0 cf hcf ih
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      exact Resolves.trustedCname addr origin rest {q with rd := b} cn target id srcPort c nsl ftr rpath tEnd cout final
        hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      exact Resolves.cacheCname slist {q with rd := b} cn target c nsl ftr rpath tEnd cout final
        hmiss hnmiss hcn hqt htgt hfresh cf hcf ih
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih =>
      exact Resolves.timeout addr rest {q with rd := b} ftr rpath tEnd final c cout d hdrop hmono ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih =>
      exact Resolves.skipMissing addr rest {q with rd := b} ftr rpath tEnd final c cout hfind ih
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      exact Resolves.gluelessNs {q with rd := b} zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
        slist2 ftr rpath tEnd final c c2 cout
        hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f ihRec
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih =>
      exact Resolves.rejectSpoof addr rest {q with rd := b} pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih =>
      exact Resolves.badResponse addr rest {q with rd := b} pq ftr rpath tEnd final c cout id srcPort reply
        hprobe htrans hacc hbad ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply
      hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih =>
      exact Resolves.unfollowableReferral addr rest {q with rd := b} pq srv tr ref id srcPort ftr rpath tEnd
        final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href
        hunfollow ih
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      exact Resolves.ancestorDenied addr origin rest {q with rd := b} pq id srcPort c reply hmiss hnmiss
        hprobe htrans hacc hrc htc cf0 hcf0 cf hcf
  | exhausted c q => exact Resolves.exhausted c {q with rd := b}
  | gaveUp c slist q hw => exact Resolves.gaveUp c slist {q with rd := b} (hw.rd b)
  | loopDetected c slist q => exact Resolves.loopDetected c slist {q with rd := b}
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih =>
      exact Resolves.chooseServer slist slist' {q with rd := b} ftr rpath tEnd final c cout hperm ih
rfc_proves VeriDNS.Spec.Net.resolves_rd_irrelevant [1034][1212:1248]

theorem accepts_off_path_false (out reply : Datagram)
    (h : (out.id == reply.id) = false ∨ (out.srcPort == reply.dstPort) = false
      ∨ nameEqCS out.qname reply.qname = false) :
    accepts out reply = false := by
  rcases h with h | h | h <;> simp [accepts, h]
rfc_proves VeriDNS.Spec.Net.accepts_off_path_false [5452][258:278]

theorem onWire_accepted_honest (out : Datagram) (honest : Response) (reply : Datagram)
    (hw : OnWire out honest reply) (hacc : accepts out reply = true) :
    reply.msg = honest := by
  cases hw with
  | fromServer => rfl
  | offPath d hblind =>
      rw [accepts_off_path_false out reply hblind] at hacc
      exact absurd hacc (by decide)
rfc_proves VeriDNS.Spec.Net.onWire_accepted_honest [5452][258:278]

theorem accepted_needs_full_secret (ra addr : String) (q : Query) (id srcPort ednsBuf : Nat)
    (reply : Datagram) (hacc : accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true) :
    id = reply.id ∧ srcPort = reply.dstPort := by
  obtain ⟨hid, _, hport, _, _, _⟩ := accepts_requires_match _ reply hacc
  simp only [queryDatagram, beq_iff_eq] at hid hport
  exact ⟨hid, hport⟩
rfc_proves VeriDNS.Spec.Net.accepted_needs_full_secret [5452][258:278]

theorem blind_match_unique (ra addr : String) (q : Query) (d : Datagram)
    (id₁ p₁ id₂ p₂ ednsBuf : Nat)
    (h₁ : accepts (queryDatagram id₁ ra addr p₁ ednsBuf q) d = true)
    (h₂ : accepts (queryDatagram id₂ ra addr p₂ ednsBuf q) d = true) :
    id₁ = id₂ ∧ p₁ = p₂ := by
  obtain ⟨e1, e1'⟩ := accepted_needs_full_secret ra addr q id₁ p₁ ednsBuf d h₁
  obtain ⟨e2, e2'⟩ := accepted_needs_full_secret ra addr q id₂ p₂ ednsBuf d h₂
  exact ⟨e1.trans e2.symm, e1'.trans e2'.symm⟩
rfc_proves VeriDNS.Spec.Net.blind_match_unique [5452][258:278]

rfc_proves VeriDNS.Spec.Net.blind_match_unique [5452][354:367]
rfc_proves VeriDNS.Spec.Net.accepted_needs_full_secret [5452][514:546]

theorem resolves_data_needs_acceptance {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat} {now : Time}
    {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    CacheRefines cout c ∨ ∃ (out reply : Datagram) (honest : Response),
      accepts out reply = true ∧ reply.msg = honest := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      exact Or.inr ⟨_, reply, _, hacc, rfl⟩
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      exact Or.inr ⟨_, reply, _, hacc, onWire_accepted_honest _ _ _ hwire hacc⟩
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      exact Or.inr ⟨_, reply, _, hacc, onWire_accepted_honest _ _ _ hwire hacc⟩
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      exact Or.inr ⟨_, reply, _, hacc, onWire_accepted_honest _ _ _ hwire hacc⟩
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      exact Or.inr ⟨_, reply, _, hacc, rfl⟩
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      exact Or.inr ⟨_, reply, _, hacc, onWire_accepted_honest _ _ _ hwire hacc⟩
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      exact Or.inr ⟨_, reply, _, hacc, rfl⟩
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>

      exact Or.inr ⟨_, reply, _, hacc, rfl⟩
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>

      rcases ihRec with h1 | h1
      · rcases ihNs with h2 | h2
        · exact Or.inl ((h1.trans hc2f).trans h2)
        · exact Or.inr h2
      · exact Or.inr h1
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => exact ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      rcases ih with h1 | h1
      · exact Or.inl (h1.trans hcf)
      · exact Or.inr h1
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
  | _ => exact Or.inl (CacheRefines.refl _)
rfc_proves VeriDNS.Spec.Net.resolves_data_needs_acceptance [5452][258:278]

theorem offpath_cannot_cache {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat} {now : Time}
    {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp)
    (hchg : ¬ CacheRefines cout c) :
    ∃ (out reply : Datagram) (honest : Response), accepts out reply = true
      ∧ (out.id == reply.id) = true ∧ (out.srcPort == reply.dstPort) = true
      ∧ reply.msg = honest := by
  rcases resolves_data_needs_acceptance h with hc | ⟨out, reply, honest, hacc, hbody⟩
  · exact absurd hc hchg
  · obtain ⟨hid, _, hport, _, _, _⟩ := accepts_requires_match out reply hacc
    exact ⟨out, reply, honest, hacc, hid, hport, hbody⟩
rfc_proves VeriDNS.Spec.Net.offpath_cannot_cache [5452][258:278]

rfc_proves VeriDNS.Spec.Net.offpath_cannot_cache [5452][491:512]
rfc_proves VeriDNS.Spec.Net.offpath_cannot_cache [5452][466:487]

theorem absorbNeg_pos (c : Cache) (now : Time) (q : Query) (resp : Response) :
    (c.absorbNeg now q resp).pos = c.pos := by
  unfold Cache.absorbNeg
  repeat' split
  all_goals rfl

theorem absorbNeg_matching (c : Cache) (now : Time) (q : Query) (resp : Response)
    (now' : Time) (q' : Query) :
    (c.absorbNeg now q resp).matching now' q' = c.matching now' q' := by
  unfold Cache.matching; rw [absorbNeg_pos]

theorem absorbNeg_topServed (c : Cache) (now : Time) (q : Query) (resp : Response)
    (now' : Time) (q' : Query) :
    (c.absorbNeg now q resp).topServed now' q' = c.topServed now' q' := by
  unfold Cache.topServed; rw [absorbNeg_matching]

def TrustedReferralCache (ra : String) (ednsBuf : Nat) (r : RR) : Prop :=
  ∃ (addr : String) (id srcPort : Nat) (q : Query) (reply : Datagram),
    accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true
    ∧ reply.msg.isReferral = true
    ∧ isAncestor (referralCut reply.msg) q.qname = true
    ∧ isAncestor (referralCut reply.msg) r.owner = true

def TrustedCnameCache (ra : String) (ednsBuf : Nat) (r : RR) : Prop :=
  ∃ (addr : String) (id srcPort : Nat) (q : Query) (reply : Datagram),
    accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true
    ∧ (cnameRR q.qname reply.msg.answer).isSome = true
    ∧ nameEq r.owner q.qname = true

def TrustedReplyCache (ra : String) (ednsBuf : Nat) (r : RR) : Prop :=
  ∃ (addr : String) (id srcPort : Nat) (q : Query) (reply : Datagram),
    accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true
    ∧ reply.msg.isReferral = false
    ∧ nameEq r.owner q.qname = true

theorem resolves_cache_in_bailiwick {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat} {now : Time}
    {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ now' q', ∀ e ∈ cout.topServed now' q', (∃ n2 q2, e ∈ c.topServed n2 q2) ∨
      (∃ srv ∈ net.servers, ∃ (qn : Name) (qc : RRClass),
        isAncestor (serverBailiwick srv qn qc) e.rr.owner = true)
      ∨ TrustedReferralCache ra ednsBuf e.rr ∨ TrustedCnameCache ra ednsBuf e.rr
      ∨ TrustedReplyCache ra ednsBuf e.rr := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro now' q' e he
      obtain ⟨n3, h3⟩ := hcf.2.1 now' q' e he
      rcases hcf0 with hw | rfl
      · obtain ⟨n4, h4⟩ := hw.2.1 n3 q' e h3
        rw [absorbNeg_topServed] at h4
        exact Or.inl ⟨n4, q', h4⟩
      · exact Or.inl ⟨n3, q', h3⟩
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro now' q' e he
      rw [absorbNeg_topServed] at he
      rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ he with h' | h'
      · exact Or.inl ⟨now', q', h'⟩
      · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q.qname, q.qclass, h'⟩)
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro now' q' e he
      rcases ih now' q' e he with ⟨n2, q2, h'⟩ | h'
      · rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h' with h'' | h''
        · exact Or.inl ⟨n2, q2, h''⟩
        · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q.qname, q.qclass,
            isAncestor_trans (isAncestor_absorbBailiwick _ _) h''⟩)
      · exact Or.inr h'
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' e he
      rcases ih now' q' e he with ⟨n2, q2, h'⟩ | h'
      ·
        obtain ⟨n3, h3⟩ := hcf.2.1 n2 q2 e h'
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
        rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h'' | h''
        · exact Or.inl ⟨n4, q2, h''⟩
        · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q.qname, q.qclass,
            isAncestor_trans (isAncestor_absorbBailiwick _ _) h''⟩)
      · exact Or.inr h'
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' e he
      rcases ih now' q' e he with ⟨n2, q2, h'⟩ | h'
      · obtain ⟨n3, h3⟩ := hcf.2.1 n2 q2 e h'
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
        rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h'' | h''
        · exact Or.inl ⟨n4, q2, h''⟩
        · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q.qname, q.qclass,
            isAncestor_trans (serverBailiwick_covers_qname srv q.qname q.qclass) h''⟩)
      · exact Or.inr h'
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' e he
      rcases ih now' q' e he with ⟨n2, q2, h'⟩ | h'
      · obtain ⟨n3, h3⟩ := hcf.2.1 n2 q2 e h'
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
        rcases absorb_cnameOwned_topServed_owner _ _ _ _ _ _ _ h4 with h'' | h''
        · exact Or.inl ⟨n4, q2, h''⟩
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc,
            (by rw [hcn]; rfl), h''⟩)))
      · exact Or.inr h'
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>
      intro now' q' e he

      obtain ⟨n3, h3⟩ := hcf.2.1 now' q' e he
      rcases hcf0 with hw | rfl
      · obtain ⟨n4, h4⟩ := hw.2.1 n3 q' e h3
        rcases absorb_answerOwned_topServed_owner _ _ _ _ _ _ _ h4 with h'' | h''
        · exact Or.inl ⟨n4, q', h''⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨addr, id, srcPort, q, reply, hacc, hnr, h''⟩)))
      · exact Or.inl ⟨n3, q', h3⟩
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>

      intro now' q' e he
      rcases ihRec now' q' e he with ⟨n2, q2, h'⟩ | h'
      · exact ihNs n2 q2 e ((hc2f.1 n2 q2).subset h')
      · exact Or.inr h'
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => exact ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro now' q' e he
      rcases ih now' q' e he with ⟨n2, q2, h'⟩ | h'
      · exact Or.inl ⟨n2, q2, (hcf.1 n2 q2).subset h'⟩
      · exact Or.inr h'
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' e he
      rcases ih now' q' e he with ⟨n2, q2, h'⟩ | h'
      · obtain ⟨n3, h3⟩ := hcf.2.1 n2 q2 e h'
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
        rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h'' | h''
        · exact Or.inl ⟨n4, q2, h''⟩
        ·
          refine Or.inr (Or.inr (Or.inl ⟨addr, id, srcPort, pq, reply, hacc, href, hcut, ?_⟩))
          rwa [absorbBailiwick_of_descendsBelow frontier reply.msg hdesc] at h''
      · exact Or.inr h'
  | _ => intro now' q' e he; exact Or.inl ⟨now', q', he⟩
rfc_proves VeriDNS.Spec.Net.resolves_cache_in_bailiwick [5452][258:278]

def RR.eqData (a b : RR) : Prop :=
  nameEq a.owner b.owner = true ∧ a.rdata = b.rdata ∧ a.cls = b.cls
rfc_proves VeriDNS.Spec.Net.RR.eqData [1035][1602:1614]

theorem RR.eqData_refl (a : RR) : RR.eqData a a := ⟨nameEq_refl _, rfl, rfl⟩

theorem RR.eqData_trans {a b c : RR} (h1 : RR.eqData a b) (h2 : RR.eqData b c) : RR.eqData a c :=
  ⟨nameEq_trans h1.1 h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem hit_eqData {c : Cache} {now : Time} {q : Query} {r : RR} (hr : r ∈ c.hit now q) :
    ∃ e ∈ c.pos, RR.eqData r e.rr := by
  unfold Cache.hit Cache.served Cache.matching at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, hre⟩ := hr
  rw [List.mem_filter, List.mem_filter] at he
  refine ⟨e, he.1.1, ?_⟩
  rw [← hre]
  exact ⟨nameEq_refl _, rfl, rfl⟩

theorem cnameAt_eqData {c : Cache} {now : Time} {qname : Name} {qcls : RRClass} {cn : RR}
    (h : c.cnameAt now qname qcls = some cn) : ∃ e ∈ c.pos, RR.eqData cn e.rr := by
  unfold Cache.cnameAt at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, he, hcn⟩ := h
  refine ⟨e, (List.mem_filter.mp (List.mem_of_head? he)).1, ?_⟩
  rw [← hcn]; exact ⟨nameEq_refl _, rfl, rfl⟩

theorem cnameServed_eqData {c : Cache} {now : Time} {qname : Name} {qcls : RRClass} {cn : RR}
    (h : cn ∈ c.cnameServed now qname qcls) : ∃ e ∈ c.pos, RR.eqData cn e.rr := by
  unfold Cache.cnameServed at h
  rw [List.mem_filterMap] at h
  obtain ⟨e, he, hcn⟩ := h
  have hpos : e ∈ c.pos := by
    have h1 : e ∈ c.matching now ⟨qname, QType.rr RRType.cname, qcls, false⟩ :=
      (List.mem_filter.mp he).1
    unfold Cache.matching at h1
    exact (List.mem_filter.mp h1).1
  refine ⟨e, hpos, ?_⟩
  split at hcn
  · injection hcn with hcn; rw [← hcn]; exact ⟨nameEq_refl _, rfl, rfl⟩
  · exact absurd hcn (by simp)

theorem packFit_subset (budget : Nat) (r : RR) :
    ∀ (xs : List RR) (st : Nat × List (Name × Nat)), r ∈ packFit budget st xs → r ∈ xs := by
  intro xs
  induction xs with
  | nil => intro st h; simp [packFit] at h
  | cons x xs ih =>
      intro st h
      simp only [packFit] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih _ h')
      · simp at h

theorem truncateToCap_answer_mem {cap : Nat} {q : Query} {resp : Response} {r : RR}
    (h : r ∈ (truncateToCap cap q resp).1.answer) : r ∈ resp.answer := by
  unfold truncateToCap at h
  split at h
  · exact packFit_subset cap r resp.answer (msgHdrQ q) h
  · exact h

theorem truncateToCap_sections_mem {cap : Nat} {q : Query} {resp : Response} {r : RR}
    (h : r ∈ (truncateToCap cap q resp).1.answer ++ (truncateToCap cap q resp).1.authority
            ++ (truncateToCap cap q resp).1.additional) :
    r ∈ resp.answer ++ resp.authority ++ resp.additional := by
  unfold truncateToCap at h
  split at h
  · simp only [List.append_nil] at h
    simp only [List.mem_append]
    exact Or.inl (Or.inl (packFit_subset cap r resp.answer (msgHdrQ q) h))
  · exact h

theorem absorb_pos_provenance (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (e : CacheRR) (he : e ∈ (c.absorb now bw resp).pos) :
    e ∈ c.pos ∨ ∃ r' ∈ resp.answer ++ resp.authority ++ resp.additional, RR.eqData e.rr r' := by
  have step : ∀ (xs : List RR) (cr : Cred) (acc : Cache),
      e ∈ ((normalizeTTL (xs.filter (fun r => isAncestor bw r.owner))).foldl
            (fun a r => a.insert now cr r) acc).pos →
      e ∈ acc.pos ∨ ∃ r' ∈ xs, RR.eqData e.rr r' := by
    intro xs cr acc h
    rcases mem_foldl_insert_pos _ acc h with h' | h'
    · exact Or.inl h'
    · obtain ⟨r, hr, hown, hrd, hcl⟩ := fields_of_mem_normalizeTTL h'
      exact Or.inr ⟨r, (List.mem_filter.mp hr).1, ⟨by rw [hown]; exact nameEq_refl _, hrd, hcl⟩⟩
  unfold Cache.absorb at he
  rcases step _ _ _ he with h2 | h2
  · rcases step _ _ _ h2 with h1 | h1
    · rcases step _ _ _ h1 with h0 | h0
      · exact Or.inl h0
      · obtain ⟨r', hr', hd⟩ := h0
        exact Or.inr ⟨r', by simp only [List.mem_append]; exact Or.inr hr', hd⟩
    · obtain ⟨r', hr', hd⟩ := h1
      have hr'auth : r' ∈ resp.authority := (List.mem_filter.mp hr').1
      exact Or.inr ⟨r', by simp only [List.mem_append]; exact Or.inl (Or.inr hr'auth), hd⟩
  · obtain ⟨r', hr', hd⟩ := h2
    exact Or.inr ⟨r', by simp only [List.mem_append]; exact Or.inl (Or.inl hr'), hd⟩

theorem absorb_no_authority_soa (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (e : CacheRR) (he : e ∈ (c.absorb now bw resp).pos) (hsoa : e.rr.rdata.rtype = RRType.soa) :
    e ∈ c.pos ∨ (∃ r' ∈ resp.answer, RR.eqData e.rr r') ∨ (∃ r' ∈ resp.additional, RR.eqData e.rr r') := by
  have step : ∀ (xs : List RR) (cr : Cred) (acc : Cache),
      e ∈ ((normalizeTTL (xs.filter (fun r => isAncestor bw r.owner))).foldl
            (fun a r => a.insert now cr r) acc).pos →
      e ∈ acc.pos ∨ ∃ r' ∈ xs, RR.eqData e.rr r' := by
    intro xs cr acc h
    rcases mem_foldl_insert_pos _ acc h with h' | h'
    · exact Or.inl h'
    · obtain ⟨r, hr, hown, hrd, hcl⟩ := fields_of_mem_normalizeTTL h'
      exact Or.inr ⟨r, (List.mem_filter.mp hr).1, ⟨by rw [hown]; exact nameEq_refl _, hrd, hcl⟩⟩
  unfold Cache.absorb at he
  rcases step _ _ _ he with h2 | h2
  · rcases step _ _ _ h2 with h1 | h1
    · rcases step _ _ _ h1 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inr h0)
    ·
      obtain ⟨r', hr', hd⟩ := h1
      have hnsoa := (List.mem_filter.mp hr').2
      have hr'soa : r'.rdata.rtype = RRType.soa := by rw [← hd.2.1]; exact hsoa
      rw [hr'soa] at hnsoa; exact absurd hnsoa (by decide)
  · exact Or.inr (Or.inl h2)

def Grounded (net : Network) (c : Cache) (r : RR) : Prop :=
  (∃ e ∈ c.pos, RR.eqData r e.rr)
  ∨ (∃ srv ∈ net.servers, ∃ (q' : Query) (t : Time) (tr : List Step) (resp' : Response),
        ServerAnswers srv t [] true q' tr resp'
          ∧ ∃ r' ∈ resp'.answer ++ resp'.authority ++ resp'.additional, RR.eqData r r')
rfc_proves VeriDNS.Spec.Net.Grounded [1034][2565:2707]

theorem grounded_eqData {net : Network} {c : Cache} {a b : RR} (h : RR.eqData a b)
    (hb : Grounded net c b) : Grounded net c a := by
  rcases hb with ⟨e, he, hbe⟩ | ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', hbr⟩
  · exact Or.inl ⟨e, he, RR.eqData_trans h hbe⟩
  · exact Or.inr ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', RR.eqData_trans h hbr⟩

def TrustedReplyAnswer (ra : String) (ednsBuf : Nat) (r : RR) : Prop :=
  ∃ (addr : String) (id srcPort : Nat) (q : Query) (reply : Datagram),
    accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true
    ∧ r ∈ reply.msg.answer ++ reply.msg.authority ++ reply.msg.additional

def TrustedReplyNxdomain (ra : String) (ednsBuf : Nat) : Prop :=
  ∃ (addr : String) (id srcPort : Nat) (q : Query) (reply : Datagram),
    accepts (queryDatagram id ra addr srcPort ednsBuf q) reply = true
    ∧ reply.msg.rcode = RCode.nameError

theorem grounded_of_cache_grounded {net : Network} {c c' : Cache}
    (hc' : ∀ e ∈ c'.pos, Grounded net c e.rr) {r : RR} (h : Grounded net c' r) :
    Grounded net c r := by
  rcases h with ⟨e, he, hre⟩ | hs
  · rcases hc' e he with ⟨e0, he0, h0⟩ | ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', hr'eq⟩
    · exact Or.inl ⟨e0, he0, RR.eqData_trans hre h0⟩
    · exact Or.inr ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', RR.eqData_trans hre hr'eq⟩
  · exact Or.inr hs

theorem absorb_entries_grounded {net : Network} {c : Cache} {now : Time} {bw : Name}
    (body : Response)
    (hmap : ∀ r' ∈ body.answer ++ body.authority ++ body.additional, Grounded net c r') :
    ∀ e ∈ (c.absorb now bw body).pos, Grounded net c e.rr := by
  intro e he
  rcases absorb_pos_provenance c now bw body e he with h | ⟨r', hr', hd⟩
  · exact Or.inl ⟨e, h, RR.eqData_refl _⟩
  · exact grounded_eqData hd (hmap r' hr')

theorem absorb_topServed_or_response (c : Cache) (now : Time) (bw : Name) (body : Response)
    (n : Time) (q : Query) (e : CacheRR)
    (he : e ∈ (c.absorb now bw body).topServed n q) :
    e ∈ c.topServed n q ∨ ∃ r' ∈ body.answer ++ body.authority ++ body.additional, RR.eqData e.rr r' := by
  unfold Cache.topServed at he
  rw [List.mem_filter] at he
  obtain ⟨hmem, hmax⟩ := he
  have hpos : e ∈ (c.absorb now bw body).pos := (List.mem_filter.mp hmem).1
  rcases absorb_pos_provenance c now bw body e hpos with hc | hbody
  · left
    have hkey := (List.mem_filter.mp hmem).2
    have hcm : e ∈ c.matching n q := by
      unfold Cache.matching; rw [List.mem_filter]; exact ⟨hc, hkey⟩
    have hsub : ∀ x ∈ c.matching n q, x ∈ (c.absorb now bw body).matching n q := by
      intro x hx
      have hx' := List.mem_filter.mp hx
      unfold Cache.matching; rw [List.mem_filter]
      exact ⟨absorb_pos_mono c now bw body x hx'.1, hx'.2⟩
    unfold Cache.topServed; rw [List.mem_filter]
    refine ⟨hcm, ?_⟩
    simp only [List.all_eq_true] at hmax ⊢
    intro x hx; exact hmax x (hsub x hx)
  · exact Or.inr hbody

theorem hit_topServed_eqData {c : Cache} {now : Time} {q : Query} {r : RR}
    (hr : r ∈ c.hit now q) : ∃ e ∈ c.topServed now q, RR.eqData r e.rr := by
  unfold Cache.hit at hr
  rw [List.mem_map] at hr
  obtain ⟨e, hes, hre⟩ := hr
  rw [c.served_eq_topServed_filter] at hes
  refine ⟨e, (List.mem_filter.mp hes).1, ?_⟩
  rw [← hre]; exact ⟨nameEq_refl _, rfl, rfl⟩

theorem cnameServed_topServed_eqData {c : Cache} {now : Time} {qname : Name} {qcls : RRClass} {cn : RR}
    (h : cn ∈ c.cnameServed now qname qcls) :
    ∃ e ∈ c.topServed now ⟨qname, QType.rr RRType.cname, qcls, false⟩, RR.eqData cn e.rr := by
  unfold Cache.cnameServed at h
  rw [List.mem_filterMap] at h
  obtain ⟨e, he, hcn⟩ := h
  rw [c.served_eq_topServed_filter] at he
  refine ⟨e, (List.mem_filter.mp he).1, ?_⟩
  split at hcn
  · injection hcn with hcn; rw [← hcn]; exact ⟨nameEq_refl _, rfl, rfl⟩
  · exact absurd hcn (by simp)

def GroundedServed (net : Network) (c : Cache) (r : RR) : Prop :=
  (∃ (n : Time) (q : Query) (e : CacheRR), e ∈ c.topServed n q ∧ RR.eqData r e.rr)
  ∨ (∃ srv ∈ net.servers, ∃ (q' : Query) (t : Time) (tr : List Step) (resp' : Response),
        ServerAnswers srv t [] true q' tr resp'
          ∧ ∃ r' ∈ resp'.answer ++ resp'.authority ++ resp'.additional, RR.eqData r r')

theorem groundedServed_eqData {net : Network} {c : Cache} {a b : RR} (h : RR.eqData a b)
    (hb : GroundedServed net c b) : GroundedServed net c a := by
  rcases hb with ⟨n, q, e, he, hbe⟩ | ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', hbr⟩
  · exact Or.inl ⟨n, q, e, he, RR.eqData_trans h hbe⟩
  · exact Or.inr ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', RR.eqData_trans h hbr⟩

theorem groundedServed_of_cache_groundedServed {net : Network} {c c' : Cache}
    (hc' : ∀ (n : Time) (q : Query), ∀ e ∈ c'.topServed n q, GroundedServed net c e.rr)
    {r : RR} (h : GroundedServed net c' r) : GroundedServed net c r := by
  rcases h with ⟨n, q, e, he, hre⟩ | hs
  · rcases hc' n q e he with ⟨n0, q0, e0, he0, h0⟩ | ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', hr'eq⟩
    · exact Or.inl ⟨n0, q0, e0, he0, RR.eqData_trans hre h0⟩
    · exact Or.inr ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', RR.eqData_trans hre hr'eq⟩
  · exact Or.inr hs

theorem absorb_topServed_groundedServed {net : Network} {c : Cache} {now : Time} {bw : Name}
    (body : Response)
    (hmap : ∀ r' ∈ body.answer ++ body.authority ++ body.additional, GroundedServed net c r') :
    ∀ (n : Time) (q : Query), ∀ e ∈ (c.absorb now bw body).topServed n q, GroundedServed net c e.rr := by
  intro n q e he
  rcases absorb_topServed_or_response c now bw body n q e he with h | ⟨r', hr', hd⟩
  · exact Or.inl ⟨n, q, e, h, RR.eqData_refl _⟩
  · exact groundedServed_eqData hd (hmap r' hr')

def GroundedServedF (net : Network) (ra : String) (ednsBuf : Nat) (c : Cache) (r : RR) : Prop :=
  GroundedServed net c r ∨ TrustedReferralCache ra ednsBuf r ∨ TrustedCnameCache ra ednsBuf r
    ∨ TrustedReplyCache ra ednsBuf r

theorem groundedServed_of_refines {net : Network} {cf c : Cache} (hcf : CacheRefines cf c)
    {r : RR} (h : GroundedServed net cf r) : GroundedServed net c r := by
  rcases h with ⟨n, q, e, he, hre⟩ | hs
  · exact Or.inl ⟨n, q, e, (hcf.1 n q).subset he, hre⟩
  · exact Or.inr hs

theorem trustedReferralCache_eqData {ra : String} {ednsBuf : Nat} {r r' : RR}
    (h : TrustedReferralCache ra ednsBuf r') (he : RR.eqData r r') :
    TrustedReferralCache ra ednsBuf r := by
  obtain ⟨addr, id, srcPort, pq, reply, hacc, href, hcut, howner⟩ := h
  exact ⟨addr, id, srcPort, pq, reply, hacc, href, hcut,
    isAncestor_congr_right howner ((nameEq_symm r.owner r'.owner) ▸ he.1)⟩

theorem trustedCnameCache_eqData {ra : String} {ednsBuf : Nat} {r r' : RR}
    (h : TrustedCnameCache ra ednsBuf r') (he : RR.eqData r r') :
    TrustedCnameCache ra ednsBuf r := by
  obtain ⟨addr, id, srcPort, q, reply, hacc, hcn, howner⟩ := h
  exact ⟨addr, id, srcPort, q, reply, hacc, hcn, nameEq_trans he.1 howner⟩

theorem trustedReplyCache_eqData {ra : String} {ednsBuf : Nat} {r r' : RR}
    (h : TrustedReplyCache ra ednsBuf r') (he : RR.eqData r r') :
    TrustedReplyCache ra ednsBuf r := by
  obtain ⟨addr, id, srcPort, q, reply, hacc, hnr, howner⟩ := h
  exact ⟨addr, id, srcPort, q, reply, hacc, hnr, nameEq_trans he.1 howner⟩

theorem groundedServedF_of_cache {net : Network} {ra : String} {ednsBuf : Nat} {c c' : Cache}
    (hc' : ∀ (n : Time) (q : Query), ∀ e ∈ c'.topServed n q, GroundedServedF net ra ednsBuf c e.rr)
    {r : RR} (h : GroundedServedF net ra ednsBuf c' r) : GroundedServedF net ra ednsBuf c r := by
  rcases h with hg | ht
  · rcases hg with ⟨n, q, e, he, hre⟩ | hs
    · rcases hc' n q e he with hg0 | ht0 | ht0 | ht0
      · rcases hg0 with ⟨n0, q0, e0, he0, h0⟩ | ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', hr'eq⟩
        · exact Or.inl (Or.inl ⟨n0, q0, e0, he0, RR.eqData_trans hre h0⟩)
        · exact Or.inl (Or.inr ⟨srv, hsrv, q', t, tr, resp', hans, r', hr', RR.eqData_trans hre hr'eq⟩)
      · exact Or.inr (Or.inl (trustedReferralCache_eqData ht0 hre))
      · exact Or.inr (Or.inr (Or.inl (trustedCnameCache_eqData ht0 hre)))
      · exact Or.inr (Or.inr (Or.inr (trustedReplyCache_eqData ht0 hre)))
    · exact Or.inl (Or.inr hs)
  · exact Or.inr ht

theorem groundedServedF_eqData {net : Network} {ra : String} {ednsBuf : Nat} {c : Cache} {a b : RR}
    (h : RR.eqData a b) (hb : GroundedServedF net ra ednsBuf c b) :
    GroundedServedF net ra ednsBuf c a := by
  rcases hb with hg | ht | ht | ht
  · exact Or.inl (groundedServed_eqData h hg)
  · exact Or.inr (Or.inl (trustedReferralCache_eqData ht h))
  · exact Or.inr (Or.inr (Or.inl (trustedCnameCache_eqData ht h)))
  · exact Or.inr (Or.inr (Or.inr (trustedReplyCache_eqData ht h)))

theorem absorb_topServed_groundedServedF {net : Network} {ra : String} {ednsBuf : Nat} {c : Cache}
    {now : Time} {bw : Name} (body : Response)
    (hmap : ∀ r' ∈ body.answer ++ body.authority ++ body.additional, GroundedServedF net ra ednsBuf c r') :
    ∀ (n : Time) (q : Query), ∀ e ∈ (c.absorb now bw body).topServed n q, GroundedServedF net ra ednsBuf c e.rr := by
  intro n q e he
  rcases absorb_topServed_or_response c now bw body n q e he with h | ⟨r', hr', hd⟩
  · exact Or.inl (Or.inl ⟨n, q, e, h, RR.eqData_refl _⟩)
  · exact groundedServedF_eqData hd (hmap r' hr')

theorem resolves_cout_grounded {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ now' q', ∀ e ∈ cout.topServed now' q', GroundedServedF net ra ednsBuf c e.rr := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro now' q' e he
      obtain ⟨n3, h3⟩ := hcf.2.1 now' q' e he
      rcases hcf0 with hw | rfl
      · obtain ⟨n4, h4⟩ := hw.2.1 n3 q' e h3
        rw [absorbNeg_topServed] at h4
        exact Or.inl (Or.inl ⟨n4, q', e, h4, RR.eqData_refl _⟩)
      · exact Or.inl (Or.inl ⟨n3, q', e, h3, RR.eqData_refl _⟩)
  | cacheHit c slist q here hhit hne => intro now' q' e he; exact Or.inl (Or.inl ⟨now', q', e, he, RR.eqData_refl _⟩)
  | negHit c slist q hneg => intro now' q' e he; exact Or.inl (Or.inl ⟨now', q', e, he, RR.eqData_refl _⟩)
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>

      intro now' q' e he
      obtain ⟨n3, h3⟩ := hcf.2.1 now' q' e he
      rcases hcf0 with hw | rfl
      · obtain ⟨n4, h4⟩ := hw.2.1 n3 q' e h3
        rcases absorb_answerOwned_topServed_owner _ _ _ _ _ _ _ h4 with h' | h'
        · exact Or.inl (Or.inl ⟨n4, q', e, h', RR.eqData_refl _⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨addr, id, srcPort, q, reply, hacc, hnr, h'⟩))
      · exact Or.inl (Or.inl ⟨n3, q', e, h3, RR.eqData_refl _⟩)
  | exhausted c q => intro now' q' e he; exact Or.inl (Or.inl ⟨now', q', e, he, RR.eqData_refl _⟩)
  | gaveUp c slist q => intro now' q' e he; exact Or.inl (Or.inl ⟨now', q', e, he, RR.eqData_refl _⟩)
  | loopDetected c slist q =>
    intro now' q' e he; exact Or.inl (Or.inl ⟨now', q', e, he, RR.eqData_refl _⟩)
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro now' q' e he
      rw [absorbNeg_topServed] at he
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      refine absorb_topServed_groundedServedF reply.msg ?_ now' q' e he
      intro r' hr'
      rw [hmsg] at hr'
      exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r',
        truncateToCap_sections_mem hr', RR.eqData_refl _⟩)
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro now' q' e he
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      refine groundedServedF_of_cache ?_ (ih now' q' e he)
      intro n q2 e0 he0
      refine absorb_topServed_groundedServedF reply.msg ?_ n q2 e0 he0
      intro r' hr'; rw [hmsg] at hr'
      exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩)
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' e he
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      refine groundedServedF_of_cache ?_ (ih now' q' e he)
      intro n q2 e0 he0
      obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
      obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
      refine absorb_topServed_groundedServedF reply.msg ?_ n4 q2 e0 h4
      intro r' hr'; rw [hmsg] at hr'
      exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩)
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' e he
      refine groundedServedF_of_cache ?_ (ih now' q' e he)
      intro n q2 e0 he0
      obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
      obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
      rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h' | h'
      · exact Or.inl (Or.inl ⟨n4, q2, e0, h', RR.eqData_refl _⟩)
      ·
        refine Or.inr (Or.inl ⟨addr, id, srcPort, pq, reply, hacc, href, hcut, ?_⟩)
        rwa [absorbBailiwick_of_descendsBelow frontier reply.msg hdesc] at h'
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' e he
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      refine groundedServedF_of_cache ?_ (ih now' q' e he)
      intro n q2 e0 he0
      obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
      obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
      refine absorb_topServed_groundedServedF (reply.msg.cnameOwned q.qname) ?_ n4 q2 e0 h4
      intro r' hr'
      simp only [Response.cnameOwned_answer, Response.cnameOwned_authority,
        Response.cnameOwned_additional, List.append_nil, List.mem_filter] at hr'
      obtain ⟨hr', -⟩ := hr'
      rw [hmsg] at hr'
      exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r',
        truncateToCap_sections_mem (by simp only [List.mem_append]; exact Or.inl (Or.inl hr')),
        RR.eqData_refl _⟩)
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' e he
      refine groundedServedF_of_cache ?_ (ih now' q' e he)
      intro n q2 e0 he0
      obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
      obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
      rcases absorb_cnameOwned_topServed_owner _ _ _ _ _ _ _ h4 with h' | h'
      · exact Or.inl (Or.inl ⟨n4, q2, e0, h', RR.eqData_refl _⟩)
      ·
        exact Or.inr (Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, (by rw [hcn]; rfl), h'⟩))
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>

      intro now' q' e he
      refine groundedServedF_of_cache ?_ (ihRec now' q' e he)
      intro n q0 e0 he0
      exact ihNs n q0 e0 ((hc2f.1 n q0).subset he0)
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => exact ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro now' q' e he
      refine groundedServedF_of_cache ?_ (ih now' q' e he)
      intro n q0 e0 he0
      exact Or.inl (Or.inl ⟨n, q0, e0, (hcf.1 n q0).subset he0, RR.eqData_refl _⟩)
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
rfc_proves VeriDNS.Spec.Net.resolves_cout_grounded [1034][2565:2707]

theorem resolves_answer_grounded {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ r ∈ resp.answer, GroundedServed net c r ∨ TrustedReplyAnswer ra ednsBuf r
      ∨ TrustedReferralCache ra ednsBuf r ∨ TrustedCnameCache ra ednsBuf r
      ∨ TrustedReplyCache ra ednsBuf r := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro r hr
      have hr2 : r ∈ reply.msg.answer := hr
      exact Or.inr (Or.inl ⟨addr, id, srcPort, pq, reply, hacc, by
        simp only [List.mem_append]; exact Or.inl (Or.inl hr2)⟩)
  | cacheHit c slist q here hhit hne =>
      intro r hr
      have hr2 : r ∈ here := hr
      rw [← hhit] at hr2
      obtain ⟨e, he, heq⟩ := hit_topServed_eqData hr2
      exact Or.inl (Or.inl ⟨_, _, e, he, heq⟩)
  | negHit c slist q hneg => intro r hr; simp [Cache.negResponse] at hr
  | exhausted c q => intro r hr; simp at hr
  | gaveUp c slist q => intro r hr; simp at hr
  | loopDetected c slist q => intro r hr; simp at hr
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc =>
      intro r hr
      have hr2 : r ∈ reply.msg.answer := hr
      exact Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, by
        simp only [List.mem_append]; exact Or.inl (Or.inl hr2)⟩)
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hr2 : r ∈ reply.msg.answer := hr
      rw [hmsg] at hr2
      exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r,
        by simp only [List.mem_append]; exact Or.inl (Or.inl (truncateToCap_answer_mem hr2)),
        RR.eqData_refl _⟩)
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      rcases ih r hr with hg | ht
      · refine Or.inl (groundedServed_of_cache_groundedServed ?_ hg)
        intro n q2 e0 he0
        refine absorb_topServed_groundedServed reply.msg ?_ n q2 e0 he0
        intro r' hr'; rw [hmsg] at hr'
        exact Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩
      · exact Or.inr ht
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      rcases ih r hr with hg | ht
      · refine Or.inl (groundedServed_of_cache_groundedServed ?_ hg)
        intro n q2 e0 he0
        obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
        refine absorb_topServed_groundedServed reply.msg ?_ n4 q2 e0 h4
        intro r' hr'; rw [hmsg] at hr'
        exact Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩
      · exact Or.inr ht
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro r hr
      rcases ih r hr with hg | ht
      · rcases hg with ⟨n, q2, e, he, hre⟩ | hsrv
        · obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e he
          obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
          rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h' | h'
          · exact Or.inl (Or.inl ⟨n4, q2, e, h', hre⟩)
          · refine Or.inr (Or.inr (Or.inl (trustedReferralCache_eqData ⟨addr, id, srcPort, pq, reply, hacc, href, hcut, ?_⟩ hre)))
            rwa [absorbBailiwick_of_descendsBelow frontier reply.msg hdesc] at h'
        · exact Or.inl (Or.inr hsrv)
      · exact Or.inr ht
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hr2 : r ∈ cn :: final.answer := hr
      rcases List.mem_cons.mp hr2 with rfl | hrest
      · have hcnmem : r ∈ reply.msg.answer := List.mem_of_find?_eq_some hcn
        rw [hmsg] at hcnmem
        exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r,
          by simp only [List.mem_append]; exact Or.inl (Or.inl (truncateToCap_answer_mem hcnmem)),
          RR.eqData_refl _⟩)
      · rcases ih r hrest with hg | ht
        · refine Or.inl (groundedServed_of_cache_groundedServed ?_ hg)
          intro n q2 e0 he0
          obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
          obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
          refine absorb_topServed_groundedServed (reply.msg.cnameOwned q.qname) ?_ n4 q2 e0 h4
          intro r' hr'
          simp only [Response.cnameOwned_answer, Response.cnameOwned_authority,
            Response.cnameOwned_additional, List.append_nil, List.mem_filter] at hr'
          obtain ⟨hr', -⟩ := hr'
          rw [hmsg] at hr'
          exact Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r',
            truncateToCap_sections_mem (by simp only [List.mem_append]; exact Or.inl (Or.inl hr')), RR.eqData_refl _⟩
        · exact Or.inr ht
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro r hr
      have hr2 : r ∈ cn :: final.answer := hr
      rcases List.mem_cons.mp hr2 with rfl | hrest
      ·
        exact Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (List.mem_of_find?_eq_some hcn))⟩)
      · rcases ih r hrest with hg | ht
        · rcases hg with ⟨n, q2, e, he, hre⟩ | hsrv
          · obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e he
            obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
            rcases absorb_cnameOwned_topServed_owner _ _ _ _ _ _ _ h4 with h' | h'
            · exact Or.inl (Or.inl ⟨n4, q2, e, h', hre⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inl (trustedCnameCache_eqData
                ⟨addr, id, srcPort, q, reply, hacc, (by rw [hcn]; rfl), h'⟩ hre))))
          · exact Or.inl (Or.inr hsrv)
        · exact Or.inr ht
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      intro r hr

      rcases ihRec r hr with hg | ht
      · rcases groundedServedF_of_cache (resolves_cout_grounded hnsres)
          (Or.inl (groundedServed_of_refines hc2f hg)) with hgr | htrc
        · exact Or.inl hgr
        · exact Or.inr (Or.inr htrc)
      · exact Or.inr ht
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => exact ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · obtain ⟨e, he, heq⟩ := cnameServed_topServed_eqData hcn
        exact Or.inl (Or.inl ⟨_, _, e, he, heq⟩)
      · rcases ih r hrest with hg | ht
        · exact Or.inl (groundedServed_of_refines hcf hg)
        · exact Or.inr ht
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
rfc_proves VeriDNS.Spec.Net.resolves_answer_grounded [1034][2565:2707]

theorem truncateToCap_untrunc {cap : Nat} {q : Query} {resp : Response}
    (h : (truncateToCap cap q resp).1.tc = false) : (truncateToCap cap q resp).1 = resp := by
  unfold truncateToCap at h ⊢
  by_cases hc : Nat.blt cap (messageWire q resp) = true
  · simp only [hc, if_true] at h; exact absurd h (by simp)
  · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, if_false]

theorem rcode_eq_of_beq {a b : RCode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem foldl_insert_neg (now : Time) (cr : Cred) (xs : List RR) (acc : Cache) :
    ((xs.foldl (fun a r => a.insert now cr r) acc)).neg = acc.neg := by
  induction xs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      unfold Cache.insert
      split <;> rfl

theorem absorb_neg (c : Cache) (now : Time) (bw : Name) (resp : Response) :
    (c.absorb now bw resp).neg = c.neg := by
  unfold Cache.absorb
  rw [foldl_insert_neg, foldl_insert_neg, foldl_insert_neg]

theorem absorbNeg_neg_mem {c : Cache} {now : Time} {q : Query} {resp : Response} {e : NegRR}
    (he : e ∈ (c.absorbNeg now q resp).neg) :
    e ∈ c.neg
      ∨ (resp.rcode = RCode.nameError ∧ e.qtype = none)
      ∨ (resp.rcode = RCode.noError ∧ resp.answer = [] ∧ e.qtype = some q.qtype) := by
  unfold Cache.absorbNeg at he
  split at he
  · exact Or.inl he
  · split at he
    · rename_i hrc
      simp only [Bool.and_eq_true] at hrc
      rcases List.mem_cons.mp he with rfl | h
      · exact Or.inr (Or.inl ⟨rcode_eq_of_beq hrc.1, rfl⟩)
      · exact Or.inl h
    · split at he
      · rename_i hcond
        rcases List.mem_cons.mp he with rfl | h
        · simp only [Bool.and_eq_true] at hcond
          exact Or.inr (Or.inr ⟨rcode_eq_of_beq hcond.1, by simpa using hcond.2, rfl⟩)
        · exact Or.inl h
      · exact Or.inl he

theorem absorb_negHit_eq (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (now' : Time) (q' : Query) :
    (c.absorb now bw resp).negHit now' q' = c.negHit now' q' := by
  unfold Cache.negHit; rw [absorb_neg]

theorem absorbNeg_negHit (c : Cache) (now : Time) (q : Query) (resp : Response)
    (now' : Time) (q' : Query) (h : (c.absorbNeg now q resp).negHit now' q' = true) :
    c.negHit now' q' = true ∨ resp.rcode = RCode.nameError
      ∨ (resp.rcode = RCode.noError ∧ resp.answer = []) := by
  unfold Cache.negHit at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, hpred⟩ := h
  rcases absorbNeg_neg_mem he with h1 | h1 | h1
  · left; unfold Cache.negHit; rw [List.any_eq_true]; exact ⟨e, h1, hpred⟩
  · exact Or.inr (Or.inl h1.1)
  · exact Or.inr (Or.inr ⟨h1.1, h1.2.1⟩)

theorem resolves_negcache_grounded {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ now' q', cout.negHit now' q' = true → c.negHit now' q' = true ∨
      (∃ srv ∈ net.servers, ∃ (q'2 : Query) (t : Time) (tr' : List Step) (resp' : Response),
        ServerAnswers srv t [] true q'2 tr' resp' ∧
          (resp'.rcode = RCode.nameError ∨ (resp'.rcode = RCode.noError ∧ resp'.answer = [])))
      ∨ TrustedReplyNxdomain ra ednsBuf := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro now' q' hn
      have hn := hcf.2.2.1 now' q' hn
      rcases hcf0 with hw | rfl
      · rw [hw.2.2.1 now' q'] at hn
        rcases absorbNeg_negHit _ _ _ _ _ _ hn with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨addr, id, srcPort, pq, reply, hacc, hrc⟩)
        · rw [h1.1] at hrc; exact nomatch hrc
      · exact Or.inl hn
  | cacheHit c slist q here hhit hne => intro now' q' hn; exact Or.inl hn
  | negHit c slist q hneg => intro now' q' hn; exact Or.inl hn
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>

      intro now' q' hn
      rw [hcf.2.2.1 now' q'] at hn
      rcases hcf0 with hw | rfl
      · rw [hw.2.2.1 now' q', absorb_negHit_eq] at hn
        exact Or.inl hn
      · exact Or.inl hn
  | exhausted c q => intro now' q' hn; exact Or.inl hn
  | gaveUp c slist q => intro now' q' hn; exact Or.inl hn
  | loopDetected c slist q => intro now' q' hn; exact Or.inl hn
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro now' q' hn
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hfull : reply.msg = resp := by rw [hmsg]; exact truncateToCap_untrunc (by rw [← hmsg]; exact htc)
      rcases absorbNeg_negHit _ _ _ _ _ _ hn with h1 | h1 | h1
      · left; rw [absorb_negHit_eq] at h1; exact h1
      · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, Or.inl (by rw [hfull] at h1; exact h1)⟩)
      · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans,
          Or.inr (by rw [hfull] at h1; exact h1)⟩)
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [absorb_negHit_eq] at h1; exact h1
      · exact Or.inr h1
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.1 now' q', hcf0.2.2.1 now' q', absorb_negHit_eq] at h1; exact h1
      · exact Or.inr h1
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.1 now' q', hcf0.2.2.1 now' q', absorb_negHit_eq] at h1; exact h1
      · exact Or.inr h1
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.1 now' q', hcf0.2.2.1 now' q', absorb_negHit_eq] at h1; exact h1
      · exact Or.inr h1
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.1 now' q', hcf0.2.2.1 now' q', absorb_negHit_eq] at h1; exact h1
      · exact Or.inr h1
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      intro now' q' hn
      rcases ihRec now' q' hn with h1 | h1
      · rw [hc2f.2.1 now' q'] at h1
        exact ihNs now' q' h1
      · exact Or.inr h1
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => intro now' q' hn; exact ih now' q' hn
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => intro now' q' hn; exact ih now' q' hn
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => intro now' q' hn; exact ih now' q' hn
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => intro now' q' hn; exact ih now' q' hn
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => intro now' q' hn; exact ih now' q' hn
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.1 now' q'] at h1; exact h1
      · exact Or.inr h1
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => intro now' q' hn; exact ih now' q' hn
rfc_proves VeriDNS.Spec.Net.resolves_negcache_grounded [2308][464:471]

theorem resolves_response_grounded {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ r ∈ resp.answer ++ resp.authority ++ resp.additional,
      GroundedServed net c r ∨ TrustedReplyAnswer ra ednsBuf r
      ∨ TrustedReferralCache ra ednsBuf r ∨ TrustedCnameCache ra ednsBuf r
      ∨ TrustedReplyCache ra ednsBuf r := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro r hr
      exact Or.inr (Or.inl ⟨addr, id, srcPort, pq, reply, hacc, hr⟩)
  | cacheHit c slist q here hhit hne =>
      intro r hr
      have hr2 : r ∈ here := by simpa using hr
      rw [← hhit] at hr2
      obtain ⟨e, he, heq⟩ := hit_topServed_eqData hr2
      exact Or.inl (Or.inl ⟨_, _, e, he, heq⟩)
  | negHit c slist q hneg => intro r hr; simp [Cache.negResponse] at hr
  | exhausted c q => intro r hr; simp at hr
  | gaveUp c slist q => intro r hr; simp at hr
  | loopDetected c slist q => intro r hr; simp at hr
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc =>
      intro r hr
      exact Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, hr⟩)
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hr2 : r ∈ reply.msg.answer ++ reply.msg.authority ++ reply.msg.additional := hr
      rw [hmsg] at hr2
      exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r,
        truncateToCap_sections_mem hr2, RR.eqData_refl _⟩)
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      rcases ih r hr with hg | ht
      · refine Or.inl (groundedServed_of_cache_groundedServed ?_ hg)
        intro n q2 e0 he0
        refine absorb_topServed_groundedServed reply.msg ?_ n q2 e0 he0
        intro r' hr'; rw [hmsg] at hr'
        exact Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩
      · exact Or.inr ht
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      rcases ih r hr with hg | ht
      · refine Or.inl (groundedServed_of_cache_groundedServed ?_ hg)
        intro n q2 e0 he0
        obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
        refine absorb_topServed_groundedServed reply.msg ?_ n4 q2 e0 h4
        intro r' hr'; rw [hmsg] at hr'
        exact Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩
      · exact Or.inr ht
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro r hr
      rcases ih r hr with hg | ht
      · rcases hg with ⟨n, q2, e, he, hre⟩ | hsrv
        · obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e he
          obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
          rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h' | h'
          · exact Or.inl (Or.inl ⟨n4, q2, e, h', hre⟩)
          · refine Or.inr (Or.inr (Or.inl (trustedReferralCache_eqData ⟨addr, id, srcPort, pq, reply, hacc, href, hcut, ?_⟩ hre)))
            rwa [absorbBailiwick_of_descendsBelow frontier reply.msg hdesc] at h'
        · exact Or.inl (Or.inr hsrv)
      · exact Or.inr ht
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      simp only [List.cons_append] at hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · have hcnmem : r ∈ reply.msg.answer := List.mem_of_find?_eq_some hcn
        rw [hmsg] at hcnmem
        exact Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r,
          by simp only [List.mem_append]; exact Or.inl (Or.inl (truncateToCap_answer_mem hcnmem)),
          RR.eqData_refl _⟩)
      · rcases ih r hrest with hg | ht
        · refine Or.inl (groundedServed_of_cache_groundedServed ?_ hg)
          intro n q2 e0 he0
          obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
          obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
          refine absorb_topServed_groundedServed (reply.msg.cnameOwned q.qname) ?_ n4 q2 e0 h4
          intro r' hr'
          simp only [Response.cnameOwned_answer, Response.cnameOwned_authority,
            Response.cnameOwned_additional, List.append_nil, List.mem_filter] at hr'
          obtain ⟨hr', -⟩ := hr'
          rw [hmsg] at hr'
          exact Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, r',
            truncateToCap_sections_mem (by simp only [List.mem_append]; exact Or.inl (Or.inl hr')), RR.eqData_refl _⟩
        · exact Or.inr ht
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro r hr
      simp only [List.cons_append] at hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · exact Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (List.mem_of_find?_eq_some hcn))⟩)
      · rcases ih r hrest with hg | ht
        · rcases hg with ⟨n, q2, e, he, hre⟩ | hsrv
          · obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e he
            obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
            rcases absorb_cnameOwned_topServed_owner _ _ _ _ _ _ _ h4 with h' | h'
            · exact Or.inl (Or.inl ⟨n4, q2, e, h', hre⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inl (trustedCnameCache_eqData
                ⟨addr, id, srcPort, q, reply, hacc, (by rw [hcn]; rfl), h'⟩ hre))))
          · exact Or.inl (Or.inr hsrv)
        · exact Or.inr ht
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      intro r hr
      rcases ihRec r hr with hg | ht
      · rcases groundedServedF_of_cache (resolves_cout_grounded hnsres)
          (Or.inl (groundedServed_of_refines hc2f hg)) with hgr | htrc
        · exact Or.inl hgr
        · exact Or.inr (Or.inr htrc)
      · exact Or.inr ht
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => intro r hr; exact ih r hr
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => intro r hr; exact ih r hr
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => intro r hr; exact ih r hr
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => intro r hr; exact ih r hr
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => intro r hr; exact ih r hr
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro r hr
      simp only [List.cons_append] at hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · obtain ⟨e, he, heq⟩ := cnameServed_topServed_eqData hcn
        exact Or.inl (Or.inl ⟨_, _, e, he, heq⟩)
      · rcases ih r hrest with hg | ht
        · exact Or.inl (groundedServed_of_refines hcf hg)
        · exact Or.inr ht
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => intro r hr; exact ih r hr
rfc_proves VeriDNS.Spec.Net.resolves_response_grounded [1034][2565:2707]

theorem absorb_negHitNx_eq (c : Cache) (now : Time) (bw : Name) (resp : Response)
    (now' : Time) (q' : Query) :
    (c.absorb now bw resp).negHitNx now' q' = c.negHitNx now' q' := by
  unfold Cache.negHitNx; rw [absorb_neg]

theorem absorbNeg_negHitNx (c : Cache) (now : Time) (q : Query) (resp : Response)
    (now' : Time) (q' : Query) (h : (c.absorbNeg now q resp).negHitNx now' q' = true) :
    c.negHitNx now' q' = true ∨ resp.rcode = RCode.nameError := by
  unfold Cache.negHitNx at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, hpred⟩ := h
  rcases absorbNeg_neg_mem he with h1 | h1 | h1
  · left; unfold Cache.negHitNx; rw [List.any_eq_true]; exact ⟨e, h1, hpred⟩
  · exact Or.inr h1.1
  · exfalso
    simp only [Bool.and_eq_true, h1.2.2] at hpred
    exact absurd hpred.2 (by simp)

theorem resolves_negHitNx_justified {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ now' q', cout.negHitNx now' q' = true → c.negHitNx now' q' = true ∨
      (∃ srv ∈ net.servers, ∃ (q'2 : Query) (t : Time) (tr' : List Step) (resp' : Response),
        ServerAnswers srv t [] true q'2 tr' resp' ∧ resp'.rcode = RCode.nameError)
      ∨ TrustedReplyNxdomain ra ednsBuf := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro now' q' hn
      have hn := hcf.2.2.2 now' q' hn
      rcases hcf0 with hw | rfl
      · rw [hw.2.2.2 now' q'] at hn
        rcases absorbNeg_negHitNx _ _ _ _ _ _ hn with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨addr, id, srcPort, pq, reply, hacc, hrc⟩)
      · exact Or.inl hn
  | cacheHit c slist q here hhit hne => intro now' q' hn; exact Or.inl hn
  | negHit c slist q hneg => intro now' q' hn; exact Or.inl hn
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc cf0 hcf0 cf hcf =>

      intro now' q' hn
      rw [hcf.2.2.2 now' q'] at hn
      rcases hcf0 with hw | rfl
      · rw [hw.2.2.2 now' q', absorb_negHitNx_eq] at hn
        exact Or.inl hn
      · exact Or.inl hn
  | exhausted c q => intro now' q' hn; exact Or.inl hn
  | gaveUp c slist q => intro now' q' hn; exact Or.inl hn
  | loopDetected c slist q => intro now' q' hn; exact Or.inl hn
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro now' q' hn
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hfull : reply.msg = resp := by rw [hmsg]; exact truncateToCap_untrunc (by rw [← hmsg]; exact htc)
      rcases absorbNeg_negHitNx _ _ _ _ _ _ hn with h1 | h1
      · left; rw [absorb_negHitNx_eq] at h1; exact h1
      · exact Or.inr (Or.inl ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, by rw [hfull] at h1; exact h1⟩)
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [absorb_negHitNx_eq] at h1; exact h1
      · exact Or.inr h1
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.2 now' q', hcf0.2.2.2 now' q', absorb_negHitNx_eq] at h1; exact h1
      · exact Or.inr h1
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.2 now' q', hcf0.2.2.2 now' q', absorb_negHitNx_eq] at h1; exact h1
      · exact Or.inr h1
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.2 now' q', hcf0.2.2.2 now' q', absorb_negHitNx_eq] at h1; exact h1
      · exact Or.inr h1
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2.2 now' q', hcf0.2.2.2 now' q', absorb_negHitNx_eq] at h1; exact h1
      · exact Or.inr h1
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      intro now' q' hn
      rcases ihRec now' q' hn with h1 | h1
      · rw [hc2f.2.2 now' q'] at h1
        exact ihNs now' q' h1
      · exact Or.inr h1
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => intro now' q' hn; exact ih now' q' hn
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => intro now' q' hn; exact ih now' q' hn
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => intro now' q' hn; exact ih now' q' hn
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => intro now' q' hn; exact ih now' q' hn
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => intro now' q' hn; exact ih now' q' hn
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro now' q' hn
      rcases ih now' q' hn with h1 | h1
      · left; rw [hcf.2.2 now' q'] at h1; exact h1
      · exact Or.inr h1
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => intro now' q' hn; exact ih now' q' hn

theorem resolves_nxdomain_justified {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Time} {nseen : List Name} {seen : List Name} {c : Cache} {slist : List String}
    {q : Query} {tr : List Step} {path : List String} {tEnd : Time} {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    resp.rcode = RCode.nameError →
      (∃ srv ∈ net.servers, ∃ (q' : Query) (t : Time) (tr' : List Step) (resp' : Response),
          ServerAnswers srv t [] true q' tr' resp' ∧ resp'.rcode = RCode.nameError)
      ∨ (∃ now2 q2, c.negHitNx now2 q2 = true)
      ∨ TrustedReplyNxdomain ra ednsBuf := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro _
      exact Or.inr (Or.inr ⟨addr, id, srcPort, pq, reply, hacc, hrc⟩)
  | cacheHit c slist q here hhit hne => intro hrc; simp at hrc
  | negHit c slist q hneg =>
      intro hrc
      refine Or.inr (Or.inl ?_)
      simp only [Cache.negResponse] at hrc
      split at hrc
      · rename_i hnx; exact ⟨_, _, hnx⟩
      · exact absurd hrc (by simp)
  | exhausted c q => intro hrc; simp at hrc
  | gaveUp c slist q => intro hrc; simp at hrc
  | loopDetected c slist q => intro hrc; simp at hrc
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc =>
      intro hrc
      exact Or.inr (Or.inr ⟨addr, id, srcPort, q, reply, hacc, hrc⟩)
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro hrc
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hfull : reply.msg = resp := by rw [hmsg]; exact truncateToCap_untrunc (by rw [← hmsg]; exact htc)
      refine Or.inl ⟨srv, serverAt_mem hfind, q, _, tr, resp, hans, ?_⟩
      rw [← hfull]; exact hrc
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro hrc
      rcases ih hrc with hd | hd | ht
      · exact Or.inl hd
      · obtain ⟨now2, q2, hh⟩ := hd; rw [absorb_negHitNx_eq] at hh; exact Or.inr (Or.inl ⟨now2, q2, hh⟩)
      · exact Or.inr (Or.inr ht)
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro hrc
      rcases ih hrc with hd | hd | ht
      · exact Or.inl hd
      · obtain ⟨now2, q2, hh⟩ := hd; rw [hcf.2.2.2 now2 q2, hcf0.2.2.2 now2 q2, absorb_negHitNx_eq] at hh; exact Or.inr (Or.inl ⟨now2, q2, hh⟩)
      · exact Or.inr (Or.inr ht)
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro hrc
      rcases ih hrc with hd | hd | ht
      · exact Or.inl hd
      · obtain ⟨now2, q2, hh⟩ := hd; rw [hcf.2.2.2 now2 q2, hcf0.2.2.2 now2 q2, absorb_negHitNx_eq] at hh; exact Or.inr (Or.inl ⟨now2, q2, hh⟩)
      · exact Or.inr (Or.inr ht)
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro hrc
      rcases ih hrc with hd | hd | ht
      · exact Or.inl hd
      · obtain ⟨now2, q2, hh⟩ := hd; rw [hcf.2.2.2 now2 q2, hcf0.2.2.2 now2 q2, absorb_negHitNx_eq] at hh; exact Or.inr (Or.inl ⟨now2, q2, hh⟩)
      · exact Or.inr (Or.inr ht)
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro hrc
      rcases ih hrc with hd | hd | ht
      · exact Or.inl hd
      · obtain ⟨now2, q2, hh⟩ := hd; rw [hcf.2.2.2 now2 q2, hcf0.2.2.2 now2 q2, absorb_negHitNx_eq] at hh; exact Or.inr (Or.inl ⟨now2, q2, hh⟩)
      · exact Or.inr (Or.inr ht)
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      intro hrc
      rcases ihRec hrc with hd | hd | ht
      · exact Or.inl hd
      · obtain ⟨now2, q2, hh⟩ := hd
        rw [hc2f.2.2 now2 q2] at hh
        rcases resolves_negHitNx_justified hnsres now2 q2 hh with h1 | h1 | h1
        · exact Or.inr (Or.inl ⟨now2, q2, h1⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · exact Or.inr (Or.inr ht)
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => intro hrc; exact ih hrc
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => intro hrc; exact ih hrc
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => intro hrc; exact ih hrc
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => intro hrc; exact ih hrc
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => intro hrc; exact ih hrc
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro hrc
      rcases ih hrc with hd | ⟨now2, q2, hh⟩ | ht
      · exact Or.inl hd
      · rw [hcf.2.2 now2 q2] at hh
        exact Or.inr (Or.inl ⟨now2, q2, hh⟩)
      · exact Or.inr (Or.inr ht)
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => intro hrc; exact ih hrc
rfc_proves VeriDNS.Spec.Net.resolves_nxdomain_justified [2308][129:204]

theorem resolves_answer_untruncated {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : Time} {nseen : List Name} {seen : List Name} {c : Cache}
    {slist : List String} {q : Query} {tr : List Step} {path : List String} {tEnd : Time}
    {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    resp.tc = false := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      show reply.msg.tc = false; exact htc
  | answer addr rest q srv tr resp id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      show reply.msg.tc = false; exact htc
  | answerCname addr rest q srv tr resp cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      show final.tc = false; exact ih
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      show final.tc = false; exact ih
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih => exact ih
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih => exact ih
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih => exact ih
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec => exact ihRec
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => exact ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih => exact ih
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc =>
      show reply.msg.tc = false; exact htc
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
  | _ => rfl
rfc_proves VeriDNS.Spec.Net.resolves_answer_untruncated [1035][1414:1420]

def AuthAnswer (net : Network) (r : RR) : Prop :=
  ∃ srv ∈ net.servers, ∃ (q' : Query) (z : Zone),
    bestZone srv q'.qname q'.qclass = some z ∧ bestDeleg z q'.qname = none ∧
    ∃ r' ∈ recordsAt z q'.qname, RR.eqData r r'
rfc_proves VeriDNS.Spec.Net.AuthAnswer [1034][1300:1310]

theorem AuthAnswer_authoritative {net : Network} {r : RR} (h : AuthAnswer net r) :
    ∃ srv ∈ net.servers, ∃ (q' : Query) (z : Zone),
      AuthoritativeFor net q'.qclass srv.name q'.qname ∧ bestZone srv q'.qname q'.qclass = some z
      ∧ ∃ r' ∈ recordsAt z q'.qname, RR.eqData r r' := by
  obtain ⟨srv, hsrv, q', z, hz, hd, r', hr', heq⟩ := h
  exact ⟨srv, hsrv, q', z, serverAnswers_answer_authoritative hz hd hsrv, hz, r', hr', heq⟩

theorem serverAnswers_leaf_auth {net : Network} {srv : Server} (hmem : srv ∈ net.servers)
    {now : Time} {seen : List Name} {o : Bool} {q : Query} {tr : List Step} {resp : Response}
    (hans : ServerAnswers srv now seen o q tr resp)
    (cc : Cache) : ∀ r ∈ resp.answer, AuthAnswer net r ∨ GroundedServed net cc r := by

  induction hans with
  | answer q z here hz hd hh hnc' hmatch =>
      intro r hr
      exact Or.inl ⟨srv, hmem, q, z, hz, hd, r, by rw [hh]; exact (List.mem_filter.mp hr).1,
        RR.eqData_refl r⟩
  | cname q z c target tr' rest hz hd hc hcov ht hfresh hrec ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine Or.inl ⟨srv, hmem, q, z, hz, hd, r, ?_, RR.eqData_refl r⟩
        have : cnameRR q.qname (recordsAt z q.qname) = some r := hc
        exact List.mem_of_find?_eq_some this
      · exact ih r hr'
  | wildcard q z syn hz hd hh hent hw =>
      intro r hr
      exact Or.inr (Or.inr ⟨srv, hmem, q, now, _, _,
        ServerAnswers.wildcard q z syn hz hd hh hent hw, r,
        by simp only [List.mem_append]; exact Or.inl (Or.inl hr), RR.eqData_refl r⟩)
  | referralCacheAnswer q z d here hz hd hca hne =>
      intro r hr
      exact Or.inr (Or.inr ⟨srv, hmem, q, now, _, _,
        ServerAnswers.referralCacheAnswer q z d here hz hd hca hne, r,
        by simp only [List.mem_append]; exact Or.inl (Or.inl hr), RR.eqData_refl r⟩)
  | fromCache q here hz hh hne =>
      intro r hr
      exact Or.inr (Or.inr ⟨srv, hmem, q, now, _, _,
        ServerAnswers.fromCache q here hz hh hne, r,
        by simp only [List.mem_append]; exact Or.inl (Or.inl hr), RR.eqData_refl r⟩)
  | referral q z d hz hd hca => intro r hr; exact absurd hr (by simp)
  | noData q z here hz hd hh hnc'' hempty hw hexists => intro r hr; exact absurd hr (by simp)
  | nameError q z hz hd hh hw hent => intro r hr; exact absurd hr (by simp)
  | exitFollowed q z hz hd hh hw hent => intro r hr; exact absurd hr (by simp)
  | cacheMiss q hz hmiss hnodeleg => intro r hr; exact absurd hr (by simp)

theorem resolves_answer_authoritative {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : Time} {nseen : List Name} {seen : List Name} {c : Cache}
    {slist : List String} {q : Query} {tr : List Step} {path : List String} {tEnd : Time}
    {cout : Cache} {resp : Response}
    (h : Resolves net ns ra ednsBuf rttOf now nseen seen c slist q tr path tEnd cout resp) :
    ∀ r ∈ resp.answer, AuthAnswer net r ∨ GroundedServed net c r ∨ TrustedReplyAnswer ra ednsBuf r
      ∨ TrustedReferralCache ra ednsBuf r ∨ TrustedCnameCache ra ednsBuf r
      ∨ TrustedReplyCache ra ednsBuf r := by
  induction h with
  | ancestorDenied addr origin rest q pq id srcPort c reply hmiss hnmiss hprobe htrans hacc hrc htc cf0 hcf0 cf hcf =>
      intro r hr
      have hr2 : r ∈ reply.msg.answer := hr
      exact Or.inr (Or.inr (Or.inl ⟨addr, id, srcPort, pq, reply, hacc, by
        simp only [List.mem_append]; exact Or.inl (Or.inl hr2)⟩))
  | cacheHit c slist q here hhit hne =>
      intro r hr
      have hr2 : r ∈ here := hr
      rw [← hhit] at hr2
      obtain ⟨e, he, heq⟩ := hit_topServed_eqData hr2
      exact Or.inr (Or.inl (Or.inl ⟨_, _, e, he, heq⟩))
  | negHit c slist q hneg => intro r hr; simp [Cache.negResponse] at hr
  | exhausted c q => intro r hr; simp at hr
  | gaveUp c slist q => intro r hr; simp at hr
  | loopDetected c slist q => intro r hr; simp at hr
  | trustedReply addr origin rest q id srcPort c reply hmiss hnmiss htrans hacc hnr htc =>
      intro r hr
      have hr2 : r ∈ reply.msg.answer := hr
      exact Or.inr (Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, by
        simp only [List.mem_append]; exact Or.inl (Or.inl hr2)⟩))
  | answer addr rest q srv tr respS id srcPort c hmiss hnmiss hfind hans reply htrans hacc hwire hnr hnc htc =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hfull : reply.msg = respS := by rw [hmsg]; exact truncateToCap_untrunc (by rw [← hmsg]; exact htc)
      have hr2 : r ∈ respS.answer := by have : r ∈ reply.msg.answer := hr; rwa [hfull] at this
      exact (serverAnswers_leaf_auth (serverAt_mem hfind) hans c r hr2).imp (fun x => x) Or.inl
  | refer addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hglue hfresh hmono sl hsl hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      rcases ih r hr with ha | hg | ht
      · exact Or.inl ha
      · refine Or.inr (Or.inl (groundedServed_of_cache_groundedServed ?_ hg))
        intro n q2 e0 he0
        refine absorb_topServed_groundedServed reply.msg ?_ n q2 e0 he0
        intro r' hr'; rw [hmsg] at hr'
        exact Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩
      · exact Or.inr (Or.inr ht)
  | referForget addr rest q pq srv tr ref ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe hfind hans reply htrans hacc hwire href hbail frontier hdesc hdescF hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      rcases ih r hr with ha | hg | ht
      · exact Or.inl ha
      · refine Or.inr (Or.inl (groundedServed_of_cache_groundedServed ?_ hg))
        intro n q2 e0 he0
        obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
        obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
        refine absorb_topServed_groundedServed reply.msg ?_ n4 q2 e0 h4
        intro r' hr'; rw [hmsg] at hr'
        exact Or.inr ⟨srv, serverAt_mem hfind, pq, _, tr, ref, hans, r', hr', RR.eqData_refl _⟩
      · exact Or.inr (Or.inr ht)
  | answerCname addr rest q srv tr respS cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss hfind hans reply htrans hacc hwire hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro r hr
      have hmsg := onWire_accepted_honest _ _ _ hwire hacc
      have hr2 : r ∈ cn :: final.answer := hr
      rcases List.mem_cons.mp hr2 with rfl | hrest
      · have hcnmem : r ∈ reply.msg.answer := List.mem_of_find?_eq_some hcn
        rw [hmsg] at hcnmem
        exact Or.inr (Or.inl (Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, respS, hans, r,
          by simp only [List.mem_append]; exact Or.inl (Or.inl (truncateToCap_answer_mem hcnmem)),
          RR.eqData_refl _⟩))
      · rcases ih r hrest with ha | hg | ht
        · exact Or.inl ha
        · refine Or.inr (Or.inl (groundedServed_of_cache_groundedServed ?_ hg))
          intro n q2 e0 he0
          obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e0 he0
          obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e0 h3
          refine absorb_topServed_groundedServed (reply.msg.cnameOwned q.qname) ?_ n4 q2 e0 h4
          intro r' hr'
          simp only [Response.cnameOwned_answer, Response.cnameOwned_authority,
            Response.cnameOwned_additional, List.append_nil, List.mem_filter] at hr'
          obtain ⟨hr', -⟩ := hr'
          rw [hmsg] at hr'
          exact Or.inr ⟨srv, serverAt_mem hfind, q, _, tr, respS, hans, r',
            truncateToCap_sections_mem (by simp only [List.mem_append]; exact Or.inl (Or.inl hr')),
            RR.eqData_refl _⟩
        · exact Or.inr (Or.inr ht)
  | trustedCname addr origin rest q cn target id srcPort c nsl ftr rpath tEnd cout final
      hmiss hnmiss reply htrans hacc hcn hqt htgt hfresh hmono htc cf0 hcf0 cf hcf hrec ih =>
      intro r hr
      have hr2 : r ∈ cn :: final.answer := hr
      rcases List.mem_cons.mp hr2 with rfl | hrest
      · exact Or.inr (Or.inr (Or.inl ⟨addr, id, srcPort, q, reply, hacc, by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (List.mem_of_find?_eq_some hcn))⟩))
      · rcases ih r hrest with ha | hg | ht
        · exact Or.inl ha
        · rcases hg with ⟨n, q2, e, he, hre⟩ | hsrv
          · obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e he
            obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
            rcases absorb_cnameOwned_topServed_owner _ _ _ _ _ _ _ h4 with h' | h'
            · exact Or.inr (Or.inl (Or.inl ⟨n4, q2, e, h', hre⟩))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (trustedCnameCache_eqData
                ⟨addr, id, srcPort, q, reply, hacc, (by rw [hcn]; rfl), h'⟩ hre)))))
          · exact Or.inr (Or.inl (Or.inr hsrv))
        · exact Or.inr (Or.inr ht)
  | gluelessNs q zone nsHost nsAddr nsNseen nsSeen nsSlist nsTr nsPath nsEnd nsResp
      slist2 ftr rpath tEnd final c c2 cout
      hmiss hnmiss hanc cprov hns hmono1 hnsres hnsaddr hmem c2f hc2f hrec ihNs ihRec =>
      intro r hr
      rcases ihRec r hr with ha | hg | ht
      · exact Or.inl ha
      · rcases groundedServedF_of_cache (resolves_cout_grounded hnsres)
          (Or.inl (groundedServed_of_refines hc2f hg)) with hgr | htrc
        · exact Or.inr (Or.inl hgr)
        · exact Or.inr (Or.inr (Or.inr htrc))
      · exact Or.inr (Or.inr ht)
  | trustedReferral addr origin rest q pq frontier ftr rpath tEnd final id srcPort c cout
      hmiss hnmiss hprobe reply htrans hacc href hbail hcut hdesc hfresh hmono sl cf0 hcf0 hsl cf hcf hrec ih =>
      intro r hr
      rcases ih r hr with ha | hg | ht
      · exact Or.inl ha
      · rcases hg with ⟨n, q2, e, he, hre⟩ | hsrv
        · obtain ⟨n3, h3⟩ := hcf.2.1 n q2 e he
          obtain ⟨n4, h4⟩ := hcf0.2.1 n3 q2 e h3
          rcases absorb_topServed_in_bailiwick _ _ _ _ _ _ _ h4 with h' | h'
          · exact Or.inr (Or.inl (Or.inl ⟨n4, q2, e, h', hre⟩))
          · refine Or.inr (Or.inr (Or.inr (Or.inl (trustedReferralCache_eqData ⟨addr, id, srcPort, pq, reply, hacc, href, hcut, ?_⟩ hre))))
            rwa [absorbBailiwick_of_descendsBelow frontier reply.msg hdesc] at h'
        · exact Or.inr (Or.inl (Or.inr hsrv))
      · exact Or.inr (Or.inr ht)
  | timeout addr rest q ftr rpath tEnd final c cout d hdrop hmono hrec ih => exact ih
  | skipMissing addr rest q ftr rpath tEnd final c cout hfind hrec ih => exact ih
  | rejectSpoof addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe hreject hrec ih => exact ih
  | badResponse addr rest q pq ftr rpath tEnd final c cout id srcPort reply hprobe htrans hacc hbad hrec ih => exact ih
  | unfollowableReferral addr rest q pq srv tr ref id srcPort ftr rpath tEnd final c cout reply hmiss hnmiss hprobe hfind hans htrans hacc href hunfollow hrec ih => exact ih
  | cacheCname slist q cn target c nsl ftr rpath tEnd cout final
      hmiss hnmiss hcn hqt htgt hfresh cf hcf hrec ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · obtain ⟨e, he, heq⟩ := cnameServed_topServed_eqData hcn
        exact Or.inr (Or.inl (Or.inl ⟨_, _, e, he, heq⟩))
      · rcases ih r hrest with ha | hg | ht
        · exact Or.inl ha
        · exact Or.inr (Or.inl (groundedServed_of_refines hcf hg))
        · exact Or.inr (Or.inr ht)
  | chooseServer slist slist' q ftr rpath tEnd final c cout hperm hrec ih => exact ih
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1034][2565:2707]

theorem absorb_drops_out_of_bailiwick_poison :
    let bw := N ["EXAMPLE","EDU"]
    let resp : Response :=
      { aa := false, rcode := RCode.noError,
        answer := [ rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93,184,216,35⟩) ],
        authority := [],
        additional := [ rr ["VICTIM","COM"] 100 (.a ⟨6,6,6,6⟩) ] }
    let out := Cache.empty.absorb 0 bw resp
    out.pos.any (fun e => nameEq e.rr.owner (N ["WWW","EXAMPLE","EDU"])) = true
      ∧ out.pos.any (fun e => nameEq e.rr.owner (N ["VICTIM","COM"])) = false := by
  refine ⟨by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.absorb_drops_out_of_bailiwick_poison [2181][343:383]

theorem nodata_authority_soa_dropped_ns_kept :
    let bw := N ["EXAMPLE","EDU"]
    let resp : Response :=
      { aa := true, rcode := RCode.noError, answer := [],
        authority :=
          [ rr ["EXAMPLE","EDU"] 100 (.soa (N ["NS","EXAMPLE","EDU"]) (N ["NS","EXAMPLE","EDU"]) 1 1 1 1 50),
            rr ["EXAMPLE","EDU"] 100 (.ns (N ["NS","EXAMPLE","EDU"])) ],
        additional := [] }
    let out := Cache.empty.absorb 0 bw resp
    out.pos.any (fun e => e.rr.rdata.rtype == RRType.soa) = false
      ∧ out.pos.any (fun e => e.rr.rdata.rtype == RRType.ns) = true := by
  refine ⟨by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.nodata_authority_soa_dropped_ns_kept [2308][274:376]

theorem forged_shallow_cut_cannot_widen_bailiwick :
    let srvApex := N ["EDU"]
    let ref : Response :=
      { aa := false, rcode := RCode.noError, answer := [],
        authority := [ rr [] 100 (.ns (N ["NS","EDU"])) ],
        additional := [ rr ["NS","EDU"] 100 (.a ⟨1,1,1,1⟩),
                        rr ["VICTIM","COM"] 100 (.a ⟨6,6,6,6⟩) ] }
    let bw := absorbBailiwick srvApex (referralCut ref)
    let out := Cache.empty.absorb 0 bw ref
    bw = srvApex
      ∧ out.pos.any (fun e => nameEq e.rr.owner (N ["NS","EDU"])) = true
      ∧ out.pos.any (fun e => nameEq e.rr.owner (N ["VICTIM","COM"])) = false := by
  refine ⟨by decide, by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.forged_shallow_cut_cannot_widen_bailiwick [2181][343:383]

theorem honest_referral_scoped_to_cut :
    let srvApex := (N [] : Name)
    let ref : Response :=
      { aa := false, rcode := RCode.noError, answer := [],
        authority := [ rr ["EDU"] 100 (.ns (N ["NS","EDU"])) ],
        additional := [ rr ["NS","EDU"] 100 (.a ⟨1,1,1,1⟩),
                        rr ["VICTIM","COM"] 100 (.a ⟨6,6,6,6⟩) ] }
    let bw := absorbBailiwick srvApex (referralCut ref)
    let out := Cache.empty.absorb 0 bw ref
    bw = N ["EDU"]
      ∧ out.pos.any (fun e => nameEq e.rr.owner (N ["NS","EDU"])) = true
      ∧ out.pos.any (fun e => nameEq e.rr.owner (N ["VICTIM","COM"])) = false := by
  refine ⟨by decide, by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.honest_referral_scoped_to_cut [2181][343:383]

macro "bailiwickFresh" : tactic =>
  `(tactic| (intro h; first
    | (rw [List.mem_singleton] at h; exact absurd (congrArg List.length h) (by decide))
    | exact absurd h (by simp)))

theorem ex_631_iterative_resolution :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["ISI","EDU"], .rr .mx, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.aa = false
      ∧ resp.answer = [ rr ["ISI","EDU"] 172800 (.mx 10 (N ["VENERA","ISI","EDU"])),
                        rr ["ISI","EDU"] 172800 (.mx 20 (N ["VAXA","ISI","EDU"])) ]
      ∧ 0 < cout.pos.length
      ∧ resp.rcode = RCode.noError
      ∧ path.Nodup := by
  refine ⟨_, _, _, _, _,
    Resolves.refer (now' := 100) "10.0.0.52" _ _ _ cISI _ _
      _ _ _ _ 4660 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
      (ServerAnswers.referral _ eduZone
        { subapex := N ["ISI","EDU"],
          nsSet := [ rr ["ISI","EDU"] 172800 (.ns (N ["VAXA","ISI","EDU"])),
                     rr ["ISI","EDU"] 172800 (.ns (N ["A","ISI","EDU"])),
                     rr ["ISI","EDU"] 172800 (.ns (N ["VENERA","ISI","EDU"])) ] } rfl rfl rfl)
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N ["EDU"]) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)

      ["128.9.0.32", "10.1.0.52", "26.3.0.103", "128.9.0.33", "10.2.0.27"] (by decide)
      (Resolves.skipMissing "128.9.0.32" _ _ _ _ _ _ _ _ rfl
        (Resolves.skipMissing "10.1.0.52" _ _ _ _ _ _ _ _ rfl
          (Resolves.answer "26.3.0.103" _ _ aISI _ _ 4661 5301 _ rfl rfl rfl
            (ServerAnswers.answer _ isiEduZone _ rfl rfl rfl (Or.inl rfl) (by decide))
            _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)))),
    rfl, rfl, by decide, rfl, by decide⟩
rfc_proves VeriDNS.Spec.Net.ex_631_iterative_resolution [1034][2565:2707]

theorem ex_631_no_servfail :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["ISI","EDU"], .rr .mx, .«in», false⟩ tr path tEnd cout resp
        ∧ resp.rcode ≠ RCode.servFail := by
  obtain ⟨tr, path, tEnd, cout, resp, hres, _, _, _, hrc⟩ := ex_631_iterative_resolution
  exact ⟨tr, path, tEnd, cout, resp, hres, by simp [hrc]⟩
rfc_proves VeriDNS.Spec.Net.ex_631_no_servfail [1034][2565:2707]

theorem ex_631_recursion_safe :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["ISI","EDU"], .rr .mx, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["ISI","EDU"] 172800 (.mx 10 (N ["VENERA","ISI","EDU"])),
                        rr ["ISI","EDU"] 172800 (.mx 20 (N ["VAXA","ISI","EDU"])) ]
      ∧ path.Nodup
      ∧ 100 ≤ tEnd
      ∧ (∀ r ∈ resp.answer, AuthAnswer scenario r ∨ GroundedServed scenario Cache.empty r
          ∨ TrustedReplyAnswer "127.0.0.1" 512 r ∨ TrustedReferralCache "127.0.0.1" 512 r
          ∨ TrustedCnameCache "127.0.0.1" 512 r ∨ TrustedReplyCache "127.0.0.1" 512 r) := by
  obtain ⟨tr, path, tEnd, cout, resp, hres, _, hansw, _, _, hnd⟩ := ex_631_iterative_resolution
  exact ⟨tr, path, tEnd, cout, resp, hres, hansw,
    hnd, resolves_time_monotone hres,
    fun r hr => resolves_answer_authoritative hres r hr⟩
rfc_proves VeriDNS.Spec.Net.ex_631_recursion_safe [1034][2565:2707]

def warmCache : Cache :=
  Cache.empty.insert 100 Cred.authoritative (rr ["C","ISI","EDU"] 86400 (.a ⟨10, 0, 0, 52⟩))
rfc_proves VeriDNS.Spec.Net.warmCache [1035][1602:1614]

theorem ex_cache_hit :
    ∃ resp, Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 200 [] [] warmCache ["10.0.0.52"]
        ⟨N ["C","ISI","EDU"], .rr .a, .«in», false⟩ [Step.fromCache] [] 200 warmCache resp
      ∧ resp.aa = false
      ∧ resp.answer = [ rr ["C","ISI","EDU"] 86300 (.a ⟨10, 0, 0, 52⟩) ]
      ∧ warmCache.hit 100000 ⟨N ["C","ISI","EDU"], .rr .a, .«in», false⟩ = [] := by
  refine ⟨_, Resolves.cacheHit warmCache _ _ _ rfl (by decide), rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_cache_hit [1034][2239:2262]

theorem ex_timeout_then_fallback :
    ∃ tr path tEnd cout resp, Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty
        ["10.0.0.52", "26.3.0.103"] ⟨N ["MIL"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                        rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.timeout (now' := 100) "10.0.0.52" _ _ _ _ _ _ _ _
      (queryDatagram 7 "127.0.0.1" "10.0.0.52" 5300 512 ⟨N ["MIL"], .rr .ns, .«in», false⟩)
      (Transit.lost _ _ _) (by decide)
      (Resolves.answer "26.3.0.103" _ _ aISI _ _ 8 5300 _ rfl rfl rfl
        (ServerAnswers.answer _ milZone _ rfl rfl rfl (Or.inl rfl) (by decide))
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)),
    rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_timeout_then_fallback [1034][1940:1948]

theorem ex_spoof_rejected :
    ∃ tr path tEnd cout resp, Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty
        ["10.0.0.52", "26.3.0.103"] ⟨N ["MIL"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                        rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.rejectSpoof "10.0.0.52" _ _ _ _ _ _ _ _ _ 1 5300
      { id := 999, srcAddr := "10.0.0.52", dstAddr := "127.0.0.1", srcPort := 53, dstPort := 5300,
        qname := N ["MIL"], qtype := .rr .ns }
      (ProbeQuery.refl _)
      (by decide)
      (Resolves.answer "26.3.0.103" _ _ aISI _ _ 2 5300 _ rfl rfl rfl
        (ServerAnswers.answer _ milZone _ rfl rfl rfl (Or.inl rfl) (by decide))
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)),
    rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_spoof_rejected [5452][258:278]

theorem ex_negcache_populated :
    ∃ tr path tEnd cout resp, Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["SIR-NIC","ARPA"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.rcode = RCode.nameError
      ∧ 0 < cout.neg.length := by
  refine ⟨_, _, _, _, _,
    Resolves.answer "10.0.0.52" _ _ cISI _ _ 7 5300 _ rfl rfl rfl
      (ServerAnswers.nameError _ rootZone rfl rfl rfl rfl (by decide))
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer (by decide) (Or.inl rfl) (by decide),
    rfl, by decide⟩
rfc_proves VeriDNS.Spec.Net.ex_negcache_populated [2308][465:472]

theorem ex_nodata_cached :
    ∃ tr path tEnd cout resp, Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["SRI-NIC","ARPA"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = []
      ∧ 0 < cout.neg.length
      ∧ cout.negHit 100 ⟨N ["SRI-NIC","ARPA"], .rr .ns, .«in», false⟩ = true
      ∧ cout.negHit 100 ⟨N ["SRI-NIC","ARPA"], .rr .a, .«in», false⟩ = false := by
  refine ⟨_, _, _, _, _,
    Resolves.answer "10.0.0.52" _ _ cISI _ _ 7 5300 _ rfl rfl rfl
      (ServerAnswers.noData _ rootZone _ rfl rfl rfl (Or.inl rfl) (by decide) rfl
        (Or.inl (by decide)))
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer (by decide) (Or.inl rfl) (by decide),
    rfl, rfl, by decide, by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.ex_nodata_cached [2308][274:376]

def nodataCache : Cache :=
  { pos := [], neg := [ ⟨N ["SRI-NIC","ARPA"], some (QType.rr RRType.ns), 0, 86400⟩ ] }

theorem ex_nodata_replay_not_nxdomain :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] nodataCache ["10.0.0.52"]
        ⟨N ["SRI-NIC","ARPA"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = []
      ∧ tr = [Step.fromCache, Step.noData] := by
  have hnx : nodataCache.negHitNx 100 ⟨N ["SRI-NIC","ARPA"], .rr .ns, .«in», false⟩ = false := by decide
  refine ⟨_, _, _, _, _, Resolves.negHit nodataCache _ _ (by decide), ?_, ?_, ?_⟩
  · simp [Cache.negResponse, hnx]
  · simp [Cache.negResponse]
  · simp [Cache.negTrace, hnx]
rfc_proves VeriDNS.Spec.Net.ex_nodata_replay_not_nxdomain [2308][274:376]

theorem ex_servfail_exhausted :
    ∃ tr path tEnd cout resp, Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty
        ["10.0.0.52", "1.2.3.4"] ⟨N ["MIL"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.rcode = RCode.servFail := by
  refine ⟨_, _, _, _, _,
    Resolves.timeout (now' := 100) "10.0.0.52" _ _ _ _ _ _ _ _
      (queryDatagram 1 "127.0.0.1" "10.0.0.52" 5300 512 ⟨N ["MIL"], .rr .ns, .«in», false⟩)
      (Transit.lost _ _ _) (by decide)
      (Resolves.skipMissing "1.2.3.4" _ _ _ _ _ _ _ _ rfl (Resolves.exhausted _ _)), rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_servfail_exhausted [1034][1940:1948]

theorem serverAnswers_rcode_ne_servFail {s : Server} {now : Time} {seen : List Name} {o : Bool}
    {q : Query} {tr : List Step} {resp : Response} (h : ServerAnswers s now seen o q tr resp) :
    resp.rcode ≠ RCode.servFail := by
  induction h with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih => exact ih
  | _ => intro hc; simp at hc

theorem no_servfail_direct {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat}
    {rttOf : String → Nat} {now : Time} {nseen : List Name} {seen : List Name} {c : Cache}
    {rest : List String} {q : Query} {addr : String} {srv : Server} {tr : List Step} {resp : Response}
    (hmiss : c.hit now q = []) (hnmiss : c.negHit now q = false)
    (hfind : serverAt net addr = some srv)
    (hreach : linkReach net ns ra addr = true) (hself : linkReach net ns ra ra = true)
    (hans : ServerAnswers srv now [] true q tr resp)
    (hnref : resp.isReferral = false)
    (hnc : cnameRR q.qname resp.answer = none ∨ q.qtype.covers RRType.cname = true)
    (huntrunc : (truncateToCap (negotiatedUdp ednsBuf) q resp).1.tc = false) :
    ∃ tr' path tEnd cout final,
      Resolves net ns ra ednsBuf rttOf now nseen seen c (addr :: rest) q tr' path tEnd cout final
        ∧ final.rcode ≠ RCode.servFail := by
  have huntr := truncateToCap_untrunc huntrunc
  refine ⟨_, _, _, _, _,
    Resolves.answer (id := 0) (srcPort := 0) addr rest q srv tr resp c hmiss hnmiss hfind hans
      (replyDatagram (queryDatagram 0 ra addr 0 ednsBuf q) (truncateToCap (negotiatedUdp ednsBuf) q resp).1)
      (Transit.deliver _ _ _ hreach hself)
      (accepts_reply 0 ra addr 0 ednsBuf q _)
      OnWire.fromServer
      (by show ((truncateToCap (negotiatedUdp ednsBuf) q resp).1).isReferral = false
          rw [huntr]; exact hnref)
      (by rw [huntr]; exact hnc.imp id Or.inl)
      huntrunc,
    ?_⟩
  show ((truncateToCap (negotiatedUdp ednsBuf) q resp).1).rcode ≠ RCode.servFail
  rw [huntr]; exact serverAnswers_rcode_ne_servFail hans

theorem ex_direct_no_servfail :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 0 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["SRI-NIC","ARPA"], .rr .a, .«in», false⟩ tr path tEnd cout resp
        ∧ resp.rcode ≠ RCode.servFail := by
  refine no_servfail_direct (rest := []) (srv := cISI) ?_ ?_ ?_ ?_ ?_
    (ServerAnswers.answer _ rootZone _ rfl rfl rfl (Or.inl rfl) (by decide)) ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · decide
  · decide
  · decide
  · exact Or.inl rfl
  · decide

def glRoot : Server :=
  { name := N ["R"], addr := "1.1.1.1", cache := []
    zones :=
      [ { apex := N []
          records := [ rr [] 100 (.soa (N ["R"]) (N ["R"]) 1 1 1 1 1), rr [] 100 (.ns (N ["R"])) ]
          delegations := [ { subapex := N ["SUB"], nsSet := [ rr ["SUB"] 100 (.ns (N ["NS1","OTHER"])) ] } ] } ] }

def glOther : Server :=
  { name := N ["O"], addr := "3.3.3.3", cache := []
    zones :=
      [ { apex := N ["OTHER"]
          records := [ rr ["OTHER"] 100 (.soa (N ["O"]) (N ["O"]) 1 1 1 1 1), rr ["OTHER"] 100 (.ns (N ["O"])),
                       rr ["NS1","OTHER"] 100 (.a ⟨7, 7, 7, 7⟩) ]
          delegations := [] } ] }

def glSub : Server :=
  { name := N ["NS1","OTHER"], addr := "7.7.7.7", cache := []
    zones :=
      [ { apex := N ["SUB"]
          records := [ rr ["SUB"] 100 (.soa (N ["NS1","OTHER"]) (N ["NS1","OTHER"]) 1 1 1 1 1),
                       rr ["SUB"] 100 (.ns (N ["NS1","OTHER"])), rr ["X","SUB"] 100 (.a ⟨8, 8, 8, 8⟩) ]
          delegations := [] } ] }

def glNet : Network := { servers := [glRoot, glOther, glSub] }

theorem ex_sibling_resolution :
    ∃ tr path tEnd cout resp,
      Resolves glNet allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["1.1.1.1"]
        ⟨N ["X","SUB"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["X","SUB"] 100 (.a ⟨8, 8, 8, 8⟩) ] := by
  refine ⟨_, _, _, _, _,

    Resolves.referForget (now' := 100) "1.1.1.1" _ _ _ glRoot _ _ _ _ _ _ 1 5300 _ _
      rfl rfl (ProbeQuery.refl _) rfl
      (ServerAnswers.referral _ _ _ rfl rfl rfl)
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide)
      (N []) (by decide) (by decide) (by simp) (by decide)
      [] _ (WriteRefines.refl _ _) (Or.inr (by exact List.nil_subperm)) _ (WriteRefines.refl _ _)

      (Resolves.gluelessNs (now1 := 100) _ (N ["SUB"]) (N ["NS1","OTHER"]) "7.7.7.7"
        [] [] ["3.3.3.3"] _ _ _ _ ["7.7.7.7"] _ _ _ _ _ _ _
        rfl rfl (by decide)
        { pos := [⟨rr ["SUB"] 100 (.ns (N ["NS1","OTHER"])), 100, .authority⟩], neg := [] }
        (List.Mem.head _) (by decide)
        (Resolves.answer "3.3.3.3" _ _ glOther _ _ 2 5300 _ rfl rfl rfl
          (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
          _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide))
        rfl (List.Mem.head _)
        _ (CacheRefines.refl _)
        (Resolves.answer "7.7.7.7" _ _ glSub _ _ 3 5300 _ rfl rfl rfl
          (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
          _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide))),
    rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_sibling_resolution [1034][1940:1948]

def rhRoot : Server :=
  { name := N ["ROOT-SERVERS","NET"], addr := "198.41.0.4", cache := []
    zones :=
      [ { apex := N []
          records :=
            [ rr [] 100 (.soa (N ["ROOT-SERVERS","NET"]) (N ["ROOT-SERVERS","NET"]) 1 1 1 1 1),
              rr [] 100 (.ns (N ["ROOT-SERVERS","NET"])),
              rr ["NS","EDU"] 100 (.a ⟨192, 5, 6, 30⟩) ]
          delegations :=
            [ { subapex := N ["EDU"], nsSet := [ rr ["EDU"] 100 (.ns (N ["NS","EDU"])) ] } ] } ] }

def rhEdu : Server :=
  { name := N ["NS","EDU"], addr := "192.5.6.30", cache := []
    zones :=
      [ { apex := N ["EDU"]
          records :=
            [ rr ["EDU"] 100 (.soa (N ["NS","EDU"]) (N ["NS","EDU"]) 1 1 1 1 1),
              rr ["EDU"] 100 (.ns (N ["NS","EDU"])),
              rr ["NS","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 34⟩) ]
          delegations :=
            [ { subapex := N ["EXAMPLE","EDU"],
                nsSet := [ rr ["EXAMPLE","EDU"] 100 (.ns (N ["NS","EXAMPLE","EDU"])) ] } ] } ] }

def rhExample : Server :=
  { name := N ["NS","EXAMPLE","EDU"], addr := "93.184.216.34", cache := []
    zones :=
      [ { apex := N ["EXAMPLE","EDU"]
          records :=
            [ rr ["EXAMPLE","EDU"] 100 (.soa (N ["NS","EXAMPLE","EDU"]) (N ["NS","EXAMPLE","EDU"]) 1 1 1 1 1),
              rr ["EXAMPLE","EDU"] 100 (.ns (N ["NS","EXAMPLE","EDU"])),
              rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩) ]
          delegations := [] } ] }

def rhNet : Network := { servers := [rhRoot, rhEdu, rhExample] }

def rootHints : List String := [rhRoot.addr]
rfc_proves VeriDNS.Spec.Net.rootHints [1034][1922:1932]

theorem ex_resolve_from_root_hints :
    ∃ tr path tEnd cout resp,
      Resolves rhNet allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty rootHints
        ⟨N ["WWW","EXAMPLE","EDU"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.aa = false
      ∧ resp.answer = [ rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩) ]
      ∧ resp.rcode = RCode.noError := by
  refine ⟨_, _, _, _, _,
    Resolves.refer (now' := 100) "198.41.0.4" _ _ _ rhRoot _ _ _ _ _ _ 1 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
      (ServerAnswers.referral _ _ _ rfl rfl rfl)
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N []) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)
      ["192.5.6.30"] (by decide)
      (Resolves.refer (now' := 100) "192.5.6.30" _ _ _ rhEdu _ _ _ _ _ _ 2 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
        (ServerAnswers.referral _ _ _ rfl rfl rfl)
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N ["EDU"]) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)
        ["93.184.216.34"] (by decide)
        (Resolves.answer "93.184.216.34" _ _ rhExample _ _ 3 5300 _ rfl rfl rfl
          (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
          _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide))),
    rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_resolve_from_root_hints [1034][1922:1932]

theorem ex_root_hints_no_servfail :
    ∃ tr path tEnd cout resp,
      Resolves rhNet allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty rootHints
        ⟨N ["WWW","EXAMPLE","EDU"], .rr .a, .«in», false⟩ tr path tEnd cout resp
        ∧ resp.rcode ≠ RCode.servFail := by
  obtain ⟨tr, path, tEnd, cout, resp, hres, _, _, hrc⟩ := ex_resolve_from_root_hints
  exact ⟨tr, path, tEnd, cout, resp, hres, by simp [hrc]⟩
rfc_proves VeriDNS.Spec.Net.ex_root_hints_no_servfail [1034][1922:1932]

theorem ex_resolve_from_root_hints_edns :
    ∃ tr path tEnd cout resp,
      Resolves rhNet allUp "127.0.0.1" 1232 (fun _ => 0) 100 [] [] Cache.empty rootHints
        ⟨N ["WWW","EXAMPLE","EDU"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.aa = false
      ∧ resp.answer = [ rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.refer (now' := 100) "198.41.0.4" _ _ _ rhRoot _ _ _ _ _ _ 1 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
      (ServerAnswers.referral _ _ _ rfl rfl rfl)
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N []) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)
      ["192.5.6.30"] (by decide)
      (Resolves.refer (now' := 100) "192.5.6.30" _ _ _ rhEdu _ _ _ _ _ _ 2 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
        (ServerAnswers.referral _ _ _ rfl rfl rfl)
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N ["EDU"]) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)
        ["93.184.216.34"] (by decide)
        (Resolves.answer "93.184.216.34" _ _ rhExample _ _ 3 5300 _ rfl rfl rfl
          (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
          _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide))),
    rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_resolve_from_root_hints_edns [1035][1756:1766]

theorem ex_resolve_from_root_hints_authoritative :
    ∃ tr path tEnd cout resp,
      Resolves rhNet allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty rootHints
        ⟨N ["WWW","EXAMPLE","EDU"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩) ]
      ∧ (∀ r ∈ resp.answer, AuthAnswer rhNet r ∨ GroundedServed rhNet Cache.empty r
          ∨ TrustedReplyAnswer "127.0.0.1" 512 r ∨ TrustedReferralCache "127.0.0.1" 512 r
          ∨ TrustedCnameCache "127.0.0.1" 512 r ∨ TrustedReplyCache "127.0.0.1" 512 r)
      ∧ AuthAnswer rhNet (rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩))
      ∧ AuthoritativeFor rhNet RRClass.«in» rhExample.name (N ["WWW","EXAMPLE","EDU"]) := by
  obtain ⟨tr, path, tEnd, cout, resp, hres, _, hansw, _⟩ := ex_resolve_from_root_hints
  refine ⟨tr, path, tEnd, cout, resp, hres, hansw,
    fun r hr => resolves_answer_authoritative hres r hr, ?_,
    serverAnswers_answer_authoritative (s := rhExample) (qname := N ["WWW","EXAMPLE","EDU"])
      (qcls := RRClass.«in») rfl rfl (by simp [rhNet])⟩
  exact ⟨rhExample, by simp [rhNet], ⟨N ["WWW","EXAMPLE","EDU"], .rr .a, RRClass.«in», false⟩,
    _, rfl, rfl, rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩),
    List.mem_singleton.mpr rfl, RR.eqData_refl _⟩
rfc_proves VeriDNS.Spec.Net.ex_resolve_from_root_hints_authoritative [1034][2565:2707]

inductive ServerDispatch (net : Network) (ns : NetState) (s : Server) (hints : List String) (ednsBuf : Nat)
    (now : Time) (cin : Cache) (q : Query) :
    List Step → Time → Cache → Response → Prop where
  | localAnswer (tr : List Step) (resp : Response)
      (hno : q.rd = false ∨ s.recursionAvailable = false)
      (h : ServerAnswers s now [] true q tr resp) :
      ServerDispatch net ns s hints ednsBuf now cin q tr now cin resp
  | recurse (tr : List Step) (path : List String) (tEnd : Time) (cout : Cache) (resp : Response)
      (hrd : q.rd = true) (hra : s.recursionAvailable = true)
      (h : Resolves net ns s.addr ednsBuf (fun _ => 0) now [] [] cin hints q tr path tEnd cout resp) :
      ServerDispatch net ns s hints ednsBuf now cin q tr tEnd cout resp
rfc_proves VeriDNS.Spec.Net.ServerDispatch [1034][2239:2262]

theorem nonRecursive_dispatch_is_local {net : Network} {ns : NetState} {s : Server}
    {hints : List String} {ednsBuf : Nat} {now : Time} {cin : Cache} {q : Query}
    {tr : List Step} {tEnd : Time} {cout : Cache} {resp : Response}
    (hra : s.recursionAvailable = false)
    (h : ServerDispatch net ns s hints ednsBuf now cin q tr tEnd cout resp) :
    ServerAnswers s now [] true q tr resp ∧ tEnd = now ∧ cout = cin := by
  cases h with
  | localAnswer _ hno hsa => exact ⟨hsa, rfl, rfl⟩
  | recurse _ _ _ _ hrd hra' hres => exact absurd (hra.symm.trans hra') (by decide)
rfc_proves VeriDNS.Spec.Net.nonRecursive_dispatch_is_local [1034][2239:2262]

def recursiveFrontEnd : Server :=
  { name := N ["RESOLVER"], addr := "127.0.0.53", cache := [], zones := [],
    recursionAvailable := true }

theorem ex_recursive_dispatch :
    ∃ tr tEnd cout resp,
      ServerDispatch rhNet allUp recursiveFrontEnd rootHints 512 100 Cache.empty
        ⟨N ["WWW","EXAMPLE","EDU"], .rr .a, .«in», true⟩ tr tEnd cout resp
      ∧ resp.aa = false
      ∧ resp.answer = [ rr ["WWW","EXAMPLE","EDU"] 100 (.a ⟨93, 184, 216, 35⟩) ] := by
  exact ⟨_, _, _, _, ServerDispatch.recurse _ _ _ _ _ rfl rfl
    (Resolves.refer (now' := 100) "198.41.0.4" _ _ _ rhRoot _ _ _ _ _ _ 1 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
      (ServerAnswers.referral _ _ _ rfl rfl rfl)
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N []) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)
      ["192.5.6.30"] (by decide)
      (Resolves.refer (now' := 100) "192.5.6.30" _ _ _ rhEdu _ _ _ _ _ _ 2 5300 _ _ rfl rfl (ProbeQuery.refl _) rfl
        (ServerAnswers.referral _ _ _ rfl rfl rfl)
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (by decide) (N ["EDU"]) (by decide) (by decide) (by decide) (by bailiwickFresh) (by decide)
        ["93.184.216.34"] (by decide)
        (Resolves.answer "93.184.216.34" _ _ rhExample _ _ 3 5300 _ rfl rfl rfl
          (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
          _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)))),
    rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_recursive_dispatch [1034][2239:2262]

theorem ex_nonrecursive_ignores_rd :
    ∃ tr tEnd cout resp,
      ServerDispatch scenario allUp cISI [] 512 0 Cache.empty
        ⟨N ["BRL","MIL"], .rr .a, .«in», true⟩ tr tEnd cout resp
      ∧ resp.isReferral = true := by
  exact ⟨_, _, _, _, ServerDispatch.localAnswer _ _ (Or.inr (by decide))
    (ServerAnswers.referral _ rootZone _ rfl rfl rfl), by decide⟩
rfc_proves VeriDNS.Spec.Net.ex_nonrecursive_ignores_rd [1034][2239:2262]

def cnS1 : Server :=
  { name := N ["s1"], addr := "1.1.1.1", cache := []
    zones :=
      [ { apex := N []
          records :=
            [ rr [] 100 (.soa (N ["s1"]) (N ["s1"]) 1 1 1 1 1),
              rr [] 100 (.ns (N ["s1"])),
              rr ["ALIAS"] 100 (.cname (N ["REAL","NET"])) ]
          delegations := [] } ] }

def cnS2 : Server :=
  { name := N ["s2"], addr := "2.2.2.2", cache := []
    zones :=
      [ { apex := N ["NET"]
          records :=
            [ rr ["NET"] 100 (.soa (N ["s2"]) (N ["s2"]) 1 1 1 1 1),
              rr ["NET"] 100 (.ns (N ["s2"])),
              rr ["REAL","NET"] 100 (.a ⟨9, 9, 9, 9⟩) ]
          delegations := [] } ] }

def cnNet : Network := { servers := [cnS1, cnS2] }

theorem ex_cname_chase_across_zones :
    ∃ tr path tEnd cout resp,
      Resolves cnNet allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["1.1.1.1"]
        ⟨N ["ALIAS"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["ALIAS"] 100 (.cname (N ["REAL","NET"])),
                        rr ["REAL","NET"] 100 (.a ⟨9, 9, 9, 9⟩) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.answerCname (now' := 100) "1.1.1.1" _ _ cnS1 _ _ _ (N ["REAL","NET"]) 1 5300 _
      ["2.2.2.2"] _ _ _ _ _ rfl rfl rfl
      (ServerAnswers.cname _ _ _ (N ["REAL","NET"]) _ _ rfl rfl rfl rfl rfl
        (fun h => absurd (congrArg List.length (List.mem_singleton.mp h)) (by decide))
        (ServerAnswers.exitFollowed _ _ rfl rfl rfl rfl rfl))
      _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer
      rfl rfl rfl (fun h => absurd (congrArg List.length (List.mem_singleton.mp h)) (by decide)) (by decide) (by decide)
      _ (WriteRefines.refl _ _) _ (WriteRefines.refl _ _)
      (Resolves.answer "2.2.2.2" _ _ cnS2 _ _ 2 5300 _ rfl rfl rfl
        (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)),
    rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_cname_chase_across_zones [1034][2565:2707]

theorem ex_cached_cname_chased :
    ∃ tr path tEnd cout resp,
      Resolves cnNet allUp "127.0.0.1" 512 (fun _ => 0) 100 [] []
        (Cache.empty.insert 100 Cred.authoritative (rr ["ALIAS"] 100 (.cname (N ["REAL","NET"]))))
        ["1.1.1.1"] ⟨N ["ALIAS"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["ALIAS"] 100 (.cname (N ["REAL","NET"])),
                        rr ["REAL","NET"] 100 (.a ⟨9, 9, 9, 9⟩) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.cacheCname _ _ _ (N ["REAL","NET"]) _ ["2.2.2.2"] _ _ _ _ _
      rfl rfl
      (List.mem_cons_self)
      (by decide) rfl
      (fun h => absurd (congrArg List.length (List.mem_singleton.mp h)) (by decide))
      _ (CacheRefines.refl _)
      (Resolves.answer "2.2.2.2" _ _ cnS2 _ _ 2 5300 _ rfl rfl rfl
        (ServerAnswers.answer _ _ _ rfl rfl rfl (Or.inl rfl) (by decide))
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)),
    rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_cached_cname_chased [1034][2565:2707]

theorem ex_spoof_cannot_poison :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52", "26.3.0.103"]
        ⟨N ["MIL"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.answer = [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                        rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.rejectSpoof "10.0.0.52" _ _ _ _ _ _ _ _ _ 1 5300
      { id := 999, srcAddr := "10.0.0.52", dstAddr := "127.0.0.1", srcPort := 53, dstPort := 5300,
        qname := N ["MIL"], qtype := .rr .ns,
        msg := { aa := true, rcode := RCode.noError, answer := [ rr ["MIL"] 9999 (.a ⟨6, 6, 6, 6⟩) ],
                 authority := [], additional := [] } }
      (ProbeQuery.refl _)
      (by decide)
      (Resolves.answer "26.3.0.103" _ _ aISI _ _ 2 5300 _ rfl rfl rfl
        (ServerAnswers.answer _ milZone _ rfl rfl rfl (Or.inl rfl) (by decide))
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)),
    rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_spoof_cannot_poison [5452][258:278]

theorem ex_strict_ancestor_denied :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["WWW","FOO","MIL"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.rcode = RCode.nameError := by
  refine ⟨_, _, _, _, _,
    Resolves.ancestorDenied "10.0.0.52" "10.0.0.52" []
      ⟨N ["WWW","FOO","MIL"], .rr .a, .«in», false⟩ ⟨N ["MIL"], .rr .a, .«in», false⟩
      7 5300 Cache.empty
      (replyDatagram
        (queryDatagram 7 "127.0.0.1" "10.0.0.52" 5300 512 ⟨N ["MIL"], .rr .a, .«in», false⟩)
        { aa := true, rcode := RCode.nameError, answer := [],
          authority := [ rr ["MIL"] 86400
            (.soa (N ["SRI-NIC","ARPA"]) (N ["SRI-NIC","ARPA"]) 1 1 1 1 86400) ],
          additional := [] })
      rfl rfl
      ⟨⟨[], by decide⟩, rfl, rfl⟩
      (Transit.deliver _ _ _ (by decide) (by decide))
      (accepts_reply _ _ _ _ _ _ _)
      rfl rfl
      _ (Or.inr rfl) _ (NegWriteRefines.refl _ _), rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_strict_ancestor_denied [9156][342:350]
rfc_proves VeriDNS.Spec.Net.ex_strict_ancestor_denied [8020][203:217]

theorem ex_poison_cannot_be_cached :
    let q : Query := ⟨N ["MIL"], .rr .ns, .«in», false⟩
    let out := queryDatagram 1 "127.0.0.1" "26.3.0.103" 5300 512 q
    let poison : Datagram :=
      { id := 999, srcAddr := "26.3.0.103", dstAddr := "127.0.0.1", srcPort := 53, dstPort := 5300,
        qname := N ["MIL"], qtype := .rr .ns,
        msg := { aa := true, rcode := RCode.noError,
                 answer := [ rr ["MIL"] 9999 (.a ⟨6, 6, 6, 6⟩) ], authority := [], additional := [] } }
    ∃ tr resp,
      ServerAnswers aISI 100 [] true q tr resp
      ∧ OnWire out (truncateToUdp q resp).1 poison
      ∧ accepts out poison = false
      ∧ ∀ reply, OnWire out (truncateToUdp q resp).1 reply → accepts out reply = true
          → reply.msg.answer ≠ poison.msg.answer := by
  refine ⟨_, _, ServerAnswers.answer _ milZone _ rfl rfl rfl (Or.inl rfl) (by decide),
    OnWire.offPath _ (Or.inl (by decide)), by decide, ?_⟩
  intro reply hw ha
  rw [onWire_accepted_honest _ _ _ hw ha]
  intro hcontra
  exact absurd (congrArg List.length hcontra) (by decide)
rfc_proves VeriDNS.Spec.Net.ex_poison_cannot_be_cached [5452][258:278]

theorem ex_resolution_advances_time :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52", "26.3.0.103"]
        ⟨N ["MIL"], .rr .ns, .«in», false⟩ tr path tEnd cout resp
      ∧ 100 < tEnd
      ∧ resp.answer = [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                        rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ] := by
  refine ⟨_, _, _, _, _,
    Resolves.timeout (now' := 150) "10.0.0.52" _ _ _ _ _ _ _ _
      (queryDatagram 7 "127.0.0.1" "10.0.0.52" 5300 512 ⟨N ["MIL"], .rr .ns, .«in», false⟩)
      (Transit.lost _ _ _) (by decide)
      (Resolves.answer "26.3.0.103" _ _ aISI _ _ 8 5300 _ rfl rfl rfl
        (ServerAnswers.answer _ milZone _ rfl rfl rfl (Or.inl rfl) (by decide))
        _ (Transit.deliver _ _ _ (by decide) (by decide)) (accepts_reply _ _ _ _ _ _ _) OnWire.fromServer rfl (Or.inl rfl) (by decide)),
    by decide, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_resolution_advances_time [1034][2565:2707]

def qBig : Query := ⟨N ["WIDE","EXAMPLE","ARPA"], .rr .a, .«in», false⟩

def bigResponse : Response :=
  { aa := true, rcode := RCode.noError,
    answer := (List.range 30).map (fun _ => rr ["WIDE","EXAMPLE","ARPA"] 3600 (.a ⟨10, 0, 0, 1⟩)),
    authority := [], additional := [] }
rfc_proves VeriDNS.Spec.Net.bigResponse [1035][1634:1738]

theorem bigResponse_truncated :
    512 < messageWire qBig bigResponse
  ∧ (truncateToUdp qBig bigResponse).2 = true
  ∧ (truncateToUdp qBig bigResponse).1.tc = true
  ∧ 0 < (truncateToUdp qBig bigResponse).1.answer.length
  ∧ (truncateToUdp qBig bigResponse).1.answer.length < bigResponse.answer.length
  ∧ messageWire qBig (truncateToUdp qBig bigResponse).1 ≤ 512 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.bigResponse_truncated [1035][1414:1420]

theorem bigResponse_edns_whole :
    (truncateToCap (negotiatedUdp 1232) qBig bigResponse).2 = false
  ∧ (truncateToCap (negotiatedUdp 1232) qBig bigResponse).1 = bigResponse
  ∧ (truncateToCap (negotiatedUdp 512) qBig bigResponse).2 = true := by
  have hfit : Nat.blt (negotiatedUdp 1232) (messageWire qBig bigResponse) = false := by decide
  refine ⟨by simp [truncateToCap, hfit], by simp [truncateToCap, hfit], by decide⟩
rfc_proves VeriDNS.Spec.Net.bigResponse_edns_whole [1035][1756:1766]

theorem insertByRtt_perm (x : SlistEntry) (l : List SlistEntry) :
    (insertByRtt x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insertByRtt]
  | cons y ys ih =>
    simp only [insertByRtt]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem insertByRtt_mem (x : SlistEntry) (l : List SlistEntry) (a : SlistEntry) :
    a ∈ insertByRtt x l ↔ a = x ∨ a ∈ l := by
  rw [(insertByRtt_perm x l).mem_iff, List.mem_cons]

theorem insertByRtt_sorted (x : SlistEntry) :
    ∀ l, List.Pairwise rttLe l → List.Pairwise rttLe (insertByRtt x l) := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [insertByRtt]
    exact List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
  | cons y ys ih =>
    intro hsort
    rw [List.pairwise_cons] at hsort
    obtain ⟨hy, hys⟩ := hsort
    simp only [insertByRtt]
    split
    · rename_i hxy
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr ⟨hy, hys⟩⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hxy
      · exact Nat.le_trans hxy (hy b hb')
    · rename_i hxy
      have hyx : y.rtt ≤ x.rtt := Nat.le_of_lt (Nat.lt_of_not_le hxy)
      rw [List.pairwise_cons]
      refine ⟨?_, ih hys⟩
      intro b hb
      rw [insertByRtt_mem] at hb
      rcases hb with rfl | hb'
      · exact hyx
      · exact hy b hb'

theorem sortedByRtt_sorted (es : List SlistEntry) : List.Pairwise rttLe (sortedByRtt es) := by
  unfold sortedByRtt
  induction es with
  | nil => exact List.Pairwise.nil
  | cons e es ih => exact insertByRtt_sorted e _ ih

theorem sortedByRtt_perm (es : List SlistEntry) : (sortedByRtt es).Perm es := by
  unfold sortedByRtt
  induction es with
  | nil => exact List.Perm.refl _
  | cons e es ih => exact (insertByRtt_perm e _).trans (ih.cons e)

theorem sortByRtt_glueEntries_perm (rttOf : String → Nat) (ref : Response) :
    (sortByRtt (glueEntries rttOf ref)).Perm (glueAddresses ref) := by
  have h : (glueEntries rttOf ref).map (·.addr) = glueAddresses ref := by
    unfold glueEntries; rw [List.map_map]; exact List.map_id _
  unfold sortByRtt
  rw [← h]
  exact (sortedByRtt_perm _).map (·.addr)

theorem sortByRtt_referralEntries_perm (rttOf : String → Nat) (c : Cache) (now : Time)
    (nm : Name) (fuel : Nat) :
    (sortByRtt (c.referralEntries rttOf now nm fuel)).Perm (c.referralSlist now nm fuel) := by
  have h : (c.referralEntries rttOf now nm fuel).map (·.addr) = c.referralSlist now nm fuel := by
    unfold Cache.referralEntries; rw [List.map_map]; exact List.map_id _
  unfold sortByRtt
  rw [← h]
  exact (sortedByRtt_perm _).map (·.addr)

theorem faster_glue_tried_first :
    let rttOf : String → Nat := fun a => if a == "1.1.1.1" then 5 else 50
    let ref : Response :=
      { aa := false, rcode := RCode.noError, answer := [],
        authority := [ rr ["SUB"] 100 (.ns (N ["SLOW","SUB"])),
                       rr ["SUB"] 100 (.ns (N ["FAST","SUB"])) ],
        additional := [ rr ["SLOW","SUB"] 100 (.a ⟨9,9,9,9⟩),
                        rr ["FAST","SUB"] 100 (.a ⟨1,1,1,1⟩) ] }
    sortByRtt (glueEntries rttOf ref) = ["1.1.1.1", "9.9.9.9"] := by decide
rfc_proves VeriDNS.Spec.Net.faster_glue_tried_first [1034][1934:1939]

theorem answer_invariant_foreign_class (recs foreign : List RR) (q : Query)
    (hf : ∀ r ∈ foreign, (r.cls == q.qclass) = false) :
    (recs ++ foreign).filter (fun x => q.qtype.covers x.rdata.rtype && x.cls == q.qclass)
      = recs.filter (fun x => q.qtype.covers x.rdata.rtype && x.cls == q.qclass) := by
  rw [List.filter_append]
  have hnil : foreign.filter (fun x => q.qtype.covers x.rdata.rtype && x.cls == q.qclass) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp [hf r hr]
  rw [hnil, List.append_nil]
rfc_proves VeriDNS.Spec.Net.answer_invariant_foreign_class [1034][1028:1051]

def inClassZone : Zone :=
  { apex := N ["X"]
    records :=
      [ rr ["X"] 100 (.soa (N ["X"]) (N ["X"]) 1 1 1 1 1),
        rr ["X"] 100 (.ns (N ["X"])),
        { owner := N ["HOST","X"], ttl := 100, rdata := .a ⟨1, 1, 1, 1⟩, cls := .«in» } ]
    delegations := [] }

def chClassZone : Zone :=
  { apex := N ["X"], cls := .ch
    records :=
      [ { owner := N ["X"], ttl := 100, rdata := .soa (N ["X"]) (N ["X"]) 1 1 1 1 1, cls := .ch },
        { owner := N ["X"], ttl := 100, rdata := .ns (N ["X"]), cls := .ch },
        { owner := N ["HOST","X"], ttl := 100, rdata := .a ⟨2, 2, 2, 2⟩, cls := .ch } ]
    delegations := [] }

def mixedClassServer : Server :=
  { name := N ["X"], zones := [inClassZone, chClassZone], cache := [], addr := "5.5.5.5" }

theorem ex_class_isolation_in :
    ∃ tr resp, ServerReplies mixedClassServer 0 ⟨N ["HOST","X"], .rr .a, .«in», false⟩ tr resp
      ∧ resp.answer = [ { owner := N ["HOST","X"], ttl := 100, rdata := .a ⟨1, 1, 1, 1⟩, cls := .«in» } ] := by
  refine ⟨_, _, ServerAnswers.answer _ inClassZone _ rfl rfl rfl (Or.inl rfl) (by decide), rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_class_isolation_in [1034][1028:1051]

theorem ex_class_isolation_ch :
    ∃ tr resp, ServerReplies mixedClassServer 0 ⟨N ["HOST","X"], .rr .a, .ch, false⟩ tr resp
      ∧ resp.answer = [ { owner := N ["HOST","X"], ttl := 100, rdata := .a ⟨2, 2, 2, 2⟩, cls := .ch } ] := by
  refine ⟨_, _, ServerAnswers.answer _ chClassZone _ rfl rfl rfl (Or.inl rfl) (by decide), rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_class_isolation_ch [1034][1028:1051]

def labelOk (l : ByteArray) : Bool := Nat.ble l.size 63
rfc_proves VeriDNS.Spec.Net.labelOk [1035][1648:1652]

def nameOctets (n : Name) : Nat := (n.map (fun l => 1 + l.size)).sum + 1
rfc_proves VeriDNS.Spec.Net.nameOctets [1035][541:546]

def nameOk (n : Name) : Bool := n.all labelOk && Nat.ble (nameOctets n) 255
rfc_proves VeriDNS.Spec.Net.nameOk [1035][541:546]

def Zone.WF (z : Zone) : Prop :=
  (z.records.any (fun r => r.rdata.rtype == RRType.soa && nameEq r.owner z.apex)) = true
  ∧ (z.records.any (fun r => r.rdata.rtype == RRType.ns && nameEq r.owner z.apex)) = true
  ∧ (z.delegations.all (fun d => isAncestor z.apex d.subapex && !nameEq d.subapex z.apex)) = true
  ∧ (z.delegations.all (fun d =>
        d.nsSet.all (fun r => nameEq r.owner d.subapex && r.rdata.rtype == RRType.ns))) = true
  ∧ (z.delegations.all (fun d =>
        d.nsSet.all (fun r => match r.rdata with
          | .ns host => (!isAncestor d.subapex host)
                          || z.records.any (fun g => nameEq g.owner host && isA g)
          | _ => true))) = true
  ∧ (z.records.all (fun r => (r.rdata.rtype != RRType.cname) ||
        (z.records.all (fun r2 => (!nameEq r2.owner r.owner) || r2.rdata.rtype == RRType.cname)))) = true
  ∧ (z.delegations.all (fun d => !d.nsSet.isEmpty)) = true
  ∧ (z.records.all (fun r => nameOk r.owner)) = true
  ∧ (z.delegations.all (fun d => nameOk d.subapex)) = true
rfc_proves VeriDNS.Spec.Net.Zone.WF [1034][1077:1136]

theorem scenario_zones_wf :
    rootZone.WF ∧ eduZone.WF ∧ isiEduZone.WF := by
  refine ⟨?_, ?_, ?_⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.scenario_zones_wf [1034][1077:1136]

theorem wf_glue_present {z : Zone} (h : z.WF) {d : Delegation} (hd : d ∈ z.delegations)
    {r : RR} (hr : r ∈ d.nsSet) {host : Name} (hns : r.rdata = RData.ns host)
    (hbw : inBailiwick d.subapex host = true) :
    addressesFor z.records host ≠ [] := by
  obtain ⟨_, _, _, _, hglue, _⟩ := h
  have hd' := List.all_eq_true.mp hglue d hd
  have hr' := List.all_eq_true.mp hd' r hr
  rw [hns] at hr'
  simp only [inBailiwick] at hbw
  simp only [hbw, Bool.not_true, Bool.false_or] at hr'
  obtain ⟨g, hgmem, hgpred⟩ := List.any_eq_true.mp hr'
  simp only [Bool.and_eq_true] at hgpred
  intro hnil
  have : g ∈ addressesFor z.records host := by
    simp only [addressesFor, List.mem_filter]
    exact ⟨hgmem, by simp [hgpred.1, hgpred.2]⟩
  rw [hnil] at this
  exact absurd this (List.not_mem_nil)

theorem Zone.WF_nsSet_owner {z : Zone} (h : z.WF) {d : Delegation} (hd : d ∈ z.delegations)
    {r : RR} (hr : r ∈ d.nsSet) : nameEq r.owner d.subapex = true := by
  obtain ⟨_, _, _, h4, _, _⟩ := h
  have hr' := List.all_eq_true.mp (List.all_eq_true.mp h4 d hd) r hr
  simp only [Bool.and_eq_true] at hr'
  exact hr'.1

theorem Zone.WF_nsSet_no_soa {z : Zone} (h : z.WF) {d : Delegation} (hd : d ∈ z.delegations) :
    d.nsSet.any (fun r => r.rdata.rtype == RRType.soa) = false := by
  obtain ⟨_, _, _, h4, _, _⟩ := h
  apply Bool.eq_false_iff.mpr
  intro hany
  rw [List.any_eq_true] at hany
  obtain ⟨r, hr, hsoa⟩ := hany
  have hns := List.all_eq_true.mp (List.all_eq_true.mp h4 d hd) r hr
  simp only [Bool.and_eq_true] at hns
  obtain ⟨-, h1⟩ := hns
  revert h1 hsoa
  cases r.rdata.rtype <;> first
    | decide
    | (intro h1 _; exact Bool.noConfusion h1)

theorem Zone.WF_deleg_below {z : Zone} (h : z.WF) {d : Delegation} (hd : d ∈ z.delegations) :
    isAncestor z.apex d.subapex = true ∧ nameEq d.subapex z.apex = false := by
  obtain ⟨_, _, h3, _, _, _⟩ := h
  have hthis := List.all_eq_true.mp h3 d hd
  simp only [Bool.and_eq_true] at hthis
  exact ⟨hthis.1, by simpa using hthis.2⟩

theorem inBailiwick_of_bestDeleg {z : Zone} (hzwf : z.WF) {qname : Name} {d : Delegation}
    (hd : bestDeleg z qname = some d) {ref : Response} (hauth : ref.authority = d.nsSet) :
    ref.inBailiwick qname = true := by
  rw [inBailiwick_iff]
  intro rr hrr _
  rw [hauth] at hrr
  have hdmem : d ∈ z.delegations := by
    unfold bestDeleg at hd
    rcases foldl_pickDeleg_mem _ none d hd with hm | hcon
    · exact (List.mem_filter.mp hm).1
    · exact absurd hcon (by simp)
  exact isAncestor_congr_left (bestDeleg_isAncestor z qname d hd) (Zone.WF_nsSet_owner hzwf hdmem hrr)

theorem descendsBelow_of_bestDeleg {z : Zone} (hzwf : z.WF) {qname : Name} {d : Delegation}
    (hd : bestDeleg z qname = some d) {ref : Response} (hauth : ref.authority = d.nsSet) :
    ref.descendsBelow z.apex = true := by
  have hdmem : d ∈ z.delegations := by
    unfold bestDeleg at hd
    rcases foldl_pickDeleg_mem _ none d hd with hm | hcon
    · exact (List.mem_filter.mp hm).1
    · exact absurd hcon (by simp)
  obtain ⟨_, _, hcbelow, h4, _, _, h7, _, _⟩ := hzwf
  have hbelow := List.all_eq_true.mp hcbelow d hdmem
  simp only [Bool.and_eq_true] at hbelow
  have hnonempty := List.all_eq_true.mp h7 d hdmem
  cases hns : d.nsSet with
  | nil => rw [hns] at hnonempty; simp at hnonempty
  | cons r₀ rest =>
    have hr0mem : r₀ ∈ d.nsSet := by rw [hns]; exact List.mem_cons_self
    have hr0 := List.all_eq_true.mp (List.all_eq_true.mp h4 d hdmem) r₀ hr0mem
    simp only [Bool.and_eq_true] at hr0
    have hfind : ((r₀ :: rest).find? (fun r => r.rdata.rtype == RRType.ns)) = some r₀ :=
      List.find?_cons_of_pos hr0.2
    have hcut : referralCut ref = r₀.owner := by
      unfold referralCut; rw [hauth, hns, hfind]; rfl
    have howner : nameEq d.subapex r₀.owner = true := by rw [nameEq_symm]; exact hr0.1
    unfold Response.descendsBelow
    rw [hcut, Bool.and_eq_true]
    refine ⟨isAncestor_congr_right hbelow.1 howner, ?_⟩
    rw [Nat.blt_eq, nameEq_length hr0.1]
    rcases Nat.lt_or_eq_of_le (isAncestor_length_le hbelow.1) with hlt | heq
    · exact hlt
    · exfalso
      have hcontra : nameEq d.subapex z.apex = true := by
        rw [nameEq_symm]; exact isAncestor_eq_length_nameEq hbelow.1 heq
      rw [hcontra] at hbelow
      simp at hbelow

def Zone.classHomogeneous (z : Zone) : Prop :=
  (z.records.all (fun r => r.cls == z.cls)) = true
  ∧ (z.delegations.all (fun d => d.nsSet.all (fun r => r.cls == z.cls))) = true
rfc_proves VeriDNS.Spec.Net.Zone.classHomogeneous [1034][1028:1051]

def Server.zonesDistinct (s : Server) : Prop :=
  ∀ z₁ ∈ s.zones, ∀ z₂ ∈ s.zones, z₁.cls = z₂.cls → nameEq z₁.apex z₂.apex = true → z₁ = z₂
rfc_proves VeriDNS.Spec.Net.Server.zonesDistinct [1034][1300:1304]

def Network.WF (net : Network) : Prop :=
  (∀ s ∈ net.servers, s.zonesDistinct ∧ ∀ z ∈ s.zones, z.WF ∧ z.classHomogeneous)
  ∧ (∀ s ∈ net.servers, ∀ z ∈ s.zones, ∀ d ∈ z.delegations,
        ∃ s' ∈ net.servers, ∃ z' ∈ s'.zones, nameEq z'.apex d.subapex = true)

  ∧ (∀ s ∈ net.servers, ∀ z ∈ s.zones, ∀ d ∈ z.delegations,
        ∀ s' ∈ net.servers, ∀ z' ∈ s'.zones,
        isAncestor z.apex z'.apex = true → isAncestor z'.apex d.subapex = true →
        nameEq z'.apex z.apex = true ∨ nameEq z'.apex d.subapex = true)
rfc_proves VeriDNS.Spec.Net.Network.WF [1034][1040:1051]

theorem referral_bailiwick_desc {net : Network} {addr : String} {srv : Server}
    {q : Query} {z : Zone} {d : Delegation} {ref : Response}
    (hnet : net.WF) (hfind : serverAt net addr = some srv)
    (hz : bestZone srv q.qname q.qclass = some z) (hd : bestDeleg z q.qname = some d)
    (hauth : ref.authority = d.nsSet) :
    ref.inBailiwick q.qname = true ∧
      ref.descendsBelow (serverBailiwick srv q.qname q.qclass) = true := by
  have hzwf : z.WF := ((hnet.1 srv (serverAt_mem hfind)).2 z (bestZone_spec hz).1).1
  have hsb : serverBailiwick srv q.qname q.qclass = z.apex := by
    simp only [serverBailiwick, hz, Option.elim]
  refine ⟨inBailiwick_of_bestDeleg hzwf hd hauth, ?_⟩
  rw [hsb]
  exact descendsBelow_of_bestDeleg hzwf hd hauth

theorem isAncestor_comparable {a b n : Name}
    (ha : isAncestor a n = true) (hb : isAncestor b n = true) (hlen : a.length ≤ b.length) :
    isAncestor a b = true := by
  have hab : a.length ≤ n.length := isAncestor_length_le ha
  have hbb : b.length ≤ n.length := isAncestor_length_le hb
  unfold isAncestor at ha hb ⊢
  rw [Nat.ble_eq_true_of_le hab, cond_true] at ha
  rw [Nat.ble_eq_true_of_le hbb, cond_true] at hb
  rw [Nat.ble_eq_true_of_le hlen, cond_true]
  refine nameEq_trans ha ?_
  rw [nameEq_symm]
  have hbd := nameEq_drop (b.length - a.length) hb
  rw [List.drop_drop] at hbd
  have harith : n.length - b.length + (b.length - a.length) = n.length - a.length := by omega
  rwa [harith] at hbd

theorem serverBailiwick_ge_priorCut {net : Network} {addr : String} {srv : Server}
    {q : Query} {z : Zone} {d : Delegation} {pc : Name}
    (hnet : net.WF) (hfind : serverAt net addr = some srv)
    (hz : bestZone srv q.qname q.qclass = some z)
    (hd : bestDeleg z q.qname = some d)
    (hpc : ∃ s' ∈ net.servers, ∃ z' ∈ s'.zones, nameEq z'.apex pc = true)
    (hpc_anc : isAncestor pc q.qname = true)
    (hpc_lt : pc.length < d.subapex.length) :
    pc.length ≤ (serverBailiwick srv q.qname q.qclass).length := by
  have hsb : serverBailiwick srv q.qname q.qclass = z.apex := by
    simp only [serverBailiwick, hz, Option.elim]
  rw [hsb]
  by_contra hgt
  rw [Nat.not_le] at hgt
  obtain ⟨hzmem, hzanc⟩ := bestZone_spec hz
  have hdmem : d ∈ z.delegations := by
    unfold bestDeleg at hd
    rcases foldl_pickDeleg_mem _ none d hd with hm | hcon
    · exact (List.mem_filter.mp hm).1
    · exact absurd hcon (by simp)
  have hdanc : isAncestor d.subapex q.qname = true := bestDeleg_isAncestor z q.qname d hd
  have h1 : isAncestor z.apex pc = true := isAncestor_comparable hzanc hpc_anc (Nat.le_of_lt hgt)
  have h2 : isAncestor pc d.subapex = true := isAncestor_comparable hpc_anc hdanc (Nat.le_of_lt hpc_lt)
  obtain ⟨s', hs', z', hz'mem, hz'eq⟩ := hpc
  have h1' : isAncestor z.apex z'.apex = true := isAncestor_congr_right h1 (by rw [nameEq_symm]; exact hz'eq)
  have h2' : isAncestor z'.apex d.subapex = true := isAncestor_congr_left h2 hz'eq
  rcases hnet.2.2 srv (serverAt_mem hfind) z hzmem d hdmem s' hs' z' hz'mem h1' h2' with he | he
  · have : pc.length = z.apex.length := by rw [← nameEq_length hz'eq, nameEq_length he]
    omega
  · have : pc.length = d.subapex.length := by rw [← nameEq_length hz'eq, nameEq_length he]
    omega

theorem scenario_WF : scenario.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    simp only [scenario, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · constructor
      · intro z₁ hz₁ z₂ hz₂ _ hapex
        simp only [show cISI.zones = [rootZone, eduZone] from rfl, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hz₁ hz₂
        rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl <;>
          first | rfl | (exact absurd hapex (by decide))
      · intro z hz
        simp only [show cISI.zones = [rootZone, eduZone] from rfl, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩, rfl, rfl⟩
    · constructor
      · intro z₁ hz₁ z₂ hz₂ _ hapex
        simp only [show aISI.zones = [rootZone, isiEduZone, milZone] from rfl, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hz₁ hz₂
        rcases hz₁ with rfl | rfl | rfl <;> rcases hz₂ with rfl | rfl | rfl <;>
          first | rfl | (exact absurd hapex (by decide))
      · intro z hz
        simp only [show aISI.zones = [rootZone, isiEduZone, milZone] from rfl, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩, rfl, rfl⟩
    · constructor
      · intro z₁ hz₁ z₂ hz₂ _ hapex
        simp only [show sriNic.zones = [rootZone, eduZone, milZone] from rfl, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hz₁ hz₂
        rcases hz₁ with rfl | rfl | rfl <;> rcases hz₂ with rfl | rfl | rfl <;>
          first | rfl | (exact absurd hapex (by decide))
      · intro z hz
        simp only [show sriNic.zones = [rootZone, eduZone, milZone] from rfl, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩, rfl, rfl⟩
  · decide
  · decide
rfc_proves VeriDNS.Spec.Net.scenario_WF [1034][1040:1051]

theorem nearest_unique {s : Server} (hd : s.zonesDistinct) {qname : Name} {qcls : RRClass}
    {z₁ z₂ : Zone} (h1 : z₁ ∈ s.zones) (h2 : z₂ ∈ s.zones)
    (hc1 : z₁.cls = qcls) (hc2 : z₂.cls = qcls)
    (ha1 : isAncestor z₁.apex qname = true) (ha2 : isAncestor z₂.apex qname = true)
    (hlen : z₁.apex.length = z₂.apex.length) : z₁ = z₂ := by
  have key : ∀ {a : Name}, isAncestor a qname = true → a.length = z₁.apex.length →
      nameEq a (qname.drop (qname.length - z₁.apex.length)) = true := by
    intro a ha hla
    unfold isAncestor at ha
    cases hble : Nat.ble a.length qname.length with
    | false => rw [hble] at ha; simp at ha
    | true => rw [hble, cond_true] at ha; rwa [hla] at ha
  have e1 := key ha1 rfl
  have e2 := key ha2 hlen.symm
  exact hd z₁ h1 z₂ h2 (hc1.trans hc2.symm) (nameEq_trans e1 (nameEq_symm _ _ ▸ e2))

theorem Zone.WF_cnameAlone {z : Zone} (h : z.WF) (qname : Name) :
    cnameAlone (recordsAt z qname) = true := by
  obtain ⟨_, _, _, _, _, hcname, _⟩ := h
  rw [cnameAlone, Bool.or_eq_true]
  by_cases hany : (recordsAt z qname).any (fun r => r.rdata.rtype == RRType.cname) = true
  · right
    obtain ⟨cl, hcl, hclcn⟩ := List.any_eq_true.mp hany
    rw [recordsAt, List.mem_filter] at hcl
    obtain ⟨hcl_z, hcl_q⟩ := hcl
    have hcl_all := List.all_eq_true.mp hcname cl hcl_z
    rw [Bool.or_eq_true] at hcl_all
    have hclcn' : (cl.rdata.rtype == RRType.cname) = true := hclcn
    have hinner : (z.records.all
        (fun r2 => (!nameEq r2.owner cl.owner) || r2.rdata.rtype == RRType.cname)) = true := by
      rcases hcl_all with hne | hall
      · simp [bne, hclcn'] at hne
      · exact hall
    rw [List.all_eq_true, recordsAt]
    intro r2 hr2
    rw [List.mem_filter] at hr2
    obtain ⟨hr2_z, hr2_q⟩ := hr2
    have hr2cl : nameEq r2.owner cl.owner = true :=
      nameEq_trans hr2_q (by rw [nameEq_symm]; exact hcl_q)
    have hr2all := List.all_eq_true.mp hinner r2 hr2_z
    rw [Bool.or_eq_true] at hr2all
    rcases hr2all with hne2 | hcn2
    · rw [hr2cl] at hne2; simp at hne2
    · exact hcn2
  · exact Or.inl (by simpa using hany)
rfc_proves VeriDNS.Spec.Net.Zone.WF_cnameAlone [1034][1311:1318]

theorem wf_cname_forces_redirection {z : Zone} (h : z.WF) {qname : Name} {c : RR}
    {qt : QType} {qcls : RRClass}
    (hcn : cnameRR qname (recordsAt z qname) = some c) (hqt : qt.covers RRType.cname = false) :
    (recordsAt z qname).filter (fun r => qt.covers r.rdata.rtype && r.cls == qcls) = [] :=
  cnameAlone_forces_cname (Zone.WF_cnameAlone h qname) hcn hqt
rfc_proves VeriDNS.Spec.Net.wf_cname_forces_redirection [1034][1311:1318]

theorem scenario_names_within_limits :
    (rootZone.records.all (fun r => nameOk r.owner)) = true
  ∧ nameOk (N ["XX", "LCS", "MIT", "EDU"]) = true := by
  refine ⟨by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.scenario_names_within_limits [1035][541:546]

theorem qname_fits_datagram (q : Query) (hq : nameOk q.qname = true) :
    (msgHdrQ q).1 ≤ udpMax := by
  have hle : nameOctets q.qname ≤ 255 := by
    simp only [nameOk, Bool.and_eq_true] at hq
    exact Nat.le_of_ble_eq_true hq.2
  have heq : (msgHdrQ q).1 = 12 + nameWire q.qname + 4 := by
    show (12 + nameWireC [] q.qname) + 4 = 12 + nameWire q.qname + 4
    rw [nameWireC_nil]
  have hwo : nameWire q.qname = nameOctets q.qname := rfl
  simp only [udpMax]
  omega
rfc_proves VeriDNS.Spec.Net.qname_fits_datagram [1035][541:546]

end VeriDNS.Spec.Net
