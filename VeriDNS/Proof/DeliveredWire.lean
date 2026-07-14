import VeriDNS.Proof.TtlCap
import VeriDNS.Proof.AnswerScrub






namespace VeriDNS.Proof.DeliveredWire

open VeriDNS.Impl
open VeriDNS.Spec
open VeriDNS.Proof.Message

def CanonicalSection (rrs : Array ByteArray) : Prop :=
  ∀ b ∈ rrs, CanonicalRR b

theorem canonicalSection_validRRBytes {rrs : Array ByteArray}
    (h : CanonicalSection rrs) : ValidRRBytes rrs :=
  validRRBytesOfMem fun b hb pre suf => by
    obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, hbe⟩ := h b hb
    subst hbe
    exact rrWire_frame ls hv hle t c ttl rdata hrd pre suf

theorem canonicalSection_empty : CanonicalSection #[] := by
  intro b hb
  simp at hb

theorem canonicalSection_append {a b : Array ByteArray}
    (ha : CanonicalSection a) (hb : CanonicalSection b) : CanonicalSection (a ++ b) := by
  intro x hx
  rcases Array.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem decode_ok_wire_facts {buf : ByteArray} {msg : Format}
    (h : Impl.Message.decode buf = .ok msg) :
    msg.header.qdcount.toNat = msg.question.size
    ∧ msg.header.ancount.toNat = msg.answer.size
    ∧ msg.header.nscount.toNat = msg.authority.size
    ∧ msg.header.arcount.toNat = msg.additional.size
    ∧ (∀ i : Fin msg.question.size, QuestionFromLabels msg.question[i])
    ∧ CanonicalSection msg.answer
    ∧ CanonicalSection msg.authority
    ∧ CanonicalSection msg.additional := by
  unfold Impl.Message.decode at h
  split at h <;> rename_i hrun
  case h_2 => exact absurd h (by simp)
  rename_i m posm
  have hm : m = msg := by
    injection h
  subst hm
  simp only [Primitives.run_bind] at hrun
  split at hrun <;> rename_i hhdr
  case h_2 => exact absurd hrun (by simp)
  rename_i hdr posh
  split at hrun <;> rename_i hqs
  case h_2 => exact absurd hrun (by simp)
  rename_i qs posq
  split at hrun <;> rename_i hans
  case h_2 => exact absurd hrun (by simp)
  rename_i ans posa
  split at hrun <;> rename_i hauth
  case h_2 => exact absurd hrun (by simp)
  rename_i auth posn
  split at hrun <;> rename_i hadd
  case h_2 => exact absurd hrun (by simp)
  rename_i add posd
  simp only [Primitives.run_pure] at hrun
  obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj hrun)
  subst h1
  have hnone : ∀ {α : Type} (P : α → Prop) (x : α), x ∈ (#[] : Array α) → P x := by
    intro α P x hx
    simp at hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (run_decodeMany_size Question.decode _ _ _ _ _ _ hqs).symm
  · simpa using (run_decodeMany_size Impl.Message.decodeRRCanonical _ _ _ _ _ _ hans).symm
  · simpa using (run_decodeMany_size Impl.Message.decodeRRCanonical _ _ _ _ _ _ hauth).symm
  · simpa using (run_decodeMany_size Impl.Message.decodeRRCanonical _ _ _ _ _ _ hadd).symm
  · exact fun i => run_decodeMany_mem QuestionFromLabels Question.decode
      (fun hq => run_questionDecode_valid hq) _ _ _ _ _ _ hqs
      (hnone _) _ (qs.getElem_mem i.isLt)
  · exact fun b hb => run_decodeMany_mem CanonicalRR Impl.Message.decodeRRCanonical
      (fun hb' => run_decodeRRCanonical_shape hb') _ _ _ _ _ _ hans (hnone _) b hb
  · exact fun b hb => run_decodeMany_mem CanonicalRR Impl.Message.decodeRRCanonical
      (fun hb' => run_decodeRRCanonical_shape hb') _ _ _ _ _ _ hauth (hnone _) b hb
  · exact fun b hb => run_decodeMany_mem CanonicalRR Impl.Message.decodeRRCanonical
      (fun hb' => run_decodeRRCanonical_shape hb') _ _ _ _ _ _ hadd (hnone _) b hb

theorem canonicalSection_map_capTtlRR {rrs : Array ByteArray}
    (h : CanonicalSection rrs) : CanonicalSection (rrs.map Server.capTtlRR) := by
  intro b hb
  rw [Array.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact TtlCap.canonicalRR_capTtlRR a (h a ha)



theorem ba_extract_suffix (a b : ByteArray) :
    (a ++ b).extract a.size (a ++ b).size = b := by
  ext1
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have h1 : a.data.extract a.size ((a ++ b).size) = #[] :=
    Array.extract_eq_empty_iff.mpr (by simp)
  have h2 : a.size - a.data.size = 0 := by simp
  have h3 : (a ++ b).size - a.data.size = b.data.size := by
    simp [ByteArray.size_append]
  rw [h1, h2, h3]
  simp

def CanonicalName (m : ByteArray) : Prop :=
  ∃ ls : Array ByteArray, VeriDNS.Proof.DomainName.ValidLabels ls
    ∧ (Impl.DomainName.labelsToWireFormat ls).size ≤ 255
    ∧ m = Impl.DomainName.labelsToWireFormat ls

theorem canonicalName_of_questionFromLabels {qu : VeriDNS.Spec.Question}
    (h : QuestionFromLabels qu) : CanonicalName qu.qname := by
  obtain ⟨ls, hv, hle, heq⟩ := h
  exact ⟨ls, hv, hle, heq.symm⟩

theorem canonicalName_randomizeCase (seed : UInt16) {m : ByteArray} (h : CanonicalName m) :
    CanonicalName (DomainName.randomizeCase seed m) := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  have hfix : ∀ (i : Nat) (b : UInt8), b.toNat ≤ 63 →
      (if DomainName.caseSeedBit seed i then DomainName.toggleCaseByte b else b) = b := by
    intro i b hb
    have htog : DomainName.toggleCaseByte b = b := by
      unfold DomainName.toggleCaseByte
      rw [if_neg (by simp [UInt8.le_iff_toNat_le]; omega),
          if_neg (by simp [UInt8.le_iff_toNat_le]; omega)]
    split
    · exact htog
    · rfl
  obtain ⟨ls', hv', heq⟩ :=
    VeriDNS.Proof.DomainName.labelsToWireFormat_mapIdx_fixSmall ls hv
      (fun i b => if DomainName.caseSeedBit seed i then DomainName.toggleCaseByte b else b) hfix
  refine ⟨ls', hv', ?_, heq⟩
  rw [← heq]
  show ((DomainName.labelsToWireFormat ls).data.mapIdx
    (fun i b => if DomainName.caseSeedBit seed i then DomainName.toggleCaseByte b else b)).size ≤ 255
  rw [Array.size_mapIdx, ByteArray.size_data]
  exact hle

theorem parseRaw_rrWire (ls : Array ByteArray) (hv : VeriDNS.Proof.DomainName.ValidLabels ls)
    (hle : (Impl.DomainName.labelsToWireFormat ls).size ≤ 255)
    (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray) (hsz : rdata.size < 65536) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) (rrWire ls t c ttl rdata)
      = some { name := Impl.DomainName.labelsToWireFormat ls, type := t, «class» := c,
               ttl := ttl, rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata } := by
  have hrun := run_resourceRecordDecode_rrWire ls hv hle t c ttl rdata hsz
    ByteArray.empty ByteArray.empty
  have hae : ∀ a : ByteArray, a ++ ByteArray.empty = a := fun a => by
    ext1; simp
  have hea : ∀ a : ByteArray, ByteArray.empty ++ a = a := fun a => by
    ext1; simp
  rw [hae, hea] at hrun
  simp only [show ByteArray.empty.size = 0 from rfl] at hrun
  show (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode (rrWire ls t c ttl rdata) with
      | .ok (rr, _) => some rr | .error _ => none) = _
  rw [hrun]

theorem canonicalRR_parse {b : ByteArray} (h : CanonicalRR b) :
    ∃ (ls : Array ByteArray) (t c : BitVec 16) (ttl : BitVec 32) (rdata : ByteArray),
      VeriDNS.Proof.DomainName.ValidLabels ls
      ∧ (Impl.DomainName.labelsToWireFormat ls).size ≤ 255
      ∧ CanonicalRdata t rdata
      ∧ b = rrWire ls t c ttl rdata
      ∧ RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b
          = some { name := Impl.DomainName.labelsToWireFormat ls, type := t, «class» := c,
                   ttl := ttl, rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata } := by
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl⟩ := h
  exact ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl,
    parseRaw_rrWire ls hv hle t c ttl rdata (canonicalRdata_size_lt hrd)⟩

theorem setOwnerB_rrWire (ls ms : Array ByteArray) (t c : BitVec 16) (ttl : BitVec 32)
    (rdata : ByteArray) {rr : VeriDNS.Spec.ResourceRecord}
    (hname : RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr
      = Impl.DomainName.labelsToWireFormat ls) :
    Resolver.setOwnerB (RR := VeriDNS.Spec.ResourceRecord) rr (rrWire ls t c ttl rdata)
        (Impl.DomainName.labelsToWireFormat ms)
      = rrWire ms t c ttl rdata := by
  unfold Resolver.setOwnerB
  rw [hname]
  show Impl.DomainName.labelsToWireFormat ms
      ++ (Impl.DomainName.labelsToWireFormat ls
          ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ rdata)).extract
        (Impl.DomainName.labelsToWireFormat ls).size (rrWire ls t c ttl rdata).size
    = rrWire ms t c ttl rdata
  rw [show (rrWire ls t c ttl rdata).size
      = (Impl.DomainName.labelsToWireFormat ls
          ++ (rrFixed t c ttl (BitVec.ofNat 16 rdata.size) ++ rdata)).size from rfl,
    ba_extract_suffix]
  rfl

theorem reachIterB_canonical {answer : Array ByteArray} (hca : CanonicalSection answer) :
    ∀ (k : Nat) (reach : Array ByteArray),
      (∀ m ∈ reach, CanonicalName m) →
      ∀ m ∈ Resolver.reachIterB (RR := VeriDNS.Spec.ResourceRecord) answer k reach,
        CanonicalName m := by
  intro k
  induction k with
  | zero => intro reach hreach m hm; exact hreach m hm
  | succ k ih =>
    intro reach hreach m hm
    apply ih (Resolver.reachStepB (RR := VeriDNS.Spec.ResourceRecord) answer reach) _ m hm
    intro x hx
    unfold Resolver.reachStepB at hx
    rw [Array.mem_append] at hx
    rcases hx with hx | hx
    · exact hreach x hx
    · rw [Array.mem_filterMap] at hx
      obtain ⟨b, hb, ht⟩ := hx
      unfold Resolver.reachTarget? at ht
      obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, hbe, hpr⟩ := canonicalRR_parse (hca b hb)
      rw [hpr] at ht
      simp only at ht
      split at ht
      · rename_i hg
        obtain rfl : rdata = x := Option.some.inj ht
        rw [Bool.and_eq_true] at hg
        have ht5 : t = (5 : BitVec 16) := beq_iff_eq.mp hg.1
        subst ht5
        cases hrd with
        | nameType ht' hv' hle' => exact ⟨_, hv', hle', rfl⟩
        | prefixedName ht' hv' hle' =>
          rcases ht' with ⟨h15, -⟩ | ⟨h33, -⟩
          · exact absurd h15 (by decide)
          · exact absurd h33 (by decide)
        | other h2 h5 h12 h6 h15 h33 hsz => exact absurd rfl h5
      · exact absurd ht (by simp)

theorem reachableNamesB_canonical {qname : ByteArray} {answer : Array ByteArray}
    (hca : CanonicalSection answer) (hqn : CanonicalName qname) :
    ∀ m ∈ Resolver.reachableNamesB (RR := VeriDNS.Spec.ResourceRecord) qname answer,
      CanonicalName m := by
  apply reachIterB_canonical hca
  intro m hm
  rw [Array.mem_singleton] at hm
  subst hm
  exact hqn

theorem canonicalSection_scrubAnswerB {qname : ByteArray} {answer : Array ByteArray}
    (h : CanonicalSection answer) (hqn : CanonicalName qname) :
    CanonicalSection
      (Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord) qname answer) := by
  intro b' hb'
  obtain ⟨b, hb, rr, hpr, m, hm, hci, rfl⟩ := Resolver.scrubAnswerB_mem hb'
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl, hpr'⟩ := canonicalRR_parse (h b hb)
  obtain rfl : _ = rr := Option.some.inj (hpr'.symm.trans hpr)
  obtain ⟨ms, hvms, hlems, rfl⟩ := reachableNamesB_canonical h hqn m hm
  rw [setOwnerB_rrWire ls ms t c ttl rdata rfl]
  exact ⟨ms, t, c, ttl, rdata, hvms, hlems, hrd, rfl⟩

theorem scrubAuthorityB_subset {qname : ByteArray} {authority : Array ByteArray}
    {bytes : ByteArray} (h : bytes ∈ Server.scrubAuthorityB qname authority) :
    bytes ∈ authority :=
  (Array.mem_filter.mp h).1

theorem canonicalSection_scrubAuthorityB {qname : ByteArray} {authority : Array ByteArray}
    (h : CanonicalSection authority) :
    CanonicalSection (Server.scrubAuthorityB qname authority) :=
  fun b hb => h b (scrubAuthorityB_subset hb)

theorem scrubAuthorityB_size_le (qname : ByteArray) (authority : Array ByteArray) :
    (Server.scrubAuthorityB qname authority).size ≤ authority.size :=
  Array.size_filter_le

theorem scrubAnswerB_size_le (qname : ByteArray) (answer : Array ByteArray) :
    (Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord) qname answer).size
      ≤ answer.size := by
  unfold Resolver.scrubAnswerB
  exact Array.size_filterMap_le

theorem canonicalRR_size_pos {b : ByteArray} (h : CanonicalRR b) : 1 ≤ b.size := by
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl⟩ := h
  simp only [rrWire, ByteArray.size_append, rrFixed_size]
  omega

theorem baConcat_length_le (l : List ByteArray) (h : ∀ b ∈ l, 1 ≤ b.size) :
    l.length ≤ (baConcat l).size := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    rw [baConcat_cons]
    simp only [List.length_cons, ByteArray.size_append]
    have hb := h b (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem encode_size_answer_le (msg : VeriDNS.Spec.Format) (h : CanonicalSection msg.answer) :
    msg.answer.size ≤ (Impl.Message.encode msg).size := by
  rw [encode_eq]
  simp only [ByteArray.size_append]
  have := baConcat_length_le msg.answer.toList
    (fun b hb => canonicalRR_size_pos (h b (by simpa using hb)))
  simp only [Array.length_toList] at this
  omega

theorem deliveredResponse_decode_encode (query resp : Format)
    (hqd : resp.header.qdcount.toNat = resp.question.size)
    (hns : resp.header.nscount.toNat = resp.authority.size)
    (har : resp.header.arcount.toNat = resp.additional.size)
    (hsz : (Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord)
      (Server.clientQname query) resp.answer).size < 65536)
    (hqn : CanonicalName (Server.clientQname query))
    (hq : ∀ i : Fin resp.question.size, QuestionFromLabels resp.question[i])
    (hca : CanonicalSection resp.answer)
    (hcn : CanonicalSection resp.authority)
    (hcd : CanonicalSection resp.additional) :
    Impl.Message.decode (Impl.Message.encode (Server.deliveredResponse query resp))
      = .ok (Server.deliveredResponse query resp) := by
  refine decode_encode _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show resp.header.qdcount.toNat = resp.question.size
    exact hqd
  · show (BitVec.ofNat 16 (Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord)
        (Server.clientQname query) resp.answer).size).toNat
      = (Resolver.scrubAnswerB (RR := VeriDNS.Spec.ResourceRecord)
        (Server.clientQname query) resp.answer).size
    rw [BitVec.toNat_ofNat]
    have h216 : 2 ^ 16 = 65536 := rfl
    omega
  · show (BitVec.ofNat 16 (Server.scrubAuthorityB (Server.clientQname query)
        resp.authority).size).toNat
      = (Server.scrubAuthorityB (Server.clientQname query) resp.authority).size
    rw [BitVec.toNat_ofNat]
    have hle := scrubAuthorityB_size_le (Server.clientQname query) resp.authority
    have hlt : resp.header.nscount.toNat < 65536 := resp.header.nscount.isLt
    have h216 : 2 ^ 16 = 65536 := rfl
    omega
  · show resp.header.arcount.toNat = resp.additional.size
    exact har
  · exact validQuestionsOfForall hq
  · exact canonicalSection_validRRBytes (canonicalSection_scrubAnswerB hca hqn)
  · exact canonicalSection_validRRBytes (canonicalSection_scrubAuthorityB hcn)
  · exact canonicalSection_validRRBytes hcd

theorem errorResponse_decode_encode (query : Format) (rc : Rcode)
    (hqd : query.header.qdcount.toNat = query.question.size)
    (hq : ∀ i : Fin query.question.size, QuestionFromLabels query.question[i]) :
    Impl.Message.decode (Impl.Message.encode
        (Server.finalizeForClient (Server.buildErrorResponse query rc)))
      = .ok (Server.finalizeForClient (Server.buildErrorResponse query rc)) := by
  refine decode_encode _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show query.header.qdcount.toNat = query.question.size
    exact hqd
  · show (BitVec.ofNat 16 (#[] : Array ByteArray).size).toNat
      = (#[] : Array ByteArray).size
    decide
  · show (BitVec.ofNat 16 (#[] : Array ByteArray).size).toNat
      = (#[] : Array ByteArray).size
    decide
  · show (BitVec.ofNat 16 (#[] : Array ByteArray).size).toNat
      = (#[] : Array ByteArray).size
    decide
  · exact validQuestionsOfForall hq
  · exact canonicalSection_validRRBytes canonicalSection_empty
  · exact canonicalSection_validRRBytes canonicalSection_empty
  · exact canonicalSection_validRRBytes canonicalSection_empty



def RRWireCanon (rr : VeriDNS.Spec.ResourceRecord) : Prop :=
  ∃ ls : Array ByteArray,
    VeriDNS.Proof.DomainName.ValidLabels ls
    ∧ (Impl.DomainName.labelsToWireFormat ls).size ≤ 255
    ∧ rr.name = Impl.DomainName.labelsToWireFormat ls
    ∧ rr.rdlength.toNat = rr.rdata.size
    ∧ CanonicalRdata rr.type rr.rdata

theorem rrBytes_eq_rrWire {rr : VeriDNS.Spec.ResourceRecord} {ls : Array ByteArray}
    (hname : rr.name = Impl.DomainName.labelsToWireFormat ls)
    (hrdl : rr.rdlength.toNat = rr.rdata.size) :
    RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr
      = rrWire ls rr.type rr.class rr.ttl rr.rdata := by
  have hrdl' : BitVec.ofNat 16 rr.rdata.size = rr.rdlength := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have h216 : 2 ^ 16 = 65536 := rfl
    have hlt := rr.rdlength.isLt
    omega
  show DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr) = _
  have henc := rrWire_encoder rr.name rr.type rr.class rr.ttl rr.rdlength rr.rdata
  unfold VeriDNS.Impl.ResourceRecord.encode
  rw [henc, hname, ← hrdl']
  rfl

theorem canonicalRR_rrBytes {rr : VeriDNS.Spec.ResourceRecord} (h : RRWireCanon rr) :
    CanonicalRR (RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr) := by
  obtain ⟨ls, hv, hle, hname, hrdl, hrd⟩ := h
  rw [rrBytes_eq_rrWire hname hrdl]
  exact ⟨ls, rr.type, rr.class, rr.ttl, rr.rdata, hv, hle, hrd, rfl⟩

theorem rrWireCanon_of_parseRaw {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hc : CanonicalRR b)
    (hp : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    RRWireCanon rr := by
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, rfl⟩ := hc
  rw [parseRaw_rrWire ls hv hle t c ttl rdata (canonicalRdata_size_lt hrd)] at hp
  injection hp with hp
  subst hp
  refine ⟨ls, hv, hle, rfl, ?_, hrd⟩
  show (BitVec.ofNat 16 rdata.size).toNat = rdata.size
  rw [BitVec.toNat_ofNat]
  have h216 : 2 ^ 16 = 65536 := rfl
  have := canonicalRdata_size_lt hrd
  omega

theorem parseRaw_rrBytes {rr : VeriDNS.Spec.ResourceRecord} (h : RRWireCanon rr) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr) = some rr := by
  obtain ⟨ls, hv, hle, hname, hrdl, hrd⟩ := h
  have h216 : 2 ^ 16 = 65536 := rfl
  have hlt := rr.rdlength.isLt
  have hsz : rr.rdata.size < 65536 := by omega
  have hrdl' : BitVec.ofNat 16 rr.rdata.size = rr.rdlength := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  rw [rrBytes_eq_rrWire hname hrdl,
    parseRaw_rrWire ls hv hle rr.type rr.class rr.ttl rr.rdata hsz, hrdl', ← hname]

theorem rrWireCanon_set_ttl {rr : VeriDNS.Spec.ResourceRecord} (ttl : BitVec 32)
    (h : RRWireCanon rr) : RRWireCanon { rr with ttl := ttl } := by
  obtain ⟨ls, hv, hle, hname, hrdl, hrd⟩ := h
  exact ⟨ls, hv, hle, hname, hrdl, hrd⟩

theorem canonicalSection_map_rrBytes {rrs : Array VeriDNS.Spec.ResourceRecord}
    (h : ∀ rr ∈ rrs.toList, RRWireCanon rr) :
    CanonicalSection (rrs.map (RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))) := by
  intro b hb
  rw [Array.mem_map] at hb
  obtain ⟨rr, hrr, rfl⟩ := hb
  exact canonicalRR_rrBytes (h rr (by simpa using hrr))

theorem normRaws_rrWireCanon {raws : Array ByteArray}
    (hcanon : ∀ b ∈ raws.toList, CanonicalRR b) :
    ∀ b ∈ (Cache.normRaws raws).toList, ∀ rr,
      RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → RRWireCanon rr := by
  intro b hb rr hp
  unfold VeriDNS.Impl.Cache.normRaws at hb
  rw [List.toList_toArray, List.mem_map] at hb
  obtain ⟨rr', hrr', rfl⟩ := hb
  unfold VeriDNS.Impl.Cache.normalizeRRsetTtls at hrr'
  rw [List.mem_map] at hrr'
  obtain ⟨rr0, hrr0, rfl⟩ := hrr'
  unfold VeriDNS.Impl.Cache.rrsOf at hrr0
  rw [List.mem_filterMap] at hrr0
  obtain ⟨raw, hraw, hp0⟩ := hrr0
  have hp0' : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr0 := hp0
  have hwc : RRWireCanon { rr0 with
      ttl := VeriDNS.Impl.Cache.groupMinTtl
        (VeriDNS.Impl.Cache.rrsOf raws) rr0 } :=
    rrWireCanon_set_ttl _ (rrWireCanon_of_parseRaw (hcanon raw hraw) hp0')
  have hrt : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode { rr0 with
        ttl := VeriDNS.Impl.Cache.groupMinTtl (VeriDNS.Impl.Cache.rrsOf raws) rr0 }))
      = some { rr0 with
        ttl := VeriDNS.Impl.Cache.groupMinTtl (VeriDNS.Impl.Cache.rrsOf raws) rr0 } :=
    parseRaw_rrBytes hwc
  rw [hrt] at hp
  injection hp with hp
  subst hp
  exact hwc

def CacheRecCanon (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.records.toList, RRWireCanon e.rr

def CacheNegSoaCanon (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.negatives.toList, ∀ rr, e.soa = some rr → RRWireCanon rr

theorem cacheRecCanon_storeChecked (c : Cache.DnsCache) (rr : VeriDNS.Spec.ResourceRecord)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheRecCanon c)
    (hnew : RRWireCanon rr) : CacheRecCanon (c.storeChecked rr cred now) := by
  have hcase : c.storeChecked rr cred now = c
      ∨ c.storeChecked rr cred now = c.store rr now cred := by
    unfold VeriDNS.Impl.Cache.DnsCache.storeChecked
    by_cases hz : (rr.ttl == 0) = true
    · exact Or.inl (if_pos hz)
    · rw [if_neg hz]
      by_cases hb : (c.records.any fun e =>
          VeriDNS.Impl.DomainName.nameEqCI e.rr.name rr.name && e.rr.type == rr.type
            && e.rr.class == rr.class
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
          ⟨rr, now + rr.ttl.toNat.toUInt32, false, cred, now⟩ := rfl
    intro e he
    rw [hrec, Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [Array.toList_filter] at he
      exact h e (List.mem_filter.mp he).1
    · exact hnew

theorem cacheRecCanon_foldl_storeChecked (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) :
    ∀ (l : List ByteArray) (cache : Cache.DnsCache), CacheRecCanon cache →
      (∀ bytes ∈ l, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        RRWireCanon rr) →
      CacheRecCanon (l.foldl (fun c bytes =>
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
      | none => exact hc
      | some rr =>
        exact cacheRecCanon_storeChecked cache rr cred now hc
          (hraw b (List.mem_cons_self ..) rr hp)
    · intro bytes hb rr hp; exact hraw bytes (List.mem_cons_of_mem _ hb) rr hp

theorem cacheRecCanon_cacheRRs (cache : Cache.DnsCache) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheRecCanon cache)
    (hraw : ∀ bytes ∈ raws.toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        RRWireCanon rr) :
    CacheRecCanon (VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord)
      cache raws cred now) := by
  have heq : VeriDNS.Impl.Resolver.cacheRRs (RR := VeriDNS.Spec.ResourceRecord)
        cache raws cred now
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
  exact cacheRecCanon_foldl_storeChecked cred now raws.toList cache h hraw

theorem cacheRecCanon_cacheUnlessTruncated (cache : Cache.DnsCache)
    (resp : VeriDNS.Spec.Format) (raws : Array ByteArray)
    (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) (h : CacheRecCanon cache)
    (hraw : ∀ bytes ∈ (VeriDNS.Spec.RRParse.normalizeSection
          (RR := VeriDNS.Spec.ResourceRecord) raws).toList, ∀ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes = some rr →
        RRWireCanon rr) :
    CacheRecCanon (VeriDNS.Impl.Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      cache resp raws cred now) := by
  unfold VeriDNS.Impl.Resolver.cacheUnlessTruncated
  by_cases htc : (resp.header.tc == 1) = true
  · rw [if_pos htc]; exact h
  · rw [if_neg htc]
    exact cacheRecCanon_cacheRRs cache _ cred now h hraw

theorem cacheRecCanon_boundExpiryClasses (c : Cache.DnsCache) (h : CacheRecCanon c) :
    CacheRecCanon c.boundExpiryClasses := by
  intro e he
  unfold VeriDNS.Impl.Cache.DnsCache.boundExpiryClasses at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictClasses_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1

theorem cacheRecCanon_touchKeys (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheRecCanon c) : CacheRecCanon (c.touchKeys ks tnow) := by
  intro e he
  rw [Cache.touchKeys_records, Array.toList_map, List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  rw [Cache.touchEntry_rr]
  exact h e₀ he₀

theorem cacheRecCanon_boundLruKeys (c : Cache.DnsCache) (h : CacheRecCanon c) :
    CacheRecCanon c.boundLruKeys := by
  intro e he
  unfold VeriDNS.Impl.Cache.DnsCache.boundLruKeys at he
  obtain ⟨p, hp⟩ := VeriDNS.Impl.Cache.evictLruKeys_filter_form c.records c.records.size
  rw [hp, Array.toList_filter, List.mem_filter] at he
  exact h e he.1

theorem cacheRecCanon_boundLru (c : Cache.DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32) (h : CacheRecCanon c) : CacheRecCanon (c.boundLru ks tnow) :=
  cacheRecCanon_boundLruKeys _ (cacheRecCanon_touchKeys c ks tnow h)

theorem cacheRecCanon_storeNegative (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (rc : VeriDNS.Spec.Rcode) (soa : Option VeriDNS.Spec.ResourceRecord)
    (expiry now : UInt32) (h : CacheRecCanon c) :
    CacheRecCanon (c.storeNegative name qt qc rc soa expiry now) :=
  fun e he => h e he

theorem cacheNegSoaCanon_congr {c c' : Cache.DnsCache}
    (heq : c'.negatives = c.negatives) (h : CacheNegSoaCanon c) : CacheNegSoaCanon c' := by
  intro e he
  exact h e (by rw [heq] at he; exact he)

theorem cacheRecCanon_empty : CacheRecCanon Cache.DnsCache.empty := by
  intro e he
  simp [Cache.DnsCache.empty] at he

theorem cacheNegSoaCanon_empty : CacheNegSoaCanon Cache.DnsCache.empty := by
  intro e he
  simp [Cache.DnsCache.empty] at he

def CacheNegSoaOwner (c : Cache.DnsCache) : Prop :=
  ∀ e ∈ c.negatives.toList, ∀ rr, e.soa = some rr →
    Resolver.isAncestorB rr.name e.name = true

theorem cacheNegSoaOwner_congr {c c' : Cache.DnsCache}
    (heq : c'.negatives = c.negatives) (h : CacheNegSoaOwner c) : CacheNegSoaOwner c' := by
  intro e he
  exact h e (by rw [heq] at he; exact he)

theorem cacheNegSoaOwner_empty : CacheNegSoaOwner Cache.DnsCache.empty := by
  intro e he
  simp [Cache.DnsCache.empty] at he

theorem lookupAnswerable_rrWireCanon (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (h : CacheRecCanon c) :
    ∀ rr ∈ (c.lookupAnswerable name qt qc now).toList, RRWireCanon rr := by
  intro rr hmem
  rw [Cache.DnsCache.lookupAnswerable, Array.toList_filterMap, List.mem_filterMap] at hmem
  obtain ⟨e, he, hsome⟩ := hmem
  split at hsome
  · rw [Option.some.injEq] at hsome
    subst hsome
    exact rrWireCanon_set_ttl _ (h e he)
  · exact absurd hsome (by simp)

theorem findNegative_mem {c : Cache.DnsCache} {name : ByteArray} {qt qc : BitVec 16}
    {now : UInt32} {e : Cache.NegativeEntry}
    (h : c.findNegative name qt qc now = some e) : e ∈ c.negatives.toList := by
  unfold VeriDNS.Impl.Cache.DnsCache.findNegative at h
  cases ho : c.negatives.find? (fun e =>
      VeriDNS.Impl.DomainName.nameEqCI e.name name && e.qclass == qc
        && decide (e.expiry > now) && e.rcode == VeriDNS.Spec.Rcode.nameError) with
  | some e1 =>
    rw [ho] at h
    have : e1 = e := by
      simpa using h
    subst this
    simpa using Array.mem_of_find?_eq_some ho
  | none =>
    rw [ho] at h
    have h' : c.negatives.find? (fun e =>
        VeriDNS.Impl.DomainName.nameEqCI e.name name && e.qtype == qt && e.qclass == qc
          && decide (e.expiry > now)) = some e := h
    simpa using Array.mem_of_find?_eq_some h'

theorem lookupNegativeSoa_rrWireCanon (c : Cache.DnsCache) (name : ByteArray)
    (qt qc : BitVec 16) (now : UInt32) (h : CacheNegSoaCanon c) :
    ∀ rr ∈ (c.lookupNegativeSoa name qt qc now).toList, RRWireCanon rr := by
  intro rr hmem
  unfold VeriDNS.Impl.Cache.DnsCache.lookupNegativeSoa at hmem
  cases hf : c.findNegative name qt qc now with
  | none =>
    rw [hf] at hmem
    simp at hmem
  | some e =>
    rw [hf] at hmem
    dsimp only at hmem
    have he : e ∈ c.negatives.toList := findNegative_mem hf
    unfold VeriDNS.Impl.Cache.NegativeEntry.authority at hmem
    cases hsoa : e.soa with
    | none =>
      rw [hsoa] at hmem
      simp at hmem
    | some rr0 =>
      rw [hsoa] at hmem
      have : rr = { rr0 with ttl := BitVec.ofNat 32 (e.expiry - now).toNat } := by
        simpa using hmem
      subst this
      exact rrWireCanon_set_ttl _ (h e he rr0 hsoa)

theorem capTtls_frame (resp : VeriDNS.Spec.Format) :
    (Server.capTtls resp).header = resp.header
    ∧ (Server.capTtls resp).question = resp.question
    ∧ (Server.capTtls resp).answer.size = resp.answer.size
    ∧ (Server.capTtls resp).authority.size = resp.authority.size
    ∧ (Server.capTtls resp).additional.size = resp.additional.size :=
  ⟨rfl, rfl, Array.size_map .., Array.size_map .., Array.size_map ..⟩

end VeriDNS.Proof.DeliveredWire
