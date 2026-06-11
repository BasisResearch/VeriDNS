import VeriDNS.Impl.Message
import VeriDNS.Proof.Header
import VeriDNS.Proof.Question
import VeriDNS.Proof.ResourceRecord
import VeriDNS.Proof.DomainName

namespace VeriDNS.Proof.Message

open VeriDNS.Impl
open VeriDNS.Spec

-- ============================================================
-- ByteArray helpers
-- ============================================================

theorem ba_append_assoc (a b c : ByteArray) : a ++ b ++ c = a ++ (b ++ c) := by
  apply ByteArray.ext; simp [ByteArray.data_append, Array.append_assoc]

theorem ba_empty_append (a : ByteArray) : ByteArray.empty ++ a = a := by
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem ba_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem ba_push_eq_append (a : ByteArray) (b : UInt8) :
    a.push b = a ++ ⟨#[b]⟩ := by
  apply ByteArray.ext; simp [ByteArray.data_push, ByteArray.data_append]

/-- Concatenation of a list of byte arrays. -/
def baConcat : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | b :: rest => b ++ baConcat rest

@[simp] theorem baConcat_nil : baConcat [] = ByteArray.empty := rfl

@[simp] theorem baConcat_cons (b : ByteArray) (rest : List ByteArray) :
    baConcat (b :: rest) = b ++ baConcat rest := rfl

-- ============================================================
-- Serializer "appends" framework: a write-only serializer run from
-- any initial buffer appends a fixed byte string.
-- ============================================================

def Appends (s : DnsSerializer Unit) (bytes : ByteArray) : Prop :=
  ∀ init : ByteArray, (StateT.run s init).2 = init ++ bytes

theorem appends_runBytes {s : DnsSerializer Unit} {b : ByteArray}
    (h : Appends s b) : DnsSerializer.runBytes s = b := by
  show (StateT.run s ByteArray.empty).2 = b
  rw [h ByteArray.empty, ba_empty_append]

/-- Restate an `Appends` fact with `runBytes s` as the byte string. -/
theorem appends_norm {s : DnsSerializer Unit} {b : ByteArray}
    (h : Appends s b) : Appends s (DnsSerializer.runBytes s) := by
  rw [appends_runBytes h]; exact h

theorem appends_pure : Appends (pure ()) ByteArray.empty := by
  intro init
  show init = init ++ ByteArray.empty
  rw [ba_append_empty]

theorem appends_writeUInt8 (b : UInt8) :
    Appends (DnsSerializer.writeUInt8 b) ⟨#[b]⟩ := by
  intro init
  show init.push b = init ++ ⟨#[b]⟩
  exact ba_push_eq_append init b

theorem appends_writeBytes (bs : ByteArray) :
    Appends (DnsSerializer.writeBytes bs) bs := by
  intro init; rfl

theorem appends_seq {s1 s2 : DnsSerializer Unit} {b1 b2 : ByteArray}
    (h1 : Appends s1 b1) (h2 : Appends s2 b2) :
    Appends (s1 >>= fun _ => s2) (b1 ++ b2) := by
  intro init
  show (StateT.run s2 (StateT.run s1 init).2).2 = init ++ (b1 ++ b2)
  rw [h1, h2, ba_append_assoc]

theorem appends_writeBV16 (v : BitVec 16) :
    Appends (writeBV16 v)
      (⟨#[UInt8.ofBitVec ((v >>> 8).setWidth 8)]⟩ ++ ⟨#[UInt8.ofBitVec (v.setWidth 8)]⟩) :=
  appends_seq (appends_writeUInt8 _) (appends_writeUInt8 _)

theorem appends_writeUInt16BE (v : UInt16) :
    Appends (DnsSerializer.writeUInt16BE v)
      (⟨#[(v >>> 8).toUInt8]⟩ ++ ⟨#[(v &&& 0xFF).toUInt8]⟩) :=
  appends_seq (appends_writeUInt8 _) (appends_writeUInt8 _)

theorem appends_header (h : VeriDNS.Spec.Header) :
    Appends (Header.encode h) (DnsSerializer.runBytes (Header.encode h)) := by
  apply appends_norm (b := _)
  exact appends_seq (appends_writeBV16 h.id)
    (appends_seq (appends_writeUInt16BE _)
      (appends_seq (appends_writeBV16 h.qdcount)
        (appends_seq (appends_writeBV16 h.ancount)
          (appends_seq (appends_writeBV16 h.nscount) (appends_writeBV16 h.arcount)))))

theorem appends_question (q : VeriDNS.Spec.Question) :
    Appends (Question.encode q) (DnsSerializer.runBytes (Question.encode q)) := by
  apply appends_norm (b := _)
  exact appends_seq (appends_writeBytes q.qname)
    (appends_seq (appends_writeBV16 q.qtype) (appends_writeBV16 q.qclass))

theorem appends_encodeList {α : Type} (enc : α → DnsSerializer Unit) (f : α → ByteArray)
    (henc : ∀ x, Appends (enc x) (f x)) :
    ∀ l : List α, Appends (Impl.Message.encodeList enc l) (baConcat (l.map f))
  | [] => by
    simp only [Impl.Message.encodeList, List.map_nil, baConcat_nil]
    exact appends_pure
  | x :: rest => by
    simp only [Impl.Message.encodeList, List.map_cons, baConcat_cons]
    exact appends_seq (henc x) (appends_encodeList enc f henc rest)

/-- The encoder output decomposes into header bytes followed by the
    concatenated per-item encodings of the four sections. -/
theorem encode_eq (msg : Format) :
    Impl.Message.encode msg =
      DnsSerializer.runBytes (Header.encode msg.header) ++
      (baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
       (baConcat msg.answer.toList ++
        (baConcat msg.authority.toList ++ baConcat msg.additional.toList))) := by
  apply appends_runBytes
  have hid : ∀ l : List ByteArray, l.map id = l := fun l => List.map_id l
  have hrr : ∀ l : List ByteArray,
      Appends (Impl.Message.encodeList DnsSerializer.writeBytes l) (baConcat l) := by
    intro l
    have := appends_encodeList DnsSerializer.writeBytes id (fun x => appends_writeBytes x) l
    rwa [hid] at this
  exact appends_seq (appends_header msg.header)
    (appends_seq (appends_encodeList _ _ (fun q => appends_question q) msg.question.toList)
      (appends_seq (hrr msg.answer.toList)
        (appends_seq (hrr msg.authority.toList) (hrr msg.additional.toList))))

-- ============================================================
-- Header frame lemma: decoding from encoded-header-plus-suffix
-- ============================================================

theorem header_size (h : VeriDNS.Spec.Header) :
    (DnsSerializer.runBytes (Header.encode h)).size = 12 := rfl

open VeriDNS.Proof in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 64000000 in
/-- Header decode is insensitive to trailing bytes: decoding from an encoded
    header followed by any suffix recovers the header and stops at byte 12. -/
theorem header_frame (h : VeriDNS.Spec.Header) (suf : ByteArray) :
    DnsParser.run Header.decode (DnsSerializer.runBytes (Header.encode h) ++ suf) 0 =
      .ok (h, 12) := by
  conv in DnsSerializer.runBytes _ =>
    unfold DnsSerializer.runBytes Header.encode writeBV16
    unfold DnsSerializer.writeUInt16BE DnsSerializer.writeUInt8
    dsimp only [modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
                bind, StateT.bind, pure, StateT.pure, StateT.run,
                EStateM.modifyGet, EStateM.bind, EStateM.pure]
  simp (config := { decide := true }) only [
    Header.decode, Primitives.run_bind, Primitives.run_pure,
    Primitives.run_readBV16, Primitives.run_readUInt16BE, Primitives.run_fail,
    ByteArray.data_append, Array.size_append, Array.getElem_append_left,
    Array.toList_append,
    ByteArray.data_push, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.getElem_push, Array.size, Array.empty, Array.emptyWithCapacity,
    Array.toList_push, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd,
    show (1 < 12 + suf.data.toList.length) = True from eq_true (by omega),
    show (3 < 12 + suf.data.toList.length) = True from eq_true (by omega),
    show (5 < 12 + suf.data.toList.length) = True from eq_true (by omega),
    show (7 < 12 + suf.data.toList.length) = True from eq_true (by omega),
    show (9 < 12 + suf.data.toList.length) = True from eq_true (by omega),
    show (11 < 12 + suf.data.toList.length) = True from eq_true (by omega),
    dite_true, dite_false,
    Parsec.bv16_roundtrip,
    Primitives.uint16_byte_roundtrip,
    Primitives.bv16_byte_identity,
    BitPacking.unpack_pack,
    Enum.opcode_ofBV4_toBV4, Enum.rcode_ofBV4_toBV4]

-- ============================================================
-- Question frame lemma: decoding an encoded question at any position
-- ============================================================

/-- The 4 trailing qtype/qclass bytes of an encoded question. -/
def tcBytes (qtype qclass : BitVec 16) : ByteArray :=
  ⟨#[UInt8.ofBitVec ((qtype >>> 8).setWidth 8), UInt8.ofBitVec (qtype.setWidth 8),
     UInt8.ofBitVec ((qclass >>> 8).setWidth 8), UInt8.ofBitVec (qclass.setWidth 8)]⟩

theorem tcBytes_size (qtype qclass : BitVec 16) : (tcBytes qtype qclass).size = 4 := rfl

/-- The serialized question is its qname followed by the 4 type/class bytes. -/
theorem question_bytes (q : VeriDNS.Spec.Question) :
    DnsSerializer.runBytes (Question.encode q) = q.qname ++ tcBytes q.qtype q.qclass :=
  (appends_runBytes (appends_seq (appends_writeBytes q.qname)
    (appends_seq (appends_writeBV16 q.qtype) (appends_writeBV16 q.qclass)))).trans (by rfl)

set_option maxHeartbeats 3200000 in
/-- Question decode frame lemma: decoding an encoded question embedded at any
    position recovers the question and advances exactly past its encoding. -/
theorem question_frame (q : VeriDNS.Spec.Question)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hqn : Impl.DomainName.labelsToWireFormat labels = q.qname)
    (pre suf : ByteArray) :
    DnsParser.run Question.decode
      (pre ++ DnsSerializer.runBytes (Question.encode q) ++ suf) pre.size
    = .ok (q, pre.size + (DnsSerializer.runBytes (Question.encode q)).size) := by
  obtain ⟨qname, qtype, qclass⟩ := q
  simp only at hqn
  subst hqn
  rw [question_bytes]
  simp only []
  have hassoc : pre ++ (Impl.DomainName.labelsToWireFormat labels ++ tcBytes qtype qclass) ++ suf
      = pre ++ Impl.DomainName.labelsToWireFormat labels ++ (tcBytes qtype qclass ++ suf) := by
    rw [← ba_append_assoc pre (Impl.DomainName.labelsToWireFormat labels) (tcBytes qtype qclass),
        ba_append_assoc (pre ++ Impl.DomainName.labelsToWireFormat labels)
          (tcBytes qtype qclass) suf]
  rw [hassoc]
  simp only [Question.decode, Primitives.run_bind]
  rw [Proof.DomainName.decodeName_frame_labels labels hv pre (tcBytes qtype qclass ++ suf)]
  simp only [Primitives.run_bind, Primitives.run_readBV16, Primitives.run_pure]
  -- buffer size fact
  have hsz : (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data.size =
      pre.size + (Impl.DomainName.labelsToWireFormat labels).size + 4 + suf.size := by
    simp [ByteArray.size_data, ByteArray.size_append, tcBytes_size]; omega
  -- resolve the two bounds checks
  simp only [dif_pos (show pre.size + (Impl.DomainName.labelsToWireFormat labels).size + 1 <
    (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data.size from by rw [hsz]; omega)]
  simp only [dif_pos (show pre.size + (Impl.DomainName.labelsToWireFormat labels).size + 2 + 1 <
    (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data.size from by rw [hsz]; omega)]
  -- byte accesses into the 4-byte type/class suffix
  have hb0 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data[pre.size +
        (Impl.DomainName.labelsToWireFormat labels).size]'hlt =
      UInt8.ofBitVec ((qtype >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat labels)
      (tcBytes qtype qclass ++ suf) _ 0 (by omega) _
      (by simp [ByteArray.size_data, ByteArray.size_append, tcBytes_size]; omega)]
    simp [ByteArray.data_append, tcBytes]
  have hb1 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data[pre.size +
        (Impl.DomainName.labelsToWireFormat labels).size + 1]'hlt =
      UInt8.ofBitVec (qtype.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat labels)
      (tcBytes qtype qclass ++ suf) _ 1 (by omega) _
      (by simp [ByteArray.size_data, ByteArray.size_append, tcBytes_size]; omega)]
    simp [ByteArray.data_append, tcBytes]
  have hb2 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data[pre.size +
        (Impl.DomainName.labelsToWireFormat labels).size + 2]'hlt =
      UInt8.ofBitVec ((qclass >>> 8).setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat labels)
      (tcBytes qtype qclass ++ suf) _ 2 (by omega) _
      (by simp [ByteArray.size_data, ByteArray.size_append, tcBytes_size]; omega)]
    simp [ByteArray.data_append, tcBytes]
  have hb3 : ∀ (hlt : _), (pre ++ Impl.DomainName.labelsToWireFormat labels ++
      (tcBytes qtype qclass ++ suf)).data[pre.size +
        (Impl.DomainName.labelsToWireFormat labels).size + 2 + 1]'hlt =
      UInt8.ofBitVec (qclass.setWidth 8) := by
    intro hlt
    rw [Primitives.byte_at_suffix pre (Impl.DomainName.labelsToWireFormat labels)
      (tcBytes qtype qclass ++ suf) _ 3 (by omega) _
      (by simp [ByteArray.size_data, ByteArray.size_append, tcBytes_size]; omega)]
    simp [ByteArray.data_append, tcBytes]
  simp only [hb0, hb1, hb2, hb3]
  have hqt_id : (UInt8.ofBitVec ((qtype >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (qtype.setWidth 8)).toBitVec.setWidth 16 = qtype := by bv_decide
  have hqc_id : (UInt8.ofBitVec ((qclass >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (qclass.setWidth 8)).toBitVec.setWidth 16 = qclass := by bv_decide
  simp only [hqt_id, hqc_id]
  have hpos : pre.size + (Impl.DomainName.labelsToWireFormat labels).size + 2 + 2 =
      pre.size + (Impl.DomainName.labelsToWireFormat labels ++ tcBytes qtype qclass).size := by
    simp [ByteArray.size_append, tcBytes_size]; omega
  rw [hpos]

-- ============================================================
-- Sequential parse induction: decoding n items from concatenated
-- per-item encodings, given a frame property for each item.
-- ============================================================

/-- Parsing `pairs.length` items from the concatenation of their encodings
    recovers all items and consumes exactly the concatenated bytes, provided
    each (item, encoding) pair satisfies the frame property. -/
theorem run_decodeMany {α : Type} (p : DnsParser α) :
    ∀ (pairs : List (α × ByteArray)),
    (∀ x ∈ pairs, ∀ (pre suf : ByteArray),
      DnsParser.run p (pre ++ x.2 ++ suf) pre.size = .ok (x.1, pre.size + x.2.size)) →
    ∀ (pre suf : ByteArray) (acc : Array α),
    DnsParser.run (Impl.Message.decodeMany p pairs.length acc)
      (pre ++ baConcat (pairs.map (·.2)) ++ suf) pre.size
    = .ok (acc ++ (pairs.map (·.1)).toArray,
           pre.size + (baConcat (pairs.map (·.2))).size)
  | [], _, pre, suf, acc => by
    simp [Impl.Message.decodeMany, Primitives.run_pure, ByteArray.size_empty]
  | hd :: tl, hframe, pre, suf, acc => by
    simp only [List.length_cons, List.map_cons, baConcat_cons, Impl.Message.decodeMany,
      Primitives.run_bind]
    have hassoc : pre ++ (hd.2 ++ baConcat (tl.map (·.2))) ++ suf
        = pre ++ hd.2 ++ (baConcat (tl.map (·.2)) ++ suf) := by
      rw [← ba_append_assoc pre hd.2 (baConcat (tl.map (·.2))),
          ba_append_assoc (pre ++ hd.2) (baConcat (tl.map (·.2))) suf]
    rw [hassoc, hframe hd List.mem_cons_self pre (baConcat (tl.map (·.2)) ++ suf)]
    have hpre : pre.size + hd.2.size = (pre ++ hd.2).size := (ByteArray.size_append).symm
    have hbuf : pre ++ hd.2 ++ (baConcat (tl.map (·.2)) ++ suf)
        = (pre ++ hd.2) ++ baConcat (tl.map (·.2)) ++ suf :=
      (ba_append_assoc (pre ++ hd.2) (baConcat (tl.map (·.2))) suf).symm
    rw [hbuf, hpre]
    simp only []
    rw [run_decodeMany p tl (fun x hx => hframe x (List.mem_cons_of_mem hd hx))
        (pre ++ hd.2) suf (acc.push hd.1)]
    congr 1
    refine Prod.ext ?_ ?_
    · show acc.push hd.1 ++ (tl.map (·.1)).toArray = acc ++ (hd.1 :: tl.map (·.1)).toArray
      apply Array.ext'
      simp
    · show (pre ++ hd.2).size + (baConcat (tl.map (·.2))).size
        = pre.size + (hd.2 ++ baConcat (tl.map (·.2))).size
      simp [ByteArray.size_append]; omega

-- ============================================================
-- Validity hypotheses and the main roundtrip theorem
-- ============================================================

/-- Each question has a valid label decomposition. -/
structure ValidQuestions (qs : Array VeriDNS.Spec.Question) where
  labels : (i : Fin qs.size) → Array ByteArray
  valid : ∀ i, DomainName.ValidLabels (labels i)
  corresponds : ∀ i, Impl.DomainName.labelsToWireFormat (labels i) = qs[i].qname

/-- Each answer/authority/additional byte sequence is canonical wire format:
    `decodeRRCanonical` embedded at any position reproduces exactly the same
    bytes and consumes exactly them. This is the invariant `decode` maintains
    (it canonicalizes every RR via `decodeRRCanonical`) and what `encode`
    (which writes RR bytes raw) needs to roundtrip. -/
structure ValidRRBytes (rrs : Array ByteArray) where
  canonical : ∀ (i : Fin rrs.size) (pre suf : ByteArray),
    DnsParser.run Impl.Message.decodeRRCanonical (pre ++ rrs[i] ++ suf) pre.size
      = .ok (rrs[i], pre.size + rrs[i].size)

/-- Questions paired with their encodings, for `run_decodeMany`. -/
private def qpairs (qs : Array VeriDNS.Spec.Question)
    : List (VeriDNS.Spec.Question × ByteArray) :=
  qs.toList.map fun q => (q, DnsSerializer.runBytes (Question.encode q))

/-- RR byte sequences paired with themselves (encoding = raw bytes). -/
private def rrpairs (rrs : Array ByteArray) : List (ByteArray × ByteArray) :=
  rrs.toList.map fun rr => (rr, rr)

private theorem qpairs_length (qs : Array VeriDNS.Spec.Question) :
    (qpairs qs).length = qs.size := by simp [qpairs]

private theorem qpairs_items (qs : Array VeriDNS.Spec.Question) :
    (qpairs qs).map (·.1) = qs.toList := by
  simp only [qpairs, List.map_map]
  show List.map (fun q => q) qs.toList = qs.toList
  simp

private theorem qpairs_encs (qs : Array VeriDNS.Spec.Question) :
    (qpairs qs).map (·.2) =
      qs.toList.map fun q => DnsSerializer.runBytes (Question.encode q) := by
  simp [qpairs]

private theorem rrpairs_length (rrs : Array ByteArray) :
    (rrpairs rrs).length = rrs.size := by simp [rrpairs]

private theorem rrpairs_items (rrs : Array ByteArray) :
    (rrpairs rrs).map (·.1) = rrs.toList := by
  simp only [rrpairs, List.map_map]
  show List.map (fun rr => rr) rrs.toList = rrs.toList
  simp

private theorem rrpairs_encs (rrs : Array ByteArray) :
    (rrpairs rrs).map (·.2) = rrs.toList := by
  simp only [rrpairs, List.map_map]
  show List.map (fun rr => rr) rrs.toList = rrs.toList
  simp

private theorem qpairs_frame (qs : Array VeriDNS.Spec.Question) (hvq : ValidQuestions qs) :
    ∀ x ∈ qpairs qs, ∀ (pre suf : ByteArray),
      DnsParser.run Question.decode (pre ++ x.2 ++ suf) pre.size
        = .ok (x.1, pre.size + x.2.size) := by
  intro x hx pre suf
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hq)
  exact question_frame _ (hvq.labels ⟨i, hi⟩) (hvq.valid ⟨i, hi⟩)
    (hvq.corresponds ⟨i, hi⟩) pre suf

private theorem rrpairs_frame (rrs : Array ByteArray) (hv : ValidRRBytes rrs) :
    ∀ x ∈ rrpairs rrs, ∀ (pre suf : ByteArray),
      DnsParser.run Impl.Message.decodeRRCanonical (pre ++ x.2 ++ suf) pre.size
        = .ok (x.1, pre.size + x.2.size) := by
  intro x hx pre suf
  obtain ⟨rr, hrr, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hrr)
  exact hv.canonical ⟨i, hi⟩ pre suf

set_option maxHeartbeats 3200000 in
/-- Full message roundtrip: decode ∘ encode = id, given count fields match
    section sizes — each stated as its generated count predicate
    (`format_qdcount_counts_question` etc., from the §4.1 "specifying the
    number of entries" field descriptions) — questions have valid domain
    names, and RR byte sequences are canonical wire format. -/
theorem decode_encode (msg : Format)
    (hqd : format_qdcount_counts_question msg)
    (han : format_ancount_counts_answer msg)
    (hns : format_nscount_counts_authority msg)
    (har : format_arcount_counts_additional msg)
    (hvq : ValidQuestions msg.question)
    (hva : ValidRRBytes msg.answer)
    (hvn : ValidRRBytes msg.authority)
    (hvd : ValidRRBytes msg.additional) :
    Impl.Message.decode (Impl.Message.encode msg) = .ok msg := by
  have hqd : msg.header.qdcount.toNat = msg.question.size := hqd
  have han : msg.header.ancount.toNat = msg.answer.size := han
  have hns : msg.header.nscount.toNat = msg.authority.size := hns
  have har : msg.header.arcount.toNat = msg.additional.size := har
  -- Section encodings
  have hQ : DnsParser.run
      (Impl.Message.decodeMany Question.decode msg.question.size #[])
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        (baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
         (baConcat msg.answer.toList ++
          (baConcat msg.authority.toList ++ baConcat msg.additional.toList)))) 12
      = .ok (msg.question,
          12 + (baConcat (msg.question.toList.map fun q =>
            DnsSerializer.runBytes (Question.encode q))).size) := by
    have h0 := run_decodeMany Question.decode (qpairs msg.question)
      (qpairs_frame _ hvq)
      (DnsSerializer.runBytes (Header.encode msg.header))
      (baConcat msg.answer.toList ++
        (baConcat msg.authority.toList ++ baConcat msg.additional.toList)) #[]
    rw [qpairs_encs, qpairs_length, qpairs_items] at h0
    rw [ba_append_assoc, header_size] at h0
    simpa using h0
  have hA : DnsParser.run
      (Impl.Message.decodeMany Impl.Message.decodeRRCanonical msg.answer.size #[])
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        (baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
         (baConcat msg.answer.toList ++
          (baConcat msg.authority.toList ++ baConcat msg.additional.toList))))
      (12 + (baConcat (msg.question.toList.map fun q =>
        DnsSerializer.runBytes (Question.encode q))).size)
      = .ok (msg.answer,
          12 + (baConcat (msg.question.toList.map fun q =>
            DnsSerializer.runBytes (Question.encode q))).size +
            (baConcat msg.answer.toList).size) := by
    have h0 := run_decodeMany Impl.Message.decodeRRCanonical (rrpairs msg.answer)
      (rrpairs_frame _ hva)
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)))
      (baConcat msg.authority.toList ++ baConcat msg.additional.toList) #[]
    rw [rrpairs_encs, rrpairs_length, rrpairs_items] at h0
    rw [ba_append_assoc (_ ++ _), ba_append_assoc, ByteArray.size_append, header_size] at h0
    simpa using h0
  have hN : DnsParser.run
      (Impl.Message.decodeMany Impl.Message.decodeRRCanonical msg.authority.size #[])
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        (baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
         (baConcat msg.answer.toList ++
          (baConcat msg.authority.toList ++ baConcat msg.additional.toList))))
      (12 + (baConcat (msg.question.toList.map fun q =>
        DnsSerializer.runBytes (Question.encode q))).size +
        (baConcat msg.answer.toList).size)
      = .ok (msg.authority,
          12 + (baConcat (msg.question.toList.map fun q =>
            DnsSerializer.runBytes (Question.encode q))).size +
            (baConcat msg.answer.toList).size + (baConcat msg.authority.toList).size) := by
    have h0 := run_decodeMany Impl.Message.decodeRRCanonical (rrpairs msg.authority)
      (rrpairs_frame _ hvn)
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
        baConcat msg.answer.toList)
      (baConcat msg.additional.toList) #[]
    rw [rrpairs_encs, rrpairs_length, rrpairs_items] at h0
    rw [ba_append_assoc (_ ++ _ ++ _), ba_append_assoc (_ ++ _), ba_append_assoc,
        ByteArray.size_append, ByteArray.size_append, header_size] at h0
    simpa using h0
  have hD : DnsParser.run
      (Impl.Message.decodeMany Impl.Message.decodeRRCanonical msg.additional.size #[])
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        (baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
         (baConcat msg.answer.toList ++
          (baConcat msg.authority.toList ++ baConcat msg.additional.toList))))
      (12 + (baConcat (msg.question.toList.map fun q =>
        DnsSerializer.runBytes (Question.encode q))).size +
        (baConcat msg.answer.toList).size + (baConcat msg.authority.toList).size)
      = .ok (msg.additional,
          12 + (baConcat (msg.question.toList.map fun q =>
            DnsSerializer.runBytes (Question.encode q))).size +
            (baConcat msg.answer.toList).size + (baConcat msg.authority.toList).size +
            (baConcat msg.additional.toList).size) := by
    have h0 := run_decodeMany Impl.Message.decodeRRCanonical (rrpairs msg.additional)
      (rrpairs_frame _ hvd)
      (DnsSerializer.runBytes (Header.encode msg.header) ++
        baConcat (msg.question.toList.map fun q => DnsSerializer.runBytes (Question.encode q)) ++
        baConcat msg.answer.toList ++ baConcat msg.authority.toList)
      ByteArray.empty #[]
    rw [rrpairs_encs, rrpairs_length, rrpairs_items] at h0
    rw [ba_append_empty (_ ++ _),
        ba_append_assoc (_ ++ _ ++ _), ba_append_assoc (_ ++ _), ba_append_assoc,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
        header_size] at h0
    simpa using h0
  -- Assemble
  simp only [Impl.Message.decode]
  rw [encode_eq]
  simp only [Primitives.run_bind]
  rw [header_frame msg.header]
  simp only []
  rw [hqd, hQ]
  simp only []
  rw [han, hA]
  simp only []
  rw [hns, hN]
  simp only []
  rw [har, hD]
  simp only [Primitives.run_pure]

/-- `ValidQuestions` discharges the generated `format_question_qname_valid`
    (qname "a domain name represented as a sequence of labels", each label
    1–63 octets), with the abstract label decomposition instantiated by the
    wire-format decoder: every question's qname decodes to labels within
    the RFC 1035 §2.3.1 bounds. -/
theorem validQuestions_qname_valid (msg : Format)
    (hvq : ValidQuestions msg.question) :
    format_question_qname_valid
      (fun b => (Impl.DomainName.wireFormatToLabels b).toOption.getD #[]) msg := by
  intro i hi l hl
  simp only [] at hl
  have hval := hvq.valid ⟨i, hi⟩
  have hcorr : Impl.DomainName.labelsToWireFormat (hvq.labels ⟨i, hi⟩)
      = msg.question[i].qname := by
    simpa using hvq.corresponds ⟨i, hi⟩
  rw [← hcorr, DomainName.wireFormat_roundtrip _ hval] at hl
  simp only [Except.toOption, Option.getD_some] at hl
  obtain ⟨j, hj, hjl⟩ := Array.getElem_of_mem hl
  rw [← hjl]
  exact hval j hj

end VeriDNS.Proof.Message
