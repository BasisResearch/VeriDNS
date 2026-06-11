import VeriDNS.Impl.Question
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Primitives
import VeriDNS.Proof.DomainName

namespace VeriDNS.Proof.Question

open VeriDNS.Impl
open VeriDNS.Spec

set_option maxHeartbeats 1600000 in
theorem decode_encode (q : VeriDNS.Spec.Question)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hqn : DomainName.labelsToWireFormat labels = q.qname) :
    DnsParser.run Question.decode (DnsSerializer.runBytes (Question.encode q)) =
      .ok (q, q.qname.size + 4) := by
  obtain ⟨qname, qtype, qclass⟩ := q
  simp only at hqn ⊢
  subst hqn
  -- Abbreviation for the buffer suffix
  let suf : ByteArray := ⟨#[UInt8.ofBitVec ((qtype >>> 8).setWidth 8),
     UInt8.ofBitVec (qtype.setWidth 8),
     UInt8.ofBitVec ((qclass >>> 8).setWidth 8),
     UInt8.ofBitVec (qclass.setWidth 8)]⟩
  -- Step 1: Compute serializer buffer
  have hbuf : DnsSerializer.runBytes (Question.encode
      { qname := DomainName.labelsToWireFormat labels, qtype, qclass }) =
      ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf := by
    simp only [suf, Question.encode, DnsSerializer.runBytes, StateT.run,
      DnsSerializer.writeBytes, writeBV16, DnsSerializer.writeUInt8,
      bind, StateT.bind, modify]
    unfold instMonadStateOfMonadStateOf
    simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]
    apply ByteArray.ext; simp [ByteArray.data_push, ByteArray.data_append, ByteArray.data]; rfl
  rw [hbuf]
  -- Step 2: Unfold decoder
  simp only [Question.decode, Primitives.run_bind, Primitives.run_pure]
  -- Step 3: decodeName via frame lemma
  have hdn : DnsParser.run DomainName.decodeName
      (ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf) 0
      = .ok (labels, (DomainName.labelsToWireFormat labels).size) := by
    have := Proof.DomainName.decodeName_frame_labels labels hv ByteArray.empty suf
    simp only [ByteArray.size_empty, Nat.zero_add] at this
    exact this
  simp only [hdn]
  -- Buffer data size fact
  have hbds : (ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data.size =
      (DomainName.labelsToWireFormat labels).size + 4 := by
    simp [ByteArray.size_data, ByteArray.size_append, suf]
  -- Steps 4-5: readBV16 for qtype and qclass
  simp only [Primitives.run_readBV16]
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 1 < (ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data.size from by rw [hbds]; omega)]
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 2 + 1 < (ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data.size from by rw [hbds]; omega)]
  -- Byte access for qtype (wrapping .data in parens to avoid line break parsing)
  have hqt0 : ((ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data
    )[(DomainName.labelsToWireFormat labels).size] =
      UInt8.ofBitVec ((qtype >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, suf]
  have hqt1 : ((ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data
    )[(DomainName.labelsToWireFormat labels).size + 1] =
      UInt8.ofBitVec (qtype.setWidth 8) := by
    simp [ByteArray.data_append, suf]
  simp only [hqt0, hqt1]
  have hqt_id : (UInt8.ofBitVec ((qtype >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (qtype.setWidth 8)).toBitVec.setWidth 16 = qtype := by bv_decide
  simp only [hqt_id]
  -- Byte access for qclass
  have hqc0 : ((ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data
    )[(DomainName.labelsToWireFormat labels).size + 2] =
      UInt8.ofBitVec ((qclass >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, suf]
  have hqc1 : ((ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data
    )[(DomainName.labelsToWireFormat labels).size + 2 + 1] =
      UInt8.ofBitVec (qclass.setWidth 8) := by
    show ((ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ suf).data
      )[(DomainName.labelsToWireFormat labels).size + 3] =
        UInt8.ofBitVec (qclass.setWidth 8)
    simp [ByteArray.data_append, suf]
  simp only [hqc0, hqc1]
  have hqc_id : (UInt8.ofBitVec ((qclass >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (qclass.setWidth 8)).toBitVec.setWidth 16 = qclass := by bv_decide
  simp only [hqc_id]

end VeriDNS.Proof.Question
