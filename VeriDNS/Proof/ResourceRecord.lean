import VeriDNS.Impl.ResourceRecord
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Primitives
import VeriDNS.Proof.DomainName

namespace VeriDNS.Proof.ResourceRecord

open VeriDNS.Impl
open VeriDNS.Spec

set_option maxHeartbeats 6400000 in
/-- ResourceRecord roundtrip: decode ∘ encode = id.
    Requires domain name labels + rdlength consistency. -/
theorem decode_encode (rr : VeriDNS.Spec.ResourceRecord)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hqn : DomainName.labelsToWireFormat labels = rr.name)
    (hrl : rr.rdlength.toNat = rr.rdata.size) :
    DnsParser.run ResourceRecord.decode (DnsSerializer.runBytes (ResourceRecord.encode rr)) =
      .ok (rr, rr.name.size + 10 + rr.rdata.size) := by
  obtain ⟨name, type_, class_, ttl, rdlength, rdata⟩ := rr
  simp only at hqn hrl ⊢
  subst hqn
  -- Abbreviation for the 10 fixed bytes after the domain name
  let fb : ByteArray := ⟨#[UInt8.ofBitVec ((type_ >>> 8).setWidth 8),
     UInt8.ofBitVec (type_.setWidth 8),
     UInt8.ofBitVec ((class_ >>> 8).setWidth 8),
     UInt8.ofBitVec (class_.setWidth 8),
     UInt8.ofBitVec ((ttl >>> 24).setWidth 8),
     UInt8.ofBitVec ((ttl >>> 16).setWidth 8),
     UInt8.ofBitVec ((ttl >>> 8).setWidth 8),
     UInt8.ofBitVec (ttl.setWidth 8),
     UInt8.ofBitVec ((rdlength >>> 8).setWidth 8),
     UInt8.ofBitVec (rdlength.setWidth 8)]⟩
  -- Compute serializer buffer
  have hbuf : DnsSerializer.runBytes (ResourceRecord.encode
      { name := DomainName.labelsToWireFormat labels, type := type_, «class» := class_,
        ttl := ttl, rdlength := rdlength, rdata := rdata }) =
      DomainName.labelsToWireFormat labels ++ fb ++ rdata := by
    simp only [fb, ResourceRecord.encode, DnsSerializer.runBytes, StateT.run,
      DnsSerializer.writeBytes, writeBV16, writeBV32, DnsSerializer.writeUInt8,
      bind, StateT.bind, modify]
    unfold instMonadStateOfMonadStateOf
    simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]
    apply ByteArray.ext
    simp [ByteArray.data_push, ByteArray.data_append, ByteArray.data_empty]; rfl
  rw [hbuf]
  -- Unfold decoder
  simp only [ResourceRecord.decode, Primitives.run_bind, Primitives.run_pure]
  -- decodeName via frame lemma
  have hdn : DnsParser.run DomainName.decodeName
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata) 0
      = .ok (labels, (DomainName.labelsToWireFormat labels).size) := by
    have h0 : DomainName.labelsToWireFormat labels ++ fb ++ rdata =
       ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ (fb ++ rdata) := by
      apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.data_empty]
    rw [h0]
    have := Proof.DomainName.decodeName_frame_labels labels hv ByteArray.empty (fb ++ rdata)
    simp only [ByteArray.size_empty, Nat.zero_add] at this
    exact this
  simp only [hdn]
  -- Buffer data size fact
  have hbds : (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size =
      (DomainName.labelsToWireFormat labels).size + 10 + rdata.size := by
    simp [ByteArray.size_data, ByteArray.size_append, fb]; omega
  -- Unfold readBV16 (type_, class_, rdlength) and readBV32 (ttl)
  simp only [Primitives.run_readBV16]
  -- Resolve type_ bounds (pos = sz, need sz + 1 < buf.data.size)
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  -- Resolve class_ bounds (pos = sz + 2, need sz + 2 + 1 < buf.data.size)
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 2 + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  -- Unfold readBV32 for ttl
  simp only [Primitives.run_readBV32]
  -- Resolve ttl bounds (pos = sz + 4, need sz + 4 + 3 < buf.data.size)
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 4 + 3 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  -- Resolve rdlength bounds (pos = sz + 8, need sz + 8 + 1 < buf.data.size)
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 8 + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  -- Byte access for type_ (bytes at sz and sz + 1)
  have ht0 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size] =
      UInt8.ofBitVec ((type_ >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, fb]
  have ht1 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 1] =
      UInt8.ofBitVec (type_.setWidth 8) := by
    simp [ByteArray.data_append, fb]
  simp only [ht0, ht1]
  have ht_id : (UInt8.ofBitVec ((type_ >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (type_.setWidth 8)).toBitVec.setWidth 16 = type_ := by bv_decide
  simp only [ht_id]
  -- Byte access for class_ (bytes at sz + 2 and sz + 3)
  have hc0 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 2] =
      UInt8.ofBitVec ((class_ >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, fb]
  have hc1 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 2 + 1] =
      UInt8.ofBitVec (class_.setWidth 8) := by
    show ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
      )[(DomainName.labelsToWireFormat labels).size + 3] =
        UInt8.ofBitVec (class_.setWidth 8)
    simp [ByteArray.data_append, fb]
  simp only [hc0, hc1]
  have hc_id : (UInt8.ofBitVec ((class_ >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (class_.setWidth 8)).toBitVec.setWidth 16 = class_ := by bv_decide
  simp only [hc_id]
  -- Byte access for ttl (4 bytes at sz + 4 .. sz + 7)
  have httl0 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 4] =
      UInt8.ofBitVec ((ttl >>> 24).setWidth 8) := by
    simp [ByteArray.data_append, fb]
  have httl1 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 4 + 1] =
      UInt8.ofBitVec ((ttl >>> 16).setWidth 8) := by
    show ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
      )[(DomainName.labelsToWireFormat labels).size + 5] =
        UInt8.ofBitVec ((ttl >>> 16).setWidth 8)
    simp [ByteArray.data_append, fb]
  have httl2 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 4 + 2] =
      UInt8.ofBitVec ((ttl >>> 8).setWidth 8) := by
    show ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
      )[(DomainName.labelsToWireFormat labels).size + 6] =
        UInt8.ofBitVec ((ttl >>> 8).setWidth 8)
    simp [ByteArray.data_append, fb]
  have httl3 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 4 + 3] =
      UInt8.ofBitVec (ttl.setWidth 8) := by
    show ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
      )[(DomainName.labelsToWireFormat labels).size + 7] =
        UInt8.ofBitVec (ttl.setWidth 8)
    simp [ByteArray.data_append, fb]
  simp only [httl0, httl1, httl2, httl3]
  have httl_id : (UInt8.ofBitVec ((ttl >>> 24).setWidth 8)).toBitVec.setWidth 32 <<< 24 |||
      (UInt8.ofBitVec ((ttl >>> 16).setWidth 8)).toBitVec.setWidth 32 <<< 16 |||
      (UInt8.ofBitVec ((ttl >>> 8).setWidth 8)).toBitVec.setWidth 32 <<< 8 |||
      (UInt8.ofBitVec (ttl.setWidth 8)).toBitVec.setWidth 32 = ttl := by bv_decide
  simp only [httl_id]
  -- Byte access for rdlength (bytes at sz + 8 and sz + 9)
  have hrl0 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 8] =
      UInt8.ofBitVec ((rdlength >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, fb]
  have hrl1 : ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
    )[(DomainName.labelsToWireFormat labels).size + 8 + 1] =
      UInt8.ofBitVec (rdlength.setWidth 8) := by
    show ((DomainName.labelsToWireFormat labels ++ fb ++ rdata).data
      )[(DomainName.labelsToWireFormat labels).size + 9] =
        UInt8.ofBitVec (rdlength.setWidth 8)
    simp [ByteArray.data_append, fb]
  simp only [hrl0, hrl1]
  have hrl_id : (UInt8.ofBitVec ((rdlength >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (rdlength.setWidth 8)).toBitVec.setWidth 16 = rdlength := by bv_decide
  simp only [hrl_id]
  -- readBytes for rdata
  simp only [Primitives.run_readBytes]
  simp only [if_pos (show (DomainName.labelsToWireFormat labels).size + 10 + rdlength.toNat ≤
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).size from by
    show _ ≤ (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size
    rw [hbds]; omega)]
  -- Rewrite rdlength.toNat to rdata.size
  rw [hrl]
  -- Prove extract equality: extracting rdata portion from buffer = rdata
  have hext : (DomainName.labelsToWireFormat labels ++ fb ++ rdata).extract
      ((DomainName.labelsToWireFormat labels).size + 10)
      ((DomainName.labelsToWireFormat labels).size + 10 + rdata.size) = rdata := by
    have hpfx : (DomainName.labelsToWireFormat labels ++ fb).size =
        (DomainName.labelsToWireFormat labels).size + 10 := by
      simp [ByteArray.size_append, fb]; rfl
    -- Rewrite as (prefix ++ rdata).extract prefix.size (prefix.size + rdata.size) = rdata
    show ((DomainName.labelsToWireFormat labels ++ fb) ++ rdata).extract
        ((DomainName.labelsToWireFormat labels).size + 10)
        ((DomainName.labelsToWireFormat labels).size + 10 + rdata.size) = rdata
    rw [← hpfx]
    ext1
    simp only [ByteArray.data_extract, ByteArray.data_append]
    rw [← Array.toList_inj, Array.toList_extract, Array.toList_append,
        List.extract_eq_take_drop, Nat.add_sub_cancel_left]
    simp only [ByteArray.size, Array.size_eq_length_toList, ByteArray.data_append,
        Array.toList_append, List.length_append]
    rw [← List.length_append, List.drop_left, List.take_length]
  simp only [hext]

end VeriDNS.Proof.ResourceRecord
