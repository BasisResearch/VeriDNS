import VeriDNS.Impl.ResourceRecord
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Primitives
import VeriDNS.Proof.DomainName

namespace VeriDNS.Proof.ResourceRecord

open VeriDNS.Impl
open VeriDNS.Spec

set_option maxHeartbeats 6400000 in

theorem decode_encode (rr : VeriDNS.Spec.ResourceRecord)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hname255 : (DomainName.labelsToWireFormat labels).size ≤ 255)
    (hqn : DomainName.labelsToWireFormat labels = rr.name)
    (hrl : rdlength_prop_0 rr) :
    DnsParser.run ResourceRecord.decode (DnsSerializer.runBytes (ResourceRecord.encode rr)) =
      .ok (rr, rr.name.size + 10 + rr.rdata.size) := by
  have hrl : rr.rdlength.toNat = rr.rdata.size := hrl
  obtain ⟨name, type_, class_, ttl, rdlength, rdata⟩ := rr
  simp only at hqn hrl ⊢
  subst hqn

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

  simp only [ResourceRecord.decode, Primitives.run_bind, Primitives.run_pure]

  have hdn : DnsParser.run DomainName.decodeName
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata) 0
      = .ok (labels, (DomainName.labelsToWireFormat labels).size) := by
    have h0 : DomainName.labelsToWireFormat labels ++ fb ++ rdata =
       ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ (fb ++ rdata) := by
      apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.data_empty]
    rw [h0]
    have := Proof.DomainName.decodeName_frame_labels labels hv hname255 ByteArray.empty (fb ++ rdata)
    simp only [ByteArray.size_empty, Nat.zero_add] at this
    exact this
  simp only [hdn]

  have hbds : (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size =
      (DomainName.labelsToWireFormat labels).size + 10 + rdata.size := by
    simp [ByteArray.size_data, ByteArray.size_append, fb]; omega

  simp only [Primitives.run_readBV16]

  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]

  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 2 + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]

  simp only [Primitives.run_readBV32]

  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 4 + 3 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]

  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 8 + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]

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
      (UInt8.ofBitVec (type_.setWidth 8)).toBitVec.setWidth 16 = type_ :=
    VeriDNS.Proof.Primitives.reassemble16 type_
  simp only [ht_id]

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
      (UInt8.ofBitVec (class_.setWidth 8)).toBitVec.setWidth 16 = class_ :=
    VeriDNS.Proof.Primitives.reassemble16 class_
  simp only [hc_id]

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
      (UInt8.ofBitVec (ttl.setWidth 8)).toBitVec.setWidth 32 = ttl :=
    VeriDNS.Proof.Primitives.reassemble32 ttl
  simp only [httl_id]

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
      (UInt8.ofBitVec (rdlength.setWidth 8)).toBitVec.setWidth 16 = rdlength :=
    VeriDNS.Proof.Primitives.reassemble16 rdlength
  simp only [hrl_id]

  simp only [Primitives.run_readBytes]
  simp only [if_pos (show (DomainName.labelsToWireFormat labels).size + 10 + rdlength.toNat ≤
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).size from by
    show _ ≤ (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size
    rw [hbds]; omega)]

  rw [hrl]

  have hext : (DomainName.labelsToWireFormat labels ++ fb ++ rdata).extract
      ((DomainName.labelsToWireFormat labels).size + 10)
      ((DomainName.labelsToWireFormat labels).size + 10 + rdata.size) = rdata := by
    have hpfx : (DomainName.labelsToWireFormat labels ++ fb).size =
        (DomainName.labelsToWireFormat labels).size + 10 := by
      simp [ByteArray.size_append, fb]; rfl

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

/-- **Decode SUCCEEDS on encode output** — the success-only weakening of `decode_encode`. For
    `parseRaw ≠ none` we only need `ResourceRecord.decode` to not *error* on `runBytes (encode rr)`, not to
    reproduce `rr` exactly. This drops `decode_encode`'s two heavy requirements: the exact size equality
    `rdlength.toNat = rdata.size` (here only `≤` is needed — `readBytes rdlength.toNat` succeeds because it
    reads no more than the available `rdata` bytes) and all the `bv_decide` value round-trips (the decoded
    type/class/ttl values are irrelevant to success). This is what the message-decoder's per-RR
    `parseRaw`-validity rides on (every `decodeRRCanonical` output is `encode` of a canonical RR with
    `rdlength := ofNat 16 rdata.size`, so `rdlength.toNat = rdata.size % 2^16 ≤ rdata.size`). -/
theorem decode_succeeds_of_encode (rr : VeriDNS.Spec.ResourceRecord)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hname255 : (DomainName.labelsToWireFormat labels).size ≤ 255)
    (hqn : DomainName.labelsToWireFormat labels = rr.name)
    (hle : rr.rdlength.toNat ≤ rr.rdata.size) :
    ∃ x, DnsParser.run ResourceRecord.decode
      (DnsSerializer.runBytes (ResourceRecord.encode rr)) = .ok x := by
  obtain ⟨name, type_, class_, ttl, rdlength, rdata⟩ := rr
  simp only at hqn hle ⊢
  subst hqn
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
  simp only [ResourceRecord.decode, Primitives.run_bind, Primitives.run_pure]
  have hdn : DnsParser.run DomainName.decodeName
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata) 0
      = .ok (labels, (DomainName.labelsToWireFormat labels).size) := by
    have h0 : DomainName.labelsToWireFormat labels ++ fb ++ rdata =
       ByteArray.empty ++ DomainName.labelsToWireFormat labels ++ (fb ++ rdata) := by
      apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.data_empty]
    rw [h0]
    have := Proof.DomainName.decodeName_frame_labels labels hv hname255 ByteArray.empty (fb ++ rdata)
    simp only [ByteArray.size_empty, Nat.zero_add] at this
    exact this
  simp only [hdn]
  have hbds : (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size =
      (DomainName.labelsToWireFormat labels).size + 10 + rdata.size := by
    simp [ByteArray.size_data, ByteArray.size_append, fb]; omega
  simp only [Primitives.run_readBV16, Primitives.run_readBV32]
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 2 + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 4 + 3 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
  simp only [dif_pos (show (DomainName.labelsToWireFormat labels).size + 8 + 1 <
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size from by rw [hbds]; omega)]
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
      (UInt8.ofBitVec (rdlength.setWidth 8)).toBitVec.setWidth 16 = rdlength :=
    VeriDNS.Proof.Primitives.reassemble16 rdlength
  simp only [hrl_id]
  simp only [Primitives.run_readBytes]
  simp only [if_pos (show (DomainName.labelsToWireFormat labels).size + 10 + rdlength.toNat ≤
      (DomainName.labelsToWireFormat labels ++ fb ++ rdata).size from by
    show _ ≤ (DomainName.labelsToWireFormat labels ++ fb ++ rdata).data.size
    rw [hbds]; omega)]
  exact ⟨_, rfl⟩

end VeriDNS.Proof.ResourceRecord
