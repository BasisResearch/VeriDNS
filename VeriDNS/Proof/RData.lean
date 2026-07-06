import VeriDNS.Impl.RData
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Primitives
import VeriDNS.Proof.DomainName

namespace VeriDNS.Proof.RData

open VeriDNS.Impl
open VeriDNS.Spec

theorem decode_encode_a (r : RData.A.ARdata) :
    DnsParser.run RData.decodeA (DnsSerializer.runBytes (RData.encodeA r)) =
      .ok (r, 4) := by
  simp only [RData.decodeA, RData.encodeA, Primitives.run_bind, Primitives.run_pure, Primitives.readBV32_writeBV32]

theorem decode_encode_cname_raw (cname : ByteArray)
    (h : DnsParser.run (VeriDNS.Impl.DomainName.decodeName >>= fun labels =>
         pure (VeriDNS.Impl.DomainName.labelsToWireFormat labels)) cname 0 = .ok (cname, cname.size)) :
    DnsParser.run RData.decodeCname (DnsSerializer.runBytes (RData.encodeCname ⟨cname⟩)) =
      .ok (⟨cname⟩, cname.size) := by
   simp at h
   revert h
   simp [RData.decodeCname, RData.encodeCname, DnsParser.run, DnsSerializer.runBytes, VeriDNS.Impl.RData.encodeDomainNameRdata, RData.decodeDomainNameRdata]
   simp [Functor.map, StateT.map, Except.map]
   grind

private theorem uint8_ofNat_toNat (n : Nat) (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2^8)]

private theorem readUInt8_eq {buf : ByteArray} {pos : Nat} {v : UInt8}
    (hsize : pos < buf.data.size) (hval : buf.data[pos] = v) :
    DnsParser.run DnsParser.readUInt8 buf pos = .ok (v, pos + 1) := by
  simp only [Primitives.run_readUInt8, dif_pos hsize]
  congr 1; exact Prod.ext hval rfl

private theorem readBytes_eq {buf : ByteArray} {pos n : Nat} {expected : ByteArray}
    (hsize : pos + n ≤ buf.size) (hval : buf.extract pos (pos + n) = expected) :
    DnsParser.run (DnsParser.readBytes n) buf pos = .ok (expected, pos + n) := by
  simp only [Primitives.run_readBytes, if_pos hsize]
  congr 1; exact Prod.ext hval rfl

theorem decode_encode_hinfo (r : RData.Hinfo.HinfoRdata)
    (hc : r.cpu.size < 256) (ho : r.os.size < 256) :
    DnsParser.run RData.decodeHinfo (DnsSerializer.runBytes (RData.encodeHinfo r)) =
      .ok (r, r.cpu.size + r.os.size + 2) := by

  simp [DnsSerializer.runBytes, StateT.run, RData.encodeHinfo, bind, StateT.bind,
        DnsSerializer.writeUInt8, modify, DnsSerializer.writeBytes]
  unfold instMonadStateOfMonadStateOf
  simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]

  have hbuf_dsize : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data.size = r.cpu.size + r.os.size + 2 := by
    simp [ByteArray.size_data]; omega
  have hbuf_size : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).size = r.cpu.size + r.os.size + 2 := by
    simp [ByteArray.size_push, ByteArray.size_append]; omega

  show DnsParser.run RData.decodeHinfo _ 0 = _
  simp only [RData.decodeHinfo, Primitives.run_bind, Primitives.run_pure]

  rw [Primitives.run_readUInt8]
  have h0 : (0 : Nat) < ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data.size := by rw [hbuf_dsize]; omega
  simp only [dif_pos h0]

  have helem0 : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data[0]'h0 = UInt8.ofNat r.cpu.size := by
    conv in (_ : ByteArray).data =>
      rw [ByteArray.data_append, ByteArray.data_push, ByteArray.data_append, ByteArray.data_push]
    simp
  simp only [helem0, uint8_ofNat_toNat r.cpu.size hc]

  rw [Primitives.run_readBytes]
  simp only [show 1 + r.cpu.size ≤ ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).size from by rw [hbuf_size]; omega, ite_true]

  have hext_cpu : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).extract 1 (1 + r.cpu.size) = r.cpu := by
    apply ByteArray.ext
    rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_push,
        ByteArray.data_append, ByteArray.data_push]
    simp [Array.size_push]
  simp only [hext_cpu]

  rw [Primitives.run_readUInt8]
  have h1 : 0 + 1 + r.cpu.size < ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data.size := by rw [hbuf_dsize]; omega
  simp only [dif_pos h1]

  have helem1 : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data[0 + 1 + r.cpu.size]'h1 = UInt8.ofNat r.os.size := by
    conv in (_ : ByteArray).data =>
      rw [ByteArray.data_append, ByteArray.data_push, ByteArray.data_append, ByteArray.data_push]
    simp [Array.getElem_push, Array.size_push]
  simp only [helem1, uint8_ofNat_toNat r.os.size ho]

  rw [Primitives.run_readBytes]
  simp only [show 0 + 1 + r.cpu.size + 1 + r.os.size ≤ ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).size from by rw [hbuf_size]; omega, ite_true]

  have hext_os : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).extract (0 + 1 + r.cpu.size + 1)
      (0 + 1 + r.cpu.size + 1 + r.os.size) = r.os := by
    apply ByteArray.ext
    rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_push,
        ByteArray.data_append, ByteArray.data_push]
    rw [Array.extract_append_of_size_left_le_start
        (by simp [Array.size_push, Array.size_append]; omega)]
    rw [Array.size_push, Array.size_append, ByteArray.data, Array.size_push, ByteArray.data_empty, Array.size_empty]
    simp
  simp only [hext_os]

  cases r; simp; omega

open DomainName in

theorem decodeDomainNameRdata_frame_labels
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hle : (labelsToWireFormat labels).size ≤ 255)
    (pre suf : ByteArray) :
    DnsParser.run RData.decodeDomainNameRdata
      (pre ++ labelsToWireFormat labels ++ suf) pre.size
    = .ok (labelsToWireFormat labels,
           pre.size + (labelsToWireFormat labels).size) := by
  simp only [RData.decodeDomainNameRdata, Primitives.run_bind, Primitives.run_map]
  simp only [DomainName.decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure]

  simp only [labelsToWireFormat]
  have hvl : ∀ l ∈ labels.toList, 0 < l.size ∧ l.size ≤ 63 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hl)
    exact hv i hi
  have hfuel_base : labels.toList.length <
      (labelsToWireFormatGo labels.toList).size := by
    induction labels.toList with
    | nil => simp [labelsToWireFormatGo]; decide
    | cons l rest ih =>
      simp [labelsToWireFormatGo, ByteArray.size_append, ByteArray.size_push]
      have := Proof.DomainName.labelsToWireFormatGo_size_pos rest; omega
  have hfuel : labels.toList.length <
      (pre ++ labelsToWireFormatGo labels.toList ++ suf).size := by
    simp only [ByteArray.size_append]; omega
  have h := Proof.DomainName.decodeNameAux_prepend_append pre suf labels.toList
    hvl _ hfuel
  rw [h]
  simp only [Array.toArray_toList]
  rw [if_pos (by rw [Proof.DomainName.encodedNameLen_eq]; exact hle)]
  simp [Array.toArray_toList]

set_option maxHeartbeats 800000 in
theorem decode_encode_mx (r : RData.Mx.MxRdata)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hle_exch : (DomainName.labelsToWireFormat labels).size ≤ 255)
    (hexch : DomainName.labelsToWireFormat labels = r.exchange) :
    DnsParser.run RData.decodeMx (DnsSerializer.runBytes (RData.encodeMx r)) =
      .ok (r, r.exchange.size + 2) := by

  have hbuf : DnsSerializer.runBytes (RData.encodeMx r) =
      (ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
        (UInt8.ofBitVec (r.preference.setWidth 8)) ++ r.exchange := by
    simp [RData.encodeMx, RData.encodeDomainNameRdata, DnsSerializer.runBytes,
      StateT.run, writeBV16, DnsSerializer.writeUInt8, DnsSerializer.writeBytes,
      bind, StateT.bind, modify]
    unfold instMonadStateOfMonadStateOf
    simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]
  rw [hbuf, ← hexch]

  simp only [RData.decodeMx, Primitives.run_bind, Primitives.run_pure, Primitives.run_readBV16]

  have hbv_size : (0 : Nat) + 1 <
      ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
        (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels).data.size := by
    simp [ByteArray.size_data, ByteArray.size_append, ByteArray.size_push,
      DomainName.labelsToWireFormat]
    have := Proof.DomainName.labelsToWireFormatGo_size_pos labels.toList; omega
  simp only [dif_pos hbv_size]

  have hb0 : ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels).data[0]'(by omega) =
      UInt8.ofBitVec ((r.preference >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, ByteArray.data_push]
  have hb1 : ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels).data[0 + 1] =
      UInt8.ofBitVec (r.preference.setWidth 8) := by
    simp [ByteArray.data_append, ByteArray.data_push]
  simp only [hb0, hb1]

  have hpref : (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (r.preference.setWidth 8)).toBitVec.setWidth 16 = r.preference :=
    VeriDNS.Proof.Primitives.reassemble16 r.preference
  simp only [hpref]

  rw [show (0 : Nat) + 1 + 1 = ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8))).size from by simp [ByteArray.size_push]]
  rw [show (ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels =
    (ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels ++ ByteArray.empty from by
    ext1; simp [ByteArray.data_append]]
  rw [decodeDomainNameRdata_frame_labels labels hv hle_exch _ _]
  simp [ByteArray.size_push, ByteArray.size_append, DomainName.labelsToWireFormat]
  obtain ⟨preference, exchange⟩ := r; subst hexch; simp [DomainName.labelsToWireFormat]; omega

set_option maxHeartbeats 6400000 in
theorem decode_encode_soa (r : RData.Soa.SoaRdata)
    (mlabels rlabels : Array ByteArray)
    (hmv : Proof.DomainName.ValidLabels mlabels)
    (hrv : Proof.DomainName.ValidLabels rlabels)
    (hle_m : (DomainName.labelsToWireFormat mlabels).size ≤ 255)
    (hle_r : (DomainName.labelsToWireFormat rlabels).size ≤ 255)
    (hmn : DomainName.labelsToWireFormat mlabels = r.mname)
    (hrn : DomainName.labelsToWireFormat rlabels = r.rname) :
    DnsParser.run RData.decodeSoa (DnsSerializer.runBytes (RData.encodeSoa r)) =
      .ok (r, r.mname.size + r.rname.size + 20) := by
  obtain ⟨mname, rname, serial, refresh, retry, expire, minimum⟩ := r
  simp only at hmn hrn ⊢
  subst hmn; subst hrn

  let fb : ByteArray := ⟨#[
    UInt8.ofBitVec ((serial >>> 24).setWidth 8), UInt8.ofBitVec ((serial >>> 16).setWidth 8),
    UInt8.ofBitVec ((serial >>> 8).setWidth 8), UInt8.ofBitVec (serial.setWidth 8),
    UInt8.ofBitVec ((refresh >>> 24).setWidth 8), UInt8.ofBitVec ((refresh >>> 16).setWidth 8),
    UInt8.ofBitVec ((refresh >>> 8).setWidth 8), UInt8.ofBitVec (refresh.setWidth 8),
    UInt8.ofBitVec ((retry >>> 24).setWidth 8), UInt8.ofBitVec ((retry >>> 16).setWidth 8),
    UInt8.ofBitVec ((retry >>> 8).setWidth 8), UInt8.ofBitVec (retry.setWidth 8),
    UInt8.ofBitVec ((expire >>> 24).setWidth 8), UInt8.ofBitVec ((expire >>> 16).setWidth 8),
    UInt8.ofBitVec ((expire >>> 8).setWidth 8), UInt8.ofBitVec (expire.setWidth 8),
    UInt8.ofBitVec ((minimum >>> 24).setWidth 8), UInt8.ofBitVec ((minimum >>> 16).setWidth 8),
    UInt8.ofBitVec ((minimum >>> 8).setWidth 8), UInt8.ofBitVec (minimum.setWidth 8)]⟩

  have hbuf : DnsSerializer.runBytes (RData.encodeSoa
      { mname := DomainName.labelsToWireFormat mlabels,
        rname := DomainName.labelsToWireFormat rlabels,
        serial, refresh, retry, expire, minimum }) =
      DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb := by
    simp only [fb, RData.encodeSoa, RData.encodeDomainNameRdata, DnsSerializer.runBytes, StateT.run,
      DnsSerializer.writeBytes, writeBV32, DnsSerializer.writeUInt8,
      bind, StateT.bind, modify]
    unfold instMonadStateOfMonadStateOf
    simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]
    apply ByteArray.ext
    simp [ByteArray.data_push, ByteArray.data_append, ByteArray.data_empty]; rfl
  rw [hbuf]

  simp only [RData.decodeSoa, Primitives.run_bind, Primitives.run_pure]

  have hmn_dec : DnsParser.run RData.decodeDomainNameRdata
      (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb) 0 =
      .ok (DomainName.labelsToWireFormat mlabels,
           (DomainName.labelsToWireFormat mlabels).size) := by
    have h0 : DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb =
       ByteArray.empty ++ DomainName.labelsToWireFormat mlabels ++
         (DomainName.labelsToWireFormat rlabels ++ fb) := by
      apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.data_empty]
    rw [h0]
    have := decodeDomainNameRdata_frame_labels mlabels hmv hle_m ByteArray.empty
      (DomainName.labelsToWireFormat rlabels ++ fb)
    simp only [ByteArray.size_empty, Nat.zero_add] at this
    exact this
  simp only [hmn_dec]

  have hrn_dec : DnsParser.run RData.decodeDomainNameRdata
      (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
      (DomainName.labelsToWireFormat mlabels).size =
      .ok (DomainName.labelsToWireFormat rlabels,
           (DomainName.labelsToWireFormat mlabels).size +
             (DomainName.labelsToWireFormat rlabels).size) := by
    exact decodeDomainNameRdata_frame_labels rlabels hrv hle_r
      (DomainName.labelsToWireFormat mlabels) fb
  simp only [hrn_dec]

  have hbds : (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++
      fb).data.size =
      (DomainName.labelsToWireFormat mlabels).size +
        (DomainName.labelsToWireFormat rlabels).size + 20 := by
    simp [ByteArray.size_data, ByteArray.size_append, fb]; rfl

  have h_serial := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size)
    serial (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 0 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 1 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 2 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 3 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_serial]

  have h_refresh := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 4)
    refresh (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 4 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 5 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 6 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 7 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_refresh]

  have h_retry := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 8)
    retry (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 8 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 9 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 10 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 11 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_retry]

  have h_expire := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 12)
    expire (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 12 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 13 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 14 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 15 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_expire]

  have h_minimum := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 16)
    minimum (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 16 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 17 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 18 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 19 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_minimum]

end VeriDNS.Proof.RData
