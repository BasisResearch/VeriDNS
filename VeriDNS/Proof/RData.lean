import VeriDNS.Impl.RData
import VeriDNS.Impl.Parsec
import VeriDNS.Proof.Primitives
import VeriDNS.Proof.DomainName

namespace VeriDNS.Proof.RData

open VeriDNS.Impl
open VeriDNS.Spec

-- ============================================================
-- A RDATA roundtrip (fixed 4 bytes)
-- ============================================================

theorem decode_encode_a (r : RData.A.ARdata) :
    DnsParser.run RData.decodeA (DnsSerializer.runBytes (RData.encodeA r)) =
      .ok (r, 4) := by
  simp only [RData.decodeA, RData.encodeA, Primitives.run_bind, Primitives.run_pure, Primitives.readBV32_writeBV32]

-- ============================================================
-- CNAME roundtrip
-- CNAME decode reads a domain name (via decodeName),
-- CNAME encode writes raw bytes (via writeBytes).
-- The roundtrip requires domain name decode/encode correspondence
-- which involves compression pointer handling.
-- We prove a simpler form: decode raw bytes written by writeBytes.
-- ============================================================


/-- CNAME roundtrip for raw wire-format names (no compression).
    Since encodeCname writes raw bytes, decodeCname must parse them
    back as a domain name. This is only valid for uncompressed names
    where the wire format IS the identity under decode-then-labelsToWireFormat. -/
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

-- ============================================================
-- HINFO roundtrip
-- ============================================================

-- HINFO involves readUInt8 + readBytes, which go through the monadic parser.
-- The proof requires ByteArray lemmas for push + extract roundtrips.
-- We state the theorem with the necessary size constraints.

-- Helper: UInt8 roundtrip for sizes < 256
private theorem uint8_ofNat_toNat (n : Nat) (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2^8)]

-- Helper: readUInt8 on a buffer at position pos, where data[pos] = v
private theorem readUInt8_eq {buf : ByteArray} {pos : Nat} {v : UInt8}
    (hsize : pos < buf.data.size) (hval : buf.data[pos] = v) :
    DnsParser.run DnsParser.readUInt8 buf pos = .ok (v, pos + 1) := by
  simp only [Primitives.run_readUInt8, dif_pos hsize]
  congr 1; exact Prod.ext hval rfl

-- Helper: readBytes on a buffer, where extract gives the expected ByteArray
private theorem readBytes_eq {buf : ByteArray} {pos n : Nat} {expected : ByteArray}
    (hsize : pos + n ≤ buf.size) (hval : buf.extract pos (pos + n) = expected) :
    DnsParser.run (DnsParser.readBytes n) buf pos = .ok (expected, pos + n) := by
  simp only [Primitives.run_readBytes, if_pos hsize]
  congr 1; exact Prod.ext hval rfl

theorem decode_encode_hinfo (r : RData.Hinfo.HinfoRdata)
    (hc : r.cpu.size < 256) (ho : r.os.size < 256) :
    DnsParser.run RData.decodeHinfo (DnsSerializer.runBytes (RData.encodeHinfo r)) =
      .ok (r, r.cpu.size + r.os.size + 2) := by
  -- Phase 1: Reduce serializer to concrete buffer
  simp [DnsSerializer.runBytes, StateT.run, RData.encodeHinfo, bind, StateT.bind,
        DnsSerializer.writeUInt8, modify, DnsSerializer.writeBytes]
  unfold instMonadStateOfMonadStateOf
  simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]
  -- Phase 2: Unfold decoder into the full DnsParser computation
  -- Use the Primitives run_bind + run_readUInt8 + run_readBytes + run_pure approach
  -- but apply them step-by-step with have lemmas for ByteArray facts.
  -- Key buffer facts
  have hbuf_dsize : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data.size = r.cpu.size + r.os.size + 2 := by
    simp [ByteArray.size_data]; omega
  have hbuf_size : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).size = r.cpu.size + r.os.size + 2 := by
    simp [ByteArray.size_push, ByteArray.size_append]; omega
  -- Unfold decoder using Primitives lemmas
  show DnsParser.run RData.decodeHinfo _ 0 = _
  simp only [RData.decodeHinfo, Primitives.run_bind, Primitives.run_pure]
  -- Step 1: readUInt8 at pos 0
  rw [Primitives.run_readUInt8]
  have h0 : (0 : Nat) < ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data.size := by rw [hbuf_dsize]; omega
  simp only [dif_pos h0]
  -- Now need: buf.data[0]'h0 and then match reduces to .ok branch
  -- Show buf.data[0] = UInt8.ofNat r.cpu.size
  have helem0 : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data[0]'h0 = UInt8.ofNat r.cpu.size := by
    conv in (_ : ByteArray).data =>
      rw [ByteArray.data_append, ByteArray.data_push, ByteArray.data_append, ByteArray.data_push]
    simp
  simp only [helem0, uint8_ofNat_toNat r.cpu.size hc]
  -- Step 2: readBytes r.cpu.size at pos 1
  rw [Primitives.run_readBytes]
  simp only [show 1 + r.cpu.size ≤ ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).size from by rw [hbuf_size]; omega, ite_true]
  -- Show extract gives r.cpu
  have hext_cpu : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).extract 1 (1 + r.cpu.size) = r.cpu := by
    apply ByteArray.ext
    rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_push,
        ByteArray.data_append, ByteArray.data_push]
    simp [Array.size_push]
  simp only [hext_cpu]
  -- Step 3: readUInt8 at pos (0 + 1 + r.cpu.size) = (1 + r.cpu.size)
  rw [Primitives.run_readUInt8]
  have h1 : 0 + 1 + r.cpu.size < ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data.size := by rw [hbuf_dsize]; omega
  simp only [dif_pos h1]
  -- Show buf.data[1 + cpu.size] = UInt8.ofNat r.os.size
  have helem1 : ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).data[0 + 1 + r.cpu.size]'h1 = UInt8.ofNat r.os.size := by
    conv in (_ : ByteArray).data =>
      rw [ByteArray.data_append, ByteArray.data_push, ByteArray.data_append, ByteArray.data_push]
    simp [Array.getElem_push, Array.size_push]
  simp only [helem1, uint8_ofNat_toNat r.os.size ho]
  -- Step 4: readBytes r.os.size at pos (0 + 1 + r.cpu.size + 1)
  rw [Primitives.run_readBytes]
  simp only [show 0 + 1 + r.cpu.size + 1 + r.os.size ≤ ((ByteArray.empty.push (UInt8.ofNat r.cpu.size) ++ r.cpu).push
      (UInt8.ofNat r.os.size) ++ r.os).size from by rw [hbuf_size]; omega, ite_true]
  -- Show extract gives r.os
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
  -- Final: struct eta + arithmetic
  cases r; simp; omega

-- ============================================================
-- Frame independence for domain name RDATA parsing
-- ============================================================

open DomainName in
/-- decodeDomainNameRdata on `pre ++ wireFormat ++ suf` at `pre.size`
    decodes the domain name correctly, given valid labels. -/
theorem decodeDomainNameRdata_frame_labels
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (pre suf : ByteArray) :
    DnsParser.run RData.decodeDomainNameRdata
      (pre ++ labelsToWireFormat labels ++ suf) pre.size
    = .ok (labelsToWireFormat labels,
           pre.size + (labelsToWireFormat labels).size) := by
  simp only [RData.decodeDomainNameRdata, Primitives.run_bind, Primitives.run_map]
  simp only [DomainName.decodeName, Primitives.run_bind, Primitives.run_getBuffer,
    Primitives.run_getPos, Primitives.run_setPos, Primitives.run_pure]
  -- Goal now involves decodeNameAux on (pre ++ wire ++ suf)
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
  rw [h]; simp [Array.toArray_toList]

-- ============================================================
-- MX roundtrip
-- ============================================================

set_option maxHeartbeats 800000 in
theorem decode_encode_mx (r : RData.Mx.MxRdata)
    (labels : Array ByteArray) (hv : Proof.DomainName.ValidLabels labels)
    (hexch : DomainName.labelsToWireFormat labels = r.exchange) :
    DnsParser.run RData.decodeMx (DnsSerializer.runBytes (RData.encodeMx r)) =
      .ok (r, r.exchange.size + 2) := by
  -- Compute the serialized buffer
  have hbuf : DnsSerializer.runBytes (RData.encodeMx r) =
      (ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
        (UInt8.ofBitVec (r.preference.setWidth 8)) ++ r.exchange := by
    simp [RData.encodeMx, RData.encodeDomainNameRdata, DnsSerializer.runBytes,
      StateT.run, writeBV16, DnsSerializer.writeUInt8, DnsSerializer.writeBytes,
      bind, StateT.bind, modify]
    unfold instMonadStateOfMonadStateOf
    simp [MonadStateOf.modifyGet, StateT.modifyGet, pure]
  rw [hbuf, ← hexch]
  -- The buffer is now: bv16_prefix ++ labelsToWireFormat labels
  -- Unfold decoder into readBV16 >> decodeDomainNameRdata
  simp only [RData.decodeMx, Primitives.run_bind, Primitives.run_pure, Primitives.run_readBV16]
  -- Resolve readBV16 bounds check
  have hbv_size : (0 : Nat) + 1 <
      ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
        (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels).data.size := by
    simp [ByteArray.size_data, ByteArray.size_append, ByteArray.size_push,
      DomainName.labelsToWireFormat]
    have := Proof.DomainName.labelsToWireFormatGo_size_pos labels.toList; omega
  simp only [dif_pos hbv_size]
  -- Byte access: bytes 0 and 1 are the BV16 encoding
  have hb0 : ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels).data[0]'(by omega) =
      UInt8.ofBitVec ((r.preference >>> 8).setWidth 8) := by
    simp [ByteArray.data_append, ByteArray.data_push]
  have hb1 : ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels).data[0 + 1] =
      UInt8.ofBitVec (r.preference.setWidth 8) := by
    simp [ByteArray.data_append, ByteArray.data_push]
  simp only [hb0, hb1]
  -- BV16 byte identity
  have hpref : (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8)).toBitVec.setWidth 16 <<< 8 |||
      (UInt8.ofBitVec (r.preference.setWidth 8)).toBitVec.setWidth 16 = r.preference := by
    simp [UInt8.ofBitVec, UInt8.toBitVec]; bv_decide
  simp only [hpref]
  -- Now need decodeDomainNameRdata at pos 2 on the buffer
  -- Rewrite 0 + 1 + 1 = 2, and add empty suffix for frame lemma
  rw [show (0 : Nat) + 1 + 1 = ((ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8))).size from by simp [ByteArray.size_push]]
  rw [show (ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels =
    (ByteArray.empty.push (UInt8.ofBitVec ((r.preference >>> 8).setWidth 8))).push
      (UInt8.ofBitVec (r.preference.setWidth 8)) ++ DomainName.labelsToWireFormat labels ++ ByteArray.empty from by
    ext1; simp [ByteArray.data_append]]
  rw [decodeDomainNameRdata_frame_labels labels hv _ _]
  simp [ByteArray.size_push, ByteArray.size_append, DomainName.labelsToWireFormat]
  obtain ⟨preference, exchange⟩ := r; subst hexch; simp [DomainName.labelsToWireFormat]; omega

-- ============================================================
-- SOA roundtrip
-- ============================================================

set_option maxHeartbeats 6400000 in
theorem decode_encode_soa (r : RData.Soa.SoaRdata)
    (mlabels rlabels : Array ByteArray)
    (hmv : Proof.DomainName.ValidLabels mlabels)
    (hrv : Proof.DomainName.ValidLabels rlabels)
    (hmn : DomainName.labelsToWireFormat mlabels = r.mname)
    (hrn : DomainName.labelsToWireFormat rlabels = r.rname) :
    DnsParser.run RData.decodeSoa (DnsSerializer.runBytes (RData.encodeSoa r)) =
      .ok (r, r.mname.size + r.rname.size + 20) := by
  obtain ⟨mname, rname, serial, refresh, retry, expire, minimum⟩ := r
  simp only at hmn hrn ⊢
  subst hmn; subst hrn
  -- 20 fixed bytes (5 × BV32)
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
  -- Compute serializer buffer
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
  -- Unfold decoder
  simp only [RData.decodeSoa, Primitives.run_bind, Primitives.run_pure]
  -- Decode mname
  have hmn_dec : DnsParser.run RData.decodeDomainNameRdata
      (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb) 0 =
      .ok (DomainName.labelsToWireFormat mlabels,
           (DomainName.labelsToWireFormat mlabels).size) := by
    have h0 : DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb =
       ByteArray.empty ++ DomainName.labelsToWireFormat mlabels ++
         (DomainName.labelsToWireFormat rlabels ++ fb) := by
      apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.data_empty]
    rw [h0]
    have := decodeDomainNameRdata_frame_labels mlabels hmv ByteArray.empty
      (DomainName.labelsToWireFormat rlabels ++ fb)
    simp only [ByteArray.size_empty, Nat.zero_add] at this
    exact this
  simp only [hmn_dec]
  -- Decode rname
  have hrn_dec : DnsParser.run RData.decodeDomainNameRdata
      (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
      (DomainName.labelsToWireFormat mlabels).size =
      .ok (DomainName.labelsToWireFormat rlabels,
           (DomainName.labelsToWireFormat mlabels).size +
             (DomainName.labelsToWireFormat rlabels).size) := by
    exact decodeDomainNameRdata_frame_labels rlabels hrv
      (DomainName.labelsToWireFormat mlabels) fb
  simp only [hrn_dec]
  -- Buffer data size fact
  have hbds : (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++
      fb).data.size =
      (DomainName.labelsToWireFormat mlabels).size +
        (DomainName.labelsToWireFormat rlabels).size + 20 := by
    simp [ByteArray.size_data, ByteArray.size_append, fb]; rfl
  -- Read serial (BV32 at ms + rs)
  have h_serial := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size)
    serial (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 0 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 1 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 2 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 3 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_serial]
  -- Read refresh (BV32 at ms + rs + 4)
  have h_refresh := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 4)
    refresh (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 4 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 5 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 6 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 7 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_refresh]
  -- Read retry (BV32 at ms + rs + 8)
  have h_retry := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 8)
    retry (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 8 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 9 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 10 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 11 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_retry]
  -- Read expire (BV32 at ms + rs + 12)
  have h_expire := Primitives.readBV32_at
    (DomainName.labelsToWireFormat mlabels ++ DomainName.labelsToWireFormat rlabels ++ fb)
    ((DomainName.labelsToWireFormat mlabels).size + (DomainName.labelsToWireFormat rlabels).size + 12)
    expire (by rw [hbds]; omega)
    (by rw [Primitives.byte_at_suffix _ _ fb _ 12 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 13 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 14 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
    (by rw [Primitives.byte_at_suffix _ _ fb _ 15 (by omega) (by rw [hbds]; omega) (by simp [fb])]; simp [fb])
  simp only [h_expire]
  -- Read minimum (BV32 at ms + rs + 16)
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
