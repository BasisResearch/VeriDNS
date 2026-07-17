import VeriDNS.Impl.TcpFraming



namespace VeriDNS.Proof.TcpFraming

open VeriDNS.Impl.TcpFraming

@[simp] theorem lenPrefix_size (n : Nat) : (lenPrefix n).size = 2 := rfl

theorem frameTcp_size (payload : ByteArray) : (frameTcp payload).size = 2 + payload.size := by
  simp [frameTcp, ByteArray.size_append]

theorem frameTcp_getElem_zero (payload : ByteArray) (h : 0 < (frameTcp payload).size) :
    (frameTcp payload)[0] = (payload.size / 256).toUInt8 := by
  unfold frameTcp; rw [ByteArray.getElem_append_left (by rw [lenPrefix_size]; omega)]
  rfl

theorem frameTcp_getElem_one (payload : ByteArray) (h : 1 < (frameTcp payload).size) :
    (frameTcp payload)[1] = (payload.size % 256).toUInt8 := by
  unfold frameTcp; rw [ByteArray.getElem_append_left (by rw [lenPrefix_size]; omega)]
  rfl

theorem frameTcp_extract (payload : ByteArray) :
    (frameTcp payload).extract 2 (2 + payload.size) = payload := by
  apply ByteArray.ext
  simp only [frameTcp, ByteArray.data_extract, ByteArray.data_append, lenPrefix]
  rw [show (2 : Nat) = (#[(payload.size / 256).toUInt8, (payload.size % 256).toUInt8]).size from rfl]
  rw [Array.extract_append_right]
  simp

theorem lenByte_lo (n : Nat) : ((n % 256).toUInt8).toNat = n % 256 := by
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)]

theorem lenByte_hi (n : Nat) (h : n ≤ 65535) : ((n / 256).toUInt8).toNat = n / 256 := by
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)]

theorem unframeTcp_frameTcp (payload : ByteArray) (h : payload.size ≤ 65535) :
    unframeTcp (frameTcp payload) = some payload := by
  have hsz : (frameTcp payload).size = 2 + payload.size := frameTcp_size payload
  have h2 : 2 ≤ (frameTcp payload).size := by omega
  have hlen : ((frameTcp payload)[0]'(by omega)).toNat * 256
        + ((frameTcp payload)[1]'(by omega)).toNat = payload.size := by
    rw [frameTcp_getElem_zero payload (by omega), frameTcp_getElem_one payload (by omega),
      lenByte_hi payload.size h, lenByte_lo payload.size]
    omega
  unfold unframeTcp
  rw [dif_pos h2]
  simp only [hlen, frameTcp_extract payload, if_true]

end VeriDNS.Proof.TcpFraming
