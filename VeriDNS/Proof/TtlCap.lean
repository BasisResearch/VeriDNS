import VeriDNS.Proof.MessageValid
import VeriDNS.Proof.ResourceRecord
import VeriDNS.Impl.Server

namespace VeriDNS.Proof.TtlCap

open VeriDNS.Impl VeriDNS.Spec VeriDNS.Impl.Cache

theorem parseRaw_encode (rr : VeriDNS.Spec.ResourceRecord) (labels : Array ByteArray)
    (hv : VeriDNS.Proof.DomainName.ValidLabels labels)
    (hle : (DomainName.labelsToWireFormat labels).size ≤ 255)
    (hqn : DomainName.labelsToWireFormat labels = rr.name)
    (hrl : VeriDNS.Spec.rdlength_prop_0 rr) :
    RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr)) = some rr := by
  show (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode
      (DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode rr)) with
      | .ok (rr, _) => some rr | .error _ => none) = some rr
  rw [VeriDNS.Proof.ResourceRecord.decode_encode rr labels hv hle hqn hrl]

theorem parseRaw_some_decode (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord)
    (h : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    ∃ p, DnsParser.run VeriDNS.Impl.ResourceRecord.decode b = .ok (rr, p) := by
  have h' : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
      | .ok (rr, _) => some rr | .error _ => none) = some rr := h
  split at h'
  · rename_i r p he; exact ⟨p, by rw [he]; injection h' with h'; rw [h']⟩
  · exact absurd h' (by simp)

theorem capTtlRR_le (b : ByteArray) (rr : VeriDNS.Spec.ResourceRecord)
    (h : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) (Server.capTtlRR b) = some rr) :
    rr.ttl.toNat ≤ 604800 := by
  unfold Server.capTtlRR at h
  cases hb : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hb] at h; dsimp only at h; rw [hb] at h; exact absurd h (by simp)
  | some rr0 =>
    rw [hb] at h; dsimp only at h
    obtain ⟨p, hd⟩ := parseRaw_some_decode b rr0 hb
    obtain ⟨labels, hv, hqn, hrl, hle255⟩ := VeriDNS.Proof.Message.run_resourceRecordDecode_valid hd
    split at h
    ·
      rw [parseRaw_encode { rr0 with ttl := 0 } labels hv hle255 hqn hrl] at h
      injection h with h; rw [← h]; dsimp only; decide
    · split at h
      ·
        rw [parseRaw_encode { rr0 with ttl := BitVec.ofNat 32 604800 } labels hv hle255 hqn hrl] at h
        injection h with h; rw [← h]; dsimp only; decide
      ·
        rename_i hle
        rw [hb] at h; injection h with h; rw [← h]; omega

theorem canonicalRR_capTtlRR (b : ByteArray)
    (hcanon : VeriDNS.Proof.Message.CanonicalRR b) :
    VeriDNS.Proof.Message.CanonicalRR (Server.capTtlRR b) := by
  obtain ⟨ls, t, c, ttl, rdata, hvls, hle_ls, hrd, rfl⟩ := hcanon
  have hsz := VeriDNS.Proof.Message.canonicalRdata_size_lt hrd
  have hrun := VeriDNS.Proof.Message.run_resourceRecordDecode_rrWire ls hvls hle_ls t c ttl rdata hsz
    ByteArray.empty ByteArray.empty
  have hae : ∀ a : ByteArray, a ++ ByteArray.empty = a := fun a => by
    ext1; simp [ByteArray.data_append]
  have hea : ∀ a : ByteArray, ByteArray.empty ++ a = a := fun a => by
    ext1; simp [ByteArray.data_append]
  rw [hae, hea] at hrun
  simp only [show ByteArray.empty.size = 0 from rfl] at hrun

  have hpr : RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Proof.Message.rrWire ls t c ttl rdata)
      = some { name := Impl.DomainName.labelsToWireFormat ls, type := t, «class» := c, ttl := ttl,
               rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata } := by
    show (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode
        (VeriDNS.Proof.Message.rrWire ls t c ttl rdata) with
        | .ok (rr, _) => some rr | .error _ => none) = _
    rw [hrun]
  unfold Server.capTtlRR
  rw [hpr]
  dsimp only

  have hreenc : ∀ ttl', DnsSerializer.runBytes (VeriDNS.Impl.ResourceRecord.encode
      { name := Impl.DomainName.labelsToWireFormat ls, type := t, «class» := c, ttl := ttl',
        rdlength := BitVec.ofNat 16 rdata.size, rdata := rdata })
      = VeriDNS.Proof.Message.rrWire ls t c ttl' rdata := by
    intro ttl'
    have := VeriDNS.Proof.Message.rrWire_encoder (Impl.DomainName.labelsToWireFormat ls) t c ttl'
      (BitVec.ofNat 16 rdata.size) rdata
    unfold VeriDNS.Impl.ResourceRecord.encode
    rw [this]
    rfl
  split
  ·
    rw [hreenc 0]
    exact ⟨ls, t, c, 0, rdata, hvls, hle_ls, hrd, rfl⟩
  · split
    ·
      rw [hreenc (BitVec.ofNat 32 604800)]
      exact ⟨ls, t, c, BitVec.ofNat 32 604800, rdata, hvls, hle_ls, hrd, rfl⟩
    ·
      exact ⟨ls, t, c, ttl, rdata, hvls, hle_ls, hrd, rfl⟩

theorem sanitizeTtlsCap_limit_ttls :
    VeriDNS.Spec.processingresponses_limit_ttls VeriDNS.Spec.ResourceRecord
      (RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord))
      (fun rr => rr.ttl.toNat) Server.sanitizeTtlsCap := by
  intro resp resp' hp bytes hmem rr hparse
  have hr : resp' = Server.capTtls (Edns.stripOpt resp) := by
    unfold Server.sanitizeTtlsCap at hp; injection hp with hp; exact hp.symm
  subst hr
  have hex : ∃ b, Server.capTtlRR b = bytes := by
    rcases hmem with (hm | hm) | hm <;>
    · simp only [Server.capTtls, Array.mem_map] at hm
      obtain ⟨b, _, hb⟩ := hm; exact ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  rw [← hb] at hparse
  exact capTtlRR_le b rr hparse

end VeriDNS.Proof.TtlCap
