import VeriDNS.Proof.NameTreeComplete




namespace VeriDNS.Proof.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.Cache
open VeriDNS.Impl.DomainName (nameEqCI)



open VeriDNS.Impl.Resolver (cacheRRs)

theorem storeStep_foldl_survivor (cred : Trustworthiness) (now : UInt32)
    (trr : ResourceRecord) (L : List ByteArray) (c : DnsCache)
    (hu : UniformTtls L)
    (hfree : ∀ e ∈ c.records, ¬ SameKey e.rr trr)
    (b : ByteArray) (hb : b ∈ L) (r : ResourceRecord)
    (hp : RRParse.parseRaw (RR := ResourceRecord) b = some r)
    (hkr : SameKey r trr) (hrd : r.rdata = trr.rdata) (httl : r.ttl ≠ 0) :
    ∃ e ∈ (L.foldl (storeStep cred now) c).records,
      SameKey e.rr trr ∧ e.rr.rdata = trr.rdata := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hb
  have hmemL₁ : ∀ {b₁ : ByteArray}, b₁ ∈ L₁ → b₁ ∈ L := by
    intro b₁ hb₁; rw [hsplit]; exact List.mem_append_left _ hb₁
  have hmemL₂ : ∀ {b₁ : ByteArray}, b₁ ∈ L₂ → b₁ ∈ L := by
    intro b₁ hb₁; rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hb₁)
  have huL₁ : UniformTtls L₁ := fun b₁ hb₁ b₂ hb₂ => hu b₁ (hmemL₁ hb₁) b₂ (hmemL₁ hb₂)
  have huL₂ : UniformTtls L₂ := fun b₁ hb₁ b₂ hb₂ => hu b₁ (hmemL₂ hb₁) b₂ (hmemL₂ hb₂)
  have hfold_eq : L.foldl (storeStep cred now) c =
      L₂.foldl (storeStep cred now)
        (storeStep cred now (L₁.foldl (storeStep cred now) c) b) := by
    rw [hsplit, List.foldl_append, List.foldl_cons]
  have hnbL1 : ¬ Blocked (L₁.foldl (storeStep cred now) c) r cred now := by
    rintro ⟨e, he, hkey, _, hbet⟩
    rcases mem_foldl_store L₁ c huL₁ he with hold | ⟨_, _, _, _, heqE, _, _⟩
    · exact hfree e hold (sameKey_trans hkey hkr)
    · rw [heqE] at hbet; exact Nat.lt_irrefl _ hbet
  have hdata : sameData r trr = true := sameData_iff.mpr ⟨hkr.1, hkr.2.1, hkr.2.2, hrd⟩
  have hsat : Sat trr (now + r.ttl.toNat.toUInt32) cred.toCode
      (storeStep cred now (L₁.foldl (storeStep cred now) c) b) := by
    rw [storeStep_some hp]
    rcases storeChecked_cases (L₁.foldl (storeStep cred now) c) r cred now
      with ⟨h0, _⟩ | ⟨_, hbl, _⟩ | ⟨_, _, heq⟩
    · exact absurd h0 httl
    · exact absurd hbl hnbL1
    · rw [heq]
      exact ⟨⟨r, now + r.ttl.toNat.toUInt32, false, cred, now⟩,
        mem_store_iff.mpr (Or.inr rfl), hdata, rfl, Nat.le_refl _⟩
  have hkeyh : ∀ b₁ ∈ L₂, ∀ r₁,
      RRParse.parseRaw (RR := ResourceRecord) b₁ = some r₁ → SameKey r₁ trr →
      r₁.ttl = 0 ∨
        Blocked (storeStep cred now (L₁.foldl (storeStep cred now) c) b) r₁ cred now ∨
        now + r₁.ttl.toNat.toUInt32 = now + r.ttl.toNat.toUInt32 := by
    intro b₁ hb₁ r₁ hp₁ hk₁
    refine Or.inr (Or.inr ?_)
    have hte : r₁.ttl = r.ttl :=
      hu b₁ (hmemL₂ hb₁) b hb r₁ r hp₁ hp (sameKey_trans hk₁ (sameKey_symm hkr))
    rw [hte]
  obtain ⟨e', he', hd', _, _⟩ :=
    sat_foldl (cred := cred) (now := now) L₂ _ huL₂ hkeyh hsat
  obtain ⟨hn', ht', hc', hrd'⟩ := sameData_iff.mp hd'
  exact ⟨e', by rw [hfold_eq]; exact he', ⟨hn', ht', hc'⟩, hrd'⟩




theorem cacheRRsNorm_complete (cache : DnsCache) (raws : Array ByteArray)
    (cred : Trustworthiness) (now : UInt32) (rr : ResourceRecord)
    (hin : rr ∈ rrsOf raws)
    (hnz : groupMinTtl (rrsOf raws) rr ≠ 0)
    (hfree : ∀ e ∈ cache.records, ¬ SameKey e.rr rr) :
    ∃ e ∈ (cacheRRs (C := DnsCache) (RR := ResourceRecord) cache
        (normRaws raws) cred now).records,
      SameKey e.rr rr ∧ e.rr.rdata = rr.rdata := by
  rw [cacheRRs_eq]
  refine storeStep_foldl_survivor cred now rr (normRaws raws).toList cache
    (normRaws_uniform raws) hfree
    (RRParse.rrBytes (RR := ResourceRecord) { rr with ttl := groupMinTtl (rrsOf raws) rr })
    (mem_normRaws_of hin) _ (parseRaw_normMember hin)
    ⟨nameEqCI_refl rr.name, rfl, rfl⟩ rfl hnz

end VeriDNS.Proof.NameTree
