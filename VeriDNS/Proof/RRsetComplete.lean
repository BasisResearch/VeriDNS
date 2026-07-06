import VeriDNS.Proof.NameTreeComplete

/-!
# RRset completeness under TTL normalization (RFC 2181 §5.2)

The soundness theorem (`ioResumeLoop_sound`) proves the impl never serves *more* than the model
(`CacheRefines` is impl-served ⊆ model-served). It structurally cannot express the *completeness*
direction — that every legal RRset member survives caching. `DnsCache.store`, storing members one at
a time, evicts a same-key member whose expiry differs (`Removes`), so a non-uniform-TTL RRset (RFC
2181 §5.2) would collapse to a single record.

`normalizeRRsetTtls` rewrites each member's TTL to the per-key minimum, so every same-key member
shares one expiry and `store` keeps them all. This file proves that guarantee:
`cacheRRsNorm_complete` — every distinct-rdata member of a normalized RRset survives the cache write.
-/

namespace VeriDNS.Proof.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.Cache
open VeriDNS.Impl.DomainName (nameEqCI)

/-! ### The per-key minimum-TTL fold, `rrSameKeyB`/`SameKey` correspondence, `groupMinTtl_congr`,
    and `normRaws_uniform` are defined upstream in `Proof/NameTreeComplete.lean` (the cache-invariant
    proofs there consume them). -/

/-! ### The survivor: a stored member of a uniform-TTL section survives the whole write -/

open VeriDNS.Impl.Resolver (cacheRRs)

/-- **A member of a uniform-TTL section survives the one-at-a-time `storeStep` fold.** If the section
    `L` has uniform per-key TTLs, no starting-cache entry shares the target's key, and some raw parses
    to a member `r` with the target's key/rdata and nonzero TTL, then the final cache still serves a
    record with that key and rdata. Establishes `Sat` at `r`'s store (no `Blocked`: same-key
    incumbents are excluded by `hfree`, and same-cred RRset mates never block) and preserves it across
    the rest via `sat_foldl` (uniform TTL ⟹ every same-key mate shares the expiry). -/
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
  -- No same-key incumbent blocks `r` when it is stored.
  have hnbL1 : ¬ Blocked (L₁.foldl (storeStep cred now) c) r cred now := by
    rintro ⟨e, he, hkey, _, hbet⟩
    rcases mem_foldl_store L₁ c huL₁ he with hold | ⟨_, _, _, _, heqE, _, _⟩
    · exact hfree e hold (sameKey_trans hkey hkr)
    · rw [heqE] at hbet; exact Nat.lt_irrefl _ hbet
  have hdata : sameData r trr = true := sameData_iff.mpr ⟨hkr.1, hkr.2.1, hkr.2.2, hrd⟩
  -- `Sat` holds right after `r` is stored.
  have hsat : Sat trr (now + r.ttl.toNat.toUInt32) cred.toCode
      (storeStep cred now (L₁.foldl (storeStep cred now) c) b) := by
    rw [storeStep_some hp]
    rcases storeChecked_cases (L₁.foldl (storeStep cred now) c) r cred now
      with ⟨h0, _⟩ | ⟨_, hbl, _⟩ | ⟨_, _, heq⟩
    · exact absurd h0 httl
    · exact absurd hbl hnbL1
    · rw [heq]
      exact ⟨⟨r, now + r.ttl.toNat.toUInt32, false, cred⟩,
        mem_store_iff.mpr (Or.inr rfl), hdata, rfl, Nat.le_refl _⟩
  -- The rest of the section preserves `Sat` (every same-key mate shares the expiry).
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

/-! ### `normRaws` produces a uniform-TTL section; final completeness

    (`mem_normRaws` / `parseRaw_normMember` / `parseRaw_mem_normRaws` / `normRaws_forall_transfer` are
    defined upstream in `Proof/NameTree.lean` so the cache-invariant preservation lemmas can use them.) -/


/-- **RRset completeness (RFC 2181 §5.2, the `#4` guarantee).** For a section written through the
    TTL-normalizing `cacheRRs (normRaws …)` on a cache with no more-credible incumbent at the key,
    every distinct-rdata member survives: the final cache serves a record with the member's key and
    rdata. This is the completeness direction the soundness `Subperm` (impl-served ⊆ model-served)
    structurally cannot express — delivered as a standalone theorem. -/
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
