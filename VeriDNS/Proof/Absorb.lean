import VeriDNS.Proof.IoResumeSound






namespace VeriDNS.Proof.Absorb

open VeriDNS.Spec
open VeriDNS.Impl.Cache
open VeriDNS.Impl.DomainName (nameEqCI)
open VeriDNS.Proof.NameTree (SameKey OneExpiryPerKey WfRR sameKey_symm)
open VeriDNS.Proof.Refinement (byteArray_beq_iff_eq)
open VeriDNS.Proof.NetworkSim (CacheWf)
open VeriDNS.Proof.Refinement (CacheNsCanon CacheCnameCanon CacheNsDistinct
  CacheNsDistinct_boundExpiryClasses)
open VeriDNS.Proof.DeliveredWire (CacheRecCanon CacheNegSoaCanon)

def recStep (c : DnsCache) (e : CacheEntry) : DnsCache :=
  { c with records := (c.records.filter fun e2 =>
      !(nameEqCI e2.rr.name e.rr.name && e2.rr.type == e.rr.type && e2.rr.class == e.rr.class
        && (e2.expiry != e.expiry || rdataEqCI e.rr.type e2.rr.rdata e.rr.rdata))).push e }

def negStep (c : DnsCache) (n : NegativeEntry) : DnsCache :=
  { c with negatives := (c.negatives.filter fun n2 =>
      !(nameEqCI n2.name n.name && n2.qclass == n.qclass
        && (n.rcode == Rcode.nameError || n2.qtype == n.qtype))).push n }

theorem absorb_eq (base new : DnsCache) :
    base.absorb new
      = (new.negatives.foldl negStep (new.records.foldl recStep base)).boundExpiryClasses := rfl

theorem recStep_negatives (c : DnsCache) (e : CacheEntry) :
    (recStep c e).negatives = c.negatives := rfl

theorem negStep_records (c : DnsCache) (n : NegativeEntry) :
    (negStep c n).records = c.records := rfl

theorem boundExpiryClasses_records (c : DnsCache) :
    c.boundExpiryClasses.records = evictClasses c.records c.records.size := rfl

theorem boundExpiryClasses_negatives (c : DnsCache) :
    c.boundExpiryClasses.negatives = c.negatives := rfl

theorem mem_recStep_inv {c : DnsCache} {e x : CacheEntry}
    (hx : x ∈ (recStep c e).records) : x ∈ c.records ∨ x = e := by
  unfold recStep at hx
  rcases Array.mem_push.mp hx with h | h
  · exact Or.inl (Array.mem_filter.mp h).1
  · exact Or.inr h

theorem mem_negStep_inv {c : DnsCache} {n m : NegativeEntry}
    (hm : m ∈ (negStep c n).negatives) : m ∈ c.negatives ∨ m = n := by
  unfold negStep at hm
  rcases Array.mem_push.mp hm with h | h
  · exact Or.inl (Array.mem_filter.mp h).1
  · exact Or.inr h

private theorem absorbRemoves_iff {e x : CacheEntry} :
    (nameEqCI x.rr.name e.rr.name && x.rr.type == e.rr.type && x.rr.class == e.rr.class
      && (x.expiry != e.expiry || rdataEqCI e.rr.type x.rr.rdata e.rr.rdata)) = true
    ↔ SameKey x.rr e.rr
      ∧ (x.expiry ≠ e.expiry ∨ rdataEqCI e.rr.type x.rr.rdata e.rr.rdata = true) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨hn, ht⟩, hc⟩, hd⟩ => ⟨⟨hn, ht, hc⟩, hd⟩,
    fun ⟨⟨hn, ht, hc⟩, hd⟩ => ⟨⟨⟨hn, ht⟩, hc⟩, hd⟩⟩

private theorem kept_samekey {arr : Array CacheEntry} {e x : CacheEntry}
    (hx : x ∈ arr.filter fun e2 =>
      !(nameEqCI e2.rr.name e.rr.name && e2.rr.type == e.rr.type && e2.rr.class == e.rr.class
        && (e2.expiry != e.expiry || rdataEqCI e.rr.type e2.rr.rdata e.rr.rdata)))
    (hk : SameKey x.rr e.rr) :
    x.expiry = e.expiry ∧ rdataEqCI e.rr.type x.rr.rdata e.rr.rdata ≠ true := by
  have hcond := (Array.mem_filter.mp hx).2
  rw [Bool.not_eq_true'] at hcond
  have hfalse : ¬ (SameKey x.rr e.rr
      ∧ (x.expiry ≠ e.expiry ∨ rdataEqCI e.rr.type x.rr.rdata e.rr.rdata = true)) := by
    intro h
    have htrue := absorbRemoves_iff.mpr h
    rw [hcond] at htrue
    exact absurd htrue (by decide)
  constructor
  · by_contra hne
    exact hfalse ⟨hk, Or.inl hne⟩
  · intro hrd
    exact hfalse ⟨hk, Or.inr hrd⟩

private theorem oneExpiry_recStep {c : DnsCache} (e : CacheEntry)
    (h : OneExpiryPerKey c) : OneExpiryPerKey (recStep c e) := by
  intro e₁ he₁ e₂ he₂ hk
  unfold recStep at he₁ he₂
  rcases Array.mem_push.mp he₁ with h₁ | h₁ <;> rcases Array.mem_push.mp he₂ with h₂ | h₂
  · exact h e₁ (Array.mem_filter.mp h₁).1 e₂ (Array.mem_filter.mp h₂).1 hk
  · rw [h₂] at hk ⊢
    exact (kept_samekey h₁ hk).1
  · rw [h₁] at hk ⊢
    exact ((kept_samekey h₂ (sameKey_symm hk)).1).symm
  · rw [h₁, h₂]

private theorem nsDistinct_recStep {c : DnsCache} (e : CacheEntry)
    (h : CacheNsDistinct c) : CacheNsDistinct (recStep c e) := by
  show ((recStep c e).records.toList).Pairwise _
  unfold recStep
  rw [Array.toList_push, List.pairwise_append]
  refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · rw [Array.toList_filter]
    exact h.filter _
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    rintro ⟨hta, hte, hname, hclass, hrdata⟩
    rw [hb] at hte hname hclass hrdata
    rw [Array.toList_filter, List.mem_filter] at ha
    obtain ⟨_, hap⟩ := ha
    rw [Bool.not_eq_true'] at hap
    have htrue : (nameEqCI a.rr.name e.rr.name && a.rr.type == e.rr.type
        && a.rr.class == e.rr.class
        && (a.expiry != e.expiry || rdataEqCI e.rr.type a.rr.rdata e.rr.rdata)) = true :=
      absorbRemoves_iff.mpr ⟨⟨hname, hta.trans hte.symm, hclass⟩,
        Or.inr (VeriDNS.Impl.Cache.rdataEqCI_of_eq _ hrdata)⟩
    rw [hap] at htrue
    exact absurd htrue (by decide)

private theorem recFold_facts (base : DnsCache) (arr : Array CacheEntry) :
    (∀ x ∈ (arr.foldl recStep base).records, x ∈ base.records ∨ x ∈ arr)
    ∧ (arr.foldl recStep base).negatives = base.negatives := by
  refine Array.foldl_induction
    (motive := fun _ (c : DnsCache) => (∀ x ∈ c.records, x ∈ base.records ∨ x ∈ arr)
      ∧ c.negatives = base.negatives)
    ⟨fun _ hx => Or.inl hx, rfl⟩ ?_
  intro i c hc
  refine ⟨fun x hx => ?_, (recStep_negatives c arr[i]).trans hc.2⟩
  rcases mem_recStep_inv hx with hin | heq
  · exact hc.1 x hin
  · exact Or.inr (heq ▸ arr.getElem_mem i.isLt)

private theorem negFold_facts (c0 : DnsCache) (arr : Array NegativeEntry) :
    (∀ m ∈ (arr.foldl negStep c0).negatives, m ∈ c0.negatives ∨ m ∈ arr)
    ∧ (arr.foldl negStep c0).records = c0.records := by
  refine Array.foldl_induction
    (motive := fun _ (c : DnsCache) => (∀ m ∈ c.negatives, m ∈ c0.negatives ∨ m ∈ arr)
      ∧ c.records = c0.records)
    ⟨fun _ hm => Or.inl hm, rfl⟩ ?_
  intro i c hc
  refine ⟨fun m hm => ?_, (negStep_records c arr[i]).trans hc.2⟩
  rcases mem_negStep_inv hm with hin | heq
  · exact hc.1 m hin
  · exact Or.inr (heq ▸ arr.getElem_mem i.isLt)

private theorem oneExpiry_recFold (base : DnsCache) (arr : Array CacheEntry)
    (h : OneExpiryPerKey base) : OneExpiryPerKey (arr.foldl recStep base) :=
  Array.foldl_induction (motive := fun _ c => OneExpiryPerKey c) h
    (fun _ _ hc => oneExpiry_recStep _ hc)

private theorem nsDistinct_recFold (base : DnsCache) (arr : Array CacheEntry)
    (h : CacheNsDistinct base) : CacheNsDistinct (arr.foldl recStep base) :=
  Array.foldl_induction (motive := fun _ c => CacheNsDistinct c) h
    (fun _ _ hc => nsDistinct_recStep _ hc)

theorem mem_absorb_records {base new : DnsCache} {x : CacheEntry}
    (hx : x ∈ (base.absorb new).records) : x ∈ base.records ∨ x ∈ new.records := by
  rw [absorb_eq, boundExpiryClasses_records] at hx
  have hx' := mem_of_mem_evictClasses hx
  rw [(negFold_facts _ _).2] at hx'
  exact (recFold_facts base new.records).1 x hx'

theorem mem_absorb_negatives {base new : DnsCache} {m : NegativeEntry}
    (hm : m ∈ (base.absorb new).negatives) : m ∈ base.negatives ∨ m ∈ new.negatives := by
  rw [absorb_eq, boundExpiryClasses_negatives] at hm
  rcases (negFold_facts _ _).1 m hm with h | h
  · rw [(recFold_facts base new.records).2] at h
    exact Or.inl h
  · exact Or.inr h

theorem CacheWf_absorb_merge {base new : DnsCache} {now : UInt32}
    (hb : CacheWf base now) (hn : CacheWf new now) : CacheWf (base.absorb new) now :=
  ⟨fun e he => (mem_absorb_records he).elim (hb.1 e) (hn.1 e),
   fun e he => (mem_absorb_records he).elim (hb.2.1 e) (hn.2.1 e),
   fun e he => (mem_absorb_records he).elim (hb.2.2 e) (hn.2.2 e)⟩

theorem CacheNsCanon_absorb_merge {base new : DnsCache}
    (hb : CacheNsCanon base) (hn : CacheNsCanon new) : CacheNsCanon (base.absorb new) := by
  intro e he ht
  rcases mem_absorb_records (Array.mem_def.mpr he) with h | h
  · exact hb e (Array.mem_def.mp h) ht
  · exact hn e (Array.mem_def.mp h) ht

theorem CacheCnameCanon_absorb_merge {base new : DnsCache}
    (hb : CacheCnameCanon base) (hn : CacheCnameCanon new) :
    CacheCnameCanon (base.absorb new) := by
  intro e he ht
  rcases mem_absorb_records (Array.mem_def.mpr he) with h | h
  · exact hb e (Array.mem_def.mp h) ht
  · exact hn e (Array.mem_def.mp h) ht

theorem wfrrAll_absorb_merge {base new : DnsCache}
    (hb : ∀ e ∈ base.records, WfRR e.rr) (hn : ∀ e ∈ new.records, WfRR e.rr) :
    ∀ e ∈ (base.absorb new).records, WfRR e.rr :=
  fun e he => (mem_absorb_records he).elim (hb e) (hn e)

theorem CacheNegWf_absorb_merge {base new : DnsCache} {qc : BitVec 16}
    (hb : CacheNegWf base qc) (hn : CacheNegWf new qc) : CacheNegWf (base.absorb new) qc :=
  fun e he => (mem_absorb_negatives he).elim (hb e) (hn e)

theorem cacheRecCanon_absorb_merge {base new : DnsCache}
    (hb : CacheRecCanon base) (hn : CacheRecCanon new) : CacheRecCanon (base.absorb new) := by
  intro e he
  rcases mem_absorb_records (Array.mem_def.mpr he) with h | h
  · exact hb e (Array.mem_def.mp h)
  · exact hn e (Array.mem_def.mp h)

theorem cacheNegSoaCanon_absorb_merge {base new : DnsCache}
    (hb : CacheNegSoaCanon base) (hn : CacheNegSoaCanon new) :
    CacheNegSoaCanon (base.absorb new) := by
  intro e he
  rcases mem_absorb_negatives (Array.mem_def.mpr he) with h | h
  · exact hb e (Array.mem_def.mp h)
  · exact hn e (Array.mem_def.mp h)

theorem oneExpiry_absorb_merge {base new : DnsCache}
    (h : OneExpiryPerKey base) : OneExpiryPerKey (base.absorb new) := by
  intro e₁ he₁ e₂ he₂ hk
  rw [absorb_eq, boundExpiryClasses_records] at he₁ he₂
  have h₁ := mem_of_mem_evictClasses he₁
  have h₂ := mem_of_mem_evictClasses he₂
  rw [(negFold_facts _ _).2] at h₁ h₂
  exact oneExpiry_recFold base new.records h e₁ h₁ e₂ h₂ hk

theorem nsDistinct_absorb_merge {base new : DnsCache}
    (h : CacheNsDistinct base) : CacheNsDistinct (base.absorb new) := by
  rw [absorb_eq]
  refine CacheNsDistinct_boundExpiryClasses _ ?_
  show ((new.negatives.foldl negStep (new.records.foldl recStep base)).records.toList).Pairwise _
  rw [(negFold_facts _ _).2]
  exact nsDistinct_recFold base new.records h

theorem absorb_size_le (base new : DnsCache) :
    (base.absorb new).records.size ≤ DnsCache.capacity := by
  rw [absorb_eq]
  exact VeriDNS.Proof.Cache.boundExpiryClasses_bounded _


theorem absorb_serve_invariants (base new : DnsCache) (now : UInt32) (qc : BitVec 16)
    (hWfB : CacheWf base now) (hNsB : CacheNsCanon base) (hCnB : CacheCnameCanon base)
    (hRrB : ∀ e ∈ base.records, WfRR e.rr) (hNegB : CacheNegWf base qc)
    (hNdB : CacheNsDistinct base) (hOEB : OneExpiryPerKey base)
    (hRcB : CacheRecCanon base) (hSoaB : CacheNegSoaCanon base)
    (hWfN : CacheWf new now) (hNsN : CacheNsCanon new) (hCnN : CacheCnameCanon new)
    (hRrN : ∀ e ∈ new.records, WfRR e.rr) (hNegN : CacheNegWf new qc)
    (hRcN : CacheRecCanon new) (hSoaN : CacheNegSoaCanon new) :
    CacheWf (base.absorb new) now
      ∧ CacheNsCanon (base.absorb new)
      ∧ CacheCnameCanon (base.absorb new)
      ∧ (∀ e ∈ (base.absorb new).records, WfRR e.rr)
      ∧ CacheNegWf (base.absorb new) qc
      ∧ CacheNsDistinct (base.absorb new)
      ∧ OneExpiryPerKey (base.absorb new)
      ∧ (base.absorb new).records.size ≤ DnsCache.capacity
      ∧ CacheRecCanon (base.absorb new)
      ∧ CacheNegSoaCanon (base.absorb new) :=
  ⟨CacheWf_absorb_merge hWfB hWfN, CacheNsCanon_absorb_merge hNsB hNsN,
   CacheCnameCanon_absorb_merge hCnB hCnN, wfrrAll_absorb_merge hRrB hRrN,
   CacheNegWf_absorb_merge hNegB hNegN, nsDistinct_absorb_merge hNdB,
   oneExpiry_absorb_merge hOEB, absorb_size_le base new,
   cacheRecCanon_absorb_merge hRcB hRcN, cacheNegSoaCanon_absorb_merge hSoaB hSoaN⟩

end VeriDNS.Proof.Absorb
