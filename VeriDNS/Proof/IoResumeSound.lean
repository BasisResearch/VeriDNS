import VeriDNS.Proof.NetworkSim
import VeriDNS.Proof.AnswerTerminal
import VeriDNS.Proof.DeliveredWire
import VeriDNS.Proof.TtlCap
import VeriDNS.Proof.GlueConnector
import VeriDNS.Proof.QnameMin
import VeriDNS.Proof.AnswerScrubAlpha
open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache VeriDNS.Spec
set_option maxHeartbeats 2000000


theorem groupMinTtl_le_seed (rrs : List ResourceRecord) (r : ResourceRecord) :
    (Cache.groupMinTtl rrs r).toNat ≤ r.ttl.toNat :=
  (VeriDNS.Proof.NameTree.foldl_minTtl_props rrs (fun e => Cache.rrSameKeyB e r) r.ttl).1

theorem normRaws_hval {raws : Array ByteArray}
    (hval : ∀ b ∈ raws.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → (αRR rr).isSome = true) :
    ∀ b ∈ (Cache.normRaws raws).toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → (αRR rr).isSome = true := by
  intro b hb rr hp
  obtain ⟨r, hr, rfl⟩ := VeriDNS.Proof.NameTree.parseRaw_mem_normRaws hb hp
  obtain ⟨b', hb', hpb'⟩ := List.mem_filterMap.mp hr
  have hvr := hval b' hb' r hpb'
  rw [αRR_set_ttl]; simpa using hvr

theorem normRaws_hno {raws : Array ByteArray} {now : UInt32}
    (hno : ∀ b ∈ raws.toList, ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr →
      (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    ∀ b ∈ (Cache.normRaws raws).toList, ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr →
      (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat := by
  intro b hb rr hp
  obtain ⟨r, hr, rfl⟩ := VeriDNS.Proof.NameTree.parseRaw_mem_normRaws hb hp
  obtain ⟨b', hb', hpb'⟩ := List.mem_filterMap.mp hr
  have hnr := hno b' hb' r hpb'
  have hle := groupMinTtl_le_seed (Cache.rrsOf raws) r
  have hsum : now.toNat + r.ttl.toNat < 2 ^ 32 := hnr ▸ UInt32.toNat_lt _
  show (now + (Cache.groupMinTtl (Cache.rrsOf raws) r).toNat.toUInt32).toNat
      = now.toNat + (Cache.groupMinTtl (Cache.rrsOf raws) r).toNat
  have hlt : (Cache.groupMinTtl (Cache.rrsOf raws) r).toNat < UInt32.size := by
    show _ < 4294967296; omega
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hlt]
  exact Nat.mod_eq_of_lt (by omega)

theorem rrsOf_RRCanonMappable {raws : Array ByteArray}
    (hval : ∀ b ∈ raws.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → (αRR rr).isSome = true) :
    ∀ e ∈ Cache.rrsOf raws, RRCanonMappable e := by
  intro e he
  obtain ⟨b, hb, hpb⟩ := List.mem_filterMap.mp he
  have hpb' : RRParse.parseRaw (RR := ResourceRecord) b = some e := hpb
  obtain ⟨me, hme⟩ := Option.isSome_iff_exists.mp (hval b hb e hpb')
  obtain ⟨na, hαN, hcanN, hsz⟩ := parseRaw_name_canonical hpb'
  have hown : αName e.name = some me.owner := (αRR_fields e me hme).1
  have hna : na = me.owner := Option.some.inj (hαN.symm.trans hown)
  exact ⟨me, hme, by rw [← hna]; exact hcanN, by rw [← hna]; exact hsz⟩

theorem CacheWf_absorb (cache : DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray) (now : UInt32)
    (h : CacheWf cache now)
    (hvalA : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr → (αRR rr).isSome = true)
    (hnoA : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hvalD : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr → (αRR rr).isSome = true)
    (hnoD : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat) :
    CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
        (Resolver.credAuthority (resp.header.aa == 1)) now)
      resp (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
      Resolver.credAdditional now) now := by
  apply CacheWf_cacheUnlessTruncated _ _ _ _ _ ?_ ?_ ?_
  ·
    apply CacheWf_cacheUnlessTruncated _ _ _ _ _ h ?_ ?_
    ·
      unfold Resolver.credAuthority
      by_cases ha : (resp.header.aa == 1) = true
      · rw [if_pos ha]; exact Or.inr (Or.inl rfl)
      · rw [if_neg ha]; exact Or.inr (Or.inr (Or.inr rfl))
    · intro raw hraw rr hp
      exact parseRaw_entry_canonical _ now hp (normRaws_hval hvalA raw hraw rr hp) (normRaws_hno hnoA raw hraw rr hp)
  ·
    exact Or.inr (Or.inr (Or.inr rfl))
  · intro raw hraw rr hp
    exact parseRaw_entry_canonical _ now hp (normRaws_hval hvalD raw hraw rr hp) (normRaws_hno hnoD raw hraw rr hp)

theorem CacheNsCanon_absorb (cache : DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray) (now : UInt32)
    (h : CacheNsCanon cache)
    (hcanonA : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority).toList,
        VeriDNS.Proof.Message.CanonicalRR raw)
    (hcanonD : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional).toList,
        VeriDNS.Proof.Message.CanonicalRR raw) :
    CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
        (Resolver.credAuthority (resp.header.aa == 1)) now)
      resp (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
      Resolver.credAdditional now) := by
  apply CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ ?_ ?_
  · apply CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ h ?_
    intro raw hraw rr hp htype
    exact canonicalRR_nsRdata_canonical (hcanonA raw hraw) hp htype
  · intro raw hraw rr hp htype
    exact canonicalRR_nsRdata_canonical (hcanonD raw hraw) hp htype

theorem CacheCnameCanon_absorb (cache : DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray) (now : UInt32)
    (h : CacheCnameCanon cache)
    (hcanonA : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority).toList,
        VeriDNS.Proof.Message.CanonicalRR raw)
    (hcanonD : ∀ raw ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional).toList,
        VeriDNS.Proof.Message.CanonicalRR raw) :
    CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
        (Resolver.credAuthority (resp.header.aa == 1)) now)
      resp (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
      Resolver.credAdditional now) := by
  apply CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ ?_ ?_
  · apply CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ h ?_
    intro raw hraw rr hp htype
    exact canonicalRR_cnameRdata_canonical (hcanonA raw hraw) hp htype
  · intro raw hraw rr hp htype
    exact canonicalRR_cnameRdata_canonical (hcanonD raw hraw) hp htype

theorem OneExpiryPerKey_absorb (cache : DnsCache) (resp : VeriDNS.Spec.Format) (cut : ByteArray) (now : UInt32)
    (h : VeriDNS.Proof.NameTree.OneExpiryPerKey cache) :
    VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) cache resp
        (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.authority)
        (Resolver.credAuthority (resp.header.aa == 1)) now)
      resp (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) cut resp.additional)
      Resolver.credAdditional now) :=
  VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated
    (VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated h _ _ _ _) _ _ _ _

theorem αCache_boundExpiryClasses_eq_of_CacheWf (c : DnsCache) (now : UInt32) (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c) :
    ∃ qf : VeriDNS.Spec.Net.CacheRR → Bool,
      αCache c.boundExpiryClasses
        = { pos := (αCache c).pos.filter qf, neg := (αCache c).neg }
      ∧ (∀ ce₁ ∈ (αCache c).pos, ∀ ce₂ ∈ (αCache c).pos,
          ce₁.sameKey ce₂.rr = true → qf ce₁ = qf ce₂) := by
  obtain ⟨qf, heq, hexp⟩ := αCache_boundExpiryClasses_eq c (fun e he => (hwf.1 e (by simpa using he)).2.1)
  have hmoe := ModelOneExpiry_αCache c now hwf hoe
  exact ⟨qf, heq, fun ce₁ h₁ ce₂ h₂ hk => hexp ce₁ ce₂ (hmoe ce₁ h₁ ce₂ h₂ hk)⟩

theorem αCache_boundStateCache_refines (c : DnsCache) (now : UInt32)
    (hwf : CacheWf c now) (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c) :
    CacheRefines (αCache c.boundExpiryClasses) (αCache c) := by
  obtain ⟨qf, heq, hkc⟩ := αCache_boundExpiryClasses_eq_of_CacheWf c now hwf hoe
  have heq' : αCache c.boundExpiryClasses = (αCache c).filterPos qf := heq
  refine ⟨fun nowT q => ?_, fun nowT q => ?_, fun nowT q => ?_⟩
  · rw [heq', filterPos_topServed qf nowT q hkc]; exact List.filter_sublist.subperm
  · rw [heq']; exact VeriDNS.Spec.Net.Cache.filterPos_negHit _ _ _ _
  · rw [heq']; exact VeriDNS.Spec.Net.Cache.filterPos_negHitNx _ _ _ _

theorem cacheRefines_boundStateCache_absorb (c : DnsCache) (cabs : VeriDNS.Spec.Net.Cache) (now : UInt32)
    (hwf : CacheWf c now) (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hmatch : MatchMaxEquiv (αCache c) cabs) :
    VeriDNS.Spec.Net.CacheRefines (αCache c.boundExpiryClasses) cabs :=
  (αCache_boundStateCache_refines c now hwf hoe).trans (MatchMaxEquiv.cacheRefines hmatch)

theorem αCache_boundLru_refines (c : DnsCache) (ks : Array VeriDNS.Impl.Cache.RRKey)
    (tnow : UInt32)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    CacheRefines (αCache (c.boundLru ks tnow)) (αCache c) := by
  obtain ⟨qf, heq, hkc⟩ := VeriDNS.Proof.Refinement.αCache_boundLru_eq c ks tnow hwfrr
  have heq' : αCache (c.boundLru ks tnow) = (αCache c).filterPos qf := heq
  refine ⟨fun nowT q => ?_, fun nowT q => ?_, fun nowT q => ?_⟩
  · rw [heq', filterPos_topServed qf nowT q (fun ce₁ _ ce₂ _ hk => hkc ce₁ ce₂ hk)]
    exact List.filter_sublist.subperm
  · rw [heq']; exact VeriDNS.Spec.Net.Cache.filterPos_negHit _ _ _ _
  · rw [heq']; exact VeriDNS.Spec.Net.Cache.filterPos_negHitNx _ _ _ _

theorem cacheRefines_boundLru_absorb (c : DnsCache) (cabs : VeriDNS.Spec.Net.Cache)
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hmatch : MatchMaxEquiv (αCache c) cabs) :
    VeriDNS.Spec.Net.CacheRefines (αCache (c.boundLru ks tnow)) cabs :=
  (αCache_boundLru_refines c ks tnow hwfrr).trans (MatchMaxEquiv.cacheRefines hmatch)

theorem WorldModels_oracle (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat)
    (now : Net.Time) {w w' : World} (hor : w'.oracle = w.oracle)
    (h : WorldModels net ns ra ednsBuf now w) : WorldModels net ns ra ednsBuf now w' := by
  intro q id cid ab d bytes resp0 resp₀ resp qm hO ha hd hs hacc hαq
  exact h q id cid ab d bytes resp0 resp₀ resp qm (by rw [← hor]; exact hO) ha hd hs hacc hαq

theorem acceptResponse_some_eq {sent r r' : VeriDNS.Spec.Format}
    (h : Server.acceptResponse sent r = some r') : r' = r := by
  unfold Server.acceptResponse at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

theorem bailiwickRaws_toList_sub {bw : ByteArray} {sect : Array ByteArray} {b : ByteArray}
    (h : b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) bw sect).toList) :
    b ∈ sect.toList := by
  unfold Resolver.bailiwickRaws at h
  rw [Array.toList_filter] at h
  exact (List.mem_filter.mp h).1

theorem ownerRaws_toList_sub {sname : ByteArray} {sect : Array ByteArray} {b : ByteArray}
    (h : b ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) sname sect).toList) :
    b ∈ sect.toList := by
  unfold Resolver.ownerRaws at h
  rw [Array.toList_filter] at h
  exact (List.mem_filter.mp h).1

theorem cnameRaws_toList_sub {sname : ByteArray} {sect : Array ByteArray} {b : ByteArray}
    (h : b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) sname sect).toList) :
    b ∈ sect.toList := by
  unfold Resolver.cnameRaws at h
  rw [Array.toList_filter] at h
  exact (List.mem_filter.mp h).1


theorem uint32_add_ttl_toNat (now : UInt32) (t : Nat) (hb : t ≤ 604800)
    (hc : now.toNat + 604800 < 2 ^ 32) :
    (now + t.toUInt32).toNat = now.toNat + t := by
  have hlt : t < UInt32.size := by
    show t < 4294967296
    omega
  have ht32 : t.toUInt32.toNat = t := UInt32.toNat_ofNat_of_lt' hlt
  rw [UInt32.toNat_add, ht32]
  exact Nat.mod_eq_of_lt (by omega)

def αSecF (b : ByteArray) : Option VeriDNS.Spec.Net.RR :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | some rr => αRR rr
  | none => none

theorem αSecF_none {b : ByteArray}
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = none) :
    αSecF b = none := by
  unfold αSecF
  rw [hp]

theorem αSecF_some {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    αSecF b = αRR rr := by
  unfold αSecF
  rw [hp]

theorem αSection_eq_filterMap (rrs : Array ByteArray) :
    αSection rrs = rrs.toList.filterMap αSecF := rfl

def implNsCutF (bytes : ByteArray) : Option ByteArray :=
  match VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) bytes with
  | some rr => if VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)
      then some (VeriDNS.Spec.RRParse.rrName rr) else none
  | none => none

theorem implNsCutF_none {b : ByteArray}
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = none) :
    implNsCutF b = none := by
  unfold implNsCutF
  rw [hp]

theorem implNsCutF_some {b : ByteArray} {rr : VeriDNS.Spec.ResourceRecord}
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr) :
    implNsCutF b = if VeriDNS.Spec.RRParse.rrType rr == (2 : BitVec 16)
      then some (VeriDNS.Spec.RRParse.rrName rr) else none := by
  unfold implNsCutF
  rw [hp]

theorem list_findSome?_congr {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.findSome?_cons, List.findSome?_cons, h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem referralCutRaw_eq_findSome (authority : Array ByteArray) :
    Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) authority
      = (authority.toList.findSome? implNsCutF).getD ByteArray.empty := by
  unfold Resolver.referralCutRaw
  split
  · rename_i owner heq
    rw [← Array.findSome?_toList] at heq
    rw [list_findSome?_congr (g := implNsCutF) authority.toList ?hpt] at heq
    case hpt =>
      intro b _
      unfold implNsCutF
      cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
    rw [heq]
    rfl
  · rename_i heq
    rw [← Array.findSome?_toList] at heq
    rw [list_findSome?_congr (g := implNsCutF) authority.toList ?hpt2] at heq
    case hpt2 =>
      intro b _
      unfold implNsCutF
      cases VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b <;> rfl
    rw [heq]
    rfl

theorem findSome?_ns_align : ∀ (l : List ByteArray),
    (∀ b ∈ l, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        αRR rr ≠ none) →
    ((l.filterMap αSecF).find? (fun r => r.rdata.rtype == RRType.ns)).map (·.owner)
      = (l.findSome? implNsCutF).bind αName := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b t ih =>
    intro hwf
    have hwft : ∀ b ∈ t, ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        αRR rr ≠ none := fun b hb => hwf b (List.mem_cons_of_mem _ hb)
    cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none =>
      have hSb : αSecF b = none := αSecF_none hp
      have hFb : implNsCutF b = none := implNsCutF_none hp
      rw [List.filterMap_cons, hSb, List.findSome?_cons, hFb]
      exact ih hwft
    | some rr =>
      have hα := hwf b (List.mem_cons_self ..) rr hp
      cases hαr : αRR rr with
      | none => exact absurd hαr hα
      | some r =>
        have hrt := αRR_rtype rr r hαr
        have hty : VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr = rr.type := rfl
        have hSb : αSecF b = some r := by rw [αSecF_some hp, hαr]
        rw [List.filterMap_cons_some hSb]
        by_cases ht : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == (2 : BitVec 16)) = true
        · have h2 : rr.type = (2 : BitVec 16) := by
            rw [← hty]
            exact eq_of_beq ht
          rw [h2] at hrt
          have hns2 : some RRType.ns = some r.rdata.rtype := by
            rw [← hrt]
            decide
          injection hns2 with hns3
          have hpr : ((fun x : VeriDNS.Spec.Net.RR => x.rdata.rtype == RRType.ns) r) = true := by
            show (r.rdata.rtype == RRType.ns) = true
            rw [← hns3]
            exact rrtype_beq_self _
          have hFb : implNsCutF b = some (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr) := by
            rw [implNsCutF_some hp, ht]
            rfl
          rw [List.find?_cons_of_pos (p := fun x : VeriDNS.Spec.Net.RR => x.rdata.rtype == RRType.ns) hpr, List.findSome?_cons, hFb]
          simp only [Option.map_some, Option.bind_some]
          exact ((αRR_fields rr r hαr).1).symm
        · have hpr : ¬(((fun x : VeriDNS.Spec.Net.RR => x.rdata.rtype == RRType.ns) r) = true) := by
            show ¬((r.rdata.rtype == RRType.ns) = true)
            intro hcon
            apply ht
            have hns3 : r.rdata.rtype = RRType.ns :=
              eq_of_αType_beq hrt (by decide : αType (2 : BitVec 16) = some RRType.ns) hcon
            rw [hns3] at hrt
            have h2 : rr.type = BitVec.ofNat 16 RRType.ns.toCode :=
              αType_injective hrt (αType_toCode RRType.ns rfl)
            show (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == (2 : BitVec 16)) = true
            show (rr.type == (2 : BitVec 16)) = true
            rw [h2]
            decide
          have hFb : implNsCutF b = none := by
            rw [implNsCutF_some hp]
            have htf : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == (2 : BitVec 16)) = false := by
              simpa using ht
            rw [htf]
            rfl
          rw [List.find?_cons_of_neg (p := fun x : VeriDNS.Spec.Net.RR => x.rdata.rtype == RRType.ns) hpr, List.findSome?_cons, hFb]
          exact ih hwft

theorem referralCutRaw_αName (authority : Array ByteArray)
    (hwf : ∀ b ∈ authority.toList, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
    (hns : Resolver.hasRRTypeIn (RR := VeriDNS.Spec.ResourceRecord) authority 2 = true) :
    αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) authority)
      = some (((αSection authority).find?
          (fun r => r.rdata.rtype == RRType.ns)).elim [] (·.owner)) := by
  have hwf' : ∀ b ∈ authority.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
    intro b hb rr hpr
    obtain ⟨rr', hpr', hα'⟩ := hwf b hb
    rw [hpr'] at hpr
    injection hpr with h
    subst h
    exact hα'
  have halign := findSome?_ns_align authority.toList hwf'
  rw [αSection_eq_filterMap]

  have hfsome : ((authority.toList.filterMap αSecF).find?
      (fun r => r.rdata.rtype == RRType.ns)).isSome = true := by
    unfold Resolver.hasRRTypeIn at hns
    rw [Array.any_eq_true] at hns
    obtain ⟨i, hi, hp⟩ := hns
    have hmem : authority[i] ∈ authority.toList := Array.mem_def.mp (Array.getElem_mem hi)
    cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) authority[i] with
    | none => rw [hpr] at hp; exact absurd hp (by simp)
    | some rr =>
      rw [hpr] at hp
      have hα := hwf' authority[i] hmem rr hpr
      cases hαr : αRR rr with
      | none => exact absurd hαr hα
      | some r =>
        have hrt := αRR_rtype rr r hαr
        have hty : VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr = rr.type := rfl
        have h2 : rr.type = (2 : BitVec 16) := by
          rw [← hty]
          exact eq_of_beq (by simpa using hp)
        rw [h2] at hrt
        have hns2 : some RRType.ns = some r.rdata.rtype := by
          rw [← hrt]
          decide
        injection hns2 with hns3
        rw [List.find?_isSome]
        refine ⟨r, ?_, by rw [← hns3]; exact rrtype_beq_self _⟩
        rw [List.mem_filterMap]
        exact ⟨authority[i], hmem, αSecF_some hpr ▸ hαr⟩
  obtain ⟨rfound, hfound⟩ := Option.isSome_iff_exists.mp hfsome
  rw [hfound] at halign ⊢
  simp only [Option.map_some] at halign
  cases hfs : (authority.toList.findSome? implNsCutF) with
  | none =>
    rw [hfs] at halign
    exact absurd halign (by simp)
  | some nm =>
    rw [hfs] at halign
    simp only [Option.bind_some] at halign
    rw [referralCutRaw_eq_findSome, hfs]
    simp only [Option.getD_some, Option.elim]
    exact halign.symm

def CnameChainModels
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q : Query) (nseen : List Name) : Prop :=
  ∀ nm ∈ q.qname :: nseen,
    ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).toList,
      αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
        ∧ (∀ x ∈ nm, x.size ≤ 63)

theorem CnameChainModels_congr
    {s s' : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    (hlq : s'.lastQuery = s.lastQuery) (hsn : s'.resources.sname = s.resources.sname)
    (hch : s'.cnameChain = s.cnameChain)
    {q : Query} {nseen : List Name} (h : CnameChainModels s q nseen) :
    CnameChainModels s' q nseen := by
  unfold CnameChainModels at h ⊢
  rw [hlq, hsn, hch]
  exact h

theorem visited_target_fresh (names : List Name) (visited : Array ByteArray)
    (targetBytes : ByteArray) (target : Name)
    (hmodels : ∀ nm ∈ names, ∃ b ∈ visited.toList,
        αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
          ∧ (∀ x ∈ nm, x.size ≤ 63))
    (htB : targetBytes = VeriDNS.Impl.DomainName.labelsToWireFormatGo target)
    (htV : ∀ x ∈ target, x.size ≤ 63)
    (hnrev : (visited.any (fun v => VeriDNS.Impl.DomainName.nameEqCI v targetBytes)) = false) :
    target ∉ names := by
  intro hmem
  obtain ⟨b, hbmem, _hα, hbc, hbv⟩ := hmodels target hmem
  have hci : VeriDNS.Impl.DomainName.nameEqCI b targetBytes = true :=
    nameEqCI_of_αName_canonical (nameEq_refl target) hbc htB hbv htV
  simp only [Array.any_eq_false'] at hnrev
  exact absurd hci (by simpa using hnrev b (Array.mem_def.mpr hbmem))

theorem cname_target_fresh
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (q : Query) (nseen : List Name) (targetBytes : ByteArray) (target : Name)
    (hCCM : CnameChainModels state q nseen)
    (htB : targetBytes = VeriDNS.Impl.DomainName.labelsToWireFormatGo target)
    (htV : ∀ x ∈ target, x.size ≤ 63)
    (hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v targetBytes)) = false) :
    target ∉ q.qname :: nseen := by
  exact visited_target_fresh (q.qname :: nseen) _ targetBytes target hCCM htB htV hnrev

theorem covers_cname_false_of_chase
    (resp : VeriDNS.Spec.Format) (target : ByteArray) (qu : VeriDNS.Spec.Question) (q : Query)
    (hchase : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (hqu : resp.question[0]? = some qu)
    (hqm : αQType qu.qtype = some q.qtype) (hqstar : q.qtype ≠ QType.star) :
    q.qtype.covers RRType.cname = false := by

  have hchase' := hchase
  unfold Resolver.cnameToChase at hchase'
  split at hchase'
  · exact absurd hchase' (by simp)
  · rename_i hansF
    rw [Bool.not_eq_true] at hansF

    simp only [hqu] at hchase'
    obtain ⟨b, hbmem, hbsome⟩ := Array.exists_of_findSome?_eq_some hchase'
    have hty5 : ∃ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr == (5 : BitVec 16)) = true := by
      cases hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
      | none => rw [hpr] at hbsome; exact absurd hbsome (by simp)
      | some rr =>
        rw [hpr] at hbsome
        simp only [] at hbsome
        split at hbsome
        · rename_i h5; exact ⟨rr, rfl, (Bool.and_eq_true _ _ |>.mp h5).1⟩
        · exact absurd hbsome (by simp)
    obtain ⟨rr, hpr, h5⟩ := hty5

    have hqne5 : qu.qtype ≠ (5 : BitVec 16) := by
      intro heq
      unfold Resolver.answersQueryB at hansF
      rw [hqu] at hansF
      simp only [] at hansF
      unfold Resolver.hasRRTypeIn at hansF
      simp only [Array.any_eq_false'] at hansF
      have hfalse := hansF b hbmem
      rw [hpr] at hfalse
      simp only [] at hfalse
      rw [heq] at hfalse
      exact hfalse h5

    unfold αQType at hqm
    split at hqm
    · exact absurd (Option.some.inj hqm).symm hqstar
    · cases hαt : αType qu.qtype with
      | none => rw [hαt] at hqm; exact absurd hqm (by simp)
      | some t =>
        rw [hαt] at hqm
        simp only [Option.map_some, Option.some.injEq] at hqm
        have htne : t ≠ RRType.cname := by
          intro heq
          subst heq

          have hto5 : qu.qtype.toNat = 5 := by
            unfold αType at hαt
            split at hαt <;> first | assumption | simp at hαt
          exact hqne5 (by
            apply BitVec.eq_of_toNat_eq
            rw [hto5]; rfl)
        rw [← hqm]
        show (QType.rr t).covers RRType.cname = false
        simp only [QType.covers]
        cases t <;> first | exact absurd rfl htne | rfl



theorem hasVerdict_congr_verdict
    {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Net.Time} {nseen seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {v v' : Response}
    (h : HasVerdict net ns ra ednsBuf rttOf now nseen seen c slist q v)
    (hrc : v'.rcode = v.rcode) (hans : v'.answer = v.answer) :
    HasVerdict net ns ra ednsBuf rttOf now nseen seen c slist q v' := by
  obtain ⟨tr, sp, tEnd, cout, resp, hres, hag⟩ := h
  exact ⟨tr, sp, tEnd, cout, resp, hres, hrc.trans hag.1, hans ▸ hag.2⟩

theorem hasVerdictAt_congr_verdict
    {net : Network} {ns : NetState} {ra : String} {ednsBuf : Nat} {rttOf : String → Nat}
    {now : Net.Time} {nseen seen : List Name} {c : Cache} {slist : List String} {q : Query}
    {v v' : Response} {coutM : Cache}
    (h : HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v coutM)
    (hrc : v'.rcode = v.rcode) (hans : v'.answer = v.answer) :
    HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v' coutM := by
  obtain ⟨tr, sp, tEnd, resp, hres, hag⟩ := h
  exact ⟨tr, sp, tEnd, resp, hres, hrc.trans hag.1, hans ▸ hag.2⟩

theorem lookupAnswerable_parseRaw_rrBytes {cache : DnsCache} {name : ByteArray} {qt qc : BitVec 16}
    {now : UInt32} {rr : VeriDNS.Spec.ResourceRecord}
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (h : rr ∈ (cache.lookupAnswerable name qt qc now).toList) :
    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr) = some rr := by
  obtain ⟨e, he, -, hrr⟩ := lookupAnswerable_mem_entry h
  subst hrr
  exact VeriDNS.Proof.NameTree.parseRaw_rrBytes_of_wf
    (VeriDNS.Proof.NameTree.wfRR_set_ttl (hwfrr e he) _)

theorem mem_cnameServed_of_hit_cname {c : Cache} {now : Net.Time} {qname : Name} {qcls : RRClass}
    {r : VeriDNS.Spec.Net.RR}
    (hmem : r ∈ c.hit now ⟨qname, QType.rr RRType.cname, qcls, false⟩)
    (hty : r.rdata.rtype = RRType.cname) :
    r ∈ c.cnameServed now qname qcls := by
  unfold Cache.hit at hmem
  rw [List.mem_map] at hmem
  obtain ⟨e, he, hr⟩ := hmem
  unfold Cache.cnameServed
  rw [List.mem_filterMap]
  refine ⟨e, he, ?_⟩
  have hety : e.rr.rdata.rtype = RRType.cname := by
    have : ({ e.rr with ttl := e.rr.ttl - (now - e.insertedAt) } : VeriDNS.Spec.Net.RR).rdata.rtype
        = RRType.cname := hr ▸ hty
    exact this
  rw [if_pos (by rw [hety]; exact rrtype_beq_self _)]
  rw [hr]

theorem hit_nil_of_lookupAnswerable_empty (cache : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : Query) (t : RRType)
    (hempty : (cache.lookupAnswerable name qt qc now).isEmpty = true)
    (hqn : αName name = some q.qname) (ht : αType qt = some t)
    (hqq : q.qtype = QType.rr t) (hqc : αClass qc = some q.qclass)
    (hcanN : name = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : CacheWf cache now) :
    (αCache cache).hit (αTime now) q = [] := by
  rw [← lookupAnswerable_αRR_eq_hit cache name qt qc now q t hqn ht hqq hqc hcanN hvN
      hwf.1 hwf.2.1 hwf.2.2]
  have : cache.lookupAnswerable name qt qc now = #[] := by
    rwa [Array.isEmpty_iff] at hempty
  rw [this]
  rfl

def CacheNegWf (c : DnsCache) (qc : BitVec 16) : Prop :=
  ∀ e ∈ c.negatives, e.qclass = qc
    ∧ (e.rcode = VeriDNS.Spec.Rcode.nameError ∨ e.rcode = VeriDNS.Spec.Rcode.noError)
    ∧ ∃ na, αName e.name = some na
        ∧ e.name = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63)

theorem CacheNegWf_congr {c c' : DnsCache} {qc : BitVec 16}
    (h : c'.negatives = c.negatives) (hwf : CacheNegWf c qc) : CacheNegWf c' qc := by
  intro e he
  exact hwf e (by rw [← h]; exact he)

theorem CacheNegWf_cacheUnlessTruncated (c : DnsCache) (resp : VeriDNS.Spec.Format)
    (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness) (now : UInt32) {qc : BitVec 16}
    (hwf : CacheNegWf c qc) :
    CacheNegWf (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      c resp raws cred now) qc :=
  CacheNegWf_congr (cacheUnlessTruncated_negatives c resp raws cred now) hwf

theorem CacheNegWf_boundExpiryClasses (c : DnsCache) {qc : BitVec 16} (hwf : CacheNegWf c qc) :
    CacheNegWf c.boundExpiryClasses qc :=
  CacheNegWf_congr rfl hwf

theorem wfrrAll_cacheUnlessTruncated {c : DnsCache}
    (hall : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (resp : VeriDNS.Spec.Format) (raws : Array ByteArray) (cred : VeriDNS.Spec.Trustworthiness)
    (now : UInt32) :
    ∀ e ∈ (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp raws cred now).records, VeriDNS.Proof.NameTree.WfRR e.rr := by
  intro e he
  unfold Resolver.cacheUnlessTruncated at he
  split at he
  · exact hall e he
  · rcases mem_cacheRRs_records _ cred now c he with hold | ⟨b, _, hp⟩
    · exact hall e hold
    · exact VeriDNS.Proof.NameTree.wfRR_of_parseRaw hp

theorem wfrrAll_boundExpiryClasses {c : DnsCache}
    (hall : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∀ e ∈ c.boundExpiryClasses.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
  intro e he
  exact hall e (mem_of_mem_evictClasses he)

theorem CacheNegWf_touchKeys {c : DnsCache} {qc : BitVec 16}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hwf : CacheNegWf c qc) : CacheNegWf (c.touchKeys ks tnow) qc := by
  intro e he
  rw [touchKeys_negatives] at he
  obtain ⟨e₀, he₀, rfl⟩ := Array.mem_map.mp he
  simp only [touchNegEntry_qclass, touchNegEntry_rcode, touchNegEntry_name]
  exact hwf e₀ he₀

theorem wfrrAll_touchKeys {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hall : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∀ e ∈ (c.touchKeys ks tnow).records, VeriDNS.Proof.NameTree.WfRR e.rr := by
  intro e he
  rw [touchKeys_records] at he
  obtain ⟨e₀, he₀, rfl⟩ := Array.mem_map.mp he
  rw [touchEntry_rr]
  exact hall e₀ he₀

theorem CacheNegWf_boundLruKeys (c : DnsCache) {qc : BitVec 16} (hwf : CacheNegWf c qc) :
    CacheNegWf c.boundLruKeys qc :=
  CacheNegWf_congr rfl hwf

theorem wfrrAll_boundLruKeys {c : DnsCache}
    (hall : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∀ e ∈ c.boundLruKeys.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
  intro e he
  exact hall e (mem_of_mem_evictLruKeys he)

theorem CacheNegWf_boundLru {c : DnsCache} {qc : BitVec 16}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hwf : CacheNegWf c qc) : CacheNegWf (c.boundLru ks tnow) qc :=
  CacheNegWf_boundLruKeys _ (CacheNegWf_touchKeys ks tnow hwf)

theorem wfrrAll_boundLru {c : DnsCache}
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hall : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    ∀ e ∈ (c.boundLru ks tnow).records, VeriDNS.Proof.NameTree.WfRR e.rr :=
  wfrrAll_boundLruKeys (wfrrAll_touchKeys ks tnow hall)

theorem cout_exports_bound (cache : DnsCache) (now32 : UInt32) (mcM : VeriDNS.Spec.Net.Cache)
    (ks : Array VeriDNS.Impl.Cache.RRKey) (tnow : UInt32)
    (hwf : CacheWf cache now32) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hnsd : CacheNsDistinct cache) (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey cache)
    (hmm : MatchMaxEquiv (αCache cache) mcM) :
    VeriDNS.Spec.Net.CacheRefines (αCache (cache.boundLru ks tnow)) mcM
    ∧ CacheWf (cache.boundLru ks tnow) now32
    ∧ CacheNsCanon (cache.boundLru ks tnow)
    ∧ CacheCnameCanon (cache.boundLru ks tnow)
    ∧ (∀ e ∈ (cache.boundLru ks tnow).records, VeriDNS.Proof.NameTree.WfRR e.rr)
    ∧ CacheNsDistinct (cache.boundLru ks tnow)
    ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey (cache.boundLru ks tnow)
    ∧ (cache.boundLru ks tnow).records.size ≤ DnsCache.capacity :=
  ⟨cacheRefines_boundLru_absorb cache mcM ks tnow hwfrr hmm,
   CacheWf_boundLru cache ks tnow now32 hwf,
   CacheNsCanon_boundLru cache ks tnow hns,
   CacheCnameCanon_boundLru cache ks tnow hcnc,
   wfrrAll_boundLru ks tnow hwfrr,
   CacheNsDistinct_boundLru cache ks tnow hnsd,
   VeriDNS.Proof.NameTree.oneExpiry_boundLru ks tnow hoe,
   VeriDNS.Proof.Cache.boundLru_bounded cache ks tnow⟩


theorem storeNegative_records (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (rc : Rcode) (soa : Option VeriDNS.Spec.ResourceRecord) (expiry tnow : UInt32) :
    (c.storeNegative name qt qc rc soa expiry tnow).records = c.records := rfl

theorem CacheNegWf_storeNegative {c : DnsCache} {qc : BitVec 16}
    (name : ByteArray) (qt : BitVec 16) (rc : Rcode)
    (soa : Option VeriDNS.Spec.ResourceRecord) (expiry tnow : UInt32)
    (hwf : CacheNegWf c qc)
    (hrc : rc = Rcode.nameError ∨ rc = Rcode.noError)
    (hcanon : ∃ na, αName name = some na
        ∧ name = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
        ∧ ∀ x ∈ na, x.size ≤ 63) :
    CacheNegWf (c.storeNegative name qt qc rc soa expiry tnow) qc := by
  intro e he
  simp only [DnsCache.storeNegative] at he
  rcases Array.mem_push.mp he with hmem | rfl
  · exact hwf e (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hmem)).1
  · exact ⟨rfl, hrc, hcanon⟩

theorem storeNegative_records_package {c : DnsCache} {now : UInt32}
    {name : ByteArray} {qt qc : BitVec 16} {rc : Rcode}
    {soa : Option VeriDNS.Spec.ResourceRecord} {expiry tnow : UInt32}
    (hwf : CacheWf c now) (hns : CacheNsCanon c) (hcnc : CacheCnameCanon c)
    (hwfrr : ∀ e ∈ c.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hnsd : CacheNsDistinct c) (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c) :
    CacheWf (c.storeNegative name qt qc rc soa expiry tnow) now
    ∧ CacheNsCanon (c.storeNegative name qt qc rc soa expiry tnow)
    ∧ CacheCnameCanon (c.storeNegative name qt qc rc soa expiry tnow)
    ∧ (∀ e ∈ (c.storeNegative name qt qc rc soa expiry tnow).records,
        VeriDNS.Proof.NameTree.WfRR e.rr)
    ∧ CacheNsDistinct (c.storeNegative name qt qc rc soa expiry tnow)
    ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey (c.storeNegative name qt qc rc soa expiry tnow) :=
  ⟨hwf, hns, hcnc, hwfrr, hnsd, hoe⟩

theorem strictDenialB_facts {resp : VeriDNS.Spec.Format}
    (h : Server.strictDenialB resp = true) :
    Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none
      ∧ resp.header.rcode = Rcode.nameError
      ∧ (resp.header.tc == 1) = false := by
  have hrcE := VeriDNS.Proof.NameTree.strictDenialB_rcode h
  unfold Server.strictDenialB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hcn, -⟩, htc⟩ := h
  refine ⟨Option.isNone_iff_eq_none.mp hcn, hrcE, ?_⟩
  have h0 : resp.header.tc = 0 := eq_of_beq htc
  rw [h0]
  decide

theorem capNegativeTtl_toNat (t : BitVec 32) :
    (Server.capNegativeTtl t).toNat = min t.toNat VeriDNS.Spec.Net.maxNegativeTtl := by
  unfold Server.capNegativeTtl Server.negativeTtlCap VeriDNS.Spec.Net.maxNegativeTtl
  by_cases h : t.toNat ≤ 10800
  · rw [if_pos h]
    omega
  · rw [if_neg h, BitVec.toNat_ofNat]
    omega

theorem topServed_eq_of_pos_eq {a b : VeriDNS.Spec.Net.Cache} (h : a.pos = b.pos)
    (now : VeriDNS.Spec.Net.Time) (q : Query) :
    a.topServed now q = b.topServed now q := by
  unfold VeriDNS.Spec.Net.Cache.topServed VeriDNS.Spec.Net.Cache.matching
  rw [h]

theorem αCache_storeNegative_pos (c : DnsCache) (name : ByteArray) (qt qc : BitVec 16)
    (rc : Rcode) (soa : Option VeriDNS.Spec.ResourceRecord) (expiry tnow : UInt32) :
    (αCache (c.storeNegative name qt qc rc soa expiry tnow)).pos = (αCache c).pos := rfl

theorem αCache_storeNegative_neg_mem {c : DnsCache} {name : ByteArray} {qt qc : BitVec 16}
    {rc : Rcode} {soa : Option VeriDNS.Spec.ResourceRecord} {expiry tnow : UInt32}
    {e : VeriDNS.Spec.Net.NegRR}
    (he : e ∈ (αCache (c.storeNegative name qt qc rc soa expiry tnow)).neg) :
    e ∈ (αCache c).neg ∨ αNegRR ⟨name, qt, qc, rc, expiry, soa, tnow⟩ = some e := by
  simp only [αCache, DnsCache.storeNegative, List.mem_filterMap] at he
  obtain ⟨ε, hεmem, hεα⟩ := he
  rcases Array.mem_push.mp (Array.mem_def.mpr hεmem) with hold | rfl
  · refine Or.inl ?_
    simp only [αCache, List.mem_filterMap]
    exact ⟨ε, Array.mem_def.mp (Array.mem_filter.mp (mem_of_mem_boundLruNegatives hold)).1, hεα⟩
  · exact Or.inr hεα

theorem αNegRR_nxEntry {name : ByteArray} {pqName : VeriDNS.Spec.Net.Name}
    (hqn : αName name = some pqName) (qt qc : BitVec 16)
    (soa : Option VeriDNS.Spec.ResourceRecord) (expiry tnow : UInt32) :
    αNegRR ⟨name, qt, qc, Rcode.nameError, expiry, soa, tnow⟩
      = some ⟨pqName, none, 0, expiry.toNat⟩ := by
  unfold αNegRR
  rw [hqn]
  rfl

theorem storeNegative_negWriteRefines_prepend
    {cache₀ : DnsCache} {c c' : VeriDNS.Spec.Net.Cache}
    {name : ByteArray} {qt qc : BitVec 16}
    {soa : Option VeriDNS.Spec.ResourceRecord} {expiry tnow : UInt32}
    {pqName : VeriDNS.Spec.Net.Name} {now ttlM : VeriDNS.Spec.Net.Time}
    (hmme : MatchMaxEquiv (αCache cache₀) c)
    (hqn : αName name = some pqName)
    (hexp : expiry.toNat = now + ttlM)
    (hpos' : c'.pos = c.pos)
    (hneg' : c'.neg = ⟨pqName, none, now, ttlM⟩ :: c.neg) :
    NegWriteRefines now
      (αCache (cache₀.storeNegative name qt qc Rcode.nameError soa expiry tnow)) c' := by
  have hpos := αCache_storeNegative_pos cache₀ name qt qc Rcode.nameError soa expiry tnow
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n _ q'
    rw [topServed_eq_of_pos_eq hpos, topServed_eq_of_pos_eq hpos']
    exact (hmme.1 n q').subperm
  · intro n q' e he
    rw [topServed_eq_of_pos_eq hpos] at he
    refine ⟨n, ?_⟩
    rw [topServed_eq_of_pos_eq hpos']
    exact (hmme.1 n q').subset he
  · intro n q' hq'
    obtain ⟨e, hmem, hpred⟩ := List.any_eq_true.mp hq'
    show c'.neg.any _ = true
    rw [hneg', List.any_cons]
    refine Bool.or_eq_true_iff.mpr ?_
    rcases αCache_storeNegative_neg_mem hmem with hold | hnew
    · refine Or.inr ?_
      show VeriDNS.Spec.Net.Cache.negHit c n q' = true
      rw [← hmme.2.1 n q']
      exact List.any_eq_true.mpr ⟨e, hold, hpred⟩
    · refine Or.inl ?_
      rw [αNegRR_nxEntry hqn] at hnew
      obtain rfl := Option.some.inj hnew
      simp only [Bool.and_eq_true] at hpred ⊢
      refine ⟨⟨?_, hpred.1.2⟩, trivial⟩
      have hfr := hpred.1.1
      unfold VeriDNS.Spec.Net.NegRR.fresh at hfr ⊢
      simpa [hexp] using hfr
  · intro n q' hq'
    obtain ⟨e, hmem, hpred⟩ := List.any_eq_true.mp hq'
    show c'.neg.any _ = true
    rw [hneg', List.any_cons]
    refine Bool.or_eq_true_iff.mpr ?_
    rcases αCache_storeNegative_neg_mem hmem with hold | hnew
    · refine Or.inr ?_
      show VeriDNS.Spec.Net.Cache.negHitNx c n q' = true
      rw [← hmme.2.2 n q']
      exact List.any_eq_true.mpr ⟨e, hold, hpred⟩
    · refine Or.inl ?_
      rw [αNegRR_nxEntry hqn] at hnew
      obtain rfl := Option.some.inj hnew
      simp only [Bool.and_eq_true] at hpred ⊢
      refine ⟨⟨?_, hpred.1.2⟩, rfl⟩
      have hfr := hpred.1.1
      unfold VeriDNS.Spec.Net.NegRR.fresh at hfr ⊢
      simpa [hexp] using hfr

theorem storeProbeNegative_negWriteRefines
    {cache₀ : DnsCache} {c : VeriDNS.Spec.Net.Cache} {sub respA : VeriDNS.Spec.Format}
    {now₀ : UInt32} {now : VeriDNS.Spec.Net.Time} {pq : Query} {reply : Datagram}
    (hmme : MatchMaxEquiv (αCache cache₀) c)
    (htm : αTime now₀ = now)
    (hclock : now₀.toNat + 604800 < 2 ^ 32)
    (hαQp : αQuery sub = some pq)
    (hauth : αSection respA.authority = reply.msg.authority)
    (hvldAuth : ∀ b ∈ respA.authority.toList, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
          ∧ αRR rr ≠ none)
    (hrcI : respA.header.rcode = Rcode.nameError)
    (hrcM : reply.msg.rcode = RCode.nameError)
    (hansM : reply.msg.answer = []) :
    NegWriteRefines now (αCache (Server.storeProbeNegative cache₀ sub respA now₀))
      (c.absorbNeg now pq reply.msg) := by
  obtain ⟨qu, hqu, hqn, -, -⟩ := αQuery_fields hαQp
  have hlock : VeriDNS.Spec.Net.soaNegTtl pq.qname reply.msg
      = (Server.extractSoaNegative qu.qname respA.authority).map (fun p => p.1.toNat) :=
    soaNegTtl_extractSoaNegative hqn hauth hvldAuth
  unfold Server.storeProbeNegative
  simp only [hqu]
  cases hext : Server.extractSoaNegative qu.qname respA.authority with
  | none =>
    have hm : VeriDNS.Spec.Net.soaNegTtl pq.qname reply.msg = none := by
      rw [hlock, hext]
      rfl
    have habs0 : c.absorbNeg now pq reply.msg = c := by
      unfold VeriDNS.Spec.Net.Cache.absorbNeg
      rw [hm]
    rw [habs0]
    exact ((MatchMaxEquiv.cacheRefines hmme).writeRefines now).negWriteRefines
  | some p =>
    obtain ⟨negTtl, soaRR⟩ := p
    have hm : VeriDNS.Spec.Net.soaNegTtl pq.qname reply.msg = some negTtl.toNat := by
      rw [hlock, hext]
      rfl
    have htm' : now₀.toNat = now := htm
    have hle : (Server.capNegativeTtl negTtl).toNat ≤ 604800 := by
      rw [capNegativeTtl_toNat]
      unfold VeriDNS.Spec.Net.maxNegativeTtl
      omega
    have hexp : (now₀ + (Server.capNegativeTtl negTtl).toNat.toUInt32).toNat
        = now + min negTtl.toNat VeriDNS.Spec.Net.maxNegativeTtl := by
      rw [uint32_add_ttl_toNat now₀ (Server.capNegativeTtl negTtl).toNat hle hclock,
        capNegativeTtl_toNat, htm']
    rw [hrcI]
    exact storeNegative_negWriteRefines_prepend hmme hqn hexp
      (VeriDNS.Spec.Net.absorbNeg_pos c now pq reply.msg)
      (VeriDNS.Spec.Net.absorbNeg_ttl_is_soa_minimum c now pq reply.msg negTtl.toNat hrcM hansM hm)

theorem storeProbeNegative_cases (cache : DnsCache) (sub resp : VeriDNS.Spec.Format)
    (now : UInt32) :
    Server.storeProbeNegative cache sub resp now = cache
    ∨ ∃ qu negTtl soaRR, sub.question[0]? = some qu
        ∧ Server.extractSoaNegative qu.qname resp.authority = some (negTtl, soaRR)
        ∧ Server.storeProbeNegative cache sub resp now
          = cache.storeNegative qu.qname qu.qtype qu.qclass resp.header.rcode
              (some { soaRR with ttl := Server.capNegativeTtl negTtl })
              (now + (Server.capNegativeTtl negTtl).toNat.toUInt32) now := by
  unfold Server.storeProbeNegative
  split
  · rename_i qu hqu
    split
    · rename_i negTtl soaRR hext
      exact Or.inr ⟨qu, negTtl, soaRR, hqu, hext, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem lookupNxdomain_none_negHitNx_false (cache : DnsCache) (sname : ByteArray) (qc : BitVec 16)
    (now : UInt32) (q : Query)
    (hcanN : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hnegwf : CacheNegWf cache qc)
    (hnone : cache.lookupNxdomain sname qc now = none) :
    (αCache cache).negHitNx (αTime now) q = false := by
  cases hx : (αCache cache).negHitNx (αTime now) q
  · rfl
  · exfalso
    unfold Cache.negHitNx at hx
    rw [List.any_eq_true] at hx
    obtain ⟨a, hamem, hcond⟩ := hx
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨⟨hfr, hnm⟩, hqt⟩ := hcond
    have hamem' : a ∈ (αCache cache).neg := hamem
    unfold αCache at hamem'
    simp only [List.mem_filterMap] at hamem'
    obtain ⟨e, he, hαe⟩ := hamem'
    obtain ⟨hcls, _hrc, na, hna, hcanE, hvE⟩ := hnegwf e (Array.mem_def.mpr he)

    unfold αNegRR at hαe
    split at hαe
    · exact absurd hαe (by simp)
    · rename_i n hn
      have hn_na : n = na := by rw [hn] at hna; exact Option.some.inj hna
      subst hn_na
      split at hαe
      · rename_i hrcE
        obtain rfl := Option.some.inj hαe

        have hfr' : now < e.expiry := by
          unfold NegRR.fresh at hfr
          simp only [Nat.zero_add] at hfr
          exact UInt32.lt_iff_toNat_lt.mpr (Nat.blt_eq.mp hfr)

        have hci : VeriDNS.Impl.DomainName.nameEqCI e.name sname = true :=
          nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN

        unfold Cache.DnsCache.lookupNxdomain at hnone
        rw [← Array.findSome?_toList, List.findSome?_eq_none_iff] at hnone
        have hfe := hnone e he
        rw [if_pos (by
          rw [hci, hrcE, hcls]
          simp only [beq_self_eq_true, Bool.and_true, Bool.true_and]
          exact decide_eq_true hfr')] at hfe
        exact absurd hfe (by simp)
      · split at hαe
        · rename_i t' hαt
          obtain rfl := Option.some.inj hαe
          exact absurd hqt (by simp)
        · exact absurd hαe (by simp)

theorem lookupNegative_none_negHit_false (cache : DnsCache) (sname : ByteArray) (qt qc : BitVec 16)
    (now : UInt32) (q : Query) (t : RRType)
    (ht : αType qt = some t) (hqq : q.qtype = QType.rr t)
    (hcanN : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hvN : ∀ x ∈ q.qname, x.size ≤ 63)
    (hnegwf : CacheNegWf cache qc)
    (hnone : cache.lookupNegative sname qt qc now = none) :
    (αCache cache).negHit (αTime now) q = false := by

  have harms : cache.lookupNxdomain sname qc now = none
      ∧ (cache.negatives.findSome? fun e =>
          if VeriDNS.Impl.DomainName.nameEqCI e.name sname && e.qtype == qt
              && e.qclass == qc && e.expiry > now then
            some e.rcode
          else none) = none := by
    unfold Cache.DnsCache.lookupNegative at hnone
    cases hnx : cache.lookupNxdomain sname qc now with
    | some rc' => rw [hnx] at hnone; exact absurd hnone (by simp [Option.orElse])
    | none => rw [hnx] at hnone; exact ⟨rfl, hnone⟩
  cases hx : (αCache cache).negHit (αTime now) q
  · rfl
  · exfalso
    unfold Cache.negHit at hx
    rw [List.any_eq_true] at hx
    obtain ⟨a, hamem, hcond⟩ := hx
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨⟨hfr, hnm⟩, hqt⟩ := hcond
    have hamem' : a ∈ (αCache cache).neg := hamem
    unfold αCache at hamem'
    simp only [List.mem_filterMap] at hamem'
    obtain ⟨e, he, hαe⟩ := hamem'
    obtain ⟨hcls, _hrc, na, hna, hcanE, hvE⟩ := hnegwf e (Array.mem_def.mpr he)
    unfold αNegRR at hαe
    split at hαe
    · exact absurd hαe (by simp)
    · rename_i n hn
      have hn_na : n = na := by rw [hn] at hna; exact Option.some.inj hna
      subst hn_na
      have hci : VeriDNS.Impl.DomainName.nameEqCI e.name sname = true := by
        split at hαe
        · obtain rfl := Option.some.inj hαe
          exact nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN
        · split at hαe
          · obtain rfl := Option.some.inj hαe
            exact nameEqCI_of_αName_canonical hnm hcanE hcanN hvE hvN
          · exact absurd hαe (by simp)
      have hfr' : now < e.expiry := by
        have hfrb : a.fresh (αTime now) = true := hfr
        have hins : a.insertedAt = 0 ∧ a.ttl = e.expiry.toNat := by
          split at hαe
          · obtain rfl := Option.some.inj hαe; exact ⟨rfl, rfl⟩
          · split at hαe
            · obtain rfl := Option.some.inj hαe; exact ⟨rfl, rfl⟩
            · exact absurd hαe (by simp)
        unfold NegRR.fresh at hfrb
        rw [hins.1, hins.2, Nat.zero_add] at hfrb
        exact UInt32.lt_iff_toNat_lt.mpr (Nat.blt_eq.mp hfrb)

      split at hαe
      ·
        rename_i hrcE
        unfold Cache.DnsCache.lookupNxdomain at harms
        have hnx := harms.1
        rw [← Array.findSome?_toList, List.findSome?_eq_none_iff] at hnx
        have hfe := hnx e he
        rw [if_pos (by
          rw [hci, hrcE, hcls]
          simp only [beq_self_eq_true, Bool.and_true, Bool.true_and]
          exact decide_eq_true hfr')] at hfe
        exact absurd hfe (by simp)
      · split at hαe
        ·
          rename_i t' hαt
          obtain rfl := Option.some.inj hαe
          have hqt' : (QType.rr t' == q.qtype) = true := hqt
          rw [hqq] at hqt'
          have htt : t' = t := by
            have hb : (t' == t) = true := hqt'
            exact eq_of_αType_beq hαt ht hb
          subst htt
          have hqteq : e.qtype = qt := αType_injective hαt ht
          have hnd := harms.2
          rw [← Array.findSome?_toList, List.findSome?_eq_none_iff] at hnd
          have hfe := hnd e he
          rw [if_pos (by
            rw [hci, hqteq, hcls]
            simp only [beq_self_eq_true, Bool.and_true, Bool.true_and]
            exact decide_eq_true hfr')] at hfe
          exact absurd hfe (by simp)
        · exact absurd hαe (by simp)

theorem cnameChaseVisited_toList (q0 : ByteArray) (chain : Array ByteArray) :
    (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) q0 chain).toList
      = q0 :: chain.toList.filterMap (fun b =>
          (VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b).map
            (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord))) := by
  unfold Resolver.cnameChaseVisited
  rw [Array.toList_append, Array.toList_filterMap]
  rfl

theorem cnameChaseVisited_push (q0 : ByteArray) (chain : Array ByteArray) {raw : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord}
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr) :
    (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) q0 (chain.push raw)).toList
      = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) q0 chain).toList
          ++ [VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr] := by
  rw [cnameChaseVisited_toList, cnameChaseVisited_toList, Array.toList_push,
    List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, hpr, Option.map_some, List.cons_append]

theorem αSection_push {chain : Array ByteArray} {raw : ByteArray}
    {rr : VeriDNS.Spec.ResourceRecord} {cn : VeriDNS.Spec.Net.RR}
    (hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr)
    (hα : αRR rr = some cn) :
    αSection (chain.push raw) = αSection chain ++ [cn] := by
  rw [αSection_eq_filterMap, αSection_eq_filterMap, Array.toList_push, List.filterMap_append]
  have h1 : List.filterMap αSecF [raw] = [cn] := by
    simp only [List.filterMap_cons, List.filterMap_nil, αSecF_some hpr, hα]
  rw [h1]

theorem covers_cname_false_of_ne {t : RRType} (htne : t ≠ RRType.cname) :
    (QType.rr t).covers RRType.cname = false := by
  simp only [QType.covers]
  cases t <;> first | exact absurd rfl htne | rfl

theorem qt_ne5_of_αType {qt : BitVec 16} {t : RRType} (ht : αType qt = some t)
    (htne : t ≠ RRType.cname) : (qt == (5 : BitVec 16)) = false := by
  cases h5 : qt == (5 : BitVec 16)
  · rfl
  · exfalso
    have hq5 : qt = (5 : BitVec 16) := eq_of_beq h5
    rw [hq5] at ht
    have hcn : some RRType.cname = some t := by rw [← ht]; rfl
    exact htne (Option.some.inj hcn).symm

theorem localAnswer_chase_peel
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (cache : DnsCache) (mc : Cache) (qt qc : BitVec 16) (now32 : UInt32)
    (q0 : Query) (t : RRType) (seen : List Name) (qname0 : ByteArray)
    (ht : αType qt = some t) (hqq : q0.qtype = QType.rr t) (htne : t ≠ RRType.cname)
    (hqc : αClass qc = some q0.qclass)
    (hmm : MatchMaxEquiv (αCache cache) mc)
    (hwf : CacheWf cache now32) (hCn : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hnegwf : CacheNegWf cache qc) :
    ∀ (fuel : Nat) (sname : ByteArray) (n0 : Name) (chain visited : Array ByteArray)
      (nseen0 : List Name) (res : Resolver.LocalResult VeriDNS.Spec.ResourceRecord),
      Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qt qc now32 fuel sname chain visited = res →
      αName sname = some n0 →
      sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo n0 →
      (∀ x ∈ n0, x.size ≤ 63) →
      n0.length ≤ 127 →
      visited.toList
        = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qname0 chain).toList →
      (∀ nm ∈ n0 :: nseen0, ∃ b ∈ visited.toList,
          αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
            ∧ (∀ x ∈ nm, x.size ≤ 63)) →
      match res with
      | .answerHit _snameF chainF rrs =>
          ∃ links : List VeriDNS.Spec.Net.RR,
            αSection chainF = αSection chain ++ links
            ∧ ∀ v : Response, v.rcode = RCode.noError
                → v.answer = links ++ rrs.toList.filterMap αRR
                → ∀ nsl : List String,
                  HasVerdictAt net ns ra ednsBuf rttOf (αTime now32) nseen0 seen mc nsl
                    { q0 with qname := n0 } v mc
      | .miss snameF chainF =>
          ∃ (links : List VeriDNS.Spec.Net.RR) (nF : Name) (nseenF : List Name),
            αSection chainF = αSection chain ++ links
            ∧ αName snameF = some nF
            ∧ snameF = VeriDNS.Impl.DomainName.labelsToWireFormatGo nF
            ∧ (∀ x ∈ nF, x.size ≤ 63)
            ∧ nF.length ≤ 127
            ∧ (∀ nm ∈ nF :: nseenF, ∃ b ∈ (Resolver.cnameChaseVisited
                  (RR := VeriDNS.Spec.ResourceRecord) qname0 chainF).toList,
                αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                  ∧ (∀ x ∈ nm, x.size ≤ 63))
            ∧ mc.hit (αTime now32) { q0 with qname := nF } = []
            ∧ mc.negHit (αTime now32) { q0 with qname := nF } = false

            ∧ (∀ r ∈ links, r.rdata.rtype = RRType.cname)

            ∧ ∀ (cfK : Cache), CacheRefines cfK mc →
                ∀ (vK : Response) (nsl : List String) (coutK : Cache),
                HasVerdictAt net ns ra ednsBuf rttOf (αTime now32) nseenF seen cfK nsl
                  { q0 with qname := nF } vK coutK →
                ∀ v : Response, v.rcode = vK.rcode → v.answer = links ++ vK.answer →
                  ∃ cOut : Cache, CacheRefines cOut mc ∧ (cOut = mc ∨ cOut = cfK) ∧
                    HasVerdictAt net ns ra ednsBuf rttOf (αTime now32) nseen0 seen cOut nsl
                      { q0 with qname := n0 } v coutK
      | .negative rc _soaAuth chainF =>
          ∃ links : List VeriDNS.Spec.Net.RR,
            αSection chainF = αSection chain ++ links
            ∧ ∀ v : Response, v.rcode = αRCode rc → v.answer = links →
              ∀ nsl : List String,
                HasVerdictAt net ns ra ednsBuf rttOf (αTime now32) nseen0 seen mc nsl
                  { q0 with qname := n0 } v mc
      | .abort => True := by

  have hnt5 : (qt == (5 : BitVec 16)) = false := qt_ne5_of_αType ht htne
  have hqtc : q0.qtype.covers RRType.cname = false := by
    rw [hqq]; exact covers_cname_false_of_ne htne
  intro fuel
  induction fuel with
  | zero =>
    intro sname n0 chain visited nseen0 res hla _ _ _ _ _ _
    simp only [Resolver.localAnswer] at hla
    rw [← hla]
    trivial
  | succ fuel ih =>
    intro sname n0 chain visited nseen0 res hla hα hcan hval hlen hveq hvis
    simp only [Resolver.localAnswer] at hla
    split at hla
    ·
      rename_i rc hnegS
      have hlk : cache.lookupNegative sname qt qc now32 = some rc := hnegS
      rw [← hla]
      refine ⟨[], (List.append_nil _).symm, ?_⟩
      intro v hrc hva nsl

      have hnegT : mc.negHit (αTime now32) { q0 with qname := n0 } = true := by
        rw [← hmm.2.1]
        exact lookupNegative_negHit cache sname qt qc now32 rc { q0 with qname := n0 } t
          hlk hα ht hqq

      have hrcEq : αRCode rc
          = (if mc.negHitNx (αTime now32) { q0 with qname := n0 }
              then RCode.nameError else RCode.noError) := by
        unfold Cache.DnsCache.lookupNegative at hlk
        cases hnx : cache.lookupNxdomain sname qc now32 with
        | some rc' =>
          rw [hnx] at hlk
          have hrc' : rc = rc' := by
            simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hlk
            exact (Option.some.inj hlk).symm
          subst hrc'
          have hne : rc = VeriDNS.Spec.Rcode.nameError := lookupNxdomain_nameError _ _ _ _ _ hnx
          have hnxT : mc.negHitNx (αTime now32) { q0 with qname := n0 } = true := by
            rw [← hmm.2.2]
            exact lookupNxdomain_negHitNx cache sname qc now32 rc { q0 with qname := n0 } hnx hα
          rw [hnxT, if_pos rfl, hne]
          rfl
        | none =>
          rw [hnx] at hlk
          simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hlk
          obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some hlk
          have hnxF : mc.negHitNx (αTime now32) { q0 with qname := n0 } = false := by
            rw [← hmm.2.2]
            exact lookupNxdomain_none_negHitNx_false cache sname qc now32
              { q0 with qname := n0 } hcan hval hnegwf hnx
          rw [hnxF, if_neg (by simp)]
          split at hef
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            have hrcE : rc = e.rcode := (Option.some.inj hef).symm
            rcases (hnegwf e hemem).2.1 with hne | hno
            ·
              exfalso
              unfold Cache.DnsCache.lookupNxdomain at hnx
              rw [← Array.findSome?_toList, List.findSome?_eq_none_iff] at hnx
              have hfe := hnx e (Array.mem_def.mp hemem)
              rw [if_pos (by
                rw [hcond.1.1.1, hne]
                simp only [Bool.true_and]
                rw [Bool.and_eq_true, Bool.and_eq_true]
                exact ⟨⟨hcond.1.2, hcond.2⟩, by decide⟩)] at hfe
              exact absurd hfe (by simp)
            · rw [hrcE, hno]; rfl
          · exact absurd hef (by simp)

      refine negHit_hasVerdictAt net ns ra ednsBuf rttOf mc nsl { q0 with qname := n0 } hnegT v
        ⟨?_, ?_⟩
      · rw [hrc, hrcEq]; rfl
      · rw [hva]
        show List.Perm [] (mc.negResponse (αTime now32) { q0 with qname := n0 }).answer
        exact List.Perm.refl _
    · rename_i hnegN
      have hlkN : cache.lookupNegative sname qt qc now32 = none := hnegN

      have hnmiss_i : mc.negHit (αTime now32) { q0 with qname := n0 } = false := by
        rw [← hmm.2.1]
        exact lookupNegative_none_negHit_false cache sname qt qc now32
          { q0 with qname := n0 } t ht hqq hcan hval hnegwf hlkN
      split at hla
      ·
        rename_i hempty

        have hmiss_i : mc.hit (αTime now32) { q0 with qname := n0 } = [] := by
          have h0 : (αCache cache).hit (αTime now32) { q0 with qname := n0 } = [] :=
            hit_nil_of_lookupAnswerable_empty cache sname qt qc now32 { q0 with qname := n0 } t
              hempty hα ht hqq hqc hcan hval hwf
          have hp := hmm.hit (αTime now32) { q0 with qname := n0 }
          rw [h0] at hp
          exact (List.perm_nil.mp hp.symm)
        split at hla
        ·
          rename_i h5
          rw [hnt5] at h5
          exact absurd h5 (by simp)
        · split at hla
          · rename_i crr hcrr
            split at hla
            ·
              rw [← hla]
              refine ⟨[], n0, nseen0, (List.append_nil _).symm, hα, hcan, hval, hlen, ?_, hmiss_i,
                hnmiss_i, (fun r hr => absurd hr (List.not_mem_nil)), ?_⟩
              · rw [← hveq]; exact hvis
              · intro cfK hcfK vK nsl coutK hK v hrc hva
                exact ⟨cfK, hcfK, Or.inr rfl, hasVerdictAt_congr_verdict hK hrc (by rw [hva]; rfl)⟩
            ·
              rename_i hnrev
              rw [Bool.not_eq_true] at hnrev

              have hcrrmem : crr ∈ (cache.lookupAnswerable sname (5 : BitVec 16) qc now32).toList := by
                obtain ⟨h0, heq0⟩ := Array.getElem?_eq_some_iff.mp hcrr
                exact heq0 ▸ Array.mem_def.mp (Array.getElem_mem h0)
              obtain ⟨⟨cn, hαcrr⟩, hty5⟩ := lookupAnswerable_αRR_isSome hwf.1 hcrrmem

              obtain ⟨na, hna, hnacan, hnaval, hnalen⟩ :=
                cname_rdata_canonical_of_CacheCnameCanon cache sname qc now32 hCn crr hcrrmem
              have hrdEq : VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr
                  = crr.rdata := rfl

              obtain ⟨na', hcnrd', hna'⟩ := αRR_cname_target crr cn hty5 hαcrr
              have hnaEq : na' = na := by
                rw [hrdEq] at hna
                exact Option.some.inj ((hna'.symm).trans hna)
              have hcnrd : cn.rdata = RData.cname na := by rw [hcnrd', hnaEq]

              have hcnServed : cn ∈ mc.cnameServed (αTime now32) n0 q0.qclass := by
                have heq5 := lookupAnswerable_αRR_eq_hit cache sname (5 : BitVec 16) qc now32
                  ⟨n0, QType.rr RRType.cname, q0.qclass, false⟩ RRType.cname
                  hα rfl rfl hqc hcan hval hwf.1 hwf.2.1 hwf.2.2
                have hmemHit : cn ∈ (αCache cache).hit (αTime now32)
                    ⟨n0, QType.rr RRType.cname, q0.qclass, false⟩ := by
                  rw [← heq5]
                  exact List.mem_filterMap.mpr ⟨crr, hcrrmem, hαcrr⟩
                have htyCn : cn.rdata.rtype = RRType.cname := by rw [hcnrd]; rfl
                have hsrv := mem_cnameServed_of_hit_cname hmemHit htyCn
                exact ((MatchMaxEquiv.cnameServed hmm (αTime now32) n0 q0.qclass).mem_iff).mp hsrv

              have hfresh : na ∉ n0 :: nseen0 :=
                visited_target_fresh (n0 :: nseen0) visited
                  (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr) na hvis
                  (hrdEq.trans hnacan) hnaval hnrev

              have hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
                  (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) crr)
                    = some crr :=
                lookupAnswerable_parseRaw_rrBytes hwfrr hcrrmem

              have hveq' : (visited.push (VeriDNS.Spec.RRParse.rrRdata
                    (RR := VeriDNS.Spec.ResourceRecord) crr)).toList
                  = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qname0
                      (chain.push (VeriDNS.Spec.RRParse.rrBytes
                        (RR := VeriDNS.Spec.ResourceRecord) crr))).toList := by
                rw [Array.toList_push, hveq, cnameChaseVisited_push qname0 chain hpr]
              have hvis' : ∀ nm ∈ na :: n0 :: nseen0,
                  ∃ b ∈ (visited.push (VeriDNS.Spec.RRParse.rrRdata
                      (RR := VeriDNS.Spec.ResourceRecord) crr)).toList,
                    αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                      ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                intro nm hnm
                rcases List.mem_cons.mp hnm with rfl | hnm
                · refine ⟨VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr,
                    ?_, by rw [hrdEq]; exact hna, hrdEq.trans hnacan, hnaval⟩
                  rw [Array.toList_push]
                  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                · obtain ⟨b, hb, hfacts⟩ := hvis nm hnm
                  refine ⟨b, ?_, hfacts⟩
                  rw [Array.toList_push]
                  exact List.mem_append_left _ hb

              have ihres := ih (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr)
                na (chain.push (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) crr))
                (visited.push (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr))
                (n0 :: nseen0) res hla (by rw [hrdEq]; exact hna) (hrdEq.trans hnacan) hnaval
                hnalen hveq' hvis'

              have hsecPush : αSection (chain.push (VeriDNS.Spec.RRParse.rrBytes
                    (RR := VeriDNS.Spec.ResourceRecord) crr)) = αSection chain ++ [cn] :=
                αSection_push hpr hαcrr

              cases res with
              | abort => trivial
              | answerHit snameF chainF rrs =>
                obtain ⟨links', hchain', hcont'⟩ := ihres
                refine ⟨cn :: links', by rw [hchain', hsecPush, List.append_assoc]; rfl, ?_⟩
                intro v hrc hva nsl
                refine cacheCname_hasVerdictAt_hv net ns ra ednsBuf rttOf nsl
                  { q0 with qname := n0 } cn na mc nsl hmiss_i hnmiss_i hcnServed hqtc hcnrd
                  hfresh mc (CacheRefines.refl mc)
                  { v with answer := links' ++ rrs.toList.filterMap αRR } v rfl
                  (by rw [hva]; rfl) mc ?_
                exact hcont' { v with answer := links' ++ rrs.toList.filterMap αRR } hrc rfl nsl
              | miss snameF chainF =>
                obtain ⟨links', nF, nseenF, hchain', hnF, hnFcan, hnFval, hnFlen, hvisF, hmissF,
                  hnmissF, hlinksCn', hcont'⟩ := ihres
                refine ⟨cn :: links', nF, nseenF,
                  by rw [hchain', hsecPush, List.append_assoc]; rfl,
                  hnF, hnFcan, hnFval, hnFlen, hvisF, hmissF, hnmissF,
                  (fun r hr => by
                    rcases List.mem_cons.mp hr with rfl | hr'
                    · rw [hcnrd]; rfl
                    · exact hlinksCn' r hr'), ?_⟩
                intro cfK hcfK vK nsl coutK hK v hrc hva
                obtain ⟨cOut', hcOut', -, hV'⟩ :=
                  hcont' cfK hcfK vK nsl coutK hK { v with answer := links' ++ vK.answer } hrc rfl
                refine ⟨mc, CacheRefines.refl mc, Or.inl rfl, ?_⟩
                exact cacheCname_hasVerdictAt_hv net ns ra ednsBuf rttOf nsl
                  { q0 with qname := n0 } cn na mc nsl hmiss_i hnmiss_i hcnServed hqtc hcnrd
                  hfresh cOut' hcOut' { v with answer := links' ++ vK.answer } v rfl
                  (by rw [hva]; rfl) coutK hV'
              | negative rc soaAuth chainF =>
                obtain ⟨links', hchain', hcont'⟩ := ihres
                refine ⟨cn :: links', by rw [hchain', hsecPush, List.append_assoc]; rfl, ?_⟩
                intro v hrc hva nsl
                refine cacheCname_hasVerdictAt_hv net ns ra ednsBuf rttOf nsl
                  { q0 with qname := n0 } cn na mc nsl hmiss_i hnmiss_i hcnServed hqtc hcnrd
                  hfresh mc (CacheRefines.refl mc)
                  { v with answer := links' } v rfl (by rw [hva]) mc ?_
                exact hcont' { v with answer := links' } hrc rfl nsl
          ·
            rw [← hla]
            refine ⟨[], n0, nseen0, (List.append_nil _).symm, hα, hcan, hval, hlen, ?_, hmiss_i,
              hnmiss_i, (fun r hr => absurd hr (List.not_mem_nil)), ?_⟩
            · rw [← hveq]; exact hvis
            · intro cfK hcfK vK nsl coutK hK v hrc hva
              exact ⟨cfK, hcfK, Or.inr rfl, hasVerdictAt_congr_verdict hK hrc (by rw [hva]; rfl)⟩
      ·
        rename_i hne
        rw [← hla]
        refine ⟨[], (List.append_nil _).symm, ?_⟩
        intro v hrc hva nsl
        have hne' : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
            (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now32).isEmpty = false := by
          simpa using hne

        have heq := lookupAnswerable_αRR_eq_hit cache sname qt qc now32
          { q0 with qname := n0 } t hα ht hqq hqc hcan hval hwf.1 hwf.2.1 hwf.2.2
        have hperm : ((VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
            (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc
              now32).toList.filterMap αRR).Perm
            (mc.hit (αTime now32) { q0 with qname := n0 }) := by
          rw [show (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
              (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now32).toList.filterMap αRR
              = (cache.lookupAnswerable sname qt qc now32).toList.filterMap αRR from rfl, heq]
          exact MatchMaxEquiv.hit hmm (αTime now32) { q0 with qname := n0 }

        have hlen : 0 < (mc.hit (αTime now32) { q0 with qname := n0 }).length := by
          have hnil : cache.lookupAnswerable sname qt qc now32 ≠ #[] := by
            intro h0
            rw [show (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
                (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now32).isEmpty
                = (cache.lookupAnswerable sname qt qc now32).isEmpty from rfl, h0] at hne'
            exact absurd hne' (by simp)
          have hsz : 0 < (cache.lookupAnswerable sname qt qc now32).size := by
            rcases Nat.eq_zero_or_pos (cache.lookupAnswerable sname qt qc now32).size with h0 | h
            · exact absurd (Array.size_eq_zero_iff.mp h0) hnil
            · exact h
          have hmem0 : (cache.lookupAnswerable sname qt qc now32)[0]
              ∈ (cache.lookupAnswerable sname qt qc now32).toList :=
            Array.mem_def.mp (Array.getElem_mem hsz)
          obtain ⟨⟨cn0, hαcn0⟩, -⟩ := lookupAnswerable_αRR_isSome hwf.1 hmem0
          have hmemM : cn0 ∈ mc.hit (αTime now32) { q0 with qname := n0 } :=
            (hperm.mem_iff).mp (List.mem_filterMap.mpr ⟨_, hmem0, hαcn0⟩)
          cases hml : mc.hit (αTime now32) { q0 with qname := n0 } with
          | nil => rw [hml] at hmemM; exact absurd hmemM (by simp)
          | cons a l => simp
        refine cacheHit_hasVerdictAt net ns ra ednsBuf rttOf mc nsl { q0 with qname := n0 }
          (mc.hit (αTime now32) { q0 with qname := n0 }) rfl hlen v ⟨hrc, ?_⟩
        rw [hva]
        show List.Perm ((VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
            (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now32).toList.filterMap αRR) _
        exact hperm


theorem αQType_rr_inv {qt : BitVec 16} {Q : VeriDNS.Spec.Net.QType}
    (h : αQType qt = some Q) (hstar : Q ≠ VeriDNS.Spec.Net.QType.star) :
    ∃ t, αType qt = some t ∧ Q = VeriDNS.Spec.Net.QType.rr t := by
  unfold αQType at h
  split at h
  · exact absurd (Option.some.inj h).symm hstar
  · cases hαt : αType qt with
    | none => rw [hαt] at h; exact absurd h (by simp)
    | some t =>
      rw [hαt] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨t, rfl, h.symm⟩

theorem buildSubQuery_inv
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (sub : VeriDNS.Spec.Format) (revealed : Nat)
    (h : Resolver.buildSubQuery s revealed = some sub) :
    ∃ qF qu, s.lastQuery = some qF ∧ qF.question[0]? = some qu
      ∧ sub.question = #[Resolver.subQuestion s.resources.sname revealed qu] := by
  unfold Resolver.buildSubQuery at h
  split at h
  · exact absurd h (by simp)
  · rename_i qF hlq
    split at h
    · exact absurd h (by simp)
    · rename_i qu hqu
      injection h with hb
      exact ⟨qF, qu, hlq, hqu, by rw [← hb]⟩

theorem subQuestion_full {sname : ByteArray} {revealed : Nat}
    (hfull : Resolver.probeRoundB sname revealed = false) (qu : VeriDNS.Spec.Question) :
    Resolver.subQuestion sname revealed qu
      = { qname := sname, qtype := qu.qtype, qclass := qu.qclass } := by
  unfold Resolver.subQuestion
  rw [hfull]
  rfl

theorem subQuestion_probe {sname : ByteArray} {revealed : Nat}
    (hprobe : Resolver.probeRoundB sname revealed = true) (qu : VeriDNS.Spec.Question) :
    Resolver.subQuestion sname revealed qu
      = { qname := VeriDNS.Impl.DomainName.minimisedName sname revealed,
          qtype := (1 : BitVec 16), qclass := qu.qclass } := by
  unfold Resolver.subQuestion
  rw [hprobe]
  rfl

theorem questionMatches_fields {respQ : Array VeriDNS.Spec.Question}
    {sentQ : Array VeriDNS.Spec.Question} {qu : VeriDNS.Spec.Question} {sw snameB : ByteArray}
    (hsq : sentQ[0]? = some { qname := sw, qtype := qu.qtype, qclass := qu.qclass })
    (hswci : VeriDNS.Impl.DomainName.nameEqCI sw snameB = true)
    (hqm : Server.questionMatches respQ sentQ = true) :
    ∃ qa : VeriDNS.Spec.Question, respQ[0]? = some qa
      ∧ VeriDNS.Impl.DomainName.nameEqCI qa.qname snameB = true
      ∧ qa.qtype = qu.qtype ∧ qa.qclass = qu.qclass := by
  unfold Server.questionMatches at hqm
  rw [hsq] at hqm
  cases hqa : respQ[0]? with
  | none => rw [hqa] at hqm; simp at hqm
  | some qa =>
    rw [hqa] at hqm
    simp only [] at hqm
    simp only [Bool.and_eq_true] at hqm
    exact ⟨qa, rfl,
      VeriDNS.Proof.NameTree.nameEqCI_trans
        (VeriDNS.Proof.NameTree.nameEqCI_of_beq hqm.1.1) hswci,
      eq_of_beq hqm.1.2, eq_of_beq hqm.2⟩

theorem withSecrets_question (q : VeriDNS.Spec.Format) (rid cid : UInt16)
    {sname : ByteArray} {qu : VeriDNS.Spec.Question}
    (hq : q.question = #[{ qname := sname, qtype := qu.qtype, qclass := qu.qclass }]) :
    (Server.withSecrets q rid cid).question[0]?
      = some { qname := VeriDNS.Impl.DomainName.randomizeCase cid sname,
               qtype := qu.qtype, qclass := qu.qclass } := by
  show (q.question.map _)[0]? = _
  rw [Array.getElem?_map, hq]
  rfl


theorem probeRoundB_facts {sname : ByteArray} {revealed : Nat}
    (h : Resolver.probeRoundB sname revealed = true) :
    0 < revealed ∧ revealed < VeriDNS.Impl.DomainName.labelCount sname := by
  unfold Resolver.probeRoundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem labelCount_of_αName {m : ByteArray} {n : VeriDNS.Spec.Net.Name}
    (h : αName m = some n) :
    VeriDNS.Impl.DomainName.labelCount m = n.length := by
  unfold αName at h
  cases hm : VeriDNS.Impl.DomainName.wireFormatToLabels m with
  | error e => rw [hm] at h; exact absurd h (by simp)
  | ok ls =>
    rw [hm] at h
    injection h with h
    unfold VeriDNS.Impl.DomainName.labelCount
    rw [hm, ← h, Array.length_toList]

private theorem rcode_beq_eq {a b : VeriDNS.Spec.Rcode} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem probePassable_false_of_chase {resp : VeriDNS.Spec.Format} {c : ByteArray}
    (h : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some c) :
    Server.probePassableB resp = false := by
  unfold Server.probePassableB Server.referralShapedB Server.retryShapedB
  rw [h]
  rfl

theorem afterResume_finished_probePassable_false
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {entryName : ByteArray} {respA : VeriDNS.Spec.Format}
    {result : Except String VeriDNS.Spec.Format} {cacheR : DnsCache}
    (hstep : state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries)
    (hAR : Server.afterResume state entryName respA = .finished result cacheR) :
    Server.probePassableB respA = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  rcases Bool.or_eq_true_iff.mp h with href | hretry
  · unfold Server.referralShapedB at href
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at href
    obtain ⟨⟨⟨⟨⟨⟨⟨hcn, hans⟩, hemp⟩, hane⟩, hns⟩, haa⟩, hnoerr⟩, hsoa⟩ := href
    have hnerr : (respA.header.rcode == VeriDNS.Spec.Rcode.nameError) = false := by
      rw [rcode_beq_eq hnoerr]; decide
    have hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = false := by
      have hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false := by
        rw [rcode_beq_eq hnoerr]; decide
      have hcls : Resolver.classifiableB respA = true := by
        unfold Resolver.classifiableB
        rw [hnoerr]
        simp
      rw [hsf, hcls]
      rfl
    obtain ⟨st, heq, -⟩ := afterResume_referral_continue_cases state entryName respA
      hstep hcn hbiz hans hnerr hemp hane hns haa hnoerr hsoa
    rw [heq] at hAR
    exact Server.IoStep.noConfusion hAR
  · unfold Server.retryShapedB at hretry
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hretry
    obtain ⟨hcn, hbiz⟩ := hretry
    rw [afterResume_bizarre state entryName respA hstep hcn hbiz] at hAR
    exact Server.IoStep.noConfusion hAR

theorem inBailiwick_of_ancestor {r : VeriDNS.Spec.Net.Response} {a b : VeriDNS.Spec.Net.Name}
    (h : r.inBailiwick a = true) (hab : isAncestor a b = true) :
    r.inBailiwick b = true := by
  unfold VeriDNS.Spec.Net.Response.inBailiwick at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro rr hrr
  rcases Bool.or_eq_true_iff.mp (h rr hrr) with hn | ha
  · exact Bool.or_eq_true_iff.mpr (Or.inl hn)
  · exact Bool.or_eq_true_iff.mpr (Or.inr (isAncestor_trans ha hab))

theorem αQuery_buildSubQuery_probe
    {state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {q : Query} {sub : VeriDNS.Spec.Format} {revealed : Nat}
    (hbuild : Resolver.buildSubQuery state revealed = some sub)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (hsn : αName state.resources.sname = some q.qname)
    (hqm : ∀ qu : VeriDNS.Spec.Question,
        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
        αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass) :
    ∃ pq : Query, αQuery sub = some pq ∧ StrictProbe pq q := by
  obtain ⟨h0lt, hltc⟩ := probeRoundB_facts hprobe
  have hlen : VeriDNS.Impl.DomainName.labelCount state.resources.sname = q.qname.length :=
    labelCount_of_αName hsn
  have hrevle : revealed ≤ q.qname.length := by omega
  obtain ⟨hanc, hplen⟩ := isAncestor_drop_ancestor (n := q.qname) (k := revealed) hrevle
  unfold Resolver.buildSubQuery at hbuild
  split at hbuild
  · exact absurd hbuild (by simp)
  · rename_i q₀ hlq
    split at hbuild
    · exact absurd hbuild (by simp)
    · rename_i qu hqu
      injection hbuild with hb
      subst hb
      obtain ⟨-, hqc⟩ := hqm qu ⟨q₀, hlq, hqu⟩
      refine ⟨{ qname := q.qname.drop (q.qname.length - revealed),
                qtype := QType.rr RRType.a, qclass := q.qclass, rd := false }, ?_, ?_⟩
      · unfold αQuery
        rw [show (#[Resolver.subQuestion state.resources.sname revealed qu]
            : Array VeriDNS.Spec.Question)[0]? = some
            (Resolver.subQuestion state.resources.sname revealed qu) from rfl,
          subQuestion_probe hprobe]
        dsimp only
        rw [VeriDNS.Proof.QnameMin.αName_minimisedName hsn revealed, hqc]
        rfl
      · refine ⟨⟨[], ?_⟩, rfl, rfl⟩
        unfold ProbeFor
        have h0 : isAncestor [] (q.qname.drop (q.qname.length - revealed)) = true := by
          have h := (isAncestor_drop_ancestor
            (n := q.qname.drop (q.qname.length - revealed)) (k := 0) (Nat.zero_le _)).1
          rwa [Nat.sub_zero, List.drop_length] at h
        rw [h0, hanc]
        simp only [Bool.true_and, Bool.and_eq_true, Nat.blt_eq, List.length_nil, hplen]
        omega

theorem cname_link_facts {sname : ByteArray} {qn : VeriDNS.Spec.Net.Name}
    {answer : Array ByteArray} {target : ByteArray}
    (hsq : αName sname = some qn)
    (hsc : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qn)
    (hsv : ∀ x ∈ qn, x.size ≤ 63)
    (h : Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) sname answer = some target)
    (hvalid : ∀ b ∈ answer.toList, ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
          ∧ αRR rr ≠ none) :
    ∃ (cnBytes : ByteArray) (rrCn : VeriDNS.Spec.ResourceRecord) (cn : VeriDNS.Spec.Net.RR)
      (tgt : VeriDNS.Spec.Net.Name),
      Resolver.extractCnameRR (RR := VeriDNS.Spec.ResourceRecord) sname answer = some cnBytes
      ∧ cnBytes ∈ answer.toList
      ∧ VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) cnBytes = some rrCn
      ∧ rrCn.type = (5 : BitVec 16)
      ∧ rrCn.rdata = target
      ∧ αRR rrCn = some cn
      ∧ VeriDNS.Spec.Net.cnameRR qn (αSection answer) = some cn
      ∧ cn.rdata = VeriDNS.Spec.Net.RData.cname tgt
      ∧ αName target = some tgt := by
  unfold Resolver.extractCname at h
  rw [← Array.findSome?_toList] at h
  unfold Resolver.extractCnameRR
  rw [← Array.find?_toList, VeriDNS.Spec.Net.cnameRR, αSection_eq_filterMap]
  revert h hvalid
  generalize answer.toList = L
  induction L with
  | nil => intro h _; simp at h
  | cons b L' ih =>
    intro h hvalid
    have hvalid' : ∀ b ∈ L', ∃ rr,
        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
          ∧ αRR rr ≠ none := fun x hx => hvalid x (List.mem_cons_of_mem _ hx)
    rw [List.findSome?_cons] at h
    cases hpb : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
    | none =>
      obtain ⟨rr0, hpr0, -⟩ := hvalid b (by simp)
      exact absurd hpr0 (by rw [hpb]; simp)
    | some rr =>
      obtain ⟨rr', hpr', hαne⟩ := hvalid b (by simp)
      rw [hpb] at hpr'
      have hαne2 : αRR rr ≠ none := by rw [Option.some.inj hpr']; exact hαne
      obtain ⟨cn0, hcn0⟩ := Option.ne_none_iff_exists'.mp hαne2
      rw [hpb] at h
      simp only [List.filterMap_cons, αSecF_some hpb, hcn0]
      have hagree := cnamePred_agree hsq hsc hsv hpb hcn0
      by_cases h5 : (VeriDNS.Spec.RRParse.rrType (RR := VeriDNS.Spec.ResourceRecord) rr
          == (5 : BitVec 16)
          && VeriDNS.Impl.DomainName.nameEqCI
              (VeriDNS.Spec.RRParse.rrName (RR := VeriDNS.Spec.ResourceRecord) rr) sname) = true
      · simp only [h5, if_true] at h
        have hrdT : rr.rdata = target := Option.some.inj h
        have h5' : rr.type = (5 : BitVec 16) := eq_of_beq (Bool.and_eq_true _ _ |>.mp h5).1
        obtain ⟨tgt, hrdeq, hname⟩ := αRR_cname_target rr cn0 h5' hcn0
        refine ⟨b, rr, cn0, tgt, ?_, by simp, hpb, h5', hrdT, hcn0, ?_, hrdeq,
          by rw [← hrdT]; exact hname⟩
        · refine List.find?_cons_of_pos ?_
          simp only [hpb]
          exact h5
        · refine List.find?_cons_of_pos ?_
          show (cn0.rdata.rtype == RRType.cname && VeriDNS.Spec.Net.nameEq cn0.owner qn) = true
          rw [← hagree]; exact h5
      · rw [Bool.not_eq_true] at h5
        simp only [h5, Bool.false_eq_true, if_false] at h
        have hne : (cn0.rdata.rtype == RRType.cname
            && VeriDNS.Spec.Net.nameEq cn0.owner qn) = false := by
          rw [← hagree]; exact h5
        obtain ⟨cnBytes, rrCn, cn, tgt, hfind, hmem, hpr, hty, hrd, hα, hcnrr, hrdcn, hnm⟩ :=
          ih (by simpa using h) hvalid'
        refine ⟨cnBytes, rrCn, cn, tgt, ?_, List.mem_cons_of_mem _ hmem, hpr, hty, hrd, hα, ?_,
          hrdcn, hnm⟩
        · rw [List.find?_cons_of_neg]
          · exact hfind
          · simp only [hpb]
            intro h5eq
            exact Bool.noConfusion (h5eq.symm.trans h5)
        · rw [List.find?_cons_of_neg]
          · exact hcnrr
          · show ¬(cn0.rdata.rtype == RRType.cname && VeriDNS.Spec.Net.nameEq cn0.owner qn) = true
            simp [hne]

theorem question_from_decode {bytes : ByteArray} {resp0 respS respA : VeriDNS.Spec.Format}
    {qaR : VeriDNS.Spec.Question}
    (hdec : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some respS)
    (hAeq : respA = respS)
    (hqaR : respA.question[0]? = some qaR) :
    VeriDNS.Proof.Message.QuestionFromLabels qaR := by
  have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
    unfold Server.sanitizeTtlsCap at hsani
    exact (Option.some.inj hsani).symm
  have hqaR0 : resp0.question[0]? = some qaR := by
    rw [show resp0.question = respA.question from by rw [hAeq, hcapEq]; rfl]
    exact hqaR
  obtain ⟨-, -, -, -, hqs, -, -, -⟩ := VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec
  rw [Array.getElem?_eq_some_iff] at hqaR0
  obtain ⟨hlt, hget⟩ := hqaR0
  exact hget ▸ hqs ⟨0, hlt⟩

theorem answer_write_WriteRefines_echo (c : DnsCache) (resp : VeriDNS.Spec.Format)
    (qaR : VeriDNS.Spec.Question) (snameB : ByteArray) (qn : VeriDNS.Spec.Net.Name) (now : UInt32)
    (hqaR : resp.question[0]? = some qaR)
    (hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR)
    (hqaCI : VeriDNS.Impl.DomainName.nameEqCI qaR.qname snameB = true)
    (hsn : αName snameB = some qn)
    (htc : (resp.header.tc == 1) = false)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname resp) resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname resp) resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname resp) resp.answer), RRCanonMappable e)
    (ref : VeriDNS.Spec.Net.Response) (cm : VeriDNS.Spec.Net.Cache)
    (hansEq : αSection resp.answer = ref.answer)
    (haaEq : (resp.header.aa == 1) = ref.aa)
    (hmme : MatchMaxEquiv (αCache c) cm) :
    WriteRefines now.toNat
      (αCache (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.echoedQname resp) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) now))
      (cm.absorb now.toNat qn (ref.answerOwned qn)) := by
  have helim : (Resolver.echoedQname resp) = qaR.qname := by
    unfold Resolver.echoedQname
    rw [hqaR]
    rfl
  obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
  have hqnRq : VeriDNS.Spec.Net.nameEq qnR qn = true := by
    obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
    obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
    exact hne'
  rw [helim] at hval hno hcanmap ⊢
  have h0 := cname_write_WriteRefines_ref c resp qaR.qname qnR now hαR hcanR hvalR htc hwf hoe
    hval hno hcanmap ref cm hansEq haaEq hmme
  rw [VeriDNS.Spec.Net.absorb_answerOwned_congr cm now.toNat hqnRq ref] at h0
  exact h0

/-- Finding 019 twin of `answer_write_WriteRefines_echo` for the chase arm:
the impl chase-link write (`cnameRaws`) refines the model `cnameOwned`
absorb. -/
theorem cname_link_write_WriteRefines_echo (c : DnsCache) (resp : VeriDNS.Spec.Format)
    (qaR : VeriDNS.Spec.Question) (snameB : ByteArray) (qn : VeriDNS.Spec.Net.Name) (now : UInt32)
    (hqaR : resp.question[0]? = some qaR)
    (hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR)
    (hqaCI : VeriDNS.Impl.DomainName.nameEqCI qaR.qname snameB = true)
    (hsn : αName snameB = some qn)
    (htc : (resp.header.tc == 1) = false)
    (hwf : CacheWf c now)
    (hoe : VeriDNS.Proof.NameTree.OneExpiryPerKey c)
    (hval : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname resp) resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (αRR rr).isSome = true)
    (hno : ∀ b ∈ (VeriDNS.Impl.Cache.normRaws (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname resp) resp.answer)).toList,
        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat)
    (hcanmap : ∀ e ∈ VeriDNS.Impl.Cache.rrsOf (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.echoedQname resp) resp.answer), RRCanonMappable e)
    (ref : VeriDNS.Spec.Net.Response) (cm : VeriDNS.Spec.Net.Cache)
    (hansEq : αSection resp.answer = ref.answer)
    (haaEq : (resp.header.aa == 1) = ref.aa)
    (hmme : MatchMaxEquiv (αCache c) cm) :
    WriteRefines now.toNat
      (αCache (Resolver.cacheUnlessTruncated (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        c resp (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.echoedQname resp) resp.answer)
        (Resolver.credAnswer (resp.header.aa == 1)) now))
      (cm.absorb now.toNat qn (ref.cnameOwned qn)) := by
  have helim : (Resolver.echoedQname resp) = qaR.qname := by
    unfold Resolver.echoedQname
    rw [hqaR]
    rfl
  obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
  have hqnRq : VeriDNS.Spec.Net.nameEq qnR qn = true := by
    obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
    obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
    exact hne'
  rw [helim] at hval hno hcanmap ⊢
  have h0 := chasedCname_write_WriteRefines_ref c resp qaR.qname qnR now hαR hcanR hvalR htc hwf hoe
    hval hno hcanmap ref cm hansEq haaEq hmme
  rw [VeriDNS.Spec.Net.absorb_cnameOwned_congr cm now.toNat hqnRq ref] at h0
  exact h0

theorem cnameToChase_none_model {respA : VeriDNS.Spec.Format} {qaR : VeriDNS.Spec.Question}
    {snameB : ByteArray} {qn : VeriDNS.Spec.Net.Name}
    (hcc : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none)
    (hansF : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false)
    (hqaR : respA.question[0]? = some qaR)
    (hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR)
    (hqaCI : VeriDNS.Impl.DomainName.nameEqCI qaR.qname snameB = true)
    (hsn : αName snameB = some qn) :
    VeriDNS.Spec.Net.cnameRR qn (αSection respA.answer) = none := by
  have hext : Resolver.extractCname (RR := VeriDNS.Spec.ResourceRecord) qaR.qname respA.answer
      = none := by
    simp only [Resolver.cnameToChase, hansF, Bool.false_eq_true, if_false, hqaR] at hcc
    exact hcc
  obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
  have hqnRq : VeriDNS.Spec.Net.nameEq qnR qn = true := by
    obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
    obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
    exact hne'
  rw [← VeriDNS.Spec.Net.cnameRR_congr hqnRq]
  exact cnameRR_none_of_extractCname_none hαR hcanR hvalR hext

theorem αSection_map_rrBytes (rrs : Array VeriDNS.Spec.ResourceRecord)
    (h : ∀ rr ∈ rrs.toList, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr) = some rr) :
    αSection (rrs.map (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)))
      = rrs.toList.filterMap αRR := by
  rw [αSection_eq_filterMap, Array.toList_map, List.filterMap_map]
  revert h
  generalize rrs.toList = L
  intro h
  induction L with
  | nil => rfl
  | cons a L' ih =>
    simp only [List.filterMap_cons, Function.comp_apply, αSecF_some (h a (by simp))]
    rw [ih (fun rr hr => h rr (List.mem_cons_of_mem _ hr))]

theorem stepAnalyzeResponse_cname_truncated
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hresp : s.lastResponse = some resp)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = true) :
    Resolver.stepAnalyzeResponse s = .answer (Resolver.finalizeAnswer s resp) s := by
  simp only [Resolver.stepAnalyzeResponse, hresp, hcname, htc, if_true]

theorem resume_cname_truncated
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (resp : VeriDNS.Spec.Format) (target : ByteArray)
    (hstep : state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = some target)
    (htc : (resp.header.tc == 1) = true) :
    Resolver.resume state resp 64
      = .ok (.done (Resolver.finalizeAnswer
          { state with
            lastResponse := some resp
            currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse } resp)
          { state with
            lastResponse := some resp
            currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse }) := by
  have hcname_step := stepAnalyzeResponse_cname_truncated
    { state with
      lastResponse := some resp
      currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse } resp target rfl hcn htc
  rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hstep, Resolver.stepSendQueries]
  rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
  simp only [Resolver.step, hcname_step]

theorem afterResume_cname_truncated
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA : VeriDNS.Spec.Format) (target : ByteArray)
    (hstep : state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = true) :
    ∃ st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Server.afterResume state entryName respA
        = .finished (.ok (Resolver.finalizeAnswer st respA))
            (Server.boundStateCache
              (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA)
              st).resources.cache
      ∧ st.cnameChain = state.cnameChain ∧ st.lastQuery = state.lastQuery
      ∧ st.resources.cache = state.resources.cache ∧ st.now = state.now := by
  obtain ⟨sl, hsD⟩ : ∃ sl, Server.dropIfBizarre state entryName respA
      = { state with resources := { state.resources with slist := sl } } := by
    by_cases hbz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = true
    · exact ⟨_, by unfold Server.dropIfBizarre; rw [if_pos hbz]⟩
    · exact ⟨state.resources.slist, by unfold Server.dropIfBizarre; rw [if_neg hbz]⟩
  refine ⟨{ state with
      resources := { state.resources with slist := sl }
      lastResponse := some respA
      currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse }, ?_, rfl, rfl, rfl, rfl⟩
  unfold Server.afterResume
  rw [hsD, resume_cname_truncated _ respA target (by exact hstep) hcn htc]

private def StepNowOk (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
    VeriDNS.Spec.ResourceRecord) :
    Resolver.StepResult DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
      → Prop
  | .answer _ stF => stF.now = s.now
  | .goto _ s' => s'.now = s.now
  | .needsIO s' => s'.now = s.now
  | .error _ => True

private theorem step_nowOk
    (s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord) :
    StepNowOk s (Resolver.step s) := by
  unfold Resolver.step
  split
  ·
    unfold Resolver.stepCheckLocal
    repeat' split
    all_goals first | rfl | trivial
  ·
    unfold Resolver.stepFindServers
    dsimp only [letFun]
    repeat' split
    all_goals rfl
  ·
    unfold Resolver.stepSendQueries
    repeat' split
    all_goals rfl
  ·
    unfold Resolver.stepAnalyzeResponse
    dsimp only [letFun]
    repeat' split
    all_goals first | rfl | trivial

private theorem loop_done_now (n : Nat) :
    ∀ (X st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
        VeriDNS.Spec.ResourceRecord) (out : VeriDNS.Spec.Format),
      Resolver.resolve.loop X n = .ok (.done out st) → st.now = X.now := by
  induction n with
  | zero =>
    intro X st out h
    rw [Resolver.resolve.loop] at h
    exact absurd h (by simp)
  | succ n ih =>
    intro X st out h
    rw [Resolver.resolve.loop] at h
    have hok := step_nowOk X
    split at h
    · rename_i r stF heq
      rw [heq] at hok
      injection h with h'
      injection h' with h1 h2
      subst h2
      exact hok
    · rename_i ns s' heq
      rw [heq] at hok
      exact (ih _ _ _ h).trans hok
    · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem resume_done_now
    {state st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry
      VeriDNS.Spec.ResourceRecord} {resp out : VeriDNS.Spec.Format} {fuel : Nat}
    (h : Resolver.resume state resp fuel = .ok (.done out st)) : st.now = state.now :=
  loop_done_now fuel { state with lastResponse := some resp } st out h

theorem afterResume_cname_ok_inv
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA qF : VeriDNS.Spec.Format) (target : ByteArray)
    (qu : VeriDNS.Spec.Question) (out : VeriDNS.Spec.Format)
    (hstep : state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (htc : (respA.header.tc == 1) = false)
    (hq : state.lastQuery = some qF) (hqu : qF.question[0]? = some qu)
    {cout : DnsCache}
    (hAR : Server.afterResume state entryName respA = .finished (.ok out) cout) :
    ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false
    ∧ ((∃ (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
          (st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
        Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now)
          qu.qtype qu.qclass state.now 8 target
          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
          = .answerHit sname chain rrs
        ∧ out = Resolver.finalizeAnswer st (Resolver.cacheResponse qF rrs) ∧ st.cnameChain = chain
        ∧ cout = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
            (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) state.now)
      ∨ (∃ (rc : VeriDNS.Spec.Rcode) (soaAuth : Array VeriDNS.Spec.ResourceRecord)
          (chain : Array ByteArray)
          (st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord),
        Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now)
          qu.qtype qu.qclass state.now 8 target
          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
          = .negative rc soaAuth chain
        ∧ out = Resolver.finalizeAnswer st (Resolver.negativeResponse qF rc soaAuth)
        ∧ st.cnameChain = chain
        ∧ cout = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
            (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) state.now)) := by
  obtain ⟨sl, hsD⟩ : ∃ sl, Server.dropIfBizarre state entryName respA
      = { state with resources := { state.resources with slist := sl } } := by
    by_cases hbz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = true
    · exact ⟨_, by unfold Server.dropIfBizarre; rw [if_pos hbz]⟩
    · exact ⟨state.resources.slist, by unfold Server.dropIfBizarre; rw [if_neg hbz]⟩
  by_cases hrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
      ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
      state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true
  · exfalso
    have hres := resume_cname_revisit
      { state with resources := { state.resources with slist := sl } } respA target hstep hcn htc hrev
    have hARv : Server.afterResume state entryName respA
        = .finished (.error "cname loop detected") state.resources.cache := by
      unfold Server.afterResume
      rw [hsD, hres]
    rw [hARv] at hAR
    exact absurd hAR (by simp)
  · rw [Bool.not_eq_true] at hrev
    refine ⟨hrev, ?_⟩
    cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target
        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) with
    | answerHit sname chain rrs =>
      obtain ⟨st, hrs, hcc, hca⟩ := resume_cname_answerHit
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        sname chain rrs hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .finished (.ok (Resolver.finalizeAnswer st (Resolver.cacheResponse qF rrs)))
              (Server.boundStateCache
                (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA)
                st).resources.cache := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      injection hAR with h1 hco
      injection h1 with h2
      refine Or.inl ⟨sname, chain, rrs, st, rfl, h2.symm, hcc, ?_⟩
      rw [← hco]
      show st.resources.cache.boundLru
        (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) st.now = _
      rw [show st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now from by exact hca,
        show st.now = state.now from by have hnw := resume_done_now hrs; exact hnw]
    | negative rc soaAuth chain =>
      obtain ⟨st, hrs, hcc, hca⟩ := resume_cname_negHit
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        rc soaAuth chain hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .finished (.ok (Resolver.finalizeAnswer st (Resolver.negativeResponse qF rc soaAuth)))
              (Server.boundStateCache
                (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA)
                st).resources.cache := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      injection hAR with h1 hco
      injection h1 with h2
      refine Or.inr ⟨rc, soaAuth, chain, st, rfl, h2.symm, hcc, ?_⟩
      rw [← hco]
      show st.resources.cache.boundLru
        (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) st.now = _
      rw [show st.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now from by exact hca,
        show st.now = state.now from by have hnw := resume_done_now hrs; exact hnw]
    | miss sname' chain =>
      obtain ⟨st', hrs⟩ := resume_cname_miss
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        sname' chain hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .continue (Server.boundStateCache
              (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) st') := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      exact Server.IoStep.noConfusion hAR
    | abort =>
      have hrs := resume_cname_abort
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .finished (.error "cname chain too long") state.resources.cache := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      exact absurd hAR (by simp)



theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have h' : ByteArray.beq a b = true := h
  unfold ByteArray.beq at h'
  exact ByteArray.ext (eq_of_beq h')

theorem wireFormatToLabelsGo_labels_valid (w : ByteArray) (pos : Nat)
    (ls : List ByteArray)
    (hw : DomainName.wireFormatToLabelsGo w pos = .ok ls) :
    ∀ x ∈ ls, 0 < x.size ∧ x.size ≤ 63 := by
  unfold DomainName.wireFormatToLabelsGo at hw
  by_cases hpos : pos < w.data.size
  · rw [dif_pos hpos] at hw
    dsimp only [] at hw
    split at hw
    · cases hw
      intro x hx
      simp at hx
    · next hzero =>
      split at hw
      · exact absurd hw (by simp)
      · next hbig =>
        split at hw
        · next hroom =>
          split at hw
          · next rest hrec =>
            cases hw
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · have hds : w.data.size = w.size := rfl
              constructor
              · rw [ByteArray.size_extract]
                omega
              · rw [ByteArray.size_extract]
                omega
            · exact wireFormatToLabelsGo_labels_valid w _ rest hrec x hx'
          · exact absurd hw (by simp)
        · exact absurd hw (by simp)
  · rw [dif_neg hpos] at hw
    cases hw
    intro x hx
    simp at hx
termination_by w.size - pos
decreasing_by omega

theorem αName_labels_valid {b : ByteArray} {nm : VeriDNS.Spec.Net.Name}
    (h : αName b = some nm) : ∀ x ∈ nm, 0 < x.size ∧ x.size ≤ 63 := by
  unfold αName at h
  split at h
  · next labels hlab =>
    have hnm : labels.toList = nm := Option.some.inj h
    unfold DomainName.wireFormatToLabels at hlab
    split at hlab
    · next ls hgo =>
      have harr : ls.toArray = labels := by injection hlab
      intro x hx
      refine wireFormatToLabelsGo_labels_valid b 0 ls hgo x ?_
      rw [← hnm, ← harr] at hx
      simpa using hx
    · exact absurd hlab (by simp)
  · exact absurd h (by simp)

def GluelessProv (slist : DnsSList) : Prop :=
  ∀ nsName ∈ slist.addressTargets.toList,
    ∃ nsQ, αName nsName = some nsQ
      ∧ nsName = DomainName.labelsToWireFormatGo nsQ
      ∧ nsQ.length ≤ 127

theorem GluelessProv_of_subset {s s' : DnsSList}
    (hsub : ∀ n ∈ s'.addressTargets.toList, n ∈ s.addressTargets.toList)
    (h : GluelessProv s) : GluelessProv s' :=
  fun n hn => h n (hsub n hn)

theorem addressTargets_markQueried (s : DnsSList) (nm : ByteArray) :
    (s.markQueried nm).addressTargets = s.addressTargets := by
  unfold DnsSList.markQueried DnsSList.addressTargets
  rw [← Array.toList_inj]
  rw [Array.toList_filterMap, Array.toList_filterMap, Array.toList_map, List.filterMap_map]
  congr 1
  funext e
  dsimp only [Function.comp]
  by_cases hb : (e.name == nm) = true
  · rw [if_pos hb]
  · rw [if_neg hb]

theorem addressTargets_addAddress_subset (s : DnsSList) (nm : ByteArray) (a : BitVec 32) :
    ∀ n ∈ (s.addAddress nm a).addressTargets.toList, n ∈ s.addressTargets.toList := by
  intro n hn
  unfold DnsSList.addAddress DnsSList.addressTargets at hn
  unfold DnsSList.addressTargets
  rw [Array.toList_filterMap, Array.toList_map, List.filterMap_map] at hn
  rw [Array.toList_filterMap]
  rcases List.mem_filterMap.mp hn with ⟨e, he, hfe⟩
  dsimp only [Function.comp] at hfe
  refine List.mem_filterMap.mpr ⟨e, he, ?_⟩
  by_cases hb : (e.name == nm) = true
  · rw [if_pos hb] at hfe
    exact absurd hfe (by simp)
  · rw [if_neg hb] at hfe
    exact hfe

theorem addressTargets_removeServer_subset (s : DnsSList) (nm : ByteArray) :
    ∀ n ∈ (s.removeServer nm).addressTargets.toList, n ∈ s.addressTargets.toList := by
  intro n hn
  unfold DnsSList.removeServer DnsSList.addressTargets at hn
  unfold DnsSList.addressTargets
  rw [Array.toList_filterMap, Array.toList_filter] at hn
  rw [Array.toList_filterMap]
  rcases List.mem_filterMap.mp hn with ⟨e, he, hfe⟩
  exact List.mem_filterMap.mpr ⟨e, (List.mem_filter.mp he).1, hfe⟩

theorem addressTargets_fromNsWithGlueAll_subset (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) :
    ∀ n ∈ (DnsSList.fromNsWithGlueAll names glue mc).addressTargets.toList,
      n ∈ names.toList := by
  intro n hn
  unfold DnsSList.fromNsWithGlueAll DnsSList.addressTargets at hn
  rw [Array.toList_filterMap, Array.toList_flatMap] at hn
  rcases List.mem_filterMap.mp hn with ⟨e, he, hfe⟩
  rcases List.mem_flatMap.mp he with ⟨nm, hnm, hee⟩
  dsimp only [] at hee
  split at hee
  · have he1 : e = ⟨nm, none, 0⟩ := by simpa using hee
    subst he1
    have : n = nm := by simpa using hfe.symm
    subst this
    exact hnm
  · rw [Array.toList_map] at hee
    rcases List.mem_map.mp hee with ⟨ga, _, he1⟩
    subst he1
    exact absurd hfe (by simp)

theorem addressTargets_copyNames (names : Array ByteArray) (mc : Nat) :
    (VeriDNS.Spec.SlistFromNameSpec.copyNames (S := DnsSList)
      (NS := VeriDNS.Spec.SlistEntry) names mc).addressTargets = names := by
  show ({ servers := names.map fun n => ⟨n, none, 0⟩,
          zone := ByteArray.empty, matchCount := mc } : DnsSList).addressTargets = names
  unfold DnsSList.addressTargets
  rw [← Array.toList_inj]
  rw [Array.toList_filterMap, Array.toList_map, List.filterMap_map]
  show names.toList.filterMap (fun n => some n) = names.toList
  simp

theorem GluelessProv_default : GluelessProv (default : DnsSList) := by
  intro n hn
  have h : (default : DnsSList).addressTargets = #[] := rfl
  rw [h] at hn
  simp at hn

theorem GluelessProv_markQueried {s : DnsSList} (nm : ByteArray) (h : GluelessProv s) :
    GluelessProv (s.markQueried nm) := by
  intro n hn
  rw [addressTargets_markQueried] at hn
  exact h n hn

theorem GluelessProv_addAddress {s : DnsSList} (nm : ByteArray) (a : BitVec 32)
    (h : GluelessProv s) : GluelessProv (s.addAddress nm a) :=
  GluelessProv_of_subset (addressTargets_addAddress_subset s nm a) h

theorem GluelessProv_removeServer {s : DnsSList} (nm : ByteArray) (h : GluelessProv s) :
    GluelessProv (s.removeServer nm) :=
  GluelessProv_of_subset (addressTargets_removeServer_subset s nm) h

theorem GluelessProv_fromNsWithGlueAll_of_canonical (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat)
    (h : ∀ n ∈ names.toList, ∃ nsQ, αName n = some nsQ
        ∧ n = DomainName.labelsToWireFormatGo nsQ ∧ nsQ.length ≤ 127) :
    GluelessProv (DnsSList.fromNsWithGlueAll names glue mc) :=
  fun n hn => h n (addressTargets_fromNsWithGlueAll_subset names glue mc n hn)

/-- Every SBELT entry carries an explicit address, so an SBELT has no
    address-less (glueless) targets at all. -/
theorem addressTargets_mkSbelt (entries : Array (ByteArray × BitVec 32)) :
    (DnsSList.mkSbelt entries).addressTargets = #[] := by
  unfold DnsSList.mkSbelt DnsSList.addressTargets
  rw [← Array.toList_inj]
  rw [Array.toList_filterMap, Array.toList_map, List.filterMap_map]
  simp [Function.comp]

/-- `GluelessProv` holds vacuously of any SBELT built by `DnsSList.mkSbelt` —
    in particular of the production root-hint SBELT in `main`
    (`DnsSList.mkSbelt rootServers`, VeriDNS/Main.lean). -/
theorem GluelessProv_mkSbelt (entries : Array (ByteArray × BitVec 32)) :
    GluelessProv (DnsSList.mkSbelt entries) := by
  intro n hn
  rw [addressTargets_mkSbelt] at hn
  simp at hn

theorem extractNsNames_canonical (authority : Array ByteArray)
    (hcanon : ∀ b ∈ authority.toList, VeriDNS.Proof.Message.CanonicalRR b) :
    ∀ n ∈ (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) authority).toList,
      ∃ nsQ, αName n = some nsQ ∧ n = DomainName.labelsToWireFormatGo nsQ ∧ nsQ.length ≤ 127 := by
  intro n hn
  unfold Resolver.extractNsNames at hn
  rw [Array.toList_filterMap, List.mem_filterMap] at hn
  obtain ⟨b, hb, hfb⟩ := hn
  cases hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b with
  | none => rw [hp] at hfb; exact absurd hfb (by simp)
  | some rr =>
    rw [hp] at hfb
    dsimp only [] at hfb
    split at hfb
    · next htype =>
      rw [Option.some.injEq] at hfb
      subst hfb
      have ht2 : rr.type = 2 := by
        have hb2 : (rr.type == BitVec.ofNat 16 2) = true := htype
        simpa using hb2
      obtain ⟨na, h1, h2, -, h4⟩ := canonicalRR_nsRdata_canonical (hcanon b hb) hp ht2
      exact ⟨na, h1, h2, h4⟩
    · exact absurd hfb (by simp)

theorem extractNsNames_ownerRaws_canonical (authority : Array ByteArray)
    (hcanon : ∀ b ∈ authority.toList, VeriDNS.Proof.Message.CanonicalRR b) :
    ∀ n ∈ (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) authority) authority)).toList,
      ∃ nsQ, αName n = some nsQ ∧ n = DomainName.labelsToWireFormatGo nsQ ∧ nsQ.length ≤ 127 := by
  apply extractNsNames_canonical
  intro b hb
  exact hcanon b (Resolver.ownerRaws_subset (RR := VeriDNS.Spec.ResourceRecord) _ authority hb)

theorem walkNs_names_canonical (cache : DnsCache) (now : UInt32) (hcanon : CacheNsCanon cache) :
    ∀ (fuel : Nat) (sname : ByteArray) (nsNames : Array ByteArray) (mc : Nat),
      Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord) sname cache
        (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now fuel = some (nsNames, mc) →
      ∀ n ∈ nsNames.toList, ∃ nsQ, αName n = some nsQ
        ∧ n = DomainName.labelsToWireFormatGo nsQ ∧ nsQ.length ≤ 127 := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname nsNames mc h
    rw [Resolver.stepFindServers.walkNs] at h
    exact absurd h (by simp)
  | succ f ih =>
    intro sname nsNames mc h
    by_cases he : (VeriDNS.Spec.CacheSpec.lookupTopCred cache sname (BitVec.ofNat 16 2)
        (BitVec.ofNat 16 1) now : Array VeriDNS.Spec.ResourceRecord).isEmpty = true
    · cases hp : DomainName.parentDomainWire sname with
      | none =>
        rw [Resolver.stepFindServers.walkNs] at h
        simp only [he, if_true, hp] at h
        exact absurd h (by simp)
      | some parent =>
        rw [walkNs_step sname cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now f parent he hp] at h
        exact ih parent nsNames mc h
    · rw [Bool.not_eq_true] at he
      rw [walkNs_base sname cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now f he] at h
      rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hns, -⟩ := h
      intro n hn
      obtain ⟨qn, h1, h2, -, h4⟩ := hhost_of_rdata_canonical cache sname now
        (hrdcanon_of_CacheNsCanon cache sname now hcanon) n (by rw [← hns] at hn; exact hn)
      exact ⟨qn, h1, h2, h4⟩

theorem gluelessNs_anchor_witness (nsQ : VeriDNS.Spec.Net.Name) (now : VeriDNS.Spec.Net.Time)
    (qn : VeriDNS.Spec.Net.Name) :
    ∃ zone cprov, VeriDNS.Spec.Net.isAncestor zone qn = true
      ∧ nsQ ∈ VeriDNS.Spec.Net.Cache.nsHostsAt cprov now zone := by
  refine ⟨[], { pos := [⟨⟨[], 1, .ns nsQ, RRClass.in⟩, now, .authority⟩], neg := [] }, ?_, ?_⟩
  · unfold VeriDNS.Spec.Net.isAncestor
    simp [VeriDNS.Spec.Net.nameEq, List.drop_length]
  · have h : VeriDNS.Spec.Net.Cache.nsHostsAt
        { pos := [⟨⟨[], 1, .ns nsQ, RRClass.in⟩, now, .authority⟩], neg := [] } now []
        = [nsQ] := by
      unfold VeriDNS.Spec.Net.Cache.nsHostsAt VeriDNS.Spec.Net.Cache.topServed
        VeriDNS.Spec.Net.Cache.matching
      simp (config := { decide := true }) [VeriDNS.Spec.Net.CacheRR.fresh,
        VeriDNS.Spec.Net.CacheRR.sameKey, VeriDNS.Spec.Net.nameEq,
        VeriDNS.Spec.Net.QType.covers, VeriDNS.Spec.Net.RR.rtype,
        VeriDNS.Spec.Net.RData.rtype, VeriDNS.Spec.Net.Cred.rank, Nat.blt,
        Nat.ble_self_eq_true, List.filter_nil]
    rw [h]
    exact List.mem_singleton.mpr rfl

theorem localAnswer_miss_ident_or_fresh (cache : DnsCache) (qt qc : BitVec 16) (now32 : UInt32) :
    ∀ (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
      (sname' : ByteArray) (chain' : Array ByteArray),
      Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache qt qc now32 fuel sname chain visited = .miss sname' chain' →
      (sname' = sname ∧ chain' = chain)
        ∨ (∀ v ∈ visited.toList, VeriDNS.Impl.DomainName.nameEqCI v sname' = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname chain visited sname' chain' h
    simp only [Resolver.localAnswer] at h
    exact absurd h (by simp)
  | succ fuel ih =>
    intro sname chain visited sname' chain' h
    simp only [Resolver.localAnswer] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · split at h
        · injection h with h1 h2
          exact Or.inl ⟨h1.symm, h2.symm⟩
        · split at h
          · rename_i crr hcrr
            split at h
            · injection h with h1 h2
              exact Or.inl ⟨h1.symm, h2.symm⟩
            · rename_i hnrev
              rw [Bool.not_eq_true] at hnrev
              rcases ih _ _ _ sname' chain' h with ⟨h1, -⟩ | hfr
              · refine Or.inr ?_
                intro v hv
                rw [h1]
                simp only [Array.any_eq_false'] at hnrev
                simpa using hnrev v (Array.mem_def.mpr hv)
              · refine Or.inr ?_
                intro v hv
                exact hfr v (by rw [Array.toList_push]; exact List.mem_append_left _ hv)
          · injection h with h1 h2
            exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact absurd h (by simp)

theorem loop_checkAnswer_miss_struct
    (X : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (qF : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (sname' : ByteArray) (chain : Array ByteArray)
    (hcs : X.currentStep = VeriDNS.Spec.AlgorithmStep.checkAnswer)
    (hq : X.lastQuery = some qF) (hqu : qF.question[0]? = some qu)
    (hmiss : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        X.resources.cache qu.qtype qu.qclass X.now 8 X.resources.sname X.cnameChain
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname X.cnameChain)
        = .miss sname' chain)
    (hident : sname' = X.resources.sname → chain = X.cnameChain)
    (hlr : X.lastResponse = none) (n : Nat) :
    ∃ st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord,
      Resolver.resolve.loop X (n + 3) = .ok (.paused st)
      ∧ st.resources.cache = X.resources.cache
      ∧ st.resources.sname = sname'
      ∧ st.now = X.now
      ∧ st.cnameChain = chain
      ∧ st.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries
      ∧ st.lastQuery = X.lastQuery
      ∧ st.resources.sbelt = X.resources.sbelt
      ∧ ( st.resources.slist = X.resources.slist
          ∨ st.resources.slist = default
          ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
                sname' X.resources.cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) X.now 128
                = some (nsNames, mc)
              ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList)
                  (NS := VeriDNS.Spec.SlistEntry) nsNames
                  (reGlue (RR := VeriDNS.Spec.ResourceRecord) X.resources.cache X.now nsNames) mc)
          ∨ st.resources.slist = X.resources.sbelt ) := by
  by_cases hsn : (sname' == X.resources.sname) = true
  · have hsEq : sname' = X.resources.sname := byteArray_eq_of_beq hsn
    have hcEq : chain = X.cnameChain := hident hsEq
    have hscl : Resolver.stepCheckLocal X = .goto .findServers X := by
      simp only [Resolver.stepCheckLocal, hq, hqu, hmiss]
      rw [if_pos hsn]
    rw [show n + 3 = (n + 2) + 1 from rfl, Resolver.resolve.loop]
    simp only [Resolver.step, hcs, hscl]
    obtain ⟨st, hloop, hc, hsna, hnw, hcc, hcs2, hlq, hsb, hdisj⟩ :=
      loop_findServers_paused_cases
        { X with currentStep := VeriDNS.Spec.AlgorithmStep.findServers } rfl (by exact hlr) n
    refine ⟨st, hloop, by exact hc,
      ((by exact hsna : st.resources.sname = X.resources.sname).trans hsEq.symm),
      by exact hnw, ((by exact hcc : st.cnameChain = X.cnameChain).trans hcEq.symm),
      hcs2, by exact hlq, by exact hsb, ?_⟩
    rcases hdisj with h | ⟨nsNames, mc, hw, -, heq⟩ | ⟨h, -⟩
    · exact Or.inl (by exact h)
    · exact Or.inr (Or.inr (Or.inl ⟨nsNames, mc, by rw [hsEq]; exact hw, by exact heq⟩))
    · exact Or.inr (Or.inr (Or.inr (by exact h)))
  · have hscl : Resolver.stepCheckLocal X = .goto .findServers
        { X with
          resources := { X.resources with sname := sname', slist := default },
          cnameChain := chain } := by
      simp only [Resolver.stepCheckLocal, hq, hqu, hmiss]
      rw [if_neg hsn]
    rw [show n + 3 = (n + 2) + 1 from rfl, Resolver.resolve.loop]
    simp only [Resolver.step, hcs, hscl]
    obtain ⟨st, hloop, hc, hsna, hnw, hcc, hcs2, hlq, hsb, hdisj⟩ :=
      loop_findServers_paused_cases
        ({ X with
           resources := { X.resources with sname := sname', slist := default },
           cnameChain := chain,
           currentStep := VeriDNS.Spec.AlgorithmStep.findServers } :
          Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
        rfl (by exact hlr) n
    refine ⟨st, hloop, by exact hc, by exact hsna, by exact hnw, by exact hcc, hcs2,
      by exact hlq, by exact hsb, ?_⟩
    rcases hdisj with h | ⟨nsNames, mc, hw, -, heq⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inl (by exact h))
    · exact Or.inr (Or.inr (Or.inl ⟨nsNames, mc, by exact hw, by exact heq⟩))
    · exact Or.inr (Or.inr (Or.inr (by exact h)))

theorem afterResume_cname_continue_inv
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (entryName : ByteArray) (respA : VeriDNS.Spec.Format) (target : ByteArray)
    (qF : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (state'' : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (hstep : state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries)
    (hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = some target)
    (hq : state.lastQuery = some qF) (hqu : qF.question[0]? = some qu)
    (htc : (respA.header.tc == 1) = false)
    (hTvis : ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)).toList,
        VeriDNS.Impl.DomainName.nameEqCI b target = true)
    (hAR : Server.afterResume state entryName respA = .continue state'') :
    ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
        ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false
    ∧ ∃ (sname' : ByteArray) (chain' : Array ByteArray),
        Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now)
          qu.qtype qu.qclass state.now 8 target
          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
          = .miss sname' chain'
        ∧ state''.resources.cache = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache respA
            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
            (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
            (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) state.now
        ∧ state''.resources.sname = sname'
        ∧ state''.now = state.now
        ∧ state''.cnameChain = chain'
        ∧ state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries
        ∧ state''.lastQuery = state.lastQuery
        ∧ state''.resources.sbelt = state.resources.sbelt
        ∧ ( state''.resources.slist = default
            ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
                  sname'
                  (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                    state.resources.cache respA
                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                      (Resolver.echoedQname respA) respA.answer)
                    (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                  (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) state.now 128 = some (nsNames, mc)
                ∧ state''.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses
                    (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry) nsNames
                    (reGlue (RR := VeriDNS.Spec.ResourceRecord)
                      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                        state.resources.cache respA
                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                          (Resolver.echoedQname respA) respA.answer)
                        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                      state.now nsNames) mc)
            ∨ state''.resources.slist = state.resources.sbelt ) := by
  obtain ⟨sl, hsD⟩ : ∃ sl, Server.dropIfBizarre state entryName respA
      = { state with resources := { state.resources with slist := sl } } := by
    by_cases hbz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
        || !Resolver.classifiableB respA) = true
    · exact ⟨_, by unfold Server.dropIfBizarre; rw [if_pos hbz]⟩
    · exact ⟨state.resources.slist, by unfold Server.dropIfBizarre; rw [if_neg hbz]⟩
  by_cases hrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
      ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
      state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = true
  · exfalso
    have hres := resume_cname_revisit
      { state with resources := { state.resources with slist := sl } } respA target hstep hcn htc hrev
    have hARv : Server.afterResume state entryName respA
        = .finished (.error "cname loop detected") state.resources.cache := by
      unfold Server.afterResume
      rw [hsD, hres]
    rw [hARv] at hAR
    exact Server.IoStep.noConfusion hAR
  · rw [Bool.not_eq_true] at hrev
    refine ⟨hrev, ?_⟩
    cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
          (Resolver.credAnswer (respA.header.aa == 1)) state.now)
        qu.qtype qu.qclass state.now 8 target
        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)) with
    | answerHit snameH chainH rrs =>
      exfalso
      obtain ⟨st, hrs, -, -⟩ := resume_cname_answerHit
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        snameH chainH rrs hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .finished (.ok (Resolver.finalizeAnswer st (Resolver.cacheResponse qF rrs)))
              (Server.boundStateCache
                (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA)
                st).resources.cache := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      exact Server.IoStep.noConfusion hAR
    | negative rc soaAuth chainN =>
      exfalso
      obtain ⟨st, hrs, -, -⟩ := resume_cname_negHit
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        rc soaAuth chainN hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .finished (.ok (Resolver.finalizeAnswer st (Resolver.negativeResponse qF rc soaAuth)))
              (Server.boundStateCache
                (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA)
                st).resources.cache := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      exact Server.IoStep.noConfusion hAR
    | abort =>
      exfalso
      have hrs := resume_cname_abort
        { state with resources := { state.resources with slist := sl } } respA target qF qu
        hstep hcn htc hrev hq hqu hla
      have hARv : Server.afterResume state entryName respA
          = .finished (.error "cname chain too long") state.resources.cache := by
        unfold Server.afterResume
        rw [hsD, hrs]
      rw [hARv] at hAR
      exact Server.IoStep.noConfusion hAR
    | miss sname' chain' =>
      have hcname_step := stepAnalyzeResponse_cname
        ({ state with
           resources := { state.resources with slist := sl },
           lastResponse := some respA,
           currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse } :
          Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
        respA target rfl hcn htc hrev
      obtain ⟨stP, hloopP, hPcache, hPsname, hPnow, hPchain, hPstep, hPlq, hPsbelt, hPdisj⟩ :=
        loop_checkAnswer_miss_struct
          { state with
            resources := { state.resources with
              sname := target,
              slist := default,
              cache := Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                (Resolver.credAnswer (respA.header.aa == 1)) state.now },
            currentStep := VeriDNS.Spec.AlgorithmStep.checkAnswer,
            lastResponse := none,
            cnameChain := Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA }
          qF qu sname' chain' rfl (by exact hq) hqu (by exact hla)
          (by
            intro hsEq
            rcases localAnswer_miss_ident_or_fresh
              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                (Resolver.credAnswer (respA.header.aa == 1)) state.now)
              qu.qtype qu.qclass state.now 8 target
              (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
              (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname
                (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
              sname' chain' hla with ⟨-, h2⟩ | hfr
            · exact h2
            · exfalso
              obtain ⟨b, hb, hci⟩ := hTvis
              have hfalse := hfr b hb
              rw [show sname' = target from hsEq] at hfalse
              rw [hci] at hfalse
              exact absurd hfalse (by simp))
          rfl 59
      have hpause : Resolver.resume { state with resources := { state.resources with slist := sl } } respA 64
          = .ok (.paused stP) := by
        rw [Resolver.resume, show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop]
        simp only [Resolver.step, hstep, Resolver.stepSendQueries]
        rw [show (63 : Nat) = 62 + 1 from rfl, Resolver.resolve.loop]
        simp only [Resolver.step, hcname_step]
        rw [show (62 : Nat) = 59 + 3 from rfl]
        exact hloopP
      have hARv : Server.afterResume state entryName respA
          = .continue (Server.boundStateCache
              (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) stP) := by
        unfold Server.afterResume
        rw [hsD, hpause]
      rw [hARv] at hAR
      have hst2 : Server.boundStateCache
          (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) stP
          = state'' := Server.IoStep.continue.inj hAR
      refine ⟨sname', chain', rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hst2]
        show stP.resources.cache.boundLru
          (Server.roundTouches (Server.dropIfBizarre state entryName respA) respA) stP.now = _
        rw [show stP.resources.cache = Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
              state.resources.cache respA
              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
              (Resolver.credAnswer (respA.header.aa == 1)) state.now from by exact hPcache,
          show stP.now = state.now from by exact hPnow]
      · rw [← hst2]; exact hPsname
      · rw [← hst2]; exact hPnow
      · rw [← hst2]; exact hPchain
      · rw [← hst2]; exact hPstep
      · rw [← hst2]; exact hPlq
      · rw [← hst2]; exact hPsbelt
      · rw [← hst2]
        rcases hPdisj with h | h | ⟨nsNames, mc, hw, heq⟩ | h
        · exact Or.inl (by exact h)
        · exact Or.inl (by exact h)
        · exact Or.inr (Or.inl ⟨nsNames, mc, by exact hw, by exact heq⟩)
        · exact Or.inr (Or.inr (by exact h))


theorem αClass_in_one {qc : BitVec 16} (h : αClass qc = some RRClass.in) :
    qc = (1 : BitVec 16) := by
  unfold αClass at h
  split at h
  · next heq => exact BitVec.eq_of_toNat_eq (by rw [heq]; rfl)
  · next heq => exact absurd (Option.some.inj h) (by decide)
  · next heq => exact absurd (Option.some.inj h) (by decide)
  · next heq => exact absurd (Option.some.inj h) (by decide)
  · exact absurd h (by simp)

theorem mkAddressQuery_question (nsName : ByteArray) :
    (Server.mkAddressQuery nsName).question[0]?
      = some ⟨nsName, (1 : BitVec 16), (1 : BitVec 16)⟩ := rfl

theorem ioResumeLoop_ok_lastQuery (sbelt : DnsSList) (deadline : UInt32) :
    ∀ (n : Nat) (depth fuel' revealed : Nat)
      (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth fuel' revealed) w
        = some ((.ok resp, cout), w') →
      ∃ q₀ qu, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro depth fuel' revealed state w w' resp cout hrun
    obtain _ | f := fuel'
    · rw [run_ioResumeLoop_fuel_zero] at hrun
      exact absurd hrun (by simp)
    · cases n with
      | zero =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_zero] at hrun
        exact absurd hrun (by simp)
      | succ m =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_eq] at hrun
        by_cases hdl : w.clock ≥ deadline
        · simp only [if_pos hdl, run_pure'] at hrun
          exact absurd hrun (by simp)
        · rw [if_neg hdl] at hrun
          simp only [seqPureUnit] at hrun
          cases hbest : state.resources.slist.bestWithAddress with
          | none =>
            rw [hbest] at hrun
            cases hat : state.resources.slist.addressTargets[0]? with
            | none => simp only [hat, run_pure'] at hrun; exact absurd hrun (by simp)
            | some nsName =>
              cases hd : depth with
              | zero =>
                rw [hd] at hrun; simp only [hat, run_pure'] at hrun
                exact absurd hrun (by simp)
              | succ depth' =>
                rw [hd] at hrun
                simp only [hat] at hrun
                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
                    VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _
                    (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache with
                | ok y =>
                  cases y with
                  | done subResp =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                        state.resources.slist nsName (Except.ok subResp)) >>= fun slist' =>
                        Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                          { state with resources := { state.resources with slist := slist' } }
                          deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                    obtain ⟨q₀, qu, hq₀, hqu⟩ := IH mB (by omega) depth' f revealed _ _ _ _ _ hrunB
                    exact ⟨q₀, qu, hq₀, hqu⟩
                  | paused st =>
                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.ioResumeLoop (M := Prog) (Sock := Unit)
                        sbelt st deadline depth' f (Server.seedRevealed st))
                        >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
                        (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                          state.resources.slist nsName p.1) >>= fun slist' =>
                        match p.1 with
                        | .ok subResp =>
                          match Server.extractAAddress nsName subResp.answer with
                          | some _ =>
                            (match Server.gluelessRecheck state p.2 with
                            | some hit =>
                              pure (.ok hit,
                                p.2.touchKeys (Server.recheckTouches state) state.now)
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := slist',
                                    cache := p.2.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed)
                          | none =>
                            Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                              { state with resources := { state.resources with
                                  slist := slist' } } deadline depth' f revealed
                        | .error _ =>
                          Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                            { state with resources := { state.resources with
                                slist := slist' } } deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mI, mK, p, w₂, hle, -, hrunK⟩ := run_bind_inv hrun'
                    obtain ⟨subResult, subCache⟩ := p
                    obtain ⟨mA, mB, slist', w₃, hle2, -, hrunB⟩ := run_bind_inv hrunK
                    cases subResult with
                    | ok subResp =>
                      dsimp only [] at hrunB
                      cases hA : Server.extractAAddress nsName subResp.answer with
                      | some addr =>
                        rw [hA] at hrunB
                        cases hgr : Server.gluelessRecheck state subCache with
                        | some hit =>

                          unfold Server.gluelessRecheck at hgr
                          cases hlq : state.lastQuery with
                          | none =>
                            rw [hlq] at hgr
                            exact absurd hgr (by simp)
                          | some q₀ =>
                            rw [hlq] at hgr
                            dsimp only [] at hgr
                            cases hqu : q₀.question[0]? with
                            | none =>
                              rw [hqu] at hgr
                              exact absurd hgr (by simp)
                            | some qu => exact ⟨q₀, qu, rfl, hqu⟩
                        | none =>
                          rw [hgr] at hrunB
                          obtain ⟨q₀, qu, hq₀, hqu⟩ := IH mB (by omega) depth' f revealed _ _ _ _ _ hrunB
                          exact ⟨q₀, qu, hq₀, hqu⟩
                      | none =>
                        rw [hA] at hrunB
                        obtain ⟨q₀, qu, hq₀, hqu⟩ := IH mB (by omega) depth' f revealed _ _ _ _ _ hrunB
                        exact ⟨q₀, qu, hq₀, hqu⟩
                    | error e =>
                      dsimp only [] at hrunB
                      obtain ⟨q₀, qu, hq₀, hqu⟩ := IH mB (by omega) depth' f revealed _ _ _ _ _ hrunB
                      exact ⟨q₀, qu, hq₀, hqu⟩
                | error msg =>
                  rw [hres] at hrun
                  have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                      state.resources.slist nsName (Except.error msg)) >>= fun slist' =>
                      Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                        { state with resources := { state.resources with slist := slist' } }
                        deadline depth' f revealed) _
                      = some ((Except.ok resp, cout), w') := hrun
                  obtain ⟨mA, mB, slist', w₂, hle, -, hrunB⟩ := run_bind_inv hrun'
                  obtain ⟨q₀, qu, hq₀, hqu⟩ := IH mB (by omega) depth' f revealed _ _ _ _ _ hrunB
                  exact ⟨q₀, qu, hq₀, hqu⟩
          | some entryIp =>
            obtain ⟨entry, ipAddr⟩ := entryIp
            rw [hbest] at hrun
            cases hbuild : Resolver.buildSubQuery state revealed with
            | none => simp only [hbuild, run_pure'] at hrun; exact absurd hrun (by simp)
            | some subQuery0 =>
              obtain ⟨qF, qu, hlq, hqu, -⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
              exact ⟨qF, qu, hlq, hqu⟩

theorem resolve_mkAddressQuery_paused_inv
    (nsName : ByteArray) (sbelt : DnsSList) (now0 : UInt32) (cache : DnsCache)
    (st : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (nsQ : Name)
    (hα : αName nsName = some nsQ)
    (hcanon : nsName = VeriDNS.Impl.DomainName.labelsToWireFormatGo nsQ)
    (hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord
        _ _ _ _ _ _ _ _ (Server.mkAddressQuery nsName) sbelt 64 now0 cache = .ok (.paused st)) :
    ∃ sname' chain',
      Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
          cache (1 : BitVec 16) (1 : BitVec 16) now0 8 nsName #[]
          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) nsName #[])
        = .miss sname' chain'
      ∧ st.resources.cache = cache
      ∧ st.resources.sname = sname'
      ∧ st.now = now0
      ∧ st.cnameChain = chain'
      ∧ st.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries
      ∧ st.lastQuery = some (Server.mkAddressQuery nsName)
      ∧ st.resources.sbelt = sbelt
      ∧ (st.resources.slist = default
         ∨ (∃ nsNames mc, Resolver.stepFindServers.walkNs (RR := VeriDNS.Spec.ResourceRecord)
              sname' cache (BitVec.ofNat 16 2) (BitVec.ofNat 16 1) now0 128 = some (nsNames, mc)
            ∧ st.resources.slist = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList)
                (NS := VeriDNS.Spec.SlistEntry) nsNames
                (reGlue (RR := VeriDNS.Spec.ResourceRecord) cache now0 nsNames) mc)
         ∨ st.resources.slist = sbelt) := by
  unfold Resolver.resolve at hres
  cases hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache (1 : BitVec 16) (1 : BitVec 16) now0 8 nsName #[]
      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) nsName #[]) with
  | negative rc soaAuth chainN =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal,
      mkAddressQuery_question, hla] at hres
    exact absurd hres (by simp)
  | answerHit snameH chainH rrs =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal,
      mkAddressQuery_question, hla] at hres
    exact absurd hres (by simp)
  | abort =>
    exfalso
    rw [show (64 : Nat) = 63 + 1 from rfl, Resolver.resolve.loop] at hres
    simp only [Resolver.step, Resolver.initFromQuery, Resolver.stepCheckLocal,
      mkAddressQuery_question, hla] at hres
    exact absurd hres (by simp)
  | miss sname' chain' =>
    obtain ⟨stP, hloopP, hPcache, hPsname, hPnow, hPchain, hPstep, hPlq, hPsbelt, hPdisj⟩ :=
      loop_checkAnswer_miss_struct
        (Resolver.initFromQuery (S := DnsSList) (C := DnsCache) (NS := VeriDNS.Spec.SlistEntry)
          (RR := VeriDNS.Spec.ResourceRecord) (Server.mkAddressQuery nsName) sbelt now0 cache)
        (Server.mkAddressQuery nsName) ⟨nsName, 1, 1⟩ sname' chain'
        rfl rfl rfl (by exact hla)
        (by
          intro hsEq
          rcases localAnswer_miss_ident_or_fresh cache (1 : BitVec 16) (1 : BitVec 16) now0 8
            nsName #[] (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) nsName #[])
            sname' chain' hla with ⟨-, h2⟩ | hfr
          · exact h2
          · exfalso
            have hmem : nsName ∈ (Resolver.cnameChaseVisited
                (RR := VeriDNS.Spec.ResourceRecord) nsName #[]).toList := by
              simp [Resolver.cnameChaseVisited]
            have hfalse := hfr nsName hmem
            rw [show sname' = nsName from hsEq] at hfalse
            rw [nameEqCI_of_αName_canonical (VeriDNS.Spec.Net.nameEq_refl nsQ) hcanon hcanon
              (fun x hx => (αName_valid hα x hx).2) (fun x hx => (αName_valid hα x hx).2)] at hfalse
            exact absurd hfalse (by simp))
        rfl 61
    have hEq : Except.ok (Resolver.ResolveYield.paused stP)
        = (Except.ok (Resolver.ResolveYield.paused st) :
            Except String (Resolver.ResolveYield DnsSList DnsCache VeriDNS.Spec.SlistEntry
              VeriDNS.Spec.ResourceRecord)) := by
      rw [← hloopP]
      exact hres
    have hstEq : stP = st := by
      injection hEq with h1
      injection h1
    subst hstEq
    refine ⟨sname', chain', rfl, by exact hPcache, hPsname, by exact hPnow, hPchain, hPstep,
      by exact hPlq, by exact hPsbelt, ?_⟩
    rcases hPdisj with h | h | ⟨nsNames, mc, hw, heq⟩ | h
    · exact Or.inl (by exact h)
    · exact Or.inl (by exact h)
    · exact Or.inr (Or.inl ⟨nsNames, mc, by exact hw, by exact heq⟩)
    · exact Or.inr (Or.inr (by exact h))

theorem extractAAddress_model_a {owner : ByteArray} {answers : Array ByteArray} {addr : BitVec 32}
    (h : Server.extractAAddress owner answers = some addr) :
    ∃ r ∈ αSection answers, (∃ ip, r.rdata = VeriDNS.Spec.Net.RData.a ip)
      ∧ ∃ m, VeriDNS.Impl.Resolver.CnameReachableB (RR := VeriDNS.Spec.ResourceRecord)
            owner answers m
          ∧ ∃ w, αName w = some r.owner
            ∧ VeriDNS.Impl.DomainName.nameEqCI w m = true := by
  unfold Server.extractAAddress at h
  obtain ⟨b, hb, hfb⟩ := Array.exists_of_findSome?_eq_some h
  cases hd : DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
  | error e => rw [hd] at hfb; exact absurd hfb (by simp)
  | ok pr =>
    obtain ⟨rr, rest⟩ := pr
    rw [hd] at hfb
    dsimp only [] at hfb
    split at hfb
    · rename_i hguard
      simp only [Bool.and_eq_true, beq_iff_eq] at hguard
      obtain ⟨⟨⟨⟨hty, hcl⟩, hsz⟩, hnm⟩, hrch⟩ := hguard
      have hpr : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr := by
        show (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
          | .ok (rr, _) => some rr
          | .error _ => none) = some rr
        rw [hd]
      obtain ⟨na, hna⟩ : ∃ na, αName rr.name = some na := by
        unfold αName
        cases hw : DomainName.wireFormatToLabels rr.name with
        | ok ls => exact ⟨ls.toList, rfl⟩
        | error e => rw [hw] at hnm; exact absurd hnm (by simp [Except.isOk, Except.toBool])
      obtain ⟨ip, hip⟩ : ∃ ip, αRData rr.type rr.rdata = some (VeriDNS.Spec.Net.RData.a ip) := by
        rw [hty, show αRData (1 : BitVec 16) rr.rdata
          = (αIPv4 rr.rdata).map VeriDNS.Spec.Net.RData.a from rfl]
        unfold αIPv4
        rw [if_pos hsz]
        exact ⟨_, rfl⟩
      have hcls : αClass rr.class = some RRClass.in := by rw [hcl]; rfl
      obtain ⟨m, hmmem, hmeq⟩ : ∃ m ∈ VeriDNS.Impl.Resolver.reachableNamesB
          (RR := VeriDNS.Spec.ResourceRecord) owner answers,
          VeriDNS.Impl.DomainName.nameEqCI rr.name m = true := by
        unfold VeriDNS.Impl.Resolver.nameMemB at hrch
        rw [Array.any_eq_true] at hrch
        obtain ⟨i, hlt, hoeq⟩ := hrch
        exact ⟨_, Array.getElem_mem hlt, by simpa using hoeq⟩
      refine ⟨{ owner := na, ttl := rr.ttl.toNat, rdata := .a ip, cls := .in }, ?_, ⟨ip, rfl⟩,
        m, VeriDNS.Impl.Resolver.reachableNamesB_sound owner answers m hmmem,
        rr.name, hna, hmeq⟩
      unfold αSection
      rw [List.mem_filterMap]
      refine ⟨b, Array.mem_def.mp hb, ?_⟩
      rw [hpr]
      dsimp only []
      unfold αRR
      rw [hna, hip, hcls]
    · exact absurd hfb (by simp)

/-- The full transport of the impl's owner-guarded address extraction to
the model: the extracted A record is ENTITLED — its owner lies on the
model CNAME chain rooted at the (abstracted) NS host. -/
theorem extractAAddress_entitled_model {owner : ByteArray} {answers : Array ByteArray}
    {addr : BitVec 32} {mo : VeriDNS.Spec.Net.Name}
    (hab : ∀ b ∈ answers.toList, ∀ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
        (αRR rr).isSome = true)
    (hα : αName owner = some mo)
    (h : Server.extractAAddress owner answers = some addr) :
    ∃ r ∈ αSection answers, (∃ ip, r.rdata = VeriDNS.Spec.Net.RData.a ip)
      ∧ ∃ n, VeriDNS.Spec.Net.CnameReachable mo (αSection answers) n
        ∧ VeriDNS.Spec.Net.nameEq r.owner n = true := by
  obtain ⟨r, hrmem, hip, m, hcrB, w, hw, hci⟩ := extractAAddress_model_a h
  have hab' : VeriDNS.Proof.Refinement.AllAbstract answers := by
    intro b hb rr hpr
    exact Option.isSome_iff_exists.mp (hab b (Array.mem_def.mp hb) rr hpr)
  obtain ⟨mm, hmm⟩ := VeriDNS.Proof.Refinement.αName_reachableB hab' hα hcrB
  have hcrM := VeriDNS.Proof.Refinement.cnameReachableB_to_model hab' hα hcrB mm hmm
  obtain ⟨na', hna', hne⟩ := VeriDNS.Proof.Refinement.αName_of_nameEqCI hci hmm
  obtain rfl : na' = r.owner := Option.some.inj (hna'.symm.trans hw)
  exact ⟨r, hrmem, hip, mm, hcrM, hne⟩

theorem foldl_ipMinOpt_some :
    ∀ (l : List VeriDNS.Spec.Net.IPv4) (a : VeriDNS.Spec.Net.IPv4),
      ∃ b, l.foldl VeriDNS.Spec.Net.ipMinOpt (some a) = some b := by
  intro l
  induction l with
  | nil => intro a; exact ⟨a, rfl⟩
  | cons x t ih =>
    intro a
    rw [List.foldl_cons]
    exact ih _

theorem gluelessRecheck_cases
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (subCache : DnsCache) (q₀ : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question)
    (hlq : state.lastQuery = some q₀) (hqu : q₀.question[0]? = some qu) :
    (∀ hit, Server.gluelessRecheck state subCache = some hit →
      (∃ rc, subCache.lookupNegative state.resources.sname qu.qtype qu.qclass state.now = some rc
        ∧ hit = Resolver.finalizeAnswer state (Resolver.negativeResponse q₀ rc
            (VeriDNS.Spec.NegativeAuthoritySpec.authoritySection (RR := VeriDNS.Spec.ResourceRecord)
              subCache state.resources.sname qu.qtype qu.qclass state.now)))
      ∨ (subCache.lookupNegative state.resources.sname qu.qtype qu.qclass state.now = none
        ∧ (subCache.lookupAnswerable state.resources.sname qu.qtype qu.qclass state.now).isEmpty
            = false
        ∧ hit = Resolver.finalizeAnswer state (Resolver.cacheResponse q₀
            (subCache.lookupAnswerable state.resources.sname qu.qtype qu.qclass state.now))))
    ∧ (Server.gluelessRecheck state subCache = none →
        subCache.lookupNegative state.resources.sname qu.qtype qu.qclass state.now = none
        ∧ (subCache.lookupAnswerable state.resources.sname qu.qtype qu.qclass state.now).isEmpty
            = true) := by
  unfold Server.gluelessRecheck
  rw [hlq]
  dsimp only []
  rw [hqu]
  dsimp only []
  constructor
  · intro hit hr
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative subCache state.resources.sname
        qu.qtype qu.qclass state.now with
    | some rc =>
      rw [hneg] at hr
      exact Or.inl ⟨rc, hneg, (Option.some.inj hr).symm⟩
    | none =>
      rw [hneg] at hr
      dsimp only [] at hr
      by_cases hie : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) subCache state.resources.sname qu.qtype qu.qclass
          state.now).isEmpty = true
      · rw [if_pos hie] at hr
        exact absurd hr (by simp)
      · rw [if_neg hie] at hr
        have hie2 : ¬((subCache.lookupAnswerable state.resources.sname qu.qtype qu.qclass
            state.now).isEmpty = true) := hie
        exact Or.inr ⟨hneg, by simpa using hie2, (Option.some.inj hr).symm⟩
  · intro hr
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative subCache state.resources.sname
        qu.qtype qu.qclass state.now with
    | some rc =>
      rw [hneg] at hr
      exact absurd hr (by simp)
    | none =>
      rw [hneg] at hr
      dsimp only [] at hr
      by_cases hie : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) subCache state.resources.sname qu.qtype qu.qclass
          state.now).isEmpty = true
      · exact ⟨hneg, hie⟩
      · rw [if_neg hie] at hr
        exact absurd hr (by simp)

theorem lookupNegative_negHit_negResponse (cache : DnsCache) (sname : ByteArray)
    (qt qc : BitVec 16) (now32 : UInt32) (q : Query) (t : RRType) (rc : VeriDNS.Spec.Rcode)
    (hlk : cache.lookupNegative sname qt qc now32 = some rc)
    (hα : αName sname = some q.qname) (ht : αType qt = some t) (hqq : q.qtype = QType.rr t)
    (hcan : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hval : ∀ x ∈ q.qname, x.size ≤ 63)
    (hnegwf : CacheNegWf cache qc) :
    (αCache cache).negHit (αTime now32) q = true
    ∧ αRCode rc = (if (αCache cache).negHitNx (αTime now32) q
        then RCode.nameError else RCode.noError) := by
  refine ⟨lookupNegative_negHit cache sname qt qc now32 rc q t hlk hα ht hqq, ?_⟩
  unfold Cache.DnsCache.lookupNegative at hlk
  cases hnx : cache.lookupNxdomain sname qc now32 with
  | some rc' =>
    rw [hnx] at hlk
    have hrc' : rc = rc' := by
      simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hlk
      exact (Option.some.inj hlk).symm
    subst hrc'
    have hne : rc = VeriDNS.Spec.Rcode.nameError := lookupNxdomain_nameError _ _ _ _ _ hnx
    have hnxT : (αCache cache).negHitNx (αTime now32) q = true :=
      lookupNxdomain_negHitNx cache sname qc now32 rc q hnx hα
    rw [hnxT, if_pos rfl, hne]
    rfl
  | none =>
    rw [hnx] at hlk
    simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hlk
    obtain ⟨e, hemem, hef⟩ := Array.exists_of_findSome?_eq_some hlk
    have hnxF : (αCache cache).negHitNx (αTime now32) q = false :=
      lookupNxdomain_none_negHitNx_false cache sname qc now32 q hcan hval hnegwf hnx
    rw [hnxF, if_neg (by simp)]
    split at hef
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      have hrcE : rc = e.rcode := (Option.some.inj hef).symm
      rcases (hnegwf e hemem).2.1 with hne | hno
      ·
        exfalso
        unfold Cache.DnsCache.lookupNxdomain at hnx
        rw [← Array.findSome?_toList, List.findSome?_eq_none_iff] at hnx
        have hfe := hnx e (Array.mem_def.mp hemem)
        rw [if_pos (by
          rw [hcond.1.1.1, hne]
          simp only [Bool.true_and]
          rw [Bool.and_eq_true, Bool.and_eq_true]
          exact ⟨⟨hcond.1.2, hcond.2⟩, by decide⟩)] at hfe
        exact absurd hfe (by simp)
      · rw [hrcE, hno]
        rfl
    · exact absurd hef (by simp)

theorem lookupAnswerable_hit_bridge (cache : DnsCache) (sname : ByteArray)
    (qt qc : BitVec 16) (now32 : UInt32) (q : Query) (t : RRType)
    (hα : αName sname = some q.qname) (ht : αType qt = some t) (hqq : q.qtype = QType.rr t)
    (hqc : αClass qc = some q.qclass)
    (hcan : sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname)
    (hval : ∀ x ∈ q.qname, x.size ≤ 63)
    (hwf : CacheWf cache now32)
    (hne : (cache.lookupAnswerable sname qt qc now32).isEmpty = false) :
    (cache.lookupAnswerable sname qt qc now32).toList.filterMap αRR
        = (αCache cache).hit (αTime now32) q
    ∧ 0 < ((αCache cache).hit (αTime now32) q).length := by
  have heq := lookupAnswerable_αRR_eq_hit cache sname qt qc now32 q t hα ht hqq hqc hcan hval
    hwf.1 hwf.2.1 hwf.2.2
  refine ⟨heq, ?_⟩
  have hnil : cache.lookupAnswerable sname qt qc now32 ≠ #[] := by
    intro h0
    rw [h0] at hne
    exact absurd hne (by simp)
  have hsz : 0 < (cache.lookupAnswerable sname qt qc now32).size := by
    rcases Nat.eq_zero_or_pos (cache.lookupAnswerable sname qt qc now32).size with h0 | h
    · exact absurd (Array.size_eq_zero_iff.mp h0) hnil
    · exact h
  have hmem0 : (cache.lookupAnswerable sname qt qc now32)[0]
      ∈ (cache.lookupAnswerable sname qt qc now32).toList :=
    Array.mem_def.mp (Array.getElem_mem hsz)
  obtain ⟨⟨cn0, hαcn0⟩, -⟩ := lookupAnswerable_αRR_isSome hwf.1 hmem0
  have hmemM : cn0 ∈ (αCache cache).hit (αTime now32) q := by
    rw [← heq]
    exact List.mem_filterMap.mpr ⟨_, hmem0, hαcn0⟩
  cases hml : (αCache cache).hit (αTime now32) q with
  | nil => rw [hml] at hmemM; exact absurd hmemM (by simp)
  | cons a l => simp

def RdataCanon (rr : VeriDNS.Spec.ResourceRecord) : Prop :=
  ∃ na, αName rr.rdata = some na
    ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
    ∧ (∀ x ∈ na, x.size ≤ 63) ∧ na.length ≤ 127

def RespWriteWf (query resp : VeriDNS.Spec.Format) (now : UInt32) : Prop :=
  ∀ raw ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
      (Server.clientQname query) resp.answer).toList, ∀ rr,
    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
      (αRR rr).isSome = true
      ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat
      ∧ (rr.type = BitVec.ofNat 16 2 → RdataCanon rr)
      ∧ (rr.type = BitVec.ofNat 16 5 → RdataCanon rr)

theorem lookupAnswerable_respWriteWf_facts {cache : DnsCache} {sname : ByteArray}
    {qt qc : BitVec 16} {now : UInt32}
    (hwf : CacheWf cache now) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    {raw : ByteArray}
    (hraw : raw ∈ ((cache.lookupAnswerable sname qt qc now).map
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))).toList)
    {rr : VeriDNS.Spec.ResourceRecord}
    (hp : VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr) :
    (αRR rr).isSome = true
    ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat
    ∧ (rr.type = BitVec.ofNat 16 2 → RdataCanon rr)
    ∧ (rr.type = BitVec.ofNat 16 5 → RdataCanon rr) := by
  rw [Array.toList_map, List.mem_map] at hraw
  obtain ⟨rr0, hrr0, rfl⟩ := hraw
  rw [lookupAnswerable_parseRaw_rrBytes hwfrr hrr0] at hp
  obtain rfl := Option.some.inj hp
  obtain ⟨⟨cn, hcn⟩, -⟩ := lookupAnswerable_αRR_isSome hwf.1 hrr0
  obtain ⟨e, he, hae, hrre⟩ := lookupAnswerable_mem_entry hrr0
  have hfr : e.fresh now = true := by
    unfold answerableEntry liveEntry at hae
    simp only [Bool.and_eq_true] at hae
    exact hae.1.2
  have hlt : now < e.expiry := by
    unfold Cache.CacheEntry.fresh at hfr
    simpa using hfr
  have hsub : (e.expiry - now).toNat = e.expiry.toNat - now.toNat :=
    UInt32.toNat_sub_of_le e.expiry now (UInt32.le_of_lt hlt)
  subst hrre
  refine ⟨by rw [hcn]; rfl, ?_, ?_, ?_⟩
  ·
    have httl : ({ e.rr with ttl := BitVec.ofNat 32 (e.expiry - now).toNat }
        : VeriDNS.Spec.ResourceRecord).ttl.toNat = e.expiry.toNat - now.toNat := by
      show (BitVec.ofNat 32 (e.expiry - now).toNat).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hsub ▸ (e.expiry - now).toNat_lt), hsub]
    rw [httl]
    have hexp_lt : e.expiry.toNat < 2 ^ 32 := e.expiry.toNat_lt
    have hnow_le : now.toNat ≤ e.expiry.toNat := by
      have := UInt32.le_of_lt hlt
      exact UInt32.le_iff_toNat_le.mp this
    have ht32 : (e.expiry.toNat - now.toNat).toUInt32.toNat = e.expiry.toNat - now.toNat :=
      UInt32.toNat_ofNat_of_lt' (by show _ < 4294967296; omega)
    rw [UInt32.toNat_add, ht32]
    exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
  · intro htype
    have hty : e.rr.type = BitVec.ofNat 16 2 := htype
    exact hns e (by simpa using he) hty
  · intro htype
    have hty : e.rr.type = BitVec.ofNat 16 5 := htype
    exact hcnc e (by simpa using he) hty

def chainOf : Resolver.LocalResult VeriDNS.Spec.ResourceRecord → Option (Array ByteArray)
  | .negative _ _ chain => some chain
  | .answerHit _ chain _ => some chain
  | .miss _ chain => some chain
  | .abort => none

theorem localAnswer_chain_provenance {cache : DnsCache} {qt qc : BitVec 16} {now : UInt32} :
    ∀ (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
      (chainOut : Array ByteArray),
      chainOf (Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname chain visited) = some chainOut →
      (∀ raw ∈ chain.toList, ∃ sn,
        raw ∈ ((cache.lookupAnswerable sn (5 : BitVec 16) qc now).map
          (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))).toList) →
      ∀ raw ∈ chainOut.toList, ∃ sn,
        raw ∈ ((cache.lookupAnswerable sn (5 : BitVec 16) qc now).map
          (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))).toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname chain visited chainOut hres
    exact absurd hres (by simp [Resolver.localAnswer, chainOf])
  | succ f IHf =>
    intro sname chain visited chainOut hres hchain
    unfold Resolver.localAnswer at hres
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now with
    | some rc =>
      rw [hneg] at hres
      obtain rfl : chain = chainOut := by
        simpa [chainOf] using hres
      exact hchain
    | none =>
      rw [hneg] at hres
      dsimp only [] at hres
      by_cases hie : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true
      · rw [if_pos hie] at hres
        by_cases hq5 : (qt == (5 : BitVec 16)) = true
        · rw [if_pos hq5] at hres
          obtain rfl : chain = chainOut := by simpa [chainOf] using hres
          exact hchain
        · rw [if_neg hq5] at hres
          cases hcrr : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
              (RR := VeriDNS.Spec.ResourceRecord) cache sname (5 : BitVec 16) qc now)[0]? with
          | none =>
            rw [hcrr] at hres
            obtain rfl : chain = chainOut := by simpa [chainOf] using hres
            exact hchain
          | some crr =>
            rw [hcrr] at hres
            dsimp only [] at hres
            by_cases hvis : (visited.any (fun v => VeriDNS.Impl.DomainName.nameEqCI v
                (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr))) = true
            · rw [if_pos hvis] at hres
              obtain rfl : chain = chainOut := by simpa [chainOf] using hres
              exact hchain
            · rw [if_neg hvis] at hres
              refine IHf _ _ _ _ hres ?_
              intro raw hraw
              rw [Array.toList_push, List.mem_append] at hraw
              rcases hraw with hold | hnew
              · exact hchain raw hold
              · refine ⟨sname, ?_⟩
                rw [List.mem_singleton] at hnew
                subst hnew
                rw [Array.toList_map, List.mem_map]
                exact ⟨crr, Array.mem_def.mp
                  (show crr ∈ cache.lookupAnswerable sname (5 : BitVec 16) qc now from
                    Array.mem_of_getElem? hcrr), rfl⟩
      · rw [if_neg hie] at hres
        obtain rfl : chain = chainOut := by simpa [chainOf] using hres
        exact hchain

def AnswerWriteWf (answer : Array ByteArray) (now : UInt32) : Prop :=
  ∀ raw ∈ answer.toList, ∀ rr,
    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) raw = some rr →
      (αRR rr).isSome = true
      ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat
      ∧ (rr.type = BitVec.ofNat 16 2 → RdataCanon rr)
      ∧ (rr.type = BitVec.ofNat 16 5 → RdataCanon rr)

theorem respWriteWf_of_answerWriteWf {query resp : VeriDNS.Spec.Format} {now : UInt32}
    (h : AnswerWriteWf resp.answer now) : RespWriteWf query resp now :=
  fun raw hraw rr hp => h raw (ownerRaws_toList_sub hraw) rr hp

theorem answerWriteWf_empty (now : UInt32) : AnswerWriteWf #[] now := by
  intro raw hraw
  simp at hraw

theorem answerWriteWf_append {a b : Array ByteArray} {now : UInt32}
    (ha : AnswerWriteWf a now) (hb : AnswerWriteWf b now) : AnswerWriteWf (a ++ b) now := by
  intro raw hraw rr hp
  rw [Array.toList_append, List.mem_append] at hraw
  rcases hraw with h | h
  · exact ha raw h rr hp
  · exact hb raw h rr hp

theorem answerWriteWf_finalize
    {s : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord}
    {resp0 : VeriDNS.Spec.Format} {now : UInt32}
    (hchain : AnswerWriteWf s.cnameChain now) (hresp : AnswerWriteWf resp0.answer now) :
    AnswerWriteWf (Resolver.finalizeAnswer s resp0).answer now := by
  rw [finalizeAnswer_answer, prependChain_answer]
  split
  · exact hresp
  · exact answerWriteWf_append hchain hresp

theorem answerWriteWf_lookup_map {cache : DnsCache} {sname : ByteArray} {qt qc : BitVec 16}
    {now : UInt32}
    (hwf : CacheWf cache now) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr) :
    AnswerWriteWf ((cache.lookupAnswerable sname qt qc now).map
      (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))) now :=
  fun _raw hraw _rr hp => lookupAnswerable_respWriteWf_facts hwf hns hcnc hwfrr hraw hp

theorem answerWriteWf_of_chain_provenance {cache : DnsCache} {qc : BitVec 16} {now : UInt32}
    {chain : Array ByteArray}
    (hwf : CacheWf cache now) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hprov : ∀ raw ∈ chain.toList, ∃ sn,
      raw ∈ ((cache.lookupAnswerable sn (5 : BitVec 16) qc now).map
        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))).toList) :
    AnswerWriteWf chain now := by
  intro raw hraw rr hp
  obtain ⟨sn, hmem⟩ := hprov raw hraw
  exact lookupAnswerable_respWriteWf_facts hwf hns hcnc hwfrr hmem hp

theorem answerWriteWf_push {a : Array ByteArray} {b : ByteArray} {now : UInt32}
    (ha : AnswerWriteWf a now)
    (hb : ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
      (αRR rr).isSome = true
      ∧ (now + rr.ttl.toNat.toUInt32).toNat = now.toNat + rr.ttl.toNat
      ∧ (rr.type = BitVec.ofNat 16 2 → RdataCanon rr)
      ∧ (rr.type = BitVec.ofNat 16 5 → RdataCanon rr)) :
    AnswerWriteWf (a.push b) now := by
  intro raw hraw rr hp
  rw [Array.toList_push, List.mem_append] at hraw
  rcases hraw with h | h
  · exact ha raw h rr hp
  · rw [List.mem_singleton] at h
    subst h
    exact hb rr hp

theorem localAnswer_chain_links {cache : DnsCache} {qt qc : BitVec 16} {now : UInt32} :
    ∀ (fuel : Nat) (sname : ByteArray) (chain visited : Array ByteArray)
      (chainOut : Array ByteArray),
      chainOf (Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qt qc now fuel sname chain visited) = some chainOut →
      ∀ raw ∈ chainOut.toList, raw ∈ chain.toList ∨ ∃ sn,
        raw ∈ ((cache.lookupAnswerable sn (5 : BitVec 16) qc now).map
          (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))).toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro sname chain visited chainOut hres
    exact absurd hres (by simp [Resolver.localAnswer, chainOf])
  | succ f IHf =>
    intro sname chain visited chainOut hres
    unfold Resolver.localAnswer at hres
    cases hneg : VeriDNS.Spec.NegativeCacheSpec.retrieveNegative cache sname qt qc now with
    | some rc =>
      rw [hneg] at hres
      obtain rfl : chain = chainOut := by
        simpa [chainOf] using hres
      exact fun raw h => Or.inl h
    | none =>
      rw [hneg] at hres
      dsimp only [] at hres
      by_cases hie : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
          (RR := VeriDNS.Spec.ResourceRecord) cache sname qt qc now).isEmpty = true
      · rw [if_pos hie] at hres
        by_cases hq5 : (qt == (5 : BitVec 16)) = true
        · rw [if_pos hq5] at hres
          obtain rfl : chain = chainOut := by simpa [chainOf] using hres
          exact fun raw h => Or.inl h
        · rw [if_neg hq5] at hres
          cases hcrr : (VeriDNS.Spec.TrustworthinessSpec.answers (C := DnsCache)
              (RR := VeriDNS.Spec.ResourceRecord) cache sname (5 : BitVec 16) qc now)[0]? with
          | none =>
            rw [hcrr] at hres
            obtain rfl : chain = chainOut := by simpa [chainOf] using hres
            exact fun raw h => Or.inl h
          | some crr =>
            rw [hcrr] at hres
            dsimp only [] at hres
            by_cases hvis : (visited.any (fun v => VeriDNS.Impl.DomainName.nameEqCI v
                (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) crr))) = true
            · rw [if_pos hvis] at hres
              obtain rfl : chain = chainOut := by simpa [chainOf] using hres
              exact fun raw h => Or.inl h
            · rw [if_neg hvis] at hres
              intro raw hraw
              rcases IHf _ _ _ _ hres raw hraw with hin | hprov
              · rw [Array.toList_push, List.mem_append] at hin
                rcases hin with hold | hnew
                · exact Or.inl hold
                · refine Or.inr ⟨sname, ?_⟩
                  rw [List.mem_singleton] at hnew
                  subst hnew
                  rw [Array.toList_map, List.mem_map]
                  exact ⟨crr, Array.mem_def.mp
                    (show crr ∈ cache.lookupAnswerable sname (5 : BitVec 16) qc now from
                      Array.mem_of_getElem? hcrr), rfl⟩
              · exact Or.inr hprov
      · rw [if_neg hie] at hres
        obtain rfl : chain = chainOut := by simpa [chainOf] using hres
        exact fun raw h => Or.inl h

theorem localAnswer_chain_answerWriteWf {cache : DnsCache} {qt qc : BitVec 16} {now : UInt32}
    {fuel : Nat} {sname : ByteArray} {chain visited chainOut : Array ByteArray}
    (hwf : CacheWf cache now) (hns : CacheNsCanon cache) (hcnc : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hres : chainOf (Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
      cache qt qc now fuel sname chain visited) = some chainOut)
    (hchain : AnswerWriteWf chain now) :
    AnswerWriteWf chainOut now := by
  intro raw hraw rr hp
  rcases localAnswer_chain_links fuel sname chain visited chainOut hres raw hraw with h | ⟨sn, hmem⟩
  · exact hchain raw h rr hp
  · exact lookupAnswerable_respWriteWf_facts hwf hns hcnc hwfrr hmem hp

theorem answerWriteWf_of_wire {resp0 respS respA : VeriDNS.Spec.Format} {now : UInt32}
    (hsani : Server.sanitizeTtlsCap resp0 = some respS)
    (hrespAeq : respA = respS)
    (hclock : now.toNat + 604800 < 2 ^ 32)
    (hvalidAns : ∀ b ∈ respA.answer.toList, ∃ rr,
      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
        ∧ αRR rr ≠ none)
    (hcanonAns : ∀ raw ∈ respA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw) :
    AnswerWriteWf respA.answer now := by
  intro raw hraw rr hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨rr', hpr', hα'⟩ := hvalidAns raw hraw
    rw [hpr'] at hp
    injection hp with h
    subst h
    cases hα : αRR rr' with
    | none => exact absurd hα hα'
    | some r => rfl
  · have hb' : raw ∈ respS.answer := by
      rw [← hrespAeq]
      exact Array.mem_def.mpr hraw
    have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani raw
      (Or.inl (Or.inl hb')) rr hp
    exact uint32_add_ttl_toNat now rr.ttl.toNat httl hclock
  · intro htype
    exact canonicalRR_nsRdata_canonical (hcanonAns raw hraw) hp htype
  · intro htype
    exact canonicalRR_cnameRdata_canonical (hcanonAns raw hraw) hp htype

theorem tcpSpoofReply_of_honest
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (now : Net.Time)
    (hnetWF : net.WF)
    (w : World) (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format) (qm : Query)
    (hwmTcp : WorldModelsTcp net ns ra ednsBuf now w)
    (hO : w.tcpOracle (Message.encode (Server.withSecrets q id cid)) ab = some bytes)
    (hdec : Message.decode bytes = .ok resp0)
    (hsan : Server.sanitizeTtlsCap resp0 = some resp₀)
    (hacc : Server.acceptResponse (Server.withSecrets q id cid) resp₀ = some resp)
    (hαq : αQuery q = some qm)
    (htc0 : (resp.header.tc == 1) = false)
    (hreachR : linkReach net ns ra ra = true) :
    SpoofReply net ns ra ednsBuf id ab resp qm := by
  obtain ⟨srv, tr, ref, hfind, hans, hrag, hreach, hisref, _hcncorr, _hansEq, hvAns, hvAuth,
      hcut, hnscanon, _hnsnodup, hauthEq, haddEq, haaEq, hvAdd, htcEq⟩ :=
    hwmTcp q id cid ab bytes resp0 resp₀ resp qm hO hdec hsan hacc hαq
  obtain ⟨htrans, hacc', _hw⟩ :=
    honest_wire_premises net ns ra (byteAddrToModel ab) id.toNat 0 ednsBuf qm ref hreach hreachR
  refine ⟨byteAddrToModel ab,
    replyDatagram (queryDatagram id.toNat ra (byteAddrToModel ab) 0 ednsBuf qm) ref, 0,
    htrans, hacc', hrag, hisref, htcEq.symm.trans htc0, hauthEq, hvAns, hvAuth, ?_⟩
  intro href
  refine ⟨haddEq, haaEq, ?_, hvAdd, hcut, hnscanon, htcEq⟩
  rcases serverAnswers_referral_inv hans href with ⟨z, dd, hz, hd, hauth⟩ | ⟨-, hauthc⟩
  · exact (referral_bailiwick_desc hnetWF hfind hz hd hauth).1
  · exact cachedDelegation_inBailiwick srv now qm.qname qm.qclass hauthc

theorem ioResumeLoop_sound
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (sbelt : DnsSList) (deadline : UInt32) (hnetWF : net.WF)

    (hGlSbelt : GluelessProv sbelt) :
    ∀ (n : Nat) (q : Query) (depth fuel' revealed : Nat)
      (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
      (c : Cache) (w w' : World) (now : Net.Time) (nseen : List Name) (seen : List Name)
      (depthFloor : Nat)
      (resp : VeriDNS.Spec.Format) (cout : DnsCache),
      StateModels net ns ra ednsBuf rttOf now q state c w →
      WorldModelsTcp net ns ra ednsBuf now w →
      CacheWf state.resources.cache state.now →
      CacheNsCanon state.resources.cache →
      CacheCnameCanon state.resources.cache →

      (∀ e ∈ state.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr) →

      (∀ qu : VeriDNS.Spec.Question,
          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
          CacheNegWf state.resources.cache qu.qclass) →
      CacheNsDistinct state.resources.cache →
      VeriDNS.Proof.NameTree.OneExpiryPerKey state.resources.cache →
      state.resources.cache.records.size ≤ DnsCache.capacity →
      c.hit now q = [] → c.negHit now q = false →

      (∀ b ∈ seen, b.length < depthFloor) →
      state.resources.slist.matchCount = depthFloor →

      GluelessProv state.resources.slist →

      GluelessProv state.resources.sbelt →
      (∀ qu : VeriDNS.Spec.Question,
          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
          αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass) →
      q.rd = false →

      q.qtype ≠ QType.star →

      q.qclass = RRClass.in →

      state.now.toNat + 604800 < 2 ^ 32 →

      state.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname →

      q.qname.length ≤ 127 →

      (∀ x ∈ q.qname, 0 < x.size ∧ x.size ≤ 63) →

      CnameChainModels state q nseen →
      AnswerWriteWf state.cnameChain state.now →
      state.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries →
      Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth fuel' revealed) w
        = some ((.ok resp, cout), w') →

      ∃ slist v coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v coutM
        ∧ (modelSlistOf state.resources.slist).Subperm slist
        ∧ (αResp resp).rcode = v.rcode
        ∧ (αResp resp).answer = αSection state.cnameChain ++ v.answer
        ∧ CacheRefines (αCache cout) coutM
        ∧ WorldModels net ns ra ednsBuf now w'
        ∧ CacheWf cout state.now
        ∧ CacheNsCanon cout
        ∧ CacheCnameCanon cout
        ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
        ∧ (∀ qu : VeriDNS.Spec.Question,
            (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
            CacheNegWf cout qu.qclass)
        ∧ CacheNsDistinct cout
        ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
        ∧ cout.records.size ≤ DnsCache.capacity
        ∧ AnswerWriteWf resp.answer state.now := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro q depth fuel' revealed state c w w' now nseen seen depthFloor resp cout hSM hwmTcp hCacheWf hNsCanon hCnCanon hwfrr hNegWf hNsDistinct hOE hCap hmiss hnmiss hfreshInv hMC hGlProv hGlBelt hqm hrd hqstar hqin hclock hsnameCanon hqlen hqvalid hCCM hAW hstep hrun
    obtain _ | f := fuel'
    · rw [run_ioResumeLoop_fuel_zero] at hrun
      exact absurd hrun (by simp)
    · cases n with
      | zero =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_zero] at hrun
        exact absurd hrun (by simp)
      | succ m =>
        unfold Server.ioResumeLoop at hrun
        rw [run_now_bind_eq] at hrun
        by_cases hdl : w.clock ≥ deadline
        · simp only [if_pos hdl, run_pure'] at hrun
          exact absurd hrun (by simp)
        · rw [if_neg hdl] at hrun
          simp only [seqPureUnit] at hrun
          cases hbest : state.resources.slist.bestWithAddress with
          | none =>

            rw [hbest] at hrun
            cases hat : state.resources.slist.addressTargets[0]? with
            | none => simp only [hat, run_pure'] at hrun; exact absurd hrun (by simp)
            | some nsName =>
              cases hd : depth with
              | zero =>
                rw [hd] at hrun; simp only [hat, run_pure'] at hrun
                exact absurd hrun (by simp)
              | succ depth' =>
                rw [hd] at hrun
                simp only [hat] at hrun

                suffices h : ∃ slist v coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v coutM
                    ∧ (αResp resp).rcode = v.rcode
                    ∧ (αResp resp).answer = αSection state.cnameChain ++ v.answer
                    ∧ CacheRefines (αCache cout) coutM
                    ∧ WorldModels net ns ra ednsBuf now w'
                    ∧ CacheWf cout state.now
                    ∧ CacheNsCanon cout
                    ∧ CacheCnameCanon cout
                    ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                    ∧ (∀ qu : VeriDNS.Spec.Question,
                        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                        CacheNegWf cout qu.qclass)
                    ∧ CacheNsDistinct cout
                    ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
                    ∧ cout.records.size ≤ DnsCache.capacity
                    ∧ AnswerWriteWf resp.answer state.now by
                  obtain ⟨sl, v, cM, hv, hrc, hans, hrest⟩ := h
                  exact ⟨sl, v, cM, hv, by
                    rw [modelSlistOf_nil_of_bestWithAddress_none state.resources.slist hbest]
                    exact List.nil_subperm, hrc, hans, hrest⟩

                obtain ⟨m1, hm1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                cases hres : @Resolver.resolve DnsSList DnsCache VeriDNS.Spec.SlistEntry
                    VeriDNS.Spec.ResourceRecord _ _ _ _ _ _ _ _
                    (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache with
                | ok y =>
                  cases y with
                  | done subResp =>

                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                        state.resources.slist nsName (Except.ok subResp)) >>= fun slist' =>
                        Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                          { state with resources := { state.resources with slist := slist' } }
                          deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    cases hA : Server.extractAAddress nsName subResp.answer with
                    | some addr =>

                      unfold Server.gluelessUpdatedSlist at hrun'
                      simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrun'
                      rw [← Prog.bind_def] at hrun'
                      obtain ⟨m2, hm2, hrun'⟩ := run_log_bind_inv _ _ _ hrun'
                      obtain ⟨s, v, cM, hrec, -, hrc, hans, hrest⟩ := IH m2 (by omega) q depth' f _
                        { state with resources := { state.resources with
                            slist := state.resources.slist.addAddress nsName addr,
                            cache := state.resources.cache } }
                        c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_addAddress nsName addr hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun'
                      exact ⟨s, v, cM, hrec, hrc, hans, hrest⟩
                    | none =>

                      unfold Server.gluelessUpdatedSlist at hrun'
                      simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrun'
                      rw [← Prog.bind_def] at hrun'
                      obtain ⟨m2, hm2, hrun'⟩ := run_log_bind_inv _ _ _ hrun'
                      obtain ⟨s, v, cM, hrec, -, hrc, hans, hrest⟩ := IH m2 (by omega) q depth' f _
                        { state with resources := { state.resources with
                            slist := state.resources.slist.removeServer nsName,
                            cache := state.resources.cache } }
                        c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_removeServer nsName hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun'
                      exact ⟨s, v, cM, hrec, hrc, hans, hrest⟩
                  | paused st =>

                    rw [hres] at hrun
                    have hrun' : Prog.run m1 ((Server.ioResumeLoop (M := Prog) (Sock := Unit)
                        sbelt st deadline depth' f (Server.seedRevealed st))
                        >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
                        (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                          state.resources.slist nsName p.1) >>= fun slist' =>
                        match p.1 with
                        | .ok subResp =>
                          match Server.extractAAddress nsName subResp.answer with
                          | some _ =>
                            (match Server.gluelessRecheck state p.2 with
                            | some hit =>
                              pure (.ok hit,
                                p.2.touchKeys (Server.recheckTouches state) state.now)
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := slist',
                                    cache := p.2.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed)
                          | none =>
                            Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                              { state with resources := { state.resources with
                                  slist := slist' } } deadline depth' f revealed
                        | .error _ =>
                          Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                            { state with resources := { state.resources with
                                slist := slist' } } deadline depth' f revealed) _
                        = some ((Except.ok resp, cout), w') := hrun
                    obtain ⟨mI, mK, p, w2, hfuelIK, hrunI, hrunK⟩ := run_bind_inv hrun'
                    obtain ⟨subResult, subCache⟩ := p
                    dsimp only [] at hrunK
                    obtain ⟨horacle2, -, -⟩ := run_world_frame hrunI
                    have htcpO2 := run_world_tcpOracle_frame hrunI
                    cases subResult with
                    | error e =>

                      unfold Server.gluelessUpdatedSlist at hrunK
                      simp only [Prog.bind_def, Prog.bind_assoc] at hrunK
                      rw [← Prog.bind_def] at hrunK
                      obtain ⟨m2, hm2, hrunK⟩ := run_log_bind_inv _ _ _ hrunK
                      obtain ⟨hmme, hsn, htm, hwm⟩ := hSM
                      obtain ⟨s, v, cM, hrec, -, hrc, hans, hrest⟩ := IH m2 (by omega) q depth' f _
                        { state with resources := { state.resources with
                            slist := state.resources.slist.removeServer nsName,
                            cache := state.resources.cache } }
                        c _ w' now nseen seen depthFloor resp cout
                        (by exact ⟨hmme, hsn, htm,
                          WorldModels_oracle net ns ra ednsBuf now (by exact horacle2) hwm⟩)
                        (by exact WorldModelsTcp_tcpOracle net ns ra ednsBuf now htcpO2 hwmTcp)
                        (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_removeServer nsName hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrunK
                      exact ⟨s, v, cM, hrec, hrc, hans, hrest⟩
                    | ok subResp =>
                      cases hA : Server.extractAAddress nsName subResp.answer with
                      | none =>

                        unfold Server.gluelessUpdatedSlist at hrunK
                        simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrunK
                        rw [← Prog.bind_def] at hrunK
                        obtain ⟨m2, hm2, hrunK⟩ := run_log_bind_inv _ _ _ hrunK
                        obtain ⟨hmme, hsn, htm, hwm⟩ := hSM
                        obtain ⟨s, v, cM, hrec, -, hrc, hans, hrest⟩ := IH m2 (by omega) q depth' f _
                          { state with resources := { state.resources with
                              slist := state.resources.slist.removeServer nsName,
                              cache := state.resources.cache } }
                          c _ w' now nseen seen depthFloor resp cout
                          (by exact ⟨hmme, hsn, htm,
                            WorldModels_oracle net ns ra ednsBuf now (by exact horacle2) hwm⟩)
                          (by exact WorldModelsTcp_tcpOracle net ns ra ednsBuf now htcpO2 hwmTcp)
                          (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_removeServer nsName hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrunK
                        exact ⟨s, v, cM, hrec, hrc, hans, hrest⟩
                      | some addr =>

                        unfold Server.gluelessUpdatedSlist at hrunK
                        simp only [hA, Prog.bind_def, Prog.bind_assoc] at hrunK
                        rw [← Prog.bind_def] at hrunK
                        obtain ⟨m2, hm2, hrunK⟩ := run_log_bind_inv _ _ _ hrunK

                        have hrunK' : Prog.run m2
                            (match Server.gluelessRecheck state subCache with
                            | some hit =>
                              (pure (.ok hit,
                                  subCache.touchKeys (Server.recheckTouches state) state.now) :
                                Prog (Except String VeriDNS.Spec.Format × DnsCache))
                            | none =>
                              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.addAddress nsName addr,
                                    cache := subCache.touchKeys (Server.recheckTouches state)
                                      state.now } } deadline depth' f revealed) _
                            = some ((Except.ok resp, cout), w') := hrunK
                        clear hrunK

                        have hLQ : ∃ q₀ qu, state.lastQuery = some q₀
                            ∧ q₀.question[0]? = some qu := by
                          cases hgr : Server.gluelessRecheck state subCache with
                          | some hit =>
                            unfold Server.gluelessRecheck at hgr
                            cases hlq : state.lastQuery with
                            | none =>
                              rw [hlq] at hgr
                              exact absurd hgr (by simp)
                            | some q₀ =>
                              rw [hlq] at hgr
                              dsimp only [] at hgr
                              cases hqu : q₀.question[0]? with
                              | none =>
                                rw [hqu] at hgr
                                exact absurd hgr (by simp)
                              | some qu => exact ⟨q₀, qu, rfl, hqu⟩
                          | none =>
                            have hrunK2 := hrunK'
                            simp only [hgr] at hrunK2
                            obtain ⟨q₀, qu, hq₀, hqu⟩ := ioResumeLoop_ok_lastQuery sbelt deadline
                              m2 depth' f _ _ _ _ _ _ hrunK2
                            exact ⟨q₀, qu, hq₀, hqu⟩
                        obtain ⟨q₀L, quL, hlqL, hquL⟩ := hLQ
                        obtain ⟨hmme, hsn, htm, hwm⟩ := hSM

                        obtain ⟨hqtL, hqcL⟩ := hqm quL ⟨q₀L, hlqL, hquL⟩
                        obtain ⟨tL, htL, hqqL⟩ := αQType_rr_inv hqtL hqstar
                        have hclsL : quL.qclass = (1 : BitVec 16) :=
                          αClass_in_one (by rw [hqcL, hqin])
                        have hnegwfMain : CacheNegWf state.resources.cache (1 : BitVec 16) := by
                          rw [← hclsL]
                          exact hNegWf quL ⟨q₀L, hlqL, hquL⟩

                        have hnsMem : nsName ∈ state.resources.slist.addressTargets.toList := by
                          obtain ⟨h0, heq0⟩ := Array.getElem?_eq_some_iff.mp hat
                          exact heq0 ▸ Array.mem_def.mp (Array.getElem_mem h0)
                        obtain ⟨nsQ, hαns, hcanNs, hlenNs⟩ := hGlProv nsName hnsMem
                        have hvalNs : ∀ x ∈ nsQ, x.size ≤ 63 :=
                          fun x hx => (αName_valid hαns x hx).2

                        obtain ⟨sname', chain', hlaS, hstCache, hstSname, hstNow, hstChain,
                          hstStep, hstLq, hstSbelt, hstSlist⟩ :=
                          resolve_mkAddressQuery_paused_inv nsName sbelt state.now
                            state.resources.cache st nsQ hαns hcanNs hres

                        have hpeelS := localAnswer_chase_peel net ns ra ednsBuf rttOf
                          state.resources.cache c (1 : BitVec 16) (1 : BitVec 16) state.now
                          ⟨nsQ, QType.rr RRType.a, RRClass.in, false⟩ RRType.a [] nsName
                          rfl rfl (by intro h; cases h) rfl hmme hCacheWf hCnCanon hwfrr
                          hnegwfMain 8 nsName nsQ #[]
                          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                            nsName #[])
                          [] (.miss sname' chain') hlaS hαns hcanNs hvalNs hlenNs rfl
                          (by
                            intro nm hnm
                            rcases List.mem_cons.mp hnm with rfl | hnm'
                            · exact ⟨nsName, by simp [Resolver.cnameChaseVisited], hαns,
                                hcanNs, hvalNs⟩
                            · exact absurd hnm' (List.not_mem_nil))
                        obtain ⟨linksS, nF, nseenF, hchainS, hnF, hnFcan, hnFval, hlenF, hvisF,
                          hmissF, hnmissF, hlinksCn, hcontS⟩ := hpeelS

                        obtain ⟨slistSub, vSub, coutMSub, hVsub, -, hrcSub, hansSub, hcrSub, hwm2,
                          hwfS, hnsS, hcnS, hwfrrS, hnegS, hnsdS, hoeS, hcapS, hawSub⟩ :=
                          IH mI (by omega) ⟨nF, QType.rr RRType.a, RRClass.in, false⟩ depth' f (Server.seedRevealed st) st
                            c _ w2 now nseenF [] st.resources.slist.matchCount subResp subCache
                            (by
                              refine ⟨?_, ?_, ?_, hwm⟩
                              · rw [hstCache]; exact hmme
                              · rw [hstSname]; exact hnF
                              · rw [hstNow]; exact htm)
                            (by exact hwmTcp)
                            (by rw [hstCache, hstNow]; exact hCacheWf)
                            (by rw [hstCache]; exact hNsCanon)
                            (by rw [hstCache]; exact hCnCanon)
                            (by rw [hstCache]; exact hwfrr)
                            (by
                              intro qu2 hqu2
                              obtain ⟨q02, hq02, hqu02⟩ := hqu2
                              rw [hstLq] at hq02
                              obtain rfl := Option.some.inj hq02
                              rw [mkAddressQuery_question] at hqu02
                              obtain rfl := Option.some.inj hqu02
                              rw [hstCache]
                              exact hnegwfMain)
                            (by rw [hstCache]; exact hNsDistinct)
                            (by rw [hstCache]; exact hOE)
                            (by rw [hstCache]; exact hCap)
                            (by rw [← htm]; exact hmissF)
                            (by rw [← htm]; exact hnmissF)
                            (by intro b hb; exact absurd hb (List.not_mem_nil))
                            rfl
                            (by
                              rcases hstSlist with h | ⟨nsNames, mcW, hwalk, heq⟩ | h
                              · rw [h]; exact GluelessProv_default
                              · rw [heq]
                                exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                  (walkNs_names_canonical _ state.now hNsCanon 128 sname'
                                    nsNames mcW (by exact hwalk))
                              · rw [h]; exact hGlSbelt)
                            (by rw [hstSbelt]; exact hGlSbelt)
                            (by
                              intro qu2 hqu2
                              obtain ⟨q02, hq02, hqu02⟩ := hqu2
                              rw [hstLq] at hq02
                              obtain rfl := Option.some.inj hq02
                              rw [mkAddressQuery_question] at hqu02
                              obtain rfl := Option.some.inj hqu02
                              exact ⟨rfl, rfl⟩)
                            rfl
                            (by intro h; cases h)
                            rfl
                            (by rw [hstNow]; exact hclock)
                            (by rw [hstSname]; exact hnFcan)
                            hlenF
                            (fun x hx => αName_labels_valid hnF x hx)
                            (by
                              unfold CnameChainModels
                              have hanch : ((st.lastQuery.bind
                                  (fun q0 => q0.question[0]?)).elim st.resources.sname
                                    (fun qu => qu.qname)) = nsName := by
                                rw [hstLq]
                                rfl
                              rw [hanch, hstChain]
                              exact hvisF)
                            (by
                              rw [hstChain, hstNow]
                              exact localAnswer_chain_answerWriteWf hCacheWf hNsCanon hCnCanon hwfrr
                                (congrArg chainOf hlaS) (answerWriteWf_empty _))
                            hstStep hrunI
                        rw [hstNow] at hwfS
                        have hnegSub1 : CacheNegWf subCache (1 : BitVec 16) :=
                          hnegS ⟨nsName, 1, 1⟩ ⟨Server.mkAddressQuery nsName, hstLq, rfl⟩

                        have hlinksEq : αSection chain' = linksS := by
                          rw [hchainS]
                          rfl
                        have hansSub' : (αResp subResp).answer = linksS ++ vSub.answer := by
                          rw [hansSub, hstChain, hlinksEq]

                        -- transport the impl's owner-guarded extraction to the model:
                        -- the extracted A record is entitled on the CNAME chain at nsQ
                        have hawAll : ∀ b ∈ subResp.answer.toList, ∀ rr,
                            VeriDNS.Spec.RRParse.parseRaw
                              (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                              (αRR rr).isSome = true :=
                          fun b hb rr hpr => (hawSub b hb rr hpr).1
                        obtain ⟨rA, hrAmem, ⟨ipA, hrdA⟩, nEnt, hEntReach, hEntEq⟩ :=
                          extractAAddress_entitled_model hawAll hαns hA

                        -- lift the sub-verdict at the chase end nF back to the NS host nsQ
                        -- (prepending the cache-CNAME links), cache-preserving
                        rw [show αTime state.now = now from htm] at hcontS
                        obtain ⟨cBig, -, hcBigEq, nsTr, nsPath, nsEnd, respBig, hnsresB, hragBig⟩ :=
                          hcontS c (CacheRefines.refl c) vSub slistSub coutMSub hVsub
                            { vSub with answer := linksS ++ vSub.answer } rfl rfl
                        have hcBigC : cBig = c := by rcases hcBigEq with h | h <;> exact h
                        rw [hcBigC] at hnsresB

                        have hrABig : rA ∈ respBig.answer := by
                          refine hragBig.2.mem_iff.mp ?_
                          show rA ∈ linksS ++ vSub.answer
                          rw [← hansSub']
                          exact hrAmem
                        have hEntBig : VeriDNS.Spec.Net.CnameReachable nsQ respBig.answer nEnt := by
                          apply VeriDNS.Spec.Net.cnameReachable_of_subset
                            (fun r hr => hragBig.2.subset hr)
                          show VeriDNS.Spec.Net.CnameReachable nsQ (linksS ++ vSub.answer) nEnt
                          rw [← hansSub']
                          exact hEntReach
                        obtain ⟨nsAddrM, hnsaddr⟩ :=
                          VeriDNS.Spec.Net.addressOf_isSome_of_entitled hrABig hrdA hEntBig hEntEq

                        obtain ⟨zoneA, cprovA, hancA, hnsA⟩ :=
                          gluelessNs_anchor_witness nsQ now q.qname

                        cases hgr : Server.gluelessRecheck state subCache with
                        | some hit =>
                          simp only [hgr] at hrunK'
                          rw [run_pure'] at hrunK'
                          simp only [Option.some.injEq, Prod.mk.injEq,
                            Except.ok.injEq] at hrunK'
                          obtain ⟨⟨hhit, hcoutEq⟩, hwEq⟩ := hrunK'
                          subst hhit
                          subst hcoutEq
                          subst hwEq
                          obtain ⟨hsome, -⟩ := gluelessRecheck_cases state subCache q₀L quL
                            hlqL hquL
                          rcases hsome hit hgr with ⟨rc, hlkN, hhitEq⟩ |
                            ⟨hlkNone, hneA, hhitEq⟩
                          ·
                            obtain ⟨hnegT, hrcEq⟩ := lookupNegative_negHit_negResponse subCache
                              state.resources.sname quL.qtype quL.qclass state.now q tL rc
                              hlkN hsn htL hqqL hsnameCanon (fun x hx => (hqvalid x hx).2)
                              (by rw [hclsL]; exact hnegSub1)
                            have hnegT' : (αCache subCache).negHit now q = true := by
                              rw [← htm]
                              exact hnegT
                            refine ⟨[], { aa := false, rcode := αRCode rc, answer := [], authority := [], additional := [], ra := false, tc := false },
                              αCache subCache,
                              ⟨_, _, _, _,
                                Resolves.gluelessNs q zoneA nsQ nsAddrM [] [] slistSub nsTr
                                  nsPath nsEnd respBig [nsAddrM] _ _ _ _ c coutMSub
                                  (αCache subCache)
                                  hmiss hnmiss hancA cprovA hnsA (Nat.le_refl now) hnsresB hnsaddr
                                  (List.mem_singleton.mpr rfl) (αCache subCache) hcrSub
                                  (Resolves.negHit (αCache subCache) [nsAddrM] q hnegT'),
                                ⟨by
                                  show αRCode rc = (if (αCache subCache).negHitNx now q
                                    then RCode.nameError else RCode.noError)
                                  rw [← htm]
                                  exact hrcEq,
                                 by
                                  show List.Perm []
                                    ((αCache subCache).negResponse now q).answer
                                  exact List.Perm.refl _⟩⟩,
                              ?_, ?_,
                              (by rw [αCache_touchKeys]; exact CacheRefines.refl _),
                              WorldModels_oracle net ns ra ednsBuf now rfl hwm2,
                              CacheWf_touchKeys _ _ _ _ hwfS,
                              CacheNsCanon_touchKeys _ _ _ hnsS,
                              CacheCnameCanon_touchKeys _ _ _ hcnS,
                              wfrrAll_touchKeys _ _ hwfrrS,
                              ?_, CacheNsDistinct_touchKeys _ _ _ hnsdS,
                              VeriDNS.Proof.NameTree.oneExpiry_touchKeys _ _ hoeS,
                              (by rw [VeriDNS.Impl.Cache.touchKeys_records, Array.size_map]
                                  exact hcapS), by
                                rw [hhitEq]
                                exact answerWriteWf_finalize (by exact hAW) (answerWriteWf_empty _)⟩
                            · rw [hhitEq, finalizeAnswer_abstracts_rcode]
                              rfl
                            · rw [hhitEq, (αResp_components _).2.1, finalizeAnswer_answer,
                                αSection_prependChain]
                              rfl
                            · intro qu2 hqu2
                              obtain ⟨q02, hq02, hqu02⟩ := hqu2
                              rw [hlqL] at hq02
                              obtain rfl := Option.some.inj hq02
                              rw [hquL] at hqu02
                              obtain rfl := Option.some.inj hqu02
                              rw [hclsL]
                              exact CacheNegWf_touchKeys _ _ hnegSub1
                          ·
                            obtain ⟨heqHit, hlenHit⟩ := lookupAnswerable_hit_bridge subCache
                              state.resources.sname quL.qtype quL.qclass state.now q tL
                              hsn htL hqqL hqcL hsnameCanon (fun x hx => (hqvalid x hx).2)
                              hwfS hneA
                            have heqHit' : (subCache.lookupAnswerable state.resources.sname
                                quL.qtype quL.qclass state.now).toList.filterMap αRR
                                = (αCache subCache).hit now q := by
                              rw [← htm]
                              exact heqHit
                            have hlenHit' : 0 < ((αCache subCache).hit now q).length := by
                              rw [← htm]
                              exact hlenHit
                            have hwfrrs : ∀ rr ∈ (subCache.lookupAnswerable
                                state.resources.sname quL.qtype quL.qclass state.now),
                                VeriDNS.Proof.NameTree.WfRR rr := by
                              intro rr hrr
                              obtain ⟨e, he, -, hrre⟩ :=
                                lookupAnswerable_mem_entry (Array.mem_def.mp hrr)
                              rw [hrre]
                              exact VeriDNS.Proof.NameTree.wfRR_set_ttl (hwfrrS e he) _
                            refine ⟨[], { aa := false, rcode := RCode.noError, answer := (subCache.lookupAnswerable state.resources.sname quL.qtype quL.qclass state.now).toList.filterMap αRR, authority := [], additional := [], ra := false, tc := false },
                              αCache subCache,
                              ⟨_, _, _, _,
                                Resolves.gluelessNs q zoneA nsQ nsAddrM [] [] slistSub nsTr
                                  nsPath nsEnd respBig [nsAddrM] _ _ _ _ c coutMSub
                                  (αCache subCache)
                                  hmiss hnmiss hancA cprovA hnsA (Nat.le_refl now) hnsresB hnsaddr
                                  (List.mem_singleton.mpr rfl) (αCache subCache) hcrSub
                                  (Resolves.cacheHit (αCache subCache) [nsAddrM] q _ rfl
                                    hlenHit'),
                                ⟨rfl, by
                                  show List.Perm _ ((αCache subCache).hit now q)
                                  rw [heqHit']⟩⟩,
                              ?_, ?_,
                              (by rw [αCache_touchKeys]; exact CacheRefines.refl _),
                              WorldModels_oracle net ns ra ednsBuf now rfl hwm2,
                              CacheWf_touchKeys _ _ _ _ hwfS,
                              CacheNsCanon_touchKeys _ _ _ hnsS,
                              CacheCnameCanon_touchKeys _ _ _ hcnS,
                              wfrrAll_touchKeys _ _ hwfrrS,
                              ?_, CacheNsDistinct_touchKeys _ _ _ hnsdS,
                              VeriDNS.Proof.NameTree.oneExpiry_touchKeys _ _ hoeS,
                              (by rw [VeriDNS.Impl.Cache.touchKeys_records, Array.size_map]
                                  exact hcapS), by
                                rw [hhitEq]
                                refine answerWriteWf_finalize (by exact hAW) ?_
                                show AnswerWriteWf ((subCache.lookupAnswerable state.resources.sname
                                    quL.qtype quL.qclass state.now).map
                                  (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))) state.now
                                exact answerWriteWf_lookup_map hwfS hnsS hcnS hwfrrS⟩
                            · rw [hhitEq, finalizeAnswer_abstracts_rcode]
                              rfl
                            · rw [hhitEq, (αResp_components _).2.1, finalizeAnswer_answer,
                                αSection_prependChain,
                                show (Resolver.cacheResponse q₀L (subCache.lookupAnswerable
                                    state.resources.sname quL.qtype quL.qclass
                                    state.now)).answer
                                  = (subCache.lookupAnswerable state.resources.sname quL.qtype
                                      quL.qclass state.now).map
                                      (VeriDNS.Spec.RRParse.rrBytes
                                        (RR := VeriDNS.Spec.ResourceRecord)) from rfl,
                                αSection_map_rrBytes_wf _ hwfrrs]
                            · intro qu2 hqu2
                              obtain ⟨q02, hq02, hqu02⟩ := hqu2
                              rw [hlqL] at hq02
                              obtain rfl := Option.some.inj hq02
                              rw [hquL] at hqu02
                              obtain rfl := Option.some.inj hqu02
                              rw [hclsL]
                              exact CacheNegWf_touchKeys _ _ hnegSub1
                        | none =>

                          simp only [hgr] at hrunK'
                          obtain ⟨-, hnone⟩ := gluelessRecheck_cases state subCache q₀L quL
                            hlqL hquL
                          obtain ⟨hlkNone, hansEmpty⟩ := hnone hgr
                          have hmissC : (αCache subCache).hit now q = [] := by
                            rw [← htm]
                            exact hit_nil_of_lookupAnswerable_empty subCache
                              state.resources.sname quL.qtype quL.qclass state.now q tL
                              hansEmpty hsn htL hqqL hqcL hsnameCanon
                              (fun x hx => (hqvalid x hx).2) hwfS
                          have hnmissC : (αCache subCache).negHit now q = false := by
                            rw [← htm]
                            exact lookupNegative_none_negHit_false subCache
                              state.resources.sname quL.qtype quL.qclass state.now q tL
                              htL hqqL hsnameCanon (fun x hx => (hqvalid x hx).2)
                              (by rw [hclsL]; exact hnegSub1) hlkNone
                          obtain ⟨slistR, v, coutMR, hVrec, -, hrcR, hansR, hrestR⟩ :=
                            IH m2 (by omega) q depth' f _
                              { state with resources := { state.resources with
                                  slist := state.resources.slist.addAddress nsName addr,
                                  cache := subCache.touchKeys (Server.recheckTouches state)
                                    state.now } }
                              (αCache subCache) _ w' now nseen seen depthFloor resp cout
                              (by
                                refine ⟨?_, hsn, htm,
                                  WorldModels_oracle net ns ra ednsBuf now rfl hwm2⟩
                                rw [αCache_touchKeys]
                                exact MatchMaxEquiv.refl _)
                              (by exact WorldModelsTcp_tcpOracle net ns ra ednsBuf now htcpO2 hwmTcp)
                              (by exact CacheWf_touchKeys _ _ _ _ hwfS)
                              (by exact CacheNsCanon_touchKeys _ _ _ hnsS)
                              (by exact CacheCnameCanon_touchKeys _ _ _ hcnS)
                              (by exact wfrrAll_touchKeys _ _ hwfrrS)
                              (by
                                intro qu2 hqu2
                                obtain ⟨q02, hq02, hqu02⟩ := hqu2
                                have hq02' : state.lastQuery = some q02 := hq02
                                rw [hlqL] at hq02'
                                obtain rfl := Option.some.inj hq02'
                                rw [hquL] at hqu02
                                obtain rfl := Option.some.inj hqu02
                                rw [hclsL]
                                exact CacheNegWf_touchKeys _ _ hnegSub1)
                              (by exact CacheNsDistinct_touchKeys _ _ _ hnsdS)
                              (by exact VeriDNS.Proof.NameTree.oneExpiry_touchKeys _ _ hoeS)
                              (by
                                rw [VeriDNS.Impl.Cache.touchKeys_records, Array.size_map]
                                exact hcapS)
                              hmissC hnmissC hfreshInv (by exact hMC)
                              (by exact GluelessProv_addAddress nsName addr hGlProv)
                              (by exact hGlBelt) (by exact hqm) hrd hqstar hqin
                              (by exact hclock) (by exact hsnameCanon) (by exact hqlen)
                              (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrunK'
                          obtain ⟨ftrR, rpathR, tEndR, respFR, hrecRes, hragR⟩ := hVrec
                          exact ⟨[], v, coutMR,
                            ⟨_, _, _, _,
                              Resolves.gluelessNs q zoneA nsQ nsAddrM [] [] slistSub nsTr
                                nsPath nsEnd respBig (nsAddrM :: slistR) _ _ _ _ c coutMSub
                                coutMR
                                hmiss hnmiss hancA cprovA hnsA (Nat.le_refl now) hnsresB hnsaddr
                                (List.mem_cons_self ..) (αCache subCache) hcrSub
                                (Resolves.timeout nsAddrM slistR q ftrR rpathR tEndR respFR
                                  (αCache subCache) coutMR default
                                  (VeriDNS.Spec.Net.Transit.lost nsAddrM ra default)
                                  (Nat.le_refl now) hrecRes),
                              hragR⟩,
                            hrcR, (by exact hansR), hrestR⟩
                | error msg =>

                  rw [hres] at hrun
                  have hrun' : Prog.run m1 ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
                      state.resources.slist nsName (Except.error msg)) >>= fun slist' =>
                      Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                        { state with resources := { state.resources with slist := slist' } }
                        deadline depth' f revealed) _
                      = some ((Except.ok resp, cout), w') := hrun
                  unfold Server.gluelessUpdatedSlist at hrun'
                  simp only [Prog.bind_def, Prog.bind_assoc] at hrun'
                  rw [← Prog.bind_def] at hrun'
                  obtain ⟨m2, hm2, hrun'⟩ := run_log_bind_inv _ _ _ hrun'
                  obtain ⟨s, v, cM, hrec, -, hrc, hans, hrest⟩ := IH m2 (by omega) q depth' f _
                    { state with resources := { state.resources with
                        slist := state.resources.slist.removeServer nsName,
                        cache := state.resources.cache } }
                    c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_removeServer nsName hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun'
                  exact ⟨s, v, cM, hrec, hrc, hans, hrest⟩
          | some entryIp =>
            obtain ⟨entry, ipAddr⟩ := entryIp
            rw [hbest] at hrun
            have hmemM : byteAddrToModel (Server.ipv4ToAddr ipAddr) ∈ modelSlistOf state.resources.slist :=
              bestWithAddress_mem_modelSlistOf state.resources.slist hbest
            have hpermAns : (byteAddrToModel (Server.ipv4ToAddr ipAddr) ::
                (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))).Perm
                (modelSlistOf state.resources.slist) := (List.perm_cons_erase hmemM).symm
            cases hbuild : Resolver.buildSubQuery state revealed with
            | none => simp only [hbuild, run_pure'] at hrun; exact absurd hrun (by simp)
            | some subQuery0 =>
              simp only [hbuild] at hrun

              by_cases hblk : Server.blockedEgress ipAddr = true
              · simp only [hblk, if_true] at hrun
                rcases m with _ | _ | _ | _ | m'
                · obtain ⟨_, h1, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, -⟩ := run_randomId_bind_inv _ _ hrun; omega
                · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨_, h3, -⟩ := run_log_bind_inv _ _ _ hrun; omega
                · obtain ⟨a1, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  obtain ⟨a2, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨a2c, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                  obtain ⟨a3, h3, hrun⟩ := run_log_bind_inv _ _ _ hrun
                  have ham : a3 = m' := by omega
                  rw [ham] at hrun
                  obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH m' (by omega) q depth f _
                    { state with resources := { state.resources with
                        slist := state.resources.slist.markQueried entry.name } }
                    c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                  exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
              simp only [Bool.not_eq_true] at hblk
              simp only [hblk, Bool.false_eq_true, if_false] at hrun

              rcases m with _ | _ | _ | _ | m'
              · obtain ⟨_, h1, -⟩ := run_log_bind_inv _ _ _ hrun; omega
              · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨_, h2, -⟩ := run_randomId_bind_inv _ _ hrun; omega
              · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨_, h2c, -⟩ := run_randomId_bind_inv _ _ hrun; omega
              · obtain ⟨_, h1, hrun⟩ := run_log_bind_inv _ _ _ hrun
                obtain ⟨_, h2, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨_, h2c, hrun⟩ := run_randomId_bind_inv _ _ hrun
                obtain ⟨_, h3⟩ := run_forwardQuery_bind_inv _ _ _ _ hrun; omega
              · cases hO : w.oracle (VeriDNS.Impl.Message.encode
                    (Server.withSecrets subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
                    (Server.ipv4ToAddr ipAddr) with
                | none =>
                  rw [run_round_bind_eq_none _ _ _ _ _ hO] at hrun
                  simp only [] at hrun
                  obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH m' (by omega) q depth f _
                    { state with resources := { state.resources with
                        slist := state.resources.slist.markQueried entry.name } }
                    c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                  exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                | some d =>
                  cases ha : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d with
                  | none =>
                    rw [run_round_bind_eq_acceptNone _ _ _ _ _ d hO ha] at hrun
                    simp only [] at hrun
                    obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH m' (by omega) q depth f _
                      { state with resources := { state.resources with
                          slist := state.resources.slist.markQueried entry.name } }
                      c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                    exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                  | some bytes =>
                    cases hdec : VeriDNS.Impl.Message.decode bytes with
                    | error errmsg =>
                      rw [run_round_bind_eq_decodeError _ _ _ _ _ d bytes errmsg hO ha hdec] at hrun
                      simp only [] at hrun
                      obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH m' (by omega) q depth f _
                        { state with resources := { state.resources with
                            slist := state.resources.slist.markQueried entry.name } }
                        c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                      exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                    | ok resp0 =>
                      rw [run_round_bind_eq _ _ _ _ _ d bytes resp0 hO ha hdec] at hrun
                      cases hsani : Server.sanitizeTtlsCap resp0 with
                      | none =>
                        simp only [hsani] at hrun
                        obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH m' (by omega) q depth f _
                          { state with resources := { state.resources with
                              slist := state.resources.slist.markQueried entry.name } }
                          c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                        exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                      | some respS =>
                        simp only [hsani] at hrun
                        cases haccR : Server.acceptResponse
                            (Server.withSecrets subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1))) respS with
                        | none =>

                          simp only [haccR] at hrun
                          obtain ⟨mr, hmr, hrun⟩ := run_log_bind_inv _ _ _ hrun
                          obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mr (by omega) q depth f _
                            { state with resources := { state.resources with
                                slist := state.resources.slist.markQueried entry.name } }
                            c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                          exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                        | some respA =>
                          simp only [haccR] at hrun
                          obtain ⟨ml, hml, hrun⟩ := run_log_bind_inv _ _ _ hrun
                          by_cases htcT : (respA.header.tc == 1) = true
                          case pos =>
                            rw [if_pos htcT] at hrun
                            rcases run_tcpFallbackGuard_inv _ _ _ _ _ hrun with
                              ⟨mF, hmF, hrun⟩ |
                              ⟨mD, bytes2, raw2, tcpResp, tcpRespA, hmD, hOr, hdec2, hsan2, hacc2, htc0, hrun⟩
                            ·
                              dsimp only [] at hrun
                              obtain ⟨mFl, hmFl, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mFl (by omega) q depth f _
                                { state with resources := { state.resources with
                                    slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_removeServer entry.name (GluelessProv_markQueried entry.name hGlProv)) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                              have hpart := modelSlistOf_removeServer_perm
                                (state.resources.slist.markQueried entry.name) entry.name
                              rw [modelSlistOf_markQueried] at hpart
                              obtain ⟨l, hp, hsl⟩ := hperm
                              exact ⟨_, v, cM, hasVerdictAt_timeout_prepend net ns ra ednsBuf rttOf c q v cM _ hrec,
                                ⟨_ ++ l, (hp.append_left _).trans hpart.symm, hsl.append_left _⟩, hrc, hans, hrest⟩
                            ·
                              dsimp only [] at hrun
                              by_cases hunf : Server.unfollowableDelegationB
                                  (state.resources.slist.markQueried entry.name) state.resources.sname tcpRespA = true
                              · simp only [hunf, if_true] at hrun
                                obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mu (by omega) q depth f _
                                  { state with resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name } }
                                  c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                                exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                              · rw [if_neg hunf] at hrun
                                by_cases hfeT : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                    && !state.noEdns) = true
                                case pos =>
                                  -- RFC 6891 §6.2.2 (finding 055): FORMERR to an OPT-bearing sub-query —
                                  -- retry without EDNS; an IH recursion with the noEdns flag set.
                                  rw [if_pos hfeT] at hrun
                                  obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mf (by omega) q depth f _
                                    { state with
                                      resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name },
                                      noEdns := true }
                                    c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                                  exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                                rw [if_neg hfeT] at hrun
                                by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                    && Server.strictDenialB tcpRespA) = true
                                case pos =>
                                  -- RFC 9156 §2.3 relaxed fallback (findings 051/064): a minimised-probe
                                  -- NXDOMAIN is consumed and the loop re-probes with the full qname; no
                                  -- verdict is delivered here, so this is an IH recursion like probe-consume.
                                  rw [if_pos hstT] at hrun
                                  obtain ⟨ms, hms, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH ms (by omega) q depth f _
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                                  exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                                rw [if_neg hstT] at hrun
                                by_cases hpgT : (Resolver.probeRoundB state.resources.sname revealed
                                    && !Server.probePassableB tcpRespA) = true
                                case pos =>
                                  rw [if_pos hpgT] at hrun
                                  obtain ⟨mq, hmq, hrun⟩ := run_log_bind_inv _ _ _ hrun
                                  obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mq (by omega) q depth f _
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                                  exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                                rw [if_neg hpgT] at hrun
                                rw [Bool.not_eq_true] at hpgT
                                split at hrun
                                ·
                                  rename_i result cacheR hAR
                                  rw [run_pure'] at hrun
                                  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                                  obtain ⟨⟨hres, hcoutEq⟩, hwEq⟩ := hrun
                                  subst hres
                                  subst hcoutEq
                                  subst hwEq
                                  obtain ⟨hmme, hsn, htm, hwm⟩ := hSM
                                  have hfull : Resolver.probeRoundB state.resources.sname revealed = false := by
                                    cases hpr : Resolver.probeRoundB state.resources.sname revealed
                                    · rfl
                                    · rw [hpr, afterResume_finished_probePassable_false
                                          (state := { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } })
                                          (by exact hstep) hAR] at hpgT
                                      exact absurd hpgT (by decide)
                                  have hαQ : αQuery subQuery0 = some q :=
                                    αQuery_buildSubQuery hbuild hfull hsn hqm hrd
                                  obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, _hisrefS, _htcS,
                                      hauthS, hvalidAnsW, hvldA, hrefImplS⟩ :=
                                    tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0
                                      (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr)
                                      bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0
                                      (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                  have hrespAeqW : tcpRespA = tcpResp := acceptResponse_some_eq hacc2
                                  have hcanonAnsW : ∀ raw ∈ tcpRespA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                    intro raw hmem
                                    have hcapAnsW : tcpRespA.answer = raw2.answer.map Server.capTtlRR := by
                                      rw [hrespAeqW, show tcpResp = Server.capTtls (Edns.stripOpt raw2) from by
                                        unfold Server.sanitizeTtlsCap at hsan2
                                        exact (Option.some.inj hsan2).symm]
                                      rfl
                                    rw [hcapAnsW, Array.toList_map, List.mem_map] at hmem
                                    obtain ⟨b0, hb0, rfl⟩ := hmem
                                    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                      (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                  have hAWwire : AnswerWriteWf tcpRespA.answer state.now :=
                                    answerWriteWf_of_wire hsan2 hrespAeqW hclock hvalidAnsW hcanonAnsW
                                  by_cases hansI : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = true
                                  ·
                                    have hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = none := by
                                      simp only [Resolver.cnameToChase, hansI, if_true]
                                    have hstepM : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := hstep
                                    have hnotbiz := afterResume_finished_not_bizarre hstepM hcn hAR

                                    have htcF : (tcpRespA.header.tc == 1) = false := htc0
                                    have hentF : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = true :=
                                      entitled_of_afterResume_finished_okTc hstepM hcn hnotbiz.1 hnotbiz.2 htcF hansI hAR
                                    have hcoutB : cacheR = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).boundLru
                                        (Server.roundTouches { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now :=
                                      (afterResume_answer_payload_pos_ent _ entry.name tcpRespA resp hstepM hcn hnotbiz.1 hnotbiz.2 hentF hAR).2
                                    subst hcoutB
                                    have hqm2 := acceptResponse_questionMatches hacc2
                                    by_cases htcT : (tcpRespA.header.tc == 1) = true
                                    · rw [htc0] at htcT; exact absurd htcT (by decide)
                                    ·
                                      rw [Bool.not_eq_true] at htcT
                                      have hvalidAns := hvalidAnsW
                                      have hvalW : ∀ b ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.echoedQname tcpRespA) tcpRespA.answer).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hvalidAns b (ownerRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hrespAeq : tcpRespA = tcpResp := acceptResponse_some_eq hacc2
                                      have hnoW : ∀ b ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.echoedQname tcpRespA) tcpRespA.answer).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ tcpResp.answer := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (ownerRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                          (Or.inl (Or.inl hb')) rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hcapEq : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                        unfold Server.sanitizeTtlsCap at hsan2
                                        exact (Option.some.inj hsan2).symm
                                      have hcapAns : tcpRespA.answer = raw2.answer.map Server.capTtlRR := by
                                        rw [hrespAeq, hcapEq]; rfl
                                      have hcanonAns : ∀ raw ∈ tcpRespA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                        intro raw hmem
                                        rw [hcapAns, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                          (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                      have hwfW : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) state.now := by
                                        refine CacheWf_cacheUnlessTruncated _ _ _ _ _ hCacheWf ?_ ?_
                                        · unfold Resolver.credAnswer
                                          by_cases ha' : (tcpRespA.header.aa == 1) = true
                                          · rw [if_pos ha']; exact Or.inl rfl
                                          · rw [if_neg ha']; exact Or.inr (Or.inr (Or.inl rfl))
                                        · intro raw hraw rr hp
                                          exact parseRaw_entry_canonical _ state.now hp (normRaws_hval hvalW raw hraw rr hp) (normRaws_hno hnoW raw hraw rr hp)
                                      have hCnW : CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) := by
                                        refine CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hCnCanon ?_
                                        intro raw hraw rr hp htype
                                        exact canonicalRR_cnameRdata_canonical (hcanonAns raw (ownerRaws_toList_sub hraw)) hp htype
                                      have hwfrrW : ∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).records,
                                          VeriDNS.Proof.NameTree.WfRR e.rr :=
                                        wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
                                      have hNsW : CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) := by
                                        refine CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hNsCanon ?_
                                        intro raw hraw rr hp htype
                                        exact canonicalRR_nsRdata_canonical (hcanonAns raw (ownerRaws_toList_sub hraw)) hp htype
                                      have hNsDW : CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) :=
                                        CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hNsDistinct
                                      have hOEW : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) :=
                                        VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hOE _ _ _ _
                                      obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                        cout_exports_bound (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)
                                          state.now
                                          (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                          (Server.roundTouches { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now
                                          hwfW hNsW hCnW hwfrrW hNsDW hOEW (MatchMaxEquiv.refl _)
                                      have hnegE : ∀ qu2 : VeriDNS.Spec.Question,
                                          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                          CacheNegWf ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).boundLru
                                            (Server.roundTouches { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now) qu2.qclass :=
                                        fun qu2 hqu2 => CacheNegWf_boundLru _ _
                                          (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu2 hqu2))

                                      obtain ⟨q₀W, quW, hq0W, hqu0W, hsubqW⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                      rw [subQuestion_full hfull quW] at hsubqW
                                      obtain ⟨qaW, hqaW, hqaCIW, -, -⟩ := questionMatches_fields
                                        (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubqW)
                                            (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                        (acceptResponse_questionMatches hacc2)
                                      have hcf0 := answer_write_WriteRefines_echo state.resources.cache tcpRespA qaW state.resources.sname
                                        q.qname state.now hqaW (question_from_decode hdec2 hsan2 (acceptResponse_some_eq hacc2) hqaW)
                                        hqaCIW hsn htcT hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                        ({ aa := (tcpRespA.header.aa == 1), rcode := αRCode tcpRespA.header.rcode,
                                           answer := αSection tcpRespA.answer, authority := [], additional := [],
                                           ra := false, tc := false } : VeriDNS.Spec.Net.Response) c rfl rfl hmme
                                      rw [show state.now.toNat = now from htm] at hcf0
                                      have hragSyn : RespAgree (αResp tcpRespA)
                                          ({ aa := (tcpRespA.header.aa == 1), rcode := αRCode tcpRespA.header.rcode,
                                             answer := αSection tcpRespA.answer, authority := [], additional := [],
                                             ra := false, tc := false } : VeriDNS.Spec.Net.Response) := by
                                        refine ⟨(αResp_components tcpRespA).1, ?_⟩
                                        rw [(αResp_components tcpRespA).2.1]
                                      obtain ⟨r, hrmem, -⟩ := positive_answer_covered hαQ hqm2 hansI hvalidAns hragSyn
                                      have hnrSyn := isReferral_false_of_answer_ne_nil _ (List.ne_nil_of_mem hrmem)
                                      obtain ⟨org, hreach⟩ : ∃ org : String, linkReach net ns ra org = true := by
                                        cases htrans with
                                        | deliver hro _ => exact ⟨origin, hro⟩
                                      by_cases hch : state.cnameChain = #[]
                                      · have hchainM : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).cnameChain = #[] := hch
                                        have hbridge : RespAgree (αResp resp)
                                            { ({ aa := (tcpRespA.header.aa == 1), rcode := αRCode tcpRespA.header.rcode,
                                                 answer := αSection tcpRespA.answer, authority := [], additional := [],
                                                 ra := false, tc := false } : VeriDNS.Spec.Net.Response) with aa := false } :=
                                          respAgree_answer_bridge hstepM hcn hnotbiz.1 hnotbiz.2 hansI hAR hchainM hragSyn
                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp),
                                          αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now),
                                          trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) org
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            (w.ids w.idCtr).toNat 0 c
                                            (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                                (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                              { aa := (tcpRespA.header.aa == 1), rcode := αRCode tcpRespA.header.rcode,
                                                answer := αSection tcpRespA.answer, authority := [], additional := [],
                                                ra := false, tc := false })
                                            hmiss hnmiss
                                            (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                            (accepts_reply _ _ _ _ _ _ _)
                                            hnrSyn rfl
                                            (αResp resp) hbridge
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                              (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                            (Or.inl hcf0)
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                              (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                            (WriteRefines.refl now _),
                                          hpermAns.symm.subperm, rfl,
                                          by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [(afterResume_finished_payload_out _ entry.name tcpRespA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                            exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                      ·

                                        have hout : resp = Resolver.finalizeAnswer
                                            { { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                              with lastResponse := some tcpRespA, currentStep := .analyzeResponse } tcpRespA :=
                                          afterResume_finished_payload_out
                                            { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR
                                        have hrcP : (αResp resp).rcode = αRCode tcpRespA.header.rcode := by
                                          rw [hout]; exact finalizeAnswer_abstracts_rcode _ tcpRespA
                                        have hansP : (αResp resp).answer
                                            = αSection ({ { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                              with lastResponse := some tcpRespA, currentStep := .analyzeResponse } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord).cnameChain
                                            ++ αSection tcpRespA.answer := by
                                          rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
                                        have hbridge2 : RespAgree (αResp tcpRespA)
                                            { ({ aa := (tcpRespA.header.aa == 1), rcode := αRCode tcpRespA.header.rcode,
                                                 answer := αSection tcpRespA.answer, authority := [], additional := [],
                                                 ra := false, tc := false } : VeriDNS.Spec.Net.Response) with aa := false } := by
                                          refine ⟨(αResp_components tcpRespA).1, ?_⟩
                                          rw [(αResp_components tcpRespA).2.1]
                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp tcpRespA,
                                          αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now),
                                          trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) org
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            (w.ids w.idCtr).toNat 0 c
                                            (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                                (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                              { aa := (tcpRespA.header.aa == 1), rcode := αRCode tcpRespA.header.rcode,
                                                answer := αSection tcpRespA.answer, authority := [], additional := [],
                                                ra := false, tc := false })
                                            hmiss hnmiss
                                            (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                            (accepts_reply _ _ _ _ _ _ _)
                                            hnrSyn rfl
                                            (αResp tcpRespA) hbridge2
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                              (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                            (Or.inl hcf0)
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                              (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                            (WriteRefines.refl now _),
                                          hpermAns.symm.subperm,
                                          hrcP.trans (αResp_components tcpRespA).1.symm,
                                          by rw [(αResp_components tcpRespA).2.1]; exact hansP,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [(afterResume_finished_payload_out _ entry.name tcpRespA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                            exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                  ·
                                    by_cases hcn2 : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = none
                                    · have hstepM2 : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := hstep
                                      have hnotbiz2 := afterResume_finished_not_bizarre hstepM2 hcn2 hAR
                                      have hansF0 : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = false := by
                                        simpa using hansI

                                      have hcoutB : cacheR = state.resources.cache.boundLru
                                          (Server.roundTouches { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now :=
                                        (afterResume_finished_payload_neg _ entry.name tcpRespA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR).2
                                      subst hcoutB
                                      obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                        cout_exports_bound state.resources.cache state.now c
                                          (Server.roundTouches { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now
                                          hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hmme
                                      have hnegE : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          CacheNegWf (state.resources.cache.boundLru
                                            (Server.roundTouches { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now) qu.qclass :=
                                        fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu')
                                      by_cases hch2 : state.cnameChain = #[]
                                      · have hchainM2 : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).cnameChain = #[] := hch2
                                        have hspoof := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                        obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, hclsLink, htcR, _hauthS, hvld, hvldA, _hrefImpl⟩ := hspoof
                                        have hansF : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = false := by simpa using hansI
                                        have hirref : (αResp tcpRespA).isReferral = false :=
                                          αResp_isReferral_false_of_finished hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF hAR hvld hvldA
                                        have hnrR : reply.msg.isReferral = false := by rw [← hclsLink]; exact hirref
                                        have hbridge : RespAgree (αResp resp) { reply.msg with aa := false } :=
                                          respAgree_finished_bridge hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hAR hchainM2 hragS
                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp), c,
                                          trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            (w.ids w.idCtr).toNat srcPort c reply hmiss hnmiss htrans hacc hnrR htcR
                                            (αResp resp) hbridge
                                            c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, rfl,
                                          by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [(afterResume_finished_payload_neg _ entry.name tcpRespA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR).1]
                                            exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                      ·

                                        have hpay := afterResume_finished_payload_neg
                                          { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          entry.name tcpRespA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR
                                        have hrcD : (αResp resp).rcode = (αResp tcpRespA).rcode := by
                                          rw [hpay.1]; exact (finalizeAnswer_abstracts_rcode _ tcpRespA).trans (αResp_components tcpRespA).1.symm
                                        have hansD2 : (αResp resp).answer = αSection state.cnameChain ++ (αResp tcpRespA).answer := by
                                          rw [hpay.1, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, (αResp_components tcpRespA).2.1]
                                        have hansF : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = false := by simpa using hansI
                                        have hspoof := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                        obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, hclsLink, htcR, _hauthS, hvld, hvldA, _hrefImpl⟩ := hspoof
                                        have hirref : (αResp tcpRespA).isReferral = false :=
                                          αResp_isReferral_false_of_finished hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF hAR hvld hvldA
                                        have hnrR : reply.msg.isReferral = false := by rw [← hclsLink]; exact hirref
                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp tcpRespA, c,
                                          trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            (w.ids w.idCtr).toNat srcPort c reply hmiss hnmiss htrans hacc hnrR htcR
                                            (αResp tcpRespA) hragS
                                            c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, hrcD, hansD2,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [hpay.1]
                                            exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                    ·

                                      obtain ⟨target, hcnT⟩ := Option.ne_none_iff_exists'.mp hcn2
                                      obtain ⟨q₀L, quL, hq0, hqu0, hsubq⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                      rw [subQuestion_full hfull quL] at hsubq
                                      have hqmL := hqm quL ⟨q₀L, hq0, hqu0⟩
                                      obtain ⟨qaR, hqaR, hqaCI, hqaT, _hqaC⟩ := questionMatches_fields
                                        (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubq)
                                            (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                        (acceptResponse_questionMatches hacc2)
                                      have hqt : q.qtype.covers RRType.cname = false :=
                                        covers_cname_false_of_chase tcpRespA target qaR q hcnT hqaR
                                          (by rw [hqaT]; exact hqmL.1) hqstar
                                      obtain ⟨t, ht, hqq⟩ := αQType_rr_inv hqmL.1 hqstar
                                      have htne : t ≠ RRType.cname := by
                                        intro hteq
                                        rw [hqq, hteq] at hqt
                                        exact absurd hqt (by decide)
                                      by_cases htcT : (tcpRespA.header.tc == 1) = true
                                      · rw [htc0] at htcT; exact absurd htcT (by decide)
                                      rw [Bool.not_eq_true] at htcT
                                      obtain ⟨hnrev, hdisj⟩ := afterResume_cname_ok_inv
                                        { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                        entry.name tcpRespA q₀L target quL resp hstep hcnT htcT hq0 hqu0 hAR
                                      have hvalidAns := hvalidAnsW
                                      have hrespAeq : tcpRespA = tcpResp := acceptResponse_some_eq hacc2
                                      have hcapEq : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                        unfold Server.sanitizeTtlsCap at hsan2
                                        exact (Option.some.inj hsan2).symm
                                      have hcapAns : tcpRespA.answer = raw2.answer.map Server.capTtlRR := by
                                        rw [hrespAeq, hcapEq]; rfl
                                      have hquesEq : tcpRespA.question = raw2.question := by
                                        rw [hrespAeq, hcapEq]; rfl
                                      have hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR := by
                                        have hqaR0 : raw2.question[0]? = some qaR := by
                                          rw [← hquesEq]; exact hqaR
                                        obtain ⟨-, -, -, -, hqs, -, -, -⟩ :=
                                          VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec2
                                        rw [Array.getElem?_eq_some_iff] at hqaR0
                                        obtain ⟨hlt, hget⟩ := hqaR0
                                        exact hget ▸ hqs ⟨0, hlt⟩
                                      obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
                                      have hqnRq : VeriDNS.Spec.Net.nameEq qnR q.qname = true := by
                                        obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
                                        obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
                                        exact hne'
                                      obtain ⟨quE, hquE, hextQ⟩ := (cnameToChase_some tcpRespA target hcnT).2
                                      rw [show quE = qaR from Option.some.inj (hquE.symm.trans hqaR)] at hextQ
                                      obtain ⟨cnBytes, rrCn, cn, tgt, hextRR, hcnMem, hprC, hty5, hrdT, hαcn, hcnRR, hcnrd, hαtgt⟩ :=
                                        cname_link_facts hαR hcanR hvalR hextQ hvalidAns
                                      rw [VeriDNS.Spec.Net.cnameRR_congr hqnRq] at hcnRR
                                      have hcanonAns : ∀ raw ∈ tcpRespA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                        intro raw hmem
                                        rw [hcapAns, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                          (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                      obtain ⟨na0, hna0, hnacan0, hnaval0, hnalen0⟩ :=
                                        canonicalRR_cnameRdata_canonical (hcanonAns cnBytes hcnMem) hprC hty5
                                      have hna0tgt : na0 = tgt := by
                                        rw [hrdT] at hna0
                                        exact Option.some.inj (hna0.symm.trans hαtgt)
                                      rw [hna0tgt] at hnacan0 hnaval0 hnalen0
                                      have htB : target = VeriDNS.Impl.DomainName.labelsToWireFormatGo tgt := by
                                        rw [← hrdT]; exact hnacan0
                                      have hfresh : tgt ∉ q.qname :: nseen :=
                                        cname_target_fresh state q nseen target tgt hCCM htB hnaval0 hnrev
                                      have hvalW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.echoedQname tcpRespA) tcpRespA.answer).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hvalidAns b (cnameRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hnoW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.echoedQname tcpRespA) tcpRespA.answer).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ tcpResp.answer := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (cnameRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                          (Or.inl (Or.inl hb')) rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hwfW : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) state.now := by
                                        refine CacheWf_cacheUnlessTruncated _ _ _ _ _ hCacheWf ?_ ?_
                                        · unfold Resolver.credAnswer
                                          by_cases ha : (tcpRespA.header.aa == 1) = true
                                          · rw [if_pos ha]; exact Or.inl rfl
                                          · rw [if_neg ha]; exact Or.inr (Or.inr (Or.inl rfl))
                                        · intro raw hraw rr hp
                                          exact parseRaw_entry_canonical _ state.now hp (normRaws_hval hvalW raw hraw rr hp) (normRaws_hno hnoW raw hraw rr hp)
                                      have hCnW : CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) := by
                                        refine CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hCnCanon ?_
                                        intro raw hraw rr hp htype
                                        exact canonicalRR_cnameRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                      have hwfrrW : ∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).records,
                                          VeriDNS.Proof.NameTree.WfRR e.rr :=
                                        wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
                                      have hnegwfW : CacheNegWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) quL.qclass :=
                                        CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf quL ⟨q₀L, hq0, hqu0⟩)

                                      have hNsW : CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) := by
                                        refine CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hNsCanon ?_
                                        intro raw hraw rr hp htype
                                        exact canonicalRR_nsRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                      have hNsDW : CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) :=
                                        CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hNsDistinct
                                      have hOEW : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) :=
                                        VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hOE _ _ _ _
                                      obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                        cout_exports_bound (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)
                                          state.now
                                          (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                          (Server.roundTouches (Server.dropIfBizarre
                                            { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA) tcpRespA) state.now
                                          hwfW hNsW hCnW hwfrrW hNsDW hOEW (MatchMaxEquiv.refl _)
                                      have hnegE : ∀ qu2 : VeriDNS.Spec.Question,
                                          (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                          CacheNegWf ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).boundLru
                                            (Server.roundTouches (Server.dropIfBizarre
                                              { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                              entry.name tcpRespA) tcpRespA) state.now) qu2.qclass :=
                                        fun qu2 hqu2 => CacheNegWf_boundLru _ _
                                          (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu2 hqu2))
                                      have hanchor : ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim
                                          state.resources.sname (fun qu => qu.qname)) = quL.qname := by
                                        rw [hq0]
                                        show (q₀L.question[0]?).elim state.resources.sname (fun qu => qu.qname) = quL.qname
                                        rw [hqu0]
                                        rfl
                                      have hCCM' : ∀ nm ∈ q.qname :: nseen, ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                                          quL.qname state.cnameChain).toList,
                                          αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                            ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                        have h := hCCM
                                        unfold CnameChainModels at h
                                        rw [hanchor] at h
                                        exact h
                                      have hpre : Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA
                                          = state.cnameChain.push cnBytes := by
                                        unfold Resolver.prependCnameLink
                                        simp only [hqaR, hextRR]
                                      have hvtl : (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)).toList
                                          = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname state.cnameChain).toList
                                            ++ [VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn] := by
                                        rw [hpre]
                                        exact cnameChaseVisited_push quL.qname state.cnameChain hprC
                                      have hvis : ∀ nm ∈ tgt :: (q.qname :: nseen),
                                          ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)).toList,
                                          αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                            ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                        intro nm hnm
                                        rcases List.mem_cons.mp hnm with rfl | hnm
                                        · refine ⟨target, ?_, hαtgt, htB, hnaval0⟩
                                          rw [hvtl]
                                          refine List.mem_append_right _ ?_
                                          rw [show VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn
                                            = rrCn.rdata from rfl, hrdT]
                                          exact List.mem_singleton.mpr rfl
                                        · obtain ⟨b, hb, hf⟩ := hCCM' nm hnm
                                          refine ⟨b, ?_, hf⟩
                                          rw [hvtl]
                                          exact List.mem_append_left _ hb
                                      rcases hdisj with ⟨snameF, chainF, rrs, st, hla, hout, hstch, hcoutW⟩ |
                                        ⟨rc, soaAuth, chainF, st, hla, hout, hstch, hcoutW⟩
                                      ·
                                        obtain ⟨links, hchainF, hcont⟩ := localAnswer_chase_peel net ns ra ednsBuf rttOf
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)
                                          (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                          quL.qtype quL.qclass state.now q t [] quL.qname ht hqq htne hqmL.2
                                          (MatchMaxEquiv.refl _) hwfW hCnW hwfrrW hnegwfW 8 target tgt
                                          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)
                                          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA))
                                          (q.qname :: nseen) (.answerHit snameF chainF rrs) hla hαtgt htB hnaval0
                                          hnalen0 rfl hvis
                                        obtain ⟨hnegF, hansF, hneF⟩ := localAnswer_answerHit_inv _ quL.qtype quL.qclass
                                          state.now 8 target _ _ snameF chainF rrs hla
                                        have hrrsPr : ∀ rr ∈ rrs.toList, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
                                            (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr) = some rr := by
                                          intro rr hrr
                                          rw [← hansF] at hrr
                                          exact lookupAnswerable_parseRaw_rrBytes hwfrrW hrr
                                        have hsecRRS : αSection (Resolver.cacheResponse q₀L rrs).answer = rrs.toList.filterMap αRR :=
                                          αSection_map_rrBytes rrs hrrsPr
                                        have hanseq : (αResp resp).answer
                                            = αSection state.cnameChain ++ (cn :: (links ++ rrs.toList.filterMap αRR)) := by
                                          rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hstch,
                                            hchainF, αSection_prependCnameLink state.cnameChain tcpRespA qaR cnBytes rrCn cn hqaR hextRR hprC hαcn,
                                            hsecRRS]
                                          simp [List.append_assoc]
                                        have hrceq : (αResp resp).rcode = RCode.noError := by
                                          rw [hout, (αResp_components _).1, finalizeAnswer_rcode]
                                          rfl

                                        subst hcoutW
                                        have hcf0 := cname_link_write_WriteRefines_echo state.resources.cache tcpRespA qaR state.resources.sname
                                          q.qname state.now hqaR (question_from_decode hdec2 hsan2 (acceptResponse_some_eq hacc2) hqaR)
                                          hqaCI hsn htcT hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                          ({ aa := (tcpRespA.header.aa == 1), rcode := RCode.noError, answer := αSection tcpRespA.answer,
                                             authority := [], additional := [], ra := false, tc := false } : Response) c rfl rfl hmme
                                        rw [show state.now.toNat = now from htm] at hcf0
                                        have hv := hcont (Response.mk false RCode.noError (links ++ rrs.toList.filterMap αRR) [] [] false false)
                                          rfl rfl []
                                        rw [show αTime state.now = now from htm] at hv
                                        obtain ⟨ftr, rpath, tEnd2, respSub, hres, hagr⟩ := hv

                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                            :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                          Response.mk false RCode.noError (cn :: (links ++ rrs.toList.filterMap αRR)) [] [] false false,
                                          αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now),
                                          (by
                                            obtain ⟨origin, reply0, srcPort0, htransS, -⟩ := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                            have hreach : linkReach net ns ra origin = true := by
                                              cases htransS with
                                              | deliver hro hrr0 => exact hro
                                            exact trustedCname_hasVerdictAt net ns ra ednsBuf rttOf
                                              (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                              ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                              cn tgt (w.ids w.idCtr).toNat 0 c [] ftr rpath tEnd2
                                              (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                              respSub hmiss hnmiss
                                              (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                                  (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                                { aa := (tcpRespA.header.aa == 1), rcode := RCode.noError, answer := αSection tcpRespA.answer,
                                                  authority := [], additional := [], ra := false, tc := false })
                                              (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                              (accepts_reply _ _ _ _ _ _ _)
                                              hcnRR hqt hcnrd hfresh (Nat.le_refl now) rfl
                                              (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                              hcf0
                                              (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                              (WriteRefines.refl now _) hres
                                              (Response.mk false RCode.noError (cn :: (links ++ rrs.toList.filterMap αRR)) [] [] false false)
                                              ⟨hagr.1, List.Perm.cons cn hagr.2⟩),
                                          hpermAns.symm.subperm, hrceq, hanseq,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [hout]
                                            refine answerWriteWf_finalize ?_ ?_
                                            · rw [hstch]
                                              refine localAnswer_chain_answerWriteWf hwfW hNsW hCnW hwfrrW
                                                (congrArg chainOf hla) ?_
                                              rw [hpre]
                                              exact answerWriteWf_push hAW
                                                (fun rr hp => hAWwire cnBytes hcnMem rr hp)
                                            · have hrrs' : rrs = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                  (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                  (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).lookupAnswerable snameF quL.qtype quL.qclass state.now := by
                                                rw [← hansF]; rfl
                                              show AnswerWriteWf (rrs.map
                                                (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))) state.now
                                              rw [hrrs']
                                              exact answerWriteWf_lookup_map hwfW hNsW hCnW hwfrrW⟩
                                      ·
                                        obtain ⟨links, hchainF, hcont⟩ := localAnswer_chase_peel net ns ra ednsBuf rttOf
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)
                                          (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                          quL.qtype quL.qclass state.now q t [] quL.qname ht hqq htne hqmL.2
                                          (MatchMaxEquiv.refl _) hwfW hCnW hwfrrW hnegwfW 8 target tgt
                                          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)
                                          (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                            (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA))
                                          (q.qname :: nseen) (.negative rc soaAuth chainF) hla hαtgt htB hnaval0
                                          hnalen0 rfl hvis
                                        have hanseq : (αResp resp).answer
                                            = αSection state.cnameChain ++ (cn :: links) := by
                                          rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hstch,
                                            hchainF, αSection_prependCnameLink state.cnameChain tcpRespA qaR cnBytes rrCn cn hqaR hextRR hprC hαcn,
                                            show αSection (Resolver.negativeResponse q₀L rc soaAuth).answer = [] from rfl]
                                          simp [List.append_assoc]
                                        have hrceq : (αResp resp).rcode = αRCode rc := by
                                          rw [hout, (αResp_components _).1, finalizeAnswer_rcode]
                                          rfl

                                        subst hcoutW
                                        have hcf0 := cname_link_write_WriteRefines_echo state.resources.cache tcpRespA qaR state.resources.sname
                                          q.qname state.now hqaR (question_from_decode hdec2 hsan2 (acceptResponse_some_eq hacc2) hqaR)
                                          hqaCI hsn htcT hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                          ({ aa := (tcpRespA.header.aa == 1), rcode := RCode.noError, answer := αSection tcpRespA.answer,
                                             authority := [], additional := [], ra := false, tc := false } : Response) c rfl rfl hmme
                                        rw [show state.now.toNat = now from htm] at hcf0
                                        have hv := hcont (Response.mk false (αRCode rc) links [] [] false false) rfl rfl []
                                        rw [show αTime state.now = now from htm] at hv
                                        obtain ⟨ftr, rpath, tEnd2, respSub, hres, hagr⟩ := hv
                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                            :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                          Response.mk false (αRCode rc) (cn :: links) [] [] false false,
                                          αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now),
                                          (by
                                            obtain ⟨origin, reply0, srcPort0, htransS, -⟩ := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                            have hreach : linkReach net ns ra origin = true := by
                                              cases htransS with
                                              | deliver hro hrr0 => exact hro
                                            exact trustedCname_hasVerdictAt net ns ra ednsBuf rttOf
                                              (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                              ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                              cn tgt (w.ids w.idCtr).toNat 0 c [] ftr rpath tEnd2
                                              (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                              respSub hmiss hnmiss
                                              (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                                  (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                                { aa := (tcpRespA.header.aa == 1), rcode := RCode.noError, answer := αSection tcpRespA.answer,
                                                  authority := [], additional := [], ra := false, tc := false })
                                              (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                              (accepts_reply _ _ _ _ _ _ _)
                                              hcnRR hqt hcnrd hfresh (Nat.le_refl now) rfl
                                              (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                              hcf0
                                              (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                                (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                                (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                              (WriteRefines.refl now _) hres
                                              (Response.mk false (αRCode rc) (cn :: links) [] [] false false)
                                              ⟨hagr.1, List.Perm.cons cn hagr.2⟩),
                                          hpermAns.symm.subperm, hrceq, hanseq,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [hout]
                                            refine answerWriteWf_finalize ?_ (answerWriteWf_empty _)
                                            rw [hstch]
                                            refine localAnswer_chain_answerWriteWf hwfW hNsW hCnW hwfrrW
                                              (congrArg chainOf hla) ?_
                                            rw [hpre]
                                            exact answerWriteWf_push hAW
                                              (fun rr hp => hAWwire cnBytes hcnMem rr hp)⟩
                                ·
                                  rename_i state'' heqC
                                  obtain ⟨hmme, hsn, htm, hwm⟩ := hSM
                                  by_cases hprC : Resolver.probeRoundB state.resources.sname revealed = true
                                  case pos =>
                                    have hpassT : Server.probePassableB tcpRespA = true := by
                                      rw [hprC] at hpgT
                                      simpa using hpgT
                                    by_cases hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = none
                                    · by_cases hbiz : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
                                          || !Resolver.classifiableB tcpRespA) = true
                                      ·
                                        rw [afterResume_bizarre
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA hstep hcn hbiz] at heqC
                                        simp only [Server.dropIfBizarre, if_pos hbiz] at heqC
                                        have hst := Server.IoStep.continue.inj heqC
                                        subst hst
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mD (by omega) q depth f _
                                          (Server.boundStateCache
                                            (Server.roundTouches
                                              { state with resources := { state.resources with
                                                  slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                              tcpRespA)
                                            { resources :=
                                                { sname := state.resources.sname, stype := state.resources.stype,
                                                  sclass := state.resources.sclass,
                                                  slist := (state.resources.slist.markQueried entry.name).removeServer entry.name,
                                                  sbelt := state.resources.sbelt, cache := state.resources.cache },
                                              currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                              lastQuery := state.lastQuery, lastResponse := none,
                                              cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                          c _ w' now nseen seen depthFloor resp cout
                                          ⟨by
                                              show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                              rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                            hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                          (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                          (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                          (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                          (by exact wfrrAll_boundLru _ _ hwfrr)
                                          (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                          (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                          (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                          (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                          hmiss hnmiss hfreshInv (by exact hMC)
                                          (by exact GluelessProv_removeServer entry.name (GluelessProv_markQueried entry.name hGlProv))
                                          (by exact hGlBelt)
                                          hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                        have hpart := modelSlistOf_removeServer_perm
                                          (state.resources.slist.markQueried entry.name) entry.name
                                        rw [modelSlistOf_markQueried] at hpart

                                        obtain ⟨l, hp, hsl⟩ := hperm
                                        exact ⟨_, v, cM, hasVerdictAt_timeout_prepend net ns ra ednsBuf rttOf c q v cM _ hrec,
                                          ⟨_ ++ l, (hp.append_left _).trans hpart.symm, hsl.append_left _⟩, hrc, hans, hrest⟩
                                      · rw [Bool.not_eq_true] at hbiz
                                        obtain ⟨pq, hαQp, hSP⟩ := αQuery_buildSubQuery_probe hbuild hprC hsn hqm
                                        have hpqanc : isAncestor pq.qname q.qname = true := by
                                          obtain ⟨⟨cut, hpf⟩, -, -⟩ := hSP
                                          exact (VeriDNS.Proof.QnameMin.probeFor_facts hpf).2.1
                                        have hcls : Resolver.classifiableB tcpRespA = true := by
                                          have h := (Bool.or_eq_false_iff.mp hbiz).2; simpa using h
                                        have hsf : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false :=
                                          (Bool.or_eq_false_iff.mp hbiz).1
                                        obtain ⟨nsG, sG, hgoto⟩ := afterResume_continue_stepAnalyze_goto
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name tcpRespA state'' hstep hcn hsf hcls heqC
                                        rcases stepAnalyzeResponse_goto_cases
                                            ({ ({ state with resources := { state.resources with
                                                  slist := state.resources.slist.markQueried entry.name } }) with
                                              lastResponse := some tcpRespA,
                                              currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse })
                                            tcpRespA nsG sG rfl hcn hbiz hgoto
                                          with ⟨-, hfacts⟩ | ⟨-, -, h4bL, hrefL, hnodataL⟩ | ⟨-, -, hRefFalse⟩
                                        rotate_left
                                        ·
                                          have hrs : Server.referralShapedB tcpRespA = false :=
                                            referralShapedB_false_of_group hrefL
                                          have hts : Server.retryShapedB tcpRespA = false := by
                                            unfold Server.retryShapedB
                                            rw [hbiz]
                                            simp
                                          unfold Server.probePassableB at hpassT
                                          rw [hrs, hts] at hpassT
                                          exact absurd hpassT (by decide)
                                        ·
                                          -- retry (foreign / bizarre): not probe-passable.
                                          -- ¬referralShaped (given) ∧ ¬serverFail ⇒ ¬retryShaped.
                                          have hrs : Server.referralShapedB tcpRespA = false := hRefFalse
                                          have hts : Server.retryShapedB tcpRespA = false := by
                                            unfold Server.retryShapedB; rw [hbiz]; simp
                                          unfold Server.probePassableB at hpassT
                                          rw [hrs, hts] at hpassT
                                          exact absurd hpassT (by decide)
                                        have hwmS : ∃ (origin : String) (reply : Datagram) (srcPort : Nat),
                                            Transit (linkReach net ns ra) origin ra reply (some reply)
                                            ∧ accepts (queryDatagram (w.ids w.idCtr).toNat ra
                                                (byteAddrToModel (Server.ipv4ToAddr ipAddr)) srcPort ednsBuf pq) reply = true
                                            ∧ (αResp tcpRespA).isReferral = reply.msg.isReferral
                                            ∧ reply.msg.tc = false
                                            ∧ (∀ b ∈ tcpRespA.authority.toList, ∃ rr,
                                                VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
                                            ∧ (reply.msg.isReferral = true →
                                                αSection tcpRespA.authority = reply.msg.authority
                                                ∧ αSection tcpRespA.additional = reply.msg.additional
                                                ∧ ((tcpRespA.header.aa == 1) = reply.msg.aa)
                                                ∧ reply.msg.inBailiwick pq.qname = true
                                                ∧ (∀ b ∈ tcpRespA.additional.toList, ∃ rr,
                                                    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
                                                ∧ (∀ sname : ByteArray, Server.respInBailiwick sname tcpRespA = true →
                                                    Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                                      tcpRespA.authority sname = (referralCut reply.msg).length)
                                                ∧ (∀ b ∈ tcpRespA.authority.toList, ∀ rr,
                                                    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                                    (rr.type == (2 : BitVec 16)) = true →
                                                    ∃ na, αName rr.rdata = some na
                                                      ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
                                                      ∧ (∀ x ∈ na, x.size ≤ 63))
                                                ∧ ((tcpRespA.header.tc == 1) = reply.msg.tc)) := by
                                          obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, hclsLink, htcR, hauthS, _hvld, hvldA, hrefImpl⟩ := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA pq hwmTcp hOr hdec2 hsan2 hacc2 hαQp htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                          exact ⟨origin, reply, srcPort, htrans, hacc, hclsLink, htcR, hvldA,
                                            fun hri => ⟨hauthS, hrefImpl hri⟩⟩
                                        obtain ⟨origin, reply, srcPort, htrans, hacc, hclsLink, htcR, hvldA, hrefImpl⟩ := hwmS
                                        have hirTrue : (αResp tcpRespA).isReferral = true :=
                                          αResp_isReferral_true_of_referralShape hfacts.2.2.1
                                            hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.1
                                            hfacts.2.2.2.2.2.2.2 hvldA
                                        have href : reply.msg.isReferral = true := hclsLink.symm.trans hirTrue
                                        obtain ⟨hauthE, haddE, haaE, hbailP, haddWf, hcutBr, hnsCanonG, htcEg⟩ := hrefImpl href
                                        have hbail : reply.msg.inBailiwick q.qname = true := inBailiwick_of_ancestor hbailP hpqanc
                                        have hcutQ : isAncestor (referralCut reply.msg) pq.qname = true :=
                                          isAncestor_referralCut_of_inBailiwick hbailP
                                        have hdel : Server.delegationShapedB tcpRespA = true :=
                                          delegationShapedB_of tcpRespA hfacts.2.2.2.2.1 hfacts.1 hfacts.2.1 hcn
                                        have hunfF : Server.unfollowableDelegationB
                                            (state.resources.slist.markQueried entry.name)
                                            state.resources.sname tcpRespA = false := by simpa using hunf
                                        have hrib : Server.respInBailiwick state.resources.sname tcpRespA = true :=
                                          respInBailiwick_of_not_unfollowable _ _ _ hunfF hdel
                                        have hbridge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                            tcpRespA.authority state.resources.sname = (referralCut reply.msg).length :=
                                          hcutBr state.resources.sname hrib
                                        have hsfF : VeriDNS.Spec.SlistFromNameSpec.searchFails
                                            (NS := VeriDNS.Spec.SlistEntry)
                                            (state.resources.slist.markQueried entry.name) = false := by
                                          have hne : state.resources.slist.servers ≠ #[] := by
                                            intro hemp
                                            rw [DnsSList.bestWithAddress, hemp] at hbest
                                            simp at hbest
                                          show (state.resources.slist.markQueried entry.name).servers.isEmpty = false
                                          simp only [DnsSList.markQueried]
                                          by_contra h
                                          rw [Bool.not_eq_false] at h
                                          apply hne
                                          simpa using congrArg Array.size (Array.isEmpty_iff.mp h)
                                        have hgt : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                            tcpRespA.authority state.resources.sname
                                            > state.resources.slist.matchCount := by
                                          have hcloser : Server.delegationCloserB
                                              (state.resources.slist.markQueried entry.name)
                                              state.resources.sname tcpRespA = true :=
                                            delegationCloserB_of_not_unfollowable _ _ _ hunfF hdel
                                          unfold Server.delegationCloserB at hcloser
                                          rw [hsfF, Bool.false_or] at hcloser
                                          exact of_decide_eq_true hcloser

                                        have hfloorlt : depthFloor < (referralCut reply.msg).length := by
                                          rw [← hbridge]; rw [← hMC]; exact hgt
                                        have hcutlenF : depthFloor ≤ (referralCut reply.msg).length := by omega
                                        obtain ⟨hfrAnc, hfrLen⟩ := isAncestor_drop_ancestor (n := referralCut reply.msg)
                                          (k := depthFloor) hcutlenF
                                        have hdescF : reply.msg.descendsBelow
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) = true :=
                                          descendsBelow_of_strict hfrAnc (by rw [hfrLen]; omega)
                                        have hfresh : (referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) ∉ seen := by
                                          intro hmem
                                          have hlt := hfreshInv _ hmem
                                          rw [hfrLen] at hlt
                                          exact Nat.lt_irrefl _ hlt

                                        have haaF : (tcpRespA.header.aa == 1) = false := by
                                          have h0 : tcpRespA.header.aa = 0 := eq_of_beq hfacts.2.2.2.2.2.1
                                          rw [h0]
                                          decide
                                        have htcF : (tcpRespA.header.tc == 1) = false := htcEg.trans htcR
                                        have htm' : state.now.toNat = now := htm
                                        have hvalA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority).toList,
                                            ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                            (αRR rr).isSome = true := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hα'⟩ := hvldA b (bailiwickRaws_toList_sub hb)
                                          rw [hpr'] at hpr
                                          injection hpr with hrr
                                          subst hrr
                                          cases hα : αRR rr' with
                                          | none => exact absurd hα hα'
                                          | some r => rfl
                                        have hvalD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional).toList,
                                            ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                            (αRR rr).isSome = true := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hα'⟩ := haddWf b (bailiwickRaws_toList_sub hb)
                                          rw [hpr'] at hpr
                                          injection hpr with hrr
                                          subst hrr
                                          cases hα : αRR rr' with
                                          | none => exact absurd hα hα'
                                          | some r => rfl
                                        have hrespAeq : tcpRespA = tcpResp := acceptResponse_some_eq hacc2
                                        have hnoA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority).toList,
                                            ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                            (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                          intro b hb rr hpr
                                          have hb' : b ∈ tcpResp.authority := by
                                            rw [← hrespAeq]
                                            exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                          have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                            (Or.inl (Or.inr hb')) rr hpr
                                          exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                        have hnoD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional).toList,
                                            ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                            (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                          intro b hb rr hpr
                                          have hb' : b ∈ tcpResp.additional := by
                                            rw [← hrespAeq]
                                            exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                          have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                            (Or.inr hb') rr hpr
                                          exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                        have hcutRef : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) = some (referralCut (αResp tcpRespA)) :=
                                          referralCutRaw_αName tcpRespA.authority hvldA hfacts.2.2.2.2.1
                                        have hrefEq : referralCut (αResp tcpRespA) = referralCut reply.msg := by
                                          unfold VeriDNS.Spec.Net.referralCut
                                          rw [show (αResp tcpRespA).authority = reply.msg.authority from hauthE]
                                        have habsF : absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg) = referralCut reply.msg :=
                                          absorbBailiwick_of_descendsBelow _ reply.msg hdescF
                                        have hcutαF : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) = some (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) := by
                                          rw [habsF, ← hrefEq]
                                          exact hcutRef
                                        have hCWwf : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now) state.now :=
                                          CacheWf_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hCacheWf hvalA0 hnoA0 hvalD0 hnoD0
                                        have hCWoe : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now) :=
                                          OneExpiryPerKey_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hOE
                                        have hcf0 : WriteRefines now (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))
                                            (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg) := by
                                          have h := refer_write_WriteRefines_ref state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority)
                                            (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg))
                                            state.now (tcpRespA.header.aa == 1) haaF hcutαF htcF hirTrue hCacheWf hOE
                                            (normRaws_hval hvalA0) (normRaws_hval hvalD0) (normRaws_hno hnoA0) (normRaws_hno hnoD0) (rrsOf_RRCanonMappable hvalA0) (rrsOf_RRCanonMappable hvalD0) reply.msg c href hauthE haddE haaE hmme
                                          rw [htm'] at h
                                          exact h
                                        have hcf : WriteRefines now (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)) :=
                                          (αCache_boundLru_refines (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now) (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)).writeRefines now

                                        obtain ⟨stC, heqStC, hstCache, hstSn, hstNow, hstCh, hstStep, hstLq, hstSbelt, hdisj⟩ :=
                                          afterResume_referral_continue_cases { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA hstep hcn hbiz hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
                                        have hst2 : state'' = stC := Server.IoStep.continue.inj (heqC.symm.trans heqStC)
                                        have hsn'' : αName state''.resources.sname = some q.qname := by rw [hst2, hstSn]; exact hsn
                                        have hsnameCanon'' : state''.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname := by
                                          rw [hst2, hstSn]; exact hsnameCanon
                                        have htm'' : αTime state''.now = now := by rw [hst2, hstNow]; exact htm
                                        have hCCM'' : CnameChainModels state'' q nseen :=
                                          CnameChainModels_congr (by rw [hst2]; exact hstLq)
                                            (by rw [hst2]; exact hstSn) (by rw [hst2]; exact hstCh) hCCM
                                        have hcache'' : state''.resources.cache = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now := by rw [hst2]; exact hstCache
                                        have hcapEq : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                          unfold Server.sanitizeTtlsCap at hsan2; exact (Option.some.inj hsan2).symm
                                        have hcapAuth : tcpRespA.authority = raw2.authority.map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                        have hcapAdd : tcpRespA.additional = (raw2.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                        have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                          rw [hcache'', hst2, hstNow]; exact CacheWf_boundLru (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)) state.now hCWwf
                                        have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                          rw [hcache'']
                                          refine CacheNsCanon_boundLru _ _ _ (CacheNsCanon_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsCanon ?_ ?_)
                                          · intro raw hraw
                                            have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                            rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                            obtain ⟨b0, hb0, rfl⟩ := hmem
                                            exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                          · intro raw hraw
                                            have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                            rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                            obtain ⟨b0, hb0, rfl⟩ := hmem
                                            exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                        have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                          rw [hcache'']
                                          refine CacheCnameCanon_boundLru _ _ _ (CacheCnameCanon_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hCnCanon ?_ ?_)
                                          · intro raw hraw
                                            have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                            rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                            obtain ⟨b0, hb0, rfl⟩ := hmem
                                            exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                          · intro raw hraw
                                            have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                            rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                            obtain ⟨b0, hb0, rfl⟩ := hmem
                                            exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                        have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                          rw [hcache'']; exact CacheNsDistinct_boundLru _ _ _ (CacheNsDistinct_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsDistinct)
                                        have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                          rw [hcache'']; exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hCWoe
                                        have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                          rw [hcache'']; exact VeriDNS.Proof.Cache.boundLru_bounded (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))
                                        have hmiss'' : (αCache state''.resources.cache).hit now q = [] := by
                                          rw [hcache'']
                                          refine hcf.hit_nil (Nat.le_refl now) (hcf0.hit_nil (Nat.le_refl now) ?_)
                                          exact absorb_hit_nil c now _ q reply.msg hmiss (VeriDNS.Spec.Net.Response.isReferral_answer_nil href) (VeriDNS.Spec.Net.Response.isReferral_aa_false href)
                                        have hnmiss'' : (αCache state''.resources.cache).negHit now q = false := by
                                          rw [hcache'']
                                          calc (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)).negHit now q
                                              = (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))).negHit now q := hcf.2.2.1 now q
                                            _ = (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg).negHit now q := hcf0.2.2.1 now q
                                            _ = c.negHit now q := by rw [VeriDNS.Spec.Net.absorb_negHit_eq]
                                            _ = false := hnmiss
                                        have hlq'' : state''.lastQuery = state.lastQuery := by rw [hst2]; exact hstLq
                                        have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                          rw [hcache'']
                                          exact wfrrAll_boundLru _ _ (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)
                                        have hNegWf'' : ∀ qu : VeriDNS.Spec.Question,
                                            (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                            CacheNegWf state''.resources.cache qu.qclass := by
                                          intro qu hqu'
                                          rw [hcache'']
                                          exact CacheNegWf_boundLru _ _ (CacheNegWf_cacheUnlessTruncated _ _ _ _ _
                                            (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu (by rw [← hlq'']; exact hqu'))))
                                        have hqm'' : ∀ qu : VeriDNS.Spec.Question,
                                            (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                            αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by rw [hlq'']; exact hqm
                                        have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hst2, hstNow]; exact hclock
                                        have hstep'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := by rw [hst2]; exact hstStep
                                        have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                          rw [hst2, hstSbelt]; exact hGlBelt
                                        have hnsne : Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority) ≠ #[] :=
                                          extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn tcpRespA.authority hfacts.2.2.2.2.1
                                        rcases hdisj with hkept | ⟨nsNames, mc, hwalk, hclose_eq, hrebuild⟩ | ⟨hbelt, hbeltcond⟩
                                        ·
                                          have hslist'' : state''.resources.slist
                                              = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority))
                                                (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional))
                                                (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname) := by rw [hst2]; exact hkept
                                          have hGlProv'' : GluelessProv state''.resources.slist := by
                                            rw [hslist'']
                                            exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                              (extractNsNames_ownerRaws_canonical tcpRespA.authority (by
                                                intro b hb
                                                rw [hcapAuth, Array.toList_map, List.mem_map] at hb
                                                obtain ⟨b0, hb0, rfl⟩ := hb
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                  (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))))
                                          have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              state''.resources.slist = (referralCut reply.msg).length := by
                                            rw [hslist'', matchCount_setUpAddresses]; exact hbridge
                                          have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < (referralCut reply.msg).length := by
                                            intro b hb
                                            rcases List.mem_cons.mp hb with rfl | hb
                                            · rw [hfrLen]; omega
                                            · have := hfreshInv b hb; omega
                                          obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH mD (by omega) q depth f _ state''
                                            (αCache state''.resources.cache) _ w' now nseen
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (referralCut reply.msg).length resp cout
                                            (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                            hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                          have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                          rw [hlq'', hnowSt] at hrest
                                          have hgae : glueAddresses (αResp tcpRespA) = glueAddresses reply.msg :=
                                            glueAddresses_congr hauthE haddE
                                          have hvalidAuth' : ∀ b ∈ tcpRespA.authority.toList, ∀ rr,
                                              VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                            intro b hb rr hpr
                                            obtain ⟨rr', hpr', hne⟩ := hvldA b hb
                                            rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                          have hvalidAdd' : ∀ b ∈ tcpRespA.additional.toList, ∀ rr,
                                              VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                            intro b hb rr hpr
                                            obtain ⟨rr', hpr', hne⟩ := haddWf b hb
                                            rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                          have hconn := glueAddresses_subperm_transient tcpRespA (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname) hcutRef hvalidAuth'
                                            hvalidAdd' hnsCanonG hfacts.2.2.2.2.1
                                          have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                              ∨ (glueAddresses reply.msg).Subperm s := by
                                            refine Or.inr ?_
                                            rw [← hgae]
                                            refine hconn.trans ?_
                                            rw [hslist''] at hperm
                                            exact hperm
                                          have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                              ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) s q v cM := by
                                            rw [← hcache'']; exact hrec
                                          exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                            trustedReferralProbe_hasVerdictAt net ns ra ednsBuf rttOf
                                              (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                              ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q pq
                                              ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                              (w.ids w.idCtr).toNat srcPort c reply
                                              hmiss hnmiss (Or.inr hSP) htrans hacc
                                              href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                              (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))) hcf0 hgl
                                              (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) hcf cM hrec'',
                                            hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                        ·
                                          have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                              tcpRespA.authority state.resources.sname ≤ mc := by
                                            have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                  (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority))
                                                  (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                    (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname)) = false := by
                                              rw [searchFails_setUpAddresses]; simpa using hnsne
                                            have hmc0 := hclose_eq
                                            rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hmc0
                                            simpa using hmc0
                                          have hslist'' : state''.resources.slist
                                              = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)) state.now nsNames) mc := by
                                            rw [hst2]; exact hrebuild
                                          have hGlProv'' : GluelessProv state''.resources.slist := by
                                            rw [hslist'']
                                            exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                              (walkNs_names_canonical _ state.now
                                                (CacheNsCanon_absorb state.resources.cache tcpRespA
                                                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsCanon
                                                  (by
                                                    intro raw hraw
                                                    have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                                    rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                    obtain ⟨b0, hb0, rfl⟩ := hmem
                                                    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                      (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0)))
                                                  (by
                                                    intro raw hraw
                                                    have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                                    rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                    obtain ⟨b0, hb0, rfl⟩ := hmem
                                                    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                      (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                                128 state.resources.sname nsNames mc hwalk)
                                          have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              state''.resources.slist = mc := by rw [hslist'', matchCount_setUpAddresses]
                                          have hsubmc : (referralCut reply.msg).length ≤ mc := by rw [← hbridge]; exact hge
                                          have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < mc := by
                                            intro b hb
                                            rcases List.mem_cons.mp hb with rfl | hb
                                            · rw [hfrLen]; omega
                                            · have := hfreshInv b hb; omega
                                          obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH mD (by omega) q depth f _ state''
                                            (αCache state''.resources.cache) _ w' now nseen
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) mc resp cout
                                            (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                            hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                          have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                          rw [hlq'', hnowSt] at hrest
                                          have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                              ∨ (glueAddresses reply.msg).Subperm s := by
                                            refine Or.inl ?_
                                            obtain ⟨sname_lab, hsna, hlabq⟩ :
                                                ∃ lab, VeriDNS.Impl.DomainName.wireFormatToLabels state.resources.sname = .ok lab
                                                  ∧ lab.toList = q.qname := by
                                              unfold αName at hsn
                                              split at hsn
                                              · next lab h => exact ⟨lab, h, Option.some.inj hsn⟩
                                              · exact absurd hsn (by simp)
                                            have hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab := by
                                              intro i hi
                                              have hmem : sname_lab[i] ∈ q.qname := by
                                                rw [← hlabq]; exact Array.mem_def.mp (Array.getElem_mem hi)
                                              exact hqvalid _ hmem
                                            have hkey := refer_continue_keystone_wf
                                              ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                  state.resources.cache tcpRespA
                                                  (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                  (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                                tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                                Resolver.credAdditional state.now))
                                              state.resources.sname q.qname sname_lab nsNames mc state.now
                                              hwalk hsna hsnav hsnameCanon hlabq hqlen hCWwf
                                              (CacheNsCanon_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsCanon
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0)))
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                              (CacheNsDistinct_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsDistinct)
                                            rw [← htm]
                                            refine hkey.trans ?_
                                            rw [← hslist'']
                                            exact hperm
                                          have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                              ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) s q v cM := by
                                            rw [← hcache'']; exact hrec
                                          exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                            trustedReferralProbe_hasVerdictAt net ns ra ednsBuf rttOf
                                              (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                              ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q pq
                                              ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                              (w.ids w.idCtr).toNat srcPort c reply
                                              hmiss hnmiss (Or.inr hSP) htrans hacc
                                              href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                              (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))) hcf0 hgl
                                              (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) hcf cM hrec'',
                                            hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                        ·
                                          exfalso
                                          have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority))
                                                (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname)) = false := by
                                            rw [searchFails_setUpAddresses]; simpa using hnsne
                                          rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hbeltcond
                                          have : 0 < (referralCut reply.msg).length := by omega
                                          rw [hbridge] at hbeltcond
                                          simp only [decide_eq_false_iff_not, Nat.not_lt] at hbeltcond
                                          omega
                                    · obtain ⟨target, hcnT⟩ := Option.ne_none_iff_exists'.mp hcn
                                      rw [probePassable_false_of_chase hcnT] at hpassT
                                      exact absurd hpassT (by decide)
                                  have hfull : Resolver.probeRoundB state.resources.sname revealed = false := by
                                    simp only [Bool.not_eq_true] at hprC; exact hprC
                                  have hαQ : αQuery subQuery0 = some q :=
                                    αQuery_buildSubQuery hbuild hfull hsn hqm hrd
                                  by_cases hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) tcpRespA = none
                                  ·

                                    by_cases hbiz : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
                                        || !Resolver.classifiableB tcpRespA) = true
                                    ·
                                      rw [afterResume_bizarre
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name tcpRespA hstep hcn hbiz] at heqC
                                      simp only [Server.dropIfBizarre, if_pos hbiz] at heqC
                                      have hst := Server.IoStep.continue.inj heqC
                                      subst hst
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mD (by omega) q depth f _
                                        (Server.boundStateCache
                                          (Server.roundTouches
                                            { state with resources := { state.resources with
                                                slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                            tcpRespA)
                                          { resources :=
                                              { sname := state.resources.sname, stype := state.resources.stype,
                                                sclass := state.resources.sclass,
                                                slist := (state.resources.slist.markQueried entry.name).removeServer entry.name,
                                                sbelt := state.resources.sbelt, cache := state.resources.cache },
                                            currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                            lastQuery := state.lastQuery, lastResponse := none,
                                            cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                        c _ w' now nseen seen depthFloor resp cout
                                        ⟨by
                                            show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                            rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                          hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                        (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                        (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                        (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                        (by exact wfrrAll_boundLru _ _ hwfrr)
                                        (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                        (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                        (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                        (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                        hmiss hnmiss hfreshInv (by exact hMC)
                                        (by exact GluelessProv_removeServer entry.name (GluelessProv_markQueried entry.name hGlProv))
                                        (by exact hGlBelt)
                                        hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                      have hpart := modelSlistOf_removeServer_perm
                                        (state.resources.slist.markQueried entry.name) entry.name
                                      rw [modelSlistOf_markQueried] at hpart

                                      obtain ⟨l, hp, hsl⟩ := hperm
                                      exact ⟨_, v, cM, hasVerdictAt_timeout_prepend net ns ra ednsBuf rttOf c q v cM _ hrec,
                                        ⟨_ ++ l, (hp.append_left _).trans hpart.symm, hsl.append_left _⟩, hrc, hans, hrest⟩
                                    ·
                                      rw [Bool.not_eq_true] at hbiz
                                      have hspoof := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)

                                      obtain ⟨origin, reply, srcPort, htrans, hacc, _hragS, hclsLink, htcR, hauthS, _hvld, hvldA, hrefImpl⟩ := hspoof
                                      have hcls : Resolver.classifiableB tcpRespA = true := by
                                        have h := (Bool.or_eq_false_iff.mp hbiz).2; simpa using h
                                      have hsf : (tcpRespA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false :=
                                        (Bool.or_eq_false_iff.mp hbiz).1
                                      obtain ⟨nsG, sG, hgoto⟩ := afterResume_continue_stepAnalyze_goto
                                        { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                        entry.name tcpRespA state'' hstep hcn hsf hcls heqC
                                      rcases stepAnalyzeResponse_goto_cases
                                          ({ ({ state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }) with
                                            lastResponse := some tcpRespA,
                                            currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse })
                                          tcpRespA nsG sG rfl hcn hbiz hgoto
                                        with ⟨-, hfacts⟩ | ⟨-, -, h4bL, hrefL, hnodataL⟩ | ⟨hnsG, hsG, -⟩
                                      rotate_left
                                      · -- B.3: lame referral ⇒ retry
                                        rw [afterResume_lame
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA hstep hcn hbiz h4bL hrefL hnodataL] at heqC
                                        have hst := Server.IoStep.continue.inj heqC
                                        subst hst
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansV, hrest⟩ := IH mD (by omega) q depth f _
                                          (Server.boundStateCache
                                            (Server.roundTouches
                                              { state with resources := { state.resources with
                                                  slist := state.resources.slist.markQueried entry.name } }
                                              tcpRespA)
                                            { resources :=
                                                { sname := state.resources.sname, stype := state.resources.stype,
                                                  sclass := state.resources.sclass,
                                                  slist := state.resources.slist.markQueried entry.name,
                                                  sbelt := state.resources.sbelt, cache := state.resources.cache },
                                              currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                              lastQuery := state.lastQuery, lastResponse := none,
                                              cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                          c _ w' now nseen seen depthFloor resp cout
                                          ⟨by
                                              show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                              rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                            hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                          (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                          (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                          (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                          (by exact wfrrAll_boundLru _ _ hwfrr)
                                          (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                          (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                          (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                          (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                          hmiss hnmiss hfreshInv (by exact hMC)
                                          (by exact GluelessProv_markQueried entry.name hGlProv)
                                          (by exact hGlBelt)
                                          hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                        obtain ⟨l, hp, hsl⟩ := hperm
                                        have hp' : l.Perm (modelSlistOf
                                            (state.resources.slist.markQueried entry.name)) := hp
                                        rw [modelSlistOf_markQueried] at hp'
                                        exact ⟨_, v, cM, hrec, ⟨l, hp', hsl⟩, hrc, hansV, hrest⟩
                                      · -- G: ambiguous empty NOERROR ⇒ retry (mirrors B.3)
                                        rw [hnsG, hsG] at hgoto
                                        rw [afterResume_of_stepGoto
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA hstep hbiz hgoto] at heqC
                                        have hst := Server.IoStep.continue.inj heqC
                                        subst hst
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansV, hrest⟩ := IH mD (by omega) q depth f _
                                          (Server.boundStateCache
                                            (Server.roundTouches
                                              { state with resources := { state.resources with
                                                  slist := state.resources.slist.markQueried entry.name } }
                                              tcpRespA)
                                            { resources :=
                                                { sname := state.resources.sname, stype := state.resources.stype,
                                                  sclass := state.resources.sclass,
                                                  slist := state.resources.slist.markQueried entry.name,
                                                  sbelt := state.resources.sbelt, cache := state.resources.cache },
                                              currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                              lastQuery := state.lastQuery, lastResponse := none,
                                              cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                          c _ w' now nseen seen depthFloor resp cout
                                          ⟨by
                                              show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                              rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                            hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                          (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                          (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                          (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                          (by exact wfrrAll_boundLru _ _ hwfrr)
                                          (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                          (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                          (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                          (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                          hmiss hnmiss hfreshInv (by exact hMC)
                                          (by exact GluelessProv_markQueried entry.name hGlProv)
                                          (by exact hGlBelt)
                                          hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                        obtain ⟨l, hp, hsl⟩ := hperm
                                        have hp' : l.Perm (modelSlistOf
                                            (state.resources.slist.markQueried entry.name)) := hp
                                        rw [modelSlistOf_markQueried] at hp'
                                        exact ⟨_, v, cM, hrec, ⟨l, hp', hsl⟩, hrc, hansV, hrest⟩
                                      have hirTrue : (αResp tcpRespA).isReferral = true :=
                                        αResp_isReferral_true_of_referralShape hfacts.2.2.1
                                          hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.1
                                          hfacts.2.2.2.2.2.2.2 hvldA
                                      have href : reply.msg.isReferral = true := hclsLink.symm.trans hirTrue
                                      have hauthE : αSection tcpRespA.authority = reply.msg.authority := hauthS
                                      obtain ⟨haddE, haaE, hbail, haddWf, hcutBr, hnsCanonG, htcEg⟩ := hrefImpl href
                                      have hcutQ : isAncestor (referralCut reply.msg) q.qname = true :=
                                        isAncestor_referralCut_of_inBailiwick hbail
                                      have hdel : Server.delegationShapedB tcpRespA = true :=
                                        delegationShapedB_of tcpRespA hfacts.2.2.2.2.1 hfacts.1 hfacts.2.1 hcn
                                      have hunfF : Server.unfollowableDelegationB
                                          (state.resources.slist.markQueried entry.name)
                                          state.resources.sname tcpRespA = false := by simpa using hunf
                                      have hrib : Server.respInBailiwick state.resources.sname tcpRespA = true :=
                                        respInBailiwick_of_not_unfollowable _ _ _ hunfF hdel
                                      have hbridge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          tcpRespA.authority state.resources.sname = (referralCut reply.msg).length :=
                                        hcutBr state.resources.sname hrib
                                      have hsfF : VeriDNS.Spec.SlistFromNameSpec.searchFails
                                          (NS := VeriDNS.Spec.SlistEntry)
                                          (state.resources.slist.markQueried entry.name) = false := by
                                        have hne : state.resources.slist.servers ≠ #[] := by
                                          intro hemp
                                          rw [DnsSList.bestWithAddress, hemp] at hbest
                                          simp at hbest
                                        show (state.resources.slist.markQueried entry.name).servers.isEmpty = false
                                        simp only [DnsSList.markQueried]
                                        by_contra h
                                        rw [Bool.not_eq_false] at h
                                        apply hne
                                        simpa using congrArg Array.size (Array.isEmpty_iff.mp h)
                                      have hgt : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          tcpRespA.authority state.resources.sname
                                          > state.resources.slist.matchCount := by
                                        have hcloser : Server.delegationCloserB
                                            (state.resources.slist.markQueried entry.name)
                                            state.resources.sname tcpRespA = true :=
                                          delegationCloserB_of_not_unfollowable _ _ _ hunfF hdel
                                        unfold Server.delegationCloserB at hcloser
                                        rw [hsfF, Bool.false_or] at hcloser
                                        exact of_decide_eq_true hcloser

                                      have hfloorlt : depthFloor < (referralCut reply.msg).length := by
                                        rw [← hbridge]; rw [← hMC]; exact hgt
                                      have hcutlenF : depthFloor ≤ (referralCut reply.msg).length := by omega
                                      obtain ⟨hfrAnc, hfrLen⟩ := isAncestor_drop_ancestor (n := referralCut reply.msg)
                                        (k := depthFloor) hcutlenF
                                      have hdescF : reply.msg.descendsBelow
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) = true :=
                                        descendsBelow_of_strict hfrAnc (by rw [hfrLen]; omega)
                                      have hfresh : (referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) ∉ seen := by
                                        intro hmem
                                        have hlt := hfreshInv _ hmem
                                        rw [hfrLen] at hlt
                                        exact Nat.lt_irrefl _ hlt

                                      have haaF : (tcpRespA.header.aa == 1) = false := by
                                        have h0 : tcpRespA.header.aa = 0 := eq_of_beq hfacts.2.2.2.2.2.1
                                        rw [h0]
                                        decide
                                      have htcF : (tcpRespA.header.tc == 1) = false := htcEg.trans htcR
                                      have htm' : state.now.toNat = now := htm
                                      have hvalA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hvldA b (bailiwickRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hvalD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := haddWf b (bailiwickRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hrespAeq : tcpRespA = tcpResp := acceptResponse_some_eq hacc2
                                      have hnoA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ tcpResp.authority := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                          (Or.inl (Or.inr hb')) rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hnoD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ tcpResp.additional := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                          (Or.inr hb') rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hcutRef : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) = some (referralCut (αResp tcpRespA)) :=
                                        referralCutRaw_αName tcpRespA.authority hvldA hfacts.2.2.2.2.1
                                      have hrefEq : referralCut (αResp tcpRespA) = referralCut reply.msg := by
                                        unfold VeriDNS.Spec.Net.referralCut
                                        rw [show (αResp tcpRespA).authority = reply.msg.authority from hauthE]
                                      have habsF : absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg) = referralCut reply.msg :=
                                        absorbBailiwick_of_descendsBelow _ reply.msg hdescF
                                      have hcutαF : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) = some (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) := by
                                        rw [habsF, ← hrefEq]
                                        exact hcutRef
                                      have hCWwf : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now) state.now :=
                                        CacheWf_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hCacheWf hvalA0 hnoA0 hvalD0 hnoD0
                                      have hCWoe : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now) :=
                                        OneExpiryPerKey_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hOE
                                      have hcf0 : WriteRefines now (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))
                                          (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg) := by
                                        have h := refer_write_WriteRefines_ref state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority)
                                          (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg))
                                          state.now (tcpRespA.header.aa == 1) haaF hcutαF htcF hirTrue hCacheWf hOE
                                          (normRaws_hval hvalA0) (normRaws_hval hvalD0) (normRaws_hno hnoA0) (normRaws_hno hnoD0) (rrsOf_RRCanonMappable hvalA0) (rrsOf_RRCanonMappable hvalD0) reply.msg c href hauthE haddE haaE hmme
                                        rw [htm'] at h
                                        exact h
                                      have hcf : WriteRefines now (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)) :=
                                        (αCache_boundLru_refines (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now) (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)).writeRefines now

                                      obtain ⟨stC, heqStC, hstCache, hstSn, hstNow, hstCh, hstStep, hstLq, hstSbelt, hdisj⟩ :=
                                        afterResume_referral_continue_cases { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          entry.name tcpRespA hstep hcn hbiz hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
                                      have hst2 : state'' = stC := Server.IoStep.continue.inj (heqC.symm.trans heqStC)
                                      have hsn'' : αName state''.resources.sname = some q.qname := by rw [hst2, hstSn]; exact hsn
                                      have hsnameCanon'' : state''.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname := by
                                        rw [hst2, hstSn]; exact hsnameCanon
                                      have htm'' : αTime state''.now = now := by rw [hst2, hstNow]; exact htm
                                      have hCCM'' : CnameChainModels state'' q nseen :=
                                        CnameChainModels_congr (by rw [hst2]; exact hstLq)
                                          (by rw [hst2]; exact hstSn) (by rw [hst2]; exact hstCh) hCCM
                                      have hcache'' : state''.resources.cache = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now := by rw [hst2]; exact hstCache
                                      have hcapEq : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                        unfold Server.sanitizeTtlsCap at hsan2; exact (Option.some.inj hsan2).symm
                                      have hcapAuth : tcpRespA.authority = raw2.authority.map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                      have hcapAdd : tcpRespA.additional = (raw2.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                      have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                        rw [hcache'', hst2, hstNow]; exact CacheWf_boundLru (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)) state.now hCWwf
                                      have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                        rw [hcache'']
                                        refine CacheNsCanon_boundLru _ _ _ (CacheNsCanon_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsCanon ?_ ?_)
                                        · intro raw hraw
                                          have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                        · intro raw hraw
                                          have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                      have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                        rw [hcache'']
                                        refine CacheCnameCanon_boundLru _ _ _ (CacheCnameCanon_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hCnCanon ?_ ?_)
                                        · intro raw hraw
                                          have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                        · intro raw hraw
                                          have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                      have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                        rw [hcache'']; exact CacheNsDistinct_boundLru _ _ _ (CacheNsDistinct_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsDistinct)
                                      have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                        rw [hcache'']; exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hCWoe
                                      have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                        rw [hcache'']; exact VeriDNS.Proof.Cache.boundLru_bounded (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))
                                      have hmiss'' : (αCache state''.resources.cache).hit now q = [] := by
                                        rw [hcache'']
                                        refine hcf.hit_nil (Nat.le_refl now) (hcf0.hit_nil (Nat.le_refl now) ?_)
                                        exact absorb_hit_nil c now _ q reply.msg hmiss (VeriDNS.Spec.Net.Response.isReferral_answer_nil href) (VeriDNS.Spec.Net.Response.isReferral_aa_false href)
                                      have hnmiss'' : (αCache state''.resources.cache).negHit now q = false := by
                                        rw [hcache'']
                                        calc (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)).negHit now q
                                            = (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))).negHit now q := hcf.2.2.1 now q
                                          _ = (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg).negHit now q := hcf0.2.2.1 now q
                                          _ = c.negHit now q := by rw [VeriDNS.Spec.Net.absorb_negHit_eq]
                                          _ = false := hnmiss
                                      have hlq'' : state''.lastQuery = state.lastQuery := by rw [hst2]; exact hstLq
                                      have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                        rw [hcache'']
                                        exact wfrrAll_boundLru _ _ (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)
                                      have hNegWf'' : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          CacheNegWf state''.resources.cache qu.qclass := by
                                        intro qu hqu'
                                        rw [hcache'']
                                        exact CacheNegWf_boundLru _ _ (CacheNegWf_cacheUnlessTruncated _ _ _ _ _
                                          (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu (by rw [← hlq'']; exact hqu'))))
                                      have hqm'' : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by rw [hlq'']; exact hqm
                                      have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hst2, hstNow]; exact hclock
                                      have hstep'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := by rw [hst2]; exact hstStep
                                      have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                        rw [hst2, hstSbelt]; exact hGlBelt
                                      have hnsne : Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority) ≠ #[] :=
                                        extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn tcpRespA.authority hfacts.2.2.2.2.1
                                      rcases hdisj with hkept | ⟨nsNames, mc, hwalk, hclose_eq, hrebuild⟩ | ⟨hbelt, hbeltcond⟩
                                      ·
                                        have hslist'' : state''.resources.slist
                                            = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional))
                                              (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname) := by rw [hst2]; exact hkept
                                        have hGlProv'' : GluelessProv state''.resources.slist := by
                                          rw [hslist'']
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (extractNsNames_ownerRaws_canonical tcpRespA.authority (by
                                              intro b hb
                                              rw [hcapAuth, Array.toList_map, List.mem_map] at hb
                                              obtain ⟨b0, hb0, rfl⟩ := hb
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))))
                                        have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            state''.resources.slist = (referralCut reply.msg).length := by
                                          rw [hslist'', matchCount_setUpAddresses]; exact hbridge
                                        have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < (referralCut reply.msg).length := by
                                          intro b hb
                                          rcases List.mem_cons.mp hb with rfl | hb
                                          · rw [hfrLen]; omega
                                          · have := hfreshInv b hb; omega
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH mD (by omega) q depth f _ state''
                                          (αCache state''.resources.cache) _ w' now nseen
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (referralCut reply.msg).length resp cout
                                          (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                          hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                        have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                        rw [hlq'', hnowSt] at hrest
                                        have hgae : glueAddresses (αResp tcpRespA) = glueAddresses reply.msg :=
                                            glueAddresses_congr hauthE haddE
                                        have hvalidAuth' : ∀ b ∈ tcpRespA.authority.toList, ∀ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hne⟩ := hvldA b hb
                                          rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                        have hvalidAdd' : ∀ b ∈ tcpRespA.additional.toList, ∀ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hne⟩ := haddWf b hb
                                          rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                        have hconn := glueAddresses_subperm_transient tcpRespA (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname) hcutRef hvalidAuth'
                                          hvalidAdd' hnsCanonG hfacts.2.2.2.2.1
                                        have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                            ∨ (glueAddresses reply.msg).Subperm s := by
                                          refine Or.inr ?_
                                          rw [← hgae]
                                          refine hconn.trans ?_
                                          rw [hslist''] at hperm
                                          exact hperm
                                        have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) s q v cM := by
                                          rw [← hcache'']; exact hrec
                                        exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                          trustedReferral_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                            (w.ids w.idCtr).toNat srcPort c reply
                                            hmiss hnmiss htrans hacc
                                            href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                            (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))) hcf0 hgl
                                            (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) hcf cM hrec'',
                                          hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                      ·
                                        have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                            tcpRespA.authority state.resources.sname ≤ mc := by
                                          have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority))
                                                (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname)) = false := by
                                            rw [searchFails_setUpAddresses]; simpa using hnsne
                                          have hmc0 := hclose_eq
                                          rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hmc0
                                          simpa using hmc0
                                        have hslist'' : state''.resources.slist
                                            = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)) state.now nsNames) mc := by
                                          rw [hst2]; exact hrebuild
                                        have hGlProv'' : GluelessProv state''.resources.slist := by
                                          rw [hslist'']
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (walkNs_names_canonical _ state.now
                                              (CacheNsCanon_absorb state.resources.cache tcpRespA
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsCanon
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                    (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0)))
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                    (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                              128 state.resources.sname nsNames mc hwalk)
                                        have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            state''.resources.slist = mc := by rw [hslist'', matchCount_setUpAddresses]
                                        have hsubmc : (referralCut reply.msg).length ≤ mc := by rw [← hbridge]; exact hge
                                        have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < mc := by
                                          intro b hb
                                          rcases List.mem_cons.mp hb with rfl | hb
                                          · rw [hfrLen]; omega
                                          · have := hfreshInv b hb; omega
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH mD (by omega) q depth f _ state''
                                          (αCache state''.resources.cache) _ w' now nseen
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) mc resp cout
                                          (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                          hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                        have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                        rw [hlq'', hnowSt] at hrest
                                        have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                            ∨ (glueAddresses reply.msg).Subperm s := by
                                          refine Or.inl ?_
                                          obtain ⟨sname_lab, hsna, hlabq⟩ :
                                              ∃ lab, VeriDNS.Impl.DomainName.wireFormatToLabels state.resources.sname = .ok lab
                                                ∧ lab.toList = q.qname := by
                                            unfold αName at hsn
                                            split at hsn
                                            · next lab h => exact ⟨lab, h, Option.some.inj hsn⟩
                                            · exact absurd hsn (by simp)
                                          have hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab := by
                                            intro i hi
                                            have hmem : sname_lab[i] ∈ q.qname := by
                                              rw [← hlabq]; exact Array.mem_def.mp (Array.getElem_mem hi)
                                            exact hqvalid _ hmem
                                          have hkey := refer_continue_keystone_wf
                                            ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache tcpRespA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                                (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                              tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                              Resolver.credAdditional state.now))
                                            state.resources.sname q.qname sname_lab nsNames mc state.now
                                            hwalk hsna hsnav hsnameCanon hlabq hqlen hCWwf
                                            (CacheNsCanon_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsCanon
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ tcpRespA.authority.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0)))
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ tcpRespA.additional.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec2 b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                            (CacheNsDistinct_absorb state.resources.cache tcpRespA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) state.now hNsDistinct)
                                          rw [← htm]
                                          refine hkey.trans ?_
                                          rw [← hslist'']
                                          exact hperm
                                        have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) s q v cM := by
                                          rw [← hcache'']; exact hrec
                                        exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                          trustedReferral_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                            (w.ids w.idCtr).toNat srcPort c reply
                                            hmiss hnmiss htrans hacc
                                            href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                            (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now))) hcf0 hgl
                                            (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache tcpRespA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority)
                                              (Resolver.credAuthority (tcpRespA.header.aa == 1)) state.now)
                                            tcpRespA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } tcpRespA) state.now)) hcf cM hrec'',
                                          hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                      ·
                                        exfalso
                                        have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority) tcpRespA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) tcpRespA.authority state.resources.sname)) = false := by
                                          rw [searchFails_setUpAddresses]; simpa using hnsne
                                        rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hbeltcond
                                        have : 0 < (referralCut reply.msg).length := by omega
                                        rw [hbridge] at hbeltcond
                                        simp only [decide_eq_false_iff_not, Nat.not_lt] at hbeltcond
                                        omega
                                  ·

                                    obtain ⟨target, hcnT⟩ := Option.ne_none_iff_exists'.mp hcn
                                    obtain ⟨q₀L, quL, hq0, hqu0, hsubq⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                    rw [subQuestion_full hfull quL] at hsubq
                                    have hqmL := hqm quL ⟨q₀L, hq0, hqu0⟩
                                    obtain ⟨qaR, hqaR, hqaCI, hqaT, _hqaC⟩ := questionMatches_fields
                                      (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubq)
                                          (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                      (acceptResponse_questionMatches hacc2)
                                    have hqt : q.qtype.covers RRType.cname = false :=
                                      covers_cname_false_of_chase tcpRespA target qaR q hcnT hqaR
                                        (by rw [hqaT]; exact hqmL.1) hqstar
                                    obtain ⟨t, ht, hqq⟩ := αQType_rr_inv hqmL.1 hqstar
                                    have htne : t ≠ RRType.cname := by
                                      intro hteq
                                      rw [hqq, hteq] at hqt
                                      exact absurd hqt (by decide)
                                    have hvalidAns : ∀ b ∈ tcpRespA.answer.toList, ∃ rr,
                                        VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                          ∧ αRR rr ≠ none := by
                                      obtain ⟨_, _, _, -, -, -, -, -, -, hvld, -⟩ := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                      exact hvld
                                    have hrespAeq : tcpRespA = tcpResp := acceptResponse_some_eq hacc2
                                    have hcapEq : tcpResp = Server.capTtls (Edns.stripOpt raw2) := by
                                      unfold Server.sanitizeTtlsCap at hsan2
                                      exact (Option.some.inj hsan2).symm
                                    have hcapAns : tcpRespA.answer = raw2.answer.map Server.capTtlRR := by
                                      rw [hrespAeq, hcapEq]; rfl
                                    have hquesEq : tcpRespA.question = raw2.question := by
                                      rw [hrespAeq, hcapEq]; rfl
                                    have hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR := by
                                      have hqaR0 : raw2.question[0]? = some qaR := by
                                        rw [← hquesEq]; exact hqaR
                                      obtain ⟨-, -, -, -, hqs, -, -, -⟩ :=
                                        VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec2
                                      rw [Array.getElem?_eq_some_iff] at hqaR0
                                      obtain ⟨hlt, hget⟩ := hqaR0
                                      exact hget ▸ hqs ⟨0, hlt⟩
                                    obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
                                    have hqnRq : VeriDNS.Spec.Net.nameEq qnR q.qname = true := by
                                      obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
                                      obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
                                      exact hne'
                                    obtain ⟨quE, hquE, hextQ⟩ := (cnameToChase_some tcpRespA target hcnT).2
                                    rw [show quE = qaR from Option.some.inj (hquE.symm.trans hqaR)] at hextQ
                                    obtain ⟨cnBytes, rrCn, cn, tgt, hextRR, hcnMem, hprC, hty5, hrdT, hαcn, hcnRR, hcnrd, hαtgt⟩ :=
                                      cname_link_facts hαR hcanR hvalR hextQ hvalidAns
                                    rw [VeriDNS.Spec.Net.cnameRR_congr hqnRq] at hcnRR
                                    have hcanonAns : ∀ raw ∈ tcpRespA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                      intro raw hmem
                                      rw [hcapAns, Array.toList_map, List.mem_map] at hmem
                                      obtain ⟨b0, hb0, rfl⟩ := hmem
                                      exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                        (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec2 b0 (Array.mem_def.mpr hb0))
                                    obtain ⟨na0, hna0, hnacan0, hnaval0, hnalen0⟩ :=
                                      canonicalRR_cnameRdata_canonical (hcanonAns cnBytes hcnMem) hprC hty5
                                    have hna0tgt : na0 = tgt := by
                                      rw [hrdT] at hna0
                                      exact Option.some.inj (hna0.symm.trans hαtgt)
                                    rw [hna0tgt] at hnacan0 hnaval0 hnalen0
                                    have htB : target = VeriDNS.Impl.DomainName.labelsToWireFormatGo tgt := by
                                      rw [← hrdT]; exact hnacan0
                                    have hanchor : ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim
                                        state.resources.sname (fun qu => qu.qname)) = quL.qname := by
                                      rw [hq0]
                                      show (q₀L.question[0]?).elim state.resources.sname (fun qu => qu.qname) = quL.qname
                                      rw [hqu0]
                                      rfl
                                    have hCCM' : ∀ nm ∈ q.qname :: nseen, ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                                        quL.qname state.cnameChain).toList,
                                        αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                          ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                      have h := hCCM
                                      unfold CnameChainModels at h
                                      rw [hanchor] at h
                                      exact h
                                    have hpre : Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA
                                        = state.cnameChain.push cnBytes := by
                                      unfold Resolver.prependCnameLink
                                      simp only [hqaR, hextRR]
                                    have hvtl : (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)).toList
                                        = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname state.cnameChain).toList
                                          ++ [VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn] := by
                                      rw [hpre]
                                      exact cnameChaseVisited_push quL.qname state.cnameChain hprC
                                    have hvis : ∀ nm ∈ tgt :: (q.qname :: nseen),
                                        ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)).toList,
                                        αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                          ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                      intro nm hnm
                                      rcases List.mem_cons.mp hnm with rfl | hnm
                                      · refine ⟨target, ?_, hαtgt, htB, hnaval0⟩
                                        rw [hvtl]
                                        refine List.mem_append_right _ ?_
                                        rw [show VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn
                                          = rrCn.rdata from rfl, hrdT]
                                        exact List.mem_singleton.mpr rfl
                                      · obtain ⟨b, hb, hf⟩ := hCCM' nm hnm
                                        refine ⟨b, ?_, hf⟩
                                        rw [hvtl]
                                        exact List.mem_append_left _ hb
                                    have hTvis : ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)).toList,
                                        VeriDNS.Impl.DomainName.nameEqCI b target = true := by
                                      refine ⟨VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn, ?_, ?_⟩
                                      · rw [hvtl]
                                        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                                      · rw [show VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn
                                          = rrCn.rdata from rfl, hrdT]
                                        exact VeriDNS.Proof.NameTree.nameEqCI_refl target

                                    have htcF0 : (tcpRespA.header.tc == 1) = false := htc0
                                    obtain ⟨hnrev0, sname', chain', hla0, hcache0, hsname0, hnow0, hchain0, hstepC0, hlq0, hsbelt0, hslistD0⟩ :=
                                      afterResume_cname_continue_inv
                                        { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                        entry.name tcpRespA target q₀L quL state'' hstep hcnT hq0 hqu0 htcF0 (by exact hTvis) heqC
                                    have hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                                        ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
                                        state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false := by
                                      exact hnrev0
                                    have hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
                                        (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)
                                        quL.qtype quL.qclass state.now 8 target
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)
                                        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                          (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA))
                                        = .miss sname' chain' := by exact hla0
                                    have hcache'' : state''.resources.cache
                                        = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).boundLru
                                          (Server.roundTouches (Server.dropIfBizarre
                                            { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                            entry.name tcpRespA) tcpRespA) state.now := by exact hcache0
                                    have hsname'' : state''.resources.sname = sname' := hsname0
                                    have hnow'' : state''.now = state.now := by exact hnow0
                                    have hchain'' : state''.cnameChain = chain' := hchain0
                                    have hstepC'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := hstepC0
                                    have hlq'' : state''.lastQuery = state.lastQuery := by exact hlq0
                                    have hsbelt'' : state''.resources.sbelt = state.resources.sbelt := by exact hsbelt0
                                    have hfresh : tgt ∉ q.qname :: nseen :=
                                      cname_target_fresh state q nseen target tgt hCCM htB hnaval0 hnrev

                                    have hvalW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                        (Resolver.echoedQname tcpRespA) tcpRespA.answer).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (αRR rr).isSome = true := by
                                      intro b hb rr hpr
                                      obtain ⟨rr', hpr', hα'⟩ := hvalidAns b (cnameRaws_toList_sub hb)
                                      rw [hpr'] at hpr
                                      injection hpr with hrr
                                      subst hrr
                                      cases hα : αRR rr' with
                                      | none => exact absurd hα hα'
                                      | some r => rfl
                                    have hnoW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                        (Resolver.echoedQname tcpRespA) tcpRespA.answer).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                      intro b hb rr hpr
                                      have hb' : b ∈ tcpResp.answer := by
                                        rw [← hrespAeq]
                                        exact Array.mem_def.mpr (cnameRaws_toList_sub hb)
                                      have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls raw2 tcpResp hsan2 b
                                        (Or.inl (Or.inl hb')) rr hpr
                                      exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                    have hwfW : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) state.now := by
                                      refine CacheWf_cacheUnlessTruncated _ _ _ _ _ hCacheWf ?_ ?_
                                      · unfold Resolver.credAnswer
                                        by_cases ha' : (tcpRespA.header.aa == 1) = true
                                        · rw [if_pos ha']; exact Or.inl rfl
                                        · rw [if_neg ha']; exact Or.inr (Or.inr (Or.inl rfl))
                                      · intro raw hraw rr hp
                                        exact parseRaw_entry_canonical _ state.now hp (normRaws_hval hvalW raw hraw rr hp) (normRaws_hno hnoW raw hraw rr hp)
                                    have hCnW : CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) := by
                                      refine CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hCnCanon ?_
                                      intro raw hraw rr hp htype
                                      exact canonicalRR_cnameRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                    have hNsW : CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) := by
                                      refine CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hNsCanon ?_
                                      intro raw hraw rr hp htype
                                      exact canonicalRR_nsRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                    have hNsDW : CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) :=
                                      CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hNsDistinct
                                    have hOEW : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) :=
                                      VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hOE _ _ _ _
                                    have hwfrrW : ∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).records,
                                        VeriDNS.Proof.NameTree.WfRR e.rr :=
                                      wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
                                    have hnegwfW : CacheNegWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now) quL.qclass :=
                                      CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf quL ⟨q₀L, hq0, hqu0⟩)

                                    have hpeel := localAnswer_chase_peel net ns ra ednsBuf rttOf
                                      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                        (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                      quL.qtype quL.qclass state.now q t [] quL.qname ht hqq htne hqmL.2
                                      (MatchMaxEquiv.refl _) hwfW hCnW hwfrrW hnegwfW 8 target tgt
                                      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA)
                                      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain tcpRespA))
                                      (q.qname :: nseen) (.miss sname' chain') hla hαtgt htB hnaval0 hnalen0 rfl hvis
                                    obtain ⟨links, nF, nseenF, hchainF, hnF, hnFcan, hnFval, hlenF, hvisF, hmissF, hnmissF, -, hcont⟩ := hpeel
                                    by_cases htcF : (tcpRespA.header.tc == 1) = false
                                    ·

                                      have hbnd : CacheRefines
                                          (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).boundLru
                                            (Server.roundTouches (Server.dropIfBizarre
                                              { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                              entry.name tcpRespA) tcpRespA) state.now))
                                          (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now)) :=
                                        αCache_boundLru_refines _ _ _ hwfrrW

                                      have hsn'' : αName state''.resources.sname = some nF := by
                                        rw [hsname'']; exact hnF
                                      have hsnameCanon'' : state''.resources.sname
                                          = VeriDNS.Impl.DomainName.labelsToWireFormatGo nF := by
                                        rw [hsname'']; exact hnFcan
                                      have htm'' : αTime state''.now = now := by rw [hnow'']; exact htm
                                      have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hnow'']; exact hclock
                                      have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                        rw [hcache'', hnow'']
                                        exact CacheWf_boundLru _ _ _ state.now hwfW
                                      have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                        rw [hcache'']
                                        exact CacheNsCanon_boundLru _ _ _ hNsW
                                      have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                        rw [hcache'']
                                        exact CacheCnameCanon_boundLru _ _ _ hCnW
                                      have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                        rw [hcache'']
                                        exact wfrrAll_boundLru _ _ hwfrrW
                                      have hNegWf'' : ∀ qu2 : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                          CacheNegWf state''.resources.cache qu2.qclass := by
                                        intro qu2 hqu2
                                        rw [hcache'']
                                        exact CacheNegWf_boundLru _ _
                                          (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu2 (by rw [← hlq'']; exact hqu2)))
                                      have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                        rw [hcache'']
                                        exact CacheNsDistinct_boundLru _ _ _ hNsDW
                                      have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                        rw [hcache'']
                                        exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOEW
                                      have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                        rw [hcache'']
                                        exact VeriDNS.Proof.Cache.boundLru_bounded _ _ _
                                      have hmiss'' : (αCache state''.resources.cache).hit now { q with qname := nF } = [] := by
                                        rw [hcache'', ← htm]
                                        exact (hbnd.writeRefines (αTime state.now)).hit_nil (Nat.le_refl _) hmissF
                                      have hnmiss'' : (αCache state''.resources.cache).negHit now { q with qname := nF } = false := by
                                        rw [hcache'', ← htm]
                                        exact (hbnd.2.1 _ _).trans hnmissF
                                      have hqm'' : ∀ qu2 : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                          αQType qu2.qtype = some q.qtype ∧ αClass qu2.qclass = some q.qclass := by
                                        rw [hlq'']
                                        exact hqm
                                      have hCCM'' : CnameChainModels state'' { q with qname := nF } nseenF := by
                                        unfold CnameChainModels
                                        have hanchor'' : ((state''.lastQuery.bind (fun q0 => q0.question[0]?)).elim
                                            state''.resources.sname (fun qu => qu.qname)) = quL.qname := by
                                          rw [hlq'', hq0]
                                          show (q₀L.question[0]?).elim state''.resources.sname (fun qu => qu.qname) = quL.qname
                                          rw [hqu0]
                                          rfl
                                        rw [hanchor'', hchain'']
                                        exact hvisF
                                      have hqvalid'' : ∀ x ∈ nF, 0 < x.size ∧ x.size ≤ 63 :=
                                        fun x hx => αName_labels_valid hnF x hx
                                      have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                        rw [hsbelt'']; exact hGlBelt

                                      have hGlProv'' : GluelessProv state''.resources.slist := by
                                        rcases hslistD0 with h | ⟨nsNames, mc, hwC, heq⟩ | h
                                        · rw [h]; exact GluelessProv_default
                                        · rw [heq]
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (walkNs_names_canonical _ state.now hNsW 128 sname' nsNames mc (by exact hwC))
                                        · rw [h]; exact hGlBelt
                                      obtain ⟨s, v, cM, hrec, -, hrc', hans', hrest⟩ := IH mD (by omega) { q with qname := nF } depth f _ state''
                                        (αCache state''.resources.cache) _ w' now nseenF []
                                        state''.resources.slist.matchCount resp cout
                                        (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                        hmiss'' hnmiss'' (by intro b hb; simp at hb) rfl
                                        hGlProv'' hGlBelt''
                                        hqm'' (by exact hrd) (by exact hqstar) (by exact hqin) hclock'' hsnameCanon'' (by exact hlenF) (by exact hqvalid'') hCCM''
                                        (by
                                          rw [hchain'', hnow'']
                                          refine localAnswer_chain_answerWriteWf hwfW hNsW hCnW hwfrrW
                                            (congrArg chainOf hla) ?_
                                          rw [show Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord)
                                              state.cnameChain tcpRespA = state.cnameChain.push cnBytes from by
                                            simp only [Resolver.prependCnameLink, hqaR, hextRR]]
                                          exact answerWriteWf_push hAW
                                            (fun rr hp => answerWriteWf_of_wire hsan2 hrespAeq hclock hvalidAns
                                              hcanonAns cnBytes hcnMem rr hp))
                                        hstepC'' hrun
                                      rw [hlq'', hnow''] at hrest

                                      have hrecK : HasVerdictAt net ns ra ednsBuf rttOf now nseenF []
                                          (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                            (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                            (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now).boundLru
                                            (Server.roundTouches (Server.dropIfBizarre
                                              { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                              entry.name tcpRespA) tcpRespA) state.now))
                                          s { q with qname := nF } v cM := by
                                        rw [← hcache'']
                                        exact hrec
                                      rw [show αTime state.now = now from htm] at hcont
                                      obtain ⟨cOut, hcOut, -, ftr, rpath, tEnd2, respSub, hres, hagr⟩ :=
                                        hcont _ hbnd v s cM hrecK { v with answer := links ++ v.answer } rfl rfl
                                      have hcf0 := cname_link_write_WriteRefines_echo state.resources.cache tcpRespA qaR state.resources.sname
                                        q.qname state.now hqaR (question_from_decode hdec2 hsan2 (acceptResponse_some_eq hacc2) hqaR)
                                        hqaCI hsn htcF hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                        ({ aa := (tcpRespA.header.aa == 1), rcode := RCode.noError, answer := αSection tcpRespA.answer,
                                           authority := [], additional := [], ra := false, tc := false } : Response) c rfl rfl hmme
                                      rw [show state.now.toNat = now from htm] at hcf0
                                      have hrcOut : (αResp resp).rcode = v.rcode := hrc'
                                      have hansOut : (αResp resp).answer
                                          = αSection state.cnameChain ++ (cn :: (links ++ v.answer)) := by
                                        rw [hans', hchain'', hchainF,
                                          αSection_prependCnameLink state.cnameChain tcpRespA qaR cnBytes rrCn cn hqaR hextRR hprC hαcn]
                                        simp [List.append_assoc]
                                      have hclose : HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                            :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)))
                                          q { v with answer := cn :: (links ++ v.answer) } cM →
                                          ∃ slist v' coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v' coutM
                                            ∧ (modelSlistOf state.resources.slist).Subperm slist
                                            ∧ (αResp resp).rcode = v'.rcode
                                            ∧ (αResp resp).answer = αSection state.cnameChain ++ v'.answer
                                            ∧ CacheRefines (αCache cout) coutM
                                            ∧ WorldModels net ns ra ednsBuf now w'
                                            ∧ CacheWf cout state.now
                                            ∧ CacheNsCanon cout
                                            ∧ CacheCnameCanon cout
                                            ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                                            ∧ (∀ qu : VeriDNS.Spec.Question,
                                                (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                                CacheNegWf cout qu.qclass)
                                            ∧ CacheNsDistinct cout
                                            ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
                                            ∧ cout.records.size ≤ DnsCache.capacity
                                            ∧ AnswerWriteWf resp.answer state.now := by
                                        intro hv
                                        exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                            :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                          { v with answer := cn :: (links ++ v.answer) }, cM, hv,
                                          hpermAns.symm.subperm, hrcOut, hansOut, hrest⟩
                                      obtain ⟨origin, reply0, srcPort0, htransS, haccS, hragS, hclsLink, htcRS, _hauthS0, hvldS, hvldAS, hrefImplS⟩ := tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr) bytes2 raw2 tcpResp tcpRespA q hwmTcp hOr hdec2 hsan2 hacc2 hαQ htc0 (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                      have hreach : linkReach net ns ra origin = true := by
                                        cases htransS with
                                        | deliver hro hrr0 => exact hro
                                      exact hclose (trustedCname_hasVerdictAt net ns ra ednsBuf rttOf
                                        (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                        ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                        cn tgt (w.ids w.idCtr).toNat 0 c s ftr rpath tEnd2 cM respSub hmiss hnmiss
                                        (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                          { aa := (tcpRespA.header.aa == 1), rcode := RCode.noError, answer := αSection tcpRespA.answer,
                                            authority := [], additional := [], ra := false, tc := false })
                                        (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                        (accepts_reply _ _ _ _ _ _ _)
                                        hcnRR hqt hcnrd hfresh (Nat.le_refl now) rfl
                                        (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache tcpRespA
                                          (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname tcpRespA) tcpRespA.answer)
                                          (Resolver.credAnswer (tcpRespA.header.aa == 1)) state.now))
                                        hcf0
                                        cOut (hcOut.writeRefines now) hres
                                        { v with answer := cn :: (links ++ v.answer) }
                                        ⟨hagr.1, List.Perm.cons cn hagr.2⟩)
                                    ·

                                      exact absurd htcF0 htcF
                          rw [if_neg htcT, run_bind_pureSome] at hrun
                          dsimp only [] at hrun
                          by_cases hunf : Server.unfollowableDelegationB
                              (state.resources.slist.markQueried entry.name) state.resources.sname respA = true
                          ·
                            simp only [hunf, if_true] at hrun
                            obtain ⟨mu, hmu, hrun⟩ := run_log_bind_inv _ _ _ hrun
                            obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mu (by omega) q depth f _
                              { state with resources := { state.resources with
                                  slist := state.resources.slist.markQueried entry.name } }
                              c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                            exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                          ·
                            rw [if_neg hunf] at hrun
                            by_cases hfeT : (respA.header.rcode == VeriDNS.Spec.Rcode.formatError
                                && !state.noEdns) = true
                            case pos =>
                              -- RFC 6891 §6.2.2 (finding 055): FORMERR to an OPT-bearing sub-query —
                              -- retry without EDNS; an IH recursion with the noEdns flag set.
                              rw [if_pos hfeT] at hrun
                              obtain ⟨mf, hmf, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mf (by omega) q depth f _
                                { state with
                                  resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name },
                                  noEdns := true }
                                c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                              exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                            rw [if_neg hfeT] at hrun
                            by_cases hstT : (Resolver.probeRoundB state.resources.sname revealed
                                && Server.strictDenialB respA) = true
                            case pos =>
                              -- RFC 9156 §2.3 relaxed fallback (findings 051/064): a minimised-probe
                              -- NXDOMAIN is consumed and the loop re-probes with the full qname; no
                              -- verdict is delivered here, so this is an IH recursion like probe-consume.
                              rw [if_pos hstT] at hrun
                              obtain ⟨ms, hms, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH ms (by omega) q depth f _
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                              exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                            rw [if_neg hstT] at hrun
                            by_cases hpgT : (Resolver.probeRoundB state.resources.sname revealed
                                && !Server.probePassableB respA) = true
                            case pos =>
                              rw [if_pos hpgT] at hrun
                              obtain ⟨mq, hmq, hrun⟩ := run_log_bind_inv _ _ _ hrun
                              obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH mq (by omega) q depth f _
                                { state with resources := { state.resources with
                                    slist := state.resources.slist.markQueried entry.name } }
                                c _ w' now nseen seen depthFloor resp cout (by exact hSM) (by exact hwmTcp) (by exact hCacheWf) (by exact hNsCanon) (by exact hCnCanon) (by exact hwfrr) (by exact hNegWf) (by exact hNsDistinct) (by exact hOE) (by exact hCap) hmiss hnmiss hfreshInv (by exact hMC) (by exact GluelessProv_markQueried entry.name hGlProv) (by exact hGlBelt) (by exact hqm) hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) (by exact hstep) hrun
                              exact ⟨s, v, cM, hrec, by rw [modelSlistOf_markQueried] at hperm; exact hperm, hrc, hans, hrest⟩
                            rw [if_neg hpgT] at hrun
                            rw [Bool.not_eq_true] at hpgT
                            split at hrun
                            ·
                              rename_i result cacheR hAR
                              rw [run_pure'] at hrun
                              simp only [Option.some.injEq, Prod.mk.injEq] at hrun

                              obtain ⟨⟨hres, hcoutEq⟩, hwEq⟩ := hrun
                              subst hres
                              subst hcoutEq
                              subst hwEq
                              obtain ⟨hmme, hsn, htm, hwm⟩ := hSM
                              have hfull : Resolver.probeRoundB state.resources.sname revealed = false := by
                                cases hpr : Resolver.probeRoundB state.resources.sname revealed
                                · rfl
                                · rw [hpr, afterResume_finished_probePassable_false
                                      (state := { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } })
                                      (by exact hstep) hAR] at hpgT
                                  exact absurd hpgT (by decide)
                              have hαQ : αQuery subQuery0 = some q :=
                                αQuery_buildSubQuery hbuild hfull hsn hqm hrd
                              have hwmApp := hwm subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr)
                                d bytes resp0 respS respA q hO ha hdec hsani haccR hαQ
                              have hvalidAnsW : ∀ b ∈ respA.answer.toList, ∃ rr,
                                  VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                    ∧ αRR rr ≠ none := by
                                rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, hvalid, -⟩ |
                                  ⟨_, _, _, -, -, -, -, -, -, hvld, -⟩
                                · exact hvalid
                                · exact hvld
                              have hrespAeqW : respA = respS := acceptResponse_some_eq haccR
                              have hcanonAnsW : ∀ raw ∈ respA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                intro raw hmem
                                have hcapAnsW : respA.answer = resp0.answer.map Server.capTtlRR := by
                                  rw [hrespAeqW, show respS = Server.capTtls (Edns.stripOpt resp0) from by
                                    unfold Server.sanitizeTtlsCap at hsani
                                    exact (Option.some.inj hsani).symm]
                                  rfl
                                rw [hcapAnsW, Array.toList_map, List.mem_map] at hmem
                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                  (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                              have hAWwire : AnswerWriteWf respA.answer state.now :=
                                answerWriteWf_of_wire hsani hrespAeqW hclock hvalidAnsW hcanonAnsW
                              by_cases hansI : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = true
                              · have hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none := by
                                  simp only [Resolver.cnameToChase, hansI, if_true]
                                have hstepM : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := hstep
                                have hnotbiz := afterResume_finished_not_bizarre hstepM hcn hAR
                                -- A type-matching (`answersQueryB`) reply that FINISHED positively is
                                -- ENTITLED: an off-owner (non-entitled) type-matching answer retries
                                -- (`⇒ .continue`) rather than delivering, so finishing forces entitlement.
                                -- The `¬ NXDOMAIN` / `¬ truncation` premises are supplied by the honest
                                -- witness (covered honest replies are never `nameError`) and the tc split;
                                -- for the spoof case a non-entitled NXDOMAIN-with-data never finishes here.
                                have hqmNE := acceptResponse_questionMatches haccR
                                have hcoutB : cacheR = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
                                    (Server.roundTouches { state with resources := { state.resources with
                                      slist := state.resources.slist.markQueried entry.name } } respA) state.now := by
                                  by_cases htc1 : (respA.header.tc == 1) = true
                                  · -- truncated: `cacheUnlessTruncated` collapses; the write is the cache.
                                    exact afterResume_finished_pos_cout_tc _ entry.name respA resp hstepM hcn
                                      hnotbiz.1 hnotbiz.2 hansI htc1 hAR
                                  · rw [Bool.not_eq_true] at htc1
                                    -- untruncated: a type-matching (`answersQueryB`) reply that
                                    -- FINISHED positively took the ENTITLED arm.  A non-entitled
                                    -- type-match retries (`⇒ .continue`) — including a spoofed
                                    -- NXDOMAIN-with-answer, which the guarded NXDOMAIN arm
                                    -- (`nameError && answer.isEmpty`) now rejects rather than
                                    -- delivering (findings 036 / off-owner-A).  So no `¬ NXDOMAIN`
                                    -- premise is needed: the honest/spoof split collapses.
                                    have hentF : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) respA = true :=
                                      entitled_of_afterResume_finished_ok hstepM hcn hnotbiz.1 hnotbiz.2 htc1 hansI hAR
                                    exact (afterResume_answer_payload_pos_ent _ entry.name respA resp hstepM hcn
                                      hnotbiz.1 hnotbiz.2 hentF hAR).2
                                subst hcoutB
                                have hqm2 := acceptResponse_questionMatches haccR
                                by_cases htcT : (respA.header.tc == 1) = true
                                ·

                                  rw [show Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now = state.resources.cache from by
                                    simp only [Resolver.cacheUnlessTruncated, htcT, if_true]]
                                  obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                    cout_exports_bound state.resources.cache state.now c
                                      (Server.roundTouches { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } } respA) state.now
                                      hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hmme
                                  have hnegE : ∀ qu : VeriDNS.Spec.Question,
                                      (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                      CacheNegWf (state.resources.cache.boundLru
                                        (Server.roundTouches { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } } respA) state.now) qu.qclass :=
                                    fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu')
                                  by_cases hch : state.cnameChain = #[]
                                  · have hchainM : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).cnameChain = #[] := hch
                                    rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, _hcncorr, hvalid, hvalidAuth, _hcut, _hnscanon⟩ | hspoof
                                    · have hbridge : RespAgree (αResp resp) { ref with aa := false } :=
                                        respAgree_answer_bridge hstepM hcn hnotbiz.1 hnotbiz.2 hansI hAR hchainM hragA
                                      have hqm2 := acceptResponse_questionMatches haccR
                                      obtain ⟨r, hrmem, hrcov⟩ := positive_answer_covered hαQ hqm2 hansI hvalid hragA
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp), c,
                                        VeriDNS.Proof.WorldNetwork.serverAnswer_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q ref
                                          (w.ids w.idCtr).toNat 0 c hmiss hnmiss
                                          hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                          (isReferral_false_of_answer_ne_nil ref (List.ne_nil_of_mem hrmem))
                                          (serverAnswers_tc_false hans)
                                          (αResp resp) hbridge
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, rfl,
                                          by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [(afterResume_finished_payload_out _ entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                            exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                    · obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, _hclsLink, htcR, _hauthS, hvld, _hvldA, _hrefImpl⟩ := hspoof

                                      have hqm2S := acceptResponse_questionMatches haccR
                                      obtain ⟨r, hrmem, _hrcov⟩ := positive_answer_covered hαQ hqm2S hansI hvld hragS
                                      have hnrR : reply.msg.isReferral = false := isReferral_false_of_answer_ne_nil reply.msg (List.ne_nil_of_mem hrmem)
                                      have hbridge : RespAgree (αResp resp) { reply.msg with aa := false } :=
                                        respAgree_answer_bridge hstepM hcn hnotbiz.1 hnotbiz.2 hansI hAR hchainM hragS
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp), c,
                                        trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          (w.ids w.idCtr).toNat srcPort c reply hmiss hnmiss htrans hacc hnrR htcR
                                          (αResp resp) hbridge
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, rfl,
                                          by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                          hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                          hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                            rw [(afterResume_finished_payload_out _ entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                            exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                  ·

                                    have hout : resp = Resolver.finalizeAnswer
                                        { { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          with lastResponse := some respA, currentStep := .analyzeResponse } respA :=
                                      afterResume_finished_payload_out
                                        { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR
                                    have hrcP : (αResp resp).rcode = αRCode respA.header.rcode := by
                                      rw [hout]; exact finalizeAnswer_abstracts_rcode _ respA
                                    have hansP : (αResp resp).answer
                                        = αSection ({ { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          with lastResponse := some respA, currentStep := .analyzeResponse }
                                          : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord).cnameChain
                                        ++ αSection respA.answer := by
                                      rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
                                    have hqm2 := acceptResponse_questionMatches haccR
                                    rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, _hcncorr, hvalid, hvalidAuth, _hcut, _hnscanon⟩ | hspoof
                                    · obtain ⟨r, hrmem, hrcov⟩ := positive_answer_covered hαQ hqm2 hansI hvalid hragA
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp respA, c,
                                        VeriDNS.Proof.WorldNetwork.serverAnswer_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q ref
                                          (w.ids w.idCtr).toNat 0 c hmiss hnmiss
                                          hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                          (isReferral_false_of_answer_ne_nil ref (List.ne_nil_of_mem hrmem))
                                          (serverAnswers_tc_false hans)
                                          (αResp respA) hragA
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm,
                                        hrcP.trans (αResp_components respA).1.symm,
                                        by rw [(αResp_components respA).2.1]; exact hansP,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [(afterResume_finished_payload_out _ entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                          exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                    · obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, _hclsLink, htcR, _hauthS, hvld, _hvldA, _hrefImpl⟩ := hspoof
                                      obtain ⟨r, hrmem, _hrcov⟩ := positive_answer_covered hαQ hqm2 hansI hvld hragS
                                      have hnrR : reply.msg.isReferral = false := isReferral_false_of_answer_ne_nil reply.msg (List.ne_nil_of_mem hrmem)
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp respA, c,
                                        trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          (w.ids w.idCtr).toNat srcPort c reply hmiss hnmiss htrans hacc hnrR htcR
                                          (αResp respA) hragS
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm,
                                        hrcP.trans (αResp_components respA).1.symm,
                                        by rw [(αResp_components respA).2.1]; exact hansP,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [(afterResume_finished_payload_out _ entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                          exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                ·

                                  rw [Bool.not_eq_true] at htcT
                                  have hvalidAns : ∀ b ∈ respA.answer.toList, ∃ rr,
                                      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                        ∧ αRR rr ≠ none := by
                                    rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, hvalid, -⟩ |
                                      ⟨_, _, _, -, -, -, -, -, -, hvld, -⟩
                                    · exact hvalid
                                    · exact hvld
                                  have hvalW : ∀ b ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
                                      (Resolver.echoedQname respA) respA.answer).toList,
                                      ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                      (αRR rr).isSome = true := by
                                    intro b hb rr hpr
                                    obtain ⟨rr', hpr', hα'⟩ := hvalidAns b (ownerRaws_toList_sub hb)
                                    rw [hpr'] at hpr
                                    injection hpr with hrr
                                    subst hrr
                                    cases hα : αRR rr' with
                                    | none => exact absurd hα hα'
                                    | some r => rfl
                                  have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                  have hnoW : ∀ b ∈ (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
                                      (Resolver.echoedQname respA) respA.answer).toList,
                                      ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                      (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                    intro b hb rr hpr
                                    have hb' : b ∈ respS.answer := by
                                      rw [← hrespAeq]
                                      exact Array.mem_def.mpr (ownerRaws_toList_sub hb)
                                    have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                      (Or.inl (Or.inl hb')) rr hpr
                                    exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                  have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                    unfold Server.sanitizeTtlsCap at hsani
                                    exact (Option.some.inj hsani).symm
                                  have hcapAns : respA.answer = resp0.answer.map Server.capTtlRR := by
                                    rw [hrespAeq, hcapEq]; rfl
                                  have hcanonAns : ∀ raw ∈ respA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                    intro raw hmem
                                    rw [hcapAns, Array.toList_map, List.mem_map] at hmem
                                    obtain ⟨b0, hb0, rfl⟩ := hmem
                                    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                      (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                  have hwfW : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) state.now := by
                                    refine CacheWf_cacheUnlessTruncated _ _ _ _ _ hCacheWf ?_ ?_
                                    · unfold Resolver.credAnswer
                                      by_cases ha' : (respA.header.aa == 1) = true
                                      · rw [if_pos ha']; exact Or.inl rfl
                                      · rw [if_neg ha']; exact Or.inr (Or.inr (Or.inl rfl))
                                    · intro raw hraw rr hp
                                      exact parseRaw_entry_canonical _ state.now hp (normRaws_hval hvalW raw hraw rr hp) (normRaws_hno hnoW raw hraw rr hp)
                                  have hCnW : CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) := by
                                    refine CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hCnCanon ?_
                                    intro raw hraw rr hp htype
                                    exact canonicalRR_cnameRdata_canonical (hcanonAns raw (ownerRaws_toList_sub hraw)) hp htype
                                  have hwfrrW : ∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now).records,
                                      VeriDNS.Proof.NameTree.WfRR e.rr :=
                                    wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
                                  have hNsW : CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) := by
                                    refine CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hNsCanon ?_
                                    intro raw hraw rr hp htype
                                    exact canonicalRR_nsRdata_canonical (hcanonAns raw (ownerRaws_toList_sub hraw)) hp htype
                                  have hNsDW : CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) :=
                                    CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hNsDistinct
                                  have hOEW : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) :=
                                    VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hOE _ _ _ _
                                  obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                    cout_exports_bound (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                                      state.now
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                      (Server.roundTouches { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } } respA) state.now
                                      hwfW hNsW hCnW hwfrrW hNsDW hOEW (MatchMaxEquiv.refl _)
                                  have hnegE : ∀ qu2 : VeriDNS.Spec.Question,
                                      (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                      CacheNegWf ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
                                        (Server.roundTouches { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } } respA) state.now) qu2.qclass :=
                                    fun qu2 hqu2 => CacheNegWf_boundLru _ _
                                      (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu2 hqu2))

                                  obtain ⟨q₀W, quW, hq0W, hqu0W, hsubqW⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                  rw [subQuestion_full hfull quW] at hsubqW
                                  obtain ⟨qaW, hqaW, hqaCIW, -, -⟩ := questionMatches_fields
                                    (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubqW)
                                        (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                    (acceptResponse_questionMatches haccR)
                                  have hcf0 := answer_write_WriteRefines_echo state.resources.cache respA qaW state.resources.sname
                                    q.qname state.now hqaW (question_from_decode hdec hsani (acceptResponse_some_eq haccR) hqaW)
                                    hqaCIW hsn htcT hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                    ({ aa := (respA.header.aa == 1), rcode := αRCode respA.header.rcode,
                                       answer := αSection respA.answer, authority := [], additional := [],
                                       ra := false, tc := false } : VeriDNS.Spec.Net.Response) c rfl rfl hmme
                                  rw [show state.now.toNat = now from htm] at hcf0
                                  have hragSyn : RespAgree (αResp respA)
                                      ({ aa := (respA.header.aa == 1), rcode := αRCode respA.header.rcode,
                                         answer := αSection respA.answer, authority := [], additional := [],
                                         ra := false, tc := false } : VeriDNS.Spec.Net.Response) := by
                                    refine ⟨(αResp_components respA).1, ?_⟩
                                    rw [(αResp_components respA).2.1]
                                  obtain ⟨r, hrmem, -⟩ := positive_answer_covered hαQ hqm2 hansI hvalidAns hragSyn
                                  have hnrSyn := isReferral_false_of_answer_ne_nil _ (List.ne_nil_of_mem hrmem)
                                  obtain ⟨org, hreach⟩ : ∃ org : String, linkReach net ns ra org = true := by
                                    rcases hwmApp with ⟨srv, tr, ref, -, -, -, hreachA, -⟩ |
                                      ⟨origin, reply, srcPort0, htransS, -⟩
                                    · exact ⟨_, hreachA⟩
                                    · cases htransS with
                                      | deliver hro hrr0 => exact ⟨origin, hro⟩
                                  by_cases hch : state.cnameChain = #[]
                                  · have hchainM : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).cnameChain = #[] := hch
                                    have hbridge : RespAgree (αResp resp)
                                        { ({ aa := (respA.header.aa == 1), rcode := αRCode respA.header.rcode,
                                             answer := αSection respA.answer, authority := [], additional := [],
                                             ra := false, tc := false } : VeriDNS.Spec.Net.Response) with aa := false } :=
                                      respAgree_answer_bridge hstepM hcn hnotbiz.1 hnotbiz.2 hansI hAR hchainM hragSyn
                                    exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp),
                                      αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now),
                                      trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                        (byteAddrToModel (Server.ipv4ToAddr ipAddr)) org
                                        ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                        (w.ids w.idCtr).toNat 0 c
                                        (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                          { aa := (respA.header.aa == 1), rcode := αRCode respA.header.rcode,
                                            answer := αSection respA.answer, authority := [], additional := [],
                                            ra := false, tc := false })
                                        hmiss hnmiss
                                        (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                        (accepts_reply _ _ _ _ _ _ _)
                                        hnrSyn rfl
                                        (αResp resp) hbridge
                                        (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache respA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                          (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                        (Or.inl hcf0)
                                        (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache respA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                          (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                        (WriteRefines.refl now _),
                                      hpermAns.symm.subperm, rfl,
                                      by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                      hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                      hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                        rw [(afterResume_finished_payload_out _ entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                        exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                  ·

                                    have hout : resp = Resolver.finalizeAnswer
                                        { { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          with lastResponse := some respA, currentStep := .analyzeResponse } respA :=
                                      afterResume_finished_payload_out
                                        { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR
                                    have hrcP : (αResp resp).rcode = αRCode respA.header.rcode := by
                                      rw [hout]; exact finalizeAnswer_abstracts_rcode _ respA
                                    have hansP : (αResp resp).answer
                                        = αSection ({ { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          with lastResponse := some respA, currentStep := .analyzeResponse }
                                          : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord).cnameChain
                                        ++ αSection respA.answer := by
                                      rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain]
                                    have hbridge2 : RespAgree (αResp respA)
                                        { ({ aa := (respA.header.aa == 1), rcode := αRCode respA.header.rcode,
                                             answer := αSection respA.answer, authority := [], additional := [],
                                             ra := false, tc := false } : VeriDNS.Spec.Net.Response) with aa := false } := by
                                      refine ⟨(αResp_components respA).1, ?_⟩
                                      rw [(αResp_components respA).2.1]
                                    exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp respA,
                                      αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now),
                                      trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                        (byteAddrToModel (Server.ipv4ToAddr ipAddr)) org
                                        ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                        (w.ids w.idCtr).toNat 0 c
                                        (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                          { aa := (respA.header.aa == 1), rcode := αRCode respA.header.rcode,
                                            answer := αSection respA.answer, authority := [], additional := [],
                                            ra := false, tc := false })
                                        hmiss hnmiss
                                        (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                        (accepts_reply _ _ _ _ _ _ _)
                                        hnrSyn rfl
                                        (αResp respA) hbridge2
                                        (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache respA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                          (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                        (Or.inl hcf0)
                                        (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          state.resources.cache respA
                                          (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                          (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                        (WriteRefines.refl now _),
                                      hpermAns.symm.subperm,
                                      hrcP.trans (αResp_components respA).1.symm,
                                      by rw [(αResp_components respA).2.1]; exact hansP,
                                      hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                      hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                        rw [(afterResume_finished_payload_out _ entry.name respA resp hstepM hcn hnotbiz.1 hnotbiz.2 hAR)]
                                        exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                              ·
                                by_cases hcn2 : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none
                                · have hstepM2 : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := hstep
                                  have hnotbiz2 := afterResume_finished_not_bizarre hstepM2 hcn2 hAR
                                  have hansF0 : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false := by
                                    simpa using hansI

                                  have hcoutB : cacheR = state.resources.cache.boundLru
                                      (Server.roundTouches { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } } respA) state.now :=
                                    (afterResume_finished_payload_neg _ entry.name respA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR).2
                                  subst hcoutB
                                  obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                    cout_exports_bound state.resources.cache state.now c
                                      (Server.roundTouches { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } } respA) state.now
                                      hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hmme
                                  have hnegE : ∀ qu : VeriDNS.Spec.Question,
                                      (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                      CacheNegWf (state.resources.cache.boundLru
                                        (Server.roundTouches { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } } respA) state.now) qu.qclass :=
                                    fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu')
                                  by_cases hch2 : state.cnameChain = #[]
                                  · have hchainM2 : (({ state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)).cnameChain = #[] := hch2
                                    rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, _hcncorr, hvalid, hvalidAuth, _hcut, _hnscanon⟩ | hspoof
                                    ·
                                      have hansF : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false := by
                                        simpa using hansI
                                      have hirref : (αResp respA).isReferral = false :=
                                        αResp_isReferral_false_of_finished hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF hAR hvalid hvalidAuth
                                      have hnr : ref.isReferral = false := by rw [← hisref]; exact hirref
                                      obtain ⟨q₀X, quX, hq0X, hqu0X, hsubqX⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                      rw [subQuestion_full hfull quX] at hsubqX
                                      obtain ⟨qaX, hqaX, hqaCIX, -, -⟩ := questionMatches_fields
                                        (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubqX)
                                            (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                        (acceptResponse_questionMatches haccR)
                                      have hcnNone : VeriDNS.Spec.Net.cnameRR q.qname ref.answer = none := by
                                        apply hcnbi.mp
                                        rw [(αResp_components respA).2.1]
                                        exact cnameToChase_none_model hcn2 hansF hqaX
                                          (question_from_decode hdec hsani (acceptResponse_some_eq haccR) hqaX) hqaCIX hsn
                                      have hbridge : RespAgree (αResp resp) { ref with aa := false } :=
                                        respAgree_finished_bridge hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hAR hchainM2 hragA
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp), c,
                                        VeriDNS.Proof.WorldNetwork.serverAnswer_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q ref
                                          (w.ids w.idCtr).toNat 0 c hmiss hnmiss
                                          hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                          hnr (serverAnswers_tc_false hans)
                                          (αResp resp) hbridge
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, rfl,
                                        by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [(afterResume_finished_payload_neg _ entry.name respA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR).1]
                                          exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                    ·
                                      obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, hclsLink, htcR, _hauthS, hvld, hvldA, _hrefImpl⟩ := hspoof
                                      have hansF : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false := by simpa using hansI
                                      have hirref : (αResp respA).isReferral = false :=
                                        αResp_isReferral_false_of_finished hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF hAR hvld hvldA
                                      have hnrR : reply.msg.isReferral = false := by rw [← hclsLink]; exact hirref
                                      have hbridge : RespAgree (αResp resp) { reply.msg with aa := false } :=
                                        respAgree_finished_bridge hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hAR hchainM2 hragS
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), (αResp resp), c,
                                        trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          (w.ids w.idCtr).toNat srcPort c reply hmiss hnmiss htrans hacc hnrR htcR
                                          (αResp resp) hbridge
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, rfl,
                                        by rw [show state.cnameChain = #[] from ‹_›]; rfl,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [(afterResume_finished_payload_neg _ entry.name respA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR).1]
                                          exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                  ·

                                    have hpay := afterResume_finished_payload_neg
                                      { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA resp hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF0 hAR
                                    have hrcD : (αResp resp).rcode = (αResp respA).rcode := by
                                      rw [hpay.1]; exact (finalizeAnswer_abstracts_rcode _ respA).trans (αResp_components respA).1.symm
                                    have hansD2 : (αResp resp).answer = αSection state.cnameChain ++ (αResp respA).answer := by
                                      rw [hpay.1, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, (αResp_components respA).2.1]
                                    have hansF : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) respA = false := by simpa using hansI
                                    rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, _hcncorr, hvalid, hvalidAuth, _hcut, _hnscanon⟩ | hspoof
                                    · have hirref : (αResp respA).isReferral = false :=
                                        αResp_isReferral_false_of_finished hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF hAR hvalid hvalidAuth
                                      have hnr : ref.isReferral = false := by rw [← hisref]; exact hirref
                                      obtain ⟨q₀X, quX, hq0X, hqu0X, hsubqX⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                      rw [subQuestion_full hfull quX] at hsubqX
                                      obtain ⟨qaX, hqaX, hqaCIX, -, -⟩ := questionMatches_fields
                                        (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubqX)
                                            (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                        (acceptResponse_questionMatches haccR)
                                      have hcnNone : VeriDNS.Spec.Net.cnameRR q.qname ref.answer = none := by
                                        apply hcnbi.mp
                                        rw [(αResp_components respA).2.1]
                                        exact cnameToChase_none_model hcn2 hansF hqaX
                                          (question_from_decode hdec hsani (acceptResponse_some_eq haccR) hqaX) hqaCIX hsn
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp respA, c,
                                        VeriDNS.Proof.WorldNetwork.serverAnswer_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q ref
                                          (w.ids w.idCtr).toNat 0 c hmiss hnmiss
                                          hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra)
                                          hnr (serverAnswers_tc_false hans)
                                          (αResp respA) hragA
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, hrcD, hansD2,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [hpay.1]
                                          exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                    · obtain ⟨origin, reply, srcPort, htrans, hacc, hragS, hclsLink, htcR, _hauthS, hvld, hvldA, _hrefImpl⟩ := hspoof
                                      have hirref : (αResp respA).isReferral = false :=
                                        αResp_isReferral_false_of_finished hstepM2 hcn2 hnotbiz2.1 hnotbiz2.2 hansF hAR hvld hvldA
                                      have hnrR : reply.msg.isReferral = false := by rw [← hclsLink]; exact hirref
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr) :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)), αResp respA, c,
                                        trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          (w.ids w.idCtr).toNat srcPort c reply hmiss hnmiss htrans hacc hnrR htcR
                                          (αResp respA) hragS
                                          c (Or.inr rfl) c (WriteRefines.refl now c), hpermAns.symm.subperm, hrcD, hansD2,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [hpay.1]
                                          exact answerWriteWf_finalize (by exact hAW) hAWwire⟩
                                ·

                                  obtain ⟨target, hcnT⟩ := Option.ne_none_iff_exists'.mp hcn2
                                  obtain ⟨q₀L, quL, hq0, hqu0, hsubq⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                  rw [subQuestion_full hfull quL] at hsubq
                                  have hqmL := hqm quL ⟨q₀L, hq0, hqu0⟩
                                  obtain ⟨qaR, hqaR, hqaCI, hqaT, _hqaC⟩ := questionMatches_fields
                                    (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubq)
                                        (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                    (acceptResponse_questionMatches haccR)
                                  have hqt : q.qtype.covers RRType.cname = false :=
                                    covers_cname_false_of_chase respA target qaR q hcnT hqaR
                                      (by rw [hqaT]; exact hqmL.1) hqstar
                                  obtain ⟨t, ht, hqq⟩ := αQType_rr_inv hqmL.1 hqstar
                                  have htne : t ≠ RRType.cname := by
                                    intro hteq
                                    rw [hqq, hteq] at hqt
                                    exact absurd hqt (by decide)
                                  by_cases htcT : (respA.header.tc == 1) = true
                                  ·

                                    obtain ⟨stT, hART, hstch, hstlq, hstca, hstnw⟩ := afterResume_cname_truncated
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA target (by exact hstep) hcnT htcT
                                    rw [hART] at hAR
                                    injection hAR with h1 hcoT
                                    injection h1 with hpay

                                    have hcoutB : cacheR = state.resources.cache.boundLru
                                        (Server.roundTouches (Server.dropIfBizarre
                                          { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA) respA) state.now := by
                                      rw [← hcoT]
                                      show stT.resources.cache.boundLru
                                        (Server.roundTouches (Server.dropIfBizarre
                                          { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA) respA) stT.now = _
                                      rw [show stT.resources.cache = state.resources.cache from by exact hstca,
                                        show stT.now = state.now from by exact hstnw]
                                    subst hcoutB
                                    obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                      cout_exports_bound state.resources.cache state.now c
                                        (Server.roundTouches (Server.dropIfBizarre
                                          { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA) respA) state.now
                                        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hmme
                                    have hnegE : ∀ qu : VeriDNS.Spec.Question,
                                        (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                        CacheNegWf (state.resources.cache.boundLru
                                          (Server.roundTouches (Server.dropIfBizarre
                                            { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                            entry.name respA) respA) state.now) qu.qclass :=
                                      fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu')
                                    have hpay' : resp = Resolver.finalizeAnswer stT respA := hpay.symm
                                    have hrcD : (αResp resp).rcode = (αResp respA).rcode := by
                                      rw [hpay']
                                      exact (finalizeAnswer_abstracts_rcode _ respA).trans (αResp_components respA).1.symm
                                    have hansD2 : (αResp resp).answer
                                        = αSection state.cnameChain ++ (αResp respA).answer := by
                                      rw [hpay', (αResp_components _).2.1, finalizeAnswer_answer,
                                        αSection_prependChain, hstch, (αResp_components respA).2.1]
                                    rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, hcncorr,
                                      hvalid2, hvalidAuth2, hcut2, hnstail2⟩ |
                                      ⟨origin, reply0, srcPort0, htransS, haccS, hragS, hclsLink, htcRS, _hauthS0, hvldS, hvldAS, hrefImplS⟩
                                    ·
                                      exfalso
                                      have htcImplF : (respA.header.tc == 1) = false := by
                                        rw [hnstail2.2.2.2.2.2.2]
                                        exact serverAnswers_tc_false hans
                                      rw [htcImplF] at htcT
                                      exact Bool.noConfusion htcT
                                    ·
                                      have hnrR : reply0.msg.isReferral = false := by
                                        by_cases hri : reply0.msg.isReferral = true
                                        · obtain ⟨-, -, -, -, -, -, htcEg⟩ := hrefImplS hri
                                          rw [htcEg.trans htcRS] at htcT
                                          exact Bool.noConfusion htcT
                                        · rw [Bool.not_eq_true] at hri; exact hri
                                      exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                          :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                        αResp respA, c,
                                        trustedReply_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                          ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          (w.ids w.idCtr).toNat srcPort0 c reply0 hmiss hnmiss htransS haccS hnrR htcRS
                                          (αResp respA) hragS
                                          c (Or.inr rfl) c (WriteRefines.refl now c),
                                        hpermAns.symm.subperm, hrcD, hansD2,
                                        hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                        hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                          rw [hpay']
                                          exact answerWriteWf_finalize (by rw [hstch]; exact hAW) hAWwire⟩
                                  rw [Bool.not_eq_true] at htcT
                                  obtain ⟨hnrev, hdisj⟩ := afterResume_cname_ok_inv
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    entry.name respA q₀L target quL resp hstep hcnT htcT hq0 hqu0 hAR
                                  have hvalidAns : ∀ b ∈ respA.answer.toList, ∃ rr,
                                      VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                        ∧ αRR rr ≠ none := by
                                    rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, hvalid, -⟩ |
                                      ⟨_, _, _, -, -, -, -, -, -, hvld, -⟩
                                    · exact hvalid
                                    · exact hvld
                                  have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                  have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                    unfold Server.sanitizeTtlsCap at hsani
                                    exact (Option.some.inj hsani).symm
                                  have hcapAns : respA.answer = resp0.answer.map Server.capTtlRR := by
                                    rw [hrespAeq, hcapEq]; rfl
                                  have hquesEq : respA.question = resp0.question := by
                                    rw [hrespAeq, hcapEq]; rfl
                                  have hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR := by
                                    have hqaR0 : resp0.question[0]? = some qaR := by
                                      rw [← hquesEq]; exact hqaR
                                    obtain ⟨-, -, -, -, hqs, -, -, -⟩ :=
                                      VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec
                                    rw [Array.getElem?_eq_some_iff] at hqaR0
                                    obtain ⟨hlt, hget⟩ := hqaR0
                                    exact hget ▸ hqs ⟨0, hlt⟩
                                  obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
                                  have hqnRq : VeriDNS.Spec.Net.nameEq qnR q.qname = true := by
                                    obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
                                    obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
                                    exact hne'
                                  obtain ⟨quE, hquE, hextQ⟩ := (cnameToChase_some respA target hcnT).2
                                  rw [show quE = qaR from Option.some.inj (hquE.symm.trans hqaR)] at hextQ
                                  obtain ⟨cnBytes, rrCn, cn, tgt, hextRR, hcnMem, hprC, hty5, hrdT, hαcn, hcnRR, hcnrd, hαtgt⟩ :=
                                    cname_link_facts hαR hcanR hvalR hextQ hvalidAns
                                  rw [VeriDNS.Spec.Net.cnameRR_congr hqnRq] at hcnRR
                                  have hcanonAns : ∀ raw ∈ respA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                    intro raw hmem
                                    rw [hcapAns, Array.toList_map, List.mem_map] at hmem
                                    obtain ⟨b0, hb0, rfl⟩ := hmem
                                    exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                      (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                  obtain ⟨na0, hna0, hnacan0, hnaval0, hnalen0⟩ :=
                                    canonicalRR_cnameRdata_canonical (hcanonAns cnBytes hcnMem) hprC hty5
                                  have hna0tgt : na0 = tgt := by
                                    rw [hrdT] at hna0
                                    exact Option.some.inj (hna0.symm.trans hαtgt)
                                  rw [hna0tgt] at hnacan0 hnaval0 hnalen0
                                  have htB : target = VeriDNS.Impl.DomainName.labelsToWireFormatGo tgt := by
                                    rw [← hrdT]; exact hnacan0
                                  have hfresh : tgt ∉ q.qname :: nseen :=
                                    cname_target_fresh state q nseen target tgt hCCM htB hnaval0 hnrev
                                  have hvalW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                      (Resolver.echoedQname respA) respA.answer).toList,
                                      ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                      (αRR rr).isSome = true := by
                                    intro b hb rr hpr
                                    obtain ⟨rr', hpr', hα'⟩ := hvalidAns b (cnameRaws_toList_sub hb)
                                    rw [hpr'] at hpr
                                    injection hpr with hrr
                                    subst hrr
                                    cases hα : αRR rr' with
                                    | none => exact absurd hα hα'
                                    | some r => rfl
                                  have hnoW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                      (Resolver.echoedQname respA) respA.answer).toList,
                                      ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                      (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                    intro b hb rr hpr
                                    have hb' : b ∈ respS.answer := by
                                      rw [← hrespAeq]
                                      exact Array.mem_def.mpr (cnameRaws_toList_sub hb)
                                    have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                      (Or.inl (Or.inl hb')) rr hpr
                                    exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                  have hwfW : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) state.now := by
                                    refine CacheWf_cacheUnlessTruncated _ _ _ _ _ hCacheWf ?_ ?_
                                    · unfold Resolver.credAnswer
                                      by_cases ha : (respA.header.aa == 1) = true
                                      · rw [if_pos ha]; exact Or.inl rfl
                                      · rw [if_neg ha]; exact Or.inr (Or.inr (Or.inl rfl))
                                    · intro raw hraw rr hp
                                      exact parseRaw_entry_canonical _ state.now hp (normRaws_hval hvalW raw hraw rr hp) (normRaws_hno hnoW raw hraw rr hp)
                                  have hCnW : CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) := by
                                    refine CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hCnCanon ?_
                                    intro raw hraw rr hp htype
                                    exact canonicalRR_cnameRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                  have hwfrrW : ∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now).records,
                                      VeriDNS.Proof.NameTree.WfRR e.rr :=
                                    wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
                                  have hnegwfW : CacheNegWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) quL.qclass :=
                                    CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf quL ⟨q₀L, hq0, hqu0⟩)

                                  have hNsW : CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) := by
                                    refine CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hNsCanon ?_
                                    intro raw hraw rr hp htype
                                    exact canonicalRR_nsRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                  have hNsDW : CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) :=
                                    CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hNsDistinct
                                  have hOEW : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                      state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now) :=
                                    VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hOE _ _ _ _
                                  obtain ⟨hcrE, hwfE, hnsE, hcnE, hwfrrE, hnsdE, hoeE, hcapE⟩ :=
                                    cout_exports_bound (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                                      state.now
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                      (Server.roundTouches (Server.dropIfBizarre
                                        { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA) respA) state.now
                                      hwfW hNsW hCnW hwfrrW hNsDW hOEW (MatchMaxEquiv.refl _)
                                  have hnegE : ∀ qu2 : VeriDNS.Spec.Question,
                                      (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                      CacheNegWf ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                        state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
                                        (Server.roundTouches (Server.dropIfBizarre
                                          { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA) respA) state.now) qu2.qclass :=
                                    fun qu2 hqu2 => CacheNegWf_boundLru _ _
                                      (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu2 hqu2))
                                  have hanchor : ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim
                                      state.resources.sname (fun qu => qu.qname)) = quL.qname := by
                                    rw [hq0]
                                    show (q₀L.question[0]?).elim state.resources.sname (fun qu => qu.qname) = quL.qname
                                    rw [hqu0]
                                    rfl
                                  have hCCM' : ∀ nm ∈ q.qname :: nseen, ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                                      quL.qname state.cnameChain).toList,
                                      αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                        ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                    have h := hCCM
                                    unfold CnameChainModels at h
                                    rw [hanchor] at h
                                    exact h
                                  have hpre : Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA
                                      = state.cnameChain.push cnBytes := by
                                    unfold Resolver.prependCnameLink
                                    simp only [hqaR, hextRR]
                                  have hvtl : (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)).toList
                                      = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname state.cnameChain).toList
                                        ++ [VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn] := by
                                    rw [hpre]
                                    exact cnameChaseVisited_push quL.qname state.cnameChain hprC
                                  have hvis : ∀ nm ∈ tgt :: (q.qname :: nseen),
                                      ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)).toList,
                                      αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                        ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                    intro nm hnm
                                    rcases List.mem_cons.mp hnm with rfl | hnm
                                    · refine ⟨target, ?_, hαtgt, htB, hnaval0⟩
                                      rw [hvtl]
                                      refine List.mem_append_right _ ?_
                                      rw [show VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn
                                        = rrCn.rdata from rfl, hrdT]
                                      exact List.mem_singleton.mpr rfl
                                    · obtain ⟨b, hb, hf⟩ := hCCM' nm hnm
                                      refine ⟨b, ?_, hf⟩
                                      rw [hvtl]
                                      exact List.mem_append_left _ hb
                                  rcases hdisj with ⟨snameF, chainF, rrs, st, hla, hout, hstch, hcoutW⟩ |
                                    ⟨rc, soaAuth, chainF, st, hla, hout, hstch, hcoutW⟩
                                  ·
                                    obtain ⟨links, hchainF, hcont⟩ := localAnswer_chase_peel net ns ra ednsBuf rttOf
                                      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                      quL.qtype quL.qclass state.now q t [] quL.qname ht hqq htne hqmL.2
                                      (MatchMaxEquiv.refl _) hwfW hCnW hwfrrW hnegwfW 8 target tgt
                                      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
                                      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
                                      (q.qname :: nseen) (.answerHit snameF chainF rrs) hla hαtgt htB hnaval0
                                      hnalen0 rfl hvis
                                    obtain ⟨hnegF, hansF, hneF⟩ := localAnswer_answerHit_inv _ quL.qtype quL.qclass
                                      state.now 8 target _ _ snameF chainF rrs hla
                                    have hrrsPr : ∀ rr ∈ rrs.toList, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
                                        (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) rr) = some rr := by
                                      intro rr hrr
                                      rw [← hansF] at hrr
                                      exact lookupAnswerable_parseRaw_rrBytes hwfrrW hrr
                                    have hsecRRS : αSection (Resolver.cacheResponse q₀L rrs).answer = rrs.toList.filterMap αRR :=
                                      αSection_map_rrBytes rrs hrrsPr
                                    have hanseq : (αResp resp).answer
                                        = αSection state.cnameChain ++ (cn :: (links ++ rrs.toList.filterMap αRR)) := by
                                      rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hstch,
                                        hchainF, αSection_prependCnameLink state.cnameChain respA qaR cnBytes rrCn cn hqaR hextRR hprC hαcn,
                                        hsecRRS]
                                      simp [List.append_assoc]
                                    have hrceq : (αResp resp).rcode = RCode.noError := by
                                      rw [hout, (αResp_components _).1, finalizeAnswer_rcode]
                                      rfl

                                    subst hcoutW
                                    have hcf0 := cname_link_write_WriteRefines_echo state.resources.cache respA qaR state.resources.sname
                                      q.qname state.now hqaR (question_from_decode hdec hsani (acceptResponse_some_eq haccR) hqaR)
                                      hqaCI hsn htcT hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                      ({ aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                         authority := [], additional := [], ra := false, tc := false } : Response) c rfl rfl hmme
                                    rw [show state.now.toNat = now from htm] at hcf0
                                    have hv := hcont (Response.mk false RCode.noError (links ++ rrs.toList.filterMap αRR) [] [] false false)
                                      rfl rfl []
                                    rw [show αTime state.now = now from htm] at hv
                                    obtain ⟨ftr, rpath, tEnd2, respSub, hres, hagr⟩ := hv

                                    exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                        :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                      Response.mk false RCode.noError (cn :: (links ++ rrs.toList.filterMap αRR)) [] [] false false,
                                      αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now),
                                      (by
                                        rcases hwmApp with ⟨srv, tr, ref, hfind, hans, -, hreachA, hfit, -, -, hansEq,
                                            -, -, -, -, -, -, -, haaEq, -, htcEq⟩ |
                                          ⟨origin, reply0, srcPort0, htransS, -⟩
                                        ·
                                          have habs : c.absorb now q.qname
                                              (({ aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                                  authority := [], additional := [], ra := false, tc := false } : Response).cnameOwned q.qname)
                                              = c.absorb now q.qname (ref.cnameOwned q.qname) :=
                                            absorb_resp_congr _ _ _ (by simpa using haaEq)
                                              (by simp only [Response.cnameOwned_answer]; rw [hansEq]) rfl rfl
                                          exact cname_classifier_bridge_at net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr))
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            srv tr ref cn tgt (w.ids w.idCtr).toNat 0 c [] ftr rpath tEnd2
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            respSub hmiss hnmiss hfind hans hreachA
                                            (VeriDNS.Proof.WorldNetwork.reach_self net ns ra) hfit
                                            (by rw [← hansEq]; exact hcnRR) hqt hcnrd hfresh (Nat.le_refl now)
                                            (htcEq.symm.trans htcT)
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            (by rw [← habs]; exact hcf0)
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            (WriteRefines.refl now _) hres
                                            (Response.mk false RCode.noError (cn :: (links ++ rrs.toList.filterMap αRR)) [] [] false false)
                                            ⟨hagr.1, List.Perm.cons cn hagr.2⟩
                                        ·
                                          have hreach : linkReach net ns ra origin = true := by
                                            cases htransS with
                                            | deliver hro hrr0 => exact hro
                                          exact trustedCname_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            cn tgt (w.ids w.idCtr).toNat 0 c [] ftr rpath tEnd2
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            respSub hmiss hnmiss
                                            (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                                (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                              { aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                                authority := [], additional := [], ra := false, tc := false })
                                            (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                            (accepts_reply _ _ _ _ _ _ _)
                                            hcnRR hqt hcnrd hfresh (Nat.le_refl now) rfl
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            hcf0
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            (WriteRefines.refl now _) hres
                                            (Response.mk false RCode.noError (cn :: (links ++ rrs.toList.filterMap αRR)) [] [] false false)
                                            ⟨hagr.1, List.Perm.cons cn hagr.2⟩),
                                      hpermAns.symm.subperm, hrceq, hanseq,
                                      hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                      hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                        rw [hout]
                                        refine answerWriteWf_finalize ?_ ?_
                                        · rw [hstch]
                                          refine localAnswer_chain_answerWriteWf hwfW hNsW hCnW hwfrrW
                                            (congrArg chainOf hla) ?_
                                          rw [hpre]
                                          exact answerWriteWf_push hAW
                                            (fun rr hp => hAWwire cnBytes hcnMem rr hp)
                                        · have hrrs' : rrs = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now).lookupAnswerable snameF quL.qtype quL.qclass state.now := by
                                            rw [← hansF]; rfl
                                          show AnswerWriteWf (rrs.map
                                            (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord))) state.now
                                          rw [hrrs']
                                          exact answerWriteWf_lookup_map hwfW hNsW hCnW hwfrrW⟩
                                  ·
                                    obtain ⟨links, hchainF, hcont⟩ := localAnswer_chase_peel net ns ra ednsBuf rttOf
                                      (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                      quL.qtype quL.qclass state.now q t [] quL.qname ht hqq htne hqmL.2
                                      (MatchMaxEquiv.refl _) hwfW hCnW hwfrrW hnegwfW 8 target tgt
                                      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
                                      (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                        (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
                                      (q.qname :: nseen) (.negative rc soaAuth chainF) hla hαtgt htB hnaval0
                                      hnalen0 rfl hvis
                                    have hanseq : (αResp resp).answer
                                        = αSection state.cnameChain ++ (cn :: links) := by
                                      rw [hout, (αResp_components _).2.1, finalizeAnswer_answer, αSection_prependChain, hstch,
                                        hchainF, αSection_prependCnameLink state.cnameChain respA qaR cnBytes rrCn cn hqaR hextRR hprC hαcn,
                                        show αSection (Resolver.negativeResponse q₀L rc soaAuth).answer = [] from rfl]
                                      simp [List.append_assoc]
                                    have hrceq : (αResp resp).rcode = αRCode rc := by
                                      rw [hout, (αResp_components _).1, finalizeAnswer_rcode]
                                      rfl

                                    subst hcoutW
                                    have hcf0 := cname_link_write_WriteRefines_echo state.resources.cache respA qaR state.resources.sname
                                      q.qname state.now hqaR (question_from_decode hdec hsani (acceptResponse_some_eq haccR) hqaR)
                                      hqaCI hsn htcT hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                      ({ aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                         authority := [], additional := [], ra := false, tc := false } : Response) c rfl rfl hmme
                                    rw [show state.now.toNat = now from htm] at hcf0
                                    have hv := hcont (Response.mk false (αRCode rc) links [] [] false false) rfl rfl []
                                    rw [show αTime state.now = now from htm] at hv
                                    obtain ⟨ftr, rpath, tEnd2, respSub, hres, hagr⟩ := hv
                                    exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                        :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                      Response.mk false (αRCode rc) (cn :: links) [] [] false false,
                                      αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now),
                                      (by
                                        rcases hwmApp with ⟨srv, tr, ref, hfind, hans, -, hreachA, hfit, -, -, hansEq,
                                            -, -, -, -, -, -, -, haaEq, -, htcEq⟩ |
                                          ⟨origin, reply0, srcPort0, htransS, -⟩
                                        ·
                                          have habs : c.absorb now q.qname
                                              (({ aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                                  authority := [], additional := [], ra := false, tc := false } : Response).cnameOwned q.qname)
                                              = c.absorb now q.qname (ref.cnameOwned q.qname) :=
                                            absorb_resp_congr _ _ _ (by simpa using haaEq)
                                              (by simp only [Response.cnameOwned_answer]; rw [hansEq]) rfl rfl
                                          exact cname_classifier_bridge_at net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr))
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            srv tr ref cn tgt (w.ids w.idCtr).toNat 0 c [] ftr rpath tEnd2
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            respSub hmiss hnmiss hfind hans hreachA
                                            (VeriDNS.Proof.WorldNetwork.reach_self net ns ra) hfit
                                            (by rw [← hansEq]; exact hcnRR) hqt hcnrd hfresh (Nat.le_refl now)
                                            (htcEq.symm.trans htcT)
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            (by rw [← habs]; exact hcf0)
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            (WriteRefines.refl now _) hres
                                            (Response.mk false (αRCode rc) (cn :: links) [] [] false false)
                                            ⟨hagr.1, List.Perm.cons cn hagr.2⟩
                                        ·
                                          have hreach : linkReach net ns ra origin = true := by
                                            cases htransS with
                                            | deliver hro hrr0 => exact hro
                                          exact trustedCname_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            cn tgt (w.ids w.idCtr).toNat 0 c [] ftr rpath tEnd2
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            respSub hmiss hnmiss
                                            (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                                (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                              { aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                                authority := [], additional := [], ra := false, tc := false })
                                            (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                            (accepts_reply _ _ _ _ _ _ _)
                                            hcnRR hqt hcnrd hfresh (Nat.le_refl now) rfl
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            hcf0
                                            (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                              (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                              (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                            (WriteRefines.refl now _) hres
                                            (Response.mk false (αRCode rc) (cn :: links) [] [] false false)
                                            ⟨hagr.1, List.Perm.cons cn hagr.2⟩),
                                      hpermAns.symm.subperm, hrceq, hanseq,
                                      hcrE, WorldModels_oracle net ns ra ednsBuf now rfl hwm,
                                      hwfE, hnsE, hcnE, hwfrrE, hnegE, hnsdE, hoeE, hcapE, by
                                        rw [hout]
                                        refine answerWriteWf_finalize ?_ (answerWriteWf_empty _)
                                        rw [hstch]
                                        refine localAnswer_chain_answerWriteWf hwfW hNsW hCnW hwfrrW
                                          (congrArg chainOf hla) ?_
                                        rw [hpre]
                                        exact answerWriteWf_push hAW
                                          (fun rr hp => hAWwire cnBytes hcnMem rr hp)⟩
                            ·
                              rename_i state'' heqC
                              obtain ⟨hmme, hsn, htm, hwm⟩ := hSM
                              by_cases hprC : Resolver.probeRoundB state.resources.sname revealed = true
                              case pos =>
                                have hpassT : Server.probePassableB respA = true := by
                                  rw [hprC] at hpgT
                                  simpa using hpgT
                                by_cases hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none
                                · by_cases hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
                                      || !Resolver.classifiableB respA) = true
                                  ·
                                    rw [afterResume_bizarre
                                        { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA hstep hcn hbiz] at heqC
                                    simp only [Server.dropIfBizarre, if_pos hbiz] at heqC
                                    have hst := Server.IoStep.continue.inj heqC
                                    subst hst
                                    obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH ml (by omega) q depth f _
                                      (Server.boundStateCache
                                        (Server.roundTouches
                                          { state with resources := { state.resources with
                                              slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                          respA)
                                        { resources :=
                                            { sname := state.resources.sname, stype := state.resources.stype,
                                              sclass := state.resources.sclass,
                                              slist := (state.resources.slist.markQueried entry.name).removeServer entry.name,
                                              sbelt := state.resources.sbelt, cache := state.resources.cache },
                                          currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                          lastQuery := state.lastQuery, lastResponse := none,
                                          cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                      c _ w' now nseen seen depthFloor resp cout
                                      ⟨by
                                          show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                          rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                        hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                      (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                      (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                      (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                      (by exact wfrrAll_boundLru _ _ hwfrr)
                                      (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                      (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                      (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                      (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                      hmiss hnmiss hfreshInv (by exact hMC)
                                      (by exact GluelessProv_removeServer entry.name (GluelessProv_markQueried entry.name hGlProv))
                                      (by exact hGlBelt)
                                      hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                    have hpart := modelSlistOf_removeServer_perm
                                      (state.resources.slist.markQueried entry.name) entry.name
                                    rw [modelSlistOf_markQueried] at hpart

                                    obtain ⟨l, hp, hsl⟩ := hperm
                                    exact ⟨_, v, cM, hasVerdictAt_timeout_prepend net ns ra ednsBuf rttOf c q v cM _ hrec,
                                      ⟨_ ++ l, (hp.append_left _).trans hpart.symm, hsl.append_left _⟩, hrc, hans, hrest⟩
                                  · rw [Bool.not_eq_true] at hbiz
                                    obtain ⟨pq, hαQp, hSP⟩ := αQuery_buildSubQuery_probe hbuild hprC hsn hqm
                                    have hpqanc : isAncestor pq.qname q.qname = true := by
                                      obtain ⟨⟨cut, hpf⟩, -, -⟩ := hSP
                                      exact (VeriDNS.Proof.QnameMin.probeFor_facts hpf).2.1
                                    have hwmApp := hwm subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr)
                                      d bytes resp0 respS respA pq hO ha hdec hsani haccR hαQp
                                    have hcls : Resolver.classifiableB respA = true := by
                                      have h := (Bool.or_eq_false_iff.mp hbiz).2; simpa using h
                                    have hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false :=
                                      (Bool.or_eq_false_iff.mp hbiz).1
                                    obtain ⟨nsG, sG, hgoto⟩ := afterResume_continue_stepAnalyze_goto
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA state'' hstep hcn hsf hcls heqC
                                    rcases stepAnalyzeResponse_goto_cases
                                        ({ ({ state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }) with
                                          lastResponse := some respA,
                                          currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse })
                                        respA nsG sG rfl hcn hbiz hgoto
                                      with ⟨-, hfacts⟩ | ⟨-, -, h4bL, hrefL, hnodataL⟩ | ⟨-, -, hRefFalse⟩
                                    rotate_left
                                    ·
                                      have hrs : Server.referralShapedB respA = false :=
                                        referralShapedB_false_of_group hrefL
                                      have hts : Server.retryShapedB respA = false := by
                                        unfold Server.retryShapedB
                                        rw [hbiz]
                                        simp
                                      unfold Server.probePassableB at hpassT
                                      rw [hrs, hts] at hpassT
                                      exact absurd hpassT (by decide)
                                    ·
                                      have hrs : Server.referralShapedB respA = false := hRefFalse
                                      have hts : Server.retryShapedB respA = false := by
                                        unfold Server.retryShapedB; rw [hbiz]; simp
                                      unfold Server.probePassableB at hpassT
                                      rw [hrs, hts] at hpassT
                                      exact absurd hpassT (by decide)
                                    have hwmS : ∃ (origin : String) (reply : Datagram) (srcPort : Nat),
                                        Transit (linkReach net ns ra) origin ra reply (some reply)
                                        ∧ accepts (queryDatagram (w.ids w.idCtr).toNat ra
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) srcPort ednsBuf pq) reply = true
                                        ∧ (αResp respA).isReferral = reply.msg.isReferral
                                        ∧ reply.msg.tc = false
                                        ∧ (∀ b ∈ respA.authority.toList, ∃ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
                                        ∧ (reply.msg.isReferral = true →
                                            αSection respA.authority = reply.msg.authority
                                            ∧ αSection respA.additional = reply.msg.additional
                                            ∧ ((respA.header.aa == 1) = reply.msg.aa)
                                            ∧ reply.msg.inBailiwick pq.qname = true
                                            ∧ (∀ b ∈ respA.additional.toList, ∃ rr,
                                                VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none)
                                            ∧ (∀ sname : ByteArray, Server.respInBailiwick sname respA = true →
                                                Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                                  respA.authority sname = (referralCut reply.msg).length)
                                            ∧ (∀ b ∈ respA.authority.toList, ∀ rr,
                                                VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                                (rr.type == (2 : BitVec 16)) = true →
                                                ∃ na, αName rr.rdata = some na
                                                  ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
                                                  ∧ (∀ x ∈ na, x.size ≤ 63))
                                            ∧ ((respA.header.tc == 1) = reply.msg.tc)) := by
                                      rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, _hcncorr, hvalid, hvalidAuth, hcutB, hnstail⟩ | ⟨origin, reply, srcPort, htrans, hacc, hragS, hclsLink, htcR, hauthS, _hvld, hvldA, hrefImpl⟩
                                      · refine ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr),
                                          replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf pq) ref, 0,
                                          Transit.deliver _ _ _ hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra),
                                          accepts_reply _ _ _ _ _ _ _, hisref, serverAnswers_tc_false hans, hvalidAuth, ?_⟩
                                        intro href'
                                        have hbailP : ref.inBailiwick pq.qname = true := by
                                          rcases serverAnswers_referral_inv hans href' with ⟨z, dd, hz, hd, hauth⟩ | ⟨-, hauthc⟩
                                          · exact (referral_bailiwick_desc hnetWF hfind hz hd hauth).1
                                          · exact cachedDelegation_inBailiwick srv now pq.qname pq.qclass hauthc
                                        exact ⟨hnstail.2.2.1, hnstail.2.2.2.1, hnstail.2.2.2.2.1, hbailP,
                                          hnstail.2.2.2.2.2.1, hcutB, hnstail.1, hnstail.2.2.2.2.2.2⟩
                                      · exact ⟨origin, reply, srcPort, htrans, hacc, hclsLink, htcR, hvldA,
                                          fun hri => ⟨hauthS, hrefImpl hri⟩⟩
                                    obtain ⟨origin, reply, srcPort, htrans, hacc, hclsLink, htcR, hvldA, hrefImpl⟩ := hwmS
                                    have hirTrue : (αResp respA).isReferral = true :=
                                      αResp_isReferral_true_of_referralShape hfacts.2.2.1
                                        hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.1
                                        hfacts.2.2.2.2.2.2.2 hvldA
                                    have href : reply.msg.isReferral = true := hclsLink.symm.trans hirTrue
                                    obtain ⟨hauthE, haddE, haaE, hbailP, haddWf, hcutBr, hnsCanonG, htcEg⟩ := hrefImpl href
                                    have hbail : reply.msg.inBailiwick q.qname = true := inBailiwick_of_ancestor hbailP hpqanc
                                    have hcutQ : isAncestor (referralCut reply.msg) pq.qname = true :=
                                      isAncestor_referralCut_of_inBailiwick hbailP
                                    have hdel : Server.delegationShapedB respA = true :=
                                      delegationShapedB_of respA hfacts.2.2.2.2.1 hfacts.1 hfacts.2.1 hcn
                                    have hunfF : Server.unfollowableDelegationB
                                        (state.resources.slist.markQueried entry.name)
                                        state.resources.sname respA = false := by simpa using hunf
                                    have hrib : Server.respInBailiwick state.resources.sname respA = true :=
                                      respInBailiwick_of_not_unfollowable _ _ _ hunfF hdel
                                    have hbridge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                        respA.authority state.resources.sname = (referralCut reply.msg).length :=
                                      hcutBr state.resources.sname hrib
                                    have hsfF : VeriDNS.Spec.SlistFromNameSpec.searchFails
                                        (NS := VeriDNS.Spec.SlistEntry)
                                        (state.resources.slist.markQueried entry.name) = false := by
                                      have hne : state.resources.slist.servers ≠ #[] := by
                                        intro hemp
                                        rw [DnsSList.bestWithAddress, hemp] at hbest
                                        simp at hbest
                                      show (state.resources.slist.markQueried entry.name).servers.isEmpty = false
                                      simp only [DnsSList.markQueried]
                                      by_contra h
                                      rw [Bool.not_eq_false] at h
                                      apply hne
                                      simpa using congrArg Array.size (Array.isEmpty_iff.mp h)
                                    have hgt : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                        respA.authority state.resources.sname
                                        > state.resources.slist.matchCount := by
                                      have hcloser : Server.delegationCloserB
                                          (state.resources.slist.markQueried entry.name)
                                          state.resources.sname respA = true :=
                                        delegationCloserB_of_not_unfollowable _ _ _ hunfF hdel
                                      unfold Server.delegationCloserB at hcloser
                                      rw [hsfF, Bool.false_or] at hcloser
                                      exact of_decide_eq_true hcloser

                                    have hfloorlt : depthFloor < (referralCut reply.msg).length := by
                                      rw [← hbridge]; rw [← hMC]; exact hgt
                                    have hcutlenF : depthFloor ≤ (referralCut reply.msg).length := by omega
                                    obtain ⟨hfrAnc, hfrLen⟩ := isAncestor_drop_ancestor (n := referralCut reply.msg)
                                      (k := depthFloor) hcutlenF
                                    have hdescF : reply.msg.descendsBelow
                                        ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) = true :=
                                      descendsBelow_of_strict hfrAnc (by rw [hfrLen]; omega)
                                    have hfresh : (referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) ∉ seen := by
                                      intro hmem
                                      have hlt := hfreshInv _ hmem
                                      rw [hfrLen] at hlt
                                      exact Nat.lt_irrefl _ hlt

                                    have haaF : (respA.header.aa == 1) = false := by
                                      have h0 : respA.header.aa = 0 := eq_of_beq hfacts.2.2.2.2.2.1
                                      rw [h0]
                                      decide
                                    have htcF : (respA.header.tc == 1) = false := htcEg.trans htcR
                                    have htm' : state.now.toNat = now := htm
                                    have hvalA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (αRR rr).isSome = true := by
                                      intro b hb rr hpr
                                      obtain ⟨rr', hpr', hα'⟩ := hvldA b (bailiwickRaws_toList_sub hb)
                                      rw [hpr'] at hpr
                                      injection hpr with hrr
                                      subst hrr
                                      cases hα : αRR rr' with
                                      | none => exact absurd hα hα'
                                      | some r => rfl
                                    have hvalD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (αRR rr).isSome = true := by
                                      intro b hb rr hpr
                                      obtain ⟨rr', hpr', hα'⟩ := haddWf b (bailiwickRaws_toList_sub hb)
                                      rw [hpr'] at hpr
                                      injection hpr with hrr
                                      subst hrr
                                      cases hα : αRR rr' with
                                      | none => exact absurd hα hα'
                                      | some r => rfl
                                    have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                    have hnoA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                      intro b hb rr hpr
                                      have hb' : b ∈ respS.authority := by
                                        rw [← hrespAeq]
                                        exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                      have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                        (Or.inl (Or.inr hb')) rr hpr
                                      exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                    have hnoD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                      intro b hb rr hpr
                                      have hb' : b ∈ respS.additional := by
                                        rw [← hrespAeq]
                                        exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                      have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                        (Or.inr hb') rr hpr
                                      exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                    have hcutRef : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (referralCut (αResp respA)) :=
                                      referralCutRaw_αName respA.authority hvldA hfacts.2.2.2.2.1
                                    have hrefEq : referralCut (αResp respA) = referralCut reply.msg := by
                                      unfold VeriDNS.Spec.Net.referralCut
                                      rw [show (αResp respA).authority = reply.msg.authority from hauthE]
                                    have habsF : absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg) = referralCut reply.msg :=
                                      absorbBailiwick_of_descendsBelow _ reply.msg hdescF
                                    have hcutαF : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) := by
                                      rw [habsF, ← hrefEq]
                                      exact hcutRef
                                    have hCWwf : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now) state.now :=
                                      CacheWf_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCacheWf hvalA0 hnoA0 hvalD0 hnoD0
                                    have hCWoe : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now) :=
                                      OneExpiryPerKey_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hOE
                                    have hcf0 : WriteRefines now (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))
                                        (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg) := by
                                      have h := refer_write_WriteRefines_ref state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority)
                                        (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg))
                                        state.now (respA.header.aa == 1) haaF hcutαF htcF hirTrue hCacheWf hOE
                                        (normRaws_hval hvalA0) (normRaws_hval hvalD0) (normRaws_hno hnoA0) (normRaws_hno hnoD0) (rrsOf_RRCanonMappable hvalA0) (rrsOf_RRCanonMappable hvalD0) reply.msg c href hauthE haddE haaE hmme
                                      rw [htm'] at h
                                      exact h
                                    have hcf : WriteRefines now (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)) :=
                                      (αCache_boundLru_refines (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now) (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)).writeRefines now

                                    obtain ⟨stC, heqStC, hstCache, hstSn, hstNow, hstCh, hstStep, hstLq, hstSbelt, hdisj⟩ :=
                                      afterResume_referral_continue_cases { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA hstep hcn hbiz hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
                                    have hst2 : state'' = stC := Server.IoStep.continue.inj (heqC.symm.trans heqStC)
                                    have hsn'' : αName state''.resources.sname = some q.qname := by rw [hst2, hstSn]; exact hsn
                                    have hsnameCanon'' : state''.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname := by
                                      rw [hst2, hstSn]; exact hsnameCanon
                                    have htm'' : αTime state''.now = now := by rw [hst2, hstNow]; exact htm
                                    have hCCM'' : CnameChainModels state'' q nseen :=
                                      CnameChainModels_congr (by rw [hst2]; exact hstLq)
                                        (by rw [hst2]; exact hstSn) (by rw [hst2]; exact hstCh) hCCM
                                    have hcache'' : state''.resources.cache = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now := by rw [hst2]; exact hstCache
                                    have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                      unfold Server.sanitizeTtlsCap at hsani; exact (Option.some.inj hsani).symm
                                    have hcapAuth : respA.authority = resp0.authority.map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                    have hcapAdd : respA.additional = (resp0.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                    have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                      rw [hcache'', hst2, hstNow]; exact CacheWf_boundLru (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)) state.now hCWwf
                                    have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                      rw [hcache'']
                                      refine CacheNsCanon_boundLru _ _ _ (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon ?_ ?_)
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                    have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                      rw [hcache'']
                                      refine CacheCnameCanon_boundLru _ _ _ (CacheCnameCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCnCanon ?_ ?_)
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                    have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                      rw [hcache'']; exact CacheNsDistinct_boundLru _ _ _ (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                    have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                      rw [hcache'']; exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hCWoe
                                    have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                      rw [hcache'']; exact VeriDNS.Proof.Cache.boundLru_bounded (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))
                                    have hmiss'' : (αCache state''.resources.cache).hit now q = [] := by
                                      rw [hcache'']
                                      refine hcf.hit_nil (Nat.le_refl now) (hcf0.hit_nil (Nat.le_refl now) ?_)
                                      exact absorb_hit_nil c now _ q reply.msg hmiss (VeriDNS.Spec.Net.Response.isReferral_answer_nil href) (VeriDNS.Spec.Net.Response.isReferral_aa_false href)
                                    have hnmiss'' : (αCache state''.resources.cache).negHit now q = false := by
                                      rw [hcache'']
                                      calc (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)).negHit now q
                                          = (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))).negHit now q := hcf.2.2.1 now q
                                        _ = (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg).negHit now q := hcf0.2.2.1 now q
                                        _ = c.negHit now q := by rw [VeriDNS.Spec.Net.absorb_negHit_eq]
                                        _ = false := hnmiss
                                    have hlq'' : state''.lastQuery = state.lastQuery := by rw [hst2]; exact hstLq
                                    have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                      rw [hcache'']
                                      exact wfrrAll_boundLru _ _ (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)
                                    have hNegWf'' : ∀ qu : VeriDNS.Spec.Question,
                                        (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                        CacheNegWf state''.resources.cache qu.qclass := by
                                      intro qu hqu'
                                      rw [hcache'']
                                      exact CacheNegWf_boundLru _ _ (CacheNegWf_cacheUnlessTruncated _ _ _ _ _
                                        (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu (by rw [← hlq'']; exact hqu'))))
                                    have hqm'' : ∀ qu : VeriDNS.Spec.Question,
                                        (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                        αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by rw [hlq'']; exact hqm
                                    have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hst2, hstNow]; exact hclock
                                    have hstep'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := by rw [hst2]; exact hstStep
                                    have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                      rw [hst2, hstSbelt]; exact hGlBelt
                                    have hnsne : Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority) ≠ #[] :=
                                      extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn respA.authority hfacts.2.2.2.2.1
                                    rcases hdisj with hkept | ⟨nsNames, mc, hwalk, hclose_eq, hrebuild⟩ | ⟨hbelt, hbeltcond⟩
                                    ·
                                      have hslist'' : state''.resources.slist
                                          = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional))
                                            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) := by rw [hst2]; exact hkept
                                      have hGlProv'' : GluelessProv state''.resources.slist := by
                                        rw [hslist'']
                                        exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                          (extractNsNames_ownerRaws_canonical respA.authority (by
                                            intro b hb
                                            rw [hcapAuth, Array.toList_map, List.mem_map] at hb
                                            obtain ⟨b0, hb0, rfl⟩ := hb
                                            exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                              (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))))
                                      have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                          state''.resources.slist = (referralCut reply.msg).length := by
                                        rw [hslist'', matchCount_setUpAddresses]; exact hbridge
                                      have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < (referralCut reply.msg).length := by
                                        intro b hb
                                        rcases List.mem_cons.mp hb with rfl | hb
                                        · rw [hfrLen]; omega
                                        · have := hfreshInv b hb; omega
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                        (αCache state''.resources.cache) _ w' now nseen
                                        ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (referralCut reply.msg).length resp cout
                                        (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                        hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                      have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                      rw [hlq'', hnowSt] at hrest
                                      have hgae : glueAddresses (αResp respA) = glueAddresses reply.msg :=
                                            glueAddresses_congr hauthE haddE
                                      have hvalidAuth' : ∀ b ∈ respA.authority.toList, ∀ rr,
                                          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hne⟩ := hvldA b hb
                                        rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                      have hvalidAdd' : ∀ b ∈ respA.additional.toList, ∀ rr,
                                          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hne⟩ := haddWf b hb
                                        rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                      have hconn := glueAddresses_subperm_transient respA (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) hcutRef hvalidAuth'
                                        hvalidAdd' hnsCanonG hfacts.2.2.2.2.1
                                      have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                          ∨ (glueAddresses reply.msg).Subperm s := by
                                        refine Or.inr ?_
                                        rw [← hgae]
                                        refine hconn.trans ?_
                                        rw [hslist''] at hperm
                                        exact hperm
                                      have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                        rw [← hcache'']; exact hrec
                                      exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                        trustedReferralProbe_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                          ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q pq
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                          (w.ids w.idCtr).toNat srcPort c reply
                                          hmiss hnmiss (Or.inr hSP) htrans hacc
                                          href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                          (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))) hcf0 hgl
                                          (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                        hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                    ·
                                      have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          respA.authority state.resources.sname ≤ mc := by
                                        have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                          rw [searchFails_setUpAddresses]; simpa using hnsne
                                        have hmc0 := hclose_eq
                                        rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hmc0
                                        simpa using hmc0
                                      have hslist'' : state''.resources.slist
                                          = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)) state.now nsNames) mc := by
                                        rw [hst2]; exact hrebuild
                                      have hGlProv'' : GluelessProv state''.resources.slist := by
                                        rw [hslist'']
                                        exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                          (walkNs_names_canonical _ state.now
                                            (CacheNsCanon_absorb state.resources.cache respA
                                              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                  (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                  (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                            128 state.resources.sname nsNames mc hwalk)
                                      have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                          state''.resources.slist = mc := by rw [hslist'', matchCount_setUpAddresses]
                                      have hsubmc : (referralCut reply.msg).length ≤ mc := by rw [← hbridge]; exact hge
                                      have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < mc := by
                                        intro b hb
                                        rcases List.mem_cons.mp hb with rfl | hb
                                        · rw [hfrLen]; omega
                                        · have := hfreshInv b hb; omega
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                        (αCache state''.resources.cache) _ w' now nseen
                                        ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) mc resp cout
                                        (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                        hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                      have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                      rw [hlq'', hnowSt] at hrest
                                      have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                          ∨ (glueAddresses reply.msg).Subperm s := by
                                        refine Or.inl ?_
                                        obtain ⟨sname_lab, hsna, hlabq⟩ :
                                            ∃ lab, VeriDNS.Impl.DomainName.wireFormatToLabels state.resources.sname = .ok lab
                                              ∧ lab.toList = q.qname := by
                                          unfold αName at hsn
                                          split at hsn
                                          · next lab h => exact ⟨lab, h, Option.some.inj hsn⟩
                                          · exact absurd hsn (by simp)
                                        have hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab := by
                                          intro i hi
                                          have hmem : sname_lab[i] ∈ q.qname := by
                                            rw [← hlabq]; exact Array.mem_def.mp (Array.getElem_mem hi)
                                          exact hqvalid _ hmem
                                        have hkey := refer_continue_keystone_wf
                                          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))
                                          state.resources.sname q.qname sname_lab nsNames mc state.now
                                          hwalk hsna hsnav hsnameCanon hlabq hqlen hCWwf
                                          (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                            (by
                                              intro raw hraw
                                              have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                              rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                              obtain ⟨b0, hb0, rfl⟩ := hmem
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                            (by
                                              intro raw hraw
                                              have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                              rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                              obtain ⟨b0, hb0, rfl⟩ := hmem
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                          (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                        rw [← htm]
                                        refine hkey.trans ?_
                                        rw [← hslist'']
                                        exact hperm
                                      have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                        rw [← hcache'']; exact hrec
                                      exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                        trustedReferralProbe_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                          ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q pq
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                          (w.ids w.idCtr).toNat srcPort c reply
                                          hmiss hnmiss (Or.inr hSP) htrans hacc
                                          href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                          (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))) hcf0 hgl
                                          (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                        hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                    ·
                                      exfalso
                                      have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                        rw [searchFails_setUpAddresses]; simpa using hnsne
                                      rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hbeltcond
                                      have : 0 < (referralCut reply.msg).length := by omega
                                      rw [hbridge] at hbeltcond
                                      simp only [decide_eq_false_iff_not, Nat.not_lt] at hbeltcond
                                      omega
                                · obtain ⟨target, hcnT⟩ := Option.ne_none_iff_exists'.mp hcn
                                  rw [probePassable_false_of_chase hcnT] at hpassT
                                  exact absurd hpassT (by decide)
                              have hfull : Resolver.probeRoundB state.resources.sname revealed = false := by
                                simp only [Bool.not_eq_true] at hprC; exact hprC
                              have hαQ : αQuery subQuery0 = some q :=
                                αQuery_buildSubQuery hbuild hfull hsn hqm hrd
                              have hwmApp := hwm subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.ipv4ToAddr ipAddr)
                                d bytes resp0 respS respA q hO ha hdec hsani haccR hαQ
                              by_cases hcn : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) respA = none
                              ·

                                by_cases hbiz : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure
                                    || !Resolver.classifiableB respA) = true
                                ·
                                  rw [afterResume_bizarre
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA hstep hcn hbiz] at heqC
                                  simp only [Server.dropIfBizarre, if_pos hbiz] at heqC
                                  have hst := Server.IoStep.continue.inj heqC
                                  subst hst
                                  obtain ⟨s, v, cM, hrec, hperm, hrc, hans, hrest⟩ := IH ml (by omega) q depth f _
                                    (Server.boundStateCache
                                      (Server.roundTouches
                                        { state with resources := { state.resources with
                                            slist := (state.resources.slist.markQueried entry.name).removeServer entry.name } }
                                        respA)
                                      { resources :=
                                          { sname := state.resources.sname, stype := state.resources.stype,
                                            sclass := state.resources.sclass,
                                            slist := (state.resources.slist.markQueried entry.name).removeServer entry.name,
                                            sbelt := state.resources.sbelt, cache := state.resources.cache },
                                        currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                        lastQuery := state.lastQuery, lastResponse := none,
                                        cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                    c _ w' now nseen seen depthFloor resp cout
                                    ⟨by
                                        show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                        rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                      hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                    (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                    (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                    (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                    (by exact wfrrAll_boundLru _ _ hwfrr)
                                    (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                    (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                    (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                    (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                    hmiss hnmiss hfreshInv (by exact hMC)
                                    (by exact GluelessProv_removeServer entry.name (GluelessProv_markQueried entry.name hGlProv))
                                    (by exact hGlBelt)
                                    hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                  have hpart := modelSlistOf_removeServer_perm
                                    (state.resources.slist.markQueried entry.name) entry.name
                                  rw [modelSlistOf_markQueried] at hpart

                                  obtain ⟨l, hp, hsl⟩ := hperm
                                  exact ⟨_, v, cM, hasVerdictAt_timeout_prepend net ns ra ednsBuf rttOf c q v cM _ hrec,
                                    ⟨_ ++ l, (hp.append_left _).trans hpart.symm, hsl.append_left _⟩, hrc, hans, hrest⟩
                                ·
                                  rw [Bool.not_eq_true] at hbiz
                                  rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, _hcncorr, hvalid, hvalidAuth, hcut, hnstail⟩ | hspoof
                                  ·
                                    have hcls : Resolver.classifiableB respA = true := by
                                      have h := (Bool.or_eq_false_iff.mp hbiz).2; simpa using h
                                    have hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false :=
                                      (Bool.or_eq_false_iff.mp hbiz).1
                                    obtain ⟨nsG, sG, hgoto⟩ := afterResume_continue_stepAnalyze_goto
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA state'' hstep hcn hsf hcls heqC
                                    rcases stepAnalyzeResponse_goto_cases
                                        ({ ({ state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }) with
                                          lastResponse := some respA,
                                          currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse })
                                        respA nsG sG rfl hcn hbiz hgoto
                                      with ⟨-, hfacts⟩ | ⟨-, -, h4bL, hrefL, hnodataL⟩ | ⟨hnsG, hsG, -⟩
                                    rotate_left
                                    · -- B.3: lame referral ⇒ retry
                                      rw [afterResume_lame
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA hstep hcn hbiz h4bL hrefL hnodataL] at heqC
                                      have hst := Server.IoStep.continue.inj heqC
                                      subst hst
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansV, hrest⟩ := IH ml (by omega) q depth f _
                                        (Server.boundStateCache
                                          (Server.roundTouches
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            respA)
                                          { resources :=
                                              { sname := state.resources.sname, stype := state.resources.stype,
                                                sclass := state.resources.sclass,
                                                slist := state.resources.slist.markQueried entry.name,
                                                sbelt := state.resources.sbelt, cache := state.resources.cache },
                                            currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                            lastQuery := state.lastQuery, lastResponse := none,
                                            cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                        c _ w' now nseen seen depthFloor resp cout
                                        ⟨by
                                            show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                            rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                          hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                        (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                        (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                        (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                        (by exact wfrrAll_boundLru _ _ hwfrr)
                                        (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                        (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                        (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                        (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                        hmiss hnmiss hfreshInv (by exact hMC)
                                        (by exact GluelessProv_markQueried entry.name hGlProv)
                                        (by exact hGlBelt)
                                        hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                      obtain ⟨l, hp, hsl⟩ := hperm
                                      have hp' : l.Perm (modelSlistOf
                                          (state.resources.slist.markQueried entry.name)) := hp
                                      rw [modelSlistOf_markQueried] at hp'
                                      exact ⟨_, v, cM, hrec, ⟨l, hp', hsl⟩, hrc, hansV, hrest⟩
                                    · -- G: ambiguous empty NOERROR ⇒ retry (mirrors B.3)
                                      rw [hnsG, hsG] at hgoto
                                      rw [afterResume_of_stepGoto
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA hstep hbiz hgoto] at heqC
                                      have hst := Server.IoStep.continue.inj heqC
                                      subst hst
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansV, hrest⟩ := IH ml (by omega) q depth f _
                                        (Server.boundStateCache
                                          (Server.roundTouches
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            respA)
                                          { resources :=
                                              { sname := state.resources.sname, stype := state.resources.stype,
                                                sclass := state.resources.sclass,
                                                slist := state.resources.slist.markQueried entry.name,
                                                sbelt := state.resources.sbelt, cache := state.resources.cache },
                                            currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                            lastQuery := state.lastQuery, lastResponse := none,
                                            cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                        c _ w' now nseen seen depthFloor resp cout
                                        ⟨by
                                            show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                            rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                          hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                        (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                        (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                        (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                        (by exact wfrrAll_boundLru _ _ hwfrr)
                                        (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                        (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                        (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                        (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                        hmiss hnmiss hfreshInv (by exact hMC)
                                        (by exact GluelessProv_markQueried entry.name hGlProv)
                                        (by exact hGlBelt)
                                        hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                      obtain ⟨l, hp, hsl⟩ := hperm
                                      have hp' : l.Perm (modelSlistOf
                                          (state.resources.slist.markQueried entry.name)) := hp
                                      rw [modelSlistOf_markQueried] at hp'
                                      exact ⟨_, v, cM, hrec, ⟨l, hp', hsl⟩, hrc, hansV, hrest⟩
                                    have hirTrue : (αResp respA).isReferral = true :=
                                      αResp_isReferral_true_of_referralShape hfacts.2.2.1
                                        hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.1
                                        hfacts.2.2.2.2.2.2.2 hvalidAuth
                                    have href : ref.isReferral = true := hisref.symm.trans hirTrue

                                    rcases serverAnswers_referral_inv hans href with
                                      ⟨z, d, hz, hd, hauth⟩ | ⟨hznone, hauthc⟩
                                    ·
                                      obtain ⟨hbail, hdesc⟩ :=
                                        referral_bailiwick_desc hnetWF hfind hz hd hauth

                                      have hdel : Server.delegationShapedB respA = true :=
                                        delegationShapedB_of respA hfacts.2.2.2.2.1 hfacts.1 hfacts.2.1 hcn
                                      have hunfF : Server.unfollowableDelegationB
                                          (state.resources.slist.markQueried entry.name)
                                          state.resources.sname respA = false := by simpa using hunf
                                      have hrib : Server.respInBailiwick state.resources.sname respA = true :=
                                        respInBailiwick_of_not_unfollowable _ _ _ hunfF hdel
                                      have hzwf : z.WF :=
                                        ((hnetWF.1 srv (serverAt_mem hfind)).2 z (bestZone_spec hz).1).1
                                      have hdmem : d ∈ z.delegations := by
                                        unfold bestDeleg at hd
                                        rcases foldl_pickDeleg_mem _ none d hd with hm | hcon
                                        · exact (List.mem_filter.mp hm).1
                                        · exact absurd hcon (by simp)
                                      have hcutSub : (referralCut ref).length = d.subapex.length := by
                                        unfold referralCut
                                        rw [hauth]
                                        cases hfd : d.nsSet.find? (fun r => r.rdata.rtype == RRType.ns) with
                                        | none =>
                                          exfalso
                                          have hne := List.all_eq_true.mp hzwf.2.2.2.2.2.2.1 d hdmem
                                          have hall := List.all_eq_true.mp hzwf.2.2.2.1 d hdmem
                                          obtain ⟨r₀, hr₀⟩ : ∃ r, r ∈ d.nsSet := by
                                            cases hns0 : d.nsSet with
                                            | nil => rw [hns0] at hne; simp at hne
                                            | cons a t => exact ⟨a, by simp⟩
                                          have hp := List.all_eq_true.mp hall r₀ hr₀
                                          have hf := List.find?_eq_none.mp hfd r₀ hr₀
                                          simp only [Bool.and_eq_true] at hp
                                          simp [hp.2] at hf
                                        | some r₀ =>
                                          simp only [Option.elim]
                                          exact nameEq_length
                                            (Zone.WF_nsSet_owner hzwf hdmem (List.mem_of_find?_eq_some hfd))
                                      have hbridge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          respA.authority state.resources.sname = d.subapex.length := by
                                        rw [hcut state.resources.sname hrib]
                                        exact hcutSub
                                      have hsfF : VeriDNS.Spec.SlistFromNameSpec.searchFails
                                          (NS := VeriDNS.Spec.SlistEntry)
                                          (state.resources.slist.markQueried entry.name) = false := by
                                        have hne : state.resources.slist.servers ≠ #[] := by
                                          intro hemp
                                          rw [DnsSList.bestWithAddress, hemp] at hbest
                                          simp at hbest
                                        show (state.resources.slist.markQueried entry.name).servers.isEmpty = false
                                        simp only [DnsSList.markQueried]
                                        by_contra h
                                        rw [Bool.not_eq_false] at h
                                        apply hne
                                        simpa using congrArg Array.size (Array.isEmpty_iff.mp h)
                                      have hgt : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          respA.authority state.resources.sname
                                          > state.resources.slist.matchCount := by
                                        have hcloser : Server.delegationCloserB
                                            (state.resources.slist.markQueried entry.name)
                                            state.resources.sname respA = true :=
                                          delegationCloserB_of_not_unfollowable _ _ _ hunfF hdel
                                        unfold Server.delegationCloserB at hcloser
                                        rw [hsfF, Bool.false_or] at hcloser
                                        exact of_decide_eq_true hcloser

                                      have hfloorlt : depthFloor < d.subapex.length := by
                                        rw [← hbridge]; rw [← hMC]; exact hgt
                                      have hcutlenF : depthFloor ≤ (referralCut ref).length := by
                                        rw [hcutSub]; omega
                                      obtain ⟨hfrAnc, hfrLen⟩ := isAncestor_drop_ancestor (n := referralCut ref)
                                        (k := depthFloor) hcutlenF
                                      have hdescF : ref.descendsBelow
                                          ((referralCut ref).drop ((referralCut ref).length - depthFloor)) = true :=
                                        descendsBelow_of_strict hfrAnc (by rw [hfrLen, hcutSub]; omega)
                                      have hfresh : (referralCut ref).drop ((referralCut ref).length - depthFloor) ∉ seen := by
                                        intro hmem
                                        have hlt := hfreshInv _ hmem
                                        rw [hfrLen] at hlt
                                        exact Nat.lt_irrefl _ hlt

                                      have haaF : (respA.header.aa == 1) = false := by
                                        have h0 : respA.header.aa = 0 := eq_of_beq hfacts.2.2.2.2.2.1
                                        rw [h0]
                                        decide
                                      have htcF : (respA.header.tc == 1) = false := by
                                        rw [hnstail.2.2.2.2.2.2]
                                        exact serverAnswers_tc_false hans
                                      have htm' : state.now.toNat = now := htm
                                      have hvalA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hvalidAuth b (bailiwickRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hvalD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hnstail.2.2.2.2.2.1 b (bailiwickRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                      have hnoA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ respS.authority := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                          (Or.inl (Or.inr hb')) rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hnoD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ respS.additional := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                          (Or.inr hb') rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hcutRef : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (referralCut (αResp respA)) :=
                                        referralCutRaw_αName respA.authority hvalidAuth hfacts.2.2.2.2.1
                                      have hrefEq : referralCut (αResp respA) = referralCut ref := by
                                        unfold VeriDNS.Spec.Net.referralCut
                                        rw [show (αResp respA).authority = ref.authority from hnstail.2.2.1]
                                      have habs : absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref) = referralCut ref :=
                                        absorbBailiwick_of_descendsBelow _ ref hdesc
                                      have hcutα : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref)) := by
                                        rw [habs, ← hrefEq]
                                        exact hcutRef
                                      have hCWwf : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now) state.now :=
                                        CacheWf_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCacheWf hvalA0 hnoA0 hvalD0 hnoD0
                                      have hCWoe : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now) :=
                                        OneExpiryPerKey_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hOE
                                      have hcf0 : WriteRefines now (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))
                                          (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref)) ref) := by
                                        have h := refer_write_WriteRefines_ref state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority)
                                          (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref))
                                          state.now (respA.header.aa == 1) haaF hcutα htcF hirTrue hCacheWf hOE
                                          (normRaws_hval hvalA0) (normRaws_hval hvalD0) (normRaws_hno hnoA0) (normRaws_hno hnoD0) (rrsOf_RRCanonMappable hvalA0) (rrsOf_RRCanonMappable hvalD0) ref c href hnstail.2.2.1 hnstail.2.2.2.1 hnstail.2.2.2.2.1 hmme
                                        rw [htm'] at h
                                        exact h
                                      have hcf : WriteRefines now (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)) :=
                                        (αCache_boundLru_refines (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now) (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)).writeRefines now

                                      obtain ⟨stC, heqStC, hstCache, hstSn, hstNow, hstCh, hstStep, hstLq, hstSbelt, hdisj⟩ :=
                                        afterResume_referral_continue_cases { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA hstep hcn hbiz hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
                                      have hst2 : state'' = stC := Server.IoStep.continue.inj (heqC.symm.trans heqStC)

                                      have hsn'' : αName state''.resources.sname = some q.qname := by rw [hst2, hstSn]; exact hsn
                                      have hsnameCanon'' : state''.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname := by
                                        rw [hst2, hstSn]; exact hsnameCanon
                                      have htm'' : αTime state''.now = now := by rw [hst2, hstNow]; exact htm
                                      have hCCM'' : CnameChainModels state'' q nseen :=
                                        CnameChainModels_congr (by rw [hst2]; exact hstLq)
                                          (by rw [hst2]; exact hstSn) (by rw [hst2]; exact hstCh) hCCM
                                      have hcache'' : state''.resources.cache = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now := by rw [hst2]; exact hstCache
                                      have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                        unfold Server.sanitizeTtlsCap at hsani; exact (Option.some.inj hsani).symm
                                      have hcapAuth : respA.authority = resp0.authority.map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                      have hcapAdd : respA.additional = (resp0.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                      have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                        rw [hcache'', hst2, hstNow]; exact CacheWf_boundLru (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)) state.now hCWwf
                                      have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                        rw [hcache'']
                                        refine CacheNsCanon_boundLru _ _ _ (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon ?_ ?_)
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                      have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                        rw [hcache'']
                                        refine CacheCnameCanon_boundLru _ _ _ (CacheCnameCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCnCanon ?_ ?_)
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                      have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                        rw [hcache'']; exact CacheNsDistinct_boundLru _ _ _ (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                      have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                        rw [hcache'']; exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hCWoe
                                      have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                        rw [hcache'']; exact VeriDNS.Proof.Cache.boundLru_bounded (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))
                                      have hmiss'' : (αCache state''.resources.cache).hit now q = [] := by
                                        rw [hcache'']
                                        refine hcf.hit_nil (Nat.le_refl now) (hcf0.hit_nil (Nat.le_refl now) ?_)
                                        exact absorb_hit_nil c now _ q ref hmiss (VeriDNS.Spec.Net.Response.isReferral_answer_nil href) (VeriDNS.Spec.Net.Response.isReferral_aa_false href)
                                      have hnmiss'' : (αCache state''.resources.cache).negHit now q = false := by
                                        rw [hcache'']
                                        calc (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)).negHit now q
                                            = (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))).negHit now q := hcf.2.2.1 now q
                                          _ = (c.absorb now (absorbBailiwick (serverBailiwick srv q.qname q.qclass) (referralCut ref)) ref).negHit now q := hcf0.2.2.1 now q
                                          _ = c.negHit now q := by rw [VeriDNS.Spec.Net.absorb_negHit_eq]
                                          _ = false := hnmiss
                                      have hlq'' : state''.lastQuery = state.lastQuery := by rw [hst2]; exact hstLq
                                      have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                        rw [hcache'']
                                        exact wfrrAll_boundLru _ _ (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)
                                      have hNegWf'' : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          CacheNegWf state''.resources.cache qu.qclass := by
                                        intro qu hqu'
                                        rw [hcache'']
                                        exact CacheNegWf_boundLru _ _ (CacheNegWf_cacheUnlessTruncated _ _ _ _ _
                                          (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu (by rw [← hlq'']; exact hqu'))))
                                      have hqm'' : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by rw [hlq'']; exact hqm
                                      have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hst2, hstNow]; exact hclock
                                      have hstep'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := by rw [hst2]; exact hstStep
                                      have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                        rw [hst2, hstSbelt]; exact hGlBelt

                                      have hsubpos : 0 < d.subapex.length := by have h2 := (descendsBelow_strict hdesc).2; omega
                                      have hbwlt : (serverBailiwick srv q.qname q.qclass).length < d.subapex.length := by
                                        have h2 := (descendsBelow_strict hdesc).2; omega
                                      have hnsne : Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority) ≠ #[] :=
                                        extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn respA.authority hfacts.2.2.2.2.1
                                      rcases hdisj with hkept | ⟨nsNames, mc, hwalk, hclose_eq, hrebuild⟩ | ⟨hbelt, hbeltcond⟩
                                      ·
                                        have hslist'' : state''.resources.slist
                                            = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional))
                                              (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) := by rw [hst2]; exact hkept
                                        have hGlProv'' : GluelessProv state''.resources.slist := by
                                          rw [hslist'']
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (extractNsNames_ownerRaws_canonical respA.authority (by
                                              intro b hb
                                              rw [hcapAuth, Array.toList_map, List.mem_map] at hb
                                              obtain ⟨b0, hb0, rfl⟩ := hb
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))))
                                        have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            state''.resources.slist = d.subapex.length := by
                                          rw [hslist'', matchCount_setUpAddresses]; exact hbridge
                                        have hfreshInv'' : ∀ b ∈ ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen), b.length < d.subapex.length := by
                                          intro b hb
                                          rcases List.mem_cons.mp hb with rfl | hb
                                          · rw [hfrLen]; omega
                                          · have := hfreshInv b hb; omega
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                          (αCache state''.resources.cache) _ w' now nseen
                                          ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) d.subapex.length resp cout
                                          (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                          hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                        have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                        rw [hlq'', hnowSt] at hrest
                                        have hauthE : (αResp respA).authority = ref.authority := hnstail.2.2.1
                                        have haddE : (αResp respA).additional = ref.additional := hnstail.2.2.2.1
                                        have hgae : glueAddresses (αResp respA) = glueAddresses ref :=
                                          glueAddresses_congr hauthE haddE
                                        have hvalidAuth' : ∀ b ∈ respA.authority.toList, ∀ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hne⟩ := hvalidAuth b hb
                                          rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                        have hvalidAdd' : ∀ b ∈ respA.additional.toList, ∀ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hne⟩ := hnstail.2.2.2.2.2.1 b hb
                                          rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                        have hconn := glueAddresses_subperm_transient respA (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) hcutRef hvalidAuth'
                                          hvalidAdd' hnstail.1 hfacts.2.2.2.2.1
                                        have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                            ∨ (glueAddresses ref).Subperm s := by
                                          refine Or.inr ?_
                                          rw [← hgae]
                                          refine hconn.trans ?_
                                          rw [hslist''] at hperm
                                          exact hperm
                                        have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                          rw [← hcache'']; exact hrec
                                        exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                          VeriDNS.Proof.WorldNetwork.serverReferForget_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q srv tr ref
                                            (w.ids w.idCtr).toNat 0 c hmiss hnmiss hfind hans hreachA
                                            (VeriDNS.Proof.WorldNetwork.reach_self net ns ra) href hbail hdesc
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor)) hdescF hfresh
                                            (Nat.le_refl now) v s (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))) hcf0 hgl
                                            (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                          hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                      ·
                                        have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                            respA.authority state.resources.sname ≤ mc := by
                                          have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                                (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                            rw [searchFails_setUpAddresses]; simpa using hnsne
                                          have hmc0 := hclose_eq
                                          rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hmc0
                                          simpa using hmc0
                                        have hslist'' : state''.resources.slist
                                            = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)) state.now nsNames) mc := by
                                          rw [hst2]; exact hrebuild
                                        have hGlProv'' : GluelessProv state''.resources.slist := by
                                          rw [hslist'']
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (walkNs_names_canonical _ state.now
                                              (CacheNsCanon_absorb state.resources.cache respA
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                    (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                    (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                              128 state.resources.sname nsNames mc hwalk)
                                        have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            state''.resources.slist = mc := by rw [hslist'', matchCount_setUpAddresses]
                                        have hsubmc : d.subapex.length ≤ mc := by rw [← hbridge]; exact hge

                                        have hfreshInv'' : ∀ b ∈ ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen), b.length < mc := by
                                          intro b hb
                                          rcases List.mem_cons.mp hb with rfl | hb
                                          · rw [hfrLen]; omega
                                          · have := hfreshInv b hb; omega
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                          (αCache state''.resources.cache) _ w' now nseen
                                          ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) mc resp cout
                                          (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                          hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                        have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                        rw [hlq'', hnowSt] at hrest

                                        have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                            ∨ (glueAddresses ref).Subperm s := by
                                          refine Or.inl ?_

                                          obtain ⟨sname_lab, hsna, hlabq⟩ :
                                              ∃ lab, VeriDNS.Impl.DomainName.wireFormatToLabels state.resources.sname = .ok lab
                                                ∧ lab.toList = q.qname := by
                                            unfold αName at hsn
                                            split at hsn
                                            · next lab h => exact ⟨lab, h, Option.some.inj hsn⟩
                                            · exact absurd hsn (by simp)
                                          have hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab := by
                                            intro i hi
                                            have hmem : sname_lab[i] ∈ q.qname := by
                                              rw [← hlabq]; exact Array.mem_def.mp (Array.getElem_mem hi)
                                            exact hqvalid _ hmem
                                          have hkey := refer_continue_keystone_wf
                                            ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache respA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                                (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                              respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                              Resolver.credAdditional state.now))
                                            state.resources.sname q.qname sname_lab nsNames mc state.now
                                            hwalk hsna hsnav hsnameCanon hlabq hqlen hCWwf
                                            (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                            (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                          rw [← htm]
                                          refine hkey.trans ?_
                                          rw [← hslist'']
                                          exact hperm
                                        have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                          rw [← hcache'']; exact hrec
                                        exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                          VeriDNS.Proof.WorldNetwork.serverReferForget_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q srv tr ref
                                            (w.ids w.idCtr).toNat 0 c hmiss hnmiss hfind hans hreachA
                                            (VeriDNS.Proof.WorldNetwork.reach_self net ns ra) href hbail hdesc
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor)) hdescF hfresh
                                            (Nat.le_refl now) v s (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))) hcf0 hgl
                                            (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                          hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                      ·
                                        exfalso
                                        have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                          rw [searchFails_setUpAddresses]; simpa using hnsne
                                        rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hbeltcond
                                        have : 0 < d.subapex.length := hsubpos
                                        rw [hbridge] at hbeltcond
                                        simp only [decide_eq_false_iff_not, Nat.not_lt] at hbeltcond
                                        omega
                                    ·

                                      have hdel : Server.delegationShapedB respA = true :=
                                        delegationShapedB_of respA hfacts.2.2.2.2.1 hfacts.1 hfacts.2.1 hcn
                                      have hunfF : Server.unfollowableDelegationB
                                          (state.resources.slist.markQueried entry.name)
                                          state.resources.sname respA = false := by simpa using hunf
                                      have hrib : Server.respInBailiwick state.resources.sname respA = true :=
                                        respInBailiwick_of_not_unfollowable _ _ _ hunfF hdel
                                      have hbail : ref.inBailiwick q.qname = true :=
                                        cachedDelegation_inBailiwick srv now q.qname q.qclass hauthc
                                      have hcutQ : isAncestor (referralCut ref) q.qname = true :=
                                        isAncestor_referralCut_of_inBailiwick hbail
                                      have hbridge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          respA.authority state.resources.sname = (referralCut ref).length :=
                                        hcut state.resources.sname hrib
                                      have hsfF : VeriDNS.Spec.SlistFromNameSpec.searchFails
                                          (NS := VeriDNS.Spec.SlistEntry)
                                          (state.resources.slist.markQueried entry.name) = false := by
                                        have hne : state.resources.slist.servers ≠ #[] := by
                                          intro hemp
                                          rw [DnsSList.bestWithAddress, hemp] at hbest
                                          simp at hbest
                                        show (state.resources.slist.markQueried entry.name).servers.isEmpty = false
                                        simp only [DnsSList.markQueried]
                                        by_contra h
                                        rw [Bool.not_eq_false] at h
                                        apply hne
                                        simpa using congrArg Array.size (Array.isEmpty_iff.mp h)
                                      have hgt : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          respA.authority state.resources.sname
                                          > state.resources.slist.matchCount := by
                                        have hcloser : Server.delegationCloserB
                                            (state.resources.slist.markQueried entry.name)
                                            state.resources.sname respA = true :=
                                          delegationCloserB_of_not_unfollowable _ _ _ hunfF hdel
                                        unfold Server.delegationCloserB at hcloser
                                        rw [hsfF, Bool.false_or] at hcloser
                                        exact of_decide_eq_true hcloser

                                      have hfloorlt : depthFloor < (referralCut ref).length := by
                                        rw [← hbridge]; rw [← hMC]; exact hgt
                                      have hcutlenF : depthFloor ≤ (referralCut ref).length := by omega
                                      obtain ⟨hfrAnc, hfrLen⟩ := isAncestor_drop_ancestor (n := referralCut ref)
                                        (k := depthFloor) hcutlenF
                                      have hdescF : ref.descendsBelow
                                          ((referralCut ref).drop ((referralCut ref).length - depthFloor)) = true :=
                                        descendsBelow_of_strict hfrAnc (by rw [hfrLen]; omega)
                                      have hfresh : (referralCut ref).drop ((referralCut ref).length - depthFloor) ∉ seen := by
                                        intro hmem
                                        have hlt := hfreshInv _ hmem
                                        rw [hfrLen] at hlt
                                        exact Nat.lt_irrefl _ hlt

                                      have haaF : (respA.header.aa == 1) = false := by
                                        have h0 : respA.header.aa = 0 := eq_of_beq hfacts.2.2.2.2.2.1
                                        rw [h0]
                                        decide
                                      have htcF : (respA.header.tc == 1) = false := by
                                        rw [hnstail.2.2.2.2.2.2]
                                        exact serverAnswers_tc_false hans
                                      have htm' : state.now.toNat = now := htm
                                      have hvalA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hvalidAuth b (bailiwickRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hvalD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (αRR rr).isSome = true := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hα'⟩ := hnstail.2.2.2.2.2.1 b (bailiwickRaws_toList_sub hb)
                                        rw [hpr'] at hpr
                                        injection hpr with hrr
                                        subst hrr
                                        cases hα : αRR rr' with
                                        | none => exact absurd hα hα'
                                        | some r => rfl
                                      have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                      have hnoA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ respS.authority := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                          (Or.inl (Or.inr hb')) rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hnoD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                          ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                          (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                        intro b hb rr hpr
                                        have hb' : b ∈ respS.additional := by
                                          rw [← hrespAeq]
                                          exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                        have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                          (Or.inr hb') rr hpr
                                        exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                      have hcutRef : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (referralCut (αResp respA)) :=
                                        referralCutRaw_αName respA.authority hvalidAuth hfacts.2.2.2.2.1
                                      have hrefEq : referralCut (αResp respA) = referralCut ref := by
                                        unfold VeriDNS.Spec.Net.referralCut
                                        rw [show (αResp respA).authority = ref.authority from hnstail.2.2.1]
                                      have habsF : absorbBailiwick ((referralCut ref).drop ((referralCut ref).length - depthFloor)) (referralCut ref) = referralCut ref :=
                                        absorbBailiwick_of_descendsBelow _ ref hdescF
                                      have hcutαF : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (absorbBailiwick ((referralCut ref).drop ((referralCut ref).length - depthFloor)) (referralCut ref)) := by
                                        rw [habsF, ← hrefEq]
                                        exact hcutRef
                                      have hCWwf : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now) state.now :=
                                        CacheWf_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCacheWf hvalA0 hnoA0 hvalD0 hnoD0
                                      have hCWoe : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now) :=
                                        OneExpiryPerKey_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hOE
                                      have hcf0 : WriteRefines now (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))
                                          (c.absorb now (absorbBailiwick ((referralCut ref).drop ((referralCut ref).length - depthFloor)) (referralCut ref)) ref) := by
                                        have h := refer_write_WriteRefines_ref state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority)
                                          (absorbBailiwick ((referralCut ref).drop ((referralCut ref).length - depthFloor)) (referralCut ref))
                                          state.now (respA.header.aa == 1) haaF hcutαF htcF hirTrue hCacheWf hOE
                                          (normRaws_hval hvalA0) (normRaws_hval hvalD0) (normRaws_hno hnoA0) (normRaws_hno hnoD0) (rrsOf_RRCanonMappable hvalA0) (rrsOf_RRCanonMappable hvalD0) ref c href hnstail.2.2.1 hnstail.2.2.2.1 hnstail.2.2.2.2.1 hmme
                                        rw [htm'] at h
                                        exact h
                                      have hcf : WriteRefines now (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)) :=
                                        (αCache_boundLru_refines (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now) (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)).writeRefines now

                                      obtain ⟨stC, heqStC, hstCache, hstSn, hstNow, hstCh, hstStep, hstLq, hstSbelt, hdisj⟩ :=
                                        afterResume_referral_continue_cases { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA hstep hcn hbiz hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
                                      have hst2 : state'' = stC := Server.IoStep.continue.inj (heqC.symm.trans heqStC)

                                      have hsn'' : αName state''.resources.sname = some q.qname := by rw [hst2, hstSn]; exact hsn
                                      have hsnameCanon'' : state''.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname := by
                                        rw [hst2, hstSn]; exact hsnameCanon
                                      have htm'' : αTime state''.now = now := by rw [hst2, hstNow]; exact htm
                                      have hCCM'' : CnameChainModels state'' q nseen :=
                                        CnameChainModels_congr (by rw [hst2]; exact hstLq)
                                          (by rw [hst2]; exact hstSn) (by rw [hst2]; exact hstCh) hCCM
                                      have hcache'' : state''.resources.cache = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now := by rw [hst2]; exact hstCache
                                      have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                        unfold Server.sanitizeTtlsCap at hsani; exact (Option.some.inj hsani).symm
                                      have hcapAuth : respA.authority = resp0.authority.map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                      have hcapAdd : respA.additional = (resp0.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                      have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                        rw [hcache'', hst2, hstNow]; exact CacheWf_boundLru (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)) state.now hCWwf
                                      have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                        rw [hcache'']
                                        refine CacheNsCanon_boundLru _ _ _ (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon ?_ ?_)
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                      have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                        rw [hcache'']
                                        refine CacheCnameCanon_boundLru _ _ _ (CacheCnameCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCnCanon ?_ ?_)
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                        · intro raw hraw
                                          have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                          rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                          obtain ⟨b0, hb0, rfl⟩ := hmem
                                          exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                      have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                        rw [hcache'']; exact CacheNsDistinct_boundLru _ _ _ (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                      have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                        rw [hcache'']; exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hCWoe
                                      have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                        rw [hcache'']; exact VeriDNS.Proof.Cache.boundLru_bounded (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))
                                      have hmiss'' : (αCache state''.resources.cache).hit now q = [] := by
                                        rw [hcache'']
                                        refine hcf.hit_nil (Nat.le_refl now) (hcf0.hit_nil (Nat.le_refl now) ?_)
                                        exact absorb_hit_nil c now _ q ref hmiss (VeriDNS.Spec.Net.Response.isReferral_answer_nil href) (VeriDNS.Spec.Net.Response.isReferral_aa_false href)
                                      have hnmiss'' : (αCache state''.resources.cache).negHit now q = false := by
                                        rw [hcache'']
                                        calc (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)).negHit now q
                                            = (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))).negHit now q := hcf.2.2.1 now q
                                          _ = (c.absorb now (absorbBailiwick ((referralCut ref).drop ((referralCut ref).length - depthFloor)) (referralCut ref)) ref).negHit now q := hcf0.2.2.1 now q
                                          _ = c.negHit now q := by rw [VeriDNS.Spec.Net.absorb_negHit_eq]
                                          _ = false := hnmiss
                                      have hlq'' : state''.lastQuery = state.lastQuery := by rw [hst2]; exact hstLq
                                      have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                        rw [hcache'']
                                        exact wfrrAll_boundLru _ _ (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)
                                      have hNegWf'' : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          CacheNegWf state''.resources.cache qu.qclass := by
                                        intro qu hqu'
                                        rw [hcache'']
                                        exact CacheNegWf_boundLru _ _ (CacheNegWf_cacheUnlessTruncated _ _ _ _ _
                                          (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu (by rw [← hlq'']; exact hqu'))))
                                      have hqm'' : ∀ qu : VeriDNS.Spec.Question,
                                          (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                          αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by rw [hlq'']; exact hqm
                                      have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hst2, hstNow]; exact hclock
                                      have hstep'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := by rw [hst2]; exact hstStep
                                      have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                        rw [hst2, hstSbelt]; exact hGlBelt
                                      have hnsne : Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority) ≠ #[] :=
                                        extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn respA.authority hfacts.2.2.2.2.1
                                      rcases hdisj with hkept | ⟨nsNames, mc, hwalk, hclose_eq, hrebuild⟩ | ⟨hbelt, hbeltcond⟩
                                      ·
                                        have hslist'' : state''.resources.slist
                                            = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional))
                                              (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) := by rw [hst2]; exact hkept
                                        have hGlProv'' : GluelessProv state''.resources.slist := by
                                          rw [hslist'']
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (extractNsNames_ownerRaws_canonical respA.authority (by
                                              intro b hb
                                              rw [hcapAuth, Array.toList_map, List.mem_map] at hb
                                              obtain ⟨b0, hb0, rfl⟩ := hb
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))))
                                        have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            state''.resources.slist = (referralCut ref).length := by
                                          rw [hslist'', matchCount_setUpAddresses]; exact hbridge
                                        have hfreshInv'' : ∀ b ∈ ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen), b.length < (referralCut ref).length := by
                                          intro b hb
                                          rcases List.mem_cons.mp hb with rfl | hb
                                          · rw [hfrLen]; omega
                                          · have := hfreshInv b hb; omega
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                          (αCache state''.resources.cache) _ w' now nseen
                                          ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) (referralCut ref).length resp cout
                                          (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                          hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                        have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                        rw [hlq'', hnowSt] at hrest
                                        have hauthE : (αResp respA).authority = ref.authority := hnstail.2.2.1
                                        have haddE : (αResp respA).additional = ref.additional := hnstail.2.2.2.1
                                        have hgae : glueAddresses (αResp respA) = glueAddresses ref :=
                                          glueAddresses_congr hauthE haddE
                                        have hvalidAuth' : ∀ b ∈ respA.authority.toList, ∀ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hne⟩ := hvalidAuth b hb
                                          rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                        have hvalidAdd' : ∀ b ∈ respA.additional.toList, ∀ rr,
                                            VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                          intro b hb rr hpr
                                          obtain ⟨rr', hpr', hne⟩ := hnstail.2.2.2.2.2.1 b hb
                                          rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                        have hconn := glueAddresses_subperm_transient respA (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) hcutRef hvalidAuth'
                                          hvalidAdd' hnstail.1 hfacts.2.2.2.2.1
                                        have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                            ∨ (glueAddresses ref).Subperm s := by
                                          refine Or.inr ?_
                                          rw [← hgae]
                                          refine hconn.trans ?_
                                          rw [hslist''] at hperm
                                          exact hperm
                                        have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                          rw [← hcache'']; exact hrec
                                        exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                          trustedReferral_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) (byteAddrToModel (Server.ipv4ToAddr ipAddr))
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor))
                                            (w.ids w.idCtr).toNat 0 c
                                            (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q) ref)
                                            hmiss hnmiss
                                            (VeriDNS.Spec.Net.Transit.deliver _ _ _ hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                            (accepts_reply _ _ _ _ _ _ _)
                                            href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                            (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))) hcf0 hgl
                                            (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                          hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                      ·
                                        have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                            respA.authority state.resources.sname ≤ mc := by
                                          have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                                (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                                (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                  (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                            rw [searchFails_setUpAddresses]; simpa using hnsne
                                          have hmc0 := hclose_eq
                                          rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hmc0
                                          simpa using hmc0
                                        have hslist'' : state''.resources.slist
                                            = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)) state.now nsNames) mc := by
                                          rw [hst2]; exact hrebuild
                                        have hGlProv'' : GluelessProv state''.resources.slist := by
                                          rw [hslist'']
                                          exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                            (walkNs_names_canonical _ state.now
                                              (CacheNsCanon_absorb state.resources.cache respA
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                    (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                                (by
                                                  intro raw hraw
                                                  have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                                  rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                    (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                              128 state.resources.sname nsNames mc hwalk)
                                        have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            state''.resources.slist = mc := by rw [hslist'', matchCount_setUpAddresses]
                                        have hsubmc : (referralCut ref).length ≤ mc := by rw [← hbridge]; exact hge
                                        have hfreshInv'' : ∀ b ∈ ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen), b.length < mc := by
                                          intro b hb
                                          rcases List.mem_cons.mp hb with rfl | hb
                                          · rw [hfrLen]; omega
                                          · have := hfreshInv b hb; omega
                                        obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                          (αCache state''.resources.cache) _ w' now nseen
                                          ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) mc resp cout
                                          (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                          hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                        have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                        rw [hlq'', hnowSt] at hrest
                                        have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                            ∨ (glueAddresses ref).Subperm s := by
                                          refine Or.inl ?_
                                          obtain ⟨sname_lab, hsna, hlabq⟩ :
                                              ∃ lab, VeriDNS.Impl.DomainName.wireFormatToLabels state.resources.sname = .ok lab
                                                ∧ lab.toList = q.qname := by
                                            unfold αName at hsn
                                            split at hsn
                                            · next lab h => exact ⟨lab, h, Option.some.inj hsn⟩
                                            · exact absurd hsn (by simp)
                                          have hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab := by
                                            intro i hi
                                            have hmem : sname_lab[i] ∈ q.qname := by
                                              rw [← hlabq]; exact Array.mem_def.mp (Array.getElem_mem hi)
                                            exact hqvalid _ hmem
                                          have hkey := refer_continue_keystone_wf
                                            ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                                state.resources.cache respA
                                                (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                                (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                              respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                              Resolver.credAdditional state.now))
                                            state.resources.sname q.qname sname_lab nsNames mc state.now
                                            hwalk hsna hsnav hsnameCanon hlabq hqlen hCWwf
                                            (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                            (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                          rw [← htm]
                                          refine hkey.trans ?_
                                          rw [← hslist'']
                                          exact hperm
                                        have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                          rw [← hcache'']; exact hrec
                                        exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                          trustedReferral_hasVerdictAt net ns ra ednsBuf rttOf
                                            (byteAddrToModel (Server.ipv4ToAddr ipAddr)) (byteAddrToModel (Server.ipv4ToAddr ipAddr))
                                            ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                            ((referralCut ref).drop ((referralCut ref).length - depthFloor))
                                            (w.ids w.idCtr).toNat 0 c
                                            (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q) ref)
                                            hmiss hnmiss
                                            (VeriDNS.Spec.Net.Transit.deliver _ _ _ hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                            (accepts_reply _ _ _ _ _ _ _)
                                            href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                            (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))) hcf0 hgl
                                            (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                          hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                      ·
                                        exfalso
                                        have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                          rw [searchFails_setUpAddresses]; simpa using hnsne
                                        rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hbeltcond
                                        have : 0 < (referralCut ref).length := by omega
                                        rw [hbridge] at hbeltcond
                                        simp only [decide_eq_false_iff_not, Nat.not_lt] at hbeltcond
                                        omega
                                  ·

                                    obtain ⟨origin, reply, srcPort, htrans, hacc, _hragS, hclsLink, htcR, hauthS, _hvld, hvldA, hrefImpl⟩ := hspoof
                                    have hcls : Resolver.classifiableB respA = true := by
                                      have h := (Bool.or_eq_false_iff.mp hbiz).2; simpa using h
                                    have hsf : (respA.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false :=
                                      (Bool.or_eq_false_iff.mp hbiz).1
                                    obtain ⟨nsG, sG, hgoto⟩ := afterResume_continue_stepAnalyze_goto
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA state'' hstep hcn hsf hcls heqC
                                    rcases stepAnalyzeResponse_goto_cases
                                        ({ ({ state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }) with
                                          lastResponse := some respA,
                                          currentStep := VeriDNS.Spec.AlgorithmStep.analyzeResponse })
                                        respA nsG sG rfl hcn hbiz hgoto
                                      with ⟨-, hfacts⟩ | ⟨-, -, h4bL, hrefL, hnodataL⟩ | ⟨hnsG, hsG, -⟩
                                    rotate_left
                                    · -- B.3: lame referral ⇒ retry
                                      rw [afterResume_lame
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA hstep hcn hbiz h4bL hrefL hnodataL] at heqC
                                      have hst := Server.IoStep.continue.inj heqC
                                      subst hst
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansV, hrest⟩ := IH ml (by omega) q depth f _
                                        (Server.boundStateCache
                                          (Server.roundTouches
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            respA)
                                          { resources :=
                                              { sname := state.resources.sname, stype := state.resources.stype,
                                                sclass := state.resources.sclass,
                                                slist := state.resources.slist.markQueried entry.name,
                                                sbelt := state.resources.sbelt, cache := state.resources.cache },
                                            currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                            lastQuery := state.lastQuery, lastResponse := none,
                                            cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                        c _ w' now nseen seen depthFloor resp cout
                                        ⟨by
                                            show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                            rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                          hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                        (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                        (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                        (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                        (by exact wfrrAll_boundLru _ _ hwfrr)
                                        (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                        (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                        (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                        (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                        hmiss hnmiss hfreshInv (by exact hMC)
                                        (by exact GluelessProv_markQueried entry.name hGlProv)
                                        (by exact hGlBelt)
                                        hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                      obtain ⟨l, hp, hsl⟩ := hperm
                                      have hp' : l.Perm (modelSlistOf
                                          (state.resources.slist.markQueried entry.name)) := hp
                                      rw [modelSlistOf_markQueried] at hp'
                                      exact ⟨_, v, cM, hrec, ⟨l, hp', hsl⟩, hrc, hansV, hrest⟩
                                    · -- G: ambiguous empty NOERROR ⇒ retry (mirrors B.3)
                                      rw [hnsG, hsG] at hgoto
                                      rw [afterResume_of_stepGoto
                                          { state with resources := { state.resources with
                                              slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA hstep hbiz hgoto] at heqC
                                      have hst := Server.IoStep.continue.inj heqC
                                      subst hst
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansV, hrest⟩ := IH ml (by omega) q depth f _
                                        (Server.boundStateCache
                                          (Server.roundTouches
                                            { state with resources := { state.resources with
                                                slist := state.resources.slist.markQueried entry.name } }
                                            respA)
                                          { resources :=
                                              { sname := state.resources.sname, stype := state.resources.stype,
                                                sclass := state.resources.sclass,
                                                slist := state.resources.slist.markQueried entry.name,
                                                sbelt := state.resources.sbelt, cache := state.resources.cache },
                                            currentStep := VeriDNS.Spec.AlgorithmStep.sendQueries,
                                            lastQuery := state.lastQuery, lastResponse := none,
                                            cnameChain := state.cnameChain, noEdns := state.noEdns, now := state.now })
                                        c _ w' now nseen seen depthFloor resp cout
                                        ⟨by
                                            show MatchMaxEquiv (αCache (state.resources.cache.boundLru _ _)) c
                                            rw [αCache_boundLru_noop state.resources.cache _ _ hCap]; exact hmme,
                                          hsn, htm, (by exact hwm)⟩ (by exact hwmTcp)
                                        (CacheWf_boundLru state.resources.cache _ _ state.now hCacheWf)
                                        (CacheNsCanon_boundLru state.resources.cache _ _ hNsCanon)
                                        (CacheCnameCanon_boundLru state.resources.cache _ _ hCnCanon)
                                        (by exact wfrrAll_boundLru _ _ hwfrr)
                                        (by exact fun qu hqu' => CacheNegWf_boundLru _ _ (hNegWf qu hqu'))
                                        (CacheNsDistinct_boundLru state.resources.cache _ _ hNsDistinct)
                                        (VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOE)
                                        (VeriDNS.Proof.Cache.boundLru_bounded state.resources.cache _ _)
                                        hmiss hnmiss hfreshInv (by exact hMC)
                                        (by exact GluelessProv_markQueried entry.name hGlProv)
                                        (by exact hGlBelt)
                                        hqm hrd hqstar hqin (by exact hclock) (by exact hsnameCanon) (by exact hqlen) (by exact hqvalid) (by exact hCCM) (by exact hAW) rfl hrun
                                      obtain ⟨l, hp, hsl⟩ := hperm
                                      have hp' : l.Perm (modelSlistOf
                                          (state.resources.slist.markQueried entry.name)) := hp
                                      rw [modelSlistOf_markQueried] at hp'
                                      exact ⟨_, v, cM, hrec, ⟨l, hp', hsl⟩, hrc, hansV, hrest⟩
                                    have hirTrue : (αResp respA).isReferral = true :=
                                      αResp_isReferral_true_of_referralShape hfacts.2.2.1
                                        hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.1
                                        hfacts.2.2.2.2.2.2.2 hvldA
                                    have href : reply.msg.isReferral = true := hclsLink.symm.trans hirTrue
                                    have hauthE : αSection respA.authority = reply.msg.authority := hauthS
                                    obtain ⟨haddE, haaE, hbail, haddWf, hcutBr, hnsCanonG, htcEg⟩ := hrefImpl href
                                    have hcutQ : isAncestor (referralCut reply.msg) q.qname = true :=
                                      isAncestor_referralCut_of_inBailiwick hbail
                                    have hdel : Server.delegationShapedB respA = true :=
                                      delegationShapedB_of respA hfacts.2.2.2.2.1 hfacts.1 hfacts.2.1 hcn
                                    have hunfF : Server.unfollowableDelegationB
                                        (state.resources.slist.markQueried entry.name)
                                        state.resources.sname respA = false := by simpa using hunf
                                    have hrib : Server.respInBailiwick state.resources.sname respA = true :=
                                      respInBailiwick_of_not_unfollowable _ _ _ hunfF hdel
                                    have hbridge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                        respA.authority state.resources.sname = (referralCut reply.msg).length :=
                                      hcutBr state.resources.sname hrib
                                    have hsfF : VeriDNS.Spec.SlistFromNameSpec.searchFails
                                        (NS := VeriDNS.Spec.SlistEntry)
                                        (state.resources.slist.markQueried entry.name) = false := by
                                      have hne : state.resources.slist.servers ≠ #[] := by
                                        intro hemp
                                        rw [DnsSList.bestWithAddress, hemp] at hbest
                                        simp at hbest
                                      show (state.resources.slist.markQueried entry.name).servers.isEmpty = false
                                      simp only [DnsSList.markQueried]
                                      by_contra h
                                      rw [Bool.not_eq_false] at h
                                      apply hne
                                      simpa using congrArg Array.size (Array.isEmpty_iff.mp h)
                                    have hgt : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                        respA.authority state.resources.sname
                                        > state.resources.slist.matchCount := by
                                      have hcloser : Server.delegationCloserB
                                          (state.resources.slist.markQueried entry.name)
                                          state.resources.sname respA = true :=
                                        delegationCloserB_of_not_unfollowable _ _ _ hunfF hdel
                                      unfold Server.delegationCloserB at hcloser
                                      rw [hsfF, Bool.false_or] at hcloser
                                      exact of_decide_eq_true hcloser

                                    have hfloorlt : depthFloor < (referralCut reply.msg).length := by
                                      rw [← hbridge]; rw [← hMC]; exact hgt
                                    have hcutlenF : depthFloor ≤ (referralCut reply.msg).length := by omega
                                    obtain ⟨hfrAnc, hfrLen⟩ := isAncestor_drop_ancestor (n := referralCut reply.msg)
                                      (k := depthFloor) hcutlenF
                                    have hdescF : reply.msg.descendsBelow
                                        ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) = true :=
                                      descendsBelow_of_strict hfrAnc (by rw [hfrLen]; omega)
                                    have hfresh : (referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) ∉ seen := by
                                      intro hmem
                                      have hlt := hfreshInv _ hmem
                                      rw [hfrLen] at hlt
                                      exact Nat.lt_irrefl _ hlt

                                    have haaF : (respA.header.aa == 1) = false := by
                                      have h0 : respA.header.aa = 0 := eq_of_beq hfacts.2.2.2.2.2.1
                                      rw [h0]
                                      decide
                                    have htcF : (respA.header.tc == 1) = false := htcEg.trans htcR
                                    have htm' : state.now.toNat = now := htm
                                    have hvalA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (αRR rr).isSome = true := by
                                      intro b hb rr hpr
                                      obtain ⟨rr', hpr', hα'⟩ := hvldA b (bailiwickRaws_toList_sub hb)
                                      rw [hpr'] at hpr
                                      injection hpr with hrr
                                      subst hrr
                                      cases hα : αRR rr' with
                                      | none => exact absurd hα hα'
                                      | some r => rfl
                                    have hvalD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (αRR rr).isSome = true := by
                                      intro b hb rr hpr
                                      obtain ⟨rr', hpr', hα'⟩ := haddWf b (bailiwickRaws_toList_sub hb)
                                      rw [hpr'] at hpr
                                      injection hpr with hrr
                                      subst hrr
                                      cases hα : αRR rr' with
                                      | none => exact absurd hα hα'
                                      | some r => rfl
                                    have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                    have hnoA0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                      intro b hb rr hpr
                                      have hb' : b ∈ respS.authority := by
                                        rw [← hrespAeq]
                                        exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                      have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                        (Or.inl (Or.inr hb')) rr hpr
                                      exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                    have hnoD0 : ∀ b ∈ (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional).toList,
                                        ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                        (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                      intro b hb rr hpr
                                      have hb' : b ∈ respS.additional := by
                                        rw [← hrespAeq]
                                        exact Array.mem_def.mpr (bailiwickRaws_toList_sub hb)
                                      have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                        (Or.inr hb') rr hpr
                                      exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                    have hcutRef : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (referralCut (αResp respA)) :=
                                      referralCutRaw_αName respA.authority hvldA hfacts.2.2.2.2.1
                                    have hrefEq : referralCut (αResp respA) = referralCut reply.msg := by
                                      unfold VeriDNS.Spec.Net.referralCut
                                      rw [show (αResp respA).authority = reply.msg.authority from hauthE]
                                    have habsF : absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg) = referralCut reply.msg :=
                                      absorbBailiwick_of_descendsBelow _ reply.msg hdescF
                                    have hcutαF : αName (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) = some (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) := by
                                      rw [habsF, ← hrefEq]
                                      exact hcutRef
                                    have hCWwf : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now) state.now :=
                                      CacheWf_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCacheWf hvalA0 hnoA0 hvalD0 hnoD0
                                    have hCWoe : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now) :=
                                      OneExpiryPerKey_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hOE
                                    have hcf0 : WriteRefines now (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))
                                        (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg) := by
                                      have h := refer_write_WriteRefines_ref state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority)
                                        (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg))
                                        state.now (respA.header.aa == 1) haaF hcutαF htcF hirTrue hCacheWf hOE
                                        (normRaws_hval hvalA0) (normRaws_hval hvalD0) (normRaws_hno hnoA0) (normRaws_hno hnoD0) (rrsOf_RRCanonMappable hvalA0) (rrsOf_RRCanonMappable hvalD0) reply.msg c href hauthE haddE haaE hmme
                                      rw [htm'] at h
                                      exact h
                                    have hcf : WriteRefines now (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)) :=
                                      (αCache_boundLru_refines (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now) (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)).writeRefines now

                                    obtain ⟨stC, heqStC, hstCache, hstSn, hstNow, hstCh, hstStep, hstLq, hstSbelt, hdisj⟩ :=
                                      afterResume_referral_continue_cases { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA hstep hcn hbiz hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
                                    have hst2 : state'' = stC := Server.IoStep.continue.inj (heqC.symm.trans heqStC)
                                    have hsn'' : αName state''.resources.sname = some q.qname := by rw [hst2, hstSn]; exact hsn
                                    have hsnameCanon'' : state''.resources.sname = VeriDNS.Impl.DomainName.labelsToWireFormatGo q.qname := by
                                      rw [hst2, hstSn]; exact hsnameCanon
                                    have htm'' : αTime state''.now = now := by rw [hst2, hstNow]; exact htm
                                    have hCCM'' : CnameChainModels state'' q nseen :=
                                      CnameChainModels_congr (by rw [hst2]; exact hstLq)
                                        (by rw [hst2]; exact hstSn) (by rw [hst2]; exact hstCh) hCCM
                                    have hcache'' : state''.resources.cache = ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now := by rw [hst2]; exact hstCache
                                    have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                      unfold Server.sanitizeTtlsCap at hsani; exact (Option.some.inj hsani).symm
                                    have hcapAuth : respA.authority = resp0.authority.map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                    have hcapAdd : respA.additional = (resp0.additional.filter (fun b => !Edns.isOptRR b)).map Server.capTtlRR := by rw [hrespAeq, hcapEq]; rfl
                                    have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                      rw [hcache'', hst2, hstNow]; exact CacheWf_boundLru (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)) state.now hCWwf
                                    have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                      rw [hcache'']
                                      refine CacheNsCanon_boundLru _ _ _ (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon ?_ ?_)
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                    have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                      rw [hcache'']
                                      refine CacheCnameCanon_boundLru _ _ _ (CacheCnameCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hCnCanon ?_ ?_)
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                      · intro raw hraw
                                        have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                        rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                        obtain ⟨b0, hb0, rfl⟩ := hmem
                                        exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)
                                    have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                      rw [hcache'']; exact CacheNsDistinct_boundLru _ _ _ (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                    have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                      rw [hcache'']; exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hCWoe
                                    have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                      rw [hcache'']; exact VeriDNS.Proof.Cache.boundLru_bounded (ks := _) (tnow := _) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))
                                    have hmiss'' : (αCache state''.resources.cache).hit now q = [] := by
                                      rw [hcache'']
                                      refine hcf.hit_nil (Nat.le_refl now) (hcf0.hit_nil (Nat.le_refl now) ?_)
                                      exact absorb_hit_nil c now _ q reply.msg hmiss (VeriDNS.Spec.Net.Response.isReferral_answer_nil href) (VeriDNS.Spec.Net.Response.isReferral_aa_false href)
                                    have hnmiss'' : (αCache state''.resources.cache).negHit now q = false := by
                                      rw [hcache'']
                                      calc (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)).negHit now q
                                          = (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))).negHit now q := hcf.2.2.1 now q
                                        _ = (c.absorb now (absorbBailiwick ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor)) (referralCut reply.msg)) reply.msg).negHit now q := hcf0.2.2.1 now q
                                        _ = c.negHit now q := by rw [VeriDNS.Spec.Net.absorb_negHit_eq]
                                        _ = false := hnmiss
                                    have hlq'' : state''.lastQuery = state.lastQuery := by rw [hst2]; exact hstLq
                                    have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                      rw [hcache'']
                                      exact wfrrAll_boundLru _ _ (wfrrAll_cacheUnlessTruncated (wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _) _ _ _ _)
                                    have hNegWf'' : ∀ qu : VeriDNS.Spec.Question,
                                        (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                        CacheNegWf state''.resources.cache qu.qclass := by
                                      intro qu hqu'
                                      rw [hcache'']
                                      exact CacheNegWf_boundLru _ _ (CacheNegWf_cacheUnlessTruncated _ _ _ _ _
                                        (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu (by rw [← hlq'']; exact hqu'))))
                                    have hqm'' : ∀ qu : VeriDNS.Spec.Question,
                                        (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                        αQType qu.qtype = some q.qtype ∧ αClass qu.qclass = some q.qclass := by rw [hlq'']; exact hqm
                                    have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hst2, hstNow]; exact hclock
                                    have hstep'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := by rw [hst2]; exact hstStep
                                    have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                      rw [hst2, hstSbelt]; exact hGlBelt
                                    have hnsne : Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority) ≠ #[] :=
                                      extractNsNames_ownerRaws_cut_ne_of_hasRRTypeIn respA.authority hfacts.2.2.2.2.1
                                    rcases hdisj with hkept | ⟨nsNames, mc, hwalk, hclose_eq, hrebuild⟩ | ⟨hbelt, hbeltcond⟩
                                    ·
                                      have hslist'' : state''.resources.slist
                                          = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional))
                                            (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) := by rw [hst2]; exact hkept
                                      have hGlProv'' : GluelessProv state''.resources.slist := by
                                        rw [hslist'']
                                        exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                          (extractNsNames_ownerRaws_canonical respA.authority (by
                                            intro b hb
                                            rw [hcapAuth, Array.toList_map, List.mem_map] at hb
                                            obtain ⟨b0, hb0, rfl⟩ := hb
                                            exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                              (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0))))
                                      have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                          state''.resources.slist = (referralCut reply.msg).length := by
                                        rw [hslist'', matchCount_setUpAddresses]; exact hbridge
                                      have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < (referralCut reply.msg).length := by
                                        intro b hb
                                        rcases List.mem_cons.mp hb with rfl | hb
                                        · rw [hfrLen]; omega
                                        · have := hfreshInv b hb; omega
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                        (αCache state''.resources.cache) _ w' now nseen
                                        ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (referralCut reply.msg).length resp cout
                                        (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                        hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                      have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                      rw [hlq'', hnowSt] at hrest
                                      have hgae : glueAddresses (αResp respA) = glueAddresses reply.msg :=
                                            glueAddresses_congr hauthE haddE
                                      have hvalidAuth' : ∀ b ∈ respA.authority.toList, ∀ rr,
                                          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hne⟩ := hvldA b hb
                                        rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                      have hvalidAdd' : ∀ b ∈ respA.additional.toList, ∀ rr,
                                          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr → αRR rr ≠ none := by
                                        intro b hb rr hpr
                                        obtain ⟨rr', hpr', hne⟩ := haddWf b hb
                                        rw [hpr'] at hpr; injection hpr with h; subst h; exact hne
                                      have hconn := glueAddresses_subperm_transient respA (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname) hcutRef hvalidAuth'
                                        hvalidAdd' hnsCanonG hfacts.2.2.2.2.1
                                      have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                          ∨ (glueAddresses reply.msg).Subperm s := by
                                        refine Or.inr ?_
                                        rw [← hgae]
                                        refine hconn.trans ?_
                                        rw [hslist''] at hperm
                                        exact hperm
                                      have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                        rw [← hcache'']; exact hrec
                                      exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                        trustedReferral_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                          ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                          (w.ids w.idCtr).toNat srcPort c reply
                                          hmiss hnmiss htrans hacc
                                          href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                          (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))) hcf0 hgl
                                          (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                        hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                    ·
                                      have hge : Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
                                          respA.authority state.resources.sname ≤ mc := by
                                        have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                              (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                              (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                                (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                          rw [searchFails_setUpAddresses]; simpa using hnsne
                                        have hmc0 := hclose_eq
                                        rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hmc0
                                        simpa using hmc0
                                      have hslist'' : state''.resources.slist
                                          = VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            nsNames (reGlue (RR := VeriDNS.Spec.ResourceRecord) ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)) state.now nsNames) mc := by
                                        rw [hst2]; exact hrebuild
                                      have hGlProv'' : GluelessProv state''.resources.slist := by
                                        rw [hslist'']
                                        exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                          (walkNs_names_canonical _ state.now
                                            (CacheNsCanon_absorb state.resources.cache respA
                                              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                  (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                              (by
                                                intro raw hraw
                                                have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                                rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                                obtain ⟨b0, hb0, rfl⟩ := hmem
                                                exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                                  (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                            128 state.resources.sname nsNames mc hwalk)
                                      have hMC'' : VeriDNS.Spec.SlistFromNameSpec.matchCount (S := DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                          state''.resources.slist = mc := by rw [hslist'', matchCount_setUpAddresses]
                                      have hsubmc : (referralCut reply.msg).length ≤ mc := by rw [← hbridge]; exact hge
                                      have hfreshInv'' : ∀ b ∈ ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen), b.length < mc := by
                                        intro b hb
                                        rcases List.mem_cons.mp hb with rfl | hb
                                        · rw [hfrLen]; omega
                                        · have := hfreshInv b hb; omega
                                      obtain ⟨s, v, cM, hrec, hperm, hrc, hansD, hrest⟩ := IH ml (by omega) q depth f _ state''
                                        (αCache state''.resources.cache) _ w' now nseen
                                        ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) mc resp cout
                                        (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                        hmiss'' hnmiss'' hfreshInv'' hMC'' hGlProv'' hGlBelt'' hqm'' hrd hqstar hqin hclock'' hsnameCanon'' (by exact hqlen) (by exact hqvalid) hCCM'' (by rw [hst2, hstCh, hstNow]; exact hAW) hstep'' hrun
                                      have hnowSt : state''.now = state.now := by rw [hst2]; exact hstNow
                                      rw [hlq'', hnowSt] at hrest
                                      have hgl : (((αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))).referralSlist now q.qname (q.qname.length + 1)).Subperm s)
                                          ∨ (glueAddresses reply.msg).Subperm s := by
                                        refine Or.inl ?_
                                        obtain ⟨sname_lab, hsna, hlabq⟩ :
                                            ∃ lab, VeriDNS.Impl.DomainName.wireFormatToLabels state.resources.sname = .ok lab
                                              ∧ lab.toList = q.qname := by
                                          unfold αName at hsn
                                          split at hsn
                                          · next lab h => exact ⟨lab, h, Option.some.inj hsn⟩
                                          · exact absurd hsn (by simp)
                                        have hsnav : VeriDNS.Proof.DomainName.ValidLabels sname_lab := by
                                          intro i hi
                                          have hmem : sname_lab[i] ∈ q.qname := by
                                            rw [← hlabq]; exact Array.mem_def.mp (Array.getElem_mem hi)
                                          exact hqvalid _ hmem
                                        have hkey := refer_continue_keystone_wf
                                          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                              state.resources.cache respA
                                              (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                              (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                            respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                            Resolver.credAdditional state.now))
                                          state.resources.sname q.qname sname_lab nsNames mc state.now
                                          hwalk hsna hsnav hsnameCanon hlabq hqlen hCWwf
                                          (CacheNsCanon_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsCanon
                                            (by
                                              intro raw hraw
                                              have hmem : raw ∈ respA.authority.toList := bailiwickRaws_toList_sub hraw
                                              rw [hcapAuth, Array.toList_map, List.mem_map] at hmem
                                              obtain ⟨b0, hb0, rfl⟩ := hmem
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_authority_canonicalRR hdec b0 (Array.mem_def.mpr hb0)))
                                            (by
                                              intro raw hraw
                                              have hmem : raw ∈ respA.additional.toList := bailiwickRaws_toList_sub hraw
                                              rw [hcapAdd, Array.toList_map, List.mem_map] at hmem
                                              obtain ⟨b0, hb0, rfl⟩ := hmem
                                              exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0 (VeriDNS.Proof.Message.decode_additional_canonicalRR hdec b0 (Array.mem_filter.mp (Array.mem_def.mpr hb0)).1)))
                                          (CacheNsDistinct_absorb state.resources.cache respA (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) state.now hNsDistinct)
                                        rw [← htm]
                                        refine hkey.trans ?_
                                        rw [← hslist'']
                                        exact hperm
                                      have hrec'' : HasVerdictAt net ns ra ednsBuf rttOf now nseen
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor) :: seen) (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) s q v cM := by
                                        rw [← hcache'']; exact hrec
                                      exact ⟨(byteAddrToModel (Server.ipv4ToAddr ipAddr)) :: ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))), v, cM,
                                        trustedReferral_hasVerdictAt net ns ra ednsBuf rttOf
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                          ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                          ((referralCut reply.msg).drop ((referralCut reply.msg).length - depthFloor))
                                          (w.ids w.idCtr).toNat srcPort c reply
                                          hmiss hnmiss htrans hacc
                                          href hbail hcutQ hdescF hfresh (Nat.le_refl now) v s
                                          (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now))) hcf0 hgl
                                          (αCache (((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                            state.resources.cache respA
                                            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority)
                                            (Resolver.credAuthority (respA.header.aa == 1)) state.now)
                                          respA
                                          (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)
                                          Resolver.credAdditional state.now)).boundLru (Server.roundTouches { state with resources := { state.resources with slist := state.resources.slist.markQueried entry.name } } respA) state.now)) hcf cM hrec'',
                                        hpermAns.symm.subperm, hrc, by rw [hst2, hstCh] at hansD; exact hansD, hrest⟩
                                    ·
                                      exfalso
                                      have hsfF0 : VeriDNS.Spec.SlistFromNameSpec.searchFails (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                          (VeriDNS.Spec.SlistFromNameSpec.setUpAddresses (S := SList.DnsSList) (NS := VeriDNS.Spec.SlistEntry)
                                            (Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.authority))
                                            (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
                                              (Resolver.referralCutRaw (RR := VeriDNS.Spec.ResourceRecord) respA.authority) respA.additional)) (Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord) respA.authority state.resources.sname)) = false := by
                                        rw [searchFails_setUpAddresses]; simpa using hnsne
                                      rw [hsfF0, Bool.not_false, Bool.true_and, matchCount_setUpAddresses] at hbeltcond
                                      have : 0 < (referralCut reply.msg).length := by omega
                                      rw [hbridge] at hbeltcond
                                      simp only [decide_eq_false_iff_not, Nat.not_lt] at hbeltcond
                                      omega
                              ·

                                obtain ⟨target, hcnT⟩ := Option.ne_none_iff_exists'.mp hcn
                                obtain ⟨q₀L, quL, hq0, hqu0, hsubq⟩ := buildSubQuery_inv state subQuery0 revealed hbuild
                                rw [subQuestion_full hfull quL] at hsubq
                                have hqmL := hqm quL ⟨q₀L, hq0, hqu0⟩
                                obtain ⟨qaR, hqaR, hqaCI, hqaT, _hqaC⟩ := questionMatches_fields
                                  (withSecrets_question subQuery0 (w.ids w.idCtr) (w.ids (w.idCtr + 1)) hsubq)
                                      (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI _ _)
                                  (acceptResponse_questionMatches haccR)
                                have hqt : q.qtype.covers RRType.cname = false :=
                                  covers_cname_false_of_chase respA target qaR q hcnT hqaR
                                    (by rw [hqaT]; exact hqmL.1) hqstar
                                obtain ⟨t, ht, hqq⟩ := αQType_rr_inv hqmL.1 hqstar
                                have htne : t ≠ RRType.cname := by
                                  intro hteq
                                  rw [hqq, hteq] at hqt
                                  exact absurd hqt (by decide)
                                have hvalidAns : ∀ b ∈ respA.answer.toList, ∃ rr,
                                    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
                                      ∧ αRR rr ≠ none := by
                                  rcases hwmApp with ⟨_, _, _, -, -, -, -, -, -, -, -, hvalid, -⟩ |
                                    ⟨_, _, _, -, -, -, -, -, -, hvld, -⟩
                                  · exact hvalid
                                  · exact hvld
                                have hrespAeq : respA = respS := acceptResponse_some_eq haccR
                                have hcapEq : respS = Server.capTtls (Edns.stripOpt resp0) := by
                                  unfold Server.sanitizeTtlsCap at hsani
                                  exact (Option.some.inj hsani).symm
                                have hcapAns : respA.answer = resp0.answer.map Server.capTtlRR := by
                                  rw [hrespAeq, hcapEq]; rfl
                                have hquesEq : respA.question = resp0.question := by
                                  rw [hrespAeq, hcapEq]; rfl
                                have hqfl : VeriDNS.Proof.Message.QuestionFromLabels qaR := by
                                  have hqaR0 : resp0.question[0]? = some qaR := by
                                    rw [← hquesEq]; exact hqaR
                                  obtain ⟨-, -, -, -, hqs, -, -, -⟩ :=
                                    VeriDNS.Proof.DeliveredWire.decode_ok_wire_facts hdec
                                  rw [Array.getElem?_eq_some_iff] at hqaR0
                                  obtain ⟨hlt, hget⟩ := hqaR0
                                  exact hget ▸ hqs ⟨0, hlt⟩
                                obtain ⟨qnR, hαR, hcanR, hvalR⟩ := questionFromLabels_canonical hqfl
                                have hqnRq : VeriDNS.Spec.Net.nameEq qnR q.qname = true := by
                                  obtain ⟨qnR', hαR', hne'⟩ := αName_of_nameEqCI hqaCI hsn
                                  obtain rfl : qnR' = qnR := Option.some.inj (hαR'.symm.trans hαR)
                                  exact hne'
                                obtain ⟨quE, hquE, hextQ⟩ := (cnameToChase_some respA target hcnT).2
                                rw [show quE = qaR from Option.some.inj (hquE.symm.trans hqaR)] at hextQ
                                obtain ⟨cnBytes, rrCn, cn, tgt, hextRR, hcnMem, hprC, hty5, hrdT, hαcn, hcnRR, hcnrd, hαtgt⟩ :=
                                  cname_link_facts hαR hcanR hvalR hextQ hvalidAns
                                rw [VeriDNS.Spec.Net.cnameRR_congr hqnRq] at hcnRR
                                have hcanonAns : ∀ raw ∈ respA.answer.toList, VeriDNS.Proof.Message.CanonicalRR raw := by
                                  intro raw hmem
                                  rw [hcapAns, Array.toList_map, List.mem_map] at hmem
                                  obtain ⟨b0, hb0, rfl⟩ := hmem
                                  exact VeriDNS.Proof.TtlCap.canonicalRR_capTtlRR b0
                                    (VeriDNS.Proof.Message.decode_answer_canonicalRR hdec b0 (Array.mem_def.mpr hb0))
                                obtain ⟨na0, hna0, hnacan0, hnaval0, hnalen0⟩ :=
                                  canonicalRR_cnameRdata_canonical (hcanonAns cnBytes hcnMem) hprC hty5
                                have hna0tgt : na0 = tgt := by
                                  rw [hrdT] at hna0
                                  exact Option.some.inj (hna0.symm.trans hαtgt)
                                rw [hna0tgt] at hnacan0 hnaval0 hnalen0
                                have htB : target = VeriDNS.Impl.DomainName.labelsToWireFormatGo tgt := by
                                  rw [← hrdT]; exact hnacan0
                                have hanchor : ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim
                                    state.resources.sname (fun qu => qu.qname)) = quL.qname := by
                                  rw [hq0]
                                  show (q₀L.question[0]?).elim state.resources.sname (fun qu => qu.qname) = quL.qname
                                  rw [hqu0]
                                  rfl
                                have hCCM' : ∀ nm ∈ q.qname :: nseen, ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                                    quL.qname state.cnameChain).toList,
                                    αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                      ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                  have h := hCCM
                                  unfold CnameChainModels at h
                                  rw [hanchor] at h
                                  exact h
                                have hpre : Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA
                                    = state.cnameChain.push cnBytes := by
                                  unfold Resolver.prependCnameLink
                                  simp only [hqaR, hextRR]
                                have hvtl : (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)).toList
                                    = (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname state.cnameChain).toList
                                      ++ [VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn] := by
                                  rw [hpre]
                                  exact cnameChaseVisited_push quL.qname state.cnameChain hprC
                                have hvis : ∀ nm ∈ tgt :: (q.qname :: nseen),
                                    ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)).toList,
                                    αName b = some nm ∧ b = VeriDNS.Impl.DomainName.labelsToWireFormatGo nm
                                      ∧ (∀ x ∈ nm, x.size ≤ 63) := by
                                  intro nm hnm
                                  rcases List.mem_cons.mp hnm with rfl | hnm
                                  · refine ⟨target, ?_, hαtgt, htB, hnaval0⟩
                                    rw [hvtl]
                                    refine List.mem_append_right _ ?_
                                    rw [show VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn
                                      = rrCn.rdata from rfl, hrdT]
                                    exact List.mem_singleton.mpr rfl
                                  · obtain ⟨b, hb, hf⟩ := hCCM' nm hnm
                                    refine ⟨b, ?_, hf⟩
                                    rw [hvtl]
                                    exact List.mem_append_left _ hb
                                have hTvis : ∃ b ∈ (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                    (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)).toList,
                                    VeriDNS.Impl.DomainName.nameEqCI b target = true := by
                                  refine ⟨VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn, ?_, ?_⟩
                                  · rw [hvtl]
                                    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                                  · rw [show VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rrCn
                                      = rrCn.rdata from rfl, hrdT]
                                    exact VeriDNS.Proof.NameTree.nameEqCI_refl target

                                have htcF0 : (respA.header.tc == 1) = false := by
                                  by_cases htcT : (respA.header.tc == 1) = true
                                  · exfalso
                                    obtain ⟨stT, hART, -, -⟩ := afterResume_cname_truncated
                                      { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                      entry.name respA target (by exact hstep) hcnT htcT
                                    rw [hART] at heqC
                                    exact Server.IoStep.noConfusion heqC
                                  · rw [Bool.not_eq_true] at htcT; exact htcT
                                obtain ⟨hnrev0, sname', chain', hla0, hcache0, hsname0, hnow0, hchain0, hstepC0, hlq0, hsbelt0, hslistD0⟩ :=
                                  afterResume_cname_continue_inv
                                    { state with resources := { state.resources with
                                        slist := state.resources.slist.markQueried entry.name } }
                                    entry.name respA target q₀L quL state'' hstep hcnT hq0 hqu0 htcF0 (by exact hTvis) heqC
                                have hnrev : ((Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord)
                                    ((state.lastQuery.bind (fun q0 => q0.question[0]?)).elim state.resources.sname (fun qu => qu.qname))
                                    state.cnameChain).any (fun v => VeriDNS.Impl.DomainName.nameEqCI v target)) = false := by
                                  exact hnrev0
                                have hla : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
                                    (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                                    quL.qtype quL.qclass state.now 8 target
                                    (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
                                    (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                      (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
                                    = .miss sname' chain' := by exact hla0
                                have hcache'' : state''.resources.cache
                                    = (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                      (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                      (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
                                      (Server.roundTouches (Server.dropIfBizarre
                                        { state with resources := { state.resources with
                                          slist := state.resources.slist.markQueried entry.name } }
                                        entry.name respA) respA) state.now := by exact hcache0
                                have hsname'' : state''.resources.sname = sname' := hsname0
                                have hnow'' : state''.now = state.now := by exact hnow0
                                have hchain'' : state''.cnameChain = chain' := hchain0
                                have hstepC'' : state''.currentStep = VeriDNS.Spec.AlgorithmStep.sendQueries := hstepC0
                                have hlq'' : state''.lastQuery = state.lastQuery := by exact hlq0
                                have hsbelt'' : state''.resources.sbelt = state.resources.sbelt := by exact hsbelt0
                                have hfresh : tgt ∉ q.qname :: nseen :=
                                  cname_target_fresh state q nseen target tgt hCCM htB hnaval0 hnrev

                                have hvalW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                    (Resolver.echoedQname respA) respA.answer).toList,
                                    ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                    (αRR rr).isSome = true := by
                                  intro b hb rr hpr
                                  obtain ⟨rr', hpr', hα'⟩ := hvalidAns b (cnameRaws_toList_sub hb)
                                  rw [hpr'] at hpr
                                  injection hpr with hrr
                                  subst hrr
                                  cases hα : αRR rr' with
                                  | none => exact absurd hα hα'
                                  | some r => rfl
                                have hnoW : ∀ b ∈ (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord)
                                    (Resolver.echoedQname respA) respA.answer).toList,
                                    ∀ rr, VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
                                    (state.now + rr.ttl.toNat.toUInt32).toNat = state.now.toNat + rr.ttl.toNat := by
                                  intro b hb rr hpr
                                  have hb' : b ∈ respS.answer := by
                                    rw [← hrespAeq]
                                    exact Array.mem_def.mpr (cnameRaws_toList_sub hb)
                                  have httl := VeriDNS.Proof.TtlCap.sanitizeTtlsCap_limit_ttls resp0 respS hsani b
                                    (Or.inl (Or.inl hb')) rr hpr
                                  exact uint32_add_ttl_toNat state.now rr.ttl.toNat httl hclock
                                have hwfW : CacheWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now) state.now := by
                                  refine CacheWf_cacheUnlessTruncated _ _ _ _ _ hCacheWf ?_ ?_
                                  · unfold Resolver.credAnswer
                                    by_cases ha' : (respA.header.aa == 1) = true
                                    · rw [if_pos ha']; exact Or.inl rfl
                                    · rw [if_neg ha']; exact Or.inr (Or.inr (Or.inl rfl))
                                  · intro raw hraw rr hp
                                    exact parseRaw_entry_canonical _ state.now hp (normRaws_hval hvalW raw hraw rr hp) (normRaws_hno hnoW raw hraw rr hp)
                                have hCnW : CacheCnameCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now) := by
                                  refine CacheCnameCanon_cacheUnlessTruncated _ _ _ _ _ hCnCanon ?_
                                  intro raw hraw rr hp htype
                                  exact canonicalRR_cnameRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                have hNsW : CacheNsCanon (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now) := by
                                  refine CacheNsCanon_cacheUnlessTruncated _ _ _ _ _ hNsCanon ?_
                                  intro raw hraw rr hp htype
                                  exact canonicalRR_nsRdata_canonical (hcanonAns raw (cnameRaws_toList_sub hraw)) hp htype
                                have hNsDW : CacheNsDistinct (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now) :=
                                  CacheNsDistinct_cacheUnlessTruncated _ _ _ _ _ hNsDistinct
                                have hOEW : VeriDNS.Proof.NameTree.OneExpiryPerKey (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now) :=
                                  VeriDNS.Proof.NameTree.oneExpiry_cacheUnlessTruncated hOE _ _ _ _
                                have hwfrrW : ∀ e ∈ (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now).records,
                                    VeriDNS.Proof.NameTree.WfRR e.rr :=
                                  wfrrAll_cacheUnlessTruncated hwfrr _ _ _ _
                                have hnegwfW : CacheNegWf (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
                                    state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now) quL.qclass :=
                                  CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf quL ⟨q₀L, hq0, hqu0⟩)

                                have hpeel := localAnswer_chase_peel net ns ra ednsBuf rttOf
                                  (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now)
                                  (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                    (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                    (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                  quL.qtype quL.qclass state.now q t [] quL.qname ht hqq htne hqmL.2
                                  (MatchMaxEquiv.refl _) hwfW hCnW hwfrrW hnegwfW 8 target tgt
                                  (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA)
                                  (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) quL.qname
                                    (Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord) state.cnameChain respA))
                                  (q.qname :: nseen) (.miss sname' chain') hla hαtgt htB hnaval0 hnalen0 rfl hvis
                                obtain ⟨links, nF, nseenF, hchainF, hnF, hnFcan, hnFval, hlenF, hvisF, hmissF, hnmissF, -, hcont⟩ := hpeel
                                by_cases htcF : (respA.header.tc == 1) = false
                                ·

                                  have hbnd : CacheRefines
                                      (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
                                        (Server.roundTouches (Server.dropIfBizarre
                                          { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA) respA) state.now))
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now)) :=
                                    αCache_boundLru_refines _ _ _ hwfrrW

                                  have hsn'' : αName state''.resources.sname = some nF := by
                                    rw [hsname'']; exact hnF
                                  have hsnameCanon'' : state''.resources.sname
                                      = VeriDNS.Impl.DomainName.labelsToWireFormatGo nF := by
                                    rw [hsname'']; exact hnFcan
                                  have htm'' : αTime state''.now = now := by rw [hnow'']; exact htm
                                  have hclock'' : state''.now.toNat + 604800 < 2 ^ 32 := by rw [hnow'']; exact hclock
                                  have hCacheWf'' : CacheWf state''.resources.cache state''.now := by
                                    rw [hcache'', hnow'']
                                    exact CacheWf_boundLru _ _ _ state.now hwfW
                                  have hNsCanon'' : CacheNsCanon state''.resources.cache := by
                                    rw [hcache'']
                                    exact CacheNsCanon_boundLru _ _ _ hNsW
                                  have hCnCanon'' : CacheCnameCanon state''.resources.cache := by
                                    rw [hcache'']
                                    exact CacheCnameCanon_boundLru _ _ _ hCnW
                                  have hwfrr'' : ∀ e ∈ state''.resources.cache.records, VeriDNS.Proof.NameTree.WfRR e.rr := by
                                    rw [hcache'']
                                    exact wfrrAll_boundLru _ _ hwfrrW
                                  have hNegWf'' : ∀ qu2 : VeriDNS.Spec.Question,
                                      (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                      CacheNegWf state''.resources.cache qu2.qclass := by
                                    intro qu2 hqu2
                                    rw [hcache'']
                                    exact CacheNegWf_boundLru _ _
                                      (CacheNegWf_cacheUnlessTruncated _ _ _ _ _ (hNegWf qu2 (by rw [← hlq'']; exact hqu2)))
                                  have hNsDistinct'' : CacheNsDistinct state''.resources.cache := by
                                    rw [hcache'']
                                    exact CacheNsDistinct_boundLru _ _ _ hNsDW
                                  have hOE'' : VeriDNS.Proof.NameTree.OneExpiryPerKey state''.resources.cache := by
                                    rw [hcache'']
                                    exact VeriDNS.Proof.NameTree.oneExpiry_boundLru _ _ hOEW
                                  have hCap'' : state''.resources.cache.records.size ≤ DnsCache.capacity := by
                                    rw [hcache'']
                                    exact VeriDNS.Proof.Cache.boundLru_bounded _ _ _
                                  have hmiss'' : (αCache state''.resources.cache).hit now { q with qname := nF } = [] := by
                                    rw [hcache'', ← htm]
                                    exact (hbnd.writeRefines (αTime state.now)).hit_nil (Nat.le_refl _) hmissF
                                  have hnmiss'' : (αCache state''.resources.cache).negHit now { q with qname := nF } = false := by
                                    rw [hcache'', ← htm]
                                    exact (hbnd.2.1 _ _).trans hnmissF
                                  have hqm'' : ∀ qu2 : VeriDNS.Spec.Question,
                                      (∃ q₀, state''.lastQuery = some q₀ ∧ q₀.question[0]? = some qu2) →
                                      αQType qu2.qtype = some q.qtype ∧ αClass qu2.qclass = some q.qclass := by
                                    rw [hlq'']
                                    exact hqm
                                  have hCCM'' : CnameChainModels state'' { q with qname := nF } nseenF := by
                                    unfold CnameChainModels
                                    have hanchor'' : ((state''.lastQuery.bind (fun q0 => q0.question[0]?)).elim
                                        state''.resources.sname (fun qu => qu.qname)) = quL.qname := by
                                      rw [hlq'', hq0]
                                      show (q₀L.question[0]?).elim state''.resources.sname (fun qu => qu.qname) = quL.qname
                                      rw [hqu0]
                                      rfl
                                    rw [hanchor'', hchain'']
                                    exact hvisF
                                  have hqvalid'' : ∀ x ∈ nF, 0 < x.size ∧ x.size ≤ 63 :=
                                    fun x hx => αName_labels_valid hnF x hx
                                  have hGlBelt'' : GluelessProv state''.resources.sbelt := by
                                    rw [hsbelt'']; exact hGlBelt

                                  have hGlProv'' : GluelessProv state''.resources.slist := by
                                    rcases hslistD0 with h | ⟨nsNames, mc, hwC, heq⟩ | h
                                    · rw [h]; exact GluelessProv_default
                                    · rw [heq]
                                      exact GluelessProv_fromNsWithGlueAll_of_canonical _ _ _
                                        (walkNs_names_canonical _ state.now hNsW 128 sname' nsNames mc (by exact hwC))
                                    · rw [h]; exact hGlBelt
                                  obtain ⟨s, v, cM, hrec, -, hrc', hans', hrest⟩ := IH ml (by omega) { q with qname := nF } depth f _ state''
                                    (αCache state''.resources.cache) _ w' now nseenF []
                                    state''.resources.slist.matchCount resp cout
                                    (by exact ⟨MatchMaxEquiv.refl _, hsn'', htm'', hwm⟩) (by exact hwmTcp) hCacheWf'' hNsCanon'' hCnCanon'' hwfrr'' hNegWf'' hNsDistinct'' hOE'' hCap''
                                    hmiss'' hnmiss'' (by intro b hb; simp at hb) rfl
                                    hGlProv'' hGlBelt''
                                    hqm'' (by exact hrd) (by exact hqstar) (by exact hqin) hclock'' hsnameCanon'' (by exact hlenF) (by exact hqvalid'') hCCM''
                                    (by
                                      rw [hchain'', hnow'']
                                      refine localAnswer_chain_answerWriteWf hwfW hNsW hCnW hwfrrW
                                        (congrArg chainOf hla) ?_
                                      rw [show Resolver.prependCnameLink (RR := VeriDNS.Spec.ResourceRecord)
                                          state.cnameChain respA = state.cnameChain.push cnBytes from by
                                        simp only [Resolver.prependCnameLink, hqaR, hextRR]]
                                      exact answerWriteWf_push hAW
                                        (fun rr hp => answerWriteWf_of_wire hsani hrespAeq hclock hvalidAns
                                          hcanonAns cnBytes hcnMem rr hp))
                                    hstepC'' hrun
                                  rw [hlq'', hnow''] at hrest

                                  have hrecK : HasVerdictAt net ns ra ednsBuf rttOf now nseenF []
                                      (αCache ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now).boundLru
                                        (Server.roundTouches (Server.dropIfBizarre
                                          { state with resources := { state.resources with
                                            slist := state.resources.slist.markQueried entry.name } }
                                          entry.name respA) respA) state.now))
                                      s { q with qname := nF } v cM := by
                                    rw [← hcache'']
                                    exact hrec
                                  rw [show αTime state.now = now from htm] at hcont
                                  obtain ⟨cOut, hcOut, -, ftr, rpath, tEnd2, respSub, hres, hagr⟩ :=
                                    hcont _ hbnd v s cM hrecK { v with answer := links ++ v.answer } rfl rfl
                                  have hcf0 := cname_link_write_WriteRefines_echo state.resources.cache respA qaR state.resources.sname
                                    q.qname state.now hqaR (question_from_decode hdec hsani (acceptResponse_some_eq haccR) hqaR)
                                    hqaCI hsn htcF hCacheWf hOE (normRaws_hval hvalW) (normRaws_hno hnoW) (rrsOf_RRCanonMappable hvalW)
                                    ({ aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                       authority := [], additional := [], ra := false, tc := false } : Response) c rfl rfl hmme
                                  rw [show state.now.toNat = now from htm] at hcf0
                                  have hrcOut : (αResp resp).rcode = v.rcode := hrc'
                                  have hansOut : (αResp resp).answer
                                      = αSection state.cnameChain ++ (cn :: (links ++ v.answer)) := by
                                    rw [hans', hchain'', hchainF,
                                      αSection_prependCnameLink state.cnameChain respA qaR cnBytes rrCn cn hqaR hextRR hprC hαcn]
                                    simp [List.append_assoc]
                                  have hclose : HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c
                                      (byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                        :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)))
                                      q { v with answer := cn :: (links ++ v.answer) } cM →
                                      ∃ slist v' coutM, HasVerdictAt net ns ra ednsBuf rttOf now nseen seen c slist q v' coutM
                                        ∧ (modelSlistOf state.resources.slist).Subperm slist
                                        ∧ (αResp resp).rcode = v'.rcode
                                        ∧ (αResp resp).answer = αSection state.cnameChain ++ v'.answer
                                        ∧ CacheRefines (αCache cout) coutM
                                        ∧ WorldModels net ns ra ednsBuf now w'
                                        ∧ CacheWf cout state.now
                                        ∧ CacheNsCanon cout
                                        ∧ CacheCnameCanon cout
                                        ∧ (∀ e ∈ cout.records, VeriDNS.Proof.NameTree.WfRR e.rr)
                                        ∧ (∀ qu : VeriDNS.Spec.Question,
                                            (∃ q₀, state.lastQuery = some q₀ ∧ q₀.question[0]? = some qu) →
                                            CacheNegWf cout qu.qclass)
                                        ∧ CacheNsDistinct cout
                                        ∧ VeriDNS.Proof.NameTree.OneExpiryPerKey cout
                                        ∧ cout.records.size ≤ DnsCache.capacity
                                        ∧ AnswerWriteWf resp.answer state.now := by
                                    intro hv
                                    exact ⟨byteAddrToModel (Server.ipv4ToAddr ipAddr)
                                        :: (modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr)),
                                      { v with answer := cn :: (links ++ v.answer) }, cM, hv,
                                      hpermAns.symm.subperm, hrcOut, hansOut, hrest⟩
                                  rcases hwmApp with ⟨srv, tr, ref, hfind, hans, hragA, hreachA, hfit, hisref, hcnbi, hcncorr,
                                    hvalid2, hvalidAuth2, hcut2, hnstail2⟩ |
                                    ⟨origin, reply0, srcPort0, htransS, haccS, hragS, hclsLink, htcRS, _hauthS0, hvldS, hvldAS, hrefImplS⟩
                                  ·
                                    have habs : c.absorb now q.qname
                                        (({ aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                            authority := [], additional := [], ra := false, tc := false } : Response).cnameOwned q.qname)
                                        = c.absorb now q.qname (ref.cnameOwned q.qname) :=
                                      absorb_resp_congr _ _ _ (by simpa using hnstail2.2.2.2.2.1)
                                        (by simp only [Response.cnameOwned_answer]; rw [hcncorr]) rfl rfl
                                    exact hclose (cname_classifier_bridge_at net ns ra ednsBuf rttOf
                                      (byteAddrToModel (Server.ipv4ToAddr ipAddr))
                                      ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                      srv tr ref cn tgt (w.ids w.idCtr).toNat 0 c s ftr rpath tEnd2 cM respSub
                                      hmiss hnmiss hfind hans hreachA (VeriDNS.Proof.WorldNetwork.reach_self net ns ra) hfit
                                      (by rw [← hcncorr]; exact hcnRR) hqt hcnrd hfresh (Nat.le_refl now)
                                      (hnstail2.2.2.2.2.2.2.symm.trans htcF)
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                      (by rw [← habs]; exact hcf0)
                                      cOut (hcOut.writeRefines now) hres
                                      { v with answer := cn :: (links ++ v.answer) }
                                      ⟨hagr.1, List.Perm.cons cn hagr.2⟩)
                                  ·
                                    have hreach : linkReach net ns ra origin = true := by
                                      cases htransS with
                                      | deliver hro hrr0 => exact hro
                                    exact hclose (trustedCname_hasVerdictAt net ns ra ednsBuf rttOf
                                      (byteAddrToModel (Server.ipv4ToAddr ipAddr)) origin
                                      ((modelSlistOf state.resources.slist).erase (byteAddrToModel (Server.ipv4ToAddr ipAddr))) q
                                      cn tgt (w.ids w.idCtr).toNat 0 c s ftr rpath tEnd2 cM respSub hmiss hnmiss
                                      (replyDatagram (queryDatagram (w.ids w.idCtr).toNat ra
                                          (byteAddrToModel (Server.ipv4ToAddr ipAddr)) 0 ednsBuf q)
                                        { aa := (respA.header.aa == 1), rcode := RCode.noError, answer := αSection respA.answer,
                                          authority := [], additional := [], ra := false, tc := false })
                                      (Transit.deliver _ _ _ hreach (VeriDNS.Proof.WorldNetwork.reach_self net ns ra))
                                      (accepts_reply _ _ _ _ _ _ _)
                                      hcnRR hqt hcnrd hfresh (Nat.le_refl now) rfl
                                      (αCache (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord) state.resources.cache respA
                                        (Resolver.cnameRaws (RR := VeriDNS.Spec.ResourceRecord) (Resolver.echoedQname respA) respA.answer)
                                        (Resolver.credAnswer (respA.header.aa == 1)) state.now))
                                      hcf0
                                      cOut (hcOut.writeRefines now) hres
                                      { v with answer := cn :: (links ++ v.answer) }
                                      ⟨hagr.1, List.Perm.cons cn hagr.2⟩)
                                ·

                                  exact absurd htcF0 htcF
