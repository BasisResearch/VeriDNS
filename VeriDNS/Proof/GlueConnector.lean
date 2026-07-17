import VeriDNS.Proof.AnswerTerminal
open VeriDNS.Proof.Refinement VeriDNS.Spec.Net VeriDNS.Impl
open VeriDNS.Spec (RRParse ResourceRecord)
set_option maxHeartbeats 1000000

namespace VeriDNS.Proof.Refinement

theorem glue_per_elem (cut n : ByteArray) (cutN h : Name) (b : ByteArray)
    (hcut : αName cut = some cutN) (hn : αName n = some h)
    (hncanon : n = DomainName.labelsToWireFormatGo h) (hnval : ∀ x ∈ h, x.size ≤ 63)
    (hwf : ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none) :
    ((if (match RRParse.parseRaw (RR := ResourceRecord) b with
            | some rr => Resolver.isAncestorB cut (RRParse.rrName (RR := ResourceRecord) rr)
            | none => false)
        then (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
              | .ok (rr, _) =>
                if rr.type == BitVec.ofNat 16 1 && rr.rdata.size == 4 then
                  some (rr.name,
                    (rr.rdata.data[0]!.toBitVec.setWidth 32 <<< 24) |||
                    (rr.rdata.data[1]!.toBitVec.setWidth 32 <<< 16) |||
                    (rr.rdata.data[2]!.toBitVec.setWidth 32 <<< 8) |||
                    rr.rdata.data[3]!.toBitVec.setWidth 32)
                else none
              | .error _ => none)
        else none) : Option (ByteArray × BitVec 32)).bind
        (fun gp => Option.map (fun a => byteAddrToModel (Server.ipv4ToAddr a))
          (if VeriDNS.Impl.DomainName.nameEqCI gp.1 n then some gp.2 else none))
      = (if ((match RRParse.parseRaw (RR := ResourceRecord) b with
              | some rr => αRR rr | none => none).any
            (fun (r : RR) => (match r.rdata with | RData.a _ => true | _ => false)
              && nameEq h r.owner && isAncestor cutN r.owner))
        then (match RRParse.parseRaw (RR := ResourceRecord) b with
              | some rr => αRR rr | none => none).bind
            (fun (r : RR) => match r.rdata with | RData.a a => some a.toDotted | _ => none)
        else none) := by
  cases hpr : RRParse.parseRaw (RR := ResourceRecord) b with
  | none => simp [hpr]
  | some rr =>
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hwf rr hpr)
    obtain ⟨pos', hdec⟩ : ∃ pos', DnsParser.run VeriDNS.Impl.ResourceRecord.decode b = .ok (rr, pos') := by
      have hm : (match DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
          | .ok (rr, _) => some rr | .error _ => none) = some rr := hpr
      cases hdc : DnsParser.run VeriDNS.Impl.ResourceRecord.decode b with
      | error e => simp [hdc] at hm
      | ok p =>
        obtain ⟨rr', pos''⟩ := p
        simp only [hdc] at hm
        obtain rfl : rr' = rr := Option.some.inj hm
        exact ⟨pos'', rfl⟩
    have hown : αName rr.name = some r.owner := (αRR_fields rr r hr).1
    have hbail : Resolver.isAncestorB cut rr.name = isAncestor cutN r.owner :=
      isAncestorB_eq cut rr.name cutN r.owner hcut hown

    have hαrd : αRData rr.type rr.rdata = some r.rdata := by
      unfold αRR at hr; split at hr
      · next o rd c ho hrd hc => rw [show r = _ from (Option.some.inj hr).symm]; exact hrd
      · simp at hr
    have hAbridge : (rr.type == BitVec.ofNat 16 1 && rr.rdata.size == 4)
        = (match r.rdata with | RData.a _ => true | _ => false) := by
      unfold αRData at hαrd
      split at hαrd
      · next h1 =>
        rw [Option.map_eq_some_iff] at hαrd
        obtain ⟨a, ha, hrd⟩ := hαrd
        have hsize : rr.rdata.size = 4 := by
          by_contra hc; unfold αIPv4 at ha; rw [if_neg hc] at ha; exact absurd ha (by simp)
        have htype : rr.type = BitVec.ofNat 16 1 := by apply BitVec.eq_of_toNat_eq; rw [h1]; rfl
        rw [← hrd]; simp [htype, hsize]
      · next h2 =>
        rw [Option.map_eq_some_iff] at hαrd; obtain ⟨x, _, hrd⟩ := hαrd
        have hne : rr.type ≠ BitVec.ofNat 16 1 := by intro hc; rw [hc] at h2; simp at h2
        rw [← hrd]; simp [hne]
      · next h5 =>
        rw [Option.map_eq_some_iff] at hαrd; obtain ⟨x, _, hrd⟩ := hαrd
        have hne : rr.type ≠ BitVec.ofNat 16 1 := by intro hc; rw [hc] at h5; simp at h5
        rw [← hrd]; simp [hne]
      · next h6 =>
        have hne : rr.type ≠ BitVec.ofNat 16 1 := by intro hc; rw [hc] at h6; simp at h6
        obtain ⟨soa, rest, mn, rn, -, -, -, hrd⟩ := αSoa_inv hαrd
        rw [hrd]; simp [hne]
      · next h12 =>
        rw [Option.map_eq_some_iff] at hαrd; obtain ⟨x, _, hrd⟩ := hαrd
        have hne : rr.type ≠ BitVec.ofNat 16 1 := by intro hc; rw [hc] at h12; simp at h12
        rw [← hrd]; simp [hne]
      ·
        next h1 _ _ _ _ =>
        rw [Option.map_eq_some_iff] at hαrd; obtain ⟨t, -, hrd⟩ := hαrd
        have hbeq : (rr.type == BitVec.ofNat 16 1) = false := by
          cases hb : rr.type == BitVec.ofNat 16 1
          · rfl
          · exact absurd (show rr.type.toNat = 1 by rw [eq_of_beq hb]; rfl) h1
        rw [← hrd]; simp [hbeq]
    simp only [hpr, hr, Option.any_some, Option.bind_some, RRParse.rrName, hdec, hbail, hAbridge]
    obtain ⟨na, hαna, hcanon, hvna⟩ := parseRaw_name_canonical hpr
    obtain rfl : na = r.owner := by rw [hown] at hαna; exact (Option.some.inj hαna).symm
    have hnameEq : DomainName.nameEqCI rr.name n = nameEq h r.owner := by
      rw [nameEqCI_eq_nameEq hcanon hvna hown hncanon hnval hn, nameEq_symm]
    by_cases hanc : isAncestor cutN r.owner = true
    · cases hrd2 : r.rdata with
      | a addr =>
        have hαiv : αIPv4 rr.rdata = some addr := by
          have hh := hαrd; rw [hrd2] at hh; unfold αRData at hh; split at hh
          · rw [Option.map_eq_some_iff] at hh; obtain ⟨a', ha', heq⟩ := hh
            obtain rfl : a' = addr := by injection heq
            exact ha'
          all_goals first
            | (rw [Option.map_eq_some_iff] at hh; obtain ⟨_, _, heq⟩ := hh; exact absurd heq (by simp))
            | exact absurd (αSoa_rtype hh) (by simp [VeriDNS.Spec.Net.RData.rtype])
            | exact absurd hh (by simp)
        have haddr := extractGlue_addr_αIPv4 rr.rdata addr hαiv
        simp only [hanc, hrd2, hnameEq, haddr]
        by_cases hnm : nameEq h r.owner = true <;> simp [hnm, haddr, hnameEq]
      | ns x => simp [hanc, hrd2]
      | cname x => simp [hanc, hrd2]
      | soa a b c d e f g => simp [hanc, hrd2]
      | mx a b => simp [hanc, hrd2]
      | hinfo a b => simp [hanc, hrd2]
      | ptr x => simp [hanc, hrd2]
      | generic t d => simp [hanc, hrd2]
    · rw [Bool.not_eq_true] at hanc; simp [hanc]

theorem glue_per_host_eq (respA : VeriDNS.Spec.Format) (cut n : ByteArray) (h : Name)
    (hcut : αName cut = some (referralCut (αResp respA)))
    (hn : αName n = some h)
    (hncanon : n = DomainName.labelsToWireFormatGo h) (hnval : ∀ x ∈ h, x.size ≤ 63)
    (hwf : ∀ b ∈ respA.additional.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none) :
    ((Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := ResourceRecord) cut respA.additional)).findSome?
        (fun gp => if DomainName.nameEqCI gp.1 n then some gp.2 else none)).map
        (fun a => byteAddrToModel (Server.ipv4ToAddr a))
      = (αName n).bind (fun h => ((αResp respA).additional.find?
          (fun (r : RR) => (match r.rdata with | RData.a _ => true | _ => false)
            && nameEq h r.owner && isAncestor (referralCut (αResp respA)) r.owner)).bind
          (fun (r : RR) => match r.rdata with | RData.a a => some a.toDotted | _ => none)) := by
  rw [← Array.findSome?_toList, findSome?_map_comm, extractGlueRecords_bailiwickRaws_fused,
      Array.toList_filterMap, findSome?_filterMap_list, hn]
  show _ = ((αSection respA.additional).find? _).bind _
  rw [αSection, List.find?_filterMap, Option.bind_assoc,
      find?_bind_eq_findSome? _ _ _ (by
        intro b _ hq
        rw [Option.any_eq_true] at hq
        obtain ⟨r, hpα, hpred⟩ := hq
        rw [hpα, Option.bind_some]
        rw [Bool.and_eq_true, Bool.and_eq_true] at hpred
        revert hpred; cases r.rdata <;> simp)]
  apply findSome?_congr_pred
  intro b hb
  exact glue_per_elem cut n (referralCut (αResp respA)) h b hcut hn hncanon hnval
    (fun rr hpr => hwf b hb rr hpr)

theorem referralCutRaw_canonical (authority : Array ByteArray)
    (hns : Resolver.hasRRTypeIn (RR := ResourceRecord) authority 2 = true) :
    ∃ nc, αName (Resolver.referralCutRaw (RR := ResourceRecord) authority) = some nc
      ∧ Resolver.referralCutRaw (RR := ResourceRecord) authority
          = DomainName.labelsToWireFormatGo nc
      ∧ (∀ x ∈ nc, x.size ≤ 63) := by
  unfold Resolver.referralCutRaw
  split
  · rename_i owner heq
    obtain ⟨b, hb, hfb⟩ := Array.exists_of_findSome?_eq_some heq
    cases hpr : RRParse.parseRaw (RR := ResourceRecord) b with
    | none =>
      rw [hpr] at hfb
      dsimp only [] at hfb
      exact absurd hfb (by simp)
    | some rr =>
      rw [hpr] at hfb
      dsimp only [] at hfb
      by_cases hty : (RRParse.rrType (RR := ResourceRecord) rr == (2 : BitVec 16)) = true
      · rw [if_pos hty] at hfb
        obtain rfl := Option.some.inj hfb
        exact parseRaw_name_canonical hpr
      · rw [if_neg hty] at hfb
        exact absurd hfb (by simp)
  · rename_i heq
    exfalso
    unfold Resolver.hasRRTypeIn at hns
    rw [Array.any_eq_true] at hns
    obtain ⟨i, hi, hp⟩ := hns
    rw [← Array.findSome?_toList, List.findSome?_eq_none_iff] at heq
    have hnone := heq authority[i] (Array.mem_def.mp (Array.getElem_mem hi))
    cases hpr : RRParse.parseRaw (RR := ResourceRecord) authority[i] with
    | none => rw [hpr] at hp; exact absurd hp (by simp)
    | some rr =>
      rw [hpr] at hp hnone
      dsimp only [] at hnone
      rw [if_pos hp] at hnone
      exact absurd hnone (by simp)

/-- The cut-filtered NS extraction abstracts to the model's `cutServers`:
the impl's referral slist hosts are EXACTLY the NS hosts owned at the
delegation cut (W1 glue fix connector). -/
theorem extractNsNames_ownerRaws_cutServers_αResp (respA : VeriDNS.Spec.Format)
    (hcut : αName (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority)
      = some (referralCut (αResp respA)))
    (hvalidAuth : ∀ b ∈ respA.authority.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none)
    (hns : Resolver.hasRRTypeIn (RR := ResourceRecord) respA.authority 2 = true) :
    (Resolver.extractNsNames (RR := ResourceRecord)
      (Resolver.ownerRaws (RR := ResourceRecord)
        (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority)
        respA.authority)).toList.filterMap αName
      = cutServers (αResp respA) := by
  obtain ⟨nc, hαc, hccanon, hcval⟩ := referralCutRaw_canonical respA.authority hns
  obtain rfl : nc = referralCut (αResp respA) := by
    rw [hαc] at hcut
    exact Option.some.inj hcut
  have hvalid' : ∀ b ∈ (Resolver.ownerRaws (RR := ResourceRecord)
      (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority)
        respA.authority).toList,
      ∀ rr, RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none :=
    fun b hb rr hpr => hvalidAuth b
      (Resolver.ownerRaws_subset (RR := ResourceRecord) _ respA.authority hb) rr hpr
  rw [extractNsNames_referredServers _ hvalid',
    αSection_ownerRaws_eq _ _ respA.authority hcut hccanon hcval]
  unfold cutServers
  rw [(αResp_components respA).2.2.1]
  apply filterMap_congr_mem
  intro r _
  cases r.rdata <;> rfl

theorem referral_slist_eq (respA : VeriDNS.Spec.Format) (mc : Nat)
    (hcut : αName (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority)
      = some (referralCut (αResp respA)))
    (hvalidAuth : ∀ b ∈ respA.authority.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none)
    (hvalidAdd : ∀ b ∈ respA.additional.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none)
    (hnscanon : ∀ b ∈ respA.authority.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → (rr.type == BitVec.ofNat 16 2) = true →
      ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63))
    (hns : Resolver.hasRRTypeIn (RR := ResourceRecord) respA.authority 2 = true) :
    modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlue
        (Resolver.extractNsNames (RR := ResourceRecord) (Resolver.ownerRaws (RR := ResourceRecord) (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority) respA.authority))
        (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := ResourceRecord)
          (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority) respA.additional)) mc)
      = glueAddresses (αResp respA) := by
  apply modelSlistOf_referral_eq_glueAddresses
  · exact extractNsNames_ownerRaws_cutServers_αResp respA hcut hvalidAuth hns
  · intro n hnmem
    obtain ⟨raw, hraw, rr, hpr, htype, hrd⟩ :=
      mem_extractNsNames _ n (Array.mem_def.mpr hnmem)
    have hrawAuth : raw ∈ respA.authority.toList :=
      Resolver.ownerRaws_subset (RR := ResourceRecord) _ respA.authority
        (Array.mem_def.mp hraw)
    obtain ⟨na, hαna, hcanon, hnaval⟩ := hnscanon raw hrawAuth rr hpr htype
    have hrd' : rr.rdata = n := hrd
    rw [hrd'] at hαna hcanon
    exact glue_per_host_eq respA
      (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority) n na hcut hαna hcanon
      hnaval hvalidAdd

theorem glueAddresses_subperm_transient (respA : VeriDNS.Spec.Format) (mc : Nat)
    (hcut : αName (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority)
      = some (referralCut (αResp respA)))
    (hvalidAuth : ∀ b ∈ respA.authority.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none)
    (hvalidAdd : ∀ b ∈ respA.additional.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → αRR rr ≠ none)
    (hnscanon : ∀ b ∈ respA.authority.toList, ∀ rr,
      RRParse.parseRaw (RR := ResourceRecord) b = some rr → (rr.type == BitVec.ofNat 16 2) = true →
      ∃ na, αName rr.rdata = some na ∧ rr.rdata = DomainName.labelsToWireFormatGo na
        ∧ (∀ x ∈ na, x.size ≤ 63))
    (hns : Resolver.hasRRTypeIn (RR := ResourceRecord) respA.authority 2 = true) :
    (glueAddresses (αResp respA)).Subperm
      (modelSlistOf (VeriDNS.Impl.SList.DnsSList.fromNsWithGlueAll
        (Resolver.extractNsNames (RR := ResourceRecord) (Resolver.ownerRaws (RR := ResourceRecord) (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority) respA.authority))
        (Resolver.extractGlueRecords (Resolver.bailiwickRaws (RR := ResourceRecord)
          (Resolver.referralCutRaw (RR := ResourceRecord) respA.authority) respA.additional)) mc)) := by
  rw [← referral_slist_eq respA mc hcut hvalidAuth hvalidAdd hnscanon hns]
  exact modelSlistOf_fromNsWithGlue_subperm_all _ _ mc mc

end VeriDNS.Proof.Refinement
