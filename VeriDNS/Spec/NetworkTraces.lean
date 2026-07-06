import VeriDNS.Spec.NetworkModel
import VeriDNS.RFC.Check

namespace VeriDNS.Spec.Net

open VeriDNS.Spec (RRType Node)

def rr (owner : List String) (ttl : Nat) (rd : RData) : RR :=
  { owner := N owner, ttl := ttl, rdata := rd }

def rootZone : Zone :=
  { apex := N []
    records :=
      [ rr [] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                          870611 1800 300 604800 86400),
        rr [] 86400 (.ns (N ["A","ISI","EDU"])),
        rr [] 86400 (.ns (N ["C","ISI","EDU"])),
        rr [] 86400 (.ns (N ["SRI-NIC","ARPA"])),
        rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
        rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩),
        rr ["SRI-NIC","ARPA"] 86400 (.mx 0 (N ["SRI-NIC","ARPA"])),
        rr ["SRI-NIC","ARPA"] 86400 (.hinfo "DEC-2060" "TOPS20"),
        rr ["ACC","ARPA"] 86400 (.a ⟨26, 6, 0, 65⟩),
        rr ["ACC","ARPA"] 86400 (.hinfo "PDP-11/70" "UNIX"),
        rr ["ACC","ARPA"] 86400 (.mx 10 (N ["ACC","ARPA"])),
        rr ["USC-ISIC","ARPA"] 86400 (.cname (N ["C","ISI","EDU"])),
        rr ["73","0","0","26","IN-ADDR","ARPA"] 86400 (.ptr (N ["SRI-NIC","ARPA"])),
        rr ["65","0","6","26","IN-ADDR","ARPA"] 86400 (.ptr (N ["ACC","ARPA"])),
        rr ["51","0","0","10","IN-ADDR","ARPA"] 86400 (.ptr (N ["SRI-NIC","ARPA"])),
        rr ["52","0","0","10","IN-ADDR","ARPA"] 86400 (.ptr (N ["C","ISI","EDU"])),
        rr ["103","0","3","26","IN-ADDR","ARPA"] 86400 (.ptr (N ["A","ISI","EDU"])),
        rr ["A","ISI","EDU"] 86400 (.a ⟨26, 3, 0, 103⟩),
        rr ["C","ISI","EDU"] 86400 (.a ⟨10, 0, 0, 52⟩) ]
    delegations :=
      [ { subapex := N ["MIL"]
          nsSet := [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                     rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ] },
        { subapex := N ["EDU"]
          nsSet := [ rr ["EDU"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                     rr ["EDU"] 86400 (.ns (N ["C","ISI","EDU"])) ] } ] }
rfc_proves VeriDNS.Spec.Net.rootZone [1034][2030:2154]

def eduZone : Zone :=
  { apex := N ["EDU"]
    records :=
      [ rr ["EDU"] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                              870729 1800 300 604800 86400),
        rr ["EDU"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
        rr ["EDU"] 86400 (.ns (N ["C","ISI","EDU"])),
        rr ["VAXA","ISI","EDU"] 172800 (.a ⟨10, 2, 0, 27⟩),
        rr ["VAXA","ISI","EDU"] 172800 (.a ⟨128, 9, 0, 33⟩),
        rr ["VENERA","ISI","EDU"] 172800 (.a ⟨10, 1, 0, 52⟩),
        rr ["VENERA","ISI","EDU"] 172800 (.a ⟨128, 9, 0, 32⟩),
        rr ["A","ISI","EDU"] 172800 (.a ⟨26, 3, 0, 103⟩) ]
    delegations :=
      [ { subapex := N ["ISI","EDU"]
          nsSet := [ rr ["ISI","EDU"] 172800 (.ns (N ["VAXA","ISI","EDU"])),
                     rr ["ISI","EDU"] 172800 (.ns (N ["A","ISI","EDU"])),
                     rr ["ISI","EDU"] 172800 (.ns (N ["VENERA","ISI","EDU"])) ] } ] }
rfc_proves VeriDNS.Spec.Net.eduZone [1034][2030:2154]

def isiEduZone : Zone :=
  { apex := N ["ISI","EDU"]
    records :=
      [ rr ["ISI","EDU"] 172800 (.soa (N ["VAXA","ISI","EDU"]) (N ["HOSTMASTER","ISI","EDU"])
                                     870611 1800 300 604800 86400),
        rr ["ISI","EDU"] 172800 (.ns (N ["VAXA","ISI","EDU"])),
        rr ["ISI","EDU"] 172800 (.ns (N ["A","ISI","EDU"])),
        rr ["ISI","EDU"] 172800 (.ns (N ["VENERA","ISI","EDU"])),
        rr ["ISI","EDU"] 172800 (.mx 10 (N ["VENERA","ISI","EDU"])),
        rr ["ISI","EDU"] 172800 (.mx 20 (N ["VAXA","ISI","EDU"])),
        rr ["C","ISI","EDU"] 86400 (.a ⟨10, 0, 0, 52⟩),
        rr ["A","ISI","EDU"] 172800 (.a ⟨26, 3, 0, 103⟩),
        rr ["VAXA","ISI","EDU"] 172800 (.a ⟨10, 2, 0, 27⟩),
        rr ["VAXA","ISI","EDU"] 172800 (.a ⟨128, 9, 0, 33⟩),
        rr ["VENERA","ISI","EDU"] 172800 (.a ⟨10, 1, 0, 52⟩),
        rr ["VENERA","ISI","EDU"] 172800 (.a ⟨128, 9, 0, 32⟩) ]
    delegations := [] }
rfc_proves VeriDNS.Spec.Net.isiEduZone [1034][2030:2154]

def milZone : Zone :=
  { apex := N ["MIL"]
    records :=
      [ rr ["MIL"] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                              870611 1800 300 604800 86400),
        rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
        rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ]
    delegations := [] }
rfc_proves VeriDNS.Spec.Net.milZone [1034][2030:2154]

def cISI : Server := { name := N ["C","ISI","EDU"], zones := [rootZone, eduZone], cache := [], addr := "10.0.0.52" }
rfc_proves VeriDNS.Spec.Net.cISI [1034][2020:2026]

def aISI : Server := { name := N ["A","ISI","EDU"], zones := [rootZone, isiEduZone, milZone], cache := [], addr := "26.3.0.103" }
rfc_proves VeriDNS.Spec.Net.aISI [1034][2020:2026]

def sriNic : Server :=
  { name := N ["SRI-NIC","ARPA"], zones := [rootZone, eduZone, milZone], cache := [], addr := "26.0.0.73" }
rfc_proves VeriDNS.Spec.Net.sriNic [1034][2020:2026]

def scenario : Network := { servers := [cISI, aISI, sriNic] }
rfc_proves VeriDNS.Spec.Net.scenario [1034][1977:2026]

theorem usc_isic_forces_cname :
    (recordsAt rootZone (N ["USC-ISIC","ARPA"])).filter
        (fun r => (QType.rr RRType.a).covers r.rdata.rtype && r.cls == RRClass.«in») = [] :=
  cnameAlone_forces_cname (c := rr ["USC-ISIC","ARPA"] 86400 (.cname (N ["C","ISI","EDU"])))
    (by decide) rfl (by decide)
rfc_proves VeriDNS.Spec.Net.usc_isic_forces_cname [1034][2465:2543]

theorem tree_holds_sri_nic_records :
    treeRecordsAt (treeOf rootZone) (N ["SRI-NIC","ARPA"])
      = [ rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
          rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩),
          rr ["SRI-NIC","ARPA"] 86400 (.mx 0 (N ["SRI-NIC","ARPA"])),
          rr ["SRI-NIC","ARPA"] 86400 (.hinfo "DEC-2060" "TOPS20") ] := by
  rw [treeRecordsAt_treeOf]; rfl
rfc_proves VeriDNS.Spec.Net.tree_holds_sri_nic_records [1034][1300:1310]

theorem cISI_authoritative_sriNic :
    AuthoritativeFor scenario RRClass.«in» (N ["C","ISI","EDU"]) (N ["SRI-NIC","ARPA"]) := by
  refine AuthoritativeFor.mk _ _ cISI rootZone ?_ rfl rfl rfl
  simp [scenario]
rfc_proves VeriDNS.Spec.Net.cISI_authoritative_sriNic [1034][1977:2026]

theorem cISI_delegates_brlMil :
    DelegatesTo scenario RRClass.«in» (N ["C","ISI","EDU"]) (N ["BRL","MIL"]) (N ["MIL"]) := by
  refine DelegatesTo.mk _ _ cISI rootZone
    { subapex := N ["MIL"],
      nsSet := [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                 rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ] }
    ?_ rfl rfl ?_ (by decide)
  · simp [scenario]
  · simp [rootZone, rr]
rfc_proves VeriDNS.Spec.Net.cISI_delegates_brlMil [1034][1977:2026]

theorem ex_621_answer :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["SRI-NIC","ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.matchNode (N ["SRI-NIC","ARPA"]),
              Step.copyAnswer, Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = [ rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
                        rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩) ]
      ∧ resp.authority = []
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.answer _ rootZone _ rfl rfl rfl (Or.inl rfl) (by decide),
    rfl, rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_621_answer [1034][2157:2224]

theorem ex_624_nodata :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["SRI-NIC","ARPA"], .rr .ns, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.noData]
      ∧ resp.aa = true
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = []
      ∧ resp.authority = [ rr [] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                                            870611 1800 300 604800 86400) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.noData _ rootZone _ rfl rfl rfl (Or.inl rfl) (by decide) rfl
    (Or.inl (by decide)), rfl, rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_624_nodata [2308][274:376]

def type1Zone : Zone :=
  { apex := N ["T"], negCacheNS := true
    records :=
      [ rr ["T"] 100 (.soa (N ["T"]) (N ["T"]) 1 1 1 1 1),
        rr ["T"] 100 (.ns (N ["T"])),
        rr ["H","T"] 100 (.a ⟨1, 1, 1, 1⟩) ]
    delegations := [] }

def type1Server : Server :=
  { name := N ["T"], zones := [type1Zone], cache := [], addr := "9.9.9.9" }

theorem ex_nodata_type1 :
    ∃ tr resp, ServerReplies type1Server 0 ⟨N ["H","T"], .rr .mx, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N ["T"]), Step.noData]
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = []
      ∧ resp.authority = [ rr ["T"] 100 (.soa (N ["T"]) (N ["T"]) 1 1 1 1 1),
                           rr ["T"] 100 (.ns (N ["T"])) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.noData _ type1Zone _ rfl rfl rfl (Or.inl rfl) (by decide) rfl
    (Or.inl (by decide)), rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_nodata_type1 [2308][274:376]

theorem ex_nxdomain_type1 :
    ∃ tr resp, ServerReplies type1Server 0 ⟨N ["NOPE","T"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N ["T"]), Step.nameError]
      ∧ resp.rcode = RCode.nameError
      ∧ resp.answer = []
      ∧ resp.authority = [ rr ["T"] 100 (.soa (N ["T"]) (N ["T"]) 1 1 1 1 1),
                           rr ["T"] 100 (.ns (N ["T"])) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.nameError _ type1Zone rfl rfl rfl rfl (by decide),
    rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_nxdomain_type1 [2308][129:204]

theorem ex_625_name_error :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["SIR-NIC","ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.nameError]
      ∧ resp.aa = true
      ∧ resp.rcode = RCode.nameError
      ∧ resp.answer = []
      ∧ resp.authority = [ rr [] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                                            870611 1800 300 604800 86400) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.nameError _ rootZone rfl rfl rfl rfl (by decide),
    rfl, rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_625_name_error [1034][2398:2430]

def rootNegEntry : NegCacheEntry :=
  { qname := N ["SIR-NIC","ARPA"],
    soa := rr [] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                            870611 1800 300 604800 86400),
    insertedAt := 0 }

theorem neg_caching_scenario :
    negTTL rootZone = some 86400
  ∧ rootNegEntry.ttl = some 86400
  ∧ rootNegEntry.fresh 86399 = true
  ∧ rootNegEntry.fresh 86400 = false
  ∧ ∃ tr resp, ServerReplies cISI 0 ⟨N ["SIR-NIC","ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.nameError]
      ∧ resp.negTTL = some 86400 := by
  refine ⟨by decide, by decide, by decide, by decide, _, _,
    ServerAnswers.nameError _ rootZone rfl rfl rfl rfl (by decide), rfl, by decide⟩
rfc_proves VeriDNS.Spec.Net.neg_caching_scenario [2308][404:475]

theorem ex_arpa_empty_non_terminal :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.noData]
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = []
      ∧ resp.authority = [ rr [] 86400 (.soa (N ["SRI-NIC","ARPA"]) (N ["HOSTMASTER","SRI-NIC","ARPA"])
                                            870611 1800 300 604800 86400) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.noData _ rootZone _ rfl rfl rfl (Or.inl rfl) rfl rfl
    (Or.inr (by decide)), rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_arpa_empty_non_terminal [2308][274:376]

def wildcardZone : Zone :=
  { apex := N ["X"]
    records :=
      [ rr ["X"] 100 (.soa (N ["X"]) (N ["X"]) 1 1 1 1 1),
        rr ["X"] 100 (.ns (N ["X"])),
        rr ["*","X"] 100 (.a ⟨9, 9, 9, 9⟩),
        rr ["B","X"] 100 (.a ⟨1, 1, 1, 1⟩) ]
    delegations := [] }

def wildcardServer : Server :=
  { name := N ["X"], zones := [wildcardZone], cache := [], addr := "5.5.5.5" }

theorem ex_wildcard_applies :
    ∃ tr resp, ServerReplies wildcardServer 0 ⟨N ["Z","X"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N ["X"]), Step.wildcard, Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["Z","X"] 100 (.a ⟨9, 9, 9, 9⟩) ] := by
  refine ⟨_, _, ServerAnswers.wildcard _ wildcardZone _ rfl rfl rfl (by decide) rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_wildcard_applies [1034][1370:1385]

theorem ex_wildcard_inhibited :
    ∃ tr resp, ServerReplies wildcardServer 0 ⟨N ["A","B","X"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N ["X"]), Step.nameError]
      ∧ resp.rcode = RCode.nameError
      ∧ resp.answer = []
      ∧ resp.authority = [ rr ["X"] 100 (.soa (N ["X"]) (N ["X"]) 1 1 1 1 1) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.nameError _ wildcardZone rfl rfl rfl rfl (by decide),
    rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_wildcard_inhibited [1034][1404:1414]

def entWildcardZone : Zone :=
  { apex := N ["X"]
    records :=
      [ rr ["X"] 100 (.soa (N ["X"]) (N ["X"]) 1 1 1 1 1),
        rr ["X"] 100 (.ns (N ["X"])),
        rr ["*","X"] 100 (.a ⟨9, 9, 9, 9⟩),
        rr ["a","b","X"] 100 (.a ⟨1, 1, 1, 1⟩) ]
    delegations := [] }

def entWildcardServer : Server :=
  { name := N ["X"], zones := [entWildcardZone], cache := [], addr := "5.5.5.5" }

theorem ex_ent_under_wildcard :
    ∃ tr resp, ServerReplies entWildcardServer 0 ⟨N ["b","X"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N ["X"]), Step.noData]
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = [] := by
  refine ⟨_, _, ServerAnswers.noData _ entWildcardZone _ rfl rfl rfl (Or.inl rfl) rfl rfl
    (Or.inr (by decide)), rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_ent_under_wildcard [1034][1404:1414]

def typedWildcardZone : Zone :=
  { apex := N ["X"]
    records :=
      [ rr ["X"] 100 (.soa (N ["X"]) (N ["X"]) 1 1 1 1 1),
        rr ["X"] 100 (.ns (N ["X"])),
        rr ["*","X"] 100 (.a ⟨9, 9, 9, 9⟩),
        rr ["B","X"] 100 (.mx 10 (N ["X"])) ]
    delegations := [] }

def typedWildcardServer : Server :=
  { name := N ["X"], zones := [typedWildcardZone], cache := [], addr := "5.5.5.5" }

theorem ex_typed_under_wildcard :
    ∃ tr resp, ServerReplies typedWildcardServer 0 ⟨N ["B","X"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N ["X"]), Step.noData]
      ∧ resp.rcode = RCode.noError
      ∧ resp.answer = [] := by
  refine ⟨_, _, ServerAnswers.noData _ typedWildcardZone _ rfl rfl rfl (Or.inl rfl) rfl rfl
    (Or.inl (by decide)), rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_typed_under_wildcard [1034][1404:1414]

theorem ex_626_referral :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["BRL","MIL"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.referral (N ["MIL"]), Step.addAdditional]
      ∧ resp.aa = false
      ∧ resp.answer = []
      ∧ resp.authority = [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                           rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ]
      ∧ resp.additional = [ rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
                            rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩),
                            rr ["A","ISI","EDU"] 86400 (.a ⟨26, 3, 0, 103⟩) ] := by
  refine ⟨_, _, ServerAnswers.referral _ rootZone _ rfl rfl rfl, rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_626_referral [1034][2431:2455]

def step4Server : Server :=
  { name := N ["s"], addr := "1.1.1.1"
    zones :=
      [ { apex := N []
          records := [ rr [] 100 (.soa (N ["s"]) (N ["s"]) 1 1 1 1 1) ]
          delegations :=
            [ { subapex := N ["SUB"], nsSet := [ rr ["SUB"] 100 (.ns (N ["NS1","SUB"])) ] } ] } ]
    cache := [ { rr := rr ["NS1","SUB"] 100 (.a ⟨9, 9, 9, 9⟩), insertedAt := 0 } ] }

theorem ex_step4_glue_from_cache :
    ∃ tr resp, ServerReplies step4Server 50 ⟨N ["X","SUB"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.referral (N ["SUB"]), Step.addAdditional]
      ∧ resp.authority = [ rr ["SUB"] 100 (.ns (N ["NS1","SUB"])) ]
      ∧ resp.additional = [ rr ["NS1","SUB"] 50 (.a ⟨9, 9, 9, 9⟩) ] := by
  refine ⟨_, _, ServerAnswers.referral _ _ _ rfl rfl rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_step4_glue_from_cache [1034][1354:1364]

def referCacheServer : Server :=
  { name := N ["s"], addr := "1.1.1.1"
    zones :=
      [ { apex := N []
          records := [ rr [] 100 (.soa (N ["s"]) (N ["s"]) 1 1 1 1 1) ]
          delegations :=
            [ { subapex := N ["SUB"], nsSet := [ rr ["SUB"] 100 (.ns (N ["NS1","SUB"])) ] } ] } ]
    cache := [ { rr := rr ["X","SUB"] 100 (.a ⟨5, 5, 5, 5⟩), insertedAt := 0 } ] }

theorem ex_referral_cache_answer :
    ∃ tr resp, ServerReplies referCacheServer 50 ⟨N ["X","SUB"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.referral (N ["SUB"]), Step.copyAnswer, Step.addAdditional]
      ∧ resp.answer = [ rr ["X","SUB"] 50 (.a ⟨5, 5, 5, 5⟩) ]
      ∧ resp.authority = [ rr ["SUB"] 100 (.ns (N ["NS1","SUB"])) ] := by
  refine ⟨_, _, ServerAnswers.referralCacheAnswer _ _ _ [ rr ["X","SUB"] 50 (.a ⟨5, 5, 5, 5⟩) ]
    rfl rfl rfl (List.cons_ne_nil _ _), rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_referral_cache_answer [1034][1354:1364]

theorem ex_622_star :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["SRI-NIC","ARPA"], .star, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.matchNode (N ["SRI-NIC","ARPA"]),
              Step.copyAnswer, Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
                        rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩),
                        rr ["SRI-NIC","ARPA"] 86400 (.mx 0 (N ["SRI-NIC","ARPA"])),
                        rr ["SRI-NIC","ARPA"] 86400 (.hinfo "DEC-2060" "TOPS20") ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.answer _ rootZone _ rfl rfl rfl (Or.inl rfl) (by decide),
    rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_622_star [1034][2264:2351]

theorem ex_623_mx :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["SRI-NIC","ARPA"], .rr .mx, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.matchNode (N ["SRI-NIC","ARPA"]),
              Step.copyAnswer, Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["SRI-NIC","ARPA"] 86400 (.mx 0 (N ["SRI-NIC","ARPA"])) ]
      ∧ resp.additional = [ rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
                            rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩) ] := by
  refine ⟨_, _, ServerAnswers.answer _ rootZone _ rfl rfl rfl (Or.inl rfl) (by decide),
    rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_623_mx [1034][2353:2376]

theorem ex_628_cname_self :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["USC-ISIC","ARPA"], .rr .cname, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.matchNode (N ["USC-ISIC","ARPA"]),
              Step.copyAnswer, Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["USC-ISIC","ARPA"] 86400 (.cname (N ["C","ISI","EDU"])) ]
      ∧ resp.additional = [] := by
  refine ⟨_, _, ServerAnswers.answer _ rootZone _ rfl rfl rfl (Or.inr rfl) (by decide),
    rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_628_cname_self [1034][2544:2564]

theorem ex_627_cname_complete :
    ∃ tr resp, ServerReplies aISI 0 ⟨N ["USC-ISIC","ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.matchNode (N ["USC-ISIC","ARPA"]),
              Step.followCNAME (N ["C","ISI","EDU"]),
              Step.findZone (N ["ISI","EDU"]), Step.matchNode (N ["C","ISI","EDU"]),
              Step.copyAnswer, Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["USC-ISIC","ARPA"] 86400 (.cname (N ["C","ISI","EDU"])),
                        rr ["C","ISI","EDU"] 86400 (.a ⟨10, 0, 0, 52⟩) ]
      ∧ resp.authority = [] := by
  refine ⟨_, _,
    ServerAnswers.cname _ rootZone _ (N ["C","ISI","EDU"]) _ _ rfl rfl rfl rfl rfl (fun h => absurd (List.mem_singleton.mp h) (by decide))
      (ServerAnswers.answer _ isiEduZone _ rfl rfl rfl (Or.inl rfl) (by decide)),
    rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_627_cname_complete [1034][2465:2543]

theorem ex_627_cname_referral :
    ∃ tr resp, ServerReplies cISI 0 ⟨N ["USC-ISIC","ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.findZone (N []), Step.matchNode (N ["USC-ISIC","ARPA"]),
              Step.followCNAME (N ["C","ISI","EDU"]),
              Step.findZone (N ["EDU"]), Step.referral (N ["ISI","EDU"]), Step.addAdditional]
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["USC-ISIC","ARPA"] 86400 (.cname (N ["C","ISI","EDU"])) ]
      ∧ resp.authority = [ rr ["ISI","EDU"] 172800 (.ns (N ["VAXA","ISI","EDU"])),
                           rr ["ISI","EDU"] 172800 (.ns (N ["A","ISI","EDU"])),
                           rr ["ISI","EDU"] 172800 (.ns (N ["VENERA","ISI","EDU"])) ]
      ∧ resp.additional = [ rr ["VAXA","ISI","EDU"] 172800 (.a ⟨10, 2, 0, 27⟩),
                            rr ["VAXA","ISI","EDU"] 172800 (.a ⟨128, 9, 0, 33⟩),
                            rr ["A","ISI","EDU"] 172800 (.a ⟨26, 3, 0, 103⟩),
                            rr ["VENERA","ISI","EDU"] 172800 (.a ⟨10, 1, 0, 52⟩),
                            rr ["VENERA","ISI","EDU"] 172800 (.a ⟨128, 9, 0, 32⟩) ] := by
  refine ⟨_, _,
    ServerAnswers.cname _ rootZone _ (N ["C","ISI","EDU"]) _ _ rfl rfl rfl rfl rfl (fun h => absurd (List.mem_singleton.mp h) (by decide))
      (ServerAnswers.referral _ eduZone _ rfl rfl rfl),
    rfl, rfl, rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_627_cname_referral [1034][2465:2543]

theorem ex_621_cached :
    ∃ tr resp,
      ServerReplies { name := N ["X"], zones := [],
                      cache := [ { rr := rr ["SRI-NIC","ARPA"] 86400 (.a ⟨10, 0, 0, 51⟩),
                                   insertedAt := 0 },
                                 { rr := rr ["SRI-NIC","ARPA"] 86400 (.a ⟨26, 0, 0, 73⟩),
                                   insertedAt := 0 } ] } 84623
        ⟨N ["SRI-NIC","ARPA"], .rr .a, .«in», false⟩ tr resp
      ∧ tr = [Step.fromCache, Step.addAdditional]
      ∧ resp.aa = false
      ∧ resp.answer = [ rr ["SRI-NIC","ARPA"] 1777 (.a ⟨10, 0, 0, 51⟩),
                        rr ["SRI-NIC","ARPA"] 1777 (.a ⟨26, 0, 0, 73⟩) ] := by
  refine ⟨_, _, ServerAnswers.fromCache _ _ rfl rfl (Or.inl (by decide)), rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_621_cached [1034][2239:2262]

theorem mil_available_despite_failure :
    zoneAvailable scenario
      { status := fun n => if nameEq n (N ["SRI-NIC","ARPA"]) then Status.down else Status.up }
      (N ["MIL"]) = true := by decide
rfc_proves VeriDNS.Spec.Net.mil_available_despite_failure [1034][1012:1018]

theorem ex_failover_mil_ns :
    ∃ resp,
      ServerFailover scenario
        { status := fun n => if nameEq n (N ["SRI-NIC","ARPA"]) then Status.down else Status.up } 0
        [N ["SRI-NIC","ARPA"], N ["A","ISI","EDU"]] ⟨N ["MIL"], .rr .ns, .«in», false⟩ resp
      ∧ resp.aa = true
      ∧ resp.answer = [ rr ["MIL"] 86400 (.ns (N ["SRI-NIC","ARPA"])),
                        rr ["MIL"] 86400 (.ns (N ["A","ISI","EDU"])) ]
      ∧ resp.authority = [] := by
  refine ⟨_, ServerFailover.skipDown _ _ _ _ rfl
    (ServerFailover.here _ _ _ aISI _ _ rfl rfl
      (ServerAnswers.answer _ milZone _ rfl rfl rfl (Or.inl rfl) (by decide))),
    rfl, rfl, rfl⟩
rfc_proves VeriDNS.Spec.Net.ex_failover_mil_ns [1034][1986:2026]

theorem descend_push {R : Type} (lab : ByteArray) (rs : Array R) (cs : Array (Node R))
    (new : Node R) (l : ByteArray) (rest : List ByteArray) (r : Node R)
    (h : Node.descend (Node.mk lab rs cs) (l :: rest) = some r) :
    Node.descend (Node.mk lab rs (cs.push new)) (l :: rest) = some r := by
  simp only [Node.descend, Node.children, ← Array.find?_toList, Array.toList_push,
    List.find?_append] at h ⊢
  cases hc : List.find? (fun c => labelEq c.label l) cs.toList with
  | none => rw [hc] at h; simp at h
  | some c => rw [hc] at h; simpa using h

theorem growSection_preserves_lookup {R : Type} (lab : ByteArray) (rs : Array R)
    (cs : Array (Node R)) (new : Node R) (n : Name) (r : Node R)
    (hne : n ≠ []) (h : Node.lookupPath (Node.mk lab rs cs) n = some r) :
    Node.lookupPath (Node.mk lab rs (cs.push new)) n = some r := by
  have hrev : n.reverse ≠ [] := fun hr => hne (by simpa using congrArg List.reverse hr)
  obtain ⟨l, rest, hlr⟩ := List.exists_cons_of_ne_nil hrev
  simp only [Node.lookupPath, hlr] at h ⊢
  exact descend_push lab rs cs new l rest r h

theorem path_stable_under_growth (rs : Array Unit) (cs : Array (Node Unit)) (r : Node Unit)
    (h : Node.lookupPath (Node.mk (L "") rs cs) (N ["MIT", "EDU"]) = some r) :
    Node.lookupPath (Node.mk (L "") rs (cs.push (Node.mk (L "GOV") #[] #[]))) (N ["MIT", "EDU"]) = some r :=
  growSection_preserves_lookup (L "") rs cs (Node.mk (L "GOV") #[] #[]) (N ["MIT", "EDU"]) r
    (by decide) h
rfc_proves VeriDNS.Spec.Net.path_stable_under_growth [1034][1065:1073]

def fooServer : Server :=
  { name := N ["foo"], zones := [ { apex := N ["FOO"], records := [], delegations := [] } ],
    cache := [], addr := "2.2.2.2" }

theorem ex_coevolve_delegate :
    CoEvolves ⟨Node.mk (L "") #[] #[], scenario⟩
              ⟨Node.mk (L "") #[] (#[].push (Node.mk (L "FOO") #[] #[])),
               (scenario.modifyServer 0 (·.delegateAt 0 ⟨N ["FOO"], []⟩)).addServer fooServer⟩
  ∧ AuthoritativeFor
      ((scenario.modifyServer 0 (·.delegateAt 0 ⟨N ["FOO"], []⟩)).addServer fooServer)
      RRClass.«in» (N ["foo"]) (N ["FOO"]) := by
  refine ⟨CoEvolves.delegate _ _ _ _ _ _ _ _ _, ?_⟩
  exact CoEvolves.delegate_creates_authority scenario 0 0 ⟨N ["FOO"], []⟩ fooServer
    { apex := N ["FOO"], records := [], delegations := [] } rfl rfl
rfc_proves VeriDNS.Spec.Net.ex_coevolve_delegate [1034][1140:1166]

end VeriDNS.Spec.Net
