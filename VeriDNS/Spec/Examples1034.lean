import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check
import VeriDNS.Spec.NameTree
import VeriDNS.Spec.RRType
import VeriDNS.Spec.ResourceRecord

namespace VeriDNS.Spec

inductive ExRcode where
  | noError : ExRcode
  | nameError : ExRcode
  deriving Repr, BEq, Inhabited

structure ExRR where
  owner : List ByteArray
  type : RRType
  ttl : Nat
  rdata : ByteArray
  deriving Inhabited

structure ExResponse where
  qname : List ByteArray
  qtype : RRType
  rcode : ExRcode
  aa : Bool
  answer : List ExRR
  authority : List ExRR
  additional : List ExRR
  deriving Inhabited

def exLabel (s : String) : ByteArray := s.toUTF8

def exName (labels : List String) : List ByteArray := labels.map exLabel

def exSriNic : List ByteArray := exName ["SRI-NIC", "ARPA"]
def exAcc : List ByteArray := exName ["ACC", "ARPA"]
def exCIsiEdu : List ByteArray := exName ["C", "ISI", "EDU"]
def exAIsiEdu : List ByteArray := exName ["A", "ISI", "EDU"]
def exVaxaIsiEdu : List ByteArray := exName ["VAXA", "ISI", "EDU"]
def exVeneraIsiEdu : List ByteArray := exName ["VENERA", "ISI", "EDU"]
def exIsiEdu : List ByteArray := exName ["ISI", "EDU"]
def exUscIsic : List ByteArray := exName ["USC-ISIC", "ARPA"]
def exSirNic : List ByteArray := exName ["SIR-NIC", "ARPA"]
def exMil : List ByteArray := exName ["MIL"]
def exBrlMil : List ByteArray := exName ["BRL", "MIL"]
def exRoot : List ByteArray := []
def exAccPtrName : List ByteArray := exName ["65", "0", "6", "26", "IN-ADDR", "ARPA"]

theorem ex_scenario_servers :
    isSubdomain exCIsiEdu exIsiEdu
  ∧ isSubdomain exAIsiEdu exIsiEdu
  ∧ isSubdomain exSriNic (exName ["ARPA"])
  ∧ isSubdomain exMil exRoot
  ∧ isSubdomain exIsiEdu (exName ["EDU"]) := by
  refine ⟨⟨[exLabel "C"], rfl⟩, ⟨[exLabel "A"], rfl⟩, ⟨[exLabel "SRI-NIC"], rfl⟩,
    ⟨exMil, rfl⟩, ⟨[exLabel "ISI"], rfl⟩⟩

def exRootSoa : ExRR :=
  { owner := exRoot, type := RRType.soa, ttl := 86400, rdata := exLabel "SRI-NIC.ARPA." }

def exRootNs : List ExRR :=
  [ { owner := exRoot, type := RRType.ns, ttl := 86400, rdata := exLabel "A.ISI.EDU." },
    { owner := exRoot, type := RRType.ns, ttl := 86400, rdata := exLabel "C.ISI.EDU." },
    { owner := exRoot, type := RRType.ns, ttl := 86400, rdata := exLabel "SRI-NIC.ARPA." } ]

def exMilNs : List ExRR :=
  [ { owner := exMil, type := RRType.ns, ttl := 86400, rdata := exLabel "SRI-NIC.ARPA." },
    { owner := exMil, type := RRType.ns, ttl := 86400, rdata := exLabel "A.ISI.EDU." } ]

def exSriNicRecords : List ExRR :=
  [ { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "26.0.0.73" },
    { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "10.0.0.51" },
    { owner := exSriNic, type := RRType.mx, ttl := 86400, rdata := exLabel "0 SRI-NIC.ARPA." },
    { owner := exSriNic, type := RRType.hinfo, ttl := 86400, rdata := exLabel "DEC-2060 TOPS20" } ]

def exUscIsicCname : ExRR :=
  { owner := exUscIsic, type := RRType.cname, ttl := 86400, rdata := exLabel "C.ISI.EDU." }

theorem ex_cisiedu_zone_contents :
    exRootSoa.type = RRType.soa
  ∧ exRootSoa.owner = exRoot
  ∧ exRootNs.length = 3
  ∧ (exRootNs.all (fun r => r.type == RRType.ns)) = true
  ∧ exMilNs.length = 2
  ∧ (exMilNs.all (fun r => r.owner == exMil && r.type == RRType.ns)) = true
  ∧ exUscIsicCname.type = RRType.cname
  ∧ (exSriNicRecords.filter (fun r => r.type == RRType.a)).length = 2
  ∧ (exSriNicRecords.filter (fun r => r.type == RRType.mx)).length = 1
  ∧ (exSriNicRecords.filter (fun r => r.type == RRType.hinfo)).length = 1 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl⟩ <;> rfl

def ExResponse.questionMatches (r : ExResponse) (qn : List ByteArray) (qt : RRType) : Prop :=
  r.qname = qn ∧ r.qtype = qt

def ex_621_response : ExResponse :=
  { qname := exSriNic, qtype := RRType.a, rcode := ExRcode.noError, aa := true
    answer :=
      [ { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "26.0.0.73" },
        { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "10.0.0.51" } ]
    authority := [], additional := [] }

theorem ex_621_answer :
    ex_621_response.aa = true
  ∧ ex_621_response.rcode = ExRcode.noError
  ∧ ex_621_response.answer.length = 2
  ∧ (ex_621_response.answer.all (fun r => r.owner == exSriNic && r.type == RRType.a)) = true
  ∧ ex_621_response.authority = []
  ∧ ex_621_response.additional = []
  ∧ ex_621_response.questionMatches exSriNic RRType.a := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def ex_621_cached_response : ExResponse :=
  { qname := exSriNic, qtype := RRType.a, rcode := ExRcode.noError, aa := false
    answer :=
      [ { owner := exSriNic, type := RRType.a, ttl := 1777, rdata := exLabel "10.0.0.51" },
        { owner := exSriNic, type := RRType.a, ttl := 1777, rdata := exLabel "26.0.0.73" } ]
    authority := [], additional := [] }

theorem ex_621_cached :
    ex_621_cached_response.aa = false
  ∧ ex_621_response.aa = true
  ∧ ex_621_cached_response.answer.length = 2
  ∧ (ex_621_cached_response.answer.all (fun r => r.type == RRType.a)) = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

def ex_622_response : ExResponse :=
  { qname := exSriNic, qtype := RRType.a, rcode := ExRcode.noError, aa := true
    answer := exSriNicRecords, authority := [], additional := [] }

theorem ex_622_star_returns_all :
    ex_622_response.aa = true
  ∧ ex_622_response.answer.length = 4
  ∧ (ex_622_response.answer.filter (fun r => r.type == RRType.a)).length = 2
  ∧ (ex_622_response.answer.filter (fun r => r.type == RRType.mx)).length = 1
  ∧ (ex_622_response.answer.filter (fun r => r.type == RRType.hinfo)).length = 1
  ∧ ex_622_response.authority = [] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def ex_623_response : ExResponse :=
  { qname := exSriNic, qtype := RRType.mx, rcode := ExRcode.noError, aa := true
    answer := [ { owner := exSriNic, type := RRType.mx, ttl := 86400, rdata := exLabel "0 SRI-NIC.ARPA." } ]
    authority := []
    additional :=
      [ { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "26.0.0.73" },
        { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "10.0.0.51" } ] }

theorem ex_623_mx_with_additional :
    ex_623_response.aa = true
  ∧ ex_623_response.answer.length = 1
  ∧ (ex_623_response.answer.all (fun r => r.type == RRType.mx)) = true
  ∧ ex_623_response.additional.length = 2
  ∧ (ex_623_response.additional.all (fun r => r.owner == exSriNic && r.type == RRType.a)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

def ex_624_response : ExResponse :=
  { qname := exSriNic, qtype := RRType.ns, rcode := ExRcode.noError, aa := true
    answer := [], authority := [], additional := [] }

theorem ex_624_empty_but_authoritative :
    ex_624_response.aa = true
  ∧ ex_624_response.rcode = ExRcode.noError
  ∧ ex_624_response.answer = []
  ∧ ex_624_response.authority = []
  ∧ ex_624_response.additional = [] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

def ex_625_response : ExResponse :=
  { qname := exSirNic, qtype := RRType.a, rcode := ExRcode.nameError, aa := true
    answer := []
    authority := [ { owner := exRoot, type := RRType.soa, ttl := 86400, rdata := exLabel "SRI-NIC.ARPA." } ]
    additional := [] }

theorem ex_625_name_error :
    ex_625_response.rcode = ExRcode.nameError
  ∧ ex_625_response.aa = true
  ∧ ex_625_response.answer = []
  ∧ ex_625_response.authority.length = 1
  ∧ (ex_625_response.authority.all (fun r => r.type == RRType.soa)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

def ex_626_response : ExResponse :=
  { qname := exBrlMil, qtype := RRType.a, rcode := ExRcode.noError, aa := false
    answer := []
    authority :=
      [ { owner := exMil, type := RRType.ns, ttl := 86400, rdata := exLabel "SRI-NIC.ARPA." },
        { owner := exMil, type := RRType.ns, ttl := 86400, rdata := exLabel "A.ISI.EDU." } ]
    additional :=
      [ { owner := exAIsiEdu, type := RRType.a, ttl := 86400, rdata := exLabel "26.3.0.103" },
        { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "26.0.0.73" },
        { owner := exSriNic, type := RRType.a, ttl := 86400, rdata := exLabel "10.0.0.51" } ] }

theorem ex_626_referral :
    isSubdomain exBrlMil exMil
  ∧ ex_626_response.answer = []
  ∧ ex_626_response.aa = false
  ∧ ex_626_response.authority.length = 2
  ∧ (ex_626_response.authority.all (fun r => r.owner == exMil && r.type == RRType.ns)) = true
  ∧ ex_626_response.additional.length = 3
  ∧ (ex_626_response.additional.all (fun r => r.type == RRType.a)) = true := by
  refine ⟨⟨[exLabel "BRL"], rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

def ex_627_complete_response : ExResponse :=
  { qname := exUscIsic, qtype := RRType.a, rcode := ExRcode.noError, aa := true
    answer :=
      [ { owner := exUscIsic, type := RRType.cname, ttl := 86400, rdata := exLabel "C.ISI.EDU." },
        { owner := exCIsiEdu, type := RRType.a, ttl := 86400, rdata := exLabel "10.0.0.52" } ]
    authority := [], additional := [] }

def ex_627_referral_response : ExResponse :=
  { qname := exUscIsic, qtype := RRType.a, rcode := ExRcode.noError, aa := true
    answer := [ { owner := exUscIsic, type := RRType.cname, ttl := 86400, rdata := exLabel "C.ISI.EDU." } ]
    authority :=
      [ { owner := exIsiEdu, type := RRType.ns, ttl := 172800, rdata := exLabel "VAXA.ISI.EDU." },
        { owner := exIsiEdu, type := RRType.ns, ttl := 172800, rdata := exLabel "A.ISI.EDU." },
        { owner := exIsiEdu, type := RRType.ns, ttl := 172800, rdata := exLabel "VENERA.ISI.EDU." } ]
    additional :=
      [ { owner := exVaxaIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "10.2.0.27" },
        { owner := exVeneraIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "10.1.0.52" },
        { owner := exAIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "26.3.0.103" } ] }

theorem ex_627_cname_complete_and_referral :
    ex_627_complete_response.aa = true
  ∧ ex_627_complete_response.answer.length = 2
  ∧ ex_627_complete_response.answer.head!.type = RRType.cname
  ∧ (ex_627_complete_response.answer.getLast!).type = RRType.a
  ∧ ex_627_referral_response.answer.length = 1
  ∧ (ex_627_referral_response.answer.all (fun r => r.type == RRType.cname)) = true
  ∧ ex_627_referral_response.authority.length = 3
  ∧ (ex_627_referral_response.authority.all (fun r => r.owner == exIsiEdu && r.type == RRType.ns)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def ex_628_response : ExResponse :=
  { qname := exUscIsic, qtype := RRType.cname, rcode := ExRcode.noError, aa := true
    answer := [ { owner := exUscIsic, type := RRType.cname, ttl := 86400, rdata := exLabel "C.ISI.EDU." } ]
    authority := [], additional := [] }

theorem ex_628_cname_self_answers :
    ex_628_response.aa = true
  ∧ ex_628_response.answer.length = 1
  ∧ (ex_628_response.answer.all (fun r => r.type == RRType.cname)) = true
  ∧ ex_628_response.additional = [] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

def ex_631_referral_response : ExResponse :=
  { qname := exIsiEdu, qtype := RRType.mx, rcode := ExRcode.noError, aa := false
    answer := []
    authority :=
      [ { owner := exIsiEdu, type := RRType.ns, ttl := 172800, rdata := exLabel "VAXA.ISI.EDU." },
        { owner := exIsiEdu, type := RRType.ns, ttl := 172800, rdata := exLabel "A.ISI.EDU." },
        { owner := exIsiEdu, type := RRType.ns, ttl := 172800, rdata := exLabel "VENERA.ISI.EDU." } ]
    additional :=
      [ { owner := exVaxaIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "10.2.0.27" },
        { owner := exVeneraIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "10.1.0.52" },
        { owner := exAIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "26.3.0.103" } ] }

def ex_631_answer_response : ExResponse :=
  { qname := exIsiEdu, qtype := RRType.mx, rcode := ExRcode.noError, aa := true
    answer :=
      [ { owner := exIsiEdu, type := RRType.mx, ttl := 172800, rdata := exLabel "10 VENERA.ISI.EDU." },
        { owner := exIsiEdu, type := RRType.mx, ttl := 172800, rdata := exLabel "20 VAXA.ISI.EDU." } ]
    authority := []
    additional :=
      [ { owner := exVaxaIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "10.2.0.27" },
        { owner := exVeneraIsiEdu, type := RRType.a, ttl := 172800, rdata := exLabel "10.1.0.52" } ] }

theorem ex_631_resolve_mx :
    ex_631_referral_response.answer = []
  ∧ ex_631_referral_response.aa = false
  ∧ ex_631_referral_response.authority.length = 3
  ∧ (ex_631_referral_response.authority.all (fun r => r.owner == exIsiEdu && r.type == RRType.ns)) = true
  ∧ ex_631_answer_response.aa = true
  ∧ ex_631_answer_response.answer.length = 2
  ∧ (ex_631_answer_response.answer.all (fun r => r.owner == exIsiEdu && r.type == RRType.mx)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def ex_632_response : ExResponse :=
  { qname := exAccPtrName, qtype := RRType.ptr, rcode := ExRcode.noError, aa := true
    answer := [ { owner := exAccPtrName, type := RRType.ptr, ttl := 86400, rdata := exLabel "ACC.ARPA." } ]
    authority := [], additional := [] }

theorem ex_632_reverse_ptr :
    ex_632_response.qtype = RRType.ptr
  ∧ ex_632_response.aa = true
  ∧ ex_632_response.answer.length = 1
  ∧ (ex_632_response.answer.all (fun r => r.owner == exAccPtrName && r.type == RRType.ptr)) = true
  ∧ ex_632_response.authority = [] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ex_633_poneria_under_isiedu :
    isSubdomain (exName ["poneria", "ISI", "EDU"]) exIsiEdu := by
  exact ⟨[exLabel "poneria"], rfl⟩

end VeriDNS.Spec

rfc_proves VeriDNS.Spec.ex_scenario_servers [1034][1977:2026]

rfc_proves VeriDNS.Spec.ex_cisiedu_zone_contents [1034][2030:2154]

rfc_proves VeriDNS.Spec.ex_621_answer [1034][2157:2224]
rfc_proves VeriDNS.Spec.ex_621_cached [1034][2239:2262]

rfc_proves VeriDNS.Spec.ex_622_star_returns_all [1034][2264:2351]

rfc_proves VeriDNS.Spec.ex_623_mx_with_additional [1034][2353:2376]

rfc_proves VeriDNS.Spec.ex_624_empty_but_authoritative [1034][2377:2397]

rfc_proves VeriDNS.Spec.ex_625_name_error [1034][2398:2430]

rfc_proves VeriDNS.Spec.ex_626_referral [1034][2431:2455]

rfc_proves VeriDNS.Spec.ex_627_cname_complete_and_referral [1034][2465:2543]

rfc_proves VeriDNS.Spec.ex_628_cname_self_answers [1034][2544:2564]

rfc_proves VeriDNS.Spec.ex_631_resolve_mx [1034][2565:2707]

rfc_proves VeriDNS.Spec.ex_632_reverse_ptr [1034][2708:2755]

rfc_proves VeriDNS.Spec.ex_633_poneria_under_isiedu [1034][2757:2775]
