import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.RRType
import VeriDNS.Spec.Header
import VeriDNS.Spec.NetworkSemantics
import VeriDNS.Spec.AcceptanceRules
import VeriDNS.Proof.Cache
import VeriDNS.Proof.Server
import VeriDNS.RFC.Check

namespace VeriDNS.Spec


/--
5. Resource Record Sets

   Each DNS Resource Record (RR) has a label, class, type, and data.  It
   is meaningless for two records to ever have label, class, type and
   data all equal - servers should suppress such duplicates if
   encountered.  It is however possible for most record types to exist
   with the same label, class and type, but with different data.  Such a
   group of records is hereby defined to be a Resource Record Set
   (RRSet).
-/
@[blueprint "RRSet"]
structure RRSet where
  label : ByteArray
  «class» : BitVec 16
  type : BitVec 16
  ttls : List (BitVec 32)
  rdatas : List ByteArray

def RRSet.ttlsUniform (s : RRSet) : Prop := ∀ a ∈ s.ttls, ∀ b ∈ s.ttls, a = b

def RRSet.setAllTtls (s : RRSet) (t : BitVec 32) : RRSet :=
  { s with ttls := s.ttls.map (fun _ => t) }

theorem rrset_setAllTtls_uniform (s : RRSet) (t : BitVec 32) :
    (s.setAllTtls t).ttlsUniform := by
  simp only [RRSet.ttlsUniform, RRSet.setAllTtls, List.mem_map]
  rintro a ⟨_, _, rfl⟩ b ⟨_, _, rfl⟩
  rfl

theorem rrset_setAllTtls_preserves_records (s : RRSet) (t : BitVec 32) :
    (s.setAllTtls t).rdatas = s.rdatas ∧ (s.setAllTtls t).ttls.length = s.ttls.length := by
  refine ⟨rfl, ?_⟩
  simp [RRSet.setAllTtls]

end VeriDNS.Spec

rfc_proves VeriDNS.Spec.accept_requires_source_match [2181][131:148]
rfc_proves VeriDNS.Spec.accept_requires_source_match [2181][149:174]

rfc_out_of_scope [2181][175:184]

check_rfc_doc VeriDNS.Spec.RRSet [2181][186:194]

rfc_out_of_scope [2181][195:202]

rfc_proves VeriDNS.Spec.rrset_setAllTtls_uniform [2181][203:214]
rfc_proves VeriDNS.Spec.rrset_setAllTtls_uniform [2181][215:234]
rfc_proves VeriDNS.Spec.rrset_setAllTtls_preserves_records [2181][215:234]

rfc_out_of_scope [2181][295:312]

rfc_proves VeriDNS.Proof.Cache.store_never_combined [2181][313:342]

rfc_out_of_scope [2181][403:424]

rfc_out_of_scope [2181][425:435]

rfc_proves VeriDNS.Spec.Net.Zone.WF_deleg_below [2181][436:459]

rfc_proves VeriDNS.Spec.Net.Zone.WF [2181][460:478]

rfc_proves VeriDNS.Spec.Net.serverAnswers_nameError_carries_soa [2181][515:529]

rfc_out_of_scope [2181][530:539]

rfc_out_of_scope [2181][540:549]

rfc_out_of_scope [2181][550:568]

rfc_out_of_scope [2181][569:571]

rfc_proves VeriDNS.Proof.Server.sanitize_limit_ttls [2181][572:576]

rfc_proves VeriDNS.Spec.Net.truncateToCap_fits [2181][577:588]

rfc_out_of_scope [2181][589:593]

rfc_out_of_scope [2181][594:600]

rfc_proves VeriDNS.Spec.Net.cnameAlone_forces_cname [2181][601:628]

rfc_out_of_scope [2181][639:658]

rfc_out_of_scope [2181][659:678]

rfc_proves VeriDNS.Spec.Net.wf_glue_present [2181][679:694]

rfc_proves VeriDNS.Spec.Net.nameOk [2181][695:713]

rfc_out_of_scope [2181][714:727]

rfc_out_of_scope [2181][728:742]
