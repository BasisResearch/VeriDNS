import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.RRType
import VeriDNS.Proof.ResourceRecord
import VeriDNS.Spec.NetworkSemantics
import VeriDNS.RFC.Check

rfc_proves VeriDNS.Proof.ResourceRecord.decode_encode [1035][553:565]
rfc_proves VeriDNS.Proof.ResourceRecord.decode_encode [1035][588:597]
rfc_proves VeriDNS.Proof.ResourceRecord.decode_encode [1035][609:616]

rfc_out_of_scope [1035][664:672]
rfc_out_of_scope [1035][680:728]

rfc_out_of_scope [1035][787:803]
rfc_out_of_scope [1035][808:824]
rfc_out_of_scope [1035][826:896]

rfc_proves VeriDNS.Spec.Net.referralAdditional [1035][957:972]

rfc_out_of_scope [1035][975:990]
rfc_out_of_scope [1035][993:1008]

rfc_out_of_scope [1035][1082:1093]
rfc_out_of_scope [1035][1125:1143]
rfc_out_of_scope [1035][1152:1176]

rfc_out_of_scope [1035][1818:1828]
rfc_out_of_scope [1035][1833:1858]
rfc_out_of_scope [1035][1862:1867]
rfc_out_of_scope [1035][1871:1888]
rfc_out_of_scope [1035][1895:1935]

rfc_proves VeriDNS.Spec.Net.Zone.WF [1035][1938:2016]

rfc_out_of_scope [1035][186:202]
