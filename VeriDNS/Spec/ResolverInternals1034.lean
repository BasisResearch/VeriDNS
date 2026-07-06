import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.NameTree
import VeriDNS.Spec.RRType
import VeriDNS.Spec.NetworkModel
import VeriDNS.Spec.NetworkSemantics
import VeriDNS.Spec.NetworkTraces
import VeriDNS.Proof.NameTree
import VeriDNS.Proof.Resolver
import VeriDNS.Proof.Cache
import VeriDNS.RFC.Check

/-!
RFC 1034 §4.3 / §5.2–5.3.3 resolver-internals prose coverage.

The genuine resolver algorithm is verified in `VeriDNS.Proof.NameTree.*`,
`VeriDNS.Proof.Resolver.*`, `VeriDNS.Proof.Cache.*` and `VeriDNS.Spec.Net.*`.
The links below remap each formalisable paragraph onto those real soundness
theorems; purely operational/administrative prose (recursive-mode negotiation,
secondary-server polling, AXFR zone transfer, error-combination API advice) is
marked out of scope.
-/

rfc_out_of_scope [1034][1194:1196]
rfc_out_of_scope [1034][1203:1204]
rfc_proves VeriDNS.Spec.Net.serverAnswers_ra_eq_capability [1034][1220:1223]
rfc_out_of_scope [1034][1241:1244]
rfc_proves VeriDNS.Proof.Resolver.step_cname_chase [1034][1251:1252]
rfc_out_of_scope [1034][1245:1288]

rfc_proves VeriDNS.Spec.Net.ex_wildcard_applies [1034][1367:1380]
rfc_proves VeriDNS.Spec.Net.ex_wildcard_applies [1034][1372:1375]
rfc_out_of_scope [1034][1390:1394]
rfc_out_of_scope [1034][1406:1408]
rfc_proves VeriDNS.Spec.Net.wildcardSynth_some_not_known [1034][1409:1410]
rfc_out_of_scope [1034][1421:1422]

rfc_proves VeriDNS.Spec.Net.change_detected [1034][1530:1531]
rfc_out_of_scope [1034][1543:1555]
rfc_out_of_scope [1034][1572:1574]

rfc_proves VeriDNS.Proof.NameTree.treeLookup_nameError_iff [1034][1664:1666]
rfc_proves VeriDNS.Proof.NameTree.treeLookup_nodata_sound [1034][1669:1672]
rfc_out_of_scope [1034][1676:1693]
rfc_proves VeriDNS.Spec.Net.cnameAlone_forces_cname [1034][1700:1703]
rfc_proves VeriDNS.Spec.Net.cname_acyclic [1034][1705:1712]
rfc_proves VeriDNS.Spec.Net.resolves_nxdomain_justified [1034][1721:1722]

rfc_proves VeriDNS.Proof.Cache.cache_untrustworthyNotAnswerable [1034][1781:1784]
rfc_proves VeriDNS.Proof.Cache.cache_untrustworthyNotAnswerable [1034][1793:1794]
