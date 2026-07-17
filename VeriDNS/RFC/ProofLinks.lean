import VeriDNS.RFC.Check
import VeriDNS.Proof.Parsec
import VeriDNS.Proof.DomainName
import VeriDNS.Proof.Question
import VeriDNS.Proof.ResourceRecord
import VeriDNS.Proof.RData
import VeriDNS.Proof.MessageValid
import VeriDNS.Proof.NameTree
import VeriDNS.Proof.NameTreeComplete
import VeriDNS.Proof.Cache
import VeriDNS.Proof.Server
import VeriDNS.Proof.Resolver
import VeriDNS.Proof.Header
import VeriDNS.Proof.FreeIO
import VeriDNS.Spec.NetworkSemantics
import VeriDNS.Spec.NetworkTraces
import VeriDNS.Spec.Clarifications

rfc_proves VeriDNS.Proof.Parsec.bv8_roundtrip [1035][437:477]
rfc_proves VeriDNS.Proof.Parsec.bv16_roundtrip [1035][437:477]
rfc_proves VeriDNS.Proof.Parsec.bv32_roundtrip [1035][437:477]
rfc_proves VeriDNS.Proof.Parsec.uint8_roundtrip [1035][437:477]
rfc_proves VeriDNS.Proof.Parsec.uint16_roundtrip [1035][437:477]
rfc_proves VeriDNS.Proof.Parsec.uint32_roundtrip [1035][437:477]

rfc_proves VeriDNS.Proof.DomainName.wireFormat_roundtrip [1035][533:552]
rfc_proves VeriDNS.Proof.DomainName.decode_encode_name [1035][533:552]
rfc_proves VeriDNS.Proof.DomainName.decodeName_namespace_conforms [1035][533:552]
rfc_proves VeriDNS.Proof.DomainName.nameEqCI_conforms [1035][478:530]
rfc_proves VeriDNS.Proof.DomainName.foldCaseByte_example_conforms [1035][478:530]

rfc_proves VeriDNS.Proof.DomainName.foldCaseByte_casefold_exact [1035][478:530]
rfc_proves VeriDNS.Proof.DomainName.nameEqCI_complete [1035][478:530]
rfc_proves VeriDNS.Proof.DomainName.foldCaseByte_nonalphabetic_exact [1035][533:552]
rfc_proves VeriDNS.Proof.NameTree.foldCaseByte_toNat [1035][478:530]
rfc_proves VeriDNS.Spec.namespace_casefold_exact [1035][478:530] via VeriDNS.Proof.DomainName.foldCaseByte_casefold_exact
rfc_proves VeriDNS.Spec.namespace_compare_complete [1035][478:530] via VeriDNS.Proof.DomainName.nameEqCI_complete
rfc_proves VeriDNS.Spec.namespace_nonalphabetic_match_exactly [1035][533:552] via VeriDNS.Proof.DomainName.foldCaseByte_nonalphabetic_exact
rfc_proves VeriDNS.Spec.namespace_compare_caseinsensitive [1035][478:530] via VeriDNS.Proof.DomainName.nameEqCI_conforms
rfc_proves VeriDNS.Spec.namespace_compare_example [1035][478:530] via VeriDNS.Proof.DomainName.foldCaseByte_example_conforms

rfc_proves VeriDNS.Proof.Question.decode_encode [1035][1530:1570]
rfc_proves VeriDNS.Proof.ResourceRecord.decode_encode [1035][1572:1632]

rfc_proves VeriDNS.Proof.RData.decode_encode_a [1035][1099:1124]
rfc_proves VeriDNS.Proof.RData.decode_encode_cname_raw [1035][729:743]
rfc_proves VeriDNS.Proof.RData.decode_encode_hinfo [1035][745:764]
rfc_proves VeriDNS.Proof.RData.decode_encode_mx [1035][913:933]
rfc_proves VeriDNS.Proof.RData.decode_encode_soa [1035][1009:1081]

rfc_proves VeriDNS.Proof.Message.decode_encode_of_decode [1035][1351:1400]
rfc_proves VeriDNS.Proof.Message.run_questionDecode_valid [1035][1530:1570]
rfc_proves VeriDNS.Proof.Message.run_decodeName_validLabels [1035][1634:1738]
rfc_proves VeriDNS.Proof.Message.decodeNameAux_validLabels [1035][1634:1738]

rfc_proves VeriDNS.Proof.NameTree.decodeName_valid [1035][1634:1738]
rfc_proves VeriDNS.Proof.NameTree.decodeNameAux_valid [1035][1634:1738]

rfc_proves VeriDNS.Proof.NameTree.treeLookup_answer_sound [1034][1289:1366]
rfc_proves VeriDNS.Proof.NameTree.treeLookup_nodata_sound [1034][1289:1366]

rfc_proves VeriDNS.Proof.NameTree.localAnswer_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.stepCheckLocal_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.stepAnalyzeResponse_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.step_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resolveLoop_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resume_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resolve_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.ioResumeLoop_sound [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resolveWithIO_sound [1034][1849:1976]

rfc_proves VeriDNS.Proof.Cache.computeNegativeTtl_conform [2308][418:463]
rfc_proves VeriDNS.Proof.Cache.nxdomain_retrieval_conform [2308][464:521]

rfc_proves VeriDNS.Proof.Server.emitted_z_conforms [1035][1401:1529]
rfc_proves VeriDNS.Proof.Server.deliveredResponse_rd [1035][1401:1529]
rfc_proves VeriDNS.Proof.Server.errorResponse_rd [1035][1401:1529]
rfc_proves VeriDNS.Proof.Server.server_qr_semantics [1035][1401:1529]
rfc_proves VeriDNS.Proof.Server.server_aa_semantics [1035][1401:1529]
rfc_proves VeriDNS.Proof.Server.server_ra_semantics [1035][1401:1529]

rfc_proves VeriDNS.Proof.Server.shim_accept_requires_source_and_query_match [5452][348:388]

rfc_proves VeriDNS.Proof.Server.truncateUdp_no_trunc [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncateUdp_flag_oversized [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncateUdp_truncated [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncateUdp_additional_only [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncateUdp_size [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncateUdp_udpusage [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncateUdp_udpusage_tc [1035][1752:1779]
rfc_proves VeriDNS.Proof.Server.truncate_tc_semantics [1035][1752:1779]

rfc_proves VeriDNS.Proof.Resolver.impl_algorithm_sbelt_fallback [1034][1849:1976]
-- Finding 015: root-cut SBELT fallback for an address-less NS RRset (RFC 1034 §5.3.3).
rfc_proves VeriDNS.Proof.Resolver.stepFindServers_rootCut_sbelt_fallback [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.stepFindServers_rootCut_sbelt_progress [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.step_implies_spec [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.impl_obligation_checkAnswer [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.impl_obligation_cname [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.impl_obligation_delegation [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.impl_obligation_serverFailure [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.impl_obligation_answerOrNameError [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.step_cname_chase [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.localAnswer_nameError_semantics [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.resolve_loop_star [1034][1849:1976]
rfc_proves VeriDNS.Proof.Resolver.resolve_loop_done [1034][1849:1976]

rfc_proves VeriDNS.Proof.Cache.negativelyCacheable_nodata [2308][464:521]
rfc_proves VeriDNS.Proof.Cache.negative_soa_in_authority [2308][404:417]

rfc_proves VeriDNS.Spec.usingthecache_truncated_not_cached [1035][2581:2587] via VeriDNS.Proof.Cache.truncated_not_cached
rfc_proves VeriDNS.Proof.Server.negativelyCacheable_truncated [1035][2581:2587]
rfc_proves VeriDNS.Proof.Server.storeNegativeIfCacheable_truncated [1035][2581:2587]
rfc_proves VeriDNS.Proof.Server.replyForResolution_truncated_cache_unchanged [1035][2581:2587]

rfc_proves VeriDNS.Proof.NameTree.localAnswer_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.stepCheckLocal_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.stepAnalyzeResponse_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.step_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resolveLoop_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resume_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resolve_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.ioResumeLoop_complete [1034][1849:1976]
rfc_proves VeriDNS.Proof.NameTree.resolveWithIO_complete [1034][1849:1976]

rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][285:294]
rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][357:361]
rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][608:620]
rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][941:953]
rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][1019:1024]

rfc_proves VeriDNS.Spec.Net.serverAnswers_answer_authoritative [1034][297:302]
rfc_proves VeriDNS.Spec.Net.serverAnswers_answer_authoritative [1034][913:921]
rfc_proves VeriDNS.Spec.Net.serverAnswers_answer_authoritative [2181][436:458]
rfc_proves VeriDNS.Spec.Net.serverAnswers_answer_authoritative [2181][460:477]
rfc_proves VeriDNS.Spec.Net.ServerAnswers_det [1034][830:844]

rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1034][310:317]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1034][327:339]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1034][846:851]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1034][1646:1654]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1034][1656:1673]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [2181][187:194]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [2181][695:728]
rfc_proves VeriDNS.Spec.Net.no_servfail_direct [1034][826:829]
rfc_proves VeriDNS.Spec.Net.no_servfail_direct [1034][1636:1645]
rfc_proves VeriDNS.Spec.Net.resolves_nxdomain_justified [2181][296:311]

rfc_proves VeriDNS.Spec.Net.cnameAlone_forces_cname [2181][601:628]
rfc_proves VeriDNS.Spec.Net.noData_branch_total [2308][245:272]
rfc_proves VeriDNS.Spec.Net.cname_acyclic [2308][542:546]
rfc_proves VeriDNS.Spec.Net.serverAnswers_nameError_carries_soa [2181][515:528]
rfc_proves VeriDNS.Spec.Net.truncateToCap_fits [2181][577:592]

rfc_proves VeriDNS.Spec.Net.ex_poison_cannot_be_cached [5452][247:251]
rfc_proves VeriDNS.Spec.Net.resolves_data_needs_acceptance [5452][441:445]
rfc_proves VeriDNS.Spec.Net.resolves_data_needs_acceptance [5452][704:725]
rfc_proves VeriDNS.Spec.Net.resolves_data_needs_acceptance [5452][736:765]

rfc_proves VeriDNS.Spec.Net.growSection_preserves_lookup [1034][1515:1520]
rfc_proves VeriDNS.Spec.Net.path_stable_under_growth [1034][1522:1529]

rfc_proves VeriDNS.Spec.Net.neg_caching_scenario [2308][761:779]

rfc_proves VeriDNS.Proof.Header.decode_encode [1034][852:855]
rfc_proves VeriDNS.Proof.Question.decode_encode [1034][880:886]

rfc_proves VeriDNS.Proof.FreeIO.run_resolveWithIO_networkAnswer [5452][399:439]

rfc_proves VeriDNS.Spec.Net.accepts_requires_match [2181][132:147]
rfc_proves VeriDNS.Spec.Net.accepts_requires_match [2181][150:167]
rfc_proves VeriDNS.Spec.Net.accepts_requires_match [2181][175:185]

rfc_proves VeriDNS.Spec.rrset_setAllTtls_uniform [2181][204:214]

rfc_proves VeriDNS.Spec.Net.wf_glue_present [2181][679:683]
rfc_proves VeriDNS.Spec.Net.wf_glue_present [2181][684:693]

rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [2181][594:599]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1035][957:979]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1035][980:1007]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1035][2153:2155]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1035][2161:2164]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1035][2174:2191]
rfc_proves VeriDNS.Spec.Net.resolves_answer_authoritative [1035][2395:2425]
rfc_proves VeriDNS.Spec.Net.no_servfail_direct [1035][2378:2392]

rfc_proves VeriDNS.Spec.Net.sortedByRtt_sorted [1035][2427:2430]

rfc_proves VeriDNS.Proof.RData.decode_encode_a [1035][788:808]
rfc_proves VeriDNS.Proof.RData.decode_encode_soa [1035][809:896]

rfc_proves VeriDNS.Proof.DomainName.decodeName_namespace_conforms [1034][596:600]

rfc_proves VeriDNS.Spec.Net.answer_invariant_foreign_class [2181][404:423]

rfc_proves VeriDNS.Spec.qr_semantics_0 [1035][1401:1529] via VeriDNS.Proof.Server.server_qr_semantics
rfc_proves VeriDNS.Spec.aa_semantics_0 [1035][1401:1529] via VeriDNS.Proof.Server.server_aa_semantics
rfc_proves VeriDNS.Spec.ra_semantics_0 [1035][1401:1529] via VeriDNS.Proof.Server.server_ra_semantics
rfc_proves VeriDNS.Spec.tc_semantics_0 [1035][1401:1529] via VeriDNS.Proof.Server.truncate_tc_semantics
rfc_proves VeriDNS.Spec.z_prop_0 [1035][1401:1529] via VeriDNS.Proof.Server.emitted_z_conforms
rfc_proves VeriDNS.Spec.aa_prop_0 [1035][1401:1529] via VeriDNS.Proof.Server.emitted_aa_conforms
rfc_proves VeriDNS.Spec.id_prop_1 [1035][1401:1529] via VeriDNS.Proof.Server.response_id_conforms
rfc_proves VeriDNS.Spec.rcode_formatError_semantics [1035][1401:1529] via VeriDNS.Proof.Server.hygiene_formatError
rfc_proves VeriDNS.Spec.rcode_notImplemented_semantics [1035][1401:1529] via VeriDNS.Proof.Server.hygiene_notImplemented
rfc_proves VeriDNS.Spec.rcode_refused_semantics [1035][1401:1529] via VeriDNS.Proof.Server.hygiene_refused
rfc_proves VeriDNS.Spec.rcode_serverFailure_semantics [1035][1401:1529] via VeriDNS.Proof.Server.hygiene_serverFailure
rfc_proves VeriDNS.Spec.rcode_nameError_semantics [1035][1401:1529] via VeriDNS.Proof.Resolver.localAnswer_nameError_semantics
