# Architecture

## Module Structure

```
VeriDNS/
  RFC/
    Parser.lean          -- RFC text extraction (line ranges, page break stripping)
    Property.lean        -- Sentence splitting and byte-position tracking utilities
    NLP.lean             -- SVO sentence parser, semantic derivation, example analysis
    PropRules.lean       -- Declarative property rule framework (PropSpec expression trees + DSL)
    Macro.lean           -- include_rfc compile-time command macro
    Syntax.lean          -- Code generation: structures, enums, formal Props from RFC text
  Spec/           -- Formal specifications derived from RFC text
    Header.lean   -- RFC 1035 section 4.1.1: DNS header format
    Question.lean -- RFC 1035 section 4.1.2: Question section format
    ResourceRecord.lean -- RFC 1035 section 4.1.3: Resource record format
    Compression.lean    -- RFC 1035 section 4.1.4: Message compression
    DomainName.lean     -- RFC 1035 section 3.1:   Name space definitions
    Message.lean  -- RFC 1035 section 4.1:   Message format (section diagram)
    RRType.lean   -- RFC 1035 section 3.2.2-3: TYPE and QTYPE values + RFC 3597 section 2 unknown-type carrier (RRType.unknown)
    RRClass.lean  -- RFC 1035 section 3.2.4-5: CLASS and QCLASS values
    RData.lean    -- RFC 1035 sections 3.3-3.4: RDATA formats (16 types)
    Transport.lean -- RFC 1035 section 4.2: UDP/TCP transport constraints
    Cache.lean    -- RFC 1034 §5.3.2 + RFC 1035 §7.4, §6.1.3: Cache constraints + timer
    Resolver.lean -- RFC 1034 §5.3.2-3: Resolver state (glossary) + algorithm (numbered steps) + SlistEntry. The refer (step 4b) guard requires `resp.answer.isEmpty` (2026-06): "dirty referrals" — a non-empty, non-answering answer section alongside an NS authority — are NOT followed as a delegation (they fall through to the answer/error branches), matching the model `refer` rule's `isReferral` premise. Closes the dirty-referral forward-simulation gap. The CNAME-chase (step 4a) prepends ONLY the chased CNAME record to the delivered chain — `cnameChain := prependCnameLink s.cnameChain resp` (= `s.cnameChain.push <the chaseable CNAME RR>` via `extractCnameRR`), NOT the whole `resp.answer` (2026-06): a CNAME response may carry extra unrelated/off-bailiwick answer records, and passing them through to the client is an answer-injection vector — they are now dropped from the delivered answer (subsequent chain links resolve separately). This matches the model `Resolves.answerCname` (which prepends exactly the single `cnameRR`), closing the CNAME-chain forward-simulation gap. The chase is additionally OWNER-CHECKED (2026-07, external review #036): `extractCname`/`extractCnameRR` only consider a type-5 record whose owner `nameEqCI`-matches the reply's echoed question name (RFC 1034 §3.6.2 — the CNAME rewrite applies to the node the query matched; unbound scrubs off-owner CNAMEs), and the model `cnameRR` carries the matching `nameEq r.owner qname` conjunct — pre-fix, an answer carrying `attacker.chosen CNAME target.` steered the resolver's next upstream query to an attacker-chosen target.
    NegativeCache.lean -- RFC 2308: negative caching props + NegativeCacheSpec/NegativeAuthoritySpec
    Credibility.lean   -- RFC 2181 §5.4.1: Trustworthiness enum + TrustworthinessSpec + answerability obligation
    Resilience.lean    -- RFC 5452 §9.1-2: response matching + unpredictability obligations
    Server.lean   -- RFC 1035 §6.2, §7.3: Server query processing + UdpSocket typeclass
    -- Platonic DNS-tree domain model + inductive network relation (the semantic
    -- domain the resolver is verified against) and the RFC-coverage sweep:
    NameTree.lean       -- RFC 1034 §3.1-3.4: Node tree, name=path, subdomain relation, octet limit, case rules, §3.4 example tree
    Zone.lean           -- RFC 1034 §4: zones (cuts), name servers, authoritative data, NS/glue, ZoneEvolution (robustness), recursive-never-referral
    NetworkModel.lean   -- RFC 1034 §3-§6: THE semantic model — names=paths in the platonic Node tree, the inductive tree↔network relations (AuthoritativeFor/DelegatesTo — both CLASS-AWARE and NEAREST-ANCESTOR, carrying a QCLASS index and phrased via bestZone/bestDeleg so authority is per-class (§4.2.2: an IN query is never satisfied by a CH zone) and through the closest covering zone (§4.3.2 step 2), never a class-blind any-ancestor match), the §4.3.2 name-server algorithm as a DECLARATIVE inductive relation (ServerAnswers, one constructor per RFC step, emitting a Step trace; NODATA-vs-NXDOMAIN via isEmptyNonTerminal — a single uniform noData branch carries the SOA for BOTH the empty-non-terminal and the "exists, wrong type" (§6.2.4) forms (answer only fires when there IS matching data), matching modern resolvers; the authority section is noDataAuthority z = SOA always, plus the apex NS RRset when the zone opts into RFC 2308 §2.2 TYPE 1 (Zone.negCacheNS, a deterministic per-zone choice, default TYPE 2 = SOA only) — so both §2.2 SOA-bearing shapes are representable (ex_nodata_type1 exhibits TYPE 1: authority = SOA + NS); the NXDOMAIN branch is SYMMETRIC — nameError's authority is nxdomainAuthority z = SOA always plus the apex NS RRset under negCacheNS (RFC 2308 §2.1: an NXDOMAIN authority is SOA + NS, not mandated SOA-only; ex_nxdomain_type1 exhibits SOA+NS, default = the literal §6.2.5 SOA-only reply), closing the asymmetry where only NODATA could carry the apex NS; RA/RD header bits present, with RA modelled as an advertised *capability* not a per-answer fact (Server.recursionAvailable; serverAnswers_ra_eq_capability: every reply carries s.recursionAvailable — the server's willingness to recurse, NOT whether this answer recursed; serverAnswers_plain_clears_ra recovers RA=0 for a plain, non-recursing server — recursion itself is the resolver's job); CNAME exclusivity tied to the algorithm: cnameAlone_forces_cname proves that at a CNAME-alone node a non-CNAME query finds no typed record, so the `answer` branch cannot fire and the alias is provably chased — "CNAME takes precedence" as a theorem (Zone.WF_cnameAlone bridges the existing Zone.WF CNAME-exclusivity clause to it, wf_cname_forces_redirection chains the two); the §4.3.2 referral is SPLIT into a pure referral (literally empty answer — so Response.isReferral classifies it as a referral by construction, removing the old cachedAnswer/classifier inconsistency) and referralCacheAnswer (the step-4 cache-hit fall-through copying matching cached RRs for QNAME into the ANSWER section, hence classified as an answer); disjoint on whether QNAME is cached (referral_classified / referralCacheAnswer_classified land each on the correct side of the classifier). The platonic tree is NOT decorative and is tied to the declarative algorithm IN GENERAL: treeOf materialises a zone's records as the actual Node trie, and treeRecordsAt_treeOf proves — for EVERY zone and name, by induction — that Node.lookupPath navigation equals recordsAt (the read every ServerAnswers constructor performs), so recordsAt_eq_treeNav restates the §4.3.2 record read as tree navigation. Supporting: a List-routed insertRR/childInsert trie, labelEq as a proven equivalence, nameEq reverse-invariance. bestZone is CLASS-AWARE (selects the nearest-ancestor zone whose Zone.cls matches QCLASS — RFC 1034 §4.2.2 parallel namespaces are parallel per-class zones, so an IN query never reads CH data; nearest_unique in NetworkSemantics proves the longest-apex choice is semantically unique on a zonesDistinct server, so the list-order tie-break is never load-bearing). GLUE is bailiwick-de-conflated: inBailiwick (a delegation server at/below the cut needs glue) splits the referral's additional section (referralAdditional) into authoritative in-bailiwick glue first, then out-of-bailiwick address hints — both drawn from zone data ++ fresh cache; on a homogeneous delegation this equals the old additionalFrom (the §6 traces are byte-identical), and wf_glue_present (NetworkSemantics) proves a Zone.WF zone always carries glue for its in-bailiwick servers, so a well-formed referral is always resolvable. NEGATIVE-TTL is consumed, not just carried: negTTLof soa = min(SOA.MINIMUM, soa.ttl) (RFC 2308 §3/§5), negTTL z reads it off soaOf, Response.negTTL reads it back off a reply's authority SOA, and noDataAuthority_negTTL / nameError_negTTL prove a NODATA/NXDOMAIN reply's negative-cache lifetime IS negTTL z; NegCacheEntry gives the negative result the same timed (fresh/expiresAt) treatment a positive CacheEntry gets (neg_caching_scenario in NetworkTraces: the §6.2.5 reply licenses exactly 86400s — fresh at 86399, expired at 86400). multi-depth wildcards with the full §4.3.3 inhibition incl. the query-name-known guard — wildcardSynth inhibits on nameKnown (a name existing with records of ANY other type, not only empty non-terminals), so a query for an absent type at an existing name under a wildcard resolves to NODATA instead of synthesizing a bogus answer or leaving the step-3c branch stuck (ex_wildcard_applies / ex_wildcard_inhibited / ex_ent_under_wildcard / ex_typed_under_wildcard); A-record RDATA is the four-octet IPv4 itself (RData.a : IPv4, with toDotted as the routing identity); referral with step-4 cache-glue fall-through; fromCache with best-cached-delegation in authority, GUARDED non-degenerate (RFC 1034 §4.3.2 step 4 fires only when QNAME is in the cache OR a best cached delegation exists — hne: a cached answer or a cached delegation — so a no-zone server with an empty cache can no longer emit a bogus empty-answer empty-authority NOERROR; every fromCache reply is a genuine cache answer or cache referral). Meta-theorems: noData_branch_total (the no-records branch is total — no gaps) and ServerAnswers_det (full determinism — `ServerAnswers s now` is a function of its inputs: same server/time/query ⇒ same trace AND same response. `now` is an explicit relation parameter precisely so the time-dependence of cache/glue TTL aging is an input, not non-determinism)), intra-zone failover (ServerFailover), timed server cache, and a UNIFIED evolution: CoEvolves bundles a System (platonic tree + network) so tree and network evolve in lock-step (tree_step/net_step projections), with delegate_creates_authority tying the network transition to AuthoritativeFor. Wildcard DEPTH follows RFC 4592 (the closest-encloser clarification of §4.3.3), not literal §1034 prose — wildcardSynth synthesises at ANY depth below the wildcard node when no closer name is known; the citation stays on [1034] as the wildcard's origin, with the deviation documented in wildcardSynth's docstring. AUTHORITATIVE CORRECTNESS at the source: serverAnswers_answer_authoritative proves the §4.3.2 positive `answer`/`cname` branch fires ONLY when the server holds the nearest-ancestor zone with no cut above QNAME (bestZone = some z ∧ bestDeleg z QNAME = none), which is EXACTLY AuthoritativeFor net QCLASS — and since AuthoritativeFor is now itself DEFINED via bestZone/bestDeleg, this is a direct constructor application (the bestZone_spec/bestDeleg_none_all fold lemmas remain as standalone characterizations) — so "the answering server is authoritative for QNAME" is a THEOREM about the branch, not an assumption (a server lacking authority cannot reach these branches; it refers/errors instead). This is the source-level half of closing "grounding ≠ correctness" (the resolver-level half, AuthAnswer/resolves_answer_authoritative, is in NetworkSemantics). Every decl rfc_proves-linked at sub-section granularity.
    NetworkTraces.lean  -- RFC 1034 §6: the scenario topology encoded as Zone/Server/Network terms; each §6.2 worked query replayed as a ServerAnswers derivation whose response IS the RFC's (non-circular — the response is produced by the relation, not asserted). Also inhabits names-as-paths, the tree↔network relation, cache aging, and failover. These derivations are what prove the model is non-vacuous. Tree-growth robustness is now GENERAL, not a hand-built example: growSection_preserves_lookup proves that for ANY tree, ANY already-resolving non-root name, and ANY grown subtree, a TreeEvolution.growSection step leaves resolution unchanged (via descend_push: an end-append never displaces find?'s first match); path_stable_under_growth is a corollary instance.
    NetworkSemantics.lean -- operational layer on top of the static model. The ITERATIVE resolver Resolves threads everything: a MONOTONE wall-clock (start time `now` → end time `tEnd`, advanced by an explicit delay on every network hop; resolves_time_monotone proves now ≤ tEnd so a resolution genuinely takes time and a cache entry checked at a later hop is checked against a later clock — ex_resolution_advances_time exhibits a strict advance via a timeout-then-fallback), a timed credibility-aware Cache (in+out, so resolution populates it and later queries hit it — RFC 2181 §5.4.1 trust + RFC 2308 negative entries, with cache_no_stale), next hops reached by IP address via glue (serverAt/glueAddresses), the transport (Transit keyed by address + RFC 5452 accepts), COMPRESSION-AWARE wire-size truncation (RFC 1035 §4.1.4): messageWire threads a "seen suffixes" state through the message in wire order (header + question + each RR's owner and RDATA names), so a name reoccurring as a suffix collapses to a 2-octet pointer exactly as on the wire — no inflated record-by-record sum that would truncate far too eagerly (an owner repeating QNAME costs 2 octets, not ~33). The seen-state tracks (suffix, on-wire OFFSET) pairs and enforces the §4.1.4 14-bit pointer ceiling (ptrMax = 16383): a suffix first written past offset 16383 is NOT a usable target and the repeat is charged in full, so the metric cannot UNDER-count by claiming a pointer the wire format can't encode (nameWireC_ptr_ceiling witnesses the boundary — compressible at offset 16383, full-width at 16384). truncateToUdp fills what fits via packFit (which threads the same compression state from the post-question point) and sets the TC bit (Response.tc) on a real >512 message — what a real compressing server does, not "drop everything". truncateToUdp_fits proves the packed reply ≤ 512 for any question that fits the datagram, and qname_fits_datagram discharges that precondition for every §3.1-legal QNAME (header+question ≤ 271); bigResponse_truncated exhibits a 30-record response that crosses 512 EVEN after maximal compression, resolution seeded from root hints / SBELT so a cold lookup walks root→TLD→authoritative purely by referral (rootHints / ex_resolve_from_root_hints), a declarative delegation-loop guard in DEPTH-PROGRESS form (refer/referForget carry an abstract `frontier : Name` watermark chosen by the derivation: the referral must descend strictly below it — hdescF — and it must be unvisited — hfresh : frontier ∉ seen, with `frontier :: seen` threaded to the recursion. The honest-server descent hdesc : descendsBelow (serverBailiwick …) is kept as a SEPARATE premise pinning the cache-write bailiwick and feeding the grounding theorems, so loop-freedom bookkeeping is DECOUPLED from served-zone provenance — which a real resolver cannot attest for a warm-cache delegation. This matches the impl's delegationCloserB matchCount-increase guard and RFC 1034 §5.3.3 progress, and lets the forward simulation discharge freshness UNIFORMLY across the honest, cache-rebuild — including a deeper prior cached delegation, the old s8 provenance gap — and spoofed referral arms, always with the cut's ancestor at the current SLIST matchCount depth, isAncestor_drop_ancestor), a BAILIWICK check AND a STRICT-DESCENT/progress guard (refer/referForget require BOTH reply.msg.inBailiwick q.qname — every NS RR in the referral's authority is owned by an ancestor of QNAME — AND reply.msg.descendsBelow (serverBailiwick srv q.qname q.qclass): the referral's cut is a PROPER descendant of the answering server's own zone apex. inBailiwick ALONE is satisfied by a referral pointing sideways or UPWARD — a closer ancestor, or even the root, is still an ancestor of QNAME — so descendsBelow is what actually forces progress: every followed referral strictly shortens the label distance to QNAME (descendsBelow_strict unpacks "proper descendant"; the loop guard only bounded re-visits, not progress). referral_in_bailiwick + referral_descends_strictly show an honest §4.3.2 referral passes BOTH guards, so they reject only lame/hostile sideways/upward referrals, never legitimate descent). The refer step ALSO requires GLUE to be present (hglue: glueAddresses reply.msg ≠ []); a glueless referral instead goes through referForget (which admits an empty recursive SLIST). The glueless case is a SPLIT pair of rules matching the implementation's (and BIND/unbound's) temporal structure: RECEIPT of the glueless referral is refer/referForget (the referral is absorbed; its NS hosts survive only as cached NS records), and the ADDRESS RESOLUTION is the separate gluelessNs rule (RFC 1034 §5.3.3 "obtain the missing addresses", performed lazily one loop iteration later) — with NO addressed SLIST candidates left (conclusion slist []), it picks an NS host at an enclosing cut of QNAME justified by a rule-carried FROZEN provenance cache cprov (hns : nsHost ∈ cprov.nsHostsAt now zone — per-key max-rank topServed, anti-poison inherited from the bailiwick-gated cache writes; the soundness driver instantiates cprov as the genuine post-referral, pre-capacity-bound cache). The anchor is deliberately NOT the rule's live cache c: real resolvers (RFC 1034 §5.3.2 SLIST) hold the referral's NS names in memory and never re-derive them at use time, and a live-cache anchor is unsound to thread — an earlier glueless sub-run can write a higher-credibility (zone,NS,IN) RRset that OCCLUDES the referral's in topServed reads, invalidating the remaining address-less targets (the corner-2 cacheCname cf-slot mechanism reused; cprov is untied to c because no local refinement holds in either direction — c both gains sub-run absorbs and loses evictions vs cprov — and hns feeds no security walk, which compose only through ihNs/ihRec). It resolves the host's A address as a FRESH sub-resolution (its own visited sets; the impl bounds the sub-run by depth), and continues the main query on an evicted image (CacheRefines slot c2f, the cacheCname cf-slot mechanism — the impl's capacity bound applies between the sub-run's return and the main loop's re-entry) of the sub-run's output cache at a SLIST containing the learned address (ex_sibling_resolution composes referForget receipt + gluelessNs address-resolution end-to-end). This replaced the old fused referNoGlue rule, which bundled receipt + NS-address sub-resolution + continuation into one step pinned to the delegating server's witnesses — unusable in the forward simulation precisely because the impl performs receipt and address resolution one loop iteration apart. So a glueless-but-resolvable referral is never abandoned. The acceptance test is ADVERSARIAL, not true-by-construction, and bites on the PAYLOAD, with payload integrity now DERIVED rather than asserted: Datagram CARRIES the response message (msg), and answer/refer/referForget/answerCname take a `reply : Datagram` whose body is NOT pinned to the honest answer — instead an OnWire provenance hypothesis admits BOTH the honest server's reply (OnWire.fromServer) AND an off-path attacker's forged-body injection (OnWire.offPath: arbitrary poison body, constrained only to not match both the ID and source port, since a blind attacker can't observe the query). So the RFC 5452 cache-poisoning attack is now EXPRESSIBLE (the old spec's `reply.msg = honest` side-condition made a poison datagram an illegal value, true-by-fiat). onWire_accepted_honest then DERIVES that any reply passing accepts carries exactly the honest body — the off-path branch can't satisfy accepts (accepts_off_path_false), so fromServer is the only survivor. accepts_requires_match pins all RFC 5452 §4 checks on passing — transaction ID + source address + both ports + the WHOLE question section, QNAME AND QTYPE AND QCLASS (Datagram carries a qclass field and accepts compares it: the §4 match is the entire question, not just name+type); resolves_data_needs_acceptance proves any cache change required an accepted OnWire datagram whose body equals the honest payload (reply.msg = honest, via onWire_accepted_honest — payload integrity, not just header existence); offpath_cannot_cache strengthens this to the UNIVERSAL guarantee — any cache change forces a datagram that echoed the query's transaction ID AND the resolver's source port AND carried the honest body, never a forged RRset; ex_poison_cannot_be_cached takes the honest body straight from ServerAnswers (not a literal), exhibits a forged poison datagram that IS a legal OnWire event yet fails accepts, and — the load-bearing clause — proves via onWire_accepted_honest that NO accepted on-wire reply (on any header the attacker forges) carries the poison RRset, and ex_spoof_cannot_poison drives one through a concrete walk to rejectSpoof. The §4.3.2 step-1 fork is modelled by ServerDispatch — a genuine two-way branch, not a bundle: localAnswer (answer from authoritative data, taken when q.rd is clear OR Server.recursionAvailable is false) vs recurse (run Resolves from the server's hints, taken only when q.rd AND recursionAvailable). nonRecursive_dispatch_is_local PROVES a server without RA can only take localAnswer — so RD is genuinely ignored when recursion is off (ex_recursive_dispatch exhibits the recurse walk root→TLD→authoritative; ex_nonrecursive_ignores_rd shows a plain server referring an RD query instead of recursing). RD DOES NOT PROPAGATE PAST THE RESOLVER: Datagram carries an `rd` header bit (RFC 1035 §4.1.1) and the iterative resolver's upstream query builder queryDatagram CLEARS it unconditionally (rd := false), independent of the client's q.rd — so the recurse branch fires BECAUSE the client set RD, yet every query it then puts on the wire to an authoritative server is non-recursive, asking only for that server's best local answer/referral (queryDatagram_clears_rd, RFC 1034 §4.3.1). This is upgraded to a DERIVATION-LEVEL guarantee by resolves_rd_irrelevant: by induction over the WHOLE resolution, overwriting the query's RD with any value yields the same trace/path/end-time/output-cache/response — so RD influences nothing downstream of the dispatch (not a single upstream query, cache write, or answer), genuine independence not just a zeroed field (rests on serverAnswers_rd_irrelevant: the §4.3.2 server algorithm never reads RD). RD is excluded from the RFC 5452 accepts tuple; an honest reply echoes it (replyDatagram keeps it via `with`). Previously the wire datagram had no RD bit, so q.rd was silently dropped at serialization rather than deliberately cleared. The off-path entropy is also proved non-circularly over a COMPLETELY free attacker: accepted_needs_full_secret shows any accepted datagram (any forged body, no provenance restriction) matched both the transaction ID AND the source port — so a forged-body injection requires guessing the full ~32-bit secret — and blind_match_unique shows a fixed blind datagram is accepted for at most ONE (id, port) secret (the 2⁻³² bound, proved). The compression metric's faithfulness is bounded below: messageWire_lb proves messageWire ≥ messageFloor (12 header + nonzero QNAME + 4 question + each RR's 10 fixed + RDATA-fixed + nonzero owner), so it cannot under-count the incompressible octets a real serializer must emit. CROSS-ZONE CNAME chasing (answerCname): when a server returns a bare CNAME whose canonical name lies in another zone, the resolver restarts resolution on the target from a fresh SLIST, prepends the CNAME, and guards a visited-name set nseen against alias loops (ex_cname_chase_across_zones walks ALIAS→REAL.NET across two servers). The SAME chase applies to a CACHED CNAME (cacheCname, RFC 1034 §4.3.2 step 3a on cached data): on a typed cache miss with a fresh cached CNAME for QNAME (Cache.cnameAt) and a non-CNAME query, the resolver follows the alias OFFLINE — no datagram, no time elapsed — restarts on the target, and prepends the cached CNAME, exactly the answerCname shape but without a round trip for the alias (ex_cached_cname_chased; cnameAt_eqData keeps the prepended cached alias grounded). This closes the asymmetry where the live path chased aliases but a cached CNAME was invisible to a non-CNAME query (Cache.hit's qtype filter never matched it), so a cache miss needlessly re-queried the network. Negative caching is wired end-to-end: absorbNeg derives the negative TTL from min(SOA.MINIMUM, SOA TTL) (absorbNeg_ttl_is_soa_minimum) — not a free parameter — and ONLY from a SOA owned at or above the query name (soaNegTtl is parameterized by qname with an isAncestor r.owner qname per-record conjunct, RFC 2308 §3: the denial's SOA must be the apex of the zone containing the qname; an attacker-owned SOA riding an NXDOMAIN — review #012/#013 negative-cache poisoning — triggers no negative write, mirrored in the impl's extractSoaNegative owner check) — and caches BOTH NXDOMAIN (name-keyed, suppressing all types) AND NODATA (type-keyed, so a re-query for the same type hits but other types don't; absorbNeg_nodata_typed, type-aware negHit), populated end-to-end by ex_negcache_populated / ex_nodata_cached. isReferral keys on NS-present AND SOA-absent (RFC 2308 §2.2: the SOA distinguishes a negative reply from a referral, so even a NODATA TYPE 1 reply carrying NS records is correctly classified — for any RFC-legal response, not just ours). Resolves carries no `fuel` index — termination of an inductive relation is automatic. Proven on the §6.3.1 multi-hop MX walk from an empty cache, a cache-hit (no network) + expire pair, a timeout→failover, a spoof-rejection, and a real truncation. ex_631_recursion_safe is the END-TO-END RECURSION CAPSTONE on the canonical §6 scenario data: the §6.3.1 referral→answer descent is shown — by instantiating the general theorems, not re-proving — to be simultaneously loop-free (delegation_bailiwick_fresh: every followed referral's frontier is fresh in the visited set — depth-progress, address-Nodup having been dropped as false under anycast), time-monotone (resolves_time_monotone), and authoritative-or-grounded (resolves_answer_authoritative), so the static NetworkModel drives a real iterative resolution that is acyclic, advancing, and non-fabricating at once (the cold root→TLD→authoritative walk is ex_resolve_from_root_hints / _authoritative). Also: §5.3.3 SLIST RTT ordering — sortedByRtt_sorted proves the SLIST is sorted by ascending RTT for ANY input (List.Pairwise, general — not one hand-picked list) and sortedByRtt_perm proves it drops/duplicates no server, with sortByRtt_fastest_first a corollary; §4.2 class partition as genuine isolation: answer_invariant_foreign_class proves the QCLASS answer is bit-for-bit INVARIANT under adjoining foreign-class data — even at the SAME owner name (the parallel trees are independent, not merely non-leaking), lifted to the §4.3.2 answer step by answer_step_invariant_foreign_class; ex_class_isolation_in/_ch exhibit it concretely as TWO parallel same-apex zones (inClassZone IN / chClassZone CH) on one server, the same name HOST.X resolving to a class-dependent address because bestZone selects the matching-class zone (same name, same QTYPE, class-dependent zone — "parallel namespace trees" made literal), the IPv4 octet model (now the representation in RData.a, not a side artifact), Zone.WF invariants incl. CNAME-exclusivity + in-bailiwick glue-completeness + §3.1 length limits (Zone.WF_cnameAlone lifts the per-record CNAME-exclusivity clause to every QNAME's recordsAt, feeding the NetworkModel forcing theorem so a well-formed CNAME node provably chases the alias); a whole-NETWORK Network.WF bundles per-server zone distinctness (Server.zonesDistinct — no two zones share both class and apex, the precondition for bestZone unambiguity) with per-zone Zone.WF + Zone.classHomogeneous (every record/NS of the zone's own class, so the class-blind node predicates are sound on a matched zone), discharged on the §6 network by scenario_WF. Loop-freeness is declarative, not an algorithm, in both dimensions: CNAME chains carry a `seen` path with cname_acyclic proving the visited names are Nodup, and the referral walk carries a visited-FRONTIER set `seen` with delegation_bailiwick_fresh proving each followed hop's frontier unvisited (name-based depth progress, not address identity — anycast makes address-Nodup false). gluelessNs's NS-address sub-resolution runs with its OWN fresh visited sets (matching the impl, which bounds the sub-run by depth rather than by the main chain's bookkeeping) while the MAIN chain's nseen/seen pass through unchanged to the continuation — so the main walk's depth-progress guarantee is untouched by a glueless chase, and the sub-run, being itself a Resolves derivation, carries every guard of the relation (an inductive relation can't have infinite derivations, so termination is automatic). END-TO-END SOUNDNESS (no fabrication): resolves_answer_grounded proves every RR in a resolution's final answer is GROUNDED in (net, input-cache) — up to TTL (RR.eqData) it is either a record from the input cache or one some REAL server placed in a section of a genuine ServerAnswers reply during the walk; resolves_cout_grounded is the same for the output cache, and the two compose across cache round-trips via grounded_of_cache_grounded (with absorb_pos_provenance bounding what a hop's Cache.absorb can introduce and packFit_subset/truncateToCap_sections_mem showing truncation only ever drops records). CNAME chasing only splices server-produced replies, so the resolver introduces nothing of its own — the functional-correctness companion to the safety results (exact-RRset equality with the origin zone is NOT claimed: truncation/aging/CNAME splicing make grounding-up-to-eqData the right end-to-end statement). Cache.absorb's RFC 2181 §5.4.1 credibility is now CONDITIONED ON THE AA BIT — the answer/authority sections of a NON-authoritative reply (aa=false, e.g. relayed cached data) are absorbed at the bottom rank (glue), so unauthoritative data can't override authoritative data already held (only an aa=true reply gets authoritative/authority credibility). Credibility is now CONSUMED AT LOOKUP, not merely stored: Cache.hit serves only Cache.served — the matching fresh entries of MAXIMAL credibility per (owner,type,class) key (CacheRR.sameKey) — so a less-credible copy of an RRset is dropped from a lookup whenever a more-credible copy of the same key is present (served_excludes_dominated; served_glue_yields_to_authoritative is the operational form of authoritative_beats_glue; hit_drops_poison_glue exhibits a poison glue A beside an authoritative A and shows ONLY the authoritative address is served). This makes the RFC 2181 §5.4.1 ranking load-bearing rather than a property of an otherwise-unused moreCredible. Compression sizing is laid out in TRUE WIRE ORDER per RData (emitRData): SOA's MNAME/RNAME precede its 20 timer octets and MX's preference precedes the exchange name, so the §4.1.4 pointer-offset (ptrMax) test is judged at each name's real position (the old "all names after all fixed octets" shortcut mis-placed SOA names ~20 octets late). The maximal-compression assumption is RELAXED into a bracket: nameWireC_le_nameWire proves compression never costs more than the uncompressed nameWire (and nameWireC_nil gives the no-compression endpoint), so every RFC-conformant server's real serialized size sits in [maximal-compression, none] and a resolver can size against the uncompressed upper bound to stay safe against a less-compressing peer. Cache eviction BY SIZE (not just TTL): Cache.cap bounds the positive and negative stores to a capacity, dropping oldest-first (lists are newest-first since insert prepends); cap_size_le enforces the bound, cap_pos/neg_subset prove eviction only ever drops (never invents) an entry, and cap_no_stale shows it composes with the TTL discipline (still serves nothing stale). EDNS0 (RFC 6891) is THREADED through resolution: Resolves carries an ednsBuf parameter (the resolver's advertised OPT buffer), queryDatagram stamps it into Datagram.udpPayload (queryDatagram_cap: each query negotiates negotiatedUdp ednsBuf), and the answer/answerCname hops truncate the honest reply to truncateToCap (negotiatedUdp ednsBuf) — so the advertised buffer genuinely drives in-walk truncation, not a constant. negotiatedUdp floors it at 512 and the buffer-parametric truncateToCap generalises truncateToUdp (recovered as the negotiatedUdp-512 instance via truncateToUdp_eq_cap); truncateToCap_fits proves any negotiated cap is honoured, bigResponse_edns_whole exhibits a >512 message delivered WHOLE under a 1232-octet buffer, and ex_resolve_from_root_hints_edns runs the full cold root→TLD→authoritative walk with ednsBuf=1232 (vs the ednsBuf=512 ex_resolve_from_root_hints — same walk, different advertised buffer). A resolver advertising 512 is the no-EDNS instance, so the rest of the development is exactly that case. glueAddresses now dials ONLY the addresses of the referral's actual NS hosts (referredServers), not arbitrary A records riding in additional — both realistic and a poisoning defence (glue_ignores_non_ns_address drops an off-topic EVIL.COM A record); on an honest well-formed referral this is exactly the prior glue set (so the §6.3 traces are unchanged), and the candidate set is RTT-ordered (sortByRtt) before consumption. SERVER SELECTION IS A FREE CHOICE, not pinned to the RTT order: the chooseServer constructor (RFC 1034 §5.3.3/§7.2) lets a derivation built for one SLIST ordering be reused for ANY permutation of the same candidate set — output-preserving (identical trace/path/end-time/output-cache/response, only the order servers would be tried differs), so it neither introduces a new server/answer nor changes cout (offpath_cannot_cache is unaffected, the visited-frontier discipline is unchanged). This reflects that RTT sorting is a performance heuristic, not a correctness constraint, and is what reconciles the forward simulation's order gap — the implementation seeds its SLIST from referral glue in NS-name/array order and queries by transmissionCount (never reading the abstract rttOf), whereas the model refer rule pins the recursive SLIST to sortByRtt (glueEntries rttOf …); the two are never equal for an abstract rttOf but are always permutations of the same glue-address set, bridged by chooseServer (chooseServer_hasVerdict is the HasVerdict-threading producer). RTT IS RESOLVER-LOCAL, not server-asserted: Resolves carries an rttOf : String → Nat index (the §5.3.3 "batting average" the resolver itself keeps from past queries) and glueEntries pairs each glue address with rttOf a — NEVER the answering server's own Server.rtt field; closing the abstraction leak where resolution read the network's ground-truth RTT, so a server cannot reorder how its peers are tried by reporting a flattering RTT (faster_glue_tried_first now ranks against the resolver's own table). TC GUARD (RFC 1035 §4.1.1, TCP-retry out of scope): the answer/answerCname hops require reply.msg.tc = false, so a TRUNCATED (partial-RRset) reply can be neither consumed as a final answer nor cached — resolves_answer_untruncated proves every response a resolution yields has TC clear (truncateToCap_untrunc: an untruncated honest reply IS the full server response); previously a TC=1 partial reply could slip through as final. The anti-poison Cache.absorb bailiwick is now QCLASS-AWARE: each hop scopes its write to serverBailiwick srv q.qname q.qclass (the apex of the zone the server used for THIS class), not the default-IN apex — so a non-IN walk is scoped against the right zone (resolves_cache_in_bailiwick generalised to quantify the class). serverBailiwick's NON-authoritative fallback is now QNAME, not the root: a forwarder/cache server (no zone for QNAME) is trusted to cache only data at/below the exact name asked, NOT the whole namespace — the old `[]` fallback made `isAncestor [] _` hold for every name, switching the anti-poison filter OFF for the least-trusted source; serverBailiwick_covers_qname proves the scope still always admits QNAME, so a legitimate answer-for-QNAME is never dropped while everything outside QNAME's subtree from a non-authoritative answerer is. Cache.absorb also DROPS the authority-section SOA before positive caching (the SOA of a NODATA/NXDOMAIN reply bounds the NEGATIVE cache via absorbNeg, RFC 2308 §3/§5 — caching it positively would wrongly answer a later SOA query for the apex from a denial): absorb_no_authority_soa proves any positively-cached SOA came from the answer or additional section (a genuine SOA answer), never authority; nodata_authority_soa_dropped_ns_kept exhibits a TYPE 1 NODATA whose apex NS is cached but apex SOA is not. AUTHORITATIVE CORRECTNESS, end-to-end (closing "grounding ≠ correctness"): AuthAnswer net r says r equals (up to TTL) a record the RIGHTFUL AUTHORITY holds at the name (some srv whose nearest-ancestor zone for q' has no cut above it carries r in recordsAt) — strictly stronger than Grounded; AuthAnswer_authoritative bridges to AuthoritativeFor via the NetworkModel serverAnswers_answer_authoritative. resolves_answer_authoritative proves — by induction over the whole iterative walk — that EVERY record in the final answer is AuthAnswer net r ∨ Grounded net (input-cache) r: for a cold walk (input cache empty) the residual Grounded covers only CNAME/wildcard-synthesis and the server's own cache, while a direct `answer` leaf yields AuthAnswer outright (serverAnswers_leaf_auth extracts it, the CNAME-redirect branch being ruled out by the leaf's hnc guard). So a lame/on-path server CANNOT have a wrong-but-grounded answer accepted — emitting a positive answer for QNAME provably requires authority over QNAME — upgrading the resolver from VERIFIED-SAFE to VERIFIED-CORRECT; ex_resolve_from_root_hints_authoritative instantiates it on the cold root→TLD→authoritative walk (the resolved WWW.EXAMPLE.EDU address is AuthAnswer, and NS.EXAMPLE.EDU is AuthoritativeFor it). NEGATIVE replies are grounded too — NOT vacuously sound: resolves_answer_grounded only quantifies over resp.answer (empty on a NODATA/NXDOMAIN reply), so resolves_response_grounded EXTENDS grounding to the authority AND additional sections — the SOA/NS a denial carries is provably a record a real server placed in a genuine ServerAnswers reply, not minted by the resolver; and resolves_nxdomain_justified grounds the DENIAL ITSELF — a returned RCODE=nameError traces to a real authoritative name-error reply in the network OR to an NXDOMAIN (qtype=none) entry already in the input cache (via resolves_negcache_grounded, the negative analogue of resolves_cout_grounded: every out-cache negative entry is from the input cache or a server denial, with qtype=none entries tied to a nameError reply; absorb_neg/absorbNeg_neg_mem are the threading lemmas). So a spurious "this name does not exist" is not derivable. SERVFAIL is NOT REACHED FOR RESOLVABLE NAMES: the servFail producers are exactly the three CONSTRAINED terminals — exhausted (empty SLIST), and the 2026-07 total-simulation pair gaveUp (RFC 1035 §7.2 bounded work: fuel/deadline/glueless-depth budget aborts, any SLIST) and loopDetected (RFC 1034 §3.6.2 CNAME chase-cap/revisit aborts) — all three pinned to rcode=servFail + EMPTY answer + output cache = input cache (cout = c), so none can justify an answer delivery or a cache mutation (an adversary gains nothing from a give-up verdict: the delivered-shape half stays pinned by the verdict theorems); every other rule's response flows from a server reply or the cache, serverAnswers_rcode_ne_servFail proves the §4.3.2 server algorithm itself never yields servFail (NOERROR/NXDOMAIN only), and no_servfail_direct is the liveness theorem — a query whose SLIST head is a REACHABLE server returning a non-referral, untruncated §4.3.2 answer has a resolution returning that server's RCODE, hence ≠ servFail (TCP retry being out of scope, a would-be-truncated reply is the one UDP-only case a resolver legitimately can't complete, hence the untruncated premise). With the glueless-referral dead-end closed (hglue above), the only route to exhausted is genuine unreachability. ex_direct_no_servfail instantiates it one-hop; ex_631_no_servfail and ex_root_hints_no_servfail show the real multi-hop §6.3 / cold root-hints resolvable names resolve to NOERROR, never SERVFAIL. QNAME MINIMISATION (RFC 9156/8020, model half — plan stage Q2): every datagram-sending rule (refer/referForget/trustedReferral/rejectSpoof/badResponse/unfollowableReferral) now carries the SENT question `pq` with `hprobe : ProbeQuery pq q` — either the true query (left disjunct: qname/qtype/qclass agree; `rd` deliberately unpinned so resolves_rd_irrelevant survives) or a STRICT probe (StrictProbe: a proper ancestor of q.qname strictly below an existentially-closed delegation cut, at the obscured QTYPE=A — RFC 9156 §2.1/§2.2) — the wire literals (hans/hacc/hwire) are keyed at pq so a minimising round reveals only the probe, while the guards, cache-write bailiwicks, and recursion stay stated against the true target; every pre-minimisation producer instantiates the left disjunct (ProbeQuery.refl) and the answer/CNAME rules keep it FORCED by construction — only referrals and denials are consumable from probe rounds. badResponse's hbad gains the probe-discard right disjunct (rcode = servFail ∨ StrictProbe pq q — the RFC 9156 §3 (6c) reading: an accepted-but-unconsumed probe reply — NOERROR with or without an answer, a CNAME at the probe name — is dropped uncached/unchased/undelivered and resolution continues; the impl's reveal+1 image for Q3a). The NEW ancestorDenied rule is the strict-mode terminal (RFC 9156 §3 (6d) / RFC 8020 §2 base SHOULD, consistent with the no-DNSSEC scope): an accepts-passing NXDOMAIN reply to a strict probe concludes NXDOMAIN for the FULL query and STOPS — no fuller name is ever sent — negative-caching keyed at the PROBE query (absorbNeg now pq; RFC 8020 §3.2's revision of RFC 2308 §5: the cached ancestor denial answers descendant queries), in trustedReply's trusted shape (arbitrary origin, RFC 5452 threat model) with the replacing/evicting cf0/cf write slots over an absorbNeg-only image (cf0 = c is the uncacheable-denial no-write case). Security posture: forging it needs the same id+port+full-question race as any spoof — probe names have fewer letters, so per-round 0x20 entropy is lower, id/port entropy unchanged — and the blast radius (subtree denial for the negative TTL) is exactly the RFC 8020 semantic, surfaced as a TrustedReplyNxdomain escape disjunct newly threaded through resolves_negcache_grounded/resolves_negHitNx_justified (resolves_nxdomain_justified already carried it; the TrustedReferralCache escape is now packed at the sent pq, and trustedReferral's hcut anti-poison bound is judged against pq.qname — the wire-facing gate). ex_strict_ancestor_denied is the right-disjunct walk: probing `MIL. A` for `WWW.FOO.MIL` gets an accepted NXDOMAIN and the client gets NXDOMAIN with no datagram carrying FOO or WWW ever sent. The impl flip (revealed loop parameter, buildSubQuery probe input, strict-NXDOMAIN terminal arm) is plan stages Q3a/Q3b — the pure resolver never sends, so Impl/ is untouched by Q2. Every decl rfc_proves-linked.
    Clarifications.lean -- RFC 2181 §4-§11: reply addressing, RRSet + TTL uniformity, zone cuts/authority, SOA, TTL range, TC bit, CNAME/PTR/MX/NS
    AcceptanceRules.lean -- RFC 5452 §3-§7: accept-iff-matches (proven accept⟹id/question/source match), in-domain-only, birthday/combined-difficulty
    ResourceModel1034.lean   -- RFC 1034 §3.6-3.7: RR fields, ttl=0-not-cacheable, CNAME alias discipline, query/response trichotomy
    ResolverInternals1034.lean -- RFC 1034 §4.3.2-3.5, §5.1-5.3: query modes, wildcards, SOA timers, alias chasing, bounded work
    Examples1034.lean        -- RFC 1034 §6: worked-example *shape* facts (older style: asserts a hand-written response then proves its shape). Superseded for trace fidelity by NetworkTraces.lean, which derives the response from the ServerAnswers relation.
    Rdata1035.lean / Misc1035.lean / Misc1035b.lean -- RFC 1035 §3.3/§3.4 RDATA formats, §5 master files, §6/§7 resolver processing
    Misc1034.lean / Misc1034b.lean -- RFC 1034 §2/§3/§4/§5 remaining prose coverage
    NegativeCacheClarify.lean / CachingTraces.lean / Misc2308.lean -- RFC 2308 NXDOMAIN/NODATA, caching, worked example
    Misc_final.lean     -- final prose-residual coverage sweep across RFC 1034/1035/2308
  Test/
    Loop.lean     -- Mock-socket compile-time (#guard) verification of serveOne/resolveWithIO
    AdequacyPins.lean -- Executable mirrors of the liveness/adequacy theorems (docs/liveness-plan.md L4/L5): Prog.run against mkHonestOracleAddr/twoServerRespond (the proof layer's own cooperative-network objects) pins the depth-1 two-server descent (byte-exact answer, restored question, exactly two rounds via idCtr), the NXDOMAIN and flat-authoritative variants, and the MockM serve-path scenario
    ExchangeJunk.lean / ExchangeJunkMain.lean -- Runtime FFI test (lean_exe exchange-junk-test): a loopback mock injects junk datagrams from a third source before/instead of the real reply; asserts veri_dns_exchange skips them (review #017). Main split out of the lib to avoid clashing with VeriDNS.Main's `main`.
  Impl/
    Parsec.lean         -- DnsParser/DnsSerializer monads + byte-level primitives
    BitPacking.lean     -- Sub-byte field pack/unpack (Header flags)
    Enum.lean           -- Opcode/Rcode/RRType/RRClass/Qtype/Qclass ↔ Nat
    DomainName.lean     -- Domain name decode/encode with compression (§4.1.4)
    Header.lean         -- Header decode/encode (12 fixed bytes)
    Question.lean       -- Question decode/encode
    RData.lean          -- All 16 RDATA types decode/encode
    ResourceRecord.lean -- ResourceRecord decode/encode
    Message.lean        -- Full DNS message decode/encode
    Cache.lean          -- Concrete DnsCache type + CacheSpec instance
    SList.lean          -- Concrete DnsSList type + SlistSpec instance. setUpAddresses = fromNsWithGlueAll: ALL-ADDRESSES per NS host (RFC 1034 §5.3.3 — a real resolver tries every known address of a nameserver), not first-per-host; glueless hosts kept as address-less entries. Glue owner↔NS name matched CASE-INSENSITIVELY via nameEqCI (RFC 1035 §2.3.3). (fromNsWithGlue, the first-per-host form, retained for legacy proofs.)
    Resolver.lean       -- Fuel-bounded resolver with NS walking, delegation (4b), CNAME chasing with chain accumulation (4c)
    Edns.lean           -- EDNS0 (RFC 6891): OPT pseudo-RR carrier (optRRBytes), advertisedUdpSize 1232, clientCap (reply budget), stripOpt (receive-side OPT scrub). See "EDNS0" below.
    UdpSocket.lean      -- @[extern] FFI (socket/bind/sendto/recvfrom) + UdpSocket IO instance
    Server.lean         -- Iterative resolution IO shim, SBELT-based server loop
  Proof/
    Enum.lean           -- Enum roundtrips (by cases; complete)
    BitPacking.lean     -- pack/unpack roundtrip (bv_decide; complete)
    Parsec.lean         -- BitVec ↔ UInt conversion roundtrips (complete)
    Primitives.lean     -- Parser/serializer equational lemmas + byte access helpers (complete)
    DomainName.lean     -- Domain name roundtrip theorems (complete)
    Header.lean         -- Header roundtrip theorem (complete)
    Question.lean       -- Question roundtrip theorem (complete)
    RData.lean          -- RData roundtrip theorems: A, CNAME, HINFO, MX, SOA (complete)
    ResourceRecord.lean -- ResourceRecord roundtrip theorem (complete)
    Message.lean        -- Full message roundtrip theorem (complete; Appends framework + frame lemmas + decodeMany induction)
    MessageValid.lean   -- Decode-side validity: decode's output satisfies every decode_encode hypothesis; end-to-end decode_encode_of_decode (complete)
    Resolver.lean       -- RFC conformance proofs: SBELT fallback, ID match, dispatch, loop trace soundness (StepSpecStar), pause inversion, needsIO, step relation soundness, response coverage (all complete)
    Server.lean         -- buildResponse/truncateUdp properties (cap-parametric since EDNS0: truncateUdp_no_trunc baseline + truncateUdp_no_trunc_cap), RFC 5452 datagram gate (complete)
    NameTreeComplete.lean -- Completeness: resolveWithIO_complete — untruncated answers deliver treeResolve's verdict whole (RRset indivisibility end-to-end; complete)
    Refinement.lean     -- Forward-simulation abstraction layer: αResp/αRR/αType/αSection/αQuery (αType/αRData TOTAL over type codes since RFC 3597 T5), the codec/bridge lemmas, HasVerdict, the Net.Resolves producers, resolveWithIO_simulates (cache branches unconditional since D2 closure 2026-07-11 — the cache-hit disjunct carries impl-level invariants, not a served-set oracle; the network disjunct is discharged at the FreeIO layer by ioResumeLoop_sound)
    AnswerTerminal.lean -- Extracted from Refinement (2026-06): αSection faithfulness (αSection_ne_nil/_nil_imp/_mem), query-type/αType bridges, and positive_answer_covered — the answer-terminal covered-record glue the forward-sim driver consumes
  Main.lean       -- Executable entry point: shared-cache UDP + TCP servers on port 5300 (see "Driver Concurrency")
```

## include_rfc Pipeline

1. Parser reads raw text from `rfc/rfc-{num}.txt`
2. Extracts lines in the given range
3. Strips page break artifacts (footer, form feed, header, surrounding blanks)
4. Strips trailing whitespace per line
5. Compares normalized text against user-provided block
6. Compile error on mismatch with line-by-line diff

## RFC Coverage Links (RFC/Check.lean)

Four commands map RFC prose to the formalization and drive the coverage view +
blueprint colouring:

- `include_rfc [num][from:to] { text }` — compile-time assertion that `text`
  matches the RFC lines verbatim (the pipeline above).
- `check_rfc_doc <decl> [num][from:to]` — links a *documented* declaration whose
  docstring must be an excerpt of the RFC range (compile-checked). Use for the
  statement/model side (a predicate, structure, or spec `def`).
- `rfc_proves <decl> [num][from:to]` — links any declaration to a range (no
  docstring/type obligation); the remap tool for pointing a range at a real
  theorem.
- `rfc_out_of_scope [num][from:to]` — declares a range outside the formal model
  (administrative/operational/advisory prose); excluded from the coverage
  denominator.

**Honest status colouring.** A span/node's colour comes from
`Pseudoprint.declStatusName`, which classifies by *what the declaration is*, not
merely by `sorry`-reachability:
- a **proof** (its type is a `Prop`, i.e. a theorem) → green if sorry-free, else blue;
- a bare **axiom** → blue;
- a **statement/predicate** (type *produces* `Prop` but asserts nothing, e.g.
  `def p : A → Prop`) → blue (*stated but unproven*) unless discharged;
- a **data/type definition** → green.

This is what stops specification predicates (e.g. `node_label_size`) from
masquerading as proven.

**Statement + proof via `via`.** Both `check_rfc_doc` and `rfc_proves` accept an
optional `via <proofThm>` clause:

```
check_rfc_doc VeriDNS.Spec.node_label_size [1034][362:365] via VeriDNS.Spec.exampleNameSpace_root_label_size
```

This registers `proofThm` as *discharging* the statement (via
`Pseudoprint.registerDischarge`), so the statement node renders green, its
coverage span takes the proof's status, and a "proven by `proofThm`" citation is
attached to the statement for navigation. A discharged statement without a
sorry-free proof stays blue.

## Diagram Types

The pipeline handles two diagram formats:

- **Bit diagrams** (`+--+--+`): Field-level layouts with precise bit widths.
  Generates structures with `BitVec` fields and inductive types for enums.
  Multiple diagrams in the same section are parsed as separate groups
  (`DiagramGroup`): the first is the definition, subsequent ones are examples.
- **Section diagrams** (`+-----+`): High-level message structure with named
  sections. Generates structures with resolved types (environment lookup) and
  `Array` wrapping via grammatical parsing (NLP.lean). The NLP pipeline parses
  inline descriptions and prose into Subject-Verb-Object clauses, derives
  `SectionProp` values (e.g., `alwaysPresent`, `pluralHead`, `containsPlural`),
  then uses those to decide singular vs. Array wrapping.

## Formal Prop Generation

Properties are generated via a declarative `PropSpec` expression tree system.
Two rule kinds cover all property shapes:

### Field-Level Rules

Field description sentences are NLP-parsed into `Clause` structures, then
matched against registered `field_prop_rule` declarations.

Props are named by clause index (`{field}_prop_{i}` where `i` is the clause
position), not by dense counter. Skipped clauses leave gaps (e.g., `aa_prop_0`,
`aa_prop_2` with no `_1`). This aligns with `pushSentenceHoverInfo`'s
`sentenceIdx` so hover links point to the correct prop.

All generated prop docstrings include the pretty-printed formal Lean term
in a fenced code block for hover display.

```lean
field_prop_rule {
  name := "zero_adj"
  pattern := .adjEquals "zero"
  prop := .forallStruct (.eq .currentField (.lit 0))
}
```

`ClausePattern` variants:
- `.adjEquals adj` — matches `SVAdj` clauses with the given adjective
- `.hasWord word` — matches `npOnly` clauses with word in preAdjs/head
- `.textPrefix pfx` — matches `unparsed` text starting with prefix
- `.textContains word` — substring match across all clause types (unparsed text,
  participle verbs, PP heads, relClause text)

Unmatched clauses are skipped (no `True` props emitted).

`PropSpec` extensions for cross-message properties:
- `.forallPair body` — `∀ (a b : Struct), body` (two-message quantification)
- `FieldRef.pairLeft`/`.pairRight` — project fields from left/right binder

This enables behavioral specs like field copying between query and response:
`∀ (a b : Header), a.qr = 0 ∧ b.qr = 1 → a.id = b.id`

### Cross-Struct Rule Framework

Properties that reference fields across structures (e.g., "QDCOUNT specifying
the number of entries in the question section") are resolved via a declarative
rule system using `SimplePersistentEnvExtension`:

**PropRules.lean** defines:
- `FieldRef` — reference to a value in the generated prop (field projections,
  bound variables, literals, PP resolution, extracted bindings, cross-spec fields)
- `PropSpec` — composable expression tree describing prop shapes (includes
  `.declField` for struct field declarations and `.seq` for sequencing)
- `ParticiplePattern` — declarative match spec: verbs, optional object head,
  required PP (prep, head) patterns
- `ClausePattern` — match spec for field descriptions
- `ProseClausePattern` — match NLP Clause structure (verb, subject, PPs)
  with value extraction via `ValueSlot` / `Extraction`
- `CrossStructRuleEntry` / `FieldPropRuleEntry` / `ProseClauseRuleEntry` — bundle pattern + PropSpec
- `cross_struct_rule` / `field_prop_rule` / `prose_clause_rule` commands — register rules

**Syntax.lean** registers rules and interprets PropSpec trees:
```lean
cross_struct_rule {
  name := "count_entries"
  pattern := { verbs := #["specifying", "specifies"],
               objHead := some #["number"],
               requiredPPs := #[("of", #["entries", "records"])] }
  prop := .forallStruct (.eq (.toNat .matchedSubField) (.size (.resolvedFromPP "in")))
}
```

At elaboration time, `generateCrossStructProps` queries the extension, matches
each sub-struct field's NLP-parsed docstring against registered rules, and
interprets the PropSpec tree into Lean syntax:
- Count props: `∀ (msg : Format), msg.header.qdcount.toNat = msg.question.size`
- Domain name validity: `∀ (msg : Format) (i : Fin ...), ∃ labels, ∀ l ∈ labels, ...`

New property shapes require only new rule declarations — no interpreter changes.

### Structured NLP PostMods

The NLP pipeline parses post-modifiers of noun phrases into typed structures
(`PostMod`) instead of raw strings:

- `PostMod.pp` — prepositional phrases with parsed NP objects
- `PostMod.participle` — participial phrases with verb, object NP, and PP chain
- `PostMod.relClause` — relative clauses with pronoun and clause text
- `PostMod.raw` — unparseable fallback

Cross-struct rules match against `PostMod.participle` structure declaratively
via `ParticiplePattern` rather than hardcoded conditionals.

## Prose-Only Section Derivation

Sections without diagrams (e.g., 3.1 Name space definitions, 4.2 Transport)
go through the full NLP pipeline to derive structure fields and constraints:

1. Parenthetical stripping removes inline clarifications
2. Sentences are tokenized and POS-tagged (lexicon + morphology + disambiguation)
3. Clauses are parsed as SVO, passive (S + copula + participle + PPs), or SVAdj
4. `parseProseClauses` returns raw `Array Clause` (deduplicated, unparsed filtered)
5. `prose_clause_rule` rules match clause structure directly:
   - `ProseClausePattern` specifies verbs, subject head, required PPs
   - `ValueSlot` / `Extraction` extract values (`.ppNumeric`, `.ppBitWidth`, etc.)
   - Output is a unified `PropSpec` tree: `.declField` for struct fields,
     `.forallStruct` for props, `.seq` for both
6. `deriveStructFields` still handles "expressed as sequence of X" → `.structField`
7. Bindings are shared across rules (e.g., size_bound's "value" aliased as "threshold")

Generates structures like `NameSpace { labels : Array ByteArray }` with
element-level bounds, and transport structures like `UdpUsage { data : ByteArray }`
with size constraints and cross-spec reference props.

### Predicate emission (no closed ∀ over free structs)

A closed `∀ (msg : Struct), …` Prop over a free generated struct is
unprovable — any `mk` value refutes it — so EVERY rule-derived prop is
emitted as a PREDICATE: the interpreters (`interpretPropSpecForField`,
`interpretPropSpec`, `interpretPropSpecForProse`,
`interpretPropSpecForAlgorithm`) turn the outer `.forallStruct` /
`.forallPair` / `.forallNamed(Pair)` quantifiers into LAMBDAS, and the
emitters drop the `: Prop` ascription, giving `Struct → Prop` (or binary)
defs that implementations instantiate at the values they construct.
Identical prop bodies within a section are deduplicated (two sentences
matching the same rule with the same extracted bound). The
`domain_name_valid` cross-struct rule additionally turns its `∃ labels`
(which would be vacuously satisfiable by `#[]`, disconnected from the
message) into an abstract label-decomposition FUNCTION parameter:
`format_question_qname_valid (labels : ByteArray → Array ByteArray)
(msg : Format)`.

Instantiation sites (Proof/): the four `format_*count_counts_*` predicates
are `decode_encode`'s count hypotheses (Proof/Message.lean), discharged on
the decode side by `run_decodeMany_size` (Proof/MessageValid.lean);
`format_question_qname_valid` ← `validQuestions_qname_valid` (labels :=
the wire-format decoder); `rdlength_prop_0` ← `ResourceRecord.decode_encode`'s
`hrl`; `udpusage_prop_0/1` ← `truncateUdp_udpusage(_tc)`; `z_prop_0` /
`aa_prop_0` / `id_prop_1` ← `emitted_z_conforms` / `emitted_aa_conforms` /
`response_id_conforms`; `algorithm_prop_1` ← `accept_id_conforms`;
`namespace_prop_0` ← `decodeName_namespace_conforms`; `qr_semantics_0` /
`rcode_nameError_semantics` / `rcode_serverFailure_semantics` ←
`server_qr_semantics` / `localAnswer_nameError_semantics` /
`hygiene_serverFailure`; `tc_semantics_0` ← `truncate_tc_semantics` (the
oversize condition is genuinely due whenever truncation emits, via
`truncateUdp_flag_iff`); `Trustworthiness.atLeastAsTrustworthy` is the
ranking vocabulary of `storeChecked_no_downgrade`'s hypothesis. Still
uninstantiated: `tcpusage_prop_0` (no TCP framing in Impl — the server is
UDP-only) and `algorithm_prop_2` (TTL positivity; no impl event enforces
it). `guard_delegation`/`guardRefined_delegation`/
`guardRefined_answerOrNameError` are consumed INSIDE the generated
obligation definitions — a zero-grep-hit guard name is not a bypass.

### Negation and Disjunction

`PropSpec` supports `.neg` (¬) and `.disj` (∨) constructors. The
`ProseClausePattern` `requireNegation` flag ensures rules only fire on
negated passive clauses (where the VP adverb is "not" or "never"). The NLP
`Clause.svPassive` carries a `negated : Bool` field derived from VP adverb
analysis.

**Closed props over free structs are unprovable** — `∀ msg, msg.cacheable
= 0` is refuted by any `mk 1` value — so negated-prohibition rules
(`should_not_cache`, `never_combine`, `expired_ignore`) emit only their
modeling `declField`; the CONSTRAINTS are emitted as parameterized Props
over abstract predicates (the `discard_unrequested` convention), which
implementations instantiate:

- **Conditional no-cache frame** (`emitProseParamProps`): a when-clause
  whose passive participle names the guard + a negated modal over a
  stateful action verb (closed-class `statefulActionVerbs` lexicon) →
  `{struct}_{guard}_not_{action}d (κ ρ) (guard : ρ → Bool)
  (act : κ → ρ → κ) : ∀ c r, guard r = true → act c r = c`
  (§7.4 truncation → `usingthecache_truncated_not_cached`).
- **Two-source preference frame** (`emitProseParamProps`): correlative
  "either ⟨NP⟩ or ⟨NP⟩" + copula + participle names the sources and the
  kept set (a generic head defers to its in-PP complement: "the data in
  the response" → `response`); the anaphoric "the two" under a negated
  modal passive forbids mixing → `{struct}_never_{participle} (ρ)
  (s₁ s₂ kept : ρ → Prop) : (∀ r, kept r → s₁ r) ∨ (∀ r, kept r → s₂ r)`
  (§7.4 → `usingthecache_never_combined`).
- **Glossary discard-old frames** (`inferClassFromClauses` →
  `ClassSpec.paramProps`, emitted by `generateGlossaryClass`): an
  ignore/discard verb (possibly the second arm of a "V or V" cluster)
  whose object NP carries a premodifying adjective and plural head
  ("ignores or discards OLD RRs") names the guard; each discarding event
  — the when-clause's in-PP through a transparent noun ("in the COURSE OF
  a search"; `transparentOf` gained "course") or the during-PP's
  recurring plural event — yields `cache_{event}_{verb}s_{adj} (ρ)
  (old p : ρ → Bool) : ∀ r, old r = true → p r = true`
  (→ `cache_search_ignores_old`, `cache_sweep_discards_old`).
- **Absolute-time law** (same convert-frame that derives `storeAt`):
  converting an interval to an absolute time at store time `t` is
  addition → `cache_storeAt_absolute (κ ρ) (interval : ρ → UInt32)
  (storeAt : κ → ρ → UInt32 → κ) (holds : κ → ρ → UInt32 → Prop) :
  ∀ c r t, holds (storeAt c r t) r (t + interval r)`.

## Example Sentence Analysis

Example sentences in RFC prose (e.g., "For example, if PROTOCOL=TCP (6),
the 26th bit corresponds to TCP port 25") are parsed into formal `Prop`
definitions via `NLP.analyzeExamples`:

1. Tokenizer splits with offset tracking and abbreviation lookahead ("e.g.", "i.e.")
2. POS tagger adds `discMarker` ("For example") and `subConj` ("if"/"when")
3. Conditional examples are split into antecedent/consequent at comma boundaries
4. Antecedent: `NOUN = NOUN ( NUM )` → `ExamplePred.fieldEq field value`
5. Consequent: field resolution + numeric extraction → `ExamplePred.fieldAccess`

Generated as:
```lean
def wksrdata_example_0 : Prop :=
  ∀ (w : WksRdata) (getBit : ByteArray → Nat → Bool),
    w.protocol = 6 → getBit w.«<bit map>» 25 = true
```

## Example Diagram Generation

Example diagrams (subsequent groups after the definition diagram) are
parsed cell-by-cell into `ByteArray` literals:

- Single-digit cells → numeric byte values (e.g., "1" → 1)
- Single-letter cells → ASCII byte values (e.g., "F" → 0x46)
- Multi-digit cells → numeric values (e.g., "20" → 20)
- Bit markers ("1  1") and empty cells → skipped

Generated as `def {struct}_example_{i} : ByteArray := ⟨#[...]⟩`.

## Glossary Parsing

Sections with glossary-format definitions (e.g., RFC 1034 §5.3.2: `NAME  description`)
use a dedicated parser path:

1. `parseGlossaryList` detects lines where first word is ALL-CAPS, followed by 2+ spaces,
   and second token is NOT a number. Continuation lines at indent ≥ 16.
2. `resolveGlossaryFieldTypes` resolves each description to a Lean type via NLP keyword
   table ("domain name" → `ByteArray`, "QTYPE" → env lookup `Qtype`, "same form as X" →
   cross-reference) and environment lookup.
3. `generateStructure` creates the struct with resolved field types.
4. Intro prose (text before first glossary entry) is parsed via `prose_clause_rule` matching.

### Glossary Typeclass Derivation

Glossary entries whose descriptions say "a structure which stores/describes ..."
are too abstract for concrete struct fields. Instead of falling back to `ByteArray`,
the pipeline derives abstract typeclass specs via full NLP inference — the
grammatical clause structure directly determines method signatures, abstract type
parameters, and axioms.

**Trigger**: glossary description contains "structure which" or "structure that".

**Pipeline**:
1. Description → `NLP.parseProseClauses` → `Array Clause`
2. For `.npOnly` clauses with `.relClause` PostMods → `NLP.reparseRelClause`
   re-parses the relative clause text into proper SVO clauses (prepends implicit
   "it" subject for verb-first text, splits coordinated objects on "and")
3. `inferClassFromClauses` maps each clause to a `MethodSpec`:
   - **SVO → Method**: verb stem = method name, object NP = type parameter or
     arg type, Self-returning vs getter inferred from verb semantics
   - **RelClause → Predicate**: "whose X has Y" → accessor + predicate
   - **Implied pairs**: `store X` → `entries` getter + `store_mem` axiom
4. `ClassSpec` → `generateGlossaryClass` → `class` declaration via
   `elabCommandStr` (string-based code generation for robust `Type` handling)
5. "same form as X" entries share the referenced entry's class
6. Polymorphic parent struct generated with type params + instance binders

**Type resolution** (`resolveNPType`): env lookup first → DNS domain mappings
("domain name" → `ByteArray`, "address" → `BitVec 32`) → abstract type param.

**Method naming** (`deriveMethodName`): verb stemming with multi-word idiom
detection ("keeps track" → `keepTrack`). Deduplication suffixes object noun
when multiple clauses produce the same verb stem.

**Example output** (RFC 1034 §5.3.2):
```lean
class SlistSpec (S : Type) (NS : Type) where
  describeServers : S → Array NS
  describeZone : S → ByteArray
  keepTrack : S → NS → S
  zoneName : S → ByteArray

class CacheSpec (C : Type) (RR : Type) where
  store : C → RR → C
  entries : C → Array RR
  store_mem : Prop

structure Resources (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where
  sname : ByteArray; stype : Qtype; sclass : Qclass
  slist : S; sbelt : S; cache : C
```

## Algorithm Step Parsing

Sections with numbered algorithm lists (e.g., RFC 1034 §5.3.3) use a dedicated parser path:

1. `parseNumberedAlgorithm` detects top-level (`   N. description`) and sub-level
   (`         a. description`) items. Parsing stops after sub-steps end and prose begins.
2. `deriveConstructorName` extracts verb + object from step descriptions via NLP
   (e.g., "See if the answer..." → `checkAnswer`, "if the response shows a CNAME" →
   `cname`).
3. `generateAlgorithmTypes` creates:
   - `inductive {Name}Step` — one constructor per top-level step
   - `inductive ResponseAction` — one constructor per sub-step
   - `structure Transition` with `from`, `action`, `to` fields
   - `def {name}_transition_{i}` constants from "go to step N" targets
4. Algorithm prose paragraphs are parsed via NLP-driven property derivation.

### Algorithm Property Generation

The algorithm path derives formal `Prop` definitions from detailed prose paragraphs
by parsing them through the NLP pipeline with conditional sentence awareness:

1. `extractAllProse` joins all algorithm paragraph text (past the numbered list).
2. `NLP.parseAlgorithmClauses` splits on ". " and "; ", then for each fragment:
   - Detects `if`/`when` subordinating conjunctions
   - Splits conditionals at comma boundaries (depth-aware) into guard/body pairs
   - Strips leading "then"/"and" connectors from body tokens
   - Handles postposed conditionals ("cache the data if its TTL > 0")
   - Returns `ConditionalClause.conditional guard body` or `.simple clause`
3. `collectContextTypes` gathers all structure/inductive types in the current namespace.
4. `deriveAlgorithmProperty` matches clause structures against patterns:
   - **Copula SVO with comparative**: "X is greater than zero" → `∀ x, x.field > 0`
   - **SVO with "matches" verb + domain guards**: "response matches query using ID"
     → `∀ (a b : Header), a.qr.toNat = 1 ∧ b.qr.toNat = 0 → a.id = b.id`
     (uses `aliasDomainWordGuarded` to distinguish query/response via QR field,
     `pairLeft`/`pairRight` FieldRef constructors to select the correct binder)
   - **SVO with "from" PP**: "initializes SLIST from SBELT"
     → the field equation `slist = sbelt` over `Resources`
   - **SVAdj with comparative + "than" PP**: numeric comparisons
   - **Conditional**: if both sides resolve, an implication; if only the
     GUARD resolves, the guard is the property. If only the BODY resolves,
     the antecedent is NOT dropped (an unconditional reading of a
     conditional sentence is false in general — it produced a vacuous
     `algorithm_prop_0`): the emitter abstracts it as a predicate parameter
     over an abstract state σ, with the body's struct reached through a
     post-state projection:
     `def algorithm_prop_0 (σ : Type) (S C NS RR : Type) [SlistSpec S NS]
     [CacheSpec C RR] (searchForNSRRsFails : σ → Prop)
     (resourcesAfter : σ → Resources S C NS RR) : Prop :=
     ∀ st, searchForNSRRsFails st → (resourcesAfter st).slist =
     (resourcesAfter st).sbelt`. The guard's name is derived grammatically
     (`predNameOfClause`: subject head + subject postmodifier PPs + an
     intransitive verb).
5. `resolveNPToField` resolves NP heads to types/fields:
   - ALL-CAPS words → field name search across context types
   - Capitalized words → type name lookup in environment
   - Domain aliases with guards ("response" → `Header` + qr=1, "query" → `Header` + qr=0)
   - General field name search across all context types
6. `walkFieldPath` performs one-level nested field resolution (e.g., `Header.id`
   from `Format.header`).
7. Non-polymorphic types generate syntax-quotation props; polymorphic types
   (like `Resources S C NS RR`) use string-based elaboration via
   `renderPolymorphicPreamble` which extracts type params and instance constraints
   from the `Expr`, resolving de Bruijn indices to parameter names.

**POS tagger enhancements** for algorithm prose:
- Verb `-s` inflection: "matches" → verb (stem + known-root check)
- Comparative adjective `-er`: "greater" → adj (stem in `knownAdjs`)
- `"than"` recognized as preposition for comparative constructions
- Verb-after-determiner disambiguation: "the search" → noun (not verb)
- Pronoun handling: "its" tagged as determiner; compound noun loop breaks on
  pronouns ("it", "they", etc.) so "the query it sent" → NP(head="query")

## Value-List Parsing

Sections with enumeration lists (e.g., TYPE values, CLASS values) use a
dedicated parser path:

1. `parseValueList` detects lines matching `NAME  code  description` patterns
2. `generateValueListType` creates an `inductive` type with one constructor per entry
3. Lean keyword conflicts are avoided: `Type` → `RRType`, `Class` → `RRClass`

## RFC Text Hover Mapping

The `include_rfc` parser (`rfcTextBodyFn` in Macro.lean) segments the verified
RFC text into atoms and idents with `.original` source info at exact byte
positions. Idents receive `TermInfo` entries (via `pushInfoLeaf`) pointing at
generated declarations, so both the editor infoview and SubVerso/Verso HTML
render hovers for RFC text. Split-point detectors per section type:

- **Field names** (`findFieldSplitPoints`): where-block names → struct field
  projections (`pushHoverInfoFromIdents`).
- **Description sentences** (`findSentenceSplitPoints`): ". "/".\n" boundaries
  within field descriptions → clause-indexed props (`pushSentenceHoverInfo`;
  sentence index aligns with `{field}_prop_{i}` clause naming).
- **Glossary entries** (`findGlossarySplitPoints`): entry names → derived
  typeclass or parent struct field (`pushGlossaryHoverInfo`).
- **Value-list entries** (`findValueListSplitPoints`): entry names → enum
  constructors (e.g., `NS` → `RRType.ns`).
- **Prose sentences** (`findProseSentenceSplitPoints`): for sections without a
  where-block, sentences in prose paragraphs become idents. Scanning skips the
  title and diagram-ish lines, never spans blank lines, and stops before the
  first glossary/value-list entry so entry names stay separate idents.
- **Section title / diagram / example triggers**: single idents → the struct.

Overlapping split points are deduplicated by sorted offset (longer preferred
at equal offsets).

Prose-derived props (prose-clause rules, algorithm properties, glossary intro
props) are linked by **source-text matching** rather than index alignment:
`parseProseClausesWithSrc` / `parseAlgorithmClausesWithSrc` pair each clause
with its source sentence fragment, `processRfcText` returns
`(propName × srcSentence)` pairs, and `pushProseHoverInfo` attaches each prop
to the first ident whose normalized text (parentheticals dropped, whitespace
collapsed, lowercased) contains the source fragment. Numeric limit constants
(`extractConstraintValues`) and ranked-list enums + their order relation
record their matched source phrase the same way, including on the
no-struct fallback path.

**One hover per token — claim map.** SubVerso renders exactly one `TermInfo`
per token, so when several definitions derive from the same sentence (a
refined guard and its obligation, `{field}_prop_i` and `{field}_semantics_i`,
a ranked enum and its order relation), only one can own the hover. All
pushers thread a shared `HoverClaims` map (ident byte position → owning
declaration) through `claimHover`: the first definition claims the ident,
and every later definition landing on a claimed ident is appended to the
owner's docstring under "**Also generated from this passage**" with its
pretty-printed form (`ppGeneratedDecl`: zero-binder `Prop` defs show their
body, parameterized defs their type, inductives their constructor list).
Push order = priority: prose props → sentence props → example props →
generic struct/field fallback on unclaimed idents only. Every generated
definition is therefore reachable from some hover on the passage that
produced it.

**Stale-cache warning**: Verso HTML pages reference hover docstrings by
sequential numeric id into a site-wide `-verso-docs.json` table. Pages and the
table must come from the same render: a browser caching one but not the other
(or a partial regeneration over a stale `.lake/build/literate/` cache) shifts
every id, making hovers show neighboring declarations (e.g., QR displaying
`Header.z`). After changing metaprogramming code, delete BOTH
`.lake/build/literate/` and `.lake/build/literate-html/` before
`lake query :literateHtml`, and hard-refresh the browser.

## Bit Width Resolution

When both diagram and where-block specify bit widths, the where-block takes
precedence. This handles cases where the diagram shows a simplified view
(e.g., A record's ADDRESS shown as one 16-bit row but described as "32 bit")
or where `mergeDiagramFields` incorrectly merges unnamed cells (e.g., WKS
PROTOCOL shown as 8 bits but adjacent unnamed cells inflate it).

## Wire-Format Implementation (Impl/)

The `Impl/` layer implements DNS wire-format parsing and serialization against
the Spec types generated by `include_rfc`.

### Parser/Serializer Monads

- **DnsParser**: `ByteArray → Nat → Except String (α × Nat)`.
  A function type (not a monad transformer stack) taking buffer and position,
  returning either an error or the parsed value with the new position. This
  design makes equational reasoning trivial (`DnsParser.run p buf pos = p buf pos`
  by `rfl`). The full message ByteArray is passed for compression pointer
  following (§4.1.4).
- **DnsSerializer**: `StateM ByteArray`. Appends bytes to a growing buffer.

### Domain Name Compression (§4.1.4)

`decodeNameAux` uses fuel-bounded recursion to follow compression pointers.
The top 2 bits of a length byte select: `00` = label, `11` = pointer.
Pointer case records the end position (2 bytes consumed) and follows the
14-bit offset. Fuel is bounded by `buf.size` to prevent infinite loops.

### Bit Packing (Header Flags)

Bytes 2–3 of the DNS header encode 8 sub-byte fields in 16 bits:
`QR(1) OPCODE(4) AA(1) TC(1) RD(1) | RA(1) Z(3) RCODE(4)`.
`packFlags` builds the word with shifts and OR; `unpackFlags` extracts
fields with shifts and truncation.

## Conformance Proofs (Proof/)

Roundtrip theorems state that for each type T:
`DnsParser.run decode (DnsSerializer.runBytes (encode x)) = .ok (x, wireSize x)`

**Complete proofs** (no sorry):
- Enum: all 6 enum types, by `cases`/`rfl`
- BitPacking: `unpack_pack` via `bv_decide` (SAT-based bitvector reasoning)
- Parsec: BitVec ↔ UInt conversion roundtrips via `simp`
- Primitives: read/write roundtrips for BV8, BV16, BV32, UInt16; equational lemmas
  for `DnsParser.run` (bind, pure, map, getPos, setPos, getBuffer, fail);
  composite helpers (`readBV32_at`, `byte_at_suffix`) for multi-field proofs
- DomainName: decode/encode roundtrip via structural induction on labels with
  frame lemma for parsing in the presence of prefix/suffix bytes
- Header: mega-simp proof composing primitive, enum, and bitpacking roundtrips
- Question: domain name frame lemma + BV16 byte access proofs
- RData: A (fixed 4 bytes), CNAME (raw wire format), HINFO (length-prefixed
  strings), MX (BV16 + domain name), SOA (two domain names + 5×BV32 via
  `readBV32_at` + `byte_at_suffix`)
- ResourceRecord: domain name + 10 fixed bytes + variable rdata extract

- Message: full message roundtrip (`decode ∘ encode = id`), complete. The
  implementation's `for` loops were replaced by structurally recursive
  `decodeMany`/`encodeList` (same semantics) so proofs can induct directly.
  Infrastructure:
  - **Appends framework**: `Appends s bytes` states a write-only serializer
    appends a fixed byte string from any initial buffer; compositional via
    `appends_seq`, giving `encode_eq` (encoder output = header bytes ++
    concatenated per-item encodings).
  - **Frame lemmas**: `header_frame` (header decode ignores trailing bytes),
    `question_frame` (question decode at any position via the domain-name
    frame lemma + byte_at_suffix).
  - **Sequential parse induction**: `run_decodeMany` — parsing n items from
    concatenated encodings recovers all items, given a per-item frame property.
  - **Validity hypotheses**: `ValidQuestions` (label decompositions);
    `ValidRRBytes` restated as the canonical fixed-point property
    (`decodeRRCanonical` reproduces the stored bytes exactly) — the previous
    `ResourceRecord.decode`-based statement was too weak because `decode`
    canonicalizes RRs while `encode` writes them raw.

- **MessageValid (Proof/MessageValid.lean)**: the `decode_encode`
  hypotheses are PROVEN for everything `decode` accepts — they are no
  longer assumptions at the system boundary:
  - `decodeNameAux_validLabels` / `run_decodeName_validLabels`: every label
    the name decoder produces has length 1–63 (positivity + the ≤63 guard);
  - **RFC 1035 §2.3.4 ≤255-octet name cap**: `decodeName` post-checks
    `encodedNameLen labels ≤ 255` (after decompression) and fails otherwise —
    bounding compression-pointer amplification (a crafted name can expand
    ~64× before the cap: re-encoded size ≤ `buf.size · 64`) so a decompression
    bomb cannot bloat the cache or overflow the 16-bit rdlength field.
    `run_decodeName_le255` (axiom-clean) is the payoff: every decoded name is
    ≤255 octets, threaded through `CanonicalRR`/`ValidQuestions`/`WfRR` so the
    re-encode round-trip (`decode_encode_of_decode`) stays total — its axiom
    footprint is UNCHANGED by the cap (no new TCB);
  - `run_decodeMany_size` / `run_decodeMany_mem`: `decodeMany` returns
    exactly the requested count, and every returned element is an output of
    the item parser — so the header counts match the section sizes and
    per-element properties lift to sections;
  - `run_decodeRRCanonical_shape`: every `decodeRRCanonical` output has the
    canonical shape `rrWire` (valid owner labels + 10 fixed bytes with true
    RDLENGTH + branch-shaped rdata, `CanonicalRdata`);
  - `rrWire_frame`: canonical RR bytes embedded at ANY position re-parse to
    exactly themselves (the `ValidRRBytes` frame property), by the
    name-decoder frame lemma, ten byte-access lemmas over the fixed fields,
    `bv_decide` byte-reassembly identities, and per-branch rdata frames;
  - `decode_encode_of_decode`: anything `decode` accepts survives the
    encode/decode roundtrip END-TO-END, with no side conditions.

### Resolver RFC Conformance (Proof/Resolver.lean)

Proofs that the fuel-bounded resolver state machine conforms to NLP-generated
algorithm properties from RFC 1034 §5.3.3:

- **SBELT fallback** (`impl_algorithm_sbelt_fallback`): instantiates the
  regenerated `algorithm_prop_0` ("If the search for NS RRs fails, then the
  resolver initializes SLIST from the safety belt SBELT"). The failure event
  (`nsSearchFails`: the cache walk finds no NS RRs AND the current SLIST has
  no closer knowledge) and the post-state projection (`findServersState`)
  instantiate the prop's abstract antecedent and `resourcesAfter` parameters;
  the conclusion `slist = sbelt` is proven against the real fallback branch
  of `stepFindServers`. (The earlier unconditional `algorithm_prop_0` was
  false of real states and its "proof" had been weakened to a vacuous
  `∨ True`; the generator now abstracts unresolvable antecedents instead of
  dropping them — see Algorithm Property Generation.)
- **ID preservation** (`stepAnalyzeResponse_preserves_id`): when `stepAnalyzeResponse`
  returns an answer, its header ID equals the input response's header ID. Handles
  all response branches (4a answer, 4a name error, 4b delegation, 4c CNAME, 4d
  server failure). Proof by nested `split at heq` with `StepResult.answer.injEq`.
- **Step dispatch**: four theorems (`step_*_dispatch`) proving `step` correctly
  dispatches to the corresponding step function based on `currentStep`.
- **Loop soundness** (replacing the former `resolve_loop_result`, which was
  vacuous — its `isResult` predicate was `True` on both constructors, and
  fuel-bounded totality is already structural):
  - `step_needsIO_inversion`: the only step yielding `.needsIO` is step 3
    with no response in hand, and it yields the state unchanged;
  - `resolve_loop_paused`: every pause is a genuine IO yield — the paused
    state is at `.sendQueries` with `lastResponse = none` (the contract
    `buildSubQuery`/`resume` rely on);
  - `resolve_loop_star`: a paused run's step is `StepSpecStar`-reachable
    from the start — the loop never takes a transition the generated RFC
    step relation does not allow;
  - `resolve_loop_done`: every answer the loop returns is produced by a
    single `.answer` step at a StepSpec-reachable state.
- **needsIO yield** (`step_sendQueries_needsIO`): stepSendQueries yields `.needsIO`
  when no response is available.
- **Sequential transitions** (`step_seq_checkAnswer`, `step_seq_findServers`):
  sequential steps always transition to the correct next step. `step_seq_findServers`
  now proves existence of a transition (may be `.sendQueries` via NS or SBELT).
- **StepSpec soundness** (`step_implies_spec`): step function only produces
  transitions allowed by StepSpec. Complete: case split on `currentStep`,
  tracing each goto branch to its StepSpec constructor; guard obligations
  discharged from branch conditions (`rcode_eq_of_beq` converts boolean enum
  tests to the guards' propositional equalities; `extractCname = some` implies
  a nonempty answer since `findSome?` on `#[]` is `none`).
- **Response coverage** (`step_analyzeResponse_coverage`): when `responseHandled`
  holds, the resolver does not return the "unhandled response type" error.
  Complete. Required aligning the implementation's 4a condition with
  `guard_answerOrNameError` (see Response Analysis below): at the fallback branch
  all four guards are provably false, contradicting `responseHandled`.

- **CNAME chase obligation** (`step_cname_chase`): when `cnameToChase` fires,
  `stepAnalyzeResponse` MUST transition analyzeResponse → checkAnswer with
  SNAME updated to the canonical name and the chain accumulated. This is the
  *liveness/obligation* direction that the NLP-generated spec cannot express:
  `StepSpec` is an inductive *permission* relation (soundness says every
  transition taken is allowed; an implementation that never chases is
  trivially sound), and the generated `guard_cname` was weakened to
  `answer.size > 0` (the prose "shows a CNAME" has no Format-level meaning
  since answers are opaque ByteArrays, and the qualifier "and that is not the
  answer itself" was dropped), making it identical to the first disjunct of
  `guard_answerOrNameError` — so the spec cannot even distinguish the 4a and 4c
  situations. The obligation is therefore stated manually against the
  implementation-level `cnameToChase` trigger.

All resolver theorems are sorry-free (axioms: `propext`, `Quot.sound`).

## Step Relation and needsIO Yield

### NLP-Derived Guard Derivation

Algorithm sub-step guards (e.g., "if the response answers the question or contains
a name error") are derived entirely via NLP — no hardcoded guard predicates or `True`
placeholders. The pipeline extends the existing NLP infrastructure with:

- **Enum constructor search** (`resolveNPToEnumCtor`): searches all inductives in
  context types for constructors whose name matches the NP head. Multi-word NPs are
  joined to camelCase ("name error" → "nameError"). Two-pass: exact match first,
  then compound substring for multi-word queries.
- **Field chain tracing** (`traceFieldChain`): given a target type (e.g., `Rcode`),
  walks struct fields to find the dotted path from the root struct (`Format`).
  Returns the chain for generating `resp.header.rcode`-style expressions.
- **Verb stem → field match**: when SVO object doesn't resolve, the verb stem is
  tried as a field name ("answers" → "answer" → `Format.answer`). Array fields
  generate `.size > 0` predicates.
- **Coordinated clause splitting**: guard text is split on " or " / " and " into
  sub-clauses, each resolved independently, then combined with `PropSpec.disj`/`.conj`.

Generated guards (in `VeriDNS.Spec`):
- `guard_answerOrNameError`: `resp.answer.size > 0 ∨ resp.header.rcode = Rcode.nameError`
- `guard_delegation`: `resp.authority.size > 0`
- `guard_cname`: `resp.answer.size > 0`
- `guard_serverFailure`: `resp.header.rcode = Rcode.serverFailure`

### Step Relation (`StepSpec`)

`generateStepRelation` (Syntax.lean) emits a formal step relation indexed by
`AlgorithmStep`:

```lean
inductive StepSpec : AlgorithmStep → AlgorithmStep → Prop where
  | seq_checkAnswer_findServers : StepSpec .checkAnswer .findServers
  | seq_findServers_sendQueries : StepSpec .findServers .sendQueries
  | seq_sendQueries_analyzeResponse : StepSpec .sendQueries .analyzeResponse
  | answerOrNameError (resp : Format) : guard_answerOrNameError resp → StepSpec .analyzeResponse .checkAnswer
  | delegation (resp : Format) : guard_delegation resp → StepSpec .analyzeResponse .findServers
  | serverFailure (resp : Format) : guard_serverFailure resp → StepSpec .analyzeResponse .sendQueries
```

Sequential constructors come from adjacent top-level steps; conditional constructors
from sub-steps with `gotoTarget` fields. `StepSpecStar` provides transitive closure.
`isTerminal` identifies terminal sub-steps (answer/name error).

`responseHandled` is the completeness obligation — a disjunction of all sub-step
guards: `guard_answerOrNameError resp ∨ guard_delegation resp ∨ guard_cname resp
∨ guard_serverFailure resp`. This states that the guards cover the full response
space. The NLP pipeline generates soundness (StepSpec: valid transitions) but this
was missing the completeness direction (all cases must be handled). Generated
automatically in `generateStepRelation` after the `isTerminal` block.

### Refined Guards and Obligations (modality + content fidelity)

`StepSpec` and the base guards are *permissions*: soundness proofs cannot
detect an implementation that never takes an allowed transition (this is how
a missing CNAME chase went unnoticed). The base guard derivation also weakens
content: "shows a CNAME" became `answer.size > 0` — identical to the first
disjunct of `guard_answerOrNameError` — because RR sections are opaque ByteArrays
at the Spec level. `generateStepRelation` therefore additionally generates:

- **Refined guards** (`guardRefined_{action}`), parameterized by abstract
  content predicates `answersQuery : Format → Bool` (the "answers the
  question" / "is not the answer itself" prose) and
  `hasRRType : Array ByteArray → BitVec 16 → Bool` (RR-type containment).
  RR-type mentions are resolved through the generated enums: if the enum is
  traceable to a Format field (Rcode, Opcode) a field equation is emitted;
  otherwise (RRType) a `hasRRType` conjunct with the constructor's code from
  `rfcEnumDescriptions` (now a `SimplePersistentEnvExtension` so codes stored
  in Spec/RRType.lean survive into Spec/Resolver.lean). NPs that fail
  name-based resolution fall back to matching the head noun of stored enum
  descriptions ("other servers" → NS via "an authoritative name server").
  `or`-coordination keeps resolved disjuncts; `and`-coordination is
  all-or-nothing (dropping a conjunct would widen the region).
- **Obligations** (`obligation_{action}`), over an abstract transition
  relation `transition : Format → Option AlgorithmStep → Prop`: when exactly
  one refined guard holds (all other refined guards negated — single-guard
  regions, so no priority judgments are needed and the spec stays consistent
  under guard overlap), the sub-step's transition MUST be taken (`none` =
  terminal answer). Generated with hygienic syntax quotations, not strings.

The implementation instantiates `answersQuery`/`hasRRType` with its
parse-based checks (`answersQueryB`, `hasRRTypeIn` in Impl/Resolver.lean) and
`transition` with `stepAnalyzeResponse` (`implTransition`), and proves all
four obligations (`impl_obligation_*` in Proof/Resolver.lean). The old
implementation (returning answers without chasing) is refuted by
`impl_obligation_cname`: a CNAME-bearing, non-answering response in
the single-guard region must transition to checkAnswer.

### Complement-Clause Semantics and Recommendations

Two further rule classes derive specs from sentence shapes the base rules
cannot handle:

- **Complement clauses** (field descriptions, §4.1.1): "specifies/denotes/
  indicates **that/whether** ⟨copular clause⟩" generates
  `{field}_semantics_{i} (emitted : Header → Prop) (⟨isX⟩ : Bool) : Prop`.
  The complement's truth is abstracted as a Bool capability parameter (the
  Spec cannot know the emitter's capability) and quantification is over an
  abstract emission predicate; a "response" mention adds a `qr = 1` guard.
  "that" yields an implication (bit set ⇒ statement); "whether" an iff (bit
  reflects statement). Generated: `aa_semantics_0` (AA=1 ⇒ `isAuthority`),
  `ra_semantics_0` (RA=1 ⇔ `isAvailable` — derived despite the RFC's own
  "this be is set" typo), plus emergent `qr`/`tc` variants. The server
  instantiates `emitted := finalizeForClient`-produced headers,
  `isAuthority := false`, `isAvailable := true` and proves both
  (`server_aa_semantics`, `server_ra_semantics` in Proof/Server.lean) — this
  is what forces the flag hygiene (QR=1, RA=1, AA=0) in `finalizeForClient`.
- **Modal recommendations** (§5.3.3 step 2 prose): "It **may** be the case
  that ⟨C⟩" marks the underlying operation as partial ("may" is now a modal
  in the POS tagger alongside should/must); the following "the **best** is to
  ⟨action⟩" recommends the reaction. C's negated copula over an availability
  adjective and the action's gerund + "for the ⟨obj⟩" become abstract
  predicates over an abstract state σ, generating
  `recommendation_addressesAvailable (σ) (addressesAvailable : σ → Bool)
  (lookAddresses : σ → Prop) : Prop := ∀ s, addressesAvailable s = false →
  lookAddresses s`. The SLIST instantiates it (`slist_recommendation`):
  partiality is `SlistEntry.address : Option`, and when servers exist with
  no known address, `DnsSList.addressTargets` is nonempty — the names the IO
  shim sub-resolves.

### Glueless NS Resolution

`ioResumeLoop` (Impl/Server.lean) implements the recommendation: when
`bestWithAddress` returns `none` (the RFC's "addresses are not available"),
it takes the first `addressTargets` name, sub-resolves its A record from
SBELT (`mkAddressQuery`, full recursive restart of the resolve loop), records
the result via `DnsSList.addAddress`, and retries. Nesting is bounded by a
`depth` parameter (default 3); termination is by lexicographic `(depth, fuel)`.
Failed lookups drop the NS name from the SLIST and try the next target.

The sub-resolution dispatch is PER-ARM: the pure `.done`/`.error` outcomes
continue on the (unchanged) main cache with only the SLIST updated, while the
`.paused` outcome — a NETWORK sub-run — continues on the sub-run's mutated
output cache and FIRST re-consults that cache for the MAIN query
(`gluelessRecheck`, RFC 1034 §5.3.3 "see if the answer is in local
information" applied at each iteration): the sub-run can legitimately have
cached the main answer (e.g. sibling-NS glue) or a negative for it, and a
real resolver serves from cache instead of sending a redundant query. The
re-check is exactly `Resolver.localAnswer`'s first two checks (negative-cache
lookup + typed answerable hit, delivered in the `stepCheckLocal` response
shapes) applied to the sub-cache — NO CNAME peeling, since only typed hits
and negatives block the model's network rules (a cached CNAME must not
preempt the network path). Soundness/completeness of the delivery are
`gluelessRecheck_sound` (Proof/NameTree.lean) and `gluelessRecheck_complete`
(Proof/NameTreeComplete.lean, = the fuel-1 cut of `localAnswer_complete`);
the FreeIO reduction for the arm is `run_ioResumeLoop_glueless_paused`.

Three glueless design decisions close the `.paused` arm of the soundness
driver (`ioResumeLoop_sound`, the last forward-simulation obligation):

- **A FAILED network sub-run contributes nothing** (impl-harden): when the
  inner `ioResumeLoop` returns `.error`, or returns `.ok` but the answer has
  no usable A record (`extractAAddress = none`), the main loop continues on
  the PRE-sub-run cache with the target dropped — the sub-run's partial
  cache writes are discarded (BIND-style conservatism). The model rule
  `Resolves.gluelessNs` threads a sub-run's output cache into the main
  derivation only together with a learned address (`hnsaddr`/`hmem`), so a
  no-address continuation-on-sub-cache would be model-unjustifiable; and an
  errored run exports no driver invariants at all. The recheck/`subCache`
  path therefore fires exactly when an address was learned.
- **`extractAAddress` accepts only a model-visible A record** (impl-harden):
  type A AND class IN AND 4-octet rdata AND a wire-valid owner name. Real
  resolvers ignore class-mismatched records when harvesting nameserver
  addresses (a CH/HS-class A is not Internet glue); the guard also makes a
  learned address provably survive `αSection` abstraction
  (`extractAAddress_model_a`), feeding `gluelessNs`'s `addressOf` premise.
- **`gluelessNs`'s continuation resumes at the rule's own clock `now`, not
  the sub-run's end time `nsEnd`** (model fix): the resolver snapshots its
  clock once per resolution (RFC 1034 §5.3.3 works one SNAME/STYPE request
  against a single TTL horizon; the impl's `state.now` is fixed for the
  whole run), so every cache read after the glueless sub-run is at the
  snapshot time — pinning `hrec` to `nsEnd` demanded freshness at a time no
  impl read ever uses, making the rule undrivable by any time-snapshotting
  resolver.

The driver additionally carries a parameter-level `GluelessProv sbelt`
hypothesis (root-hint belt provenance: the sub-resolution's
`stepFindServers` can install `sbelt` itself as the live SLIST; vacuous
when every root hint carries a glue address).

### needsIO Yield Pattern

The resolver (Impl/Resolver.lean) is a pure state machine. When step 3 (sendQueries)
has no cached response, it yields `.needsIO` instead of erroring:

- `StepResult.needsIO`: new constructor for IO-requiring states
- `StepResult.answer` carries BOTH the delivered response AND the state current at
  delivery (post any `cnameChain` update — the same state passed to `finalizeAnswer`),
  so the terminal outcome can retain the final cache
- `ResolveYield.done (resp) (state)`/`.paused (state)`: resolve loop returns either a
  complete response TOGETHER WITH the finished state (mirroring `.paused`) or a paused
  state waiting for IO. Carrying the finished state closes the terminal-cache wart:
  previously the delivered answer's absorbed records were dropped with the final state,
  so the returned (warm) cache never saw them — an RFC 1034 caching gap, and the
  verification's terminal cache tie was unprovable
- `resume`: continues a paused resolver with an externally-supplied response

Correspondingly, `Server.IoStep.finished (result) (cache)` carries the cache the
terminal delivery returns: a successful `.done` yields the FINISHED state's
`boundStateCache` cache (post-absorb, expiry-bounded), while error deliveries keep
returning the pre-resume `state.resources.cache` (no semantic change there).
`ioResumeLoop`'s `.finished result cache => pure (result, cache)` then persists the
delivered answer's records to the returned cache. The glueless pure-`.done` arm and
`resolveWithIO`'s initial pure-`.done` arm deliberately IGNORE the carried state
(cache-only resolution never absorbs — its final cache equals the input cache).

The IO shim (Impl/Server.lean) drives the resolver via `resolveWithIO`:
1. Run pure `resolve` with SBELT → if `.done`, return response
2. If `.paused` → pick best server from SLIST via `DnsSList.bestWithAddress`
3. Build fresh sub-query for current SNAME via `Resolver.buildSubQuery`
4. Convert `BitVec 32` IP to 6-byte FFI addr via `ipv4ToAddr` (port 53)
5. `forwardQuery` → `resume` with response → loop or return
6. On timeout: remove failed server from SLIST, try next best

`serveOne` uses `resolveWithIO` for true iterative resolution per RFC 1034
§5.3.3. The resolver iterates through delegations autonomously: cache →
NS walk → query → analyze → delegation → re-query until answer or error.
Uses separate client socket (no timeout) and upstream socket (2s recv timeout
via `SO_RCVTIMEO`). On upstream timeout, removes the failed server from SLIST
and tries the next best.

### Glue Record Propagation

Delegation (4b) extracts glue A records from the additional section via
`extractGlueRecords` and populates the SLIST with addresses via
`SlistFromNameSpec.setUpAddresses`. `stepFindServers` also looks up cached A records
for NS names to populate addresses when building the SLIST from cached NS records;
if that re-derived glue is empty AND the walk's cut is the root (match count 0)
it commits to the SBELT instead of an address-less SLIST (external review #015 —
see "Root-hint priming" for why this is root-cut-only).
Both `lastResponse` clearing (4b/4c) and `currentStep` updating (in `resolve.loop`)
are critical for correct state machine transitions.

### Response Flag Hygiene

`finalizeForClient` (Impl/Server.lean) is applied to every response sent to a
client: QR=1, RA=1 (this server recurses), AA=0 (not an authority), Z=0
(§4.1.1 "must be zero in all ... responses"; also strips an echoed or
upstream AD bit this resolver did not validate, RFC 4035 §3.2.3 —
`finalizeForClient_z`). QR/RA/AA are forced by the instantiated
complement-semantics props (`server_ra_semantics`, `server_aa_semantics`).

### EDNS0 (RFC 6891)

`Impl/Edns.lean` implements EDNS0 (DNS flag-day-2020 posture, `docs/tcp-plan.md`
stage E) so that answers larger than the RFC 1035 §4.2.1 512-byte UDP baseline
resolve over UDP; answers still larger than 1232 fall back to upstream TCP (stage U,
below).

- **Advertise upstream.** `buildSubQuery` (Impl/Resolver.lean) appends one OPT
  pseudo-RR (`Edns.optRRBytes Edns.advertisedUdpSize`, root owner, TYPE 41,
  CLASS = 1232 payload size, TTL 0) to every outbound query's additional section
  (arcount 1). The formal model needs no new rules: `Resolves`/`WorldModels` have
  been buffer-parametric via the `ednsBuf` parameter since the EDNS0 model work,
  and the OPT sits below `αQuery` (which abstracts only the question + RD bit).
  The OPT carries the type-41 code through the codec as an opaque RR (RFC 3597).
- **Strip on receive.** `sanitizeTtlsCap` (Impl/Server.lean) runs `Edns.stripOpt`
  before response analysis, filtering OPT out of the reply's additional section and
  recomputing arcount (unbound-parity scrub). This keeps the cache, the glue path,
  and the model reflection (`αSection`) OPT-free, so `WorldModels`' additional-section
  exactness clause stays realizable against OPT-free honest-server model responses.
- **Honor downstream.** `serveDatagram` truncates the client reply at
  `Edns.clientCap query` — the client's advertised size clamped to `[512, 1232]`,
  512 for a plain non-EDNS client — instead of a hardcoded 512. `truncateUdp` gained
  a `cap : Nat := 512` parameter (the default preserves every pre-EDNS0 RFC-conformance
  theorem verbatim); `ServeJustification`'s wire round-trip conjunct generalizes its
  guard and cap to `Edns.clientCap query`, and `serveDatagram_total` stays axiom-clean.
- **FFI receive buffer.** `ffi/recvfrom.c` `veri_dns_exchange` reads upstream
  responses into a `VERI_DNS_UPSTREAM_BUFSIZE` (= 1232) iovec — it MUST match the
  advertised size, or an EDNS-sized referral/answer would be silently `MSG_TRUNC`-clipped
  and fail to decode.

Deviations (documented, all outside dig/unbound differential observability): no OPT
echo in our replies (clients accept the correctly-sized UDP answer regardless), no
BADVERS / version negotiation, EDNS options and the DO bit ignored (no DNSSEC), and no
per-server fallback to plain DNS on FORMERR from a pre-EDNS0 server. Answers still larger
than 1232 (e.g. `cloudflare.com`/`apple.com TXT`) truncate over UDP and are delivered over TCP —
the resolver now speaks TCP on both sides: upstream fallback (stage U) and client serving (stage S),
both below.

### TCP Upstream Fallback (RFC 7766 / RFC 1035 §4.2.2, stage U)

When an accepted upstream reply carries TC=1, `ioResumeLoop` (Impl/Server.lean) re-sends
the SAME encoded sub-query over a one-shot TCP connection to the same server via
`tcpForward` → `UdpSocket.tcpExchange` → the `veri_dns_tcp_exchange` extern
(`ffi/recvfrom.c`: connect + RFC 7766 §8 two-octet-length-framed send/recv + close, one
call). A reply that is accepted and itself un-truncated is analyzed with its TC bit pinned
false, so the model rules' `htc` premise holds structurally; a `none`/still-truncated reply
drops the server and retries as if the datagram were lost (decision 4 → eventually the
`gaveUp` SERVFAIL) — the truncated UDP payload is never consumed (review #008). The model
side is spoof-free (decision 5): the TCP connection is the return path, so `tcpForward` does
NO RFC 5452 source check and `WorldModelsTcp` has only an honest-or-lost clause. Flagship
`ioResumeLoop_sound` stays axiom-clean. `Impl/TcpFraming.lean` proves the frame round-trip;
`Proof/NetworkSim.lean` carries `WorldModelsTcp` (a TCB-adjacent assumption, like
`WorldModels`). Client-side TCP SERVING (delivering a >1232 answer to a UDP client that
retries over TCP) is stage S, below.

**Differential test (stage U6), test-only env overrides.** `test/tcp_difftest.sh` +
`test/mock_auth.py` (dnspython) point both veri-dns and a reference unbound at one hermetic
loopback mock that truncates over UDP and answers over TCP. veri-dns is redirected by three
overrides that are **off by default** (production resolution is byte-identical): `VERI_DNS_ROOT_HINT`
(root-hint IP, `Main.lean`), `VERI_DNS_UPSTREAM_PORT` (upstream dest port, `ffi/recvfrom.c` —
the redirect lives in the C IO-shell so Lean/proofs are untouched; the nominal port 53 is still
presented to the RFC 5452 gate), and `VERI_DNS_ALLOW_LOOPBACK_EGRESS` (lifts the `blockedEgress`
SSRF loopback guard, the analogue of unbound's `do-not-query-localhost: no`). The last is an
`@[init]`-backed `Bool` (`egressBypassEnabled`) whose LOGICAL value stays `false`, so
`blockedEgress` is definitionally unchanged and every proof/flagship is unaffected; only the
compiled startup value is read from the env. Turning it on merely selects the already-proven
`blockedEgress = false` (query-normally) branch — it disables a security guard, not any
soundness property. The exe imports only the runtime `Impl` modules (not the `VeriDNS` umbrella),
keeping `VeriDNS.Test.*` module initializers out of the shipped binary.

### TCP Serving (RFC 7766 §5 / RFC 1035 §4.2.2, stage S)

The resolver accepts client queries over TCP as well as UDP. `serveTcpDatagram`
(Impl/Server.lean) is the transport-agnostic core of `serveDatagram` *verbatim* — the RFC 5358
ACL gate, decode, the `queryProblem` FORMERR gate, `resolveWithIO`, `replyForResolution`, and the
identical `serveTouches`/`boundLru` read-set accounting — with only the reply tail swapped: the
RFC 7766 §8 two-octet length framing (`TcpFraming.frameTcp`, **no truncation** — TCP carries a
whole ≤65535-octet message) written to the accepted connection with `tcpSend`, replacing the UDP
`truncateUdp` + `sendTo`. Because the reply `Format` is byte-for-byte the one `serveDatagram`
computes, the whole client-boundary verdict/authenticity chain transfers unchanged; the serving
capstone `serveTcpDatagram_total` (Proof/ServeTcp.lean, axiom-clean) is `serveDatagram_total` with
the ≤512 truncation conjunct replaced by the frame-fit round-trip `TcpFraming.unframeTcp_frameTcp`
under the real 16-bit ≤65535 length bound. `tcpSend` is effect-free at the `Prog` boundary
(`.pure ()`, exactly like `sendTo`), so the proof needs no new model rule.

Serving is **sequential accept–serve–close, one query per connection** (decision 7): the
`serveTcpOne`/`tcpServeLoop` driver (`Main.lean`) accepts a connection, reads one framed message
(`veri_dns_tcp_recv_msg`), runs `serveTcpDatagram`, and closes (`veri_dns_tcp_close`). It runs on a
dedicated background task alongside the UDP loop, and the two transports **share one resolver cache**
through a `Std.Mutex` held across each serve. Five pure-I/O serving externs join the FFI TCB
(`tcp_listen`/`tcp_accept`/`tcp_recv_msg`/`tcp_send`/`tcp_close`, gap-4 audit trail). Documented
deviations from unbound (decision 7): no persistent connections / idle timeout / out-of-order
answering / RFC 7828 keepalive, and no per-TCP connection-count cap. **Differential test (stage S):**
`test/tcp_serve_difftest.sh` queries both veri-dns and unbound with `dig +tcp` against the same
hermetic mock; the oversized `big.veridns TXT` (~2 KB) that stage U can only truncate to a UDP
client is delivered IN FULL and byte-for-byte matches unbound over TCP.

### Persistent TTL Cache

The §5.3.2 CACHE glossary prose now generates time-aware operations and real
laws on `CacheSpec`: `storeAt : C → RR → UInt32 → C` (from "convert the
interval ... to some sort of absolute time when the RR is stored"),
`sweep : C → UInt32 → C` (from "discards them during periodic sweeps"), and
law fields `store_mem`/`storeAt_mem` (membership) and `sweep_subset`
(removal-only) — emitted as the law statements themselves, so instances must
prove them (previously `store_mem : Prop` was discharged with `True`).
The manual `CacheLookup` class is gone entirely:

- **`CacheSpec.lookup`** is assembled cross-ENTRY within the §5.3.2 block:
  the intro prose names the operation ("converted to a general LOOKUP
  function" — participle "converted" + "to" PP, the premodifier before
  "function"); the search-state entries supply the key in glossary order
  (an entry whose description uses the "search" lexeme contributes a
  component — ALL-CAPS references resolve through a context struct's wire
  field, "the QTYPE of the search request" → `Question.qtype : BitVec 16`,
  else the entry's own resolved type, SNAME → `ByteArray`); the entry
  whose class already has the temporal store and whose description
  encounters stored items "in the course of a search" hosts the method,
  time-indexed.
- **`TrustworthinessSpec`** (`acceptRrset`, `answers`) is generated
  cross-FILE in Spec/Credibility.lean from the §5.4.1 sentences: the
  deliberated verb + object NP ("whether to ACCEPT an RRSET ... should
  consider the ... trustworthiness") give the ranked store; the possessive
  anaphor "already in ITS CACHE" resolves to the generated `CacheSpec`
  (glossary naming convention), whose keyed time-indexed retrieval — read
  via forall-telescope — fixes the key and time arguments; the negated
  passive's "as" complement ("returned as ANSWERS to a received query")
  names the answer-path accessor. This required flipping the import:
  Spec/Credibility.lean now imports Spec/Resolver.lean (CacheSpec must be
  in the env), and Resolver no longer needs Credibility.
  The RFC 2308 negative-cache operations are also generated — see
  "Negative-Cache Typeclass Generation" below.

`DnsCache` (Impl/Cache.lean) wires the TTL machinery into the instances and
proves all laws. Every remaining cache constraint in Proof/Cache.lean
INSTANTIATES a generated parameterized Prop (the
`usingthecache_discard_unrequested` convention — the generator emits the
constraint over abstract predicates when it needs projections the Spec
leaves abstract; hand-written statements survive only as marked membership
helpers):

- `store_absolute_expiry` instantiates `cache_storeAt_absolute` (§5.3.2
  "convert the interval ... to some sort of absolute time when the RR is
  stored" — the same convert-frame that derives `storeAt` also emits the
  conversion LAW: `holds (storeAt c r t) r (t + interval r)`).
- `lookup_ignores_old` instantiates `cache_search_ignores_old` (§5.3.2
  "ignores or discards old RRs ... in the course of a search") against
  `liveEntry`, the exact per-entry test `DnsCache.lookup` filters by;
  helper `lookup_fresh` is the membership/remaining-TTL reading.
- `sweep_discards_old` instantiates `cache_sweep_discards_old` (§5.3.2
  "discards them during periodic sweeps") against `CacheEntry.fresh`, the
  exact retention test `DnsCache.sweep` filters by; helper
  `sweep_removes_expired` is the membership reading.
- `store_never_combined` instantiates `usingthecache_never_combined`
  (§7.4 "either the data in the response or the cache is preferred, but
  the two should never be combined"); helper `store_replaces` carries the
  membership argument.
- `truncated_not_cached` instantiates `usingthecache_truncated_not_cached`
  (§7.4 partial sets: the caching action must be a no-op on truncated
  data); corollary `truncated_cache_unchanged` is the pointwise equation.
- `accept_discard_unrequested` instantiates the generated
  `usingthecache_discard_unrequested` (§7.4 "other than that requested ...
  without caching it").

The cache persists across queries: `serveOne` threads
it (final answers stored with TTL at the wall clock from `UdpSocket.now`),
and `State.now` carries the resolution start time for expiry checks.

### Cache-Hit Answers (step 1 obligation)

RFC 1034 §5.3.3 step 1 — "See if the answer is in local information, and
if so return it to the client" — is a top-level step with an anaphoric
conditional, a shape the obligation generator previously never analyzed
(only the 4a–4d sub-steps got guards/obligations), so an implementation
that proceeded to findServers on a positive cache hit satisfied every
generated spec. This was the same root cause as the earlier CNAME miss:
permissions were generated, the MUST direction wasn't.

The pipeline now parses "See if ⟨condition⟩, and if so ⟨action⟩"
(`NLP.parseIfSoStep`: complementizer "if" after the imperative verb,
anaphoric "so", and an object pronoun resolved to the condition's subject
via `parseImperativeClause`) and generates

```lean
def obligation_checkAnswer (σ : Type)
    (answerInLocalInformation returnAnswerToClient : σ → Prop) : Prop :=
  ∀ s, answerInLocalInformation s → returnAnswerToClient s
```

The honest instantiation (`impl_obligation_checkAnswer`,
Proof/Resolver.lean: condition = fresh negative or positive entry for the
query key; action = `stepCheckLocal s = .answer r`) was UNPROVABLE against
the old implementation — both arms of the positive-hit `if` were gotos.
The fix: `RRParse.rrBytes` (canonical re-encoding), `cacheResponse`
(synthesized answer from cached RRs, finalized through `finalizeAnswer`
for CNAME-chain/question restoration), and `DnsCache.lookup` returning
REMAINING TTLs (expiry − now; `lookup_fresh` restated). `DnsCache.store`
replaces same-key entries at RRset granularity (same-batch members share
an expiry, RFC 2181 §5.2, and survive; stale sets are evicted whole —
`store_replaces` restated), so multi-record sets are served intact.

**RRset TTL normalization (RFC 2181 §5.2, bug #4 fix, 2026-07-06).** A response
can carry an RRset whose members have *differing* TTLs; storing them one-at-a-time
through `store` evicted differing-expiry same-key members, collapsing the set. The
lossy `store` (load-bearing for `OneExpiryPerKey`, consumed by the max-cred gate)
is untouched. Instead the section is normalized to its per-key MIN TTL *before* the
write, in **both** the model and impl, in lockstep: model `Cache.absorb` folds
`Net.normalizeTTL (section.filter keep)`; impl `RRParse.normalizeSection`
(= `Cache.normRaws`: parse → per-key min ttl → re-serialize) runs inside
`cacheUnlessTruncated`, so the runtime call sites are unchanged. The refinement
stays tight via the keystone `αSection (normRaws R) = normalizeTTL (αSection R)`
(`Proof/Refinement.αSection_normRaws`, under an α-mappable+canonical hypothesis),
threaded through `section_extra_perm`/`refer_extra_perm`, the whole
`*_write_WriteRefines` family, and the `_cacheUnlessTruncated` invariant lemmas
(statements unchanged, invariants transferred across `normRaws` by
`normRaws_forall_transfer`). Min (not the incoming TTL) is `Subperm`-safe and never
revives an expired member. `ioResumeLoop_sound` stays axiom-clean.

### Bogus-Delegation Gate (RFC 1034 §5.3.3)

From "the resolver should check to see that the delegation is 'closer' to
the answer than the servers in SLIST are ... **If not, the reply is bogus
and should be ignored**", the check-that/if-not rule (the anaphoric "not"
negates the checked condition — the negative twin of step 1's "if so")
generates `obligation_replyIgnored` with the condition predicate named
from the parsed clause (`delegationCloserToAnswerThanServersInSlist`).
Implementation: `bogusDelegationB` (Impl/Server.lean) = delegation-shaped
(NS in authority, non-answering, no name error, no CNAME to chase) ∧ NOT
closer (`delegationMatchCount` — trailing labels shared between SNAME and
the NS owner zone — ≤ the SLIST's match count). The gate sits in
`ioResumeLoop` beside `acceptResponse`: a bogus reply reaches neither
resolution state nor the cache, closing the in-protocol poisoning vector
where a legitimately-queried server injects NS/glue for zones no closer
than where the resolver already is. `shim_obligation_replyIgnored`
instantiates the generated obligation. (`RRParse` gained `rrName` for the
owner-zone extraction.)

### Cached-CNAME Chase at Step 1

`stepCheckLocal` consults the cache through `localAnswer`, a fuel-bounded
local chase: at each name, the negative then positive lookups come FIRST
(so a direct hit is never shadowed), and only on a miss does it follow a
cached CNAME (RFC 1034 §3.6.2's restart at the canonical name),
accumulating the chain. A full chain hit answers entirely from cache; a
partial chase that ends in a miss continues resolution at the canonical
name (SLIST reset — its match count measured the old SNAME). No new step
transition is introduced, so `StepSpec` soundness is untouched, and the
`obligation_checkAnswer` instantiation discharges on the first chase
iteration.

### NXDOMAIN Covers All Types (RFC 2308 §5)

The §5 sentences key NXDOMAIN by `<QNAME, QCLASS>` and NODATA by
`<QNAME, QTYPE, QCLASS>`. The tuple-key rule treats `<...>` as ONE lexical
token (notation, like a numeral — tokenizer + tagger change), finds the
keyed PP grammatically (prep "for" + NP with "same" premodifier and a
tuple-token head), and resolves the answer class through the enum
machinery ("resulted from a name error" → `Rcode.nameError`). Question
fields OMITTED from the tuple render as invariance of an abstract retrieve
function: `cachingnegativeanswers_nameError_retrieval` (qtype-invariance);
the NODATA sentence names all three fields, so nothing is generated for
it. Implementation: `DnsCache.lookupNxdomain` takes no qtype at all
(invariance is definitional — `nxdomain_retrieval_conform`), is consulted
first by `lookupNegative` (`lookupNegative_nxdomain_any_qtype` bridges),
and an NXDOMAIN store replaces all entries for `<QNAME, QCLASS>`. Live: an
NXDOMAIN cached from an A query answers a subsequent AAAA query in 0 ms.

### Periodic Cache Sweep

`serverLoop` sweeps the cache at the wall clock every `sweepInterval`
(64) queries — the §5.3.2 "periodic sweeps to reclaim the memory" whose
operation and laws (`sweep_subset`, `sweep_removes_expired`) were already
generated and proven but never invoked. Between sweeps, expired entries
are already invisible to lookups (`lookup_fresh`).

### Negative Caching (RFC 2308)

`rfc/rfc-2308.txt` is captured in Spec/NegativeCache.lean via three
`include_rfc` blocks, all run through the NLP pipeline (the generator's
section-title and prose-header recognition was extended for RFC 2308's
"N - Title" format):

- §2.2 ("NODATA is indicated by an answer with the RCODE set to NOERROR and
  no relevant answers in the answer section") generates `nodata_indicated`:
  the "is indicated by" rule resolves "RCODE set to NOERROR" to an enum
  equation through the field chain and "no relevant answers" to
  `(Format.answer resp).size = 0`.
- §3 ("the TTL of this record is set to the minimum of the MINIMUM field of
  the SOA record and the TTL of the SOA itself") generates
  `negativeanswersfromauthoritativeservers_negative_ttl`: the
  minimum-of-two-fields rule locates `SoaRdata` (searching nested
  namespaces) and emits the if-form minimum (`BitVec 32` has no `Min`
  instance).
- §5's closing paragraph generates
  `cachingnegativeanswers_limit_negativeresponse_ttl` via the duration-cap
  rule: the capped entity is the object NP of the verb "cache" in the limit
  sentence ("… limit for how long it will cache a negative response …"),
  and the bound is the upper end of a grammatically parsed
  ⟨numeral to numeral time-unit⟩ range (`NLP.parseDurationRange`; word
  numerals are `.quant` tokens) from "Values of one to three hours … would
  make sensible a default" → every stored negative TTL ≤ 10800 s.
- §6 ("it MUST add the cached SOA record to the authority section of the
  response with the TTL decremented by the amount of time it was stored in
  the cache") generates `obligation_addCachedSoaRecordToAuthoritySection`
  via the MUST-add-to rule: the when-clause guard
  (`encountersCachedNegativeResponse`), object NP (`cachedSoaRecord`),
  "to" PP target (`authoritySection`), and "with" PP head-noun + participle
  transform (`withTtlDecremented`) are all read from the parse.

Implementation: `DnsCache.storeNegative`/`lookupNegative` (keyed
`NegativeEntry` array with absolute expiry), `computeNegativeTtl` +
`extractSoaNegative` (SOA scan of the authority section, returning both the
negative TTL and the SOA RR itself — **owner-checked**: only a SOA owned at
or above the response's echoed question name qualifies (RFC 2308 §3 / review
#012/#013), mirroring the model `soaNegTtl qname`'s `isAncestor r.owner
qname` conjunct; an off-owner SOA — the negative-cache poisoning vector — is
skipped, a response with no on-owner SOA is an un-cacheable bare denial, and
the fact is pinned by `extractSoaNegative_owner` plus the store invariant
`CacheNegSoaOwner`/`replyPath_cacheOut_negSoaOwner`), and
`negativelyCacheable` (untruncated
NXDOMAIN or NODATA). `serveOne` stores negatives after answering — TTL
capped by `capNegativeTtl` (10800 s) and the SOA RR stored alongside,
carrying the capped TTL; `stepCheckLocal` answers a fresh negative hit
immediately via `negativeResponse`, whose authority section now carries the
cached SOA with the decremented TTL (`NegativeEntry.authority`: remaining
lifetime `expiry − now`, served via `CacheLookup.lookupNegativeSoa`).
Re-storing a cache-served negative is harmless: the served TTL is the
remaining lifetime, so the absolute expiry never extends (no §5 loop).
Conformance proofs: `computeNegativeTtl_conform` (instantiates the
generated TTL law by `rfl`), `negativelyCacheable_nodata` (the NODATA arm
implies the generated `nodata_indicated`), `lookupNegative_fresh` (no
expired entry is ever returned), `capNegativeTtl_conforms` (Proof/Server:
the generated §5 cap), and `negative_soa_in_authority` +
`lookupNegativeSoa_serves_authority` (Proof/Cache: the generated §6
obligation and the lookup serving exactly that authority).

### Negative-Cache Typeclass Generation (RFC 2308 §5/§6)

The manual `CacheLookup.storeNegative`/`lookupNegative`/`lookupNegativeSoa`
methods were replaced by typeclasses generated from the same sentences that
already generated the §5/§6 props:

- **§5 (tuple-key rule, extended)**: the keyed cached/retrieved frame
  ("should be cached such that it can be retrieved and returned ... for the
  same ⟨TUPLE⟩") now also generates `NegativeCacheSpec (C : Type)` with
  `cacheNegative : C → ByteArray → BitVec 16 → BitVec 16 → Rcode → UInt32 → C`
  and `retrieveNegative : ... → Option Rcode`. The store key is the UNION of
  the tuple fields across the keyed sentences (NXDOMAIN names ⟨QNAME,
  QCLASS⟩, NODATA ⟨QNAME, QTYPE, QCLASS⟩); field types come from the
  `Question` struct projections; the answer class is the enum resolved from
  the subject's relative clause ("resulted from a name error" → `Rcode`);
  the operation names come from the passive participles after "be"
  (`participleStem`, with an e-final verb-root lexicon: "cached" → "cache");
  the subject's premodifier supplies the suffix ("a NEGATIVE answer"). The
  TTL-countdown sentence ("This TTL decrements ... upon reaching zero ...
  MUST NOT be used again") adds the absolute-time argument.
- **§6 (MUST-add rule, extended)**: the when-clause's object ("a CACHED
  NEGATIVE response") anaphorically references the §5 class — its
  premodifiers (participle + adjective) reconstruct the class name — so the
  obligation's pieces also generate
  `NegativeAuthoritySpec (C RR : Type) extends NegativeCacheSpec C` with
  `storeSoaRecord` (from "... the amount of time it was STORED in the
  cache") and `authoritySection` (the "to"-PP target served back for the
  same key). The key is read off the parent's store projection via a
  forall-telescope, so the two blocks stay independent.

`DnsCache` instantiates both (`cacheNegative` = `storeNegative` with no SOA;
`storeSoaRecord` = `DnsCache.setNegativeSoa`, attaching the SOA to the
just-stored entry; `authoritySection` = `lookupNegativeSoa`); `localAnswer`
consults the generated methods. The server-side one-shot
`DnsCache.storeNegative` (rcode + SOA in one entry) remains the concrete
composition of the two generated operations.

### Entry-Structure Derivation (SlistEntry)

The manual `ServerEntry` was replaced by `SlistEntry`, generated from the
§5.3.3 algorithm prose by `deriveEntryStructure` (RFC/Syntax.lean), entirely
from grammatical structure:

1. **Membership imperative** — a verb-first clause whose plural object moves
   "into" an ALL-CAPS structure ("Copy the names into SLIST") fixes the
   entry identity → field `name : ByteArray`.
2. **Possessive-anaphor imperative** — "Set up THEIR addresses ..." (the
   determiner "their" refers to the just-established entries) → per-entry
   field `address : BitVec 32`.
3. **Modal partiality** — "It may be the case that the addresses are not
   available" ("may" + expletive copula + "case" head with a that-relClause
   negating an adjectival predication over a known field's plural) → the
   field wraps in `Option`.
4. **Keep-track purpose** — "keep track of previous transmissions" (token
   level: purpose-infinitive coordination is lossy at clause level) →
   `transmissionCount : Nat`.

The per-entry `matchCount` of the old manual struct was dropped: §5.3.2 ties
the match count to the SLIST itself (it remains on `DnsSList` and
`SlistFromNameSpec.matchCount`). Supporting NLP fixes: "their" joined the
determiner lexicon, `parseImperativeClause` absorbs verb particles ("Set up"),
the det-adj-verb sequence retags as a noun ("a negative ANSWER"), and
`stripPlural` only strips "-es" after sibilant stems ("names" → "name",
"addresses" → "address").

### Cache Bounds (read-LRU eviction at IO-round boundaries — item 5)

Both cache sections are bounded by `DnsCache.capacity` (4096) under a full
**read-LRU** policy (unbound's `lruhash` parity — no RFC mandates an
eviction policy): every entry carries a `lastUsed : UInt32` recency stamp
(`now` at store time), every LOOKUP counts as a use, and the eviction
victim is the least-recently-used unit (ties to the oldest write; the
model stays unbounded and `αCache` is blind to recency).

- **Batched touches**: recency is NOT bumped in-band on every pure-machine
  read (that would churn every state literal in the run-inversion proofs
  for zero observable difference). Since eviction only ever happens at
  the IO-round boundaries, applying a round's accumulated read-set
  touches (`DnsCache.touchKeys`) immediately before each eviction
  decision is bit-identical to per-read touching. The read set is
  mirrored deterministically: `roundTouches` (Impl/Server.lean) re-uses
  the REAL step functions (`stepAnalyzeResponse`/`stepCheckLocal`/
  `walkNs`) for every traversal decision and only mirrors the demand-key
  extraction (`localAnswerTouches`/`walkNsTouches`/`findServersTouches`);
  `serveTouches` mirrors the first resolve pass for the server-side
  bound. Per-site `touches_cover_*` pins (Proof/Server.lean) break at
  compile time if a read is re-keyed.
- **Positive section**: `store` never evicts (a mid-batch eviction could
  split an RRset, breaking `LookupComplete`). `DnsCache.boundLru`
  (touch-then-`boundLruKeys`) evicts WHOLE `(owner-CI, type, class)`
  key-groups — strictly finer than the old expiry-class drop (only the
  stale RRset dies, never a cross-key cohort) and still never splits a
  set (`lruRRsetAtomic` mock). `evictLruKeys_filter_form` states every
  eviction pass is a filter on the entry's RRset key alone;
  `boundLruKeys_bounded`/`boundLru_bounded` (Proof/Cache.lean) prove the
  bound. Applied at `afterResume`'s two arms (with `roundTouches`) and at
  `serveDatagram`'s final store (with `serveTouches`). Under abstraction
  the eviction is a model `pos`-filter whose verdict is constant on
  whole `sameKey` classes BY CONSTRUCTION (`αCache_boundLru_eq`,
  Proof/Refinement.lean — unlike the old expiry filter, no
  `OneExpiryPerKey` needed; only `WfRR` canonicity for the reverse key
  bridge), feeding the same `CacheRefines` c2f slot
  (`cacheRefines_boundLru_absorb`). Below capacity the bound is an
  `αCache`-equality (`αCache_boundLru_noop`), not a byte identity —
  touches still bump `lastUsed`.
- **Negative section**: `storeNegative` runs `boundLruNegatives` per
  store (drop the min-`lastUsed` entry's key while at capacity; entries
  are their own unit). `storeNegative_bounded` (Proof/Cache.lean) proves
  the bound; `NegWriteRefines`' implication-shaped clauses pre-pay any
  shrink, so the policy change is proof-invisible on the model side.

Read-LRU pins (Test/Loop.lean): `lruReadIsAUse` (a READ makes the other
key the victim — write-recency mutants red), `lruHotSurvivesEviction`
(end-to-end serve-path touch wiring), `lruRRsetAtomic` (whole-key
atomicity — per-entry mutants red), `lruNegativeRecency`/
`lruNegativeEvictsCold` (negative twins). Within a round the section may
transiently exceed the bound by at most one response's record count.

### Total Query Deadline

`resolveWithIO` takes a `budget` (default 5 s) and computes an absolute
deadline; `ioResumeLoop` checks `UdpSocket.now` against it on every
iteration (RFC 1035 §7.2's per-request bound on total work). This caps
wall-clock time independently of the 2 s per-exchange timeout and the
fuel/depth bounds — e.g. a long SLIST of unresponsive servers times out at
the deadline rather than at (servers × 2 s).

### QNAME Minimisation (RFC 9156 strict mode, item 6 — Q3a+Q3b landed)

The iterative loop reveals to each upstream server only as much of the
client's QNAME as it needs (RFC 9156), in strict mode (RFC 8020 subtree
denial). Design points:

- **Reveal floor as a loop parameter.** `ioResumeLoop` carries
  `revealed : Nat` (labels of `sname` currently revealed) exactly like
  `deadline`/`depth`/`fuel` — universally quantified in every reduction
  lemma and both capstone inductions, so no `Resources` surgery and no
  state-literal churn. Seeded at `Server.seedRevealed` (SLIST
  `matchCount + 1`) by `resolveWithIO` and by each glueless sub-run (its
  own ladder); bumped by `Resolver.bumpRevealed` (+1 per consumed probe
  outcome, reveal-all once `maxMinimiseSteps = 10` is reached — the §2.3
  MUST-level query bound); pulled to `max revealed (matchCount + 1)` on
  referral continues and re-seeded on CNAME restarts
  (`Server.revealedAfterContinue`).
- **Per-round question.** `Resolver.subQuestion` (named semi-reducible
  def): on a probe round (`probeRoundB` = `0 < revealed < labelCount
  sname`) the qname is `DomainName.minimisedName sname revealed` (a
  wire-suffix re-encoding, canonicity inherited) at obscured QTYPE=A
  (§2.1, unbound's choice); on a full round it is byte-identically
  today's question. The `0 < revealed` conjunct makes the model's
  non-root-ancestor requirement a computational consequence of the
  boolean rather than a threaded invariant.
- **Probe guard.** Between the unfollowable-delegation check and
  `afterResume`: a probe reply that is neither referral-shaped
  (`referralShapedB`, the analyzer's referral branch as one boolean) nor
  retry-shaped (`retryShapedB` — SERVFAIL/unclassifiable *with no CNAME
  to chase*; the CNAME conjunct matters because the analyzer checks the
  chase branch before the bizarre branch) is consumed opaquely:
  reveal+1, continue. Probe answers are never delivered, cached, or
  chased (documented deviation from §3 (6c)'s "cache this answer" — the
  strictly-safer anti-poison posture). Timeouts retransmit the SAME
  minimised name with fresh rid/cid (locked decision 3; no RFC 5452
  entropy regression — note 0x20 entropy on probe rounds is lower
  because probe names have fewer letters; id/port entropy unchanged).
- **Model image.** Datagram-sending `Resolves` rules carry `pq : Query`
  with `ProbeQuery pq q` (full-round left disjunct / `StrictProbe` right
  disjunct). Probe-round referrals are justified via `trustedReferral`
  at `pq` (its `hcut` is judged against the sent name — Q2's retarget);
  `refer`'s `hdesc` is pinned at `q.qname` and is not derivable from a
  probe-round `ServerAnswers`, so honest probe referrals ride the
  trusted shape (their cache writes fall under the
  `TrustedReferralCache` escape in the grounding theorems). Ignored
  probe outcomes map to `badResponse`'s `StrictProbe` disjunct; in
  `ioResumeLoop_sound` the consumed-probe arm needs no model step at all
  (markQueried-only, Subperm-framed like the retry family).
- **Completeness dichotomy.** `StateOK.respMatch` (the question-pin on
  the pending response) is conditional on the response NOT being
  probe-passable (`probePassableB`): vacuous on probe rounds (the guard
  ensures only passable shapes reach the analyzer), recovered on full
  rounds by per-arm shape refutations from the analyzer's own branch
  conditions.
- **Strict terminal (Q3b, RFC 9156 §3 (6d) / RFC 8020).** An
  accepts-passing NXDOMAIN answering a probe (`strictDenialB`: no
  chaseable CNAME, NXDOMAIN, TC=0) is a TERMINAL: the impl delivers the
  client NXDOMAIN (`finalizeAnswer`, chain prepended) and negative-caches
  it keyed at the SENT probe question (`storeProbeNegative` — RFC 8020
  §3.2's revision of RFC 2308 §5; same SOA-owner gate and
  `capNegativeTtl` TTL story as the delivery-side
  `storeNegativeIfCacheable`; no usable SOA ⇒ no write). Model step:
  `ancestorDenied` (trusted-shaped, covering honest and spoofed replies
  with one rule), whose second write slot is `NegWriteRefines`
  (implication-form negative clauses: the impl store replaces same-key
  entries, caps the TTL at `maxNegativeTtl = 10800`, and FIFO-evicts —
  all only SHRINK the served-denial window vs the prepend-only
  `absorbNeg` image). Driver bricks: `soaNegTtl_extractSoaNegative`
  (BRICK 1, the first-match SOA lockstep between
  `Server.extractSoaNegative` over the wire authority and the model's
  `soaNegTtl` over the abstracted one, pointwise via `isAncestorB_eq` +
  `computeNegativeTtl_eq_min`) and `storeProbeNegative_negWriteRefines`
  (BRICK 2, the `NegWriteRefines` instance). To make BRICK 1 non-vacuous
  the abstraction layer gained a **type-6 branch in `αRData`** (`αSoa`:
  decode the SOA rdata, abstract mname/rname via `αName`, numerics via
  `toNat`) — previously SOA records did not abstract at all, so
  `WorldModels`' authority-validity conjuncts excluded every
  SOA-carrying (i.e. every realistic negative) response and the
  strict-terminal write would have been dead under the refinement.
- **The flagship egress pin (Q4, `Proof/SentMinimised.lean`).**
  `ioResumeLoop_sent_minimised`: in EVERY world — any oracle behaviour,
  any clock, any id stream — every datagram `ioResumeLoop` can ever hand
  to the network is the secrets-stamped encoding of a `buildSubQuery` at
  some loop state and reveal floor, whose single question qname is a
  CI-ancestor of that session's `sname`; a probe round reveals *exactly*
  `revealed < labels sname` labels at QTYPE=A, a full round sends the
  session name (CI) itself. Stated over the free-monad program TREE via
  a new `AllSent` inductive (every reachable `.exchange` under every
  environment response satisfies the predicate), so it needs no oracle
  hypotheses and covers timeout/spoof/glueless/blocked-egress branches
  uniformly — strictly stronger than any per-run statement, and it
  proves there is NO egress path that escapes the minimised-question
  builder. Session-anchored per-round content in
  `sent_question_minimised` (built on the Q1 `minimisedName` lemmas);
  `resolveWithIO_sent_minimised` lifts it to the entry point (the pure
  front-end exchanges nothing). Axiom-clean (standard three). The reveal
  SCHEDULE (seed, +1-with-cap, referral max-bump) is deliberately not
  part of the per-datagram predicate — it is pinned by the `Test/Loop`
  ladder mocks (`probeSequenceMinimised`, `probeNodataRevealsMore`,
  `probeAnswerNotDelivered`, `probeCnameNotChased`,
  `probeStrictNxdomainFinal`, `retransmitFreshSecrets`).
- **Coverage (`Spec/QnameMinimisation.lean`).** `check_rfc_doc`/
  `rfc_proves` links over the load-bearing RFC 9156 + 8020 ranges, with
  the five documented deviations recorded in the module docstring
  ((6c) no-cache anti-poison reading; +1-with-cap vs proportional
  jumps; full-round qtype restore one round early; RFC 8020 base SHOULD
  without the DNSSEC gate; §3.2 read-side descendant lookup not
  implemented — siblings under a denied ancestor re-probe) and the
  RFC 6604 `strictDenialB` CNAME-exclusion reading pinned by
  `strict_denial_excludes_cname`.

### Retransmission and Server Selection (RFC 1035 §7.2)

`rfc/rfc-1035.txt` §7.2 is captured in Spec/Resolver.lean. From "Each time
an address is chosen and the state should be altered to prevent its
selection again until all other addresses have been tried", a new prose
rule (passive event clause + "to prevent ⟨possessive-anaphor⟩
⟨nominalization⟩ again") generates `sendingthequeries_prevent_selection`:
after `addressChosen`, `selection` of the same item is false.
`slist_prevent_selection` (Proof/Server.lean) instantiates it:
`bestWithAddress` is least-queried-first (`bestWithAddress_min`, a foldl
invariant over the named `pickBest` step — which also fixed a latent bug
pairing the kept entry with the wrong address), `markQueried` is the state
alteration, and a full cycle of equal counts is the "until all other
addresses have been tried" escape. Behaviorally: a timed-out server is no
longer removed — it is only count-deprioritized, so every less-tried
address is preferred before it is retransmitted to, with total work
bounded by fuel and the deadline. Servers are removed only for bizarre
responses (4d) or failed glueless resolution.

### Query Hygiene (RFC 1035 §4.1.1 RCODE semantics)

Where-block enum value descriptions are now joined across wrapped lines
(previously truncated at the first line), and values whose description is
a negated-capability clause generate use-condition semantics
(`generateNegatedCapabilitySemantics`; the POS tagger learned "unable" as
adjective and verb retagging after "unable to"/"does not"):

- RCODE 1 "The name server was unable to interpret the query" →
  `rcode_formatError_semantics` (capability `interpretQuery`)
- RCODE 4 "The name server does not support the requested kind of query" →
  `rcode_notImplemented_semantics` (capability `supportRequestedKindOfQuery`)
- RCODE 5 "The name server refuses to perform the specified operation for
  policy reasons" → `rcode_refused_semantics` (capability
  `performSpecifiedOperationForPolicyReasons`; the negated-capability
  frame was extended with "refuses to ⟨verb⟩" — a refusal is the
  willingness-capability failing — plus verb retagging after "refuses to")

`serveOne` screens requests before resolution: undecodable datagrams get a
minimal raw FORMERR (ID echoed; dropped if under 12 bytes), `queryProblem`
classifies decoded queries (≠1 question → FORMERR; opcode ≠ QUERY →
NOTIMP; RD=0 → REFUSED, since iterative service is the one operation this
recursive-only server refuses to perform). `hygiene_formatError` /
`hygiene_notImplemented` / `hygiene_refused` (Proof/Server) instantiate the
generated semantics (each over the subtype that passed the earlier
checks — an uninterpretable query has no judgeable kind).

### Client access control (RFC 5358 / BCP 140)

Recursion is confined to the intended clients. `serveOne` splits into the
mandatory `recvFrom` followed by `serveDatagram`, whose *first* action is the
access-control gate: `permitted acl clientAddr` tests the source IPv4 against a
list of CIDR blocks (`AclEntry`/`clientIp`/`AclEntry.matches`), and a source
outside every block returns `pure cache` — no decode, no `resolveWithIO`, no
`sendTo`. `serveDatagram_denied` (Proof/Server) proves this holds in *any*
`UdpSocket` monad: a denied — possibly spoofed — client can neither be reflected
off of nor drive the resolver's recursion, closing the open-resolver
reflection/amplification and cache-exposure surface. The gate is fail-closed
(`permitted_nil`: the empty ACL serves nobody); the shipped default `defaultAcl`
allows loopback + the RFC 1918 private ranges only
(`defaultAcl_permits_loopback` confirms localhost still resolves). The
executable `aclDeniedNoService` (`Test/Loop`) exhibits a public-source query
producing no reply and no upstream traffic.

### Response rate limiting (RRL)

Below the ACL, a per-source fixed-window counter caps how much traffic one
client (or an in-ACL spoofed-source flood) may drive through the serial
`serverLoop`. `serveOneLimited` receives a datagram, then `afterRecv` charges
its source IPv4 via `RateBucket.bump`: a source at `rateWindowLimit`
datagrams for the window gets `none` and is dropped — `afterRecv_ratelimited`
(Proof/Server) proves the drop reduces to `pure (cache, rb)` in *any* monad
(no `serveDatagram`, hence no `sendTo` and no `resolveWithIO`), the same
fail-safe shape as the ACL gate. `RateBucket.bump_over` pins the over-limit
condition. The bucket is memory-bounded (`rateBucketCapacity`; a fresh source
past capacity is admitted untracked, never falsely denied) and reset each
sweep window by `serverLoop`. `serveOne`/`serveDatagram` (and their proofs)
are unchanged — RRL wraps them. Executable `rateLimitDrops` / `rateLimitAdmits`
(`Test/Loop`) exhibit both arms.

### Root-hint priming (RFC 1034 §5.3.3 / RFC 8109)

`Main.primeRootHints` sends ONE direct NS query for the root (`rootPrimeQuery`,
id/question-matched via `acceptResponse`, TTL-capped by `forwardQuery`) to each
hardcoded hint address in turn, and absorbs BOTH the answer (the live root NS
RRset) and the Additional-section glue A records (RFC 8109 §3.3) into the cache
under the root bailiwick (`bailiwickRaws`/`cacheUnlessTruncated`, `credAnswer`/
`credAdditional`). Caching the glue keeps the resolver off the SBELT
round-trip; historically it was also load-bearing: `stepFindServers` used to
fall back to the SBELT only when `walkNs` found NO NS set, so a cached root NS
RRset WITHOUT cached addresses shadowed the SBELT and every resolution starved
in circular glueless sub-resolutions (a root server's address can only be
resolved via the root servers) — a total, restart-only outage. That root cause
is now fixed inside the verified core (external review #015): the
`stepFindServers` rebuild arm falls back to the SBELT when the walk's cut is
the ROOT and the re-derived glue is empty (`glue.isEmpty && mc == 0`). The
fallback is deliberately root-cut-only — an address-less SLIST at a deeper cut
is what triggers glueless sub-resolution, and substituting the SBELT there
would loop (the re-referral re-caches the same NS set); at the root cut the
SBELT is by definition the configured address set for exactly the starving
zone, and deeper glueless sub-runs now bottom out at this fallback. Because
the fallback fires only at match-count 0, its guard coincides with the
existing safety-belt disjunct of the paused-SLIST shape
(`stepFindServers_cases`), so the refinement/soundness statements were
unchanged (`Test/Loop.addresslessRootNsSbeltFallback` is the regression
test). The prime still must not go through `resolveWithIO`: its answer arm
caches only the answer section and drops the glue (the original priming
implementation did exactly that and broke the server from startup). A failed
prime on all hints leaves the cache unchanged — with no root NS cached,
`walkNs` finds nothing and the SBELT path serves normally.

### Client-boundary answer authenticity

`replyForResolution` hands the stub `deliveredResponse query resp` — the
resolved message with its answer section scrubbed to the CNAME-closure of the
queried name (`scrubAnswerB`, which since review #003 also **case-normalizes
each kept owner to the first entitled reach name it CI-matches**: the reach set
is seeded with the client's question bytes verbatim, so a record owned at the
queried name is delivered with the client's exact case — the resolver's
0x20-randomized upstream case never leaks to the client (`eXaMpLE.COm.` in dig
output, post item-4 C2) — and chain-hop owners take the case of the previous
link's rdata, the compression-pointer behaviour of real servers; RFC 1035
§2.3.3. On canonical blobs the rewrite is an `rrWire`-to-`rrWire` splice,
`setOwnerB`. Model pin: `scrubAnswer_owner_at_qname`; mock:
`Test/Loop.deliveredOwnerClientCase`), its authority section scrubbed to decodable
records owned at or above the queried name (`scrubAuthorityB`, review
#012/#013 residual: an off-owner SOA riding a first NXDOMAIN is dropped before
delivery, matching unbound's AUTHORITY:0; `deliveredResponse_authority_owned`
is the delivery-side companion of the `CacheNegSoaOwner` cache pin), the
client transaction id and RD bit restored (RFC 1035 §4.1.1 — upstream
sub-queries are iterative `rd=0`, so without the restore the delivered RD
leaked whether the answer came from cache; `deliveredResponse_rd`, review
#007/#010a), and the client-facing header finalization applied.
`deliveredResponse_answer` pins the
delivered answer to that scrub, and `deliveredResponse_authentic` (Proof/Server)
lifts the impl scrub authenticity (`scrubAnswerB_authentic`) to it: every answer
RR the client receives is the owner-case-normalized rewrite of a resolved answer
record whose owner is genuinely CNAME-reachable (RFC 1035 §2.3.3,
case-insensitively) from the queried name — and the delivered owner IS that
entitled name.
`replyForResolution_ok_fst` proves (via `SatisfiesM`, any `UdpSocket` monad) that
the Format the server reply function actually returns *is* `deliveredResponse`,
and `replyForResolution_ok_authentic` composes the two — so the
answer-injection / poison-conduit vector is closed at the real client boundary,
threading the answer-scrub guarantee up from the scrub through the server reply
path (not merely a pure builder).

The *soundness* companion lives in `Proof/ServeSound.lean`: `resolveThenReply_sound`
composes the tree-level `resolveWithIO_sound` (every resolved answer agrees with
the authoritative name-tree `T`) with `replyForResolution_answer_sound`, so the
Format the resolver hands the client carries only answer records present in `T` —
no fabricated record ever reaches the stub (up to the review-#003 owner-case
normalization, which the case-insensitive tree walk absorbs).
`deliveredResponse_sectionAgrees` carries the tree agreement across the
owner-rewriting scrub: `rrInTree_owner_congrCI` transfers `RRInTree` along the
CI-equal rewritten owner (`nodeAtName_congrCI` + `sameData`'s CI compare), and
showing the rewritten blob *parses* takes the resolved answer canonical
(`CanonicalSection`) plus the client question name canonical (`CanonicalName`) —
facts held on the real serve path by the codec, so `resolveThenReply_sound` now
takes them as one combined `SatisfiesM` run hypothesis alongside `ShimSound`
(two `SatisfiesM` facts about the same computation cannot be conjoined
generically). Together
the two results — authenticity (no injected record) and soundness (no fabricated
record) — are the client-facing half of end-to-end `serveDatagram` soundness. The
remaining verdict/network half is the `ioResumeLoop_sound` entry-hypothesis
discharge (`Proof/IoResumeSound.lean`), tracked separately.

Verdict-half step 1 is `Proof/ResolveWithIOSound.lean`:
`resolveWithIO_paused_sound` is the structural reduction — when the pure resolver
`Resolver.resolve` pauses into `state`, a successful `Prog.run` of `resolveWithIO`
reduces to an `ioResumeLoop` run on that state (deadline `now + budget`), so the
network-track capstone `ioResumeLoop_sound` applies verbatim and yields the model
verdict with the full α-bridge, SLIST `Subperm`, cache-refinement, and
well-formedness-preservation package. This isolates the remaining work: discharging
`ioResumeLoop_sound`'s ~24 entry hypotheses for the resolve-paused `state`. The
ingredients already exist piecewise. `resolve_paused_inv` (same file) is the first
assembled brick: the general-query analogue of `resolve_mkAddressQuery_paused_inv`,
it inverts a paused `Resolver.resolve query` run to the structural facts the discharge
needs — the `localAnswer` cache miss, the untouched cache, and preserved
`now`/`step = sendQueries`/`lastQuery`/`sbelt` — using the query-name canonicity to
close `stepCheckLocal`'s identity-miss branch. Step 2 is assembled in the same file:
the model-tied entry hypotheses are *derived* from the input query + cache
well-formedness + `WorldModels` (`paused_StateModels_noPeel` via
`StateModels_initFromQuery` + the query-renaming `StateModels_cacheCname_preserve`;
`paused_cacheMiss` via `localAnswer_miss_reads` + the read-side bridges;
`paused_GluelessProv` via `walkNs_names_canonical`; `paused_CnameChainModels_noPeel`),
giving `resolveWithIO_noPeel_paused_sound` for the no-peel path. The capstone
`resolveWithIO_paused_full_sound` then closes the CNAME-peel case: a CNAME-type
query cannot peel (identity-miss inversion), and otherwise `localAnswer_chase_peel`'s
`.miss` arm supplies the peeled name's canonicity, model reads, `CnameChainModels`,
and the verdict transformer — the run is resolved at the peeled query and the
transformer folds the peeled links back, so the delivered response IS a model verdict
**at the original client query** (`nseen = []`, verdict input cache `CacheRefines`
the session cache). The `.done` cache-hit outcomes get the same treatment:
`resolveWithIO_negative_full_sound`/`resolveWithIO_answerHit_full_sound` cover a
negative/answerable hit reached AFTER peeling (the read happens at the final chase
target; the chase-peel `.negative`/`.answerHit` arms wrap it back), subsuming the
direct-hit `resolveWithIO_negHit_sound`/`resolveWithIO_answerHit_sound` via the
`localAnswer_qt5_inv` dispatcher. So the CNAME-peel gap is closed across ALL
`localAnswer` outcomes. The top-level assembly `resolveWithIO_verdict_sound` then
hides the internal resolver state entirely: it cases on the `localAnswer` outcome
(hit → the `_full_sound` theorems, output cache = input cache; miss →
`resolve_pauses_of_miss` + the paused capstone, with the paused state's
clock/lastQuery converting the conclusion to input-cache terms; abort → the pure
resolver errors, contradicting a successful run) — ANY successful `resolveWithIO`
run on an abstractable canonical fresh query delivers a model verdict at that
query under natural preconditions only, `WorldModels` being the one irreducible
network premise.

The `serveDatagram` lift is `serveDatagram_verdict_sound` (same file): a
permitted, decoded, well-formed client datagram that `serveDatagram` successfully
serves either failed resolution (SERVFAIL delivery) or hands the client
`deliveredResponse query resp` whose rcode IS the model verdict's and whose
answer is EXACTLY the model scrub of the verdict answer
(`deliveredResponse_answer_exact` — since review #003 the scrub on BOTH sides
also case-normalizes each kept owner to the first entitled reach name, so the
old byte-literal Sublist-of-verdict conjunct no longer holds and was dropped in
favour of the equality; with `deliveredResponse_authentic`, every delivered
record is an owner-case-normalized verdict record, CNAME-reachable from the
query name, and a record owned at the query name carries the client's qname
bytes verbatim). The exactness rides the scrub commutation
`αSection_scrubAnswerB_eq` (`Proof/AnswerScrubAlpha.lean`): `NamesCorr`, the
review-#003 strengthening of the old two-sided existential `ReachCorr` to a
POINTWISE correspondence (same length, `αName reachB[i] = some reachM[i]`, each
wire member canonical within the 255-octet cap), carried through
`reachIterB`/`reachIter` in lockstep (no fixpoint/completeness argument — under
canonical/all-abstracting sections the iteration counts coincide, and each
round appends the targets of the same kept CNAME records in the same order).
The pointwise form is what makes the two `find?` scans pick CORRESPONDING reach
names (`NamesCorr.find?_corr`); the impl rewrite is then an `rrWire`-to-`rrWire`
splice (`setOwnerB_rrWire`) whose abstraction is exactly the model's
owner-rewritten record (`αRR_setName`). The per-pair predicate bridge
(`nameCorr_pred_eq`) takes owner canonicity from the decode itself
(`parseRaw_name_canonical`) and reach-name canonicity from `NamesCorr`; CNAME
target canonicity now comes from `CanonicalSection`'s `CanonicalRdata` (the
`AnswerWriteWf` `RdataCanon` feed became redundant and was dropped), and the
query name's canonicity hypothesis gained the 255-octet cap (from the client
datagram's decode). The exposed
`resolveWithIO` sub-run pins `resp` as this run's resolution. Plumbing:
`serveDatagram_served` reduces the gated do-block (needs the new
`LawfulMonad Prog` instance; the default-simp `Prog.bind_def`/`Prog.pure_def`
must be EXCLUDED so the LawfulMonad `pure_bind` can fire), then
`run_now_bind_inv` + the generic `run_bind_inv` split off the resolution sub-run
at the world's clock.

The post-reply cache-write wf package is CLOSED end-to-end: the serve-loop
invariant conjunct of `serveDatagram_verdict_sound` is UNCONDITIONAL — all eight
cache invariants hold at the ACTUAL served cache (`replyPath_cacheOut_wf` pushes
them through `replyForResolution`'s client-boundary absorb, the RFC 2308 negative
store, and the expiry-class bound), so a successful serve re-establishes the
theorem's own cache preconditions for the next datagram. The byte-validity
interface this needs (`RespWriteWf`, stated on PARSED in-bailiwick answer records:
abstracts + TTL-no-overflow + NS/CNAME `RdataCanon`) is DISCHARGED from the
verdict chain itself: `AnswerWriteWf` (the whole-section, per-raw form, defined in
`IoResumeSound.lean`) is threaded through `ioResumeLoop_sound` as an entry
hypothesis on the paused chain (supplied by `paused_chain_answerWriteWf`) and a
conclusion conjunct on the delivered answer — wire terminals via
`answerWriteWf_of_wire` (WorldModels validity + `sanitizeTtlsCap` + codec
canonicity), cache blobs via `lookupAnswerable_respWriteWf_facts`, and chase-peel
chain growth via `localAnswer_chain_links`/`localAnswer_chain_answerWriteWf` (the
input-chain-agnostic link dichotomy). The `.done` cache-hit deliveries satisfy it
outright (`resolveWithIO_done_answerWriteWf`). Both former verdict-half
residuals — scrub exactness and truncation-to-bytes conditioning — are now
CLOSED (see above and below).

The pure wire-level layer of the truncation residual is
`Proof/DeliveredWire.lean`: `CanonicalSection` (membership-form per-raw
`CanonicalRR`, the compositional unit that survives `++`/`map`/`filter`, unlike
the index-based `ValidRRBytes` it converts to via `rrWire_frame`);
`decode_ok_wire_facts` (everything a successful `Message.decode` says — the four
count-correctness facts, per-question `QuestionFromLabels`, and canonical RR
sections — so wire responses are canonical at the `forwardQuery` source);
transformer lemmas for the TTL cap (`canonicalSection_map_capTtlRR`) and the
client scrub (a filter); and the assembled round-trips
`deliveredResponse_decode_encode` / `errorResponse_decode_encode` — under
natural section-validity hypotheses on the resolution output (resp. the client
query), the encoded delivered reply decodes back to exactly the delivered
`Format`.

The delivered-payload pass supplying those hypotheses from the run is CLOSED
(`ResolveWithIOSound.lean`, `DeliveredSections` section): `SectionsPin` — the
sections analogue of the question-pin — threads `StateSections` (both cache
wire-canonicity invariants `CacheRecCanon`/`CacheNegSoaCanon`, a canonical
CNAME chain, and pending-response section validity) through the four pure
steps, the pure loop, `resume`/`afterResume`/`gluelessRecheck`, and the
`ioResumeLoop` run-inversion (`ioResumeLoop_ok_sections`, mirroring the
question-pin skeleton; the wire arms expose the decode via the
`run_round_bind_eq` family, the glueless arm applies the induction hypothesis
to the sub-run for the recheck cache's invariants). The lift is
`resolveWithIO_ok_sections`. The capstone `serveDatagram_verdict_sound` now
exports the **bytes round-trip conjunct**: when the encoded delivered reply
fits a UDP datagram (≤ 512 bytes), `truncateUdp` sends it verbatim and it
decodes back to exactly `deliveredResponse query resp` — the 16-bit `ancount`
requirement is derived FROM the fits condition via `encode_size_answer_le`
(canonical raws are nonempty), so no size invariant is threaded. The serve-loop
invariant now also re-establishes `CacheRecCanon`/`CacheNegSoaCanon` at the
served cache (`replyPath_cacheOut_canon`: the client-boundary absorb writes
canonical delivered-answer raws; the negative store's SOA is a TTL-adjusted
parse of the canonical delivered authority), so all TEN cache invariants are
self-sustaining across serves.

The total-simulation closure sits on top (plan: `docs/total-simulation-plan.md`).
`serveDatagram_total` (T2, end of `ResolveWithIOSound.lean`) is
`serveDatagram_verdict_sound` with every client-boundary hypothesis DISCHARGED
from the decode itself (`decode_ok_wire_facts`'s `QuestionFromLabels`;
`labelsToWireFormatGo_size_ge` turns the ≤255-octet wire name into ≤127 labels;
the model query is constructed as `⟨decoded labels, .rr t, .in, false⟩`, so its
qtype/class/rd conjuncts hold by construction) — remaining premises are exactly
the ingress gates, the two deliberate scope keeps (no ANY, class IN), the
environment set, and the self-sustaining entry invariants. Since T5 (RFC 3597,
2026-07-11) the qtype-abstractability premise is GONE: `Spec.RRType` carries
`unknown (code : BitVec 16)` (a code outside the 16 named RFC 1035 §3.2.2
assignments — verified against `rfc/rfc-3597.txt` §2–§3 by `include_rfc`) and
the model `RData` carries `generic (t : RRType) (data : ByteArray)` (§3
transparency: opaque bytes, stored and transmitted without change; §4: never a
compression target in the model wire-size layer). `αType` is TOTAL on 16-bit
codes (`αType_total`) and `αRData` total over type codes via the generic arm
(the five interpreted formats — A/NS/CNAME/SOA/PTR — still parse structurally),
so `serveDatagram_total` produces `t` existentially and its only qtype premise
is the explicit ANY exclusion `qu.qtype.toNat ≠ 255` (RFC 8482 direction; ANY
maps to the model `.star`, which the driver's scope excludes). Records of
previously-unmodelled types (MX, TXT, unknown codes) now survive `αSection`
as `.generic`-rdata records, so unknown-type traffic is inside the verified
claim end-to-end. A consequence worth remembering: `rtype = .ns` no longer
pins the `.ns` constructor at the model level (`.generic .ns …` is a value) —
the NS/A extraction proofs invert through `αRData`'s image instead
(`αRData_ns_inv`/`αRData_a_inv` via `αRR_rdata`); and `RRType`'s derived `==`
is now Eq-reflecting on the WHOLE type (`rrtype_eq_of_beq` unconditional — the
`unknown` cell rides `BitVec`'s lawful `BEq`). The `.error`
disjunct is verdict-carrying since T1 (`Proof/IoResumeErrorSound.lean`): every
SERVFAIL delivery comes with `HasVerdictAt` at the entry model cache, the
verdict pinned to `servFail`/empty answer and classified by message
(`Resolves.loopDetected` for the two RFC 1034 §3.6.2 CNAME guards,
`Resolves.exhausted` for the empty belt, `Resolves.gaveUp` otherwise), plus the
full ten-invariant re-export at both the resolution cache and the served cache.
One `gaveUp` inhabitant is proven dead code (give-up follow-up 2): the pure
machine's fuel can never exhaust — `fuelRank` in `Proof/Resolver.lean` bounds
every run at ≤ 7 gotos (each goto out of `analyzeResponse` clears
`lastResponse`, so the re-entered pipeline pauses), and
`resolve_ne_maxIterations`/`resume_ne_maxIterations` show the driver's fuel-64
calls never yield `.error "resolver: max iterations"`.
The serve-sequence corollary (T3) is `Proof/ServeSequence.lean`: `serveSeq`
folds `Server.afterRecv` (rate limiter + `serveDatagram`) over an explicit
finite datagram list (under `Prog`, `recvFrom` is effect-free, so the list IS
the receive sequence; `serverLoop` is `partial` and adds only the periodic
sweep — the corollary quantifies over the sequence, not the loop).
`serveSeq_sound` threads the ten-invariant pack (`ServePack`, with the per-class
negative invariant pinned to the concrete IN code via `αClass_inj` — every
in-scope query's class is byte-identical), `WorldModels`, and the clock
(`run_world_frame`: serving mutates only `trace`/`idCtr`) through the three step
shapes — rate-dropped (`bump = none`), gate-failing (`serveDatagram_unserved`:
under the free monad any failed ingress gate reduces `serveDatagram` to
`pure cache`), and served (`serveDatagram_total`) — concluding a
`JustifiedTrace`: every admitted, gate-passing step carries the full
per-datagram model justification (`ServeJustification`) at its arrival cache.
`serveSeq_total` instantiates at the cold start (`DnsCache.empty`,
`RateBucket.empty` — `ServePack_empty` holds vacuously), so the ONLY entry
premises are the environment set and the per-datagram scope condition
(`InScope`, required only of datagrams that pass the gates — out-of-scope
resolutions carry no invariant guarantee; since T5 the qtype conjunct is just
the ANY exclusion `qu.qtype.toNat ≠ 255` — the class-IN keep and the ANY keep
are the plan's two deliberate scopes, everything else is in the claim).

### TTL Sanity (RFC 1035 §7.3)

From "If a RR has an excessively long TTL, say greater than 1 week, either
discard the whole response, or limit all TTLs in the response to 1 week"
(already-included §7.3 text), an either/or prose rule (imperative or-arm
parsed with `parseImperativeClause`; duration from a numeral + time-unit
pair) generates `processingresponses_limit_ttls`: a processed response is
either discarded (`none`) or every parsed RR carries TTL ≤ 604800, over
all `Array ByteArray` sections of `Format` (discovered from the struct).
The implementation takes the DISCARD arm (`sanitizeTtls` in
`forwardQuery`; the limit arm would need decode-side label-validity lemmas
for the re-encode roundtrip): an offending response is dropped like any
bogus response. `sanitize_limit_ttls` proves conformance. Note
Spec/Server.lean now imports Spec.Message — without `Format` in scope the
prose rules silently no-op.

### Case-Insensitive Name Comparison (RFC 1035 §3.1 / §2.3.3)

The §3.1 block in Spec/DomainName.lean (already verified text) generates
three props via the insensitive-comparison rule — all read from the parse
of "Name servers and resolvers must compare labels in a case-insensitive
manner (i.e., A=a), assuming ASCII with zero parity.  Non-alphabetic codes
must match exactly.":

- `namespace_compare_caseinsensitive` — the manner-PP frame (verb
  "compare" + "in a ⟨X⟩-insensitive manner"; X read from the hyphenated
  adjective, which is a single token since '-' is not punctuation): values
  identified by an abstract `foldCase` compare equal.
- `namespace_compare_example` — the "i.e."-marked `A=a` pair (two
  single-letter tokens differing only in case around "=", scanned in the
  ORIGINAL-case sentence; "assuming ASCII" in the same sentence sanctions
  numeric codes): `compare 65 97 = true`.
- `namespace_nonalphabetic_match_exactly` — the exactness sentence
  (negated-adjective plural subject headed "codes" + MUST + "match" +
  adverb "exactly"): outside the `alphabetic` range the byte comparison is
  exact equality.

Implementation (Impl/DomainName.lean): `foldCaseByte` (A–Z → +32, all
else fixed), `foldNameCase`, and `nameEqCI`; every protocol-level name
comparison routes through it — cache keying (store/storeChecked/
storeNegative/lookup/answerableEntry/lookupNxdomain/lookupNegative/
findNegative), `questionMatches` (response acceptance — an upstream that
echoes the QNAME in different case, e.g. 0x20-randomizing, still matches),
`suffixMatchCount` and `matchCountLabels` (SLIST closeness / delegation
match counts). Wire-format length bytes are ≤ 63 < 'A', so folding whole
wire names only touches label content. Conformance (Proof/DomainName.lean):
`nameEqCI_conforms`, `foldCaseByte_example_conforms`,
`foldCaseByte_nonalphabetic_exact`; end-to-end (Proof/Cache.lean):
`lookup_caseInsensitive` / `lookupAnswerable_caseInsensitive` /
`lookupNegative_caseInsensitive` — lookups are invariant under the case of
the queried name, so `EXAMPLE.COM` hits the `example.com` entry (verified
live: second query 0 ms from cache, including negative entries).

### SLIST Closeness (truncated referrals)

§7.4 forbids caching truncated responses, but a truncated referral is still
usable for the immediate step: 4b installs the response-derived SLIST, and
`stepFindServers` now keeps the current SLIST whenever it is strictly closer
than the cache walk's result — using §5.3.2's own semantics ("a match count
... this is used as a measure of how 'close' the resolver is to SNAME"),
exposed via the generated `SlistFromNameSpec.matchCount`/`searchFails`. Without this,
a truncated (hence uncached) referral caused a re-query loop. Dually, the
CNAME chase (4c) resets the SLIST: its match count measured closeness to the
OLD SNAME ("change the SNAME ... and go to step 1" = fresh context).

### RFC 5452 Resilience

`rfc/rfc-5452.txt` §9.1–9.2 are captured in Spec/Resilience.lean. The §9.1
MUST-match bullet list generates `querymatchingrules_match_obligation` (one
abstract matcher per bullet) — and ALL SEVEN matchers are instantiated with
real predicates over data; none is delegated to the transport:

- **Datagram-level** (`datagramMatches` + `acceptExchanged`,
  Impl/Server.lean): the transport (`UdpSocket.exchange`) runs each query
  on a fresh UNCONNECTED socket and REPORTS the first datagram whose
  source is the queried server, with its kernel-observed addressing
  (`Exchanged`: payload, source, delivery destination, the socket's local
  binding at send time). Datagrams from any OTHER source are skipped in C
  (never returned, never accepted — a strict subset of the Lean gate's
  drop) and the wait continues on the same socket until a 2 s deadline,
  so an off-path junk datagram cannot consume the socket and starve the
  real reply (review #017; runtime regression `exchange-junk-test`,
  Test/ExchangeJunk.lean). The Lean gate
  then decides: source = the queried server (address AND port, bytes 0–3 /
  4–5), destination address = the address the query left from, destination
  port = the query's source port. A mismatch is dropped before
  `Message.decode` runs (`forwardQuery`), and is proven dropped
  (`exchanged_mismatch_dropped`); accepted datagrams provably satisfy all
  three matchers (`exchanged_matches`).
- **Message-level** (`acceptResponse`): query ID + question echo — the qname
  compare is **byte-exact** (`questionMatches`, item 4 / RFC 5452 §9.2 DNS
  0x20; qtype/qclass exact), applied before `resume` so spoofed responses
  never reach the resolver or cache (`acceptResponse_matches`). The model
  gate mirrors this: `accepts` compares qnames with `Net.nameEqCS` and
  `OnWire.offPath`'s blindness disjunction includes the case pattern
  (id ∨ port ∨ qname-case).

`accept_match_obligation` instantiates the generated obligation over
(datagram, response) pairs with the conjunction of the two gates. The fresh
ephemeral local port per query is §9.2's port randomization; unpredictable
query IDs are implemented by `UdpSocket.randomId` (kernel-CSPRNG FFI, TCB
contract on the extern) + `withRandomId`; `serveOne` restores the client's
ID on the final response.

**DNS 0x20 outbound entropy (item 4, stage C2)**: each upstream query draws
`randomId` TWICE — the txid `rid` and an independent case seed `cid` — and
sends `withSecrets subQuery₀ rid cid` (= `withCaseSeed (withRandomId …)`),
which toggles the case of every alphabetic qname byte per `cid`
(`DomainName.randomizeCase`, wire-format-safe: length octets ≤ 63 and the 0
terminator are below 'A'). Honest servers echo the question verbatim, so the
byte-exact gate passes (rig-verified live); an off-path spoofer must now
guess id + port + one case bit per letter. The seed is deliberately NOT
derived from the txid (zero added entropy); both draws share the `randomU16`
TCB contract. **Per-retry TXID (item 4, stage D)**: the transport `exchange`
is single-shot (the old `retryOption` same-datagram retransmit combinator and
its `retryOption_pure` deterministic-collapse contract were deleted) —
retransmit-before-failover happens at the `ioResumeLoop` round level, where
`bestWithAddress` re-selects least-tried-first (§7.2 above) and each round
draws BOTH secrets fresh, so the same (id, case) pair is never on the wire
twice (RFC 5452 §4.4: a repeated pair would extend the spoof race window
across retransmits). Freshness is theorem-pinned: the FreeIO retry lemmas
(`run_ioResumeLoop_retryThenAnswer`) show the second round sends
`withSecrets subQuery₀ (ids (idCtr+2)) (ids (idCtr+3))`; runtime pins are
`exchange-junk-test` case 3 (single-shot) and
`Test/Loop.retransmitFreshSecrets` (fresh id + case on the retry round,
answer still delivered). Proof-side, the second
draw is one extra monadic step threaded through the FreeIO round lemmas
(`run_round_bind_eq` family, fuel +1, continuation takes `rid cid`),
`WorldModels` (quantifies `cid`, oracle keyed by `withSecrets`), and the two
run-inversion capstones — both capstone *statements* unchanged; the reply's
CI match to the canonical SNAME re-derives via `randomizeCase_nameEqCI` +
`nameEqCI_trans`. Regression: `Test/Loop.sentQnameCaseVaries` (sent qname =
seeded image, ≠ canonical, varies with the id stream);
`Test/Loop.caseVaryingEchoRejected` pins the gate half.

`UdpSocket` also has `now` (clock) and a defaulted `log` diagnostic hook
(IO instance: stderr).

### SBELT Initialization

RFC 1034 §5.3.2: SBELT is "initialized from a configuration file" with root
server entries at match count -1 (represented as 0 since `Nat` can't be
negative). `DnsSList.mkSbelt` builds the initial SLIST from `(name, IPv4)`
pairs. Main.lean configures 5 root servers (a-e.root-servers.net).

### Soundness Proofs

- `step_sendQueries_needsIO`: stepSendQueries yields `.needsIO` when no response exists
- `step_seq_checkAnswer`: checkAnswer either proceeds to findServers or answers
  immediately (a fresh negative-cache hit, RFC 2308)
- `step_seq_findServers`: sequential steps always transition correctly
- `resolve_loop_result`: fuel-bounded loop always terminates (extended for needsIO branch)
- `step_implies_spec`: step function only produces StepSpec-allowed transitions
- `step_analyzeResponse_coverage`: `responseHandled` implies no fallback error

## #naturallanguage: NLP Pipeline Inspector

`#naturallanguage { ⟨prose⟩ }` (Macro.lean) runs the pipeline on arbitrary
text and reports what comes out:

1. **NLP trace** — per sentence, the POS-tagged tokens (`word/TAG`, short
   tags from `POS.short`) and every clause the chunker parses (compact
   `Clause.render` notation: `SVO ⟨subj⟩ · verb · ⟨obj⟩ + PP(...)`).
2. **Generated declarations** — the text is fed through the SAME
   generation pipeline `include_rfc` runs after verifying its text (so
   structures, classes, enums, and props are really elaborated into the
   current namespace, with editor hovers on the block), and the report
   lists every new declaration; defs concluding in `Prop` print their
   value. "no declarations generated" is itself informative: it usually
   means the text took a different generator path than expected
   (diagram / glossary / algorithm / value-list / prose-only).

Use it inside a scratch `namespace` to avoid name collisions with the
real specs.

## Key Design Decisions

- **Case-insensitive glue matching everywhere (2026-07-02)**: `DnsSList.fromNsWithGlueAll` matches a glue
  owner to its NS-name case-insensitively (`foldNameCase gn == foldNameCase n`), completing the
  glue-case-sensitivity fix on the *response-transient* SLIST path (a zero-TTL delegation followed from the
  wire without caching it, RFC 2181). The earlier fix covered only the cache-rebuild path (where the
  case-insensitive match happens during the `lookupTopCred` read). The refinement proofs use `Subperm`
  throughout the referral keystone (`refer_continue_keystone` concludes `referralSlist.Subperm modelSlistOf`,
  not equality): case-folding only ADDS glue vs the old byte-exact `==`, so the model SLIST is a sub-multiset
  of the impl's — the fix strictly widens what the resolver tries while keeping the anti-poisoning bailiwick
  filter intact.

- **Referral continuation caches via `WriteRefines` (2026-07-02)**: the model
  `Resolves.referForget` rule no longer pins the recursive resolution to the
  model's accumulate-`absorb` cache. An RFC-faithful store REPLACES a same-key
  RRset (RFC 2181 §5.2) and refuses less-trustworthy data (§5.4.1), so on warm
  revisits the accumulate-cache — and any SLIST re-derived from it — genuinely
  over-approximates the implementation. The rule now carries the resolver's own
  continuation caches `cf0` (post-write) and `cf` (post-eviction), each
  constrained by `WriteRefines t` (Spec/NetworkSemantics): a `topServed`
  sub-multiset at read times ≥ the continuation time (clocks are monotone, so
  earlier reads never occur) plus an ALL-TIME existential provenance clause
  (anything the written cache ever serves, the absorb-cache serves at some
  time). The provenance clause is what the unconditional cache-poisoning
  theorems (`resolves_cache_in_bailiwick`, `resolves_cout_grounded`, …) walk,
  so their statements are unchanged. The recursive SLIST lower bound (`hsl`,
  now `Subperm`) reads `cf0.referralSlist` — the cache the resolver actually
  consulted. The isolated remaining obligation is `refer_write_WriteRefines`
  (Proof/NetworkSim): the impl's two referral `cacheUnlessTruncated` writes
  write-refine the model absorb, under `CacheWf` + `OneExpiryPerKey`.
  The CNAME-chase analogue is `cname_write_WriteRefines(_ref)` (Proof/NetworkSim):
  the impl's single answer-section write at `credAnswer aa` write-refines the
  model's answer-only absorb. Unlike the referral (whose tier is rank-minimal,
  so `ble_additional_rank` closes every rank obligation), the answer tier can
  be rank-MAXIMAL (`authoritativeSection` when `aa=1`), so it instantiates the
  `cred`-generic core `single_cred_write_WriteRefines`, whose rank argument is
  `warm_foldl_key_covered` (every cacheable raw's key survives in the written
  cache at tier-code ≤ the write tier: its push, a later same-key push, or the
  RFC 2181 §5.4.1 skip's strictly-better blocker under INV-B) composed with
  `written_rep_rank_le` (any same-key written entry's model rank is bounded by
  a served record's, through the impl `topServed` gate with freshness carried
  by `OneExpiryPerKey`) and `αCred_order_used` (impl `toCode` ↔ model
  `Cred.rank` order reversal on the four used tiers).
- **CNAME-chase rules restart the descent and carry `WriteRefines` caches;
  `trustedCname` is the spoofed-chase escape (2026-07-03)**: `answerCname`'s
  recursion now runs at `seen := []` (RFC 1034 §3.6.2 "go back to the first
  step" — the canonical name's delegation path is unrelated to the old one's,
  so the referral-descent watermarks reset while the chase's own `nseen`
  grows, which is what terminates it) and over `cf0`/`cf` `WriteRefines`
  continuation caches (the pinned accumulate-absorb was unrealizable on a warm
  cache — the target's RRset may already be cached even though the chase
  visits only fresh names). `trustedCname` mirrors `trustedReferral` for an
  `accepts`-passing forged CNAME the resolver chases; the anti-poison
  theorems carry a `TrustedCnameCache` escape bounded by the QUERIED NAME's
  own subtree (the write bailiwick is `q.qname` itself — tighter than the
  referral escape's delegation cut). Impl-side, the chase is chain-capped:
  `localAnswer` at fuel 0 returns `.abort` and `stepCheckLocal` fails the
  query (`"cname chain too long"`, BIND's max-cname-chain behavior) instead
  of re-querying the network for a name whose cached data was never
  consulted. The `ioResumeLoop_sound` driver threads `CnameChainModels`
  (every model-visited chase name has a canonical wire representative in the
  impl's `cnameChaseVisited` set — what lets the case-insensitive revisit
  guard refute a model revisit) and is scoped to `q.qtype ≠ .star`: on a
  QTYPE=ANY query the impl's `answersQueryB` (`hasRRTypeIn` against a single
  type code) never fires, so it would chase a CNAME that RFC 1034 §3.6.2
  says IS the answer — a divergence deliberately excluded (ANY is deprecated,
  RFC 8482) rather than fixed, since a star-aware `answersQueryB` reaches
  into the NameTreeComplete completeness layer.
- **Truncated responses are never chased (2026-07-04)**: `stepAnalyzeResponse`
  TC-checks BEFORE `cnameToChase` — a tc=1 payload is possibly incomplete
  (RFC 1035 §4.1.1; real resolvers discard it and retry over TCP), so a
  truncated chaseable-CNAME response is now delivered as-is (the impl's
  uniform tc=1 handling), never chased and never cached (`cacheUnlessTruncated`
  was already the tc=1 identity). Model-side this closed the last cname-arm
  corner of `ioResumeLoop_sound`: a spoofed tc=1 chase had no model rule
  (`trustedCname` forces a cache absorb the unwritten impl cache falsifies) —
  post-harden the tc=1 chase is unreachable (`afterResume_cname_truncated`
  contradiction in the `.continue` arm) and the tc=1 delivery is concluded by
  `trustedReply` (spoofed-only; honest servers never truncate in the world
  model, `serverAnswers_tc_false`).
- **`cacheCname` carries a `CacheRefines` eviction slot (2026-07-04)**: the
  impl's capacity bound (now `boundLru`, item 5) can evict between the cached
  CNAME-link reads and the chase's driver re-entry, so the cached-chase rule's
  recursion runs at any `cf` with `hcf : CacheRefines cf c` — a pure ALL-TIME
  shrink (whole-key expiry-class drops under `OneExpiryPerKey`; stronger than
  the network rules' time-gated `WriteRefines` write slot). The security walks
  compose through `hcf` unconditionally (`CacheRefines.trans_perm`,
  `groundedServed_of_refines`); `resolves_data_needs_acceptance`'s
  cache-unchanged disjunct is sharpened from `cout = c` to
  `CacheRefines cout c` (an eviction changes the cache without an acceptance
  witness but never fabricates served data — the RFC 5452 content is the
  no-fabrication direction), and `offpath_cannot_cache`'s hypothesis follows.
  Driver-side, `localAnswer_chase_peel`'s `.miss` continuation quantifies the
  evicted continuation cache (`cfK`) and exports the output cache (`cOut`), so
  the continue-chase arm is eviction-uniform (no capacity case split).
- **`CacheCnameCanon` carries the ≤127-label bound (2026-07-04)**: canonical
  wire names cap at 255 octets (RFC 1035 §2.3.4), and each nonempty label
  costs ≥2 wire octets plus the root octet
  (`labelsToWireFormatGo_length_bound`), so cached CNAME rdata names have
  ≤127 labels. Threaded from `CanonicalRdata.nameType`'s `hle` through
  `canonicalRR_cnameRdata_canonical` and the cache invariant, it discharges
  the chase recursion's query-name label bound (`hqlen`) invariantly.
- **`ioResumeLoop_sound` co-exports the terminal cache/world ties (2026-07-04,
  the "stage C" conclusion-decomposition style)**: the driver's conclusion is
  `∃ slist v coutM, HasVerdictAt … v coutM ∧ …` — `HasVerdictAt` is
  `HasVerdict` with the model derivation's OUTPUT CACHE named instead of
  existentially closed (`HasVerdictAt.toHasVerdict` repacks) — plus ten new
  conjuncts: `CacheRefines (αCache cout) coutM` (the impl's returned cache
  serves within the model derivation's output cache — exactly the
  `gluelessNs` rule's `hc2f` slot, so a caller can re-enter the loop on a
  sub-run's `cout`), `WorldModels` at the FINAL world (`WorldModels` depends
  only on the oracle field, which no `World` round mutates —
  `WorldModels_oracle`), and the eight impl-cache invariants re-exported at
  `cout` (mirroring the hypothesis section; `cout_exports_bound` bundles
  them through the bound-preservation lemmas, now the `_boundLru` family). Pass-through
  arms inherit the conjuncts from the IH (rewriting the `CacheNegWf`
  conjunct's `lastQuery` conditioning and `CacheWf`'s clock across the
  arm's state-framing equations); terminal arms pin `cout` via
  `afterResume_finished_payload_pos`/`_neg` inversions (the
  `.done`-carries-state equations, now kept instead of discarded). TWO
  producer re-attributions fell out of the cout tie: (1) the plain
  answer/negative terminals route the honest transport through
  `Resolves.trustedReply` (`serverAnswer_hasVerdictAt`) instead of
  `Resolves.answer`, whose pinned cout absorbs the WHOLE reply — a write the
  impl never performs; (2) the finished-chase terminals attribute BOTH
  honest and spoofed origins via `trustedCname` (whose `cf0`/`cf`
  `WriteRefines` slots carry the impl's answer-section write) — a spoofed
  no-write `trustedReply` re-attribution cannot be tied to the impl's
  written `cout`. The observable verdict statement is unchanged; only the
  ∃-witness derivation's rule attribution moved to the cout-faithful rules.
- **Delivered answers are CACHED (RFC 1034 §5.3.3 step 4a / §7.4 impl-harden),
  and `trustedReply` carries write slots**: `stepAnalyzeResponse`'s positive
  plain-answer delivery (`answersQueryB = true`, a NEW arm ahead of the
  no-write answer/nameError leaf) writes the answer section before
  delivering — `cacheUnlessTruncated` at the answer-section owner filter
  (`ownerRaws (echoedQname resp) resp.answer` since review #004; see the
  exact-owner bullet below) with `credAnswer (aa == 1)`, exactly the
  CNAME-chase branch's call shape
  (tc=1 stays a no-op: partial data is never cached) — so the returned warm
  cache serves what was delivered (previously the delivered records never
  reached the returned cache; only chase/referral hops wrote). Model-side,
  `Resolves.trustedReply` gained the `trustedCname`-shaped `cf0`/`cf`
  `WriteRefines` continuation-cache slots against the answer-only,
  `q.qname`-bailiwick absorb, with conclusion cout pinned to `cf` (it is a
  terminal rule). The no-write deliveries (tc=1 truncation, negatives,
  junk answers) are kept expressible by the `∨ cf0 = c` DISJUNCT of `hcf0` —
  deliberately a disjunct, NOT a `WriteRefines.refl` instance, because an
  unwritten cache does not `WriteRefines` the absorb image (a
  higher-credibility absorbed record can occlude what the old cache served,
  breaking both the read-soundness and the provenance clause); the
  disjunction is also RFC-faithful (a truncated delivery caches nothing,
  RFC 1035 §4.1.1). Since the rule now writes, it joins
  `trustedReferral`/`trustedCname` as a bounded in-bailiwick poisoning
  admission: the anti-poison walks gained the `TrustedReplyCache` escape
  disjunct (accepts-passing non-referral reply, poison confined to
  `q.qname`'s own subtree — RFC 5452's classic answer-forgery vector made
  explicit and bounded). Driver-side, the positive terminals split on tc:
  tc=0 attributes BOTH origins via the write-carrying `trustedReply` over a
  synthetic accepted reply (answer `αSection respA.answer`), with
  `cname_write_WriteRefines_ref` discharging `hcf0` and the written-cache
  invariant bundle mirroring the finished-chase arms; tc=1 and the negative
  terminals keep the no-write instantiation (`cf0 := c`, `Or.inr rfl`).
  The resolver still does NOT store delivered negatives in its negative
  cache mid-loop (`storeNegative` runs only in the server wrapper
  `replyForResolution` via `storeNegativeIfCacheable`) — a possible future
  RFC 2308 harden.
- **The answer-section cache keep is EXACT-OWNER, not whole-bailiwick
  (external review #004, 2026-07)**: the answer writes above filter with
  `ownerRaws` — keep a record iff its owner `nameEqCI`-matches the reply's
  ECHOED question name (`Resolver.echoedQname`; the client-boundary write in
  `replyForResolution` uses `clientQname query`) — replacing the
  `bailiwickRaws`/`isAncestorB` keep, which admitted any in-bailiwick
  SUBDOMAIN record riding the answer (`sub.example.test A 6.6.6.6` on an
  `example.test` answer, then served from cache with zero upstream queries —
  cache injection; unbound scrubs the answer to `owner == qname`,
  `iter_scrub.c`). Referral authority/additional writes keep the bailiwick
  keep (glue legitimately lives below the cut). Model-side the
  `trustedReply`/`answerCname`/`trustedCname` `hcf0` image is
  `Response.answerOwned q.qname` (answer filtered to `nameEq r.owner
  q.qname`, empty authority/additional); `Cache.absorb` itself is untouched —
  its `isAncestor` keep is vacuous on the pre-filtered image
  (`isAncestor_of_nameEq`). The `TrustedReplyCache`/`TrustedCnameCache`
  escape predicates are correspondingly SHARPENED from `isAncestor q.qname
  r.owner` to `nameEq r.owner q.qname`: a trusted-forgery write is provably
  confined to the queried name ITSELF, not its subtree
  (`absorb_answerOwned_topServed_owner`). The impl↔model bridge
  (`αSection_ownerRaws_eq`) needs the filter name's canonical wire triple —
  `nameEqCI` compares whole case-folded bytes, unlike the parsed-labels
  `isAncestorB` — which is why the filter is keyed to the echoed question
  name (canonical by the decode pipeline, `questionFromLabels_canonical`)
  and bridged to the model `q.qname` through the `questionMatches` CI gate
  (`absorb_answerOwned_congr`, the write-path `cnameRR_congr`). Exact-owner
  drops inline CNAME chain TAILS from the cache (owner = intermediate target
  ≠ qname); the chase re-queries each hop's target anyway, so the cost is
  one extra round-trip on inline chains, never a wrong answer.
- **Grammar over string anchors**: rules read RFC text through the
  tokenizer/POS-tagger/chunker, never by matching literal phrases.
  Notation (tuples, numerals, durations) is tokenized; frames are
  detected over tagged tokens (assertive verb + complementizer for
  "specifies that/whether", "same ⟨form⟩ as ⟨REF⟩" structural-identity
  references, quantifier-partitive "some of which are ⟨adj⟩",
  conjunction-token object coordination); content words come from parsed
  NPs/clauses. Closed-class lexicons (determiners, particles, verb roots,
  time units) are the only word lists.
- **Line ranges over section numbers**: Line numbers are unambiguous and
  don't require section header parsing. If the RFC were re-formatted, line
  numbers would change but so would any other reference.
- **Raw text blocks**: The `{ }` syntax uses a custom parser that reads
  everything between balanced braces as raw text, avoiding string escaping.
- **Page break stripping**: Old RFCs (1034, 1035) have page breaks with
  `[Page N]` footers and form feeds. Modern RFCs (9606) don't. The stripper
  handles both.
- **Batteries dependency**: Used for standard library extensions.

## RR Decompression and Resolver Typeclasses

### Canonical RR Decoding (`decodeRRCanonical`)

DNS message sections (answer, authority, additional) store resource records as
`Array ByteArray`. Originally `decodeRRAsBytes` extracted raw byte slices from
the message buffer, but these could contain compression pointers (§4.1.4)
referencing positions in the original buffer, making standalone parsing fail.

`decodeRRCanonical` replaces this by decoding the RR (resolving compression via
`decodeName` which has the full buffer), then re-encoding uncompressed. For
domain-name rdata types (NS=2, CNAME=5, PTR=12), the rdata is also decompressed,
and SOA (6) rdata has MNAME/RNAME decompressed before its fixed 20-byte tail —
AWS name servers compress SOA rdata names, which silently broke RFC 2308
negative-TTL extraction from authority sections until canonicalized.
After this, all `ByteArray` values in `Format.answer/authority/additional` are
self-contained and can be parsed independently.

### Resolver Typeclasses

The resolver is parametric over `{S C NS RR : Type}` with typeclass constraints.
Two new typeclasses bridge the abstraction gap between `Format` (which stores
`Array ByteArray`) and the parametric types:

- **`SlistFromNameSpec S NS`** (extends `SlistSpec S NS`): batch SLIST
  creation from an array of NS name wire bytes and a match count.
  GENERATED by the operations reading of the same §5.3.3 imperatives the
  entry structure reads as fields: "Copy the names into SLIST" →
  `copyNames`, "Set up their addresses" → `setUpAddresses` (the possessive
  anaphor pairs each address with its name), "comparing the match count in
  SLIST with that computed from SNAME and the NS RRs" → `matchCount` plus
  the construction-time `Nat` argument, and "If the search for NS RRs
  fails, then the resolver initializes SLIST from ... SBELT" →
  `searchFails` (the emptiness test; the former manual `hasServers`,
  polarity inverted). The class extends the glossary-generated `SlistSpec`
  (the ⟨Entry⟩Spec naming convention the anaphor rules use), with binder
  names read from its Π-type. Used by `stepFindServers` (NS walking) and
  `stepAnalyzeResponse` (4b delegation).

- **`RRParse RR`**: parsing canonical wire bytes into `RR` values and extracting
  type/rdata fields. Methods: `parseRaw : ByteArray → Option RR`,
  `rrType : RR → BitVec 16`, `rrRdata : RR → ByteArray`. Used by helper
  functions `extractNsNames`, `extractCname`, and `cacheRRs`.

### NS Walking (Step 2)

`stepFindServers` now walks SNAME labels looking for NS records in cache,
following RFC 1034 §5.3.3 step 2: start at SNAME, then parent, grandparent,
up to the root. Uses `DomainName.parentDomainWire` to strip labels and
`CacheLookup.lookup` to query the cache. Falls back to SBELT only when no
cached NS records are found. Fuel-bounded to prevent infinite loops.

### Response Analysis (Step 4)

`stepAnalyzeResponse` now handles all four sub-cases from RFC 1034 §5.3.3,
checking 4c first per the RFC's qualifier:

- **4c**: CNAME redirect, checked before 4a ("if the response shows a CNAME
  **and that is not the answer itself**"). The trigger `cnameToChase` fires
  when the answer contains a CNAME but no RR of the queried type (and the
  query was not for CNAME records). On chase: cache the answer, set SNAME to
  the canonical name, append the answer RRs to `State.cnameChain`, goto
  step 1. The obligation direction is proved (`step_cname_chase`).
- **4a**: Answer (non-empty answer section) or name error → return
  `finalizeAnswer s resp`: the accumulated CNAME chain is prepended to the
  answer (ANCOUNT updated) and the **original client question is restored** —
  after chasing, the last sub-query's question names the canonical name, and
  stub resolvers silently discard responses whose question section does not
  match what they asked (this manifests as a client-side timeout, not an
  error). The branch condition matches the NLP-generated `guard_answerOrNameError`
  (`answer.size > 0 ∨ rcode = nameError`) exactly, so that `responseHandled`
  covers the branch space (`step_analyzeResponse_coverage`).
- **4b**: Delegation (empty answer, non-empty authority with NS records) →
  cache authority RRs, build new SLIST from NS names (match count =
  trailing labels the delegation zone shares with SNAME — the §5.3.2
  closeness measure, previously mis-set to SNAME's full label count),
  goto step 2. A NOT-closer delegation is bogus and never reaches resume:
  see "Bogus-Delegation Gate" below.
- **4c**: CNAME redirect (answer contains CNAME record) → cache answer RRs,
  update SNAME to canonical name, goto step 1
- **4d**: Server failure **or other bizarre contents** → clear the response
  and retry with step 3. The NLP rule for "or other ⟨adj⟩ ⟨noun⟩"
  disjuncts renders the complement class: the base `guard_serverFailure`
  gains `∨ (¬guard_answerOrNameError ∧ ¬guard_delegation ∧ ¬guard_cname)`
  (making `responseHandled` total — `step_analyzeResponse_coverage` is now
  unconditional and the fallback error is provably dead), and the refined
  guards gain a uniform abstract `handled : Format → Bool` parameter with
  4d's guard becoming `rcode = serverFailure ∨ handled resp = false`,
  instantiated by `classifiableB` (which includes the RFC 2308 NODATA and
  TC handling RFC 1034's enumeration doesn't know about). Behaviorally: a
  REFUSED or odd-rcode response no longer aborts resolution — the server
  is removed (shim-side, §7.2) and the next candidate tried. This also
  fixed a live bug: 4d previously kept `lastResponse`, so an upstream
  SERVFAIL ping-ponged between steps 3 and 4 until fuel ran out.

## Semantic Model: the RFC 1034 §3.1 Name Tree (June 2026)

Everything above constrains the *mechanics* of resolution (wire
roundtrips, cache laws, step permissions/obligations). The semantic layer
gives queries their *meaning*: one global tree of labeled nodes, and a
proof that the resolver can only ever tell the client what that tree
holds.

### Generated tree model (Spec/NameTree.lean)

`include_rfc [1034][355:371]` runs the new **tree-structure frame** in the
prose-only path: a copular clause whose object NP is headed "structure"
with premodifier "tree" defines a recursive node type — the lexical entry
for "tree" carries the recursive-children semantics, the way time-unit
nouns carry seconds. The other pieces are read from the surrounding
clauses (all grammatical, no string anchors):

- term introduction ("uses the term ⟨"node"⟩ to refer to both") names the
  type from the quoted object head → `inductive Node (R : Type)`;
- possession ("Each node has a label, which is zero to 63 octets in
  length") → `label : ByteArray` field + `node_label_size` (the numeral
  range is parsed from the relative clause). "Each node" ranges over the
  nodes of THE TREE, not all values of the type, so the prop binds the
  node (a ∀-over-type reading is provably false — construct a bad value);
- correspondence ("corresponds to a resource set (which may be empty)")
  → `resourceSet : Array R` (collection head noun → Array; element
  premodifier unresolvable → abstract type parameter; the modal relative
  clause permits emptiness, so no constraint);
- negated kinship possession ("Brother nodes may not have the same
  label") → `node_brothers_distinct_label` over one node's child pairs;
- "null (zero length) label used for the root" (token-level with the
  parenthetical, like the A=a example rule) → `node_root_label_null`;
- the path-definition copula → `domainname_labels_on_path`
  (name = label projection mapped over an abstract root path).

NLP support added for this: coordinated subjects distribute over the
predicate in `parseClauses` (one clause per conjunct), modal "can",
subordinator "although", demonstrative subjects ("that is the null
label"), and an NP-final bare-verb retag ("a resource SET (").
Constructor idents in generation quotations must be antiquoted
(`$mkId:ident`) — a literal `mk` picks up macro scopes under
`include_rfc` elaboration.

### Denotation (Impl/NameTree.lean)

`nodeAt`/`nodeAtName` descend from the root by labels (case-insensitive
via `foldNameCase`); `treeLookup` is the per-query verdict
(`Outcome`: answer / nodata / redirect / nameError — NXDOMAIN exactly
for missing nodes); `treeResolve` adds the §3.6.2 CNAME chase with chain
accumulation; `WellFormed` is the recursive closure of the generated
node-local props. `cnameType : BitVec 16 := 5` is a named constant so
proofs can `rw` across the OfNat/`5#16` literal-form divide.

### §4.3.2 lookup semantics (Spec/ServerAlgorithm.lean)

`include_rfc [1034][1289:1366]` (own namespace `Spec.ServerLookup` — the
algorithm path's `AlgorithmStep`/`ResponseAction`/`Transition`/`StepSpec`
names would collide with §5.3.3's). The new **sub-step discourse rule**
reads each match-termination sub-step as a small discourse: the first
conditional names the case guard, later conditionals nest inside it,
"Otherwise" holds in the complement of its predecessor's local guard,
and each conditional imperative emits one obligation per substantive
action (discourse verbs — go/exit/look/check/see — oblige nothing).
Generated: `obligation_copyRRsMatchQTYPE`,
`obligation_copyCNAMERRIntoAnswerSection`,
`obligation_changeQNAMEToCanonicalName`,
`obligation_setAuthoritativeNameErrorInResponse`. A conditional whose
guard fails to name is skipped WITH its body (an unscoped obligation
would be overbroad) — §4.3.2's wildcard sentences drop out this way,
consistent with wildcards being out of scope. Top-level step constructor
names are deduplicated by the final nominal of the first sentence
(`startMatchingZone`/`startMatchingCache`). All four obligations are
PROVEN of `treeLookup` (Proof/NameTree.lean) over the subtype of
scenarios whose tree honors §3.6.2 CNAME exclusivity.

### The proof layer (Proof/NameTree.lean)

- **Oracle** (`ResponseConsistent`): the WEAKENED honesty assumption —
  only responses the resolver ACCEPTS are constrained (RFC 5452 matching
  + connected per-exchange sockets + random IDs keep everything else
  out): every section RR parses to tree data at its owner (up to TTL —
  `sameData`), a name error is deserved, answers are RRset-complete.
- **Tree lemmas**: `treeLookup_nameError_iff` (NXDOMAIN ⟺ missing
  node), `treeLookup_answer_sound` (answers = the node's records of the
  queried type), `treeLookup_nodata_sound`.
- **CI congruence** (`nodeAtName_congrCI`): CI-equal names reach the
  same node — `EXAMPLE.COM` and `example.com` exist and are absent
  together. Via fold-commutation through the label decomposition
  (`wireFormatToLabelsGo_fold_ok`/`_error`; the parse takes identical
  branches because length bytes ≤ 63 fold to themselves).
  `wireFormatToLabelsGo`'s guard is now phrased over `wire.data.size` so
  its index bound proofs are type-correct at instances transparency
  (rewriting under its `dite`s was impossible before).
- **Wire fidelity** (`parseRaw_rrBytes_of_wf`): decoded records are
  `WfRR` (valid name labels + RDLENGTH consistency — `decodeNameAux`
  only returns 1–63-octet labels) and well-formed records re-encode to
  bytes that parse back to themselves — cached data is served
  byte-for-byte honestly.
- **Cache soundness** (`CacheAgrees`): every positive entry is tree data
  (and `WfRR`); an NXDOMAIN entry's node is really absent; every
  negative entry's key really has no data. Preserved by
  store/storeChecked/storeNegative/sweep/FIFO; `lookup`/
  `lookupAnswerable` only return tree data;
  `lookupNegative_deserved` transfers stored deservedness to the queried
  spelling through the CI congruence.
- **Resolver soundness** (`StateAgrees` = cache + CNAME chain agree):
  `stepCheckLocal_sound`, `stepAnalyzeResponse_sound` (all of 4a–4d),
  `step_sound`, and the headline `resolveLoop_sound` /
  `resume_sound` / `resolve_sound`: starting from an agreeing cache,
  with every injected response T-consistent, the resolver only ever
  completes with answers made of tree data and pauses preserve the
  invariant. **Semantic non-poisoning**: nothing the tree does not hold
  can reach the cache or the client.

### Shim soundness (the end-to-end theorem)

`Proof/NameTree.lean`'s `ShimSoundness` section composes the pure-loop
soundness through the monadic IO shim with `SatisfiesM` (Batteries),
over any `[Monad M] [LawfulMonad M] [UdpSocket M Sock ByteArray]`:

- **`NetworkConsistent`** — the weakened oracle in operational form: any
  response that survives `forwardQuery`'s datagram gate AND the RFC 5452
  `acceptResponse` match is `ResponseConsistent` with the tree; spoofs,
  mismatches, undecodable datagrams, and timeouts are unconstrained.
- **`ioResumeLoop_sound`** — by induction on the loop's own (depth, fuel)
  lexicographic measure, through every branch: upstream exchanges, RFC
  5452 rejection, bogus-delegation filtering, server removal, glueless NS
  sub-resolution (the inner recursion starts from the empty cache via
  `resolve_sound` + `cacheAgrees_empty`), and the pure `resume` rounds.
  `ioResumeLoop` was made public (was `private`) so this theorem can name
  it. Proof technique: `rw [ioResumeLoop.eq_def]; dsimp only []` (plain
  `rw [ioResumeLoop]` selects a conditional equation lemma with an
  impossible side goal), then a `SatisfiesM.bind` cascade where plumbing
  binds carry `fun _ => True` and the `let y ← pure (…, cache)` pair-binds
  carry `fun y => y.2 = state.resources.cache` so the cache invariant
  threads through.
- **`resolveWithIO_sound`** — the public entry point: starting from an
  agreeing persistent cache, under the weakened oracle, a full resolution
  run only ever completes with answers made of tree data and returns a
  cache that still agrees.

Axiom profile of the headline theorems: `propext`, `Classical.choice`,
`Quot.sound`, plus the `bv_decide` certificates already trusted by the
wire-format roundtrips. No new axioms.

### The tree network, executable (Test/Loop.lean)

`treeHandler` is a mock upstream that IS the tree: every query is
answered with `treeLookup`'s verdict on a concrete `theTree`
(`.` → `com` → `example` (A) → `www` (CNAME example.com)) — the
`ResponseConsistent` oracle satisfied by construction. Compile-time
checks: the served A record is the tree's record byte-for-byte
(`#guard treeAnswered`), `EXAMPLE.COM` answers from the `example.com`
node (`#guard treeCaseInsensitive`), the CNAME chase follows tree edges
with the full chain served (`#guard treeChased`), and a missing node
yields NXDOMAIN that negatively caches (`treeMissing`) with NODATA for
present-node/absent-type (`treeNodata`) — the last two checked natively
via build-failing `#eval` throws (their kernel reduction under `#guard`
exceeds the default 1 GB stack; the positive-path guards reduce fine).

## Completeness: the resolver delivers the verdict, whole (June 2026)

`Proof/NameTreeComplete.lean` proves the completeness direction of
`AnswersFromTree`, end to end: under the strengthened oracle and a sane
tree, every UNTRUNCATED response a `resolveWithIO` run completes carries
`treeResolve`'s verdict on the client's question at EVERY fuel — NXDOMAIN
exactly for missing nodes, NODATA with no record of the queried type in
the answer, and positive answers containing the chased node's WHOLE
RRset (RFC 2181 §5.2 indivisibility) — and the returned cache keeps
every answerable RRset whole and every negative entry deserved.
Headline: `resolveWithIO_complete`, composed from `resolve_complete` /
`resume_complete` (pure loop) through `ioResumeLoop_complete`
(`SatisfiesM` cascade mirroring the soundness proof). Axiom profile:
identical to soundness (`propext`, `Classical.choice`, `Quot.sound`,
the wire-format `bv_decide` certificates).

### Standing assumptions (beyond the soundness oracle)

- **`TreeSane`** — RFC-mandated tree shape: §3.6.2 CNAME exclusivity
  (reused) and uniqueness (one CNAME rdata per node), records named by
  their owner node (§3.1), one class per node.
- **Completeness clauses of `ResponseConsistent`** (lying by omission is
  now dishonest; all guarded on `tc = 0` except `redirectsOnPath` —
  truncation is the protocol's own incompleteness signal and truncated
  content is never cached or finally served under a `tc = 0` completion):
  `answerWhole`/`authorityWhole`/`additionalWhole` (RFC 2181 §5.2 RRsets
  served whole per section), `*TtlUniform` (§5.2 equal TTLs per RRset),
  `rcodeFaithful` (answer-bearing responses are NOERROR/NXDOMAIN),
  `answerShape` (a NOERROR answer either answers or redirects),
  `answersFaithful` (a response claiming to answer really resolves, with
  the full final RRset), `redirectsOnPath` (offered CNAMEs lie on the
  question's chase path), `nodataDeserved` (RFC 2308 §2.2 NODATA means
  the verdict IS `.nodata`). The soundness theorems use none of these;
  spoofs and timeouts remain unconstrained.

### Cache invariants

- **`LookupComplete`**: every answerable entry's whole tree RRset is
  cached alongside it, same batch (expiry), answerable credibility — so
  step-1 cache hits serve RRsets whole. Preservation through the
  credibility-checked section fold (`lookupComplete_cacheRRs`) rests on
  a per-key dichotomy: blocking status is CONSTANT across one section's
  fold (`blocked_storeStep`), so a key's records all store or all no-op;
  batch members share one expiry (`TtlUniform` + the zero-TTL skip), so
  `store`'s replacement filter keeps siblings and rdata-equal
  replacement preserves the satisfier (`sat_foldl`); `final_keyAt` pins
  every surviving same-key entry to the batch expiry.
- **`NegativesFaithful`**: negative entries pin the tree verdict —
  NXDOMAIN ⟹ node missing, NODATA ⟹ verdict `.nodata` (node present, no
  data of the type, no CNAME); only those two rcodes are ever stored.
  The pure loop never writes negatives, so this is carried; `serveOne`'s
  negative store sites discharge it from `nodataDeserved`/
  `nameErrorDeserved` (the entry-point hypotheses mirror `CacheAgrees`).

### Implementation changes the proof forced

1. **`store` no longer evicts; eviction is whole-key read-LRU at IO-round
   boundaries** (`boundLru`, item 5 — see Cache Bounds; originally
   whole-expiry-class `boundExpiryClasses`): per-record FIFO could strand
   half an RRset.
2. **Zero-TTL records are not cached** (`storeChecked`, RFC 1035 §3.2.1
   "should not be cached") — this also keeps stored entries strictly
   fresh at store time, which the blocking dichotomy needs.
3. **The credibility blocker also matches same-expiry entries**
   (`storeChecked`'s `e.expiry == expiry` disjunct): a least-trustworthy
   store may not overwrite better-credibility data of the same vintage —
   without it a floor-credibility re-store could replace an answerable
   batch member and split its RRset.

### Chase simulation

`Reaches T qtype q s` (defined with the oracle in Proof/NameTree.lean) is
CI-tolerant reachability along `treeLookup` redirects. The resolver's
SNAME is `Reaches`-invariant from the original QNAME: cached-CNAME chases
walk real tree redirects (`localAnswer_complete`, via CNAME exclusivity +
uniqueness), and upstream chases follow `redirectsOnPath`. Terminal
verdicts at reachable names pin every defined `treeResolve` outcome from
the origin (`reaches_terminal_pins`, via determinism/fuel-stability/
chain-irrelevance of `treeResolve`), which discharges the `∀ fuel`
quantifier in `AnswersFromTree` with no existential fuel in the statement.
The accumulated CNAME chain is provably free of records of the queried
type (`StateOK.chainFree`), so chain prepending never fabricates NODATA
answers.

## UDP Server Architecture

### UdpSocket Typeclass

The `UdpSocket` typeclass (Spec/Server.lean) abstracts socket operations over
a monad `M`, socket type `Sock`, and address type `Addr`. This follows the
`CacheLookup` pattern: a manually defined typeclass extending NLP-generated
transport specs. The abstraction enables:

- **Proofs about server logic** without IO dependencies (pure `M`)
- **Testing** with mock sockets
- **IO instantiation** via Impl/UdpSocket.lean

### FFI Approach (Impl/UdpSocket.lean)

Self-contained C FFI in `ffi/recvfrom.c` providing the UDP operations:
`socket()`, `bind()`, `sendto()`, `recvfrom()`, plus `veri_dns_exchange`
(one UNCONNECTED query exchange: fresh socket with a 2 s timeout; a brief
`connect`/`getsockname`/`AF_UNSPEC`-dissolve learns the kernel's local
address selection for the destination WITHOUT filtering the receive;
`sendto` → `recvmsg` with `IP_RECVDSTADDR`/`IP_PKTINFO` destination
metadata → `close`. Returns `Option (payload, source6, destination6,
local6)`; `none` on timeout. The function makes NO acceptance decision —
the RFC 5452 §9.1 source/destination match is decided by the Lean gate
`datagramMatches`), `veri_dns_now` (wall clock) and `veri_dns_random_u16`
(arc4random). Each is exposed via `@[extern]` with simple Lean types
(`UInt32` for fd, `ByteArray` for 6-byte encoded addresses). No external
socket library dependency — avoids Alloy/socket.lean version
incompatibility with Lean 4.31.

### IO-Shim Verification (Test/Loop.lean)

`serveOne`/`resolveWithIO`/`ioResumeLoop` are parametric over `UdpSocket`,
so the full serving loop runs in pure `StateM MockState` over a scripted
mock socket (per-exchange handlers `ByteArray → Option ByteArray`; an
exhausted script is a timeout; the mock reports `Exchanged` addressing
metadata, with `spoofSource`/`spoofDest` overrides for attacker scenarios).
Seven end-to-end behaviors are checked by `#guard` AT COMPILE TIME — the
build fails on regression:

1. **Direct answer**: exactly one datagram to the client, client's ID
   restored, QR=1/RA=1/AA=0/Z=0, the answer delivered, question echoed.
2. **RFC 5452 spoof rejection**: a forged-ID response never reaches the
   client (no answer data; non-NOERROR after the script runs dry).
2b. **Wrong-source rejection**: a correct-ID response reported from the
   wrong source address is dropped by the Lean datagram gate (the
   transport does not filter).
2c. **Wrong-destination rejection**: a response whose delivery metadata
   does not match the binding the query left from is dropped.
3. **Iterative delegation**: a referral (NS + glue, closer match count) is
   chased — two upstream exchanges, final answer correct.
4. **RFC 2308 negative caching**: NXDOMAIN cached from an A query answers
   a subsequent AAAA query with an EMPTY script (qtype invariance, no
   upstream), the §6 SOA served in the authority both times.
5. **Query hygiene**: RD=0 is REFUSED before any upstream work.

Only the C FFI layer (ffi/recvfrom.c) sits outside this boundary; it is
exercised live with `dig`.

### Server Proofs (Proof/Server.lean)

- **buildResponse properties**: ID preservation, QR=1, rcode propagation, question
  preservation — all by `unfold`/`rfl` (struct field projection through `with` update)
- **truncateUdp**: the full truncation discipline —
  - `truncateUdp_no_trunc`: ≤512 bytes pass through unchanged;
  - `truncateUdp_flag_iff`: the truncated flag is reported exactly when the
    encoding exceeded 512 bytes;
  - `truncateUdp_truncated` (RFC 1035 §6.2 "truncation should start at the
    end of the response and work forward"): a truncated reply keeps the
    client's ID and question, sets TC=1, always drops the additional
    section, and never drops the answer while authority data remains;
  - `truncateUdp_size`: the result is within 512 bytes unless it is the
    final header+question form (bounded by the client's own ≤512 query).

All theorems are sorry-free.

## Driver Concurrency (Main.lean, liveness plan L6)

`main` serves UDP and TCP on the same port over ONE shared resolver cache
(`Std.Mutex DnsCache`, `cacheMx`). The UDP loop runs on the main thread; the TCP
loop (`tcpServeLoop`) runs on a dedicated background task (`IO.asTask`). Both are
`partial` server loops — intentionally non-terminating — so their per-query
liveness is not a Lean theorem (see `docs/liveness-plan.md`, decision 5); the
properties below are DOCUMENTED invariants backed by `test/concurrency_stress.sh`.

**Invariant 1 — no cache lock is held across network I/O (snapshot-in / merge-out).**
Each serving round:
1. reads a cache *snapshot* under the lock, then releases it
   (`let snapshot ← cacheMx.atomically get`);
2. runs `serveDatagram` / `serveTcpDatagram` on the snapshot with NO lock held —
   the entire upstream resolution (`resolveWithIO`: round-trips + the query
   deadline) and the client reply happen lock-free;
3. merges the round's resulting cache back into the CURRENT cache under the lock
   (`cacheMx.atomically do set ((← get).absorb served)`) — never a blind `set`
   that would clobber a concurrent writer's insertions.

Consequence: a serve on one transport cannot head-of-line-block a client on the
other. The previous design held `cacheMx` across the whole serve, so one slow
delegation chain (up to the query deadline) stalled every client on both
transports — an availability/DoS surface. `test/concurrency_stress.sh` checks A1/A2
witness this: a fast client returns in ~ms while a 2 s upstream resolution is in
flight on the other transport.

**Invariant 2 — the merge is credibility-safe (`DnsCache.absorb`).** `absorb base
new` replays each of `new`'s entries onto `base` using the SAME same-key dedup
filter as `store`/`storeNegative`, so no RRset record is duplicated or corrupted;
`base`'s keys that `new` did not touch (the other transport's concurrent inserts)
survive, and each key `new` wrote takes `new`'s entry (last-writer-wins per key).
Safety rests on reads being per-key MAX-credibility gated (`maxCredForKey` /
`maxRankForKey`) and freshness gated: absorbing a lower-credibility or stale entry
can never *downgrade* a served RRset because the read path filters it out.
Last-writer-merge is thus acceptable on this advisory cache — a merge that loses a
race merely re-fetches. `boundExpiryClasses` re-bounds capacity after the union.

**Invariant 2 is now a THEOREM** (`Proof/Absorb.lean`, axiom-clean):
`absorb_serve_invariants` proves `DnsCache.absorb` preserves the FULL cache
invariant pack `serveDatagram_verdict_sound` consumes on its entry cache and
re-establishes on its exit cache (`CacheWf`, `CacheNsCanon`, `CacheCnameCanon`,
per-record `WfRR`, `CacheNegWf`, `CacheNsDistinct`, `OneExpiryPerKey`, the
capacity bound, `CacheRecCanon`, `CacheNegSoaCanon`) — so the shared cache's
well-formedness is INDUCTIVE across serve rounds on both transports. Two
structural facts drive it: a membership inversion (`mem_absorb_records` /
`mem_absorb_negatives` — the merge invents no entry, transferring every
per-entry invariant), and the replay filter's dedup (same filter as `store`),
which deletes any same-key-different-expiry / same-NS-key-same-rdata incumbent
before each push — so the RELATIONAL invariants (`OneExpiryPerKey`,
`CacheNsDistinct`) and the capacity bound hold from `base`'s invariants ALONE,
against arbitrary merge input. The non-starvation half (Invariant 1) remains the
stress test's job (a `partial` IO loop's liveness is not kernel-provable).

**Rate limiting.** BOTH loops enforce the RFC 5358 per-source-IP `RateBucket`
(previously only UDP did — TCP was an unthrottled ingress). Each threads its own
bucket, reset every `sweepInterval` datagrams/connections; the UDP loop also drives
the periodic expiry `sweep` on the shared cache.

**Data-race safety.** One global `cacheMx`, acquired alone, never nested, no
re-entrancy — the verified core always runs on a private snapshot, so no serving
path observes a partially-updated cache.

## Adequacy / Liveness Proofs (liveness plan L0–L5)

The converse of the soundness capstones: against a *cooperative* network the
resolver actually DELIVERS the model's answer (soundness alone is vacuously
satisfiable by a resolver that SERVFAILs everything). Four modules, all
axiom-clean; full staging and per-brick status in `docs/liveness-plan.md`.

- **Proof/Adequacy.lean** — the descent machinery, independent of any oracle
  model. `ioResumeLoop_terminates`/`resolveWithIO_terminates` (L0: per-query
  termination in ANY world), `Delivers` (the `∃ K w', Prog.run … = some (out, w')`
  adequacy analogue of soundness's run equation), `Delivers_referral_step` (one
  honest referral round lifts a deeper delivery one zone up), the `DescentChain`
  inductive + `DescentChain.delivers` (chain ⟹ delivery) + `DescentChain.of_descent`
  (build a chain by well-founded induction on a delegation-depth metric), and the
  entry bridges `resolveWithIO_adequate_of_chain`/`_of_descent`.

- **Proof/CooperativeNetwork.lean** — the honest-oracle model feeding that
  machinery. `mkHonestOracle{,Addr}`/`CooperativeNetwork{,Addr}` (the plan's
  decision-2 premise: the oracle is DEFINED and honest, keyed on a responder —
  address-keyed for delegating descents, since with QNAME minimisation off the
  query bytes repeat and only the destination distinguishes rounds), the flat
  `treeRespond` responder + classification/round-trip bridges, the END-TO-END flat
  capstones `resolveWithIO_flatAuthoritative_{answer,nxdomain}_adequate`, the
  referral responder `referralReply` + `delegatingReferralRound_node` /
  `delegating{Answer,Nxdomain}Round_delivers` (per-round constructors), the
  branch-2 continue-state inversion pack (`cooperativeReferral_continue_
  terminalFacts{,_exact}`), the cache write-through engines (glue:
  `reGlue_of_referral_glue`/`reGlue_preBoundLru_of_referral_glue`; NS-key
  exactness: `referralWrite_nsKey_facts` with the `mem_*_inv` write inversions),
  and `depth1Delegation_chain` (the assembled two-round delegating descent).

- **Proof/Depth1Adequacy.lean** — the concrete depth-1 instance discharging
  `depth1Delegation_chain`'s premise set from per-instance-computable zone data
  over a COLD entry cache: `referralReply_roundtrips` (round-1 wire round-trip),
  `mem_reGlue_inv` + `referralWrite_reGlue_exact` (every `reGlue`-recovered glue
  address IS the referral's own glue IP — pins the two-server responder's child
  arm to ONE address), `twoServerRespond` + arm equations, and the capstone
  `resolveWithIO_depth1_adequate`: entry `resolve` pause + two-server cooperative
  network ⟹ `resolveWithIO` delivers the child zone's answer in exactly two
  rounds — PINNED in the statement (plan decision 1): the run output is
  `(.ok resp, cout)` with `resp.answer = rrs.map rrBytes` (the child zone's
  records byte-exact, via `finalizeAnswer_answer`/`treeRespond_answer_eq`) and
  `resp.question = q.question` (the client's question restored). Pairs with
  `ioResumeLoop_sound` on the cooperative path.

- **Proof/ServeAdequacy.lean** — stage L5, serving adequacy: the serve pipeline
  itself delivers. `storeNegativeIfCacheable_runs`/`replyForResolution_runs`
  (the serve tail is total — every arm a log and/or pure cache write),
  `serveDatagram_delivers_of_resolve` / `serveTcpDatagram_delivers_of_resolve`
  (per transport: ingress gates passed + the embedded `resolveWithIO` sub-run
  delivering ⟹ the serve run completes; forward composition over
  `serve{,Tcp}Datagram_served`, with `sendTo`/`tcpSend` effect-free under
  `Prog`), and the end-to-end `serveDatagram_depth1_adequate`: a client
  datagram against the depth-1 cooperative network is SERVED, with the
  embedded (deterministic) resolution pinned to `.ok resp` carrying the child
  zone's records. The reply CONTENT at the client boundary is deliberately not
  re-stated: it is already pinned by `serveDatagram_verdict_sound`
  (`deliveredResponse query resp` for this same sub-run) — adequacy contributes
  the missing half, that the run and its positive `resp` exist.
