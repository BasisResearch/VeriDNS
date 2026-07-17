import VeriDNS.RFC.ScopeGates
import VeriDNS.Proof.ServeSequence
import VeriDNS.Proof.ResolveWithIOSound
import VeriDNS.Proof.ServeTcp
import VeriDNS.Proof.IoResumeSound
import VeriDNS.Proof.SpineAdequacy
import VeriDNS.Proof.ServeAdequacy

/-!
# Scope-gate ledger driver

This file drives the scope-gate enforcement spine (`VeriDNS/RFC/ScopeGates.lean`) over the real
top correctness capstones (imported above).

It:

1. seeds every *current* scope gate with an `open_scope` annotation pointing at its
   `docs/model-strengthening-plan-2.md` escape-hatch-ledger row (so the build is GREEN today);
2. generates `docs/scope-gates.md` from the live signatures; and
3. runs `scope_gate_lint`, which FAILS the build if any capstone carries a scope-gate
   hypothesis that is neither `open_scope`- nor `justified_scope`-annotated.

The seed list below is the ledger backlog: each `open_scope` is a door plan-2 says to shut. When
a row closes (its restricting hypothesis is removed from the capstone), the census stops finding
that gate and its `open_scope` line becomes a no-op documenting the closed door. When a *new*
door opens (a new scope-narrowing hypothesis is added), the lint reddens until someone makes a
deliberate `open_scope`/`justified_scope` decision — that is the whole point.

## Seeded open doors (by plan-2 ledger row)

* **Query shape** — `qtype ≠ ANY`, `qclass = IN`, `rd = false` (and the `InScope` bundle). Closed
  by proving the excluded cases, or proving the resolver's total RFC-correct rejection of them.
* **Adversary model** — soundness/adequacy stated against `WorldModels`/`WorldModelsTcp` /
  `CooperativeNetworkAddr`. Closed by proving the adversary model complete (every wire datagram
  realises some disjunct).
* **Topology** — single-NS `SlistShape`. Closed by a set-valued `SlistShape'` + failover adequacy.
* **State** — `serveSeq_total`'s empty-cache base (`DnsCache.empty`). Closed by the primed-cache
  variant (plan-2 W2a: `serveSeq_total_primed`).
* **Rcode scope** — the adequacy capstones assume the upstream reply is `noError` / not
  `serverFailure`. Closed by adequacy duals for the error rcodes.
* **Direction** — the soundness/total capstones have no completeness dual (a spurious NODATA or a
  misclassified referral satisfies them). Highest-value door per plan-2: closed by a total
  `Classify` theorem + completeness corollary. Recorded here at the capstone level.
-/

open VeriDNS.RFC
open VeriDNS.Proof.Adequacy

/-! ### Seed: query-shape doors -/

open_scope serveSeq_total "query-shape"
  "Query shape CLOSED at the serve boundary: `serveSeq_total` no longer carries the \
   `InScope` hypothesis — its two clauses are now handled, not assumed (qclass=IN via \
   non-IN → REFUSED at ingress; QTYPE=ANY via the RFC 8482 §4.2 serve arm). The census \
   finds no query-shape binder; this seed is a documenting no-op. The ingress \
   classifier is now TOTAL and pinned sound+complete by `queryProblem_spec` / \
   `queryProblem_none_iff` (Proof/Server.lean): TC-set → FORMERR (032, reply TC \
   severed from the client bit via finalizeForClient tc:=0 + truncateUdp_tc_exact), \
   stuffed answer/authority/non-OPT-additional → FORMERR (042), AXFR/IXFR → REFUSED \
   and OPT/TKEY/TSIG/MAILB/MAILA/128–248 → FORMERR (044b, unbound-1.24.2 parity), \
   multi-question FORMERR echoes only the first question (033, errorResponse_question). \
   (plan-2 Query-shape row FULLY CLOSED; CHAOS, ANY, 032, 033, 042, 044b)."
-- `serveDatagram_verdict_sound` is the abstract-`qm` verdict helper that the real
-- serve-boundary capstone `serveDatagram_total` uses.  Its `hqany`/`hrd` binders
-- are facts about the caller-supplied abstract upstream query `qm`, not input
-- gates: `serveDatagram_total` derives both (qtype ≠ ANY from the ANY serve arm
-- being taken, i.e. `isAnyQuery = false`; rd = false because `buildSubQuery`
-- clears rd, `queryDatagram_clears_rd`) and supplies them here.  Justified.
justified_scope serveDatagram_verdict_sound "query-shape"
  "Query shape (abstract-qm helper): hqany/hrd are facts about the caller-supplied \
   upstream model query qm, discharged by serveDatagram_total — qtype ≠ ANY from \
   the RFC 8482 ANY serve arm (isAnyQuery = false, Server.serveDatagram_any), rd = \
   false because buildSubQuery clears rd (Spec.Net.queryDatagram_clears_rd). The \
   serve-boundary capstone serveDatagram_total is itself query-shape-clean. \
   (plan-2 Query-shape row CLOSED at the serve boundary; CHAOS, ANY)."
-- The serve-boundary capstones below are now query-shape-CLEAN (non-IN → REFUSED
-- at ingress closes qclass; QTYPE=ANY → RFC 8482 §4.2 serve arm closes qtype). The
-- census finds no query-shape binder on them, so these seeds are documenting no-ops.
open_scope serveDatagram_total "query-shape"
  "Query shape CLOSED at the serve boundary: qclass=IN via non-IN → REFUSED at \
   ingress; QTYPE=ANY via the RFC 8482 §4.2 synthesized-HINFO serve arm; and the \
   whole malformed/unsupported-query class via the TOTAL ingress classifier \
   `queryProblem` (TC-set/stuffed-sections/meta-QTYPE gates), pinned sound+complete \
   by `queryProblem_spec`/`queryProblem_none_iff`. No query-shape binder remains. \
   (plan-2 Query-shape row FULLY CLOSED; CHAOS, ANY, 032, 033, 042, 044b)."
open_scope serveTcpDatagram_total "query-shape"
  "Query shape CLOSED at the serve boundary (TCP): same as serveDatagram_total — \
   the shared `queryProblem` classifier (total, `queryProblem_spec`) gates the TCP \
   serve path identically. No query-shape binder remains. (plan-2 Query-shape row \
   FULLY CLOSED; CHAOS, ANY, 032, 033, 042, 044b)."
-- EDNS row (findings 049/050/056/063/065/016): the serve capstones now carry
-- `hedns : Edns.ednsProblem query = none` — a served-shape gate like
-- `queryProblem = none`, NOT a scope door: a query failing it is *handled*
-- (multi-OPT → FORMERR per RFC 6891 §6.1.1, version > 0 → BADVERS per §6.1.3,
-- pinned by `Proof.Edns.serveDatagram_ednsProblem` + the `ednsProblemResponse_*`
-- pins), exactly as `queryProblem`'s REFUSED/FORMERR arms handle shape problems;
-- the census classifier deliberately does not match it. Sizing is two-sided:
-- the delivered-wire conjuncts of `serveDatagram_total` pin
-- `truncateUdp … (Edns.clientCap query)` to ≤ cap with the exact TC iff
-- (`Proof.Edns.truncateUdp_size_cap`/`truncateUdp_tc_iff`,
-- `Edns.clientCap_ge/_noOpt/_opt/_eq_512_iff`), replacing the one-sided
-- `clientCap_le`-only story (findings 049/050/063).
-- The resolver-CORE capstones legitimately assume IN / rd-cleared / non-ANY upstream
-- queries: the serve boundary guarantees only such queries reach the core (non-IN is
-- REFUSED and ANY is answered by the serve arm before resolution). These are genuine
-- below-boundary premises, hence justified rather than open.
justified_scope resolveWithIO_verdict_sound "query-shape"
  "Query shape (resolver core): the core only ever resolves IN, rd-cleared, non-ANY \
   upstream queries — the serve boundary REFUSES non-IN (queryProblem) and answers \
   QTYPE=ANY via the RFC 8482 serve arm (Server.serveDatagram_any) BEFORE the core \
   runs, and buildSubQuery clears rd. rd = false is the ITERATIVE-UPSTREAM-QUERY \
   convention (RFC 1035 §4.1.1): the resolver strips rd on its own upstream queries \
   (Server.buildSubQuery rd := 0; Spec.Net.queryDatagram_clears_rd). It is NOT a \
   restriction on real recursive CLIENTS — queryProblem REQUIRES client rd = 1 to \
   serve at all (performsRequestedOperation), and the client's rd bit is echoed back \
   on delivery (deliveredResponse rd := query.header.rd, review #007/#010a). So \
   qclass=IN / rd=false / qtype ≠ ANY are guaranteed below-boundary premises, not \
   doors; recursive rd=1 client queries are fully in scope. (plan-2 Query-shape \
   row CLOSED)."
justified_scope ioResumeLoop_sound "query-shape"
  "Query shape (resolve loop core): the loop only runs on IN, rd-cleared upstream \
   queries the serve boundary lets through (non-IN REFUSED, ANY served by arm). \
   rd = false is the iterative-upstream-query convention, not a client-input gate: \
   the resolver clears rd on upstream queries (buildSubQuery) and echoes the \
   client's rd on delivery (review #007/#010a); recursive rd=1 clients are served \
   (queryProblem requires rd=1). Guaranteed below-boundary premises. (plan-2 \
   Query-shape row CLOSED)."

-- `serveSeq_total_mkSbelt` and `serveSeq_total_primed` are the production-SBELT and primed-cache
-- siblings of `serveSeq_total` (quick-wins / W2a). Their query-shape door is CLOSED with
-- `serveSeq_total`'s (no `InScope` binder); the cache-state and adversary rows remain seeded.
open_scope serveSeq_total_mkSbelt "query-shape"
  "Query shape CLOSED: like serveSeq_total, no `InScope` binder remains (non-IN → REFUSED, \
   ANY → RFC 8482 serve arm). Documenting no-op. (plan-2 Query-shape row CLOSED; CHAOS, ANY)."
open_scope serveSeq_total_mkSbelt "cache-state"
  "State: production-SBELT sequence totality still runs from DnsCache.empty. \
   Close by the primed-cache variant serveSeq_total_primed (plan-2 State row; W2a)."
open_scope serveSeq_total_primed "query-shape"
  "Query shape CLOSED: like serveSeq_total, no `InScope` binder remains (non-IN → REFUSED, \
   ANY → RFC 8482 serve arm). Documenting no-op. (plan-2 Query-shape row CLOSED; CHAOS, ANY)."
justified_scope serveSeq_total_primed "cache-state"
  "NOT a scope door: `serveSeq_total_primed` is the DEPLOYED capstone — its cache is \
   `primeWrites DnsCache.empty resp` = exactly the state `main` serves from after root-hint \
   priming (W2a), not an empty-cache restriction. The census flags `DnsCache.empty` because it \
   appears inside the `primeWrites` run expression, but this is the real Main initial state. \
   (plan-2 State row: deployed base, justified)."

/-! ### Seed: adversary-model doors

**Adversary-model row CLOSED** (plan-2 Adversary-model row; 038, 017).  The `WorldModels` /
`WorldModelsTcp` premises are no longer open doors: `VeriDNS/Proof/AdversaryComplete.lean` proves
the adversary model *complete* over the accepted-datagram space —
`AdversaryComplete.WorldModels_complete` shows every datagram the resolver accepts as a reply
realises a `WorldModels` disjunct (honest ∨ `SpoofReply`), and
`AdversaryComplete.accepts_requires_source_and_query_match` ties the un-accepted (junk-source /
id-mismatch) case to the shim's accept predicate (dropped below the shim, the 017 boundary), so
no wire datagram escapes both.  `AdversaryComplete.serveDatagram_verdict_sound_any_wire` is the
any-wire corollary.  These `WorldModels`/`WorldModelsTcp` gates are therefore *justified*
below-boundary premises (a complete, non-vacuous model of what the wire can deliver), not scope
doors — so they carry `justified_scope`, pointing at the completeness proof.

The `resolveWithIO_spine_adequate_warm` / `serveDatagram_depth1_adequate` gates below remain
`open_scope`: they assume a `CooperativeNetworkAddr` (an *honest* network that actually answers)
for the adequacy/liveness direction, which model completeness does not close — adequacy needs the
network to reply, not merely that any reply is modelled. -/

justified_scope serveSeq_total_mkSbelt "adversary"
  "Adversary model COMPLETE (AdversaryComplete.WorldModels_complete): every accepted wire datagram realises a WorldModels disjunct; unaccepted junk is dropped below the shim (accepts_requires_source_and_query_match). Soundness vs the model = soundness vs every wire. (plan-2 Adversary-model row CLOSED; 038, 017)."
justified_scope serveSeq_total_primed "adversary"
  "Adversary model COMPLETE (AdversaryComplete.WorldModels_complete): every accepted wire datagram realises a WorldModels disjunct; unaccepted junk is dropped below the shim. (plan-2 Adversary-model row CLOSED; 038, 017)."
justified_scope serveSeq_total "adversary"
  "Adversary model COMPLETE (AdversaryComplete.WorldModels_complete): the disjunction is exhaustive over the accepted-datagram space — every wire datagram either realises a disjunct or is dropped below the shim. (plan-2 Adversary-model row CLOSED; 038, 017)."
justified_scope serveDatagram_verdict_sound "adversary"
  "Adversary model COMPLETE (AdversaryComplete.WorldModels_complete / serveDatagram_verdict_sound_any_wire): soundness vs the model is soundness vs every accepted wire datagram. (plan-2 Adversary-model row CLOSED)."
justified_scope serveDatagram_total "adversary"
  "Adversary model COMPLETE (AdversaryComplete.WorldModels_complete): the model is exhaustive over the accepted-datagram space. (plan-2 Adversary-model row CLOSED)."
justified_scope serveTcpDatagram_total "adversary"
  "Adversary model COMPLETE for TCP (AdversaryComplete.WorldModelsTcp_complete): every accepted TCP datagram realises the honest disjunct; the honest arm subsumes the UDP SpoofReply shape (AcceptsTcp_realises_SpoofReply). No MITM arm by tcp-plan decision 5, a deliberate choice not a gap. (plan-2 Adversary-model row CLOSED)."
justified_scope resolveWithIO_verdict_sound "adversary"
  "Adversary model COMPLETE (AdversaryComplete.WorldModels_complete): soundness vs the model is soundness vs every accepted wire datagram. (plan-2 Adversary-model row CLOSED)."
justified_scope ioResumeLoop_sound "adversary"
  "Adversary model COMPLETE for TCP (AdversaryComplete.WorldModelsTcp_complete): the resume loop's WorldModelsTcp premise is a complete honest-only model; the honest arm subsumes the SpoofReply shape via tcpSpoofReply_of_honest. (plan-2 Adversary-model row CLOSED)."
justified_scope resolveWithIO_spine_adequate_warm "adversary"
  "INTRINSIC to the adequacy (liveness) direction, not a scope door: adequacy proves \
   the resolver DELIVERS, which is impossible against a silent or lying network. The \
   CooperativeNetworkAddr premise (an honest, responsive network) is a genuine \
   precondition of any liveness theorem — a non-responsive network is not a resolver \
   bug. Since finding 061 the premise is also TIMELY, not vacuous: the clock is live \
   (every exchange advances World.clock by the latency schedule World.tick), the old \
   frozen-clock hdl was replaced by TimelyWorld w.clock w.tick w.exchCtr (now+budget) \
   fuel (start clock + worst-case total descent latency < deadline), which is FALSE \
   for slow worlds — the deadline dual run_resolveWithIO_deadline_witness proves such \
   worlds get the deadline error (client SERVFAIL), and the tick ≡ 0 sibling \
   resolveWithIO_spine_adequate_warm_tick0 recovers the pre-061 statement verbatim. \
   The SOUNDNESS direction (serveDatagram_verdict_sound etc.) carries no such \
   premise and is proven complete over every wire (AdversaryComplete). (plan-2 \
   Adversary-model row: adequacy-side justified; 061 CLOSED.)"
justified_scope serveDatagram_depth1_adequate "adversary"
  "INTRINSIC to adequacy (liveness): delivery cannot be proven against a silent/lying \
   network, so CooperativeNetworkAddr is a genuine liveness precondition, not a door. \
   Since 061 the cooperative premise is also timely, not frozen-clock: this capstone's \
   two rounds carry hdl (round 1 at w.clock) and hdl₂ (round 2 at w.clock + \
   w.tick w.exchCtr — the root round's latency has elapsed); a slow world falsifies \
   hdl₂ and hits the deadline branch instead (run_ioResumeLoop_deadline_after_referral, \
   vector deadlineFiresMidResolution). Soundness is proven vs every wire \
   (AdversaryComplete). (plan-2 Adversary-model row: adequacy-side justified; 061.)"

/-! ### Seed: topology door -/

open_scope resolveWithIO_spine_adequate_warm "topology"
  "Topology (035 coverage CLOSED; gate persists in generalised form). The spine capstone still \
   STATES the single-NS SlistShape, but that shape is now the singleton instance of the set-valued \
   SlistShape' (VeriDNS.Proof.Adequacy.SlistShape', with SlistShape.toShape'/SlistShape'.toSingleton \
   the round trip; VeriDNS/Proof/Failover.lean). The multi-homed FAILOVER coverage plan-2 asks for \
   is proven and axiom-clean: Failover.run_ioResumeLoop_failoverAnswer delivers when the first \
   server of a multi-homed cut times out and a distinct second server answers (impl mechanism = \
   bestWithAddress least-tried-first rotation + markQueried, composing run_ioResumeLoop_timeout' \
   with run_ioResumeLoop_answer), and SlistShape'.of_fromNsWithGlueAll builds the set shape for a \
   genuinely multi-NS cut with NO name/address collapse. The generalised collapse-point primitives \
   (reGlue_owned; SlistShape'.{bestWithAddress,markQueried,addressTargets_none}) are in place. This \
   gate is detected only because the spine capstone's binder is not yet migrated to SlistShape'; \
   the finding-035 gap itself is closed (plan-2 Topology row; 035)."

/-! ### Seed: cache-state door -/

open_scope serveSeq_total "cache-state"
  "State: the sequence-totality base case runs from DnsCache.empty. Close by the primed-cache \
   variant serveSeq_total_primed (plan-2 State row; W2a)."

/-! ### Seed: rcode-scope doors -/

justified_scope resolveWithIO_spine_adequate_warm "rcode-scope"
  "Client well-formedness precondition, NOT an error-reply scope door. `hrcq : q.header.rcode = noError` constrains the INCOMING CLIENT QUERY (q = state.lastQuery), which buildSubQuery echoes verbatim into every outgoing sub-query rcode (buildSubQuery_withSecrets_header: withSecrets rcode = q.header.rcode). A well-formed DNS query carries rcode 0 (RFC 1035 §4.1.1). The gate does NOT constrain the upstream reply rcode — the NODATA error-reply dual exists (resolveWithIO_flatAuthoritative_nodata_adequate), and NXDOMAIN adequacy (resolveWithIO_flatAuthoritative_nxdomain_adequate) is likewise reply-error. A lone SERVFAIL/timeout reply is a retry (.goto .sendQueries), not a leaf terminal, so it has no per-round delivery dual — SERVFAIL adequacy is a whole-descent exhaustion property. (plan-2 Rcode-scope row CLOSED)."
justified_scope serveDatagram_depth1_adequate "rcode-scope"
  "Client well-formedness precondition, NOT an error-reply scope door. `hqsf : (q.header.rcode == serverFailure) = false` constrains the INCOMING CLIENT QUERY rcode, echoed into the outgoing sub-query by buildSubQuery (buildSubQuery_withSecrets_header). A well-formed DNS query carries rcode 0 (RFC 1035 §4.1.1); it does NOT constrain the upstream reply. The NODATA reply-error dual exists (resolveWithIO_flatAuthoritative_nodata_adequate); SERVFAIL replies retry rather than terminate, so they have no per-round delivery dual. (plan-2 Rcode-scope row CLOSED)."

/-! ### Seed: direction doors (capstone-level; not binder-detected)

The soundness/total capstones have no completeness dual, so a wrong answer (spurious NODATA,
misclassified referral) still satisfies them. This is the largest open door per plan-2. It is
recorded here at the capstone level (there is no single binder to attach it to). -/

open_scope serveSeq_total "direction"
  "Direction: soundness/totality with no completeness dual. Close by a total Classify theorem + \
   completeness corollary (plan-2 Direction row; 040, 041/045)."
open_scope serveDatagram_verdict_sound "direction"
  "Direction: soundness with no completeness dual. (plan-2 Direction row; 040, 041/045)."
open_scope resolveWithIO_verdict_sound "direction"
  "Direction: soundness with no completeness dual. (plan-2 Direction row; 040, 041/045)."

/-! ### Observability / egress / freshness rows (findings 054, 062, 060b, 002)

These rows are CONCLUSION-side strengthenings, not scope-gate binders, so the census has
nothing to annotate; this block is the ledger record.

* **054 (client sends were invisible) — CLOSED, delivery pinned.** `sendTo`/`tcpSend` are now
  visible `DnsCmd` steps in `Prog` (`World.sent`/`World.tcpSent` delivery logs).  The resolver
  and reply-assembly phases are proven send-free
  (`SentMinimised.resolveWithIO_sends_frame` / `replyForResolution_sends_frame`, via the
  `AllSent` program-tree cover), and the serve capstones now pin the delivery log EXACTLY:
  `serveTcpDatagram_total` gains
  `w'.tcpSent = w.tcpSent ++ [frameTcp (encode (withReplyOpt query (deliveredResponse query
  resp)))]` (SERVFAIL dual: the framed encoded `withReplyOpt`-wrapped error reply), and
  `serveDatagram_total` gains `w'.sent = w.sent ++ [((truncateUdp (encode (withReplyOpt query
  …)) … (clientCap query)).1, clientAddr)]` — the single appended entry IS the verified reply,
  to THE requesting client address.
* **062 (egress do-not-query mask) — CLOSED BY THEOREM.**
  `SentMinimised.ioResumeLoop_sent_egress` / `resolveWithIO_sent_egress`: every reachable
  `exchange`/`tcpExchange` node in ANY world satisfies `EgressOk` — the destination is
  `ipv4ToAddr ip` for an `ip` with `blockedEgress ip = false`.  The TC→TCP fallback needs no
  separate impl guard: it reuses the SAME address that passed the UDP-first gate (the
  `tcpForward` node is only reachable under `hegress`), and the `AllSent` cover pins its
  `tcpExchange` node with the same witness.
* **060b (claimed ACL mask off-by-one) — SPEC'D, CLAIM REFUTED.**
  `SentMinimised.aclEntry_matches_iff` / `aclEntry_matches_interval` give the exact
  prefix/interval semantics of `AclEntry.matches`; the upper half of every blocked range IS
  blocked (Test/Loop.lean `EgressMask` vectors pin both halves, just-outside neighbours, and
  the sockaddr round-trip `clientIp_ipv4ToAddr`).
* **002 (TXID/case-seed freshness) — PINNED.** `SentFresh.ioResumeLoop_sent_fresh` /
  `resolveWithIO_sent_fresh`: the TXID and 0x20 case seed on every upstream wire are THE two
  `randomId` draws made immediately before that send (`withSecrets_id` /
  `withSecrets_question` tie the wire header id and question casing to the draws).  A
  constant-ID or draw-ignoring mutant breaks the theorem. -/

/-! ### Closed-finding notes (delivered-answer soundness; no gate binder)

**Finding 068 (CLOSED)** — qtype-relevant delivery (RFC 1034 §3.6.2). The
delivered-answer conjunct of the serve capstones was STRENGTHENED (a
soundness tightening, not a new door): the answer section a client receives is
now `typeScrub qm.qtype (scrubAnswer qm.qname v.answer)` — every delivered
record matches the query type or is a chase-chain CNAME. The owner scrub alone
let an entitled answer smuggle same-owner wrong-type records (e.g. a junk TXT
riding the queried A), and the tc=1 acceptance arm could deliver a wrong-type
record outright. Impl `typeScrubB ∘ scrubAnswerB` in `deliveredResponse`; model
twin `Spec.Net.typeScrub`/`typeRelevant`; α-bridge `αSection_typeScrubB_eq`;
pins `deliveredResponse_answer_qtype_relevant` / `typeScrub_relevant`.
`serveDatagram_verdict_sound` re-verified axiom-clean. This tightens the
soundness direction; it does NOT supply the missing completeness dual (the
Direction door above stays open).

**Finding 039 (CLOSED)** — CNAME-target NXDOMAIN keying (RFC 6604 §3). The
negative-cache trigger was tightened IN LOCKSTEP on both sides: the model
`Cache.absorbNeg` NXDOMAIN arm and the impl `Server.negativelyCacheable`
NXDOMAIN disjunct now BOTH require an empty answer section. A CNAME chain
terminating in NXDOMAIN reaches the serve-layer store with the chain
prepended (`finalizeAnswer`), so it no longer plants a name-wide
`lookupNxdomain` negative at the ORIGINAL query name (which exists — it owns
a CNAME); the client still receives the NXDOMAIN rcode (RFC 6604 §3, matches
unbound). Bridge re-proven: `negativelyCacheable_iff_absorbNeg_trigger` (both
disjuncts now carry the empty-answer conjunct). Producer-gate pins:
`Proof.Server.negativelyCacheable_chained_nxdomain` /
`storeNegativeIfCacheable_chained_nxdomain` (the ONLY nxdomain-negative
producer is a no-op on a chained response) and the model dual
`Spec.Net.absorbNeg_chained_nxdomain`. Vectors: `chainedNxdomainNotWideKeyed`
+ `otherTypeAfterChainedNxdomainNotDenied` (Test/Loop.lean — a follow-up
qtype=CNAME query at the original name answers NOERROR from the cached CNAME
instead of the former wide-key NXDOMAIN denial). Residue: the correctly-keyed
negative at the CHAIN-FINAL target is not written by the serve layer (it keys
at the echoed qname only) — a cache-efficiency follow-up, not a soundness
door.

**Finding 019 (CLOSED)** — CNAME-conduit wrong-record caching. The
resolver-core chase arm and the model were restricted IN LOCKSTEP to the
chased CNAME slice: the impl arm now caches `cnameRaws (echoedQname)
resp.answer` (the `extractCname` predicate — owner at the query name AND
type=CNAME) instead of `ownerRaws` (all qname-owned records of any type), and
the `answerCname`/`trustedCname` rules' cache write is `Response.cnameOwned`
(the `cnameRR` find?-predicate as a filter) instead of `answerOwned`. A junk
same-owner record of another type riding a CNAME response no longer enters
the cache through the chase arm — the cache side now mirrors the delivery
side (`prependCnameLink`). The write-refinement cascade re-proven:
`chasedCname_write_WriteRefines(_ref)` / `section_cnameOwner_extra_perm` /
`absorb_cnameOwned_pos` (NetworkSim), `cname_link_write_WriteRefines_echo`
and the six chase-arm sites of `ioResumeLoop_sound` (IoResumeSound), the
`resume_cname_*`/`afterResume_cname_*` inversion family and
`stepAnalyzeResponse_cname` (Refinement), `αSection_cnameRaws_eq`
(AnswerTerminal), plus the `cnameOwned` congruence/ownership lemmas
(`absorb_cnameOwned_congr`/`_pos_owner`/`_topServed_owner`,
NetworkSemantics). The shrink weakened obligations as predicted
(Subperm-framed writes). Vector: `junkRideAlongCnameNotCached`
(Test/Loop.lean — after the chase the chased CNAME is cached at the original
name, the junk same-owner TXT is NOT; red before the fix). -/

/-! ### Behaviour-deviation rows (external-review findings triage, docs/latest-report.md)

Finding **053** (0x20-cased rdata defeats cache dedup, high) is **FIXED**, not ledgered: the
RRset-member dedup identity at the cache write boundary is now case-insensitive in the embedded
rdata names of the well-known name-bearing types (`Impl/Cache.rdataEqCI`; RFC 4343 §3, RFC 3597 §7
— unknown types stay opaque bytes). Stored bytes are not rewritten, only the member identity.
Pinned by `VeriDNS.Proof.Cache.store_ci_variant_dedups` + the `ciDedup*`/`ciUnknownTypeNotFolded`
`#guard` vectors (Test/Loop.lean); the proof layer (`sameData`, `Removes`, `LookupComplete`)
carries the CI identity in lockstep. The rows below record the four triaged residuals. -/

justified_scope serveDatagram_total "behaviour"
  "Finding 024 (negcache aa-blindness) — JUSTIFIED, the hardening is forbidden by spec: \
   RFC 2308 §3 makes SOA-accompanied negative responses cacheable with NO AA precondition \
   (§5's MUST is about the SOA's presence, not AA), and unbound likewise negative-caches on \
   the iterative path without AA. The actual defenses, all present: (i) the negative key is \
   exactly the resolved qname/qtype/qclass (storeNegative from replyForResolution), so a \
   server can only 'poison' the very query the descent already trusts it for on an unsigned \
   path; (ii) the SOA owner must be an ancestor of the qname — extractSoaNegative's \
   isAncestorB guard, the 012/013 fix, mirrored by the model soaNegTtl isAncestor conjunct; \
   (iii) TC=1 responses are never negative-cached (negativelyCacheable tc==0, the #008 pin); \
   (iv) negative TTL = min(SOA MINIMUM, SOA TTL) capped at 10800 (computeNegativeTtl / \
   capNegativeTtl, RFC 2308 §3/§5). (latest-report residual row 024.)"

justified_scope serveSeq_total "behaviour"
  "Finding 034 (phantom-value TTL) — DIAGNOSED, no phantom-TTL source found in the current \
   tree. TTL-provenance audit: (i) every accepted upstream reply passes sanitizeTtlsCap = \
   capTtlRR — RFC 2181 §8 high-bit TTLs are zeroed, the rest capped at 604800; (ii) cache \
   hits serve expiry − now, monotone decreasing and fresh-guarded (never wraps); (iii) \
   intra-RRset TTL differences normalize to the group minimum at the write boundary \
   (normRaws/groupMinTtl, RFC 2181 §5.2); (iv) TTL=0 records are never cached (storeChecked \
   ttl==0 guard — RFC 1035 use-once); (v) negative TTL = min(SOA MINIMUM, SOA TTL) capped at \
   10800, re-served decremented (NegativeEntry.authority); (vi) the only impl-fabricated TTL \
   is the RFC 8482 §4.2 synthesized HINFO's 3600, spec-sanctioned. Most probable original \
   repro: the pre-remediation ingest (sanitizeTtls DROPPED excessive-TTL replies instead of \
   capping), superseded by capTtlRR. If a resumed rig re-reproduces 034, capture the exact \
   record+TTL — the audit above enumerates every producer. (latest-report residual row 034.)"

open_scope resolveWithIO_verdict_sound "behaviour"
  "Finding 059 (DS query at a zone cut routed to the child when its NS set is cached) — OPEN, \
   deferred with a precise boundary: RFC 4035 §3.1.4.1 requires DS to be answered from the \
   PARENT zone, but stepFindServers.walkNs is qtype-blind and starts the NS walk at sname, so \
   a cached child NS set captures qtype=DS descent (documented by the intended-behavior vector \
   Test.Loop.dsWalkTargetsChildToday — flip it when fixing). The fix (start the walk one label \
   short for qtype=DS) is NOT contained: walkNs is mirrored in lockstep by the model \
   findServers rule (the refer keystone re-derives NS from cache), by findServersTouches (LRU \
   anti-drift pins), and feeds the SentMinimised revealed-labels ladder — a qtype-conditional \
   descent start must move through Impl+Spec+Refinement+IoResumeSound together. BOUNDED: \
   veri-dns performs no DNSSEC validation and never originates DS queries; only a client's \
   explicit DS query at a cached cut is mis-routed, the reply is cached under the DS key only \
   (no cross-type corruption), and a child zone commonly answers the DS from its own copy or \
   returns NODATA. (latest-report 059; RFC 4035 §3.1.4.1.)"

justified_scope serveDatagram_verdict_sound "behaviour"
  "Finding 060a (DNAME stripped by the CNAME-only delivery scrub) — JUSTIFIED deviation with \
   an exact statement: when qtype=DNAME the record IS the entitled answer (owner = qname, the \
   chain-reachable seed) and IS delivered — scrubAnswerB filters by owner reachability, never \
   by type (pinned: Test.Loop.dnameAtQnameDelivered). The deviation: an upstream DNAME \
   accompanying its RFC 6672 §3.2 synthesized CNAME is dropped from the delivered answer \
   because its owner (a strict ANCESTOR of a chain link) is not itself chain-reachable, while \
   unbound forwards DNAME+CNAME (documented: Test.Loop.dnameChainLinkScrubbedToday — flip when \
   extending). Correctness preserved: RFC 6672 §3.2 lets a DNAME-oblivious client follow the \
   delivered synthesized CNAME verbatim; nothing wrong is served, one redundant-for-resolution \
   record is withheld. Delivering it requires widening AnswerAuthenticWrt and the scrubAnswer \
   equality baked into serveDatagram_verdict_sound's statement (the #003 remediation's only \
   capstone-statement change lives in exactly this conjunct) with a type-39 \
   owner-is-ancestor-of-a-chain-link arm — a deliberate deferral, recorded here rather than \
   made silently. (latest-report 060a; RFC 6672 §3.2.)"

/-! ## QNAME-minimisation robustness (findings 051/052/064/055, 2026-07-17)

**Findings 051/064 (CLOSED, impl-bug HIGH)** — strict RFC 8020 denial
NXDOMAINed existing names behind ENT-mishandling servers. The strict-denial
terminal of `ioResumeLoop` was replaced by the RFC 9156 §3 (6d) NON-strict
fallback (unbound `qname-minimisation-strict: no` default): a minimised-probe
NXDOMAIN is consumed and the loop re-probes with the FULL qname (`revealed :=
labelCount sname`; at most one fallback per sname since `probeRoundB sname
(labelCount sname) = false`). `storeProbeNegative` is no longer invoked (the
probe denial is not believed — caching it would deny the very full-name
re-probe). Only a full-name NXDOMAIN is delivered: the theorem-level pin is
the `hprobe : probeRoundB … = false` hypothesis of `run_ioResumeLoop_nxdomain`
(the ONLY network NXDOMAIN delivery lemma) together with
`run_ioResumeLoop_probeNxdomainFallsBack` (the probe arm recurses, delivering
nothing). Every soundness/completeness induction treats the arm as an IH
recursion (markQueried-only, Subperm-framed, no model step); the model KEEPS
the strict `ancestorDenied` rule (sound for cooperative servers). Mocks:
`fullNameNxdomainFinal` (full-name NXDOMAIN still final + client-keyed
negative cache), `probeNxdomainEntRecovered` (existing-name-behind-ENT
resolves; RED under the old strict behaviour).

**Finding 052 (CLOSED, coverage-gap medium)** — minimised-probe timeout had no
fallback and re-sent the probe until the retry budget expired. The timeout arm
(and its unusable-reply siblings: accept/decode/sanitize failure, blocked
egress — all flow through `upstreamResp = none`) now recurses at
`Server.fallbackRevealed sname revealed` (= `labelCount sname` at a probe
round, identity at a full round — `probe_denial_falls_back` /
`full_round_no_fallback`). Pinned by `run_ioResumeLoop_timeout`'s conclusion
and the `probeTimeoutFallsBackToFull` / `retransmitFreshSecrets` mocks.

**Finding 055 (CLOSED, impl-bug medium)** — upstream FORMERR to an OPT-bearing
sub-query retry-looped to SERVFAIL instead of retrying once without OPT
(RFC 6891 §6.2.2; deferred by the EDNS agent). Landed as: a `noEdns : Bool`
field on `Resolver.State` (default false) consulted by `buildSubQuery`
(`additional/arcount` conditional — so `SentShape` holds VERBATIM, the
stripped query being a `buildSubQuery` image of the flagged state) + one new
loop arm `rcode = formatError ∧ ¬noEdns → recurse { state with noEdns :=
true }` between the unfollowable and probe arms (fires at most once per
resolution — a FORMERR to an already-EDNS-free query takes the ordinary retry
path). Proof cost as mapped: +1 by_cases (IH recursion) in each loop-walking
induction (IoResumeSound ×2, IoResumeErrorSound ×2, ResolveWithIOSound ×6,
NameTree, NameTreeComplete + `stateOK_slistNoEdns`, Adequacy terminates,
SentMinimised/SentFresh auxes), a new `rcode ≠ FORMERR` hypothesis (`hfe`) in
the post-TC-guard FreeIO run lemmas — derived internally where the rcode is
pinned (nxdomain / probeNxdomainFallsBack / nodata) — threaded through
`DescentChain` and the flat/delegating adequacy wrappers to the client-level
`hrcq : rcode = noError` facts, and a `state.noEdns` case split in the two
`buildSubQuery_withSecrets_roundtrips*` OPT-singleton pins plus the
`treeRespond_*_classified`/`_probeConsumed` guard bundles. Mock:
`formerrRetriesWithoutEdns` (first sub-query advertises OPT, the retry after
FORMERR is EDNS-free, the resolution completes NOERROR). RESIDUE: the flag is
per-RESOLUTION, not per-server (coarser than unbound's per-server EDNS status
cache — after one FORMERR the rest of that resolution's servers are also
queried EDNS-free; safe, mildly pessimistic), and no negative EDNS status is
remembered ACROSS resolutions (each query re-probes with OPT first). -/

/-! ## Finding 061 (CLOSED 2026-07-17): the liveness clock is LIVE

The review's headline spec finding: the adequacy/liveness capstones ran against a
frozen clock (`DnsCmd.run` returned the world unchanged on `.exchange`, so `.now`
was constant), making every deadline test decidably false in the model — a
SERVFAIL-on-deadline mutant stayed green. Closed by making the clock live and the
deadline behaviour theorem-visible:

* **Model**: `FreeIO.World` gains a latency schedule `tick : Nat → UInt32`
  (default `fun _ => 0`) and an exchange counter `exchCtr`; every
  `.exchange`/`.tcpExchange` (including timeouts) advances `clock` by
  `tick exchCtr` (`World.afterExchange`). Zero-latency worlds reproduce the
  pre-061 behaviour EXACTLY (`run_world_clock_frame_tick0`,
  `TimelyWorld.of_tick0`, and every pre-existing Test/AdequacyPins vector
  unchanged).
* **Timeout witness (the mutant-killer)**:
  `FreeIO.run_ioResumeLoop_deadline_after_referral` and the capstone-level
  `FreeIO.run_resolveWithIO_deadline_witness` — a world whose first round's
  latency crosses the deadline REACHES the deadline branch and returns the
  deadline error (mapped to client SERVFAIL by `replyForResolution`). Deleting
  the `t ≥ deadline` check or changing its behaviour breaks these theorems and
  flips the decidable vectors `deadlineFiresMidResolution` /
  `deadlineSurvivesFastWorld` (Test/AdequacyPins.lean).
* **Adequacy restated**: the multi-round adequacy capstones now carry the honest
  budget account `TimelyWorld w.clock w.tick w.exchCtr deadline fuel`
  (`resolveWithIO_spine_adequate{_warm}`, `resolveWithIO_within_bound`,
  `resolveWithIO_spine_no_starvation`, `resolveWithIO_flatMultiLabel_adequate`)
  or per-round `hdl₂` premises (`resolveWithIO_depth1_adequate`,
  `serveDatagram_depth1_adequate`, `run_ioResumeLoop_failoverAnswer`,
  `run_ioResumeLoop_retryThenAnswer`); the premise is genuinely bivalent — false
  exactly for the slow worlds the dual covers. `_tick0` siblings restate the
  old frozen-clock forms as corollaries
  (`resolveWithIO_spine_adequate_warm_tick0`,
  `resolveWithIO_flatMultiLabel_adequate_tick0`).
* **Deliberate residue**: (a) the multi-datagram serve-TRACE theorems
  (`serveSeq_sound`/`serveSeq_total*`) take `∀ i, w.tick i = 0` — they pin the
  cache pack and world model at ONE clock across a whole datagram sequence;
  lifting that is a cache-expiry-over-time refinement, not a deadline-behaviour
  gap (the per-RESOLUTION deadline logic below them is fully live). (b) TCP
  per-connection READ timeouts (057/067) are driver-level (`Main.lean` socket
  timeouts), outside the `Prog`/`World` model — the model's `tcpExchange` costs
  one tick like any exchange, but connection lifetime is not modelled; recorded
  as a deliberate boundary, not silently. -/

/-! ## Census, ledger generation, and the lint -/

scope_census

generate_scope_ledger

scope_gate_lint
