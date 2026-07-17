# W4 hypothesis audit — slice: server, delivery, codec, cache

Scope: `VeriDNS/Proof/{Server,ServeSound,ServeSequence,ServeTcp,AnswerTerminal,AnswerScrub,
AnswerScrubAlpha,DeliveredAuthentic,DeliveredWire,Message,MessageValid,Cache,Resolver,RData,
DomainName,SentMinimised,QnameMin,TtlCap,GlueConnector,Absorb,Primitives,Parsec,Header,Question,
ResourceRecord,TcpFraming}.lean`, plus the serve capstones that live in
`ResolveWithIOSound.lean` (`serveDatagram_verdict_sound`, `serveDatagram_total`) because they are
named special-attention items for this slice. Method: read-only textual/structural analysis;
premises whose only consumer is `simp_all`/`omega`/`assumption` are marked *uncertain-unused*.
Severity: 5 = worst.

Classes: **U** = unused, **UR** = unrealistic / scopes away from the running system,
**OS** = over-scoped conclusion (name promises more than statement), **LB** = load-bearing and
fair. **D** = derivable from another premise (kept for factoring; not a defect).

## Headline findings

| # | Theorem | Hypothesis / conclusion element | Class | Evidence | Suggested action | Sev |
|---|---|---|---|---|---|---|
| 1 | `serveDatagram_verdict_sound`, `serveDatagram_total`, `serveTcpDatagram_total`, `serveSeq_sound/_total` | full cache-invariant pack (`CacheWf`, `CacheNsCanon`, `CacheCnameCanon`, `WfRR`-all, `CacheNsDistinct`, `OneExpiryPerKey`, `size ≤ capacity`, `CacheNegWf`, `CacheRecCanon`, `CacheNegSoaCanon`) **at the initial cache** | UR (at the real entry point) | The pack is established only for `DnsCache.empty` (`ServePack_empty`, ServeSequence.lean:33) and preserved through serves. But `main` (Main.lean:140) does **not** start from empty: it serves from `primeRootHints rootServers DnsCache.empty now`. `primeRootHints` (Main.lean:37–60) performs two `cacheUnlessTruncated` writes from a decoded-but-**unsanitized** network reply (no `sanitizeTtlsCap`, unlike the verified resolve path), and no theorem `ServePack (primeRootHints …)` exists — `grep primeRootHints VeriDNS` hits only Main.lean. Every capstone invariant premise is therefore *assumed, never established, on the real ingest path*. Excessive TTLs from a hostile first hop reach `storeChecked` uncapped (`now + rr.ttl.toNat.toUInt32` wraps), which is exactly what `CacheWf`/`OneExpiryPerKey` protect against. | Prove `ServePack (primeRootHints …) clk qc` (priming uses the same `cacheUnlessTruncated`/`storeChecked` machinery the preservation lemmas already cover), or route priming through the verified resolve path; add `sanitizeTtlsCap` to the priming path either way. | **5** |
| 2 | `serveDatagram_total`, `serveTcpDatagram_total` (`hqany`, `hqc`); `serveSeq_sound/_total` (`hscope : ∀ d ∈ ds, InScope …`) | `qu.qtype.toNat ≠ 255` and `αClass qu.qclass = some RRClass.in` | UR | `queryProblem` (Impl/Server.lean:118) filters only qdcount≠1 / opcode / rd — it does **not** reject qtype=ANY or non-IN classes, so the running server *serves* `dig ANY` and `dig CH TXT version.bind` with zero theorem coverage. Worse, `InScope` (ServeSequence.lean:53) universally quantifies the gate over the whole trace: **one** ANY or CHAOS query in `ds` voids `serveSeq_total` for the entire trace, including all the IN/A traffic around it. This is the plan's canonical example of an unrealistic gate ("class-IN-only or qtype ≠ ANY gates that hide the general case"). Known T5 scope-keep. | Short term: refactor `serveSeq_sound` so out-of-scope datagrams degrade to invariant-preservation-only (they still run `serveDatagram`!) instead of voiding the trace theorem. Long term: either extend the model to `QType.star`/non-IN, or make the impl refuse them (`queryProblem` → notImplemented), which would turn the gate into a derivable fact. | **4** |
| 3 | `serveDatagram_verdict_sound` / `serveTcpDatagram_verdict_sound` — error disjunct | conclusion conjunct `∃ slist v, HasVerdictAt … ∧ v.rcode = servFail ∧ v.answer = []` | OS | Discharged for the catch-all error message by `gaveUp_hasVerdictAt` (WorldNetwork.lean:427) over `Resolves.gaveUp` (Spec/NetworkSemantics.lean:1661), an **unconditional** constructor: any SERVFAIL/[] is a model verdict for any cache/slist/query. The conjunct is trivially satisfiable, so the error arm's "verdict soundness" carries no information beyond cache-invariant preservation. (Matches the recorded open item "give-up 4" in the total-simulation notes.) | Condition `Resolves.gaveUp`/`exhausted` on a genuine failure witness (all slist candidates tried/timed out), or annotate the capstone that the error arm is invariants-only. Feed to W2. | **4** |
| 4 | `serveDatagram_verdict_sound` — delivery conjunct; `serveTcpDatagram_verdict_sound` — framing conjunct | wire claims gated on `encode (deliveredResponse …) ≤ clientCap` (UDP) / `≤ 65535` (TCP); and: nothing links the conclusion to the bytes actually sent | OS | Prog's socket instance maps `sendTo`/`tcpSend` to `.pure ()` (FreeIO.lean:49,54) — client-bound emissions are invisible to the model, so the "delivered" object in the conclusion is the internal `deliveredResponse` value, and the wire conjunct is a *pure* statement (`truncateUdp`/`unframeTcp∘frameTcp`/`decode∘encode` applied to `encode (deliveredResponse …)`), never an equation about the datagram passed to `sendTo` (the proof obtains `hrunSend` and discards it; the link `response = deliveredResponse query resp` from `replyForResolution_ok_fst` is used internally but not exported). When the response exceeds the cap, the actually-sent bytes are `(truncateUdp …).1` with TC=1 — covered only by standalone lemmas (`truncateUdp_truncated/_size`, Server.lean:53/91), not by any capstone conjunct. TCP is sharper: `serveTcpDatagram` (Impl/Server.lean:802) sends `frameTcp (encode response)` with **no size guard**, and `frameTcp` writes a mod-truncated 2-byte length for payloads > 65535 (Impl/TcpFraming, cf. `lenByte_hi` needing `n ≤ 65535`), i.e. corrupt framing exactly in the case the theorem's gate excludes. | Export `sent = truncateUdp (encode (deliveredResponse …)) … .1` (resp. `sent = frameTcp …`) as a conclusion conjunct — cheap, the proof already has it. Add the oversize arm (TC=1 shape claim; W3 lists the TC dual). For TCP, guard `frameTcp` at 65535 in the impl or prove the size bound unreachable. | **4** |
| 5 | all serve capstones (`hGlSbelt : GluelessProv sbelt`) | `GluelessProv sbelt` for the deployed SBELT | UR (unestablished, likely provable) | Instances exist for `default`, `fromNsWithGlueAll`, `markQueried`, `addAddress`, `removeServer` (IoResumeSound.lean:2244–2267) — but none for `DnsSList.mkSbelt`, which is what `main` uses (Main.lean:136). The premise every capstone consumes is never proven of the real root-hint SBELT. The root-server names in Main.lean:13 are hand-built canonical wire names, so the lemma should be `decide`-adjacent. | Add `GluelessProv_mkSbelt` (or a concrete `GluelessProv (mkSbelt rootServers)` pin) and cite it next to `main`. | 3 |
| 6 | `serveSeq_total` / `JustifiedTrace` | whole theorem vs the deployed loop | OS | No consumers of `serveSeq_total`/`serveSeq_sound` outside ServeSequence.lean. The deployed loops (`udpServeLoop`/`tcpServeLoop`, Main.lean:85–128; `serverLoop`, Impl/Server.lean:845) differ structurally from `serveSeq`: (a) periodic `DnsCache.sweep` every `sweepInterval` is absent from `serveSeq`; (b) UDP and TCP loops run concurrently sharing one `Std.Mutex` cache — interleaving is unmodeled and `JustifiedTrace` covers only UDP `afterRecv` datagrams (no TCP sibling of `serveSeq` exists at all); (c) conclusion `w'.clock = w.clock` — the Prog clock is frozen, so the whole trace is served at one instant and cross-datagram TTL expiry is out of model. | Add a TCP-inclusive trace combinator; include the sweep step (sweep preserves the pack — lemmas exist); document the frozen-clock scope; longer-term, a shim theorem tying `serveSeq` to `serverLoop`'s recursion. | 3 |
| 7 | `resolveThenReply_sound` (ServeSound.lean:108), and its supplier chain `replyForResolution_answer_sound`, `deliveredResponse_sectionAgrees` | `hrun : SatisfiesM (ShimSound T ∧ ∀ resp … CanonicalSection resp.answer) (resolveWithIO …)` | UR + orphaned | The combined SatisfiesM premise has **no producer**: `resolveWithIO_sound` (NameTree.lean:2010) yields only `ShimSound T`, and per the recorded lesson no generic `SatisfiesM.and` is provable, so nobody can discharge `hrun`. The theorem also has **no consumers** (grep: only ServeSound.lean). The whole ServeSound layer is a dead-end capstone superseded by `serveDatagram_verdict_sound`. | Either prove a combined `resolveWithIO` post (ShimSound ∧ canonicity — the canonicity half already exists on the ResolveWithIOSound path via `resolveWithIO_ok_sections`) and wire a consumer, or delete/demote the layer to avoid a soundness-looking theorem that is vacuous in practice. | 3 |
| 8 | `resolves_delivered_no_foreign` (DeliveredAuthentic.lean:26) | `_h : Resolves …` | **U** (confirmed textually — underscore-bound, never used) | The proof is exactly `scrubAnswer_no_foreign hr hforeign`; the `Resolves` premise decorates the statement so it reads like a delivery theorem. | Delete the premise (free strengthening) or delete the theorem and cite `scrubAnswer_no_foreign` directly; if kept, rename so it doesn't imply resolution is needed. | 2 |
| 9 | `serveDatagram_verdict_sound` (and TCP twin) — ok disjunct | conclusion equates only `rcode` and `answer` with the model verdict `v` | OS | `(αResp (deliveredResponse …)).rcode = v.rcode ∧ … .answer = scrubAnswer qm.qname v.answer` — the delivered **authority/additional** sections are never tied to `v.authority`/`v.additional`. Authority is separately constrained (owner-ancestor scrub, `deliveredResponse_authority_owned`) but has no model-agreement conjunct; a name-error's SOA delivery is uncovered at capstone level. | W3 candidate: add authority-section agreement (negative-answer SOA) to the verdict conjuncts. | 2 |
| 10 | `serveDatagram_verdict_sound`/`_total`, `serveTcpDatagram_*` (`hrd : qm.rd = false`) | model query has `rd = false` while the impl **requires** RD=1 | UR (cosmetic) | `queryProblem = none` forces `performsRequestedOperation q = (q.header.rd == 1)` (Impl/Server.lean:115–122), i.e. every served query has RD=1; `_total` then builds `qm` with `rd := false` (ResolveWithIOSound.lean:3939). Harmless because `Resolves` is rd-invariant (NetworkSemantics.lean:1787 rd-transport), but the mismatch is a trap for readers and future rd-sensitive model rules. | Set `qm.rd := true` (or prove/record the rd-irrelevance link next to the capstone). | 2 |
| 11 | `serveDatagram_verdict_sound` etc. (`hqu`) | `query.question[0]? = some qu` | D | Derivable from `hqp`: `question_head_of_queryProblem_none` (ServeSequence.lean:62). Kept to bind the witness `qu` in the statement. | Keep; optionally restate with `∃ qu` to drop one premise. | 1 |
| 12 | all serve capstones (`hclock`) | `w.clock.toNat + 604800 < 2^32` | LB | Realistic until ~Feb 2106 (UInt32 Unix seconds minus one week of TTL headroom); needed for expiry-arithmetic non-overflow. Preserved along traces because the Prog clock is frozen (see #6). | Keep; record the 2106 horizon. | 1 |
| 13 | all serve capstones (`hw : WorldModels …`, `hwTcp`, `hnetWF : net.WF`) | the network-oracle premises | LB (standing TCB interface) | These are the physical-world assumptions the plan routes to W2. Two properties worth recording: (a) the honest arm demands `truncateToCap (negotiatedUdp ednsBuf) qm ref = (ref, false)` and `resp.tc = ref.tc` (NetworkSim.lean:112,147) — an honest-but-truncated (TC=1) UDP reply can only inhabit the `SpoofReply` arm, i.e. gets zero honest guarantees (deliberate: TC → TCP retry, and the spoof arm was deliberately weakened at 1510da1 so the disjunction stays total); (b) the honest arm bundles parse-and-abstract totality plus NS-rdata canonicality for all sections (lines 82–92, 120–135) — the model-side canonical-wire assumption (see W0 seeds). | Keep; W2 should restate each conjunct as a checkable model obligation, and the diff rig should exercise the TC=1 honest case. | 2 (note) |

## Per-file triage (everything else)

| File | Verdict |
|---|---|
| `Server.lean` | All hypotheses are branch conditions or run-equations (LB). `truncateUdp_*`, `rawDatagramReply_*` (incl. the nice `rawDatagramReply_no_amplification`), acceptance/selection lemmas, LRU touch pins: clean. `serveOne_undecodable_no_reply` states the *bind* form rather than `serveOne` itself (recvFrom is unmodeled) — cosmetic. |
| `ServeSound.lean` | See finding #7 (orphaned layer). Internal `nameEqCI` lemmas LB. |
| `ServeSequence.lean` | Findings #1, #2, #6. `serveDatagram_unserved` is honest (queryProblem=some path sends an error reply, but sends are `.pure ()` so `= pure cache` holds). `ServePack_empty` is the only base-case producer of the pack. |
| `ServeTcp.lean` | Findings #4 (framing gate), and note: no TCP trace/sequence theorem exists; `serveTcpDatagram` error/undecodable paths have no `_unserved` sibling. Otherwise a faithful mirror of the UDP capstone. |
| `AnswerTerminal.lean` | Recurring premise `hvalid : ∀ b ∈ section, ∃ rr, parseRaw b = some rr ∧ αRR rr ≠ none` — LB, supplied by the WorldModels honest arm at consumers; also a W0 seed (below). `αResp_isReferral_false_of_finished` premises are exhaustive branch facts, LB. |
| `AnswerScrub.lean` | `scrubAnswerB_mem/_authentic` hypothesis-free beyond membership: **good**. `scrubAnswerB_excludes_foreign`'s `hforeign` is the contrapositive driver — LB and fair. Note (positive): scrubAnswerB silently *drops* unparseable answer bytes (filterMap), so the scrub family needs no canonicality premise for exclusion, only for exactness. |
| `AnswerScrubAlpha.lean` | `αSection_scrubAnswerB_eq` needs `CanonicalSection + AllAbstract + NameCorr(qname)` — LB; all discharged from `decode_ok_wire_facts` + WorldModels at the call sites in ResolveWithIOSound. W0 seeds. |
| `DeliveredAuthentic.lean` | Finding #8. `resolves_delivered_grounded_and_authentic`'s `Resolves` premise IS used (via `resolves_answer_authoritative`) — LB. |
| `DeliveredWire.lean` | The CanonicalRaw machinery already-in-embryo (see W0 section). All hypotheses are canonical-shape premises with real producers (`decode_ok_wire_facts` at ingress, `cacheRecCanon_*` preservation at every write, `_empty` at the base) — LB. `deliveredResponse_decode_encode`'s `hsz < 65536` discharged via `encode_size_answer_le` + `clientCap ≤ 1232` — LB. |
| `Message.lean`, `MessageValid.lean` | `decode_encode` premises (`counts`, `ValidQuestions`, `ValidRRBytes`) are exactly the canonical image; `decode_encode_of_decode` closes them for decoded inputs. All other hypotheses are parser-run equations. LB throughout. |
| `Cache.lean` | All branch-condition premises (`hnz`, `hnb`, `hkeep`, `hlive`, `hrank`, …) LB. RFC-conformance wrappers (`truncated_not_cached`, `accept_discard_unrequested`, `store_never_combined`) instantiate generated specs — fine. `storeChecked_no_downgrade` fair. No unrealistic premises found. |
| `Resolver.lean` | Dispatch/coverage/step lemmas; hypotheses are state-shape equations. LB. |
| `RData.lean`, `ResourceRecord.lean`, `TtlCap.lean` | Roundtrips conditioned on canonical shape (`ValidLabels`, `≤ 255`, `rdlength_prop_0`) — LB and precisely the W0 `CanonicalRaw` boundary (below). `capTtlRR_le` clean. |
| `DomainName.lean`, `QnameMin.lean`, `Primitives.lean`, `Parsec.lean`, `Header.lean`, `Question.lean`, `Absorb.lean`, `GlueConnector.lean` | Mechanical; hypotheses are validity/shape premises with producers (`run_decodeName_validLabels`, `CanonicalName`, WorldModels conjuncts for GlueConnector's `hnscanon`). LB. GlueConnector's `hnscanon` is only available on the **honest** arm — the spoofed-referral sub-case lacks it (already recorded as the NS-rdata trailing-bytes note). |
| `SentMinimised.lean` | `ioResumeLoop_sent_minimised` / `resolveWithIO_sent_minimised` are **hypothesis-free** program-tree capstones — the strongest statements in the slice. Mild note: `SentMinimisedWire` internally guards the claim on a canonicality antecedent (`fun hcanon => …`), so the minimisation property of a sent packet is conditional on the state name being canonical; a state-invariant discharge would make it unconditional. |
| `TcpFraming.lean` | `unframeTcp_frameTcp`'s `≤ 65535` LB (2-byte prefix); the impl-side missing guard is finding #4. |

## Canonical-raw assumptions (W0 seeds)

Everywhere the lenient internal decoder (`ResourceRecord.decode` / `RRParse.parseRaw`) is trusted,
the justifying fact is some phrasing of "this ByteArray is a `decodeRRCanonical` output". The
formal carriers already exist — W0's `CanonicalRaw` should unify them:

1. **`CanonicalRR` / `CanonicalSection`** (MessageValid.lean:300, DeliveredWire.lean:15) — the
   byte-level canonical-wire predicate; produced at ingress by `decode_ok_wire_facts`
   (DeliveredWire.lean:36) via `run_decodeRRCanonical_shape`. This *is* `CanonicalRaw b`.
2. **`RRWireCanon`** (DeliveredWire.lean:362) — the same predicate on parsed records;
   `rrWireCanon_of_parseRaw` / `canonicalRR_rrBytes` / `parseRaw_rrBytes` are the record↔bytes
   halves of the W0 inverse theorem, already proven.
3. **Cache-side threading** — `CacheRecCanon` / `CacheNegSoaCanon` (DeliveredWire.lean:465,468)
   with preservation at `storeChecked`/`cacheRRs`/`cacheUnlessTruncated`/`boundLru`/eviction and
   read-side `lookupAnswerable_rrWireCanon` / `lookupNegativeSoa_rrWireCanon`. This is the
   `CacheRawsCanonical` invariant W0 asks for, modulo naming. **Gap: the store premise
   `hraw : ∀ bytes …, parseRaw bytes = some rr → RRWireCanon rr`
   (`cacheRecCanon_cacheRRs`, DeliveredWire.lean:525) must be discharged at every write site;
   the one write site with no discharge anywhere is `primeRootHints` (finding #1).**
4. **Parse-and-abstract premises** — the `∀ b ∈ section, ∃ rr, parseRaw b = some rr ∧ αRR rr ≠ none`
   family (`AllParse`/`AllAbstract`, AnswerScrubAlpha.lean:73/16; `hvalid`/`hvalidAuth`/`hvalidAdd`
   throughout AnswerTerminal.lean and GlueConnector.lean; `hnscanon` NS-rdata canonicality,
   GlueConnector.lean:151). Producers: `decode_ok_wire_facts` (own messages) and the WorldModels
   honest-arm conjuncts (NetworkSim.lean:82–92,120–135) — i.e. for *peer* messages the canonical-wire
   fact is currently an **oracle assumption**, not a theorem; W0 can convert the answer/authority
   halves into theorems because the resolver only accepts `Message.decode`-ok replies (the decode
   already ran `decodeRRCanonical`). The spoofed arm intentionally lacks it (recorded).
5. **`CanonicalName`** (DeliveredWire.lean:111) for qnames: assumed as `hqn` in
   `resolveThenReply_sound` (undischarged there — finding #7), derived from
   `QuestionFromLabels`/`decode_ok_wire_facts` on the live path.
6. **Roundtrip-side conditions** — `ResourceRecord.decode_encode` / `TtlCap.parseRaw_encode`
   hypotheses (`ValidLabels`, wire-size ≤ 255, `rdlength_prop_0`): the "inverse on the canonical
   image" half of W0 in older clothes; restating them as `CanonicalRaw` corollaries removes the
   per-call-site side-condition juggling.
7. **Informal (no predicate at all)**: `Impl.Edns.lean:19`, `Impl/Server.lean:81,100,304`,
   `Impl/Cache.lean:605,613`, `Impl/Resolver.lean:205` run the lenient decoder on cache/section
   blobs relying on 1–4 upstream; these are the sites W0's `CanonicalRaw` flow-proof must reach.

## Counts

- Unused: **1** confirmed (`resolves_delivered_no_foreign`'s `_h`); 1 derivable-kept (`hqu`).
- Unrealistic / unestablished-at-entry: **4** (primed-cache invariant pack — top severity;
  qtype-ANY + class-IN gates incl. the trace-voiding `InScope`; `GluelessProv (mkSbelt …)`;
  ServeSound's undischargeable combined SatisfiesM premise).
- Over-scoped conclusions: **5** (trivially-satisfied error-arm verdict via `Resolves.gaveUp`;
  unobservable sends + fits-gated wire claims incl. the TCP >65535 framing hole;
  `serveSeq_total` unconnected to the deployed concurrent loop, frozen clock, no TCP trace;
  authority/additional not tied to the model verdict; `qm.rd = false` mismatch).
- Load-bearing and fair: everything else in the slice (~150 theorems), including the entire codec
  stack, the cache lemma family, the scrub family, and the hypothesis-free `SentMinimised`
  capstones. The oracle premises (`WorldModels`, `WorldModelsTcp`, `net.WF`) are fair as the
  standing TCB interface; their conjuncts are W2 obligations.
