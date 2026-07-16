# VeriDNS Execution-Path Map (upstream 26b5849, harness dc8c981)

Supersedes the 8e4e16d-era map. Upstream added DNS-over-TCP (client + upstream fallback),
EDNS0/OPT, QNAME minimisation, an egress filter, a rate limiter, a mutex-based concurrent
main loop, and a large new soundness/adequacy capstone stack
(IoResumeSound → ResolveWithIOSound → ServeSequence/ServeTcp, plus Adequacy/SpineAdequacy/Depth1Adequacy).

## 1. Runtime call graph (packet in → packet out)

### Entry / startup (`VeriDNS/Main.lean`)

`main` (`Main.lean:130`):
1. `mkUdpSocket`/`bindSocket` port 5300 (FFI opaques, `Impl/UdpSocket.lean:6-13`).
2. `resolvedRootServers` (`Main.lean:71`) — 5 hardcoded root IPs (`Main.lean:20`) or **env override `VERI_DNS_ROOT_HINT`** (test hook, unverified).
3. `DnsSList.mkSbelt` (`Impl/SList.lean:35`).
4. **`primeRootHints`** (`Main.lean:37`) — root NS priming: `withSecrets` → `forwardQuery` → `acceptResponse` → `cacheUnlessTruncated` over `bailiwickRaws root answer/additional`. Executes real cache writes at startup; **no theorem mentions `primeRootHints`**.
5. Cache into `Std.Mutex` (`Main.lean:141`); `tcpListen` + `IO.asTask tcpServeLoop` on a dedicated task (`Main.lean:144-145`); then `udpServeLoop`.

**The serving loops live in Main, not Impl.** `udpServeLoop` (`Main.lean:84`, `partial`) and `tcpServeLoop` (`Main.lean:104`, `partial`) each do: recv → `RateBucket.bump` (`Impl/Server.lean:177`, 200 q/window per IP) → mutex **snapshot** → `serveDatagram`/`serveTcpDatagram` → mutex **`(·).absorb served`** (`Impl/Cache.lean:197`) → `DnsCache.sweep` every 64 datagrams. Consequence: `Impl/Server.lean`'s `serverLoop` (:846), `serveOne` (:826), `serveOneLimited` (:839), `afterRecv` (:831) are **runtime-dead** — they survive only as proof subjects (ServeSequence proves about `afterRecv` folds) and test harness entry points (`Test/Loop.lean`). The executed loops (mutex snapshot/absorb, two concurrent threads) have **no theorem**; only the `absorb` merge itself does (Proof/Absorb).

### UDP request path — `serveDatagram` (`Impl/Server.lean:779`)

1. `permitted acl clientAddr` (`Server.lean:156`; `defaultAcl` :159 = loopback+RFC1918) — silent drop.
2. `Message.decode` (`Impl/Message.lean:70`; `Header.decode`, `Question.decode` via `DomainName.decodeName`, `decodeRRCanonical` `Message.lean:12` — decompress + re-serialize each RR to canonical wire bytes). Undecodable → `rawDatagramReply` (`Server.lean:124`): FORMERR iff header decodes with qr=0/opcode=query, else silent drop.
3. `query.header.qr == 1` → drop. `queryProblem` (`Server.lean:118`): qdcount≠1 → FORMERR, opcode≠query → NOTIMPL, rd=0 → REFUSED (this resolver *requires* RD from clients).
4. `UdpSocket.now` → **`resolveWithIO`** (`Server.lean:713`) — see below.
5. **`replyForResolution`** (`Server.lean:755`): on error → SERVFAIL; on ok → `deliveredResponse` (`Server.lean:742`) = **`scrubAnswerB`** (`Impl/AnswerScrub.lean:35`, CNAME-reachability answer scrub) + `scrubAuthorityB` (`Server.lean:98`, ancestor-only authority) + `finalizeForClient`; then positive caching (`ownerRaws`+`credAnswer`) and `storeNegativeIfCacheable` (`Server.lean:724`, SOA negTtl capped at 10800 :73-76).
6. `truncateUdp (Message.encode response) response (Edns.clientCap query)` (`Server.lean:317`; `Edns.clientCap` `Impl/Edns.lean:47` = 512 or min(client OPT size, 1232)) — staged: drop additional → TC+drop authority → TC+drop answer.
7. `sendTo` (FFI) → `cache''.boundLru (serveTouches …)` (LRU bound keyed by demand).

### TCP request path — `tcpServeLoop` → `serveTcpDatagram` (`Impl/Server.lean:802`)

`tcpAccept` (FFI `recvfrom.c:433`) → `tcpRecvMsg` (FFI `recvfrom.c:460` — **the 2-byte length unframing of inbound queries happens in C**, not Lean) → same pipeline as UDP except: replies are `TcpFraming.frameTcp` (`Impl/TcpFraming.lean:11`) → `UdpSocket.tcpSend` (FFI), and **no truncation stage** (full response, no `truncateUdp`). `tcpClose` in `finally`. Lean's `unframeTcp` (`TcpFraming.lean:14`) **never executes at runtime**.

### The resolver core — `resolveWithIO` (`Server.lean:713`, fuel=40 depth=6 budget=5s)

`Resolver.resolve` (`Impl/Resolver.lean:512`) — pure fueled loop over `Resolver.step` (:445):
- `stepCheckLocal` (:270) → `localAnswer` (:244): `NegativeCacheSpec.retrieveNegative`, `TrustworthinessSpec.answers`, cached-CNAME chase with `cnameChaseVisited` loop guard (:241), fuel 8.
- `stepFindServers` (:295) → `walkNs` (:334) via `DnsCache.lookupTopCred` (`Impl/Cache.lean:152`) + `DomainName.parentDomainWire`; SLIST via `SlistFromNameSpec.setUpAddresses` = `DnsSList.fromNsWithGlueAll` (`SList.lean:48,57`); falls back to SBELT.
- `stepSendQueries` (:351) → pauses (`needsIO`).
- `stepAnalyzeResponse` (:363): `cnameToChase` (:77), referral handling — `referralCutRaw` (:148), **`bailiwickRaws`** (:102, anti-poison filter, with its two inline theorems :108,:115), `extractGlueRecords` (:202), `delegationMatchCount` (:156) — and `cacheUnlessTruncated` (:197) → `cacheRRs` over `RRParse.normalizeSection` (RFC 2181 RRset-TTL normalisation) → `DnsCache.storeChecked` (`Cache.lean:76`, credibility no-downgrade).

On pause → **`ioResumeLoop`** (`Server.lean:566`) — now **total** (`termination_by (depth, fuel)` :710, no longer `partial`). Per round:
- deadline check against `budget`.
- `bestWithAddress` (`SList.lean:76`) none → **glueless branch**: nested `Resolver.resolve (mkAddressQuery nsName)` + recursive `ioResumeLoop` at `depth-1`; `gluelessUpdatedSlist` (:511), `gluelessRecheck` (:527), `extractAAddress` (:302).
- **query branch**: `Resolver.buildSubQuery state revealed` (`Resolver.lean:468`) — **QNAME minimisation**: `subQuestion` (:457) sends `DomainName.minimisedName sname revealed` (`Impl/DomainName.lean:134`) with qtype=A while `probeRoundB` (:454); sub-query is rd=0, arcount=1 with **EDNS0 OPT** `Edns.optRRBytes 1232` (`Edns.lean:36,14`). Then `withSecrets` (`Server.lean:41`) = random ID + **0x20 case randomization** (`DomainName.randomizeCase` :126).
- **egress filter**: `blockedEgress ipAddr` (`Server.lean:354`; `doNotQueryNets` :336 = 0/8, 127/8, RFC1918, CGN, link-local, 240/4; bypass via `@[init]`-env global `egressBypassEnabled` :352 / `VERI_DNS_ALLOW_LOOPBACK_EGRESS`) → skip send, treated as timeout.
- **`forwardQuery`** (`Server.lean:377`): `Message.encode` → `UdpSocket.exchange` = **single-shot `exchangeRaw` FFI** (the old `retryOption` retransmit wrapper is gone from the IO instance, `UdpSocket.lean:49-61`) → `acceptExchanged`/`datagramMatches` (:366-372, RFC 5452 source+destination address/port check over the FFI 4-tuple) → decode → `sanitizeTtlsCap` (:278) = `capTtls ∘ Edns.stripOpt` (TTL cap 604800, negative-bit→0; OPT stripped).
- `markQueried`; `acceptResponse` (:51, id + question triple match, case-sensitive qname == so 0x20 is load-bearing).
- **TC=1 → TCP fallback**: `tcpForward` (`Server.lean:389`) → `tcpExchangeRaw` FFI (`recvfrom.c:323` — framing AND unframing in C) → `acceptResponse` again; still-TC or fail → drop server, retry loop.
- `unfollowableDelegationB` (:214) = `bogusDelegationB` (not closer than SLIST, :198) ∪ `delegationShaped ∧ ¬respInBailiwick` (:201) → ignore response.
- probe-round handling: `probeRoundB ∧ strictDenialB` (:235) → **RFC 8020 subtree denial** — return NXDOMAIN + `storeProbeNegative` (:240); `probeRoundB ∧ ¬probePassableB` (:232) → `bumpRevealed` (`Resolver.lean:465`, reveal one more label, cap `maxMinimiseSteps`=10).
- else `afterResume` (:500): `dropIfBizarre` (:408, SERVFAIL/unclassifiable → remove server) → `Resolver.resume` (:525) → `boundStateCache`/`roundTouches` (:482-498, LRU cache bounding after every round).

### Runtime-dead Impl code (do not spend review effort proving things about these)

`Impl/NameTree.lean` (`treeLookup`/`treeResolve` — proof ORACLE only + `Test/Loop.lean`), `DnsCache.lookup` (`Cache.lean:118`), `sanitizeTtls` (`Server.lean:256`, superseded by `sanitizeTtlsCap`), `DnsSList.bestServer` (:20) and `fromNsWithGlue` (:40), `TcpFraming.unframeTcp`, `mkUpstreamSocket` extern (`UdpSocket.lean:10`), `RData.decodeA`/`decodeCname` (only `decodeSoa` runs, via `extractSoaNegative` `Server.lean:78`), and — new this round — `serverLoop`/`serveOne`/`serveOneLimited`/`afterRecv` (Main bypasses them; `afterRecv` is the *model* of what `udpServeLoop` inlines, minus mutex/absorb/sweep).

## 2. Classification of every Proof/ file

Proof spine (imports): `IoResumeSound` → {`IoResumeErrorSound`, `Absorb`, `SentMinimised`, `ResolveWithIOSound`} → {`ServeSequence`, `ServeTcp`} → `ServeAdequacy`. Adequacy spine: `Adequacy` → `CooperativeNetwork` → {`Depth1Adequacy`, `SpineAdequacy`} → `ServeAdequacy`. All of these state facts about `Prog.run` of the **exact executed constants** at `M = Prog` (free monad, `FreeIO.lean:7-72`, `World` now carries `oracle`, `tcpOracle`, `ids`, `idCtr`, `clock`).

| Proof file | Class | Justification |
|---|---|---|
| `Absorb.lean` | **ON-PATH subject / TERMINAL capstone** | `DnsCache.absorb` runs on every mutex merge in `Main.lean:94,119`. `absorb_serve_invariants` (:239) proves all 10 serve invariants survive the merge — but is **never applied** (its would-be consumer, `udpServeLoop`, is unverified). The only theorem touching the concurrency story. |
| `Adequacy.lean` | **ON-PATH (Prog)** | `resolveWithIO_terminates` (:268 — every world, fuel-bounded termination of the executed `ioResumeLoop`), `resolveWithIO_delivers` (:376), `resolveWithIO_adequate_of_descent` (:545). Consumed by CooperativeNetwork. |
| `AnswerScrub.lean` | **ON-PATH** | `scrubAnswerB_mem`/`_authentic`/`_excludes_foreign` (:64,:87,:97) — the scrub executes on every ok client reply. |
| `AnswerScrubAlpha.lean` | **MIXED** | The α-bridge `αSection_scrubAnswerB_eq` (:369) is consumed (`ResolveWithIOSound.lean:1163`). But `scrubAnswerB_delivered_model_authentic` (:419) is a **TERMINAL ORPHAN** — never applied. |
| `AnswerTerminal.lean` | **MIXED support** | Impl-predicate/α agreement lemmas feeding IoResumeSound (e.g. `cnamePred_agree` :510, canonicality of parsed rdata :655-763). |
| `BitPacking.lean` | **ON-PATH** | Header codec, every packet. |
| `Cache.lean` | **MIXED, mostly ON-PATH** | `storeChecked_no_downgrade` (:378), `lookupAnswerable_excludes_floor` (:329), `lookupNegativeSoa_serves_authority` (:322) — all executed ops. Exception: `lookup_caseInsensitive` (:409) is about dead `DnsCache.lookup`. |
| `CooperativeNetwork.lean` | **ON-PATH (Prog) support** | 3.8k lines of `DescentChain`/`DescentCacheInv` machinery: the executed `ioResumeLoop` descends and delivers under a cooperative `respond` world. Feeds Depth1/Spine adequacy. |
| `DeliveredAuthentic.lean` | **OFF-PATH — TERMINAL ORPHANS** | Both theorems (`resolves_delivered_grounded_and_authentic` :9, `resolves_delivered_no_foreign` :26) are about the model `Net.Resolves` and are **never applied**. Deadweight. |
| `DeliveredWire.lean` | **ON-PATH support** | Cache/section canonicality invariants (`CacheRecCanon`, `CacheNegSoaCanon`) + `capTtls_frame` (:678); consumed throughout the sound spine. |
| `Depth1Adequacy.lean` | **ON-PATH (Prog)** | `resolveWithIO_depth1_adequate` (:155): concrete root-referral→child-answer 2-server world, executed loop delivers. Consumed by ServeAdequacy. |
| `DomainName.lean` | **ON-PATH** | Name codec round-trips; every parse/compare. |
| `Enum.lean` | **ON-PATH** | Header enum codec. |
| `FreeIO.lean` | **MIXED infra** | `Prog`/`World`/`Prog.run` are proof-only, but every lemma's subject (`ioResumeLoop`, `forwardQuery`, `tcpForward` at `Prog`) is the executed definition. `World.tcpOracle` (:57) models the TCP fallback. |
| `GlueConnector.lean` | **ON-PATH support** | Executed `extractGlueRecords`/`bailiwickRaws`/`fromNsWithGlueAll` vs model referral SLIST (`referral_slist_eq` :151). |
| `Header.lean` | **ON-PATH** | Header round-trip. |
| `IoResumeErrorSound.lean` | **ON-PATH (Prog)** | `ioResumeLoop_error_sound` (:706): the `.error` arm (SERVFAIL) still yields a model verdict + cache invariants. Consumed at `ResolveWithIOSound.lean:3502`. |
| `IoResumeSound.lean` | **ON-PATH (Prog) — the workhorse** | `ioResumeLoop_sound` (:3468, 11k-line file): `Prog.run` of the executed loop returning `.ok resp` implies `HasVerdictAt` in the RFC network model, answer = cnameChain ++ verdict answer, `CacheRefines`, and all 10 cache invariants preserved. **Old finding 025 is RESOLVED**: no longer an orphan — consumed at `ResolveWithIOSound.lean:181` and `IoResumeErrorSound.lean:908`. Hypotheses (~28) include `q.rd = false` (sub-query rd, fine), `q.qtype ≠ star`, class IN, `now+604800 < 2^32`, canonical sname, `GluelessProv` slist/sbelt. |
| `Message.lean` | **ON-PATH** | `decode_encode` round-trip, every datagram. |
| `MessageValid.lean` | **ON-PATH** | Decoder-output canonicality that the whole sound spine leans on. |
| `NameTree.lean` | **MIXED** | `treeLookup_*` about the never-executed oracle. But `ioResumeLoop_sound` (:1822) / `resolveWithIO_sound` (:2010) are **SatisfiesM over any lawful M — hold at M=IO directly** for the executed `resolveWithIO`, under `NetworkConsistent` + new **`NetworkConsistentTcp`** oracles (so the TCP fallback is inside the oracle boundary too). |
| `NameTreeComplete.lean` | **MIXED** | `resolveWithIO_complete` (:3483): completeness for any M relative to `TreeSane`+consistency; plus off-path `treeResolve` congruences. |
| `NetworkSim.lean` | **MIXED support** | `WorldModels` (:95) / **`WorldModelsTcp`** (:151) — the honest-world oracles — and `StateModels` preservation lemmas joining executed state to model state. |
| `Parsec.lean`, `Primitives.lean` | **ON-PATH** | Codec primitive round-trips. |
| `QnameMin.lean` | **ON-PATH support** | `labelCount_minimisedName` (:91), `minimisedName_full` (:98), `isAncestorB_minimisedName` (:109), `αName_minimisedName` (:142) — `minimisedName` executes in every probe-round sub-query. Feeds IoResumeSound + SentMinimised. |
| `Question.lean` | **ON-PATH** | Question codec. |
| `RData.lean` | **MIXED** | `decodeSoa` executes (negative caching); `decodeA`/`decodeCname` theorems are about dead code. |
| `Refinement.lean` | **MIXED — infra ON-PATH, capstone ORPHANED** | The α-abstraction stack (`αCache`, `αResp`, `HasVerdict` :2759, `HasVerdictAt` :2769) is consumed everywhere. But the old capstone `resolveWithIO_simulates` (:8863) — whose network disjunct takes `HasVerdict` as a *premise* — is now a **TERMINAL ORPHAN**, superseded by IoResumeSound→ResolveWithIOSound which discharges that arm constructively from `WorldModels`. |
| `Resolver.lean` | **ON-PATH** | Fuel-sufficiency: `resolve_ne_maxIterations` (:950) — the inner 64-step loop never dies of fuel. |
| `ResolveWithIOSound.lean` | **ON-PATH (Prog) capstone assembly** | `resolveWithIO_error_sound` (:3449), **`serveDatagram_verdict_sound`** (:3553 — full per-datagram pipeline: any run of executed `serveDatagram` embeds a `resolveWithIO` run whose ok-result has a model verdict, error-result is justified SERVFAIL), **`serveDatagram_total`** (:3826 — same with the qm/t existentials derived rather than assumed). |
| `ResourceRecord.lean` | **ON-PATH** | RR codec. |
| `RRsetComplete.lean` | **ON-PATH** | `cacheRRsNorm_complete` (:70) — `normalizeSection` caching in `cacheUnlessTruncated` keeps every survivor. |
| `SentMinimised.lean` | **ON-PATH (Prog) capstone — QNAME-min/privacy** | `AllSent` (:16) quantifies over **every `.exchange` and `.tcpExchange`** the executed program emits. `resolveWithIO_sent_minimised` (:400): every byte sent upstream is an encoded secret-randomized sub-query whose question is an ancestor of sname; on probe rounds qtype=A and exactly `revealed` labels leak. Terminal by design (capstone). **Two caveats**: `SentMinimisedWire` is conditional on `CanonicalName sname` (vacuous per-send otherwise), and `SentShape` **ignores the destination address** — nothing constrains *where* bytes go. |
| `ServeAdequacy.lean` | **ON-PATH (Prog) capstone** | `serveDatagram_delivers_of_resolve` (:47), `serveTcpDatagram_delivers_of_resolve` (:67), **`serveDatagram_depth1_adequate`** (:88): client datagram in → served datagram out through a concrete 2-server world. Terminal by design. |
| `ServeSequence.lean` | **ON-PATH (Prog) capstone — UDP** | `serveSeq_sound` (:215) / `serveSeq_total` (:333): a whole *list* of client datagrams folded through the executed `afterRecv` yields a `JustifiedTrace` — every served in-scope query gets a `ServeJustification` (verdict-or-SERVFAIL + truncation semantics under `Edns.clientCap`) and `ServePack` invariants persist. NOTE: `serveSeq` models `serverLoop`-minus-sweep, i.e. the *sequential* loop, not Main's mutex loop. |
| `ServeSound.lean` | **ON-PATH (any lawful M)** | `resolveThenReply_sound` (:108): `resolveWithIO` + `replyForResolution` delivers sections agreeing with the tree oracle. Complements the Prog-side verdict theorems at M=IO. |
| `ServeTcp.lean` | **ON-PATH (Prog) capstone — TCP** | `serveTcpDatagram_served` (:11, pipeline shape), `serveTcpDatagram_verdict_sound` (:34), `serveTcpDatagram_total` (:272). Uses `unframeTcp_frameTcp` (:252) to show the framed reply is client-recoverable when the payload fits 65535. `serveTcpDatagram_total` is terminal (capstone). |
| `Server.lean` | **MIXED, mostly ON-PATH** | `truncateUdp_*` (:36-:122, now cap-generic so EDNS sizes are covered), `acceptResponse_matches` (:219), `exchanged_matches` (:238), `accept_match_obligation` (:262), hygiene rcodes (:292-:322), `rawDatagramReply_no_amplification` (:584), `afterRecv_ratelimited` (:725), `slist_prevent_selection` (:425). Exception: **`sanitize_limit_ttls` (:460) is still about dead `sanitizeTtls`** — the live guarantee is `TtlCap.sanitizeTtlsCap_limit_ttls`. |
| `SpineAdequacy.lean` | **ON-PATH (Prog) capstones** | `resolveWithIO_spine_adequate` (:1658, n-hop delegation spine), `resolveWithIO_within_bound` (:1710, fuel bound `spineFuelBound`), `resolveWithIO_spine_no_starvation` (:1758). Terminal by design. |
| `TcpFraming.lean` | **ON-PATH (send side only)** | `unframeTcp_frameTcp` (:38) + size/byte lemmas. Only `frameTcp` executes; runtime unframing is C. |
| `Test.lean` | **OFF-PATH** | Reference parser, decorative. |
| `TtlCap.lean` | **ON-PATH** | `sanitizeTtlsCap_limit_ttls` (:99) — runs on every accepted upstream response (UDP and TCP). |
| `WorldNetwork.lean` | **Support (model)** | Constructs realizable model networks (`nodata_model_realizable` :393 etc.) to discharge oracle premises. Not decorative — it is the vacuity guard for `Network`-parametric theorems. |

### Terminal-orphan scoreboard

- **RESOLVED**: `IoResumeSound.ioResumeLoop_sound` (old finding 025) — now consumed by `ResolveWithIOSound.lean:181` and `IoResumeErrorSound.lean:908`.
- **New orphans** (proven, never applied, not obviously capstones):
  - `Refinement.resolveWithIO_simulates` (`Refinement.lean:8863`) — superseded legacy capstone; its assumption-shaped network arm is exactly what the new spine proves. ~Dead weight now.
  - `AnswerScrubAlpha.scrubAnswerB_delivered_model_authentic` (`AnswerScrubAlpha.lean:419`).
  - Both theorems in `DeliveredAuthentic.lean` (:9, :26).
  - `Absorb.absorb_serve_invariants` (`Absorb.lean:239`) — orphaned *because its consumer (Main's mutex loop) is outside the verified boundary*; treat as a capstone with a missing bridge, and check its hypotheses actually hold at the call site (the mutex-held `base` cache's invariants are never re-established anywhere).
- **Capstones (terminal by design, fine)**: `serveSeq_total`, `serveTcpDatagram_total`, `serveDatagram_depth1_adequate`, `resolveWithIO_sent_minimised`, `resolveWithIO_within_bound`, `resolveWithIO_spine_no_starvation`, `resolveWithIO_adequate_of_descent`.

## 3. Trust boundary / unverified glue

- **FFI C, `ffi/recvfrom.c` (512 lines, unverified)**:
  - `veri_dns_recvfrom` (:78) — **EAGAIN timeout returns empty ByteArray, not an error** (:90-98).
  - `veri_dns_random_u16` (:130) — getrandom/urandom; **all RFC 5452 ID + 0x20 entropy rests here**.
  - `veri_dns_exchange` (:189) — fresh unconnected socket per query (ephemeral source port = the port-randomization story, implicit, kernel-provided), connect→getsockname→dissolve trick, 2s recvmsg loop that **already discards wrong-source datagrams in C** (:277) before Lean's `datagramMatches` re-check; builds the `(payload,src,dst,local)` tuple. **`src6` is constructed with `nominalPort`, not the actual sender port** (:305) — the source-port half of the verified match is therefore synthesized by trusted C, and honored only because C's own :277 filter checked `sin_port`.
  - `veri_dns_tcp_exchange` (:323) — upstream TCP: **framing and unframing both in C**; no Lean theorem applies to this parsing.
  - `veri_dns_tcp_listen/accept/recv_msg/send/close` (:411-:512) — inbound TCP unframing in C (:460); 3s socket timeouts.
  - `veri_dns_upstream_port` (:168) — **env `VERI_DNS_UPSTREAM_PORT` rewrites every upstream destination port** (test hook inside the TCB).
- **`@[extern]`/`opaque`**: 13 in `Impl/UdpSocket.lean:6-47`; `mkUpstreamSocket` (:10) is a dead extern. The `UdpSocket IO` instance (:49) is unverified glue; note `exchange` is now **single-shot** (the old `retryOption` retransmit and its informal determinism argument are gone entirely).
- **`partial` defs with no theorem**: `Main.udpServeLoop` (:84), `Main.tcpServeLoop` (:104) — the *actual* serve loops, including `Std.Mutex` snapshot/absorb concurrency and the sweep cadence; `Impl.Server.serverLoop` (:846, dead anyway). `primeRootHints` (`Main.lean:37`) is a straight-line unverified cache-seeding path (a hostile "root" reachable at startup writes into the cache through `bailiwickRaws root` — root bailiwick is *everything*, so only `acceptResponse` + source-match guard it).
- **Modelling gaps**:
  1. **Prog ≈ IO**: the entire verdict/adequacy stack is at `M = Prog` with `WorldModels`/`WorldModelsTcp` honest-oracle hypotheses; transfer to the real network is trust, softened by the SatisfiesM theorems (`NameTree.resolveWithIO_sound`/`_complete`) which do hold at IO but under `NetworkConsistent`/`NetworkConsistentTcp` oracles.
  2. **Concurrency**: all sequence-level proofs (`serveSeq`) thread the cache sequentially; the real system is two threads racing on snapshot+absorb. Lost-update behavior (both threads absorb into a base that has moved) has no theorem; only per-merge invariant preservation is proven (and unapplied).
  3. **Rate limiter drift**: proofs cover `afterRecv`'s bump semantics; Main resets `rb` only at sweep boundaries and the TCP loop swallows exceptions around bump — unmodelled.
  4. **`@[init] egressBypassEnabled`** (`Server.lean:352`): an env-dependent global constant folded into `blockedEgress`; proofs never unfold it (they hypothesize `blockedEgress ip = false`).
- **No `axiom`, no `sorry`, no `unsafe`** anywhere (grep-verified this session). Residual TCB: Lean kernel/compiler, batteries, the C above, and hardcoded root IPs (`Main.lean:20`).

## 4. New-surface coverage: theorem vs merely implemented

| New surface | Covered by theorem? | Gap / hunting ground |
|---|---|---|
| **TCP framing — server reply** | YES: `frameTcp` correctness via `unframeTcp_frameTcp` (`Proof/TcpFraming.lean:38`) applied in `serveTcpDatagram_total` (`ServeTcp.lean:252`) under a ≤65535 size hypothesis. | What discharges the ≤65535 hypothesis for real responses? If a response encodes >65535 bytes, `frameTcp`'s 2-byte length silently truncates mod 2^16 (`lenPrefix` does `n/256, n%256` with `toUInt8` wrap) — check whether any bound on encoded response size is actually proven on the TCP path (UDP has `truncateUdp_size`; TCP has **no truncation stage**). |
| **TCP framing — inbound queries & upstream responses** | **NO Lean theorem can apply**: unframing lives in C (`recvfrom.c:460`, `:374-399`). Lean's `unframeTcp` is dead code — the round-trip theorem verifies a function that never runs. | Malformed-length handling, short reads, trailing bytes after the frame, connection reuse — all pure-C behavior. |
| **TCP fallback (`tcpForward` on TC=1)** | YES, inside the sound spine: `WorldModelsTcp` (`NetworkSim.lean:151`), `World.tcpOracle`, `NetworkConsistentTcp` (NameTree), `tcpSpoofReply_of_honest` (`IoResumeSound.lean:3440`); `SentMinimised` covers `.tcpExchange` sends too. | TCP responses have **no source/destination `datagramMatches` check in Lean** (`tcpForward` `Server.lean:389` goes straight decode→sanitize) — the anti-spoof story for TCP is "C connected the socket", trust not theorem. |
| **EDNS0 / OPT** | Mostly YES: `clientCap_le` (`Impl/Edns.lean:52`), cap-generic `truncateUdp_no_trunc_cap`/`truncateUdp_size` (`Proof/Server.lean:41,91`) consumed in ServeSequence's justification; OPT-on-subquery flows through `ioResumeLoop_sound`; upstream OPT stripped and TTL-capped via `sanitizeTtlsCap_limit_ttls` (`TtlCap.lean:99`) + `capTtls_frame` (`DeliveredWire.lean:678`) + `stripOpt_*` simp set (`Impl/Edns.lean:62-99`). | RFC 6891 conformance gaps, all unproven and mostly unimplemented: server **never emits an OPT in replies** (clients that sent OPT get an OPT-less reply); multiple client OPT RRs should be FORMERR — `findOptSize` (`Edns.lean:39`) just takes the first; OPT with extended-rcode/version>0 ignored; `clientCap` trusts the advertised size only down/up-clamped — none of this has a spec-side statement. |
| **QNAME minimisation** | Richest coverage of the new surface: send-side privacy capstone `resolveWithIO_sent_minimised` (`SentMinimised.lean:400`, UDP+TCP), `QnameMin.lean` name lemmas, probe semantics (RFC 8020 strict-denial + probe-consume) inside `ioResumeLoop_sound` and `Adequacy.Delivers_probeConsume_step` (:335). | (a) `SentMinimisedWire` is **conditional on `CanonicalName sname`** — a non-canonical sname (can it arise? decoder canonicalises, but CNAME targets come from rdata) makes the per-send claim vacuous; (b) minimisation-bypass correctness (`bumpRevealed` jumping to full labelCount after `maxMinimiseSteps`=10) is adequacy-relevant but the *privacy loss* of the jump is by design unbounded; (c) `storeProbeNegative` caches an NXDOMAIN for the **minimised** probe name under the sub-query's qname — poisoning surface analysed only inside IoResumeSound's referral cases. |
| **Egress filter (`doNotQueryNets`/`blockedEgress`)** | **Implemented, essentially UNVERIFIED.** `doNotQueryNets` has **zero mentions in Proof/**. `blockedEgress` appears only as `= false` *hypotheses* in adequacy (e.g. `SpineAdequacy.lean:1620`) and case splits in soundness. | There is **no theorem "the resolver never sends to a blocked address"** — and `SentShape` deliberately ignores the address, so the existing AllSent machinery would carry it cheaply. Also unproven: the filter runs *before* `forwardQuery` but the **glueless sub-resolve and TCP fallback paths** reuse the same `addr`; and `AclEntry.matches`/`clientIp` bit-arithmetic (`Server.lean:144-154`) has no correctness lemma. Prime hunting ground. |
| **Rate limiting + ACL** | Partial: `afterRecv_ratelimited` (`Proof/Server.lean:725`), `serveDatagram_denied` (:605), ServeSequence takes `InScope` as hypothesis. | `RateBucket.bump`'s `set!`/capacity-full behavior (returns `some rb` unchanged at 65536 IPs = **fail-open**, `Server.lean:184`) unproven; Main's reset cadence unmodelled. |
| **Mutex/absorb concurrency (Main)** | Only `Absorb.lean` (merge preserves invariants; bounded size) — and it is unapplied. | No interleaving/linearizability statement; snapshot-based serving means concurrent queries can each resolve from stale caches and absorb conflicting RRsets — check `absorb`'s conflict policy (`Cache.lean:197-278`) against the no-downgrade theorem. |

Also note two **query-shape holes** shared by all verdict/total capstones: `hqany : qu.qtype ≠ 255` (ANY queries are *served* by the real code path — `queryProblem` doesn't reject them — but every soundness statement excludes them) and `αClass = IN` (CH/HS queries likewise served but unverified).

## 5. Prioritize reading these (the assurance actually rests here)

1. **`Proof/IoResumeSound.lean:3468` `ioResumeLoop_sound`** — the single load-bearing theorem; audit its ~28 hypotheses for dischargeability at the `serveDatagram` call site (they *are* discharged in ResolveWithIOSound — verify no hypothesis is smuggled back in as an unprovable side condition).
2. **`Proof/ResolveWithIOSound.lean:3553/:3826` `serveDatagram_verdict_sound` / `serveDatagram_total`** — the per-datagram UDP pipeline capstone; check the SERVFAIL arm's `HasVerdictAt` is meaningful (not vacuous over empty slist).
3. **`Proof/ServeSequence.lean:215/:333` `serveSeq_sound` / `serveSeq_total`** — outermost proven statement; measure the distance to `Main.udpServeLoop` (sweep, mutex, absorb, rb reset are all outside it).
4. **`Proof/ServeTcp.lean:34/:272`** — TCP capstones; probe the 65535 framing hypothesis and the absent TCP source check.
5. **`Proof/NameTree.lean:2010` `resolveWithIO_sound`** (+ `NameTreeComplete.lean:3483` `resolveWithIO_complete`) — the only statements that hold at `M = IO` verbatim; the oracle definitions `NetworkConsistent`/`NetworkConsistentTcp` are where reality is assumed.
6. **`Proof/SentMinimised.lean:400` `resolveWithIO_sent_minimised`** — privacy capstone; probe the `CanonicalName` conditionality and the address-blindness of `SentShape`.
7. **`Proof/ServeAdequacy.lean:88` + `Proof/SpineAdequacy.lean:1658/:1710`** — liveness: does it answer at all, in bounded fuel; hypotheses lists here are enormous — vacuity-check against `Depth1Adequacy.twoServerRespond_*` instantiations.
8. **`Proof/AnswerScrub.lean:87,:97` + `Proof/Server.lean:219,:238,:262`** — the two anti-poison gates every reply passes (scrub; RFC 5452 accept/match over the FFI tuple — recall the tuple's src port is C-synthesized).
9. **`Proof/Cache.lean:378,:329` + `Proof/TtlCap.lean:99` + `Proof/RRsetComplete.lean:70`** — credibility ranking, TTL cap, RRset-normalized caching (all executed every round).
10. **`Proof/Absorb.lean:239` `absorb_serve_invariants`** — the unapplied concurrency theorem; verify its hypotheses would actually hold for the mutex-held base cache in `Main.lean:94`.

## Summary

- The verification is now **two-tiered and largely on-path**: (i) SatisfiesM theorems at any lawful M (hold at IO under network-consistency oracles), (ii) a deep `Prog`-level spine — IoResumeSound → ResolveWithIOSound → ServeSequence/ServeTcp/ServeAdequacy — about the *exact executed* `serveDatagram`/`serveTcpDatagram`/`ioResumeLoop`, with constructive world models. `ioResumeLoop` is now total (no `partial`), and old orphan finding 025 is resolved.
- **The verified boundary stops at `serveDatagram`**: Main's mutex loops, `primeRootHints`, sweep/rate-limiter cadence, and the absorb-merge *usage* are unverified; `serverLoop`/`serveOne` theorems describe runtime-dead stand-ins.
- **New-surface coverage is uneven**: QNAME minimisation (rich), EDNS0 (good mechanically, RFC-6891 gaps), TCP (send-side proven, receive-side and anti-spoof are C trust), **egress filter (no positive theorem at all — richest hunting ground)**, concurrency (one unapplied theorem).
- **Known orphans/deadweight**: `Refinement.resolveWithIO_simulates`, `AnswerScrubAlpha.scrubAnswerB_delivered_model_authentic`, `DeliveredAuthentic.lean` (both), `Proof/Server.lean:460 sanitize_limit_ttls` (dead subject), `Proof/Test.lean`, dead-`DnsCache.lookup` lemmas.
- **Systematic exclusions to probe for silent unsoundness**: qtype=ANY and non-IN classes are served but outside every capstone; `CanonicalName` side conditions on CNAME-derived snames; the C-synthesized source-port in the 5452 tuple; TCP responses bypassing `datagramMatches`.
