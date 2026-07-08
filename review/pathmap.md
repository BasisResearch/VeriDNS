# VeriDNS Execution-Path Map

## 1. Runtime call graph (UDP packet in → packet out)

**Entry**: `main` (`VeriDNS/Main.lean:20`) → `mkUdpSocket`/`bindSocket` (FFI opaques, `Impl/UdpSocket.lean:6-13`) → `DnsSList.mkSbelt` over 5 hardcoded root-server IPs (`Main.lean:12-18`, `Impl/SList.lean:35`) → `serverLoop` (`Impl/Server.lean:508`, **`partial`**, unverified loop) which calls `serveOne` per datagram and `DnsCache.sweep` every 64 queries (`Server.lean:506-520`).

**`serveOne`** (`Impl/Server.lean:483-504`), per client datagram:
1. `UdpSocket.recvFrom` → `recvFromRaw` FFI (`ffi/recvfrom.c:100`).
2. `Message.decode` (`Impl/Message.lean:61`) — `Header.decode`, `Question.decode` (uses `DomainName.decodeName`), `decodeRRCanonical` (decompresses names, re-serialises each RR to canonical wire bytes). Undecodable input → `rawDatagramReply = none` (`Server.lean:115`) → silent drop. `qr==1` → drop.
3. `queryProblem` (`Server.lean:101`) → FORMERR/NOTIMPL/REFUSED via `buildErrorResponse`/`finalizeForClient` → `Message.encode` → `sendToRaw` FFI.
4. `UdpSocket.now` → **`resolveWithIO`** (`Server.lean:432`):
   - `Resolver.resolve` (`Impl/Resolver.lean:492`) — fuelled loop over `Resolver.step` (`Resolver.lean:441`):
     - `stepCheckLocal` → `localAnswer`: `DnsCache.lookupNegative`, `lookupAnswerable`, `lookupNegativeSoa`, cached-CNAME chase with loop guard.
     - `stepFindServers` → `walkNs` via `DnsCache.lookupTopCred` + `DomainName.parentDomainWire`; SLIST via `DnsSList.fromNsWithGlueAll`.
     - `stepSendQueries` → pauses (`needsIO`).
     - `stepAnalyzeResponse`: `cnameToChase`, `answersQueryB`, referral handling, **`bailiwickRaws`** (anti-poison filter, `:111`), `cacheUnlessTruncated` → `cacheRRs` over `normRaws` (RFC 2181 TTL normalisation) → `DnsCache.storeChecked`.
   - On pause → **`ioResumeLoop`** (`Server.lean:333`): glueless branch runs nested resolve for NS address; query branch does `buildSubQuery` → `withRandomId` (`randomU16` FFI, CSPRNG) → **`forwardQuery`** (`Server.lean:241`): `Message.encode` → `UdpSocket.exchange` = `retryOption`(`exchangeRaw` FFI, retransmitLimit=2) → `acceptExchanged`/`datagramMatches` (source+destination check) → `Message.decode` → `sanitizeTtlsCap`/`capTtls`. Then `acceptResponse` (id+question match), `unfollowableDelegationB` (= `bogusDelegationB` ∪ out-of-`respInBailiwick`), `afterResume` → `dropIfBizarre` → `Resolver.resume` → cache bounding/eviction.
5. **`replyForResolution`** (`Server.lean:460`): **`scrubAnswerB`** (client-answer CNAME-reachability scrub), `finalizeForClient`, positive caching, `storeNegativeIfCacheable` (SOA-derived negative TTL).
6. `truncateUdp` (512-byte staged truncation) → `Message.encode` → `sendToRaw` FFI.

**Never executed by the server**: `Impl/NameTree.lean` (`treeLookup`, `treeResolve`, `nodeAtName` — the ground-truth ORACLE, used only in proofs and `Test/Loop.lean`), `DnsCache.lookup` (superseded by `lookupTopCred`/`lookupAnswerable`), `DnsSList.bestServer`, `fromNsWithGlue`, `sanitizeTtls` (superseded by `sanitizeTtlsCap`), `RData.decodeA`/`decodeCname` (only `decodeSoa` runs).

## 2. Classification of Proof/ files

Key fact: the resolver code is **monad-polymorphic** (`variable {M} [Monad M] [UdpSocket M Sock ByteArray]`). Proofs constrain the *same constants* the server runs, in two styles: (a) `SatisfiesM` over any `[LawfulMonad M]` — applies at `M = IO` directly; (b) `Prog.run` over the free monad `Prog`/`World` — same definition, transfers to `IO` only insofar as the FFI instance behaves like the `DnsCmd.run` oracle.

| Proof file | Class | Justification |
|---|---|---|
| `AnswerScrub.lean` (`scrubAnswerB_no_foreign`, `_authentic`, `_subset`) | **ON-PATH** | `scrubAnswerB` executes on every non-error client reply. |
| `AnswerScrubAlpha.lean` (`scrubAnswerB_delivered_model_authentic`) | **ON-PATH** (bridge) | Lifts executed scrub guarantee to model `CnameReachable`. |
| `AnswerTerminal.lean` | **MIXED** (support) | Half executed impl predicates, half proof-only α abstractions; feeds IoResumeSound. |
| `BitPacking.lean` | **ON-PATH** | Executed in header codec every packet. |
| `Cache.lean` | **MIXED, mostly ON-PATH** | store/lookup/sweep/bound ops execute. Exception: `lookup_fresh`/`mem_lookup`/`lookup_caseInsensitive` about dead `DnsCache.lookup` — off-path. |
| `DeliveredAuthentic.lean` | **OFF-PATH subject** | About model `Net.Resolves`/`scrubAnswer`; corollary via `ioResumeLoop_sound`. |
| `DomainName.lean` | **ON-PATH** | Name codec runs in every parse/compare. |
| `Enum.lean` | **ON-PATH** | Header codec. |
| `FreeIO.lean` | **MIXED** | `Prog`/`World` proof-only, but subjects are the real `ioResumeLoop`/`forwardQuery` at `Prog`. |
| `GlueConnector.lean` | **ON-PATH subject** | Relates executed `extractGlueRecords`/`bailiwickRaws`/`fromNsWithGlueAll` to model referral SLIST. |
| `Header.lean` | **ON-PATH** | Header round-trip. |
| `IoResumeSound.lean` (**`ioResumeLoop_sound`** :2810) | **ON-PATH via Prog** | Subject is `Prog.run n (Server.ioResumeLoop (M:=Prog) …)` — exact executed def. Heaviest theorem, modulo Prog≈IO gap and ~25 hypotheses (`q.rd=false`, `qtype≠star`, class IN, clock bound, canonical sname — CHECK dischargeable). |
| `Message.lean` (`decode_encode`) | **ON-PATH** | Every datagram. |
| `MessageValid.lean` | **ON-PATH** | Canonicality of executed decoder output. |
| `NameTree.lean` (`treeLookup_*` oracle; **`ioResumeLoop_sound`** :1633, **`resolveWithIO_sound`** :1747) | **MIXED** | `treeLookup`/`treeResolve` never executed (oracle). ShimSoundness theorems via `SatisfiesM` for any lawful M → hold at IO for executed `resolveWithIO`, under `NetworkConsistent T` oracle hypothesis. |
| `NameTreeComplete.lean` | **MIXED** | Completeness of executed loop for any M, relative to `TreeSane`+`NetworkConsistent`; plus off-path `treeResolve` congruences. |
| `NetworkSim.lean` | **MIXED** | Joins real-code Prog run with model realizability. |
| `Parsec.lean` / `Primitives.lean` | **ON-PATH** | Codec primitive round-trips. |
| `Question.lean` | **ON-PATH** | Question codec. |
| `RData.lean` | **MIXED** | `decodeSoa` runs; `decodeA`/`decodeCname` not called at runtime. |
| `Refinement.lean` (**`resolveWithIO_simulates`** :9700) | **MIXED, capstone ON-PATH** | Subject `resolveWithIO` for any M. CAVEAT: network disjunct of `houtcome` takes `HasVerdict` as a **premise** (oracle discharged separately at Prog only) — at `M=IO` the network arm is an ASSUMPTION, not a proof. |
| `Resolver.lean` | **ON-PATH** | About executed `step*`. |
| `ResourceRecord.lean` | **ON-PATH** | RR decode/encode throughout caching/scrub/TTL. |
| `RRsetComplete.lean` | **ON-PATH** | `normRaws` executes in `cacheUnlessTruncated`. |
| `Server.lean` (hygiene, `truncateUdp_*`, `acceptResponse_matches`, `exchanged_matches`, …) | **MIXED, mostly ON-PATH** | Exception: **`sanitize_limit_ttls` about dead `sanitizeTtls`**; live guarantee is `TtlCap.sanitizeTtlsCap_limit_ttls`. |
| `Test.lean` | **OFF-PATH** | Unused reference parser. Decorative. |
| `TtlCap.lean` | **ON-PATH** | `capTtls` runs on every accepted response. |
| `WorldNetwork.lean` | **OFF-PATH subject** (support) | Constructs model networks to discharge oracle premises. |

## 3. Trust boundary / unverified glue

- **FFI C** (`ffi/recvfrom.c`, unverified): `veri_dns_recvfrom` (**timeout returns empty ByteArray instead of error** — `recvfrom.c:100`), `veri_dns_random_u16` (getrandom/urandom — RFC 5452 ID entropy rests ENTIRELY here), `veri_dns_exchange` (fresh unconnected socket per query; builds the `(payload,src,dst,local)` tuple the verified `datagramMatches` gate consumes; connect/dissolve is pure-C trust).
- **`@[extern]`/`opaque`**: all 8 in `Impl/UdpSocket.lean`. `mkUpstreamSocket` declared but never used (dead extern).
- **`UdpSocket IO` instance** including `retryOption` retransmit wiring: harmlessness argued by `retryOption_pure` which **assumes a deterministic action — real networks are not**; informal, not a proof about IO.
- **`partial def serverLoop`**: no termination proof; **no theorem mentions `serverLoop` or full `serveOne`** (only `serveOne_undecodable_no_reply`). serveOne = decode→hygiene→resolveWithIO→scrub→truncate→send verified piecewise, NOT end-to-end.
- **No `axiom`, no `sorry`, no `unsafe`** anywhere (grep-verified). Residual TCB: Lean kernel + compiler, batteries/verso, and the Prog≈IO modelling gap.
- Hardcoded root-server IPs in `Main.lean:12-18` are unverified config.

## 4. Prioritize reading these (on-path, load-bearing)

1. `Proof/NameTree.lean:1747` `resolveWithIO_sound` (+ `:1633` `ioResumeLoop_sound`) — SatisfiesM form, holds at IO; every delivered answer/cached record agrees with the tree given `NetworkConsistent`.
2. `Proof/IoResumeSound.lean:2810` `ioResumeLoop_sound` — deep model refinement; **check its ~25 hypotheses for vacuity** (`serveOne` requires `rd=1` from clients at `Server.lean:98-99`; the model query's `q.rd=false` refers to sub-queries — confirm no vacuity).
3. `Proof/Message.lean:362` + `Proof/MessageValid.lean` — decoder canonicality everything downstream assumes.
4. `Proof/AnswerScrub.lean:80,103` + `AnswerScrubAlpha.lean:94` — client-delivery anti-poison.
5. `Impl/Resolver.lean:129` `bailiwickRaws_owner_inBailiwick` — cache anti-poison filter.
6. `Proof/Server.lean:218,261,237` `acceptResponse_matches`/`accept_match_obligation`/`exchanged_matches` — RFC 5452 spoofing gate over FFI tuple.
7. `Proof/Cache.lean:402,353` `storeChecked_no_downgrade`, `lookupAnswerable_excludes_floor` — credibility ranking.
8. `Proof/TtlCap.lean:106` `sanitizeTtlsCap_limit_ttls` (note `Proof/Server.lean:459` is about dead code).
9. `Proof/RRsetComplete.lean:102` `cacheRRsNorm_complete`.
10. `Proof/Refinement.lean:9700` `resolveWithIO_simulates` — what is oracle-premised (network disjunct) vs proven (cache-hit disjuncts).

## Summary

- **Verification is largely load-bearing**: resolver core is monad-polymorphic, so major soundness theorems are about the *exact constants the server executes*. Codec round-trips, cache credibility/negative/TTL, bailiwick + scrub anti-poison, and the spoof-acceptance gate are all on-path.
- **Off-path/decorative**: `NameTree.treeLookup`/`treeResolve` theorems (oracle), `Test.lean`, `sanitize_limit_ttls` (dead `sanitizeTtls`), `DnsCache.lookup` lemmas, `DeliveredAuthentic`/`WorldNetwork` (model support).
- **Trust boundary**: 340 lines C FFI, `UdpSocket IO` instance, `partial serverLoop` (no end-to-end theorem), Prog≈IO gap; no axiom/sorry.
- **Load-bearing caveat to probe**: at `M=IO` the *network arm* of the refinement is an ASSUMPTION (`HasVerdict`/`NetworkConsistent` oracle), discharged constructively only at `M=Prog`. The honesty oracle is where soundness meets trust.
