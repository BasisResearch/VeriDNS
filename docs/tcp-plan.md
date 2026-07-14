# TCP (RFC 7766 / RFC 1035 §4.2.2) — plan

> **🎉🎉🎉 WHOLE TCP PLAN COMPLETE 2026-07-12 — stages E + U + S all done.** EDNS0-first (E),
> upstream TC→TCP fallback (U), and client TCP serving (S) are all landed, build 293 green, the
> serving capstone `serveTcpDatagram_total` axiom-clean, and both hermetic rigs
> (`tcp_difftest.sh` upstream, `tcp_serve_difftest.sh` serving) all-pass vs unbound. See the
> per-stage banners below.

> **🎉 STAGE E COMPLETE 2026-07-11** — EDNS0-first (decision 1) landed end-to-end: resolver
> advertises OPT 1232 upstream (`Impl/Edns.lean` + `buildSubQuery`), strips OPT on receive
> (`sanitizeTtlsCap`), honors the client's advertised buffer when truncating replies
> (`serveDatagram` at `Edns.clientCap query`, `truncateUdp` cap-parametric), and the FFI upstream
> receive buffer was bumped 512→1232 (`ffi/recvfrom.c`, the actual live-resolution fix — an
> EDNS-sized referral was being `MSG_TRUNC`-clipped). 290 jobs green, all four flagships stay
> axiom-clean, rig 13/13 vs unbound with a new oversized `google.com TXT` (1110 B over UDP, no
> TC) case. NO new model rules (the `ednsBuf` buffer parameter already threaded it). Remaining
> deviations (no OPT echo, no BADVERS/version, DO ignored, no pre-EDNS FORMERR fallback)
> documented in `docs/architecture.md` §EDNS0. Answers >1232 B still need real TCP — stages U/S
> below are UNCHANGED and still open.

Lift the two TCP scope-outs (upstream TC→TCP fallback; TCP serving) to the same verification
standard as the UDP path. Written 2026-07-11 against HEAD `9fe0eb0` (post total-simulation
T0–T2); sized during the T1 arc discussion. This plan is INDEPENDENT of the remaining
total-simulation stages (T3/T4/T5) — no shared files beyond the loop theorems, so order is
a scheduling choice, but the loop-theorem branch (U5) should NOT be interleaved with T4's
honest-arm surgery (both edit `ioResumeLoop_sound`).

**Overall size: XL — an item-5/item-6-scale arc.** Stage U (upstream fallback) ≈ 2–3
sessions, stage S (serving) ≈ 1–2 sessions on top. U5 (the loop-theorem branch) dominates.

## Why (and why now-ish)

- Today a truncated upstream reply is DELIVERED to the client with TC=1 and never cached
  (review #008 — proven), and the client's RFC-mandated TCP retry hits a server that
  doesn't speak TCP. Functionally: any answer that truncates at 512 is unresolvable
  through us. The rig carries a standing wart for this (`testing-gotchas`: "TC→TCP
  fallback expected" — dig's automatic TCP retry gets connection-refused, so
  truncated-answer cases can't complete end-to-end).
- unbound's actual posture: EDNS0 buffer 1232 makes truncation rare; TCP is the fallback
  of last resort. See decision 1 — EDNS0-first is on the table as a cheaper partial
  mitigation and matches unbound parity better than TCP-first.

## Design decisions (PROPOSED — not yet user-locked; recommendations marked)

1. **Ordering vs EDNS0 — RECOMMEND: EDNS0 upstream first, then TCP.** The model already
   threads EDNS0 end-to-end (`ednsBuf`, `negotiatedUdp`, `truncateToCap` — Resolves is
   buffer-parametric since the EDNS0 model work); only the impl lacks the OPT record. An
   impl-side OPT (advertise 1232) + wiring shrinks the truncation surface to unbound
   parity BEFORE the expensive transport work, and makes the TCP fallback the rare path
   it is in unbound. If EDNS0-first is chosen it becomes stage E of this plan (impl +
   codec + `serveDatagram` OPT echo; est. ≤1 session; no new model rules).
2. **Upstream FFI shape — RECOMMEND: ONE pure extern.**
   `tcpExchange : ByteArray → ByteArray → Option ByteArray` (connect + 2-byte-length-framed
   send/recv + close, one call). Mirrors the existing oracle shape exactly: `DnsCmd` gains
   one constructor, `World` gains one field `tcpOracle : ByteArray → ByteArray → Option
   ByteArray`, and the `run_round_*` lemma family gets a small mirror. No `Exchanged`
   wrapper: TCP needs no RFC 5452 source check — the connection is the return path (the
   spoof-free arm in the model, decision 5). Splitting into connect/read/write externs
   would triple the TCB surface and break the oracle symmetry — rejected.
3. **One-shot connections (no reuse/pipelining) — RECOMMEND: YES, as a DOCUMENTED
   SHOULD-deviation.** RFC 7766 §6.2.1 says clients SHOULD reuse connections; modern
   unbound (≥1.13.2) reuses + pipelines out-of-order (§7). One-shot is unbound-pre-2021
   behaviour and observationally identical at the answer/cache/verdict level the model
   verifies (same class of below-the-abstraction detail as RTT ordering, handled by
   `chooseServer`). Connection pooling later is impl-only work below the oracle — but
   breaks the one-extern TCB shape, so it stays out unless a real workload needs it.
4. **On TCP-fallback failure — RECOMMEND: drop the server and retry (unbound parity),
   NEVER consume the truncated UDP reply.** The truncated payload is already never cached
   (#008); with the fallback, it is also never delivered on this path — the resolver
   behaves as if the datagram were lost (`removeServer` + retry → eventually the
   `gaveUp`-justified SERVFAIL, which T1 just made verdict-carrying for free). The
   alternative (deliver TC=1 to the client as today when TCP fails) is more forgiving but
   diverges from unbound and keeps the degraded path alive; rejected.
5. **Model shape for the TCP exchange — spoof-FREE honest-or-lost.** `WorldModels` gains a
   `tcpOracle` clause with only the honest arm (ServerAnswers + RespAgree + validity
   facts, NO `truncateToCap` — or capped at 65535) ∨ loss. No spoofed disjunct: off-path
   TCP injection requires sequence-number hijack, outside the RFC 5452 threat model the
   development targets (document as a TCB-adjacent assumption alongside `WorldModels`
   itself). Consequence: `trustedReply`-style arms are unreachable on TCP hops — the
   threat model is strictly STRONGER there.
6. **Where the fallback lives — in `ioResumeLoop`, NOT the pure resolver.** New guard
   branch after `acceptResponse` (parallel to the bizarre/probe guards): if
   `respA.header.tc == 1`, run `tcpExchange` on the SAME encoded `subQuery` to the same
   server, re-run the decode→sanitize→acceptResponse pipeline on the framed reply, and
   proceed to `afterResume` with the TCP response; `none`/still-truncated ⟹ decision 4.
   The pure step machine (`stepAnalyzeResponse`'s tc=1 arms) is untouched — those arms
   become unreachable under the loop (their delivery semantics remains proven for the
   below-boundary artifact). This keeps `Resolver.resume`/`resolve` and every pure-layer
   theorem byte-identical.
7. **Serving concurrency — sequential accept–serve–close, one query per connection.**
   RFC 1035 baseline; deviations from unbound (persistent connections, 30s idle timeout,
   out-of-order answering, RFC 7828 keepalive) documented, not implemented. dig sends one
   query per connection by default, so the rig sees no difference.

## What exists today (leverage)

- TC guard machinery: model answer/cname rules require `htc : tc = false`; impl
  `cacheUnlessTruncated` is the identity on TC=1; #008 (TC=1 ⟹ cache-byte-identical)
  proven. Decision 4 keeps all of it true and makes most of it vacuous on the main path.
- EDNS0 model threading (`ednsBuf`/`negotiatedUdp`/`truncateToCap`) — stage E needs no
  model work.
- T1's error machinery: TCP connect failures land on the existing lost-datagram retry and
  the now-verdict-carrying `gaveUp` terminal — no new error classification.
- The framing codec is 2 length octets + an existing `Message.encode/decode` payload —
  round-trip proof composes with `Message.decode_encode`.

## Stage U — upstream TC→TCP fallback

### U1 — framing codec — **S**
`frameTcp : ByteArray → ByteArray` (length prefix, guard ≤65535) + `unframeTcp` +
round-trip theorem composed with the message codec. Pure, tiny.

### U2 — FFI + free-monad plumbing — **S–M**
The extern (decision 2) + `UdpSocket` typeclass method + `DnsCmd.tcpExchange` constructor
(`Res := Option ByteArray`) + `World.tcpOracle` + `DnsCmd.run` case. Sweep: every
`DnsCmd`-total proof gains a trivial case — notably `run_world_frame` (the new case
preserves oracle/clock/ids like `.exchange`) and a `run_tcpRound_bind_eq{,_none,…}` mirror
of the `run_round_*` family. Mechanical; the FreeIO file is the only proof file touched.

### U3 — impl loop branch — **M**
Decision 6's guard branch in `ioResumeLoop` + decision 4's failure handling. Also: treat a
TC=1-on-TCP reply as failure (a server that truncates on TCP is broken — unbound parity),
so the response entering `afterResume` from this branch has `tc = false` PINNED — the
model rules' `htc` is satisfied structurally, no truncation reasoning needed.

### U4 — model: the TCP exchange clause — **M**
Decision 5's `WorldModels` clause + the honest-arm realizability lemma (the
`serverAnswer_hasVerdict`-family sibling with the no-cap wire fit). No new `Resolves`
rules: the TCP reply enters the SAME accept/analyze path, so the existing
answer/refer/cname rules justify it — only the WIRE premises differ (no `truncateToCap`,
no spoof disjunct). The per-branch classifiers get a TCP-round variant where they unpack
`hwmApp`.

### U5 — the loop-theorem branch — **L** (dominates the stage)
Thread the new branch through the four big inductions + qmin:
`ioResumeLoop_sound` (~4800 lines), `ioResumeLoop_error_sound`,
`ioResumeLoop_ok_sections`/`_error_sections`, `ioResumeLoop_sent_minimised`. Bounded
because everything AFTER acceptance is shared code — the branch is run-inversion plumbing
+ the U4 clause unpack, not new verdict machinery (same shape as the T1a experience:
retries were `by exact`-cheap, only response-consuming branches cost). `AllSent`: the TCP
retry re-sends the SAME `buildSubQuery` image, so the qmin claim extends by construction —
but the `AllSent` predicate must be taught that `.tcpExchange` is an exchange (its Prog
tree walk gains the constructor).

### U6 — differential testing — **S–M** — ✅ DONE 2026-07-12
`test/tcp_difftest.sh` + `test/mock_auth.py` (dnspython, in `test/.venv`). All four sub-tests
green + stable across repeated runs; the mock logs every query so the fallback decision is
asserted hermetically (tshark on lo0 corroborates). Both resolvers point at ONE loopback mock:
veri-dns via three TEST-ONLY, off-by-default env overrides — `VERI_DNS_ROOT_HINT` (root IP,
`Main.lean`), `VERI_DNS_UPSTREAM_PORT` (dest port, `ffi/recvfrom.c` — Lean/proofs untouched),
`VERI_DNS_ALLOW_LOOPBACK_EGRESS` (lifts the SSRF loopback guard, an `@[init]` Bool whose LOGICAL
value stays `false` so `blockedEgress` is defeq-unchanged and every proof/flagship is unaffected);
unbound via `forward-zone "."` + `do-not-query-localhost: no`.
1. Forced-TC (`forcetc.veridns A`, TC=1 unconditional on UDP): end-to-end answer parity — the
   small answer is fetched over TCP and delivered to the UDP client. veri==unbound.
2. Oversized RRset (`big.veridns TXT`, ~2 KB > 1232): upstream fallback asserted from the mock
   log (UDP tc=1 → TCP). Its ~2 KB answer is truncated to the UDP client with TC=1 — client-side
   delivery of an oversized answer needs TCP SERVING (Stage S), so it is out of U6 scope.
3. tshark lo0: UDP then TCP packets to the mock for the same exchange (decision-logic sniff).
4. Negative controls: (a) repeated forced-TC query stays a correct full answer (truncated payload
   never served); (b) mock TCP listener down ⟹ both degrade to SERVFAIL (drop server → `gaveUp`).

Two findings surfaced + fixed while building the rig:
- **Test code was linked into the shipped exe** — `VeriDNS.Main` imported the `VeriDNS` umbrella,
  which pulls in `VeriDNS.Test.*`; their module initializers computed mock caches at startup
  (~5 s of spin, and flaky first-query drops). `Main.lean` now imports only the runtime Impl
  modules (exe 586→446 jobs, startup 5 s → <0.1 s). This was the real cause of the rig flakiness.
- The mock is a **flat authoritative root** (authoritative for `.` down, no delegation): a
  collapsed root+child mock on ONE loopback IP cannot mimic a real two-server delegation and
  provoked cache-state-dependent descent loops in veri-dns; a flat root sidesteps that and still
  forces the UDP→TCP fallback, which is what U6 verifies.

NOTE: the "TC→TCP fallback expected" wart in `test/difftest.sh` is a SERVING (Stage S) deliverable
and stays until S4 — U6 is the upstream side only.

## Stage S — TCP serving — ✅ DONE 2026-07-12

> **🎉 STAGE S COMPLETE 2026-07-12 — TCP serving end-to-end, build 293 green, `serveTcpDatagram_total`
> axiom-clean, Stage-S rig all-pass. The WHOLE TCP PLAN (E + U + S) is now done.** The resolver
> speaks TCP on both sides. `serveTcpDatagram` (Impl/Server.lean) is `serveDatagram`'s core verbatim
> with the reply tail swapped to RFC 7766 §8 framing (`TcpFraming.frameTcp`, no truncation) via a new
> effect-free `tcpSend` class method; `serveTcpDatagram_total` (Proof/ServeTcp.lean) is
> `serveDatagram_total` with the ≤512 truncation conjunct replaced by `unframeTcp_frameTcp` under a
> ≤65535 guard — first-compile, axiom-clean `[propext, Classical.choice, Quot.sound]`. Serving is
> sequential accept–serve–close on a background task (`Main.lean` `tcpServeLoop`), sharing the cache
> with the UDP loop via a `Std.Mutex`. Five pure-I/O externs added. `test/tcp_serve_difftest.sh`
> asserts `dig +tcp` parity vs unbound including the flagship `big.veridns TXT` (~2 KB delivered IN
> FULL, byte-identical, TC=0). The "TC→TCP fallback expected" wart is gone from `test/difftest.sh`.

### S1 — FFI — **S** — ✅ DONE
Five pure-I/O serving externs in `ffi/recvfrom.c` (TCB note, gap-4 audit trail): `tcp_listen`,
`tcp_accept` (→ `(connfd, 6-byte client addr)`), `tcp_recv_msg` (one RFC 7766 §8 length-framed
message → unframed payload, `none` on EOF/short-read/deadline), `tcp_send`, `tcp_close`. Serving
cannot be one pure extern — the resolver computes the reply between read and write. Only `tcp_send`
is exposed through the verified `UdpSocket` class (as `tcpSend`, default `pure ()`, Prog = `.pure ()`);
the rest are driver plumbing like the UDP `recvfrom`/`bind`.

### S2 — impl — **M** — ✅ DONE
`serveTcpDatagram` (Impl/Server.lean): the EXISTING `serveDatagram` core (ACL, decode,
`queryProblem`, `resolveWithIO`, `replyForResolution`, `serveTouches`/`boundLru`) verbatim →
`TcpFraming.frameTcp` → `tcpSend`. No `truncateUdp` (TCP carries a whole ≤65535 message). The
accept/recv/close driver (`tcpServeLoop`) and the UDP↔TCP shared-cache mutex live in `Main.lean`
(both loops lock across each serve). Per-TCP connection-count cap deferred (decision 7).

### S3 — capstone sibling — **M** — ✅ DONE
`serveTcpDatagram_total` (Proof/ServeTcp.lean): the `serveDatagram_total` statement minus the ≤512
truncation conjunct (replaced by the frame-fit round-trip `unframeTcp_frameTcp` under ≤65535). The
reply-path packs (`replyPath_cacheOut_wf`/`_canon`, scrub exactness, RD echo, question pin) and the
verdict chain (`resolveWithIO_verdict_sound`/`_error_sound`) are shared UNCHANGED — only the send tail
differs, and `tcpSend = pure ()` makes it one fewer run-inversion step than the UDP proof. Mechanical
copy of the (~260-line) capstone + `serveTcpDatagram_served`; axiom-clean on first compile.

### S4 — rig — **S** — ✅ DONE
`test/tcp_serve_difftest.sh`: `dig +tcp` parity vs unbound on the U6 hermetic mock — small answer,
forced-TC name, NXDOMAIN, and the flagship `big.veridns TXT` (~2 KB delivered in full over TCP,
byte-identical to unbound, TC=0). The "TC→TCP fallback expected" wart is deleted from
`test/difftest.sh` (dig's automatic TC=1 retry now completes over our TCP listener, so those cases
assert end-to-end equality; a residual TC=1 is now a regression, not a skip).

## Unbound parity ledger

| Aspect | Us (this plan) | unbound | Verdict |
|---|---|---|---|
| UDP-first, same-query same-server TCP retry on TC | ✓ | ✓ | parity |
| EDNS0 1232 posture | stage E (decision 1) | default since 1.12 | parity if E lands first |
| TCP reply trusted without spoof entropy | ✓ (model: spoof-free arm) | ✓ | parity |
| Fallback failure → drop server, retry next | ✓ (decision 4) | ✓ | parity |
| Upstream connection reuse / pipelining | ✗ one-shot | ✓ (≥1.13.2, RFC 7766 §6.2.1.1/§7) | documented SHOULD-deviation |
| Persistent serving connections, idle timeout, OOO | ✗ sequential | ✓ (`tcp-idle-timeout` 30s) | documented deviation |
| TFO / keepalive (RFC 7828) / DoT / DoH | ✗ | ✓ | scoped out |

## Risk register

| Risk | Mitigation |
|---|---|
| `DnsCmd` constructor ripple beyond FreeIO (any `match` over `DnsCmd` in proofs) | U2 sweep is grep-bounded (`DnsCmd` appears only in FreeIO + UdpSocket instance); `run_world_frame`'s new case is one line |
| U5 branch cost balloons in `ioResumeLoop_sound` (the 4800-line induction) | The branch consumes a response through the SHARED accept/analyze path — crib the existing accepted-response case with the U4 clause substituted for the UDP one; T1a demonstrated the retry-shaped branches are `by exact`-cheap |
| `AllSent`/qmin misses the new exchange constructor (silent under-claim) | U5 explicitly extends the Prog-tree predicate; the SentMinimised mocks get a TCP-round script so an unhandled constructor fails a mock, not silently |
| A server answers TCP with TC=1 (corner) | Decision 4/U3: classified as failure, never consumed — `htc` stays structurally pinned |
| TCB growth (1 upstream + ~3 serving externs) | Flag in the gap-4 audit trail; upstream stays one pure call by design (decision 2); serving externs are pure-I/O like the existing 8 |
| Interleaving with total-simulation T4 (both edit `ioResumeLoop_sound`) | Schedule U5 strictly before or after T4, never concurrent |
| Rig flakiness from real-network truncation cases | All U6/S4 cases run against local dnspython mocks — hermetic; the live-Internet cases stay truncation-free |
