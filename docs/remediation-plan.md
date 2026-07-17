# veri-dns remediation plan — external security review (2026-07)

Triaged against HEAD `47efe79` (post the priming-glue and scrub-exactness fixes of 2026-07-07).
Each finding is classified by *where the fix lands*, which determines its cost far more than the
finding's severity:

- **impl-only** — a change under `VeriDNS/Impl/` (or `ffi/`) with no model/proof obligation. Cheap;
  verify by `dig` against unbound.
- **verified-core** — touches a definition the capstones (`IoResumeSound.lean`, `Refinement.lean`,
  `ResolveWithIOSound.lean`) unfold, so it needs a coordinated model + impl change and a re-proof.
- **spec-decision** — the *model* is over-permissive; the impl faithfully conforms. Requires a
  design call (standing preference: match RFC + unbound, per `prefer-rfc-real-impl`), then a
  model-tighten + re-proof.
- **below-boundary** — FFI/C or kernel behaviour the proofs do not cover; fix + differential test,
  no proof.
- **coverage-gap** — the behaviour is fine but nothing pins it; add a theorem/obligation or a test.

The refinement is a forward simulation, so **tightening the impl to reject more is usually free**
(the model already permits the superset); **tightening the model** is the expensive direction
(every rule consumer re-proves). Where a fix can be framed as "impl rejects a subset the model
still allows", prefer that.

Verification harness for every runtime item: `pkill -f bin/veri-dns; (.lake/build/bin/veri-dns >/tmp/v.log 2>&1 &)`
then `dig @127.0.0.1 -p 5300 <name> <type> +tries=1 +timeout=15`, diffed against unbound. FFI
externs are not interpretable — test through the built exe (see `testing-gotchas`).

---

## Progress log

- **2026-07-09 (10)** — **#003 (delivered answer owner case) CLOSED — the last deferred item;
    every review finding is now fixed, theorem-pinned, or scoped out with rationale.** Commit
    `35c1454`; build green (284 jobs), both capstones axiom-clean, rig 12/12 (incl. live CNAME chains — chain-hop
    normalization does not break chasing), new mock `Test/Loop.deliveredOwnerClientCase`, live
    `dig`: `example.com` owners now `example.com.` (the post-C2 `eXaMpLE.COm.` leak is gone) and
    a mixed-case client query gets its exact bytes back — including on the cache-served second
    query, since the rewrite is per-delivery. The mapped fix executed as planned (both scrub
    halves move together), with three refinements:
  - **Normalization target = the FIRST entitled reach name (`find?`), not a case-fold**: the
    reach set is seeded with the client's question bytes verbatim, so qname-owned records get
    the client's exact case (RFC 1035 §2.3.3) and chain hops take the previous link's rdata case
    — compression-pointer behaviour. Model `scrubAnswer` and impl `scrubAnswerB` both became
    `filterMap`s (`{r with owner := n}` / the `setOwnerB` splice `m ++ (rrFixed ++ rdata)` —
    an `rrWire`-to-`rrWire` rewrite on canonical blobs). New model pin
    `scrubAnswer_owner_at_qname` (the query name heads the entitled list, so a CI-match at the
    qname always normalizes to the client's bytes — a scrub that skips the rewrite is red here).
  - **The ReachCorr re-run became a STRENGTHENING, not a re-prove**: the owner rewrite needs the
    two `find?` scans to pick corresponding names, which the old two-sided existential
    `ReachCorr` cannot give — replaced by the pointwise `NamesCorr` (same length,
    `αName reachB[i] = some reachM[i]` + canonicity within the 255-octet cap per member),
    provable because both closures expand in lockstep. `AnswerScrubAlpha` rewritten around it;
    the commute `αSection_scrubAnswerB_eq` now takes `CanonicalSection` (which subsumes the old
    `AnswerWriteWf`-`RdataCanon` CNAME-target feed — `CnameTargetsCanonical` deleted) + the seed
    qname's ValidLabels/≤255 package (from the client datagram's decode, via `hdec` at the
    capstone). New `DeliveredWire` layer: `CanonicalName`, `canonicalRR_parse`,
    `setOwnerB_rrWire`, `reachableNamesB_canonical` (the scrub-preserves-canonicity proof needs
    every reach name canonical: seed = decoded question, steps = `CanonicalRdata` type-5 rdata).
  - **One capstone statement change (accepted)**: `serveDatagram_verdict_sound`'s byte-literal
    `Sublist v.answer` conjunct is FALSE under the rewrite and was **dropped** — subsumed by the
    kept equality `= scrubAnswer qm.qname v.answer` plus the model-side membership form
    `scrubAnswer_mem`/`scrubAnswer_data` (delivered record = owner-rewritten verdict record,
    same rdata/ttl/class). Subset-shaped consumers reshaped: `scrubAnswer(B)_subset` →
    `scrubAnswer(B)_mem` (pre-image form); `DeliveredAuthentic`/`deliveredResponse_authentic`
    restated over the normalized copy; `ServeSound` tree-agreement transfers via new
    `rrInTree_owner_congrCI` (the tree walk was already CI — `nodeAtName_congrCI` existed), but
    proving the rewritten blob *parses* needs `CanonicalSection`+`CanonicalName`, which the
    generic-monad NameTree track cannot supply — `resolveThenReply_sound` now takes them in one
    combined `SatisfiesM` hypothesis with `ShimSound` (no generic `SatisfiesM.and` exists;
    the facts are discharged by the codec in the `Prog` track).
  - Est was M; actual ≈ M (one session, ~10 files). `ioResumeLoop_sound` untouched entirely;
    `serveDatagram_verdict_sound` changed only by the dropped conjunct + the two derived
    hypotheses (`hq255`/`hqn` from the existing `hdec`).
- **2026-07-09 (9)** — **Phase 6 batch: #008 + #007/#010a + #001/#014 + the #012/#013
    delivered-authority residual ALL CLOSED; #003/#016/rebind decided + documented.** Three
    commits (`bd88cba`/`6d2047a`/`2bc03e5`), build green (284 jobs), both capstones untouched in
    statement and axiom-clean, rig 12/12, four new mock `#guard`s. Per-item:
  - **#008 (TC=1 negative-cache gate, coverage-gap)**: the *positive* half was already pinned
    (`Proof/Cache.truncated_cache_unchanged` via the generated `usingthecache_truncated_not_cached`
    predicate — which was itself undischarged in the coverage layer; now `via`-linked green). The
    negative half + end-to-end are new: `negativelyCacheable_truncated`,
    `storeNegativeIfCacheable_truncated` (= `pure base`, no effects), and
    `replyForResolution_truncated_cache_unchanged` (TC=1 ⇒ the reply path returns the cache
    **byte-identical**, positive AND negative, while still delivering) — all `rfc_proves`-linked
    to RFC 1035 §7.4's caveat ([1035][2581:2587]). Mock:
    `Test/Loop.truncatedReplyNotNegativelyCached`. Proof cost ≈ 0 (first-pass green;
    `import VeriDNS.Proof.Cache` into Proof/Server is cycle-free).
  - **#007/#010a (RD echo, impl-only — and it stayed impl-only)**: `deliveredResponse` gains
    `rd := query.header.rd`. Recon: `buildSubQuery` sends iterative `rd=0` upstream, so the
    fresh path delivered the upstream echo `rd=0` while cache/error paths (built on
    `query.header`) echoed `rd=1` — RD leaked cache state. One field in a named builder =
    invisible to the run-inversion proofs (the #010b cheap-direction lesson again): zero proof
    diff. Pins `deliveredResponse_rd`/`errorResponse_rd` (both `rfl`), linked [1035][1401:1529];
    mock `Test/Loop.rdEchoedUniformly`; `dig` flags now `qr rd ra` on both paths.
  - **#001/#014 (case-fold provenance)**: new spec predicates `namespace_casefold_exact` (the
    complete per-byte ASCII fold characterization, stated against raw octets: 65–90 → +32,
    everything else fixed) and `namespace_compare_complete` (compare true ONLY on fold-equal —
    the converse `namespace_compare_caseinsensitive` can't express; kills the always-true
    compare). Instantiations `foldCaseByte_casefold_exact` + `nameEqCI_complete` (ByteArray has
    no `LawfulBEq`; beq→eq goes through the `nameEqCI_of_beq` ext recipe). ProofLinks: both new
    theorems + previously-unlinked `foldCaseByte_nonalphabetic_exact` + the load-bearing hand
    lemma `NameTree.foldCaseByte_toNat`; all five `namespace_*` case predicates discharged green
    with `via`. **Red/green: the review's surgical 'W' under-fold (`b != 87` in the guard) now
    fails at `foldCaseByte_casefold_exact` — previously every RFC-linked prop survived it.**
  - **#012/#013 residual (delivered authority)**: the plan's "would touch deliveredResponse/
    verdict statements" worry was **stale** — recon showed the capstones never pin the authority
    section (`RespAgree` = rcode + answer only), so the scrub is a `deliveredResponse`-internal
    redefinition (cheap direction). New `Server.scrubAuthorityB` (decode-or-drop +
    `isAncestorB` owner-at-or-above-qname keep), `nscount` recomputed;
    `deliveredResponse_decode_encode` re-proved with the same hypothesis list (`hns` now supplies
    only the 16-bit bound via `scrubAuthorityB_size_le` + `BitVec.isLt` — call sites unchanged).
    Pin `deliveredResponse_authority_owned`; mock `Test/Loop.deliveredAuthorityScrubbed`
    (off-owner SOA → AUTHORITY:0, on-owner SOA kept); live NXDOMAIN still carries the root SOA.
  - **Decisions recorded (see Phase 6 table)**: #003 deferred with a mapped fix (post-C2 the
    0x20-randomized case is now client-visible in answer owners — a both-sides case-normalization
    through `scrubAnswerB`/`scrubAnswer` + the ReachCorr lockstep, est M; not worth breaking the
    byte-exact scrub theorem for a cosmetic SHOULD today); #016 EDNS0 stays scoped out (same
    stance as TCP); rebind filter stays out (unbound's `private-address` is also off by default —
    `prefer-rfc-real-impl` says match).
  - ⚠ **Gotcha**: `lake build` does NOT rebuild the `veri-dns` exe (not a default target) — the
    first rig run this session validated a **stale binary** (looked green, proved nothing).
    `lake build veri-dns` before any runtime verification.
- **2026-07-09 (8)** — **Item-4 stage D (per-retry TXID) LANDED — ITEM 4 COMPLETE, Phase 5 closed.**
    Build green (284 jobs), both capstones untouched (statements AND proofs — zero proof diff),
    `exchange-junk-test` 3/3 with red/green confirmed, new mock `Test/Loop.retransmitFreshSecrets`.
    **The feared `retryOption_pure`/transport-determinism rework evaporated on recon** — the fix
    is a *deletion*, not a rework, because the loop already retransmits with fresh secrets:
  - **Recon that changed the plan**: `markQueried` only *count-deprioritizes* (increments
    `transmissionCount`; `bestWithAddress` picks least-tried-first, RFC 1035 §7.2) — a timed-out
    server is never removed, so `ioResumeLoop`'s timeout arm already round-robins back to it, and
    **every round draws a fresh `rid` + `cid`** (post-C2). Loop-level per-retry TXID was already
    real and already *theorem-pinned*: `run_ioResumeLoop_retryThenAnswer` (FreeIO) shows the
    second round sends `withSecrets subQuery₀ (w.ids (idCtr+2)) (w.ids (idCtr+3))` — the next
    stream draws, never a reuse. The ONLY same-(id, case) retransmit was the below-boundary
    `retryOption retransmitLimit` inside the IO `UdpSocket.exchange` instance — the same encoded
    datagram up to 3×, which per RFC 5452 §4.4 hands an off-path spoofer three race windows for
    one (id, case) guess. The model never saw it (that's what `retryOption_pure` was *for*).
  - **Fix (landed)**: the IO instance `exchange` is now **single-shot** (one `exchangeRaw` call);
    `retryOption`/`retransmitLimit` deleted (`Impl/UdpSocket.lean`), `retryOption_pure`/
    `retryOption_all_timeout` deleted (`Proof/Server.lean`, replaced by a module-doc pointing at
    the FreeIO retry-lemma pin). Retransmit liveness is preserved — it just moved above the
    boundary: timeout → round recursion → least-tried re-selection → fresh secrets, bounded by
    fuel + the 5 s deadline exactly as before (the old ×3 same-datagram retry at 2 s each could
    blow through the whole deadline mid-round; per-round attempts respect it). `primeRootHints`
    inherits the same semantics (its per-hint loop is the retry, fresh secrets per hint).
  - **Proof impact: ZERO** (below-boundary in the *cheap* direction of the #021 lesson — deleted
    control flow the model never modelled). First-pass green; no capstone, FreeIO, or driver
    file touched.
  - **Verify**: mock `Test/Loop.retransmitFreshSecrets` (`#guard`): script = timeout then answer
    → exactly 2 sent queries, ids 7777/7779, qnames `randomizeCase 7778/7780` (fresh txid AND
    fresh case pattern, datagrams differ), answer still delivered. Runtime `exchange-junk-test`
    case 3: silent mock server → exactly **1** datagram on the wire, `none` at ~2 s;
    **red/green confirmed** (re-adding a 3-attempt same-datagram loop → case 3 fails on both
    the 6 s elapsed and the 3-datagram count). `randomU16` TCB docstring extended (draws are
    per *send attempt*, retransmits included); architecture.md 0x20 section updated.
- **2026-07-09 (7)** — **Item-4 stage C2 (0x20 outbound entropy) LANDED — the anti-spoof flagship's
    stage-1 is complete** (A+B+C1+C2). Build green (284 jobs), both capstones axiom-clean
    `[propext, Classical.choice, Quot.sound]`, rig **12/12 live** (incl. CNAME chains + NXDOMAIN —
    real servers echo the case-randomized qname byte-exact), new mock
    `Test/Loop.sentQnameCaseVaries` (sent upstream qname = `randomizeCase cid sname` under the
    SECOND draw, ≠ canonical bytes, CI-equal, varies with the id stream). The C2 recipe below
    executed as mapped; the threading cost came in at the LOW end of the M-L estimate (single
    session, most files first-pass green). Four addenda to the recipe:
  - **`positive_answer_covered` (AnswerTerminal) was the one hidden consumer** of the acceptance
    gate at the *unstamped* question: its `hqmatch` was stated at `subQuery0.question`, which was
    silently defeq through `withRandomId` (header-only update) but NOT through `withCaseSeed`'s
    question map. It only ever reads the **qtype** conjunct, so it now takes the gate at
    `(withSecrets subQuery0 rid cid).question` (new `{rid cid}` implicits; the 5 call sites pass
    their existing `acceptResponse_questionMatches haccR` unchanged).
  - **Singleton `Array.map` is not `rfl`-reducible** — state sent-question facts in `[0]?` form
    and reduce via `Array.getElem?_map` (the NameTreeComplete recipe's trick, needed in three
    places: `withSecrets_question`, `positive_answer_covered`'s `hsub'`, and
    `questionMatches_fields`' restated `hsq`).
  - `questionMatches_fields` gained `hswci : nameEqCI sw snameB` exactly as planned; call sites
    supply `withSecrets_question … hsubq` + `randomizeCase_nameEqCI _ _` (a 2-line perl-able
    rewrite ×5).
  - Reduction-lemma fuel bumps for the record: round `bind_eq` family m+3→m+4 (k gains the `cid`
    arg; new `run_log_randomId2_bind_eq` prefix helper), `timeout` +5, `rejectSpoof` +6,
    `unfollowable` +7, `continue` +6, `bizarre(')` +6 (idCtr conjunct `+1`→`+2`), `answer`/
    `nxdomain` `Exists.intro 5`→`6` (one extra `refine run_randomId_bind`), retry lemma
    second-round ids `+2`/`+3` and `K₂+6`. Capstone clusters: exactly the predicted 4th `rcases`
    successor arm (two clusters each file, incl. the egress-blocked arm) + `withSecrets` literal
    retargets + `hwm` gains `(w.ids (w.idCtr + 1))`. Drivers: one `SatisfiesM.bind` peel each;
    NameTreeComplete's `questionMatches_facts` consumer bridges via `hsentq` +
    `nameEqCI_trans hci (randomizeCase_nameEqCI cid _)` as scripted. `Main.primeRootHints` second
    draw + #002 TCB docstring extension (case seed shares the extern contract) done.
    **Remaining item-4: stage D (per-retry TXID) only.**
- **2026-07-09 (5)** — **Phase 4 parser batch DONE: #009a/#009b/#037/#010b all closed** (three
  commits `17b9bf2`/`16e11e9`/`c3c5832`), build green (283 jobs), both capstones axiom-clean
  (statements untouched), rig 12/12, seven new parser regressions in `Test/Loop.ParserHardening`.
  Corrections to the triage below:
  - **#009a was already fixed** pre-review (`decodeName`'s `encodedNameLen ≤ 255` check landed
    with the June diff-test hardening), as was #009b's strictly-backward-pointer half. Only the
    header-pointer rejection remained. New pin: `overlongNameRejected`.
  - **#009b (cheapest possible form)**: `decodeNameAux`'s pointer guard tightened *in place*
    (`offset < pos` → `12 ≤ offset ∧ offset < pos`). Changing the guard **condition** rather
    than nesting a new `if` kept every proof shape-identical — the adversarial inversion proofs
    (`decodeNameAux_validLabels`/`_valid`/`_adversarial_bounds`) split blindly and never consume
    the guard fact, and the round-trip proofs never enter the pointer branch (encoder emits no
    pointers). **Zero proof diff.** Tests: `headerPointerRejected` + `compressionStillAccepted`
    (positive control: ordinary offset-12 compression still decodes).
  - **#010b landed as FORMERR-split, not documentation**: `rawDatagramReply` now decodes the
    12-byte header of an undecodable datagram — header undecodable / QR=1 / non-QUERY opcode →
    still dropped (anti-reflection); decodable *query* header + malformed body → minimal
    **12-byte FORMERR echoing the id** (unbound parity, `prefer-rfc-real-impl`). The
    anti-reflection property the old blanket-drop protected is now a **theorem**:
    `rawDatagramReply_no_amplification` (reply = 12 bytes ≤ any datagram with a decodable
    header, via new `headerDecode_min_size`); `rawDatagramReply_formerr` pins the reply shape
    (no question echo, all sections empty — nothing attacker-controlled reflects).
    **Proof cost ≈ 0 at the capstones**: the send was *already* gated on `rawDatagramReply`
    inside `serveDatagram`, so no control flow visible to the run-inversion proofs changed —
    the #021 lesson applied in the cheap direction; only `Proof/Server.lean`'s two policy
    theorems were rewritten (+ helpers). Tests: `garbageDatagramDropped`,
    `responseDatagramDropped`, `malformedQueryFormerr`; live-checked against the binary.
  - **#037 halved by a unified constructor**: `decodeRRCanonical` gained ONE
    fixed-prefix-then-name arm covering MX (15, 2-byte pref) and SRV (33, 6-byte
    prio/weight/port), mirroring how 2/5/12 share the `nameType` arm; `CanonicalRdata` gained
    the single `prefixedName` constructor (`(t=15 ∧ pre=2) ∨ (t=33 ∧ pre=6)`), so
    `run_decodeRRCanonical_shape`/`rrWire_frame`/`decode_answer_parseRaw` each needed one new
    arm (templated on SOA), not two; the two AnswerTerminal rdata-canonicity `cases` discharge
    it by type-code contradiction. Est. was ~260-330 new proof lines; actual ≈ 230. Tests:
    `mxPointerDecompressed`, `srvPointerDecompressed`, `mxBadRdlenRejected`.
- **2026-07-09 (4)** — **#017 (FFI drops the real reply on one junk datagram) FIXED**, C-only as
  planned — the below-boundary framing held (zero Lean impl/model/proof changes; both capstones
  untouched by construction). `veri_dns_exchange` now loops `recvmsg` on the same fd, skipping any
  datagram whose source (IP:port) ≠ the queried address, re-arming `SO_RCVTIMEO` with the
  *remaining* time each iteration against a `CLOCK_MONOTONIC` 2 s deadline (a junk stream cannot
  extend the wait; `EINTR` retried). The C pre-filter is deliberately a **strict subset** of the
  proven Lean gate's drop — it only ever *skips* source-mismatched datagrams the gate would reject,
  never accepts; the returned datagram is still fully checked in Lean (`datagramMatches`:
  id/question/destination). Verified by a new **runtime FFI test** (externs aren't interpretable):
  `lean_exe exchange-junk-test` (`Test/ExchangeJunk.lean`, logic in the lib so `lake build`
  type-checks it; entry point split into `Test/ExchangeJunkMain.lean` because a top-level `main`
  in the lib closure clashes with `VeriDNS.Main`'s). Case 1: mock server injects two junk
  datagrams from a third source port before the real reply → reply returned (pre-fix binary:
  FAILS, junk returned as the exchange result — red/green confirmed by rebuilding against the
  pre-fix `recvfrom.c`). Case 2: junk-only flood → `none` at ~2 s (deadline enforced). Build green
  (283 jobs), rig 12/12. Run: `lake build exchange-junk-test && .lake/build/bin/exchange-junk-test`.
- **2026-07-09 (3)** — **#004 (in-bailiwick subdomain answer caching) FIXED**, impl + model +
  sharpened pin. Build green (282 jobs), both capstones axiom-clean, rig 12/12 (incl. the live
  CNAME chains — the chain-tail drop did not break chasing), new mock regression
  `Test/Loop.subdomainRiderNotCached` (`sub.example.com A 6.6.6.6` riding an `example.com`
  answer → not cached; repeat query for the subdomain goes back upstream — pre-fix it was
  cache-served the attacker record with zero exchanges). Three refinements to the recon below:
  - **Impl filter keyed to the reply's ECHOED question name, not `s.resources.sname`**: new
    `Resolver.echoedQname` + `ownerRaws` (`nameEqCI (rrName rr) qEcho` keep) at the two
    `stepAnalyzeResponse` answer writes; `Server.replyForResolution` keeps `clientQname query`.
    Reason: the bridge `αSection_ownerRaws_eq` needs the filter name's **canonical wire triple**
    (`nameEqCI` is a whole-bytes case-folded compare, not a parsed-labels compare like
    `isAncestorB`, so — unlike `αSection_bailiwickRaws_eq` — αName facts alone don't suffice);
    only the decoded question supplies canonicity (`questionFromLabels_canonical`). The #036/#012
    echoed-name recipe, now confirmed *forced* for any `nameEqCI`-based filter.
  - **Model tighten via a helper image, not 18 in-place record updates**: new
    `Response.answerOwned qname` (answer filtered to `nameEq r.owner qname`, empty
    authority/additional) + component simps + `answerOwned_congr` +
    `absorb_answerOwned_congr` (image AND bailiwick slot move together under `nameEq` — the
    write-path `cnameRR_congr`); swapped at the `trustedReply`/`answerCname`/`trustedCname`
    `hcf0` images and every downstream wrapper. `Cache.absorb` untouched (its `isAncestor` keep
    is vacuous on the pre-filtered image — new `isAncestor_of_nameEq`).
  - **Pin is STRONGER than planned**: `TrustedReplyCache`/`TrustedCnameCache` escape predicates
    sharpened from `isAncestor q.qname r.owner` to `nameEq r.owner q.qname` — a trusted-forgery
    write is now provably confined to the queried name ITSELF, not its subtree (via new
    `absorb_answerOwned_pos_owner`/`absorb_answerOwned_topServed_owner`); reverting the filter
    breaks `resolves_cache_in_bailiwick`/`DeliveredAuthentic`, not just a test.
  - Producer side: `section_owner_extra_perm` + `absorb_answerOwned_pos` (filter-collapse) +
    `cname_write_WriteRefines(_ref)` restated over `ownerRaws`; driver-facing
    `answer_write_WriteRefines_echo` (IoResumeSound) packages echoed-name canonicity + the congr
    move for all four `hcf0` call sites. `ownerRaws_{subset,owner_eq,toList_sub,canonical}` +
    `sectionWhole_owner`/`ttlUniform_owner` mirror the bailiwick companions.
  - ⚠ **Gotcha (cost spike + fix)**: inlining `(resp.question[0]?).elim ByteArray.empty
    (·.qname)` in the impl blew up `whnf`/`isDefEq` at three `IoResumeSound` clusters
    (deterministic heartbeat timeouts that survived a 2M→4M bump — the elim scrutinee re-reduces
    inside every big state-literal comparison). Naming the expression (`echoedQname`,
    semi-reducible) restored the old performance profile at 2M. **Lesson: never inline a
    compound expression into impl code that run-inversion proofs carry through state literals —
    name it.** Est was M; actual ≈ M (one session).
- **2026-07-09 (2)** — **#012/013 (negative-cache SOA owner) FIXED**, impl + model + pin. Build
  green (282 jobs), both capstones axiom-clean, rig 12/12 (incl. the live NXDOMAIN), new mock
  regression `Test/Loop.offOwnerSoaNotNegativelyCached` (NXDOMAIN with a `poison.attacker.test`
  SOA → delivered but `negatives` stays empty and a repeat query goes back upstream; pre-fix the
  poison SOA was cached and served for the negative TTL). The #036 recipe applied verbatim:
  `extractSoaNegative` gained a `qname` param with an `isAncestorB rr.name qname` conjunct
  (per-element inside `findSome?`, NOT a rule premise — first-match lockstep), fed the reply's
  echoed question name (`clientQname resp`); model `soaNegTtl` gained `(qname : Name)` with
  `isAncestor r.owner qname`, `absorbNeg` passes `q.qname`. **Proof cost: S, below the S-M
  estimate — the whole cascade compiled unchanged on the first build** (every `absorbNeg`
  consumer treats `soaNegTtl` opaquely; the run-inversion/canon proofs are shape-stable under
  the extra Bool conjunct and the extra parameter). Pin: new `CacheNegSoaOwner` invariant
  (DeliveredWire) + `extractSoaNegative_owner` + `cacheNegSoaOwner_storeNegative` +
  `replyPath_cacheOut_negSoaOwner` (ResolveWithIOSound) — a mutation dropping the owner conjunct
  now breaks a theorem, not just a test. Not done (deliberately): the *delivered* authority
  section on the first (non-cache) response still passes through verbatim — unbound would scrub
  it to AUTHORITY:0; only the cache and every cache-served negative are protected. Full
  authority-section scrub would touch `deliveredResponse`/verdict statements — fold into #037/
  parser batch if wanted.
- **2026-07-09** — **#036 (off-owner CNAME chase) FIXED**, impl + model + full re-proof. Build
  green (282 jobs), both capstones (`ioResumeLoop_sound`, `serveDatagram_verdict_sound`)
  axiom-clean, rig 12/12 (incl. the live CNAME chains `www.iana.org`/`www.ietf.org`), new mock
  regression `Test/Loop.offOwnerCnameNotChased` (off-owner CNAME → 1 exchange, no query for the
  attacker target, empty scrubbed answer; pre-fix it steered the next upstream query). Two
  refinements to the original triage under #036 below: the model tighten was done by
  *parameterizing* `cnameRR` with the query name (not a rule premise), keeping impl/model
  first-match lockstep; and the impl compares against the **reply's echoed question name**
  (self-contained in the datagram), bridged to the model `q.qname` through the `questionMatches`
  CI gate + `cnameRR_congr` (model `nameEq` is itself case-insensitive). Est was M-L; actual ≈ M.
- **2026-07-08 (2)** — **#015 root cause FIXED** (SBELT fallback at the root cut). Build green
  (282 jobs), `ioResumeLoop_sound` + `serveDatagram_verdict_sound` axiom-clean, rig 12/12,
  new mock regression test `Test/Loop.addresslessRootNsSbeltFallback`. Two corrections to the
  original triage under #015 below: the fallback must be **root-cut-only** (a blanket
  zero-address fallback breaks ordinary glueless delegations), and the proof cost was **S, not
  M** (the `mc = 0` guard makes the new arm land in the *existing* belt disjunct verbatim — no
  model rule, no new induction, `ioResumeLoop_sound` untouched).
- **2026-07-08** — Phase 0 (#000 + rig) and **#021 (egress filter) DONE**. Build green (282 jobs),
  `ioResumeLoop_sound` axiom-clean, differential rig 12/12 vs unbound. See the ✅ marks below.
  Key correction: #021's proof impact was **not** "none" as originally triaged — the call-site
  egress guard is structurally visible to the operational refinement, so it had to be threaded
  through five proof files (see the revised note under #021).

## Phase 0 — unblock + baseline (do first)

### 000 — Linux link failure (`arc4random`) — **below-boundary — ✅ DONE 2026-07-08**
The review host needed `arc4random`→`getrandom` in the FFI to link at all on Linux. This host is
macOS (arc4random present), so it never surfaced here.
- **Fix (landed)**: `ffi/recvfrom.c` `veri_dns_random_u16` now `#ifdef __linux__` → `getrandom(2)`
  with a `/dev/urandom` fallback (and `#ifdef VERI_DNS_HAVE_GETRANDOM` guard for pre-3.17 kernels),
  keeping `arc4random` on BSD/macOS. **Fails closed** (returns an `EIO` IO error) if no CSPRNG is
  available — there is deliberately no predictable fallback, since the anti-poison proofs assume id
  unpredictability. TCB assumption documented in a comment at the extern (ties to #002).
- **Verify (done)**: macOS `lake build` green + `dig` answers; Linux branch syntax-checked with stub
  `<lean/lean.h>`/`<sys/random.h>` headers (`clang -fsyntax-only -D__linux__`).

### Regression rig — **✅ DONE 2026-07-08**
Committed as `test/difftest.sh` + `test/corpus.txt`: cold-starts veri-dns (5300) and a recursive
unbound (5399) on loopback, replays the corpus, and diffs `status` + answer-set (strict on rcode /
TC=1 skipped as TCP-out-of-scope / non-empty answer for stable NOERROR names). Baseline is 12/12.
Injection-based findings (036/004/012/013/009b/037) still need a mock-authoritative `inject.sh`
(NOT yet built) — those poisoning repros can't be driven from the live-network corpus.

---

## Phase 1 — availability (remote unauthenticated DoS)

### 015 — `. NS` permanently bricks resolution — **verified-core — ✅ ROOT CAUSE FIXED 2026-07-08**
The priming-glue fix (`Main.primeRootHints`, 47efe79) stopped the cold-start repro; the root cause
(`stepFindServers` falls back to the SBELT only in the `walkNs = none` arm, so a cached root NS
RRset with *no cached addresses* shadows the SBELT and starves every root-descending resolution in
circular glueless sub-resolution) is now fixed too.
- **Fix (landed) — root-cut-only, NOT the blanket fallback originally sketched**: in
  `stepFindServers`'s rebuild arm, `if glue.isEmpty && mc == 0 then slist := s.resources.sbelt`.
  The original sketch ("zero addresses ⇒ sbelt" at any cut) is **wrong**: an address-less SLIST is
  precisely what triggers the glueless sub-resolution machinery, and for a deeper cut (e.g.
  `example.com NS ns.example.net`, no cached A) replacing it with the sbelt loops forever — the
  root re-referral re-caches the same NS set, `walkNs` re-finds it as the deepest cut, the glue is
  still empty, and the resolver re-queries root until fuel exhausts. The pathology of #015 is
  specific to the **root cut** (`mc = 0`): there the glueless targets circularly need the very
  zone being resolved, and the SBELT is by definition the configured address set for exactly that
  zone. Deeper glueless cuts keep the address-less SLIST and now *bottom out* at the root-cut
  fallback in their sub-runs.
- **Proof impact — S, not M (the `mc = 0` guard is what makes it cheap)**: because the new arm
  fires only at `mc = 0`, its branch guard `currentCloser mc = false` **is** the existing belt
  disjunct's `currentCloser 0 = false` conjunct — so the 3-way SLIST disjunction
  (kept / rebuilt / sbelt) that `stepFindServers_cases`, `loop_findServers_paused_cases`,
  `resolve_paused_inv`, and the `IoResumeSound` driver arms all carry is **unchanged in
  statement**; no model rule, no `GluelessProv` change, `ioResumeLoop_sound` untouched. Work was:
  re-prove `stepFindServers_{goto,frame,cases}` (extra split / `by_cases` on the guard), give
  `stepFindServers_rebuild` a `¬(glue.isEmpty ∧ mc = 0)` hypothesis threaded through the (otherwise
  unused) `_slist` chain, and add one `(try split at h)` at each of the seven structural inversion
  sites (Proof/Resolver, NameTree, NameTreeComplete). Post-referral the arm is unreachable
  (followable referrals give `mc ≥ 1`), so the keystone path needed nothing.
- **Verify (done)**: new mock test `Test/Loop.addresslessRootNsSbeltFallback` (`#guard`): cache
  pre-loaded with an address-less `. NS` set → NOERROR with exactly one upstream exchange
  (pre-fix: SERVFAIL, zero exchanges). Rig 12/12 incl. `. NS`; both capstones axiom-clean.
- **Companion (cheap, impl-only, still open)**: the *answer arm* of `stepAnalyzeResponse` could
  absorb bailiwick-filtered `additional` (as the referral arm does), so a `. NS` refresh re-caches
  the glue too. Now purely an efficiency nicety (fewer sbelt round-trips), no longer availability.

### 017 — FFI drops the real reply on one junk datagram — **below-boundary — ✅ FIXED 2026-07-09**
`veri_dns_exchange` (`ffi/recvfrom.c`) did one `recvmsg` then `close(fd)`. A junk datagram
arriving before the real reply was consumed as *the* reply, forcing a re-query; a junk flood →
SERVFAIL. The model-level junk-drop is proven, but that logic never ran because the C layer
discarded the socket after one packet.
- **Fix (landed)**: `recvmsg` loop on the same fd skipping source-mismatched datagrams, remaining-
  time `SO_RCVTIMEO` re-arm against a monotonic 2 s deadline. Of the two options sketched, the
  "mirror the source-match in C" form was chosen over "return all datagrams" — the latter would
  have changed the `exchangeRaw` extern signature and moved the change above the boundary.
- **Proof impact**: none, as triaged (below boundary — C-only, no Lean diff at all; the #021
  reclassification lesson does not bite here because no `ioResumeLoop`-visible control flow
  changed). The model already assumes exchange yields a source-matched datagram or none; the C
  filter is a strict subset of the proven Lean gate's drop.
- **Verify (done)**: runtime FFI test `exchange-junk-test` (mock server + third-source junk
  socket on loopback): junk-before-reply → real reply returned (red on the pre-fix binary);
  junk-only → `none` at the deadline. Rig 12/12 unaffected. See the 2026-07-09 (4) progress
  entry for the red/green details.

### 006 / 015b — no DNS-over-TCP (RFC 7766 §5 MUST) — **scoped-out, impl-only if pursued**
No TCP listener; `+tcp`/ANY/oversized answers get a kernel RST. Currently declared out of scope.
- **Decision needed**: is TCP in scope? If yes it's a large impl-only addition (listener, length
  framing, TC=1→retry-over-TCP fallback) with no proof obligation beyond re-using the codec. If no,
  document it and make the TC=1 path degrade cleanly (see 008). **Recommend: keep out of scope,
  document, and fix only the TC=1 over-truncation (008-adjacent).**

---

## Phase 2 — egress control (SSRF / attacker-steered egress)

### 036 — off-owner CNAME chased during resolution — **spec-decision — ✅ FIXED 2026-07-09**
`extractCname` (`Resolver.lean:43`) and `cnameToChase` chased the **first type-5 record with no
owner==sname check**, so an answer carrying `attacker.chosen CNAME target.` made veri-dns resolve
the attacker's target. **The model was equally permissive**: `cnameRR` was `find? (rtype == cname)`
with no owner check, and `answerCname`/`trustedCname` restart at `{q with qname := target}` from
that record. Not covered by the client scrub (which filters the returned answer, not the egress) —
a genuine model gap.
- **Fix (landed, impl + model together)**:
  - Impl: `extractCname`/`extractCnameRR` gained an `sname` parameter with a
    `nameEqCI (rrName rr) sname` conjunct; `cnameToChase` passes the **reply's echoed question
    name** (`resp.question[0]?` — self-contained, none-question ⇒ no chase); `prependCnameLink`
    takes the whole `Format` so the pushed chain link uses the same owner-filtered pick.
  - Model: `cnameRR` gained a `(qname : Name)` parameter with a `nameEq r.owner qname` conjunct
    (parameterized, NOT a rule premise — keeps impl/model `find?` first-match lockstep);
    `answerCname`/`trustedCname`/`answer`-hnc use `cnameRR q.qname`. `cacheCname` needed nothing
    (`cnameServed` was already qname-keyed). New `cnameRR_congr` (`nameEq`-equal query names pick
    the same record) bridges the reply's echoed name to the model `q.qname` through the
    `questionMatches` CI gate.
  - Abstract obligation layer: `guardRefined_cname` tightened with a `chase` parameter
    (instantiated with `cnameToChase`) — the referral-guard-leniency pattern; the four
    `obligation_*` defs + five `impl_obligation_*` proofs re-proven. `ResponseConsistent.answerShape`'s
    CNAME disjunct strengthened to the owner-carrying `HasOwnedCname` (RFC 1034 §4.3.2 step 3a).
  - Faithfulness pair (`cnameRR_none_of_extractCname_none` / `cnameRR_some_of_extractCname`) and
    the capstone lockstep lemma (`cname_link_facts`) re-proven with a per-element predicate
    agreement (`cnamePred_agree`), owner canonicity from `parseRaw_name_canonical` and question
    canonicity from `decode_ok_wire_facts` (new `questionFromLabels_canonical`); the none-direction
    packaged as `cnameToChase_none_model`.
- **Proof impact (actual ≈ M)**: NetworkModel/NetworkSemantics/NetworkTraces, Spec+Proof Resolver
  obligations, AnswerTerminal, WorldNetwork, NetworkSim (WorldModels cname conjuncts now at
  `qm.qname`), Refinement (producer wrappers + `αSection_prependCnameLink`), NameTree(+Complete),
  IoResumeSound (chase sites derive the echoed-question canonical triple; `questionMatches_fields`
  now also exports the qname CI-match), ResolveWithIOSound (`prependCnameLink_canonical`).
  `ioResumeLoop_sound` and `serveDatagram_verdict_sound` untouched in statement, axiom-clean.
- **Verify (done)**: mock `Test/Loop.offOwnerCnameNotChased` (`#guard`): off-owner CNAME answer →
  exactly 1 upstream exchange, no query for `victim-internal`, empty scrubbed client answer.
  Legit chases intact: `Test/Loop.treeChased` + rig 12/12 incl. live CNAME chains
  (`www.iana.org`, `www.ietf.org`).

### 021 — no do-not-query egress filter — **✅ DONE 2026-07-08 (was mis-triaged "impl-only")**
The RFC-1918 list at `Server.lean:152` is the *client ACL* (who may query us), not an egress guard.
Nothing stopped the resolver forwarding a sub-query to `127.0.0.1:53` or an RFC-1918 address supplied
as glue / a CNAME-chased target's nameserver → SSRF / amplification / internal-service probing.
- **Fix (landed)**: new `Server.doNotQueryNets` (loopback, 0/8, 10/8, 100.64/10 CGN, 169.254/16
  link-local, 172.16/12, 192.168/16, 240/4-incl-broadcast) + `Server.blockedEgress : BitVec 32 →
  Bool` reusing `AclEntry.matches`. In `ioResumeLoop` the upstream send is now
  `if blockedEgress ipAddr then (log; pure none) else forwardQuery …` — a blocked destination is
  observationally a **lost datagram**, so the existing `upstreamResp = none` continue-path handles
  it (retry on the markQueried SLIST). The priming path is unaffected (root hints are public).
- **Proof impact — CORRECTION: NOT "none".** The model's transport oracle does abstract
  reachability (so semantically a block *is* a `Transit.lost` subset), but the guard was added at the
  **call site**, which the *operational* refinement/soundness proofs pattern-match literally. That
  forced threading a `blockedEgress ipAddr = false` fact (or a case-split) through five files:
  `Proof/NameTree.lean` (`ioResumeLoop_sound` SatisfiesM driver — `if_neg` + `pure_bind`),
  `Proof/NameTreeComplete.lean` (`ioResumeLoop_complete`), `Proof/FreeIO.lean` (10 concrete
  reduction lemmas got a `hegress` hypothesis + `simp only [hegress, Bool.false_eq_true, if_false]`;
  the two "peel-first" lemmas used `rw [if_neg …]`), and the two run-inversion capstones
  `Proof/IoResumeSound.lean` + `Proof/ResolveWithIOSound.lean` (a `by_cases blockedEgress` whose
  blocked arm peels log→randomId→egress-log then hands `cont none` to the IH, exactly the
  `oracle = none` branch). `Test/Loop.lean`'s `referralHandler` mock glue was moved from `10.0.0.53`
  to a public address (the old private glue is now — correctly — dropped). **Lesson: a call-site
  guard is verified-core even when it's a semantic no-op; push such guards below the refinement
  boundary (into `forwardQuery`/FFI) if "impl-only" is the goal.** Build green (282), axiom-clean.
- **Verify (partial)**: rig baseline 12/12 unaffected (public NS). The loopback-glue poisoning repro
  needs `inject.sh` (not yet built); the mock unit test `Test/Loop.delegationChased` now exercises
  the public-glue path and a private-glue address would be dropped.

---

## Phase 3 — cache injection (poisoning of self-cache)

### 004 — answer caching keeps any in-bailiwick subdomain — **spec-decision — ✅ FIXED 2026-07-09**

**Landed (see the 2026-07-09 (3) progress entry for the full recipe + deviations):** impl
`ownerRaws` keyed to the reply's echoed question name (`Resolver.echoedQname`) at both
`stepAnalyzeResponse` answer writes + `Server.replyForResolution` (`clientQname query`); model
`Response.answerOwned` image at the `trustedReply`/`answerCname`/`trustedCname` `hcf0`s;
escape predicates `TrustedReplyCache`/`TrustedCnameCache` sharpened to exact-owner. The original
triage below is kept for reference — its recon was accurate except (a) the model tighten used a
named helper image rather than editing the 18 record-update sites in place, and (b) the impl
filter name had to be the echoed question name (canonicity), not `s.resources.sname`.
Answer-section caching keeps every record whose owner `isAncestorB` the qname (any subdomain),
where unbound strips to `owner == qname` (`iter_scrub.c:584`). Repro: `sub.example.test A 6.6.6.6`
injected on an `example.test` answer is served from cache with 0 upstream. The impl faithfully
conforms to an over-permissive spec (`absorbBailiwick`/`isAncestor` keep).
- **Fix**: for the **answer section** specifically, tighten the keep from `isAncestor bw owner` to
  `nameEq owner qname` (subject records only) — in both `bailiwickRaws` usage at the answer sites
  and the model `absorb` for `answerCname`/`trustedReply`. Referral authority/additional keep their
  bailiwick (glue is legitimately sub-zone).
- **Recon (2026-07-09, sites mapped — start here next session):**
  - **Impl answer-write sites (3)**: `Resolver.lean:400` (cname arm — caches the whole in-bailiwick
    answer section before the chase restart), `Resolver.lean:448` (answer arm), `Server.lean:626`
    (`replyForResolution` client-boundary absorb, keyed `clientQname query`). Referral sites
    (`Resolver.lean:427/430/435`, bw = cut) stay bailiwick. Sketch: new `ownerRaws` filter
    (`nameEqCI (rrName rr) sname`) mirroring `bailiwickRaws` + its three companion lemmas
    (`_subset`, `_owner_*`, `mem_`).
  - **Model**: don't touch `Cache.absorb` (its single `keep := isAncestor bw` has ~50 opaque
    consumers) — tighten the absorbed **image** at the rule sites instead: `trustedReply`'s
    `hcf0` image is already `c.absorb now q.qname { reply.msg with authority := [], additional
    := [] }` (`NetworkSemantics.lean:1458`); make the answer component
    `reply.msg.answer.filter (nameEq ·.owner q.qname)` (a helper, e.g. `answerOwned qname msg`).
    The `{… with authority := [], additional := []}` image appears at **18 sites in
    NetworkSemantics** (trustedReply/trustedCname family + provenance theorems) and **~39 sites
    in NetworkSim + IoResumeSound** (the WriteRefines producers around `NetworkSim.lean:295-397,
    961, 1612-1670` do the real filter-correspondence work).
  - **Bridge**: the machinery is predicate-generic — `filter_filterMap_comm` +
    `αSection_bailiwickRaws_eq` (`Refinement.lean:1295`) reduce to a per-element Bool equality
    (`isAncestorB_eq`); the exact-owner analogue (`nameEqCI owner sname = nameEq ownerN qnameN`
    under `αName` canonicity) is #036's `cnamePred_agree` dependency — already built. Add
    `αSection_ownerRaws_eq` and re-run the producer proofs with the stricter filter.
  - **Behavioral note (decided, record in docs)**: exact-owner drops inline CNAME **chain tails**
    (owner = intermediate target ≠ sname) from the cache that unbound's chain-following scrub
    would keep — veri-dns re-queries the target per hop anyway (post-#036 the chase restarts at
    the target), so the cost is one extra round-trip on inline chains, never a wrong answer.
    Strictly-safer-than-unbound is consistent with `prefer-rfc-real-impl`'s anti-poison intent.
- **Proof impact**: verified-core + spec. The write-path refinement (`αSection_bailiwickRaws_eq`,
  `bailiwickRaws_owner_model`) is stated over the generic keep predicate; specializing the answer
  keep to `owner==qname` re-proves those with a stricter filter (still a filter — the sublist/perm
  lemmas hold). **Est: M** (site count above confirms: one dedicated session, #036-shaped).
- **Verify**: rig injects an in-bailiwick subdomain A on an answer; expect it NOT served from cache
  (unbound returns NXDOMAIN / re-queries). Mock: `Test/Loop` handler answering `example.com` with
  an extra `sub.example.com A 6.6.6.6` answer record → repeat query for `sub.example.com` must go
  upstream (pre-fix: served from cache, 0 exchanges). Keep `treeChased`/live-chain rig cases green
  (chain-tail drop must not break chasing).

### 012 / 013 — negative-cache SOA owner unconstrained — **✅ FIXED 2026-07-09**
`extractSoaNegative` (`Server.lean:70`) took any type-6 record in the authority section with no
owner-vs-qname check, so an NXDOMAIN whose SOA is owned by `poison.attacker.test` was cached and
served for the negative TTL (RFC 2308 §3 says the SOA must be at or above the qname's zone).
unbound scrubs it.
- **Fix (landed, impl + model together — the #036 parameterization recipe, not a rule premise)**:
  - Impl: `extractSoaNegative`/`extractSoaNegTtl` gained a `qname` parameter with an
    `isAncestorB rr.name qname` conjunct inside the `findSome?` element predicate;
    `storeNegativeIfCacheable` passes the **reply's echoed question name** (`clientQname resp`,
    hoisted above it) — which is exactly the stored entry's key, so the stored negative
    authority is owner-bounded by construction. A response whose only SOA is off-owner extracts
    `none` → un-cacheable bare denial (delivered but never cached).
  - Model: `soaNegTtl` gained `(qname : Name)` with an `isAncestor r.owner qname` conjunct
    (per-element — keeps impl/model first-match lockstep); `Cache.absorbNeg` passes `q.qname`.
- **Proof impact — S (under the S-M estimate; the cascade was free)**: every `absorbNeg`
  consumer (NetworkSim ×27, Refinement) treats `soaNegTtl` opaquely, and the run-inversion +
  canon proofs (`storeNegativeIfCacheable_run_inv`, `extractSoaNegative_rrWireCanon`) are
  shape-stable under the extra conjunct — the full build went green on the **first** pass after
  the mechanical signature updates (statements only; zero new proof work). Both capstones
  untouched in statement, axiom-clean.
- **Pin (the "add the ancestor predicate alongside `CacheNegSoaCanon`" half)**: new
  `CacheNegSoaOwner` invariant (`Proof/DeliveredWire.lean` — every stored negative SOA owned at
  or above the entry name) + `extractSoaNegative_owner` / `cacheNegSoaOwner_storeNegative` /
  `replyPath_cacheOut_negSoaOwner` (`Proof/ResolveWithIOSound.lean`): reverting the owner check
  turns these red. Not threaded into the serve-loop invariant bundle (the write path is the sole
  negative producer; thread it alongside the ten if a consumer ever needs it downstream).
- **Verify (done)**: mock `Test/Loop.offOwnerSoaNotNegativelyCached` (`#guard`): off-owner-SOA
  NXDOMAIN delivered, `negatives` empty, repeat query re-queries upstream (pre-fix: served from
  negative cache, 0 exchanges). On-owner negatives intact (`negativeCached`, `treeMissing`); rig
  12/12 incl. live NXDOMAIN. **Residual (low)**: the *first* delivered response still forwards
  the off-owner SOA in its authority section verbatim (unbound: AUTHORITY:0) — scrubbing
  delivered authority touches `deliveredResponse`/verdict statements; NOT folded into the
  Phase 4 batch (2026-07-09 (5)) — now a Phase 6 conformance item if parity is wanted.
  **[Residual ✅ CLOSED 2026-07-09 (9)** — `scrubAuthorityB`; the "touches verdict statements"
  worry was stale, the capstones never pinned authority. See the (9) progress entry.]

---

## Phase 4 — parser hardening (malformed-packet conformance)

All below are **impl-only** (the parser is under the codec TCB, exercised by `decodeRRCanonical`/
`decodeName`); the model consumes already-decoded `Format`, so stricter parsing only *rejects* more
inputs → strict subset, no proof obligation beyond keeping `Message.decode_encode` green on
well-formed inputs. Batch them.

### 009b — compression pointer into the 12-byte header — **impl-only — ✅ FIXED 2026-07-09 (5)**
`decodeNameAux` accepted pointer offsets into the header, fabricating a name from header bytes.
The strictly-backward check and pointer-follow cap (fuel) were already in place pre-review.
- **Fix (landed)**: guard tightened in place to `12 ≤ offset ∧ offset < pos` — shape-neutral to
  every proof (zero proof diff; see the progress entry for why). Tests: `headerPointerRejected`
  + `compressionStillAccepted`.

### 009a — no total-name 255-octet limit — **✅ ALREADY FIXED pre-review**
`decodeName` has enforced `encodedNameLen ≤ 255` (RFC 1035 §2.3.4) since the June diff-test
hardening; the review finding was stale against HEAD. Now pinned by `overlongNameRejected`
(the >255 name survives `encode` — the encoder has no total cap — and is caught on decode).

### 037 — name-bearing RDATA forwarded with compression pointers intact — **✅ FIXED 2026-07-09 (5)**
MX/SRV rdata was forwarded verbatim with compression pointers, corrupting the embedded name
off-path.
- **Fix (landed)**: one unified fixed-prefix-then-name arm in `decodeRRCanonical` (MX 15 /
  SRV 33) decode-and-re-encodes the embedded name with the same rdlength-agreement check as
  NS/CNAME/PTR/SOA; single new `CanonicalRdata.prefixedName` constructor keeps the proof cost
  at one new arm per canonicity theorem (~230 lines, all templated on the SOA arm). Other
  RFC-1035 name-bearing types (MB/MG/MR/MINFO) are obsolete and stay opaque; the resolver
  re-emits them un-cached like any unknown type.
- **Verify (done)**: `mxPointerDecompressed`, `srvPointerDecompressed`, `mxBadRdlenRejected`.

### 010b — undecodable query silently dropped (should FORMERR) — **✅ FIXED 2026-07-09 (5)**
- **Fix (landed)**: `rawDatagramReply` header-decodes the failed datagram: undecodable header /
  QR=1 / non-QUERY opcode → drop (anti-reflection, as before); decodable query header + bad
  body → minimal 12-byte FORMERR echoing the id (unbound parity). Anti-reflection is now
  theorem-pinned (`rawDatagramReply_no_amplification`, `_formerr`, `_headerUndecodable_drops`,
  `_response_drops`) instead of resting on the blanket drop. Capstones untouched — the send was
  already gated on this function, so no `ioResumeLoop`-visible control flow changed.
- **Verify (done)**: `garbageDatagramDropped`, `responseDatagramDropped`,
  `malformedQueryFormerr`; live check: 13-byte bad-label query → 12-byte FORMERR, id echoed;
  2-byte garbage → silence.

---

## Phase 5 — anti-spoof entropy (the flagship)

### 002 — query-ID entropy is untested extern glue — **coverage-gap — ✅ (a)+(b) DONE 2026-07-09 (6)**
The query ID comes from an unverified `@[extern]` FFI; a constant-ID mutation builds green. The
RFC 5452 unpredictability the anti-poison proofs *assume* (`accepts` gates on id) is untested.
- **Fix**: (a) ✅ runtime statistical test **`id-entropy-test`** (`Test/IdEntropy.lean` logic in
  the lib + `Test/IdEntropyMain.lean` entry, the `exchange-junk-test` split): 4096 samples,
  three checks — birthday distinct-count ≥ 3850 (observed ≈ 3968, as theory predicts),
  per-bit balance 2048 ± 192 (6σ), modal adjacent-delta ≤ 64 (counter/fixed-stride detector).
  **Red/green confirmed by C mutation**: constant `0x4242` → fails distinct-count; a
  `ctr += 1` counter → fails bit-balance (and would fail modal-delta if wide-ranged). A
  constant-ID mutation is now red at *runtime* (it still builds green — the gap is below the
  boundary and can only be tested, not proven). (b) ✅ TCB contract documented as a docstring on
  the `randomU16` extern (`Impl/UdpSocket.lean`), stating what the anti-poison theorems are
  proven *relative to* and pointing at the C-side CSPRNG comment + this test. (c) the remaining
  entropy widening folds into item 4 below.

### Item 4 — 0x20 case randomization + per-retry TXID — **✅ COMPLETE 2026-07-09 (8): A/B/C1/C2/D all landed**
The standing anti-spoof hardening. veri-dns's only off-path entropy is 16-bit id + source port; no
0x20, no cookies, and `questionMatches` compares the returned qname **case-insensitively**
(`Server.lean:36`), so even a 0x20-encoded outbound query is unverifiable on return.

**Recon (2026-07-09, full consumer sweep — the original sketch is revised in four load-bearing
ways):**
- **The model `Name` preserves case** (`Net.Name = List ByteArray`, raw label bytes; `nameEq`
  folds only at compare time) and `replyDatagram` copies `out.qname` verbatim — the model's
  honest server *already* echoes byte-exact. Case-sensitivity is expressible with **no change to
  the `Name` abstraction**; the feared capstone-unfolding does not materialize.
- **The #036/#004/#012 echoed-name recipe already made the write path case-robust**: every
  post-acceptance reply filter (`cnameToChase`, `ownerRaws`, `extractSoaNegative`, `scrubAnswerB`)
  keys off the **reply's echoed question name** with `nameEqCI`/`αName_of_nameEqCI` CI bridges to
  the model `q.qname`. A case-randomized echo flows through those bridges unchanged. The only CI
  facts to re-derive are the exports of `questionMatches_fields` (IoResumeSound:1391, consumed at
  ~5 sites incl. `answer_write_WriteRefines_echo`/`cnameToChase_none_model`) and
  `questionMatches_facts` (NameTreeComplete:2909): under a byte-exact gate they re-derive via a
  new `randomizeCase` CI-invariance lemma (`foldNameCase (randomizeCase seed n) = foldNameCase n`)
  + transitivity — **statements and consumers unchanged, only their proofs reroute**.
- **No WorldModels honest-echo conjunct is needed.** `WorldModels` is *conditioned on*
  `acceptResponse … = some resp` (a stricter gate makes the hypothesis fire less — free for
  soundness), and `ioResumeLoop_complete` **splits** on `acceptResponse` rather than proving it
  passes (the rejected arm recurses; completeness is conditional). Honest-echo (real servers copy
  the question verbatim) is a runtime-liveness fact — rig-verified, not proof-consumed.
- **The case seed must be fresh random bits, NOT derived from the txid** (case = f(id) adds zero
  entropy: an attacker guessing the id gets the case for free). One extra `randomId` call = one
  extra monadic step = the #021-style threading through every `run_ioResumeLoop_*` lemma
  (FreeIO: 11 hegress lemmas + `run_round_bind_eq`) and the run-inversion peels
  (IoResumeSound / ResolveWithIOSound / NameTreeComplete `run_randomId_bind_inv` sites) with all
  fuel counts +1 — mechanical but broad; this threading, not the acceptance logic, is the bulk of
  the cost. The pure case-transform itself is a `let`, not a bind — zero steps.
  `randomizeCase` can be byte-level (toggle only `alphabeticByte` bytes): wire-format length
  octets are ≤ 63 and the terminator is 0, both below 'A' = 65, so no parse needed on the
  canonical `sname`. ~~Retransmit determinism holds for free: `randomId` sits above `retryOption`,
  so retransmits reuse the same id *and* case, per server attempt~~ **(superseded by stage D:
  same-(id, case) retransmission is exactly what D removed — `retryOption` is gone and every
  retransmit is a fresh-secrets loop round).**
- **WorldModels/αQuery threading choice (decided)**: instantiate WorldModels with the *canonical*
  `q` and put the case transform **inside the oracle-key literal only**
  (`w.oracle (encode (withCaseSeed (withRandomId q id) cid)) ab`), so `qm = αQuery q` and every
  conjunct stays at the canonical `qm.qname`. Do NOT pass the randomized Format as `q` — that
  moves `qm.qname` to the random-cased name and forces `cnameRR_congr`/`absorb_answerOwned_congr`
  re-instantiations at every conjunct.

- **Fix, staged (A→C2 = stage-1 "0x20"; D = stage-2 TXID):**
  - **A (pure additions, zero risk) — ✅ DONE 2026-07-09 (6)**:
    `DomainName.randomizeCase (seed : UInt16) (n : ByteArray)` (byte-level
    `caseSeedBit`/`toggleCaseByte`, wire-format-safe on valid names) + lemmas
    `foldCaseByte_toggleCaseByte` / `randomizeCase_foldNameCase` / `randomizeCase_nameEqCI` /
    `randomizeCase_size` / `nameEqCI_of_beq` (Proof/NameTree `CICongruence`, reusing the
    `foldCaseByte_toNat` technique). Note: `split_ifs` is not available in this env — nested-if
    goals close with `by_cases` + `simp only [if_pos/if_neg]` + `omega`.
  - **B (model) — ✅ DONE 2026-07-09 (6), zero downstream breakage**: `Net.nameEqCS` +
    `nameEqCS_refl`/`labelEq_of_beq`/`nameEq_of_nameEqCS` (NetworkModel); `accepts` qname
    conjunct `nameEq → nameEqCS`; `OnWire.offPath` hblind third disjunct
    (`∨ nameEqCS out.qname d.qname = false` — widening the constructor's disjunction = more
    attacker datagrams modeled = strictly stronger); `accepts_off_path_false` 3-way;
    `accepts_reply` by `nameEqCS_refl`; `accepts_requires_match` keeps its CI export via the
    weakening + new byte-exact `accepts_requires_qname_cs`. As predicted, every `accepts_reply`
    consumer (WorldNetwork ×5, IoResumeSound ×7, NetworkSim) is construction-direction on the
    reflexive `replyDatagram` form: **the full build was green on the first pass**, both
    capstones axiom-clean. The off-path blindness theorems now state id ∨ port ∨ qname-case.
  - **C1 (impl gate flip) — ✅ DONE 2026-07-09 (6), proof cost ≈ 2 lines**: `questionMatches`
    qname compare `nameEqCI → ==` (byte-exact). Exactly the predicted two CI-export reroutes
    (`questionMatches_facts` NameTreeComplete:2913, `questionMatches_fields`
    IoResumeSound:1410 — both via `nameEqCI_of_beq`); every other consumer is opaque. No fuel
    changes; capstones axiom-clean; **rig 12/12 live** (real servers echo byte-exact — the 0x20
    echo assumption holds on the live corpus); new mock `Test/Loop.caseVaryingEchoRejected`
    (`caseEchoHandler` flips the echoed qname's case: correct id, plausible answer → rejected;
    pre-C1 the CI gate accepted it).
  - **C2 (the entropy — bulk of the work) — ✅ DONE 2026-07-09 (7), see the progress entry for
    the four addenda (the `positive_answer_covered` hidden consumer, the `[0]?`-form
    `Array.getElem?_map` trick, and the per-lemma fuel bumps). The original threading recipe
    below is kept for reference and executed as written:**
    `Server.withCaseSeed`/`withSecrets` (`withSecrets q rid cid := withCaseSeed (withRandomId q
    rid) cid`) are committed (unused). Remaining = wire + thread. **Attempted the wiring, then
    reverted it to keep the two soundness capstones green/axiom-clean** — the threading is larger
    than "one extra step" because of a *continuation-signature* change discovered mid-attempt:
    - **The SatisfiesM drivers are trivial** (NameTree `ioResumeLoop_sound`, NameTreeComplete
      `ioResumeLoop_complete`): one extra `refine SatisfiesM.bind (satisfiesM_true _) ?_; intro
      cid _` peel — verified working. NameTreeComplete's `questionMatches_facts` consumer needs
      `hsentq` (sent question qname = `randomizeCase cid sname`) then
      `nameEqCI_trans hci (randomizeCase_nameEqCI cid _)` — verified working (uses
      `Array.getElem?_map` on the `withCaseSeed` map).
    - **The hard part**: `run_round_bind_eq` + `_none`/`_acceptNone`/`_decodeError` (FreeIO) model
      the round `log; randomId; forwardQuery(withRandomId subQuery₀ rid) >>= k rid` with
      continuation `k : UInt16 → Option Format → Prog β`. Adding the second `randomId` makes the
      round `log; randomId(rid); randomId(cid); forwardQuery(withSecrets subQuery₀ rid cid) >>=
      k rid cid` — **`k` must gain a `cid` arg** (the continuation's `acceptResponse` reads
      `withSecrets subQuery₀ rid cid`), fuel `m+3 → m+4`, oracle literal → `withSecrets`. That
      k-signature change ripples to every `rw [run_round_bind_eq …]` site in the two capstones'
      fuel inductions (IoResumeSound:~3971, ResolveWithIOSound:~2904), each of which then needs
      its `rcases m with _|_|_|m'` to gain a *fourth* successor arm (one more fuel unit for the
      extra `randomId`) and its downstream `acceptResponse (withRandomId subQuery0 …)` matches
      retargeted to `withSecrets`. Plus the ~9 `run_ioResumeLoop_*` reduction lemmas each get one
      extra `run_randomId_bind` peel + the two literal (`horacle`/`haccResp`) updates, and the
      retry lemma's second-round indices shift `idCtr+1/+2 → +2/+3`.
    - Then: restate `questionMatches_fields` (IoResumeSound) with a `nameEqCI sw snameB`
      hypothesis (call sites supply `randomizeCase_nameEqCI`); WorldModels (NetworkSim:104)
      quantifies `cid`, oracle-key + acceptResponse literals → `withSecrets` (keep `qm = αQuery q`
      at the **canonical** `q`); `Main.primeRootHints` gets the second draw (impl-only). Extend
      the #002 TCB docstring (case seed shares the extern contract).
    - **Verify**: the byte-exact gate (C1) already rejects case-mangling — C2 adds the outbound
      *entropy* on top. Regression: a new mock asserting the sent upstream qname's case varies
      with the id stream; rig 12/12 (honest servers echo whatever case we send). This is the one
      remaining item-4 stage that genuinely touches the capstone fuel inductions; est M-L.
  - **D (per-retry TXID) — ✅ DONE 2026-07-09 (8), proof cost ZERO (est was M — see the progress
    entry for the recon that collapsed it)**: the `retryOption_pure`/transport-determinism
    "rework" turned out to be a **deletion**. The loop already retransmits with fresh secrets
    (timeout arm → round recursion → `bestWithAddress` least-tried re-selection → two fresh
    `randomId` draws), and that freshness was already theorem-pinned by the FreeIO retry lemmas
    (second round = `w.ids (idCtr+2)/(idCtr+3)`). The only same-(id, case) retransmission was the
    below-boundary `retryOption` in the IO `exchange` instance — deleted; `exchange` is now
    single-shot, with `Proof/Server.lean`'s dead `retryOption_pure`/`retryOption_all_timeout`
    removed in favour of a doc pointing at the retry-lemma pin. Verify: mock
    `Test/Loop.retransmitFreshSecrets` + runtime `exchange-junk-test` case 3 (single-shot,
    red/green vs a re-added 3-attempt loop).
- **Proof impact**: verified-core. **Est: A+B = S, C1 = S-M, C2 = M-L, D = M. Actual: A+B+C1 as
  estimated, C2 = low-M-L, D = zero** — the whole item landed without ever touching a capstone
  statement.

---

## Phase 6 — protocol conformance + provenance (low)

| # | Finding | Class | Status / fix |
|---|---------|-------|-----------|
| 008 | TC=1 gate on negative caching unbound to any obligation | coverage-gap | **✅ DONE 2026-07-09 (9)** — `storeNegativeIfCacheable_truncated` + `replyForResolution_truncated_cache_unchanged` (TC=1 ⇒ cache byte-identical end-to-end), RFC-linked [1035][2581:2587]; `usingthecache_truncated_not_cached` discharged `via` the positive-half theorem; mock `truncatedReplyNotNegativelyCached` |
| 012/013-residual | first delivered response forwards off-owner SOA in authority (unbound: AUTHORITY:0) | impl-only | **✅ DONE 2026-07-09 (9)** — `scrubAuthorityB` in `deliveredResponse` (capstones never pinned authority, so the "touches verdict statements" worry was stale); pin `deliveredResponse_authority_owned`; mock `deliveredAuthorityScrubbed` |
| 007 / 010a | RD bit not echoed / echo depends on cache state (RFC 1035 §4.1.1) | impl-only (low) | **✅ DONE 2026-07-09 (9)** — `rd := query.header.rd` in `deliveredResponse`; pins `deliveredResponse_rd`/`errorResponse_rd`; mock `rdEchoedUniformly` |
| 001 / 014 | case-fold spec not load-bearing via RFC-generated props (surgical `W` under-fold survives green; correctness rests on hand lemma `foldCaseByte_toNat`) | provenance | **✅ DONE 2026-07-09 (9)** — `namespace_casefold_exact`/`namespace_compare_complete` + instantiations, all five case predicates `via`-discharged, `foldCaseByte_toNat` RFC-linked; the W under-fold mutant confirmed red at `foldCaseByte_casefold_exact` |
| 003 | delivered answer owner case ≠ client's query case (RFC 1035 §2.3.3 SHOULD) | verified-core | **✅ DONE 2026-07-09 (10)** — owner case-normalization in both scrub halves (first-entitled-name `find?` rewrite; client-case at qname, rdata-case on chain hops), pointwise `NamesCorr` lockstep replacing `ReachCorr`, capstone `Sublist` conjunct dropped for the (kept) scrub-exactness equality; pins `scrubAnswer_owner_at_qname` + `αSection_scrubAnswerB_eq`; mock `deliveredOwnerClientCase`; live dig case-echo verified. See the (10) progress entry. |
| 016 | no EDNS0 / OPT ignored | **scoped out** | same stance as TCP (RFC 7766): document; TC=1 degrades cleanly (`truncateUdp_*`, and #008 keeps truncated replies out of the cache). Revisit only if >512-byte answers become a requirement (then do EDNS0 before TCP — cheaper). |
| 009a-dup / rebind | no private-address answer filtering (DNS-rebind) | **scoped out** | unbound's `private-address` is **off by default** — `prefer-rfc-real-impl` says match. An answer filter would also break the byte-exact scrub-exactness equality for a non-RFC hardening. Deployment-level mitigation; revisit only on explicit requirement. |

---

## Suggested execution order (dependency-aware)

1. ✅ **Phase 0** (000 link + rig) — DONE 2026-07-08.
2. ✅ **015 SBELT fallback** (Phase 1) — root cause FIXED 2026-07-08 (root-cut-only guard).
3. ✅ ~~036 + 021 together~~ → **021 DONE 2026-07-08**; **036 DONE 2026-07-09** (owner-checked
   chase, impl + model + full re-proof).
4. ✅ ~~012/013~~ **DONE 2026-07-09** (owner-checked SOA extraction, parameterization recipe,
   proof cost S — cascade free). ✅ ~~004~~ **DONE 2026-07-09** (exact-owner answer keep,
   echoed-name recipe, sharpened trusted-escape pin — cache-injection class now closed).
5. ✅ ~~017~~ **DONE 2026-07-09** (C-only recv loop + `exchange-junk-test` runtime FFI test —
   below-boundary framing held, zero proof impact).
6. ✅ ~~Phase 4 parser batch~~ **DONE 2026-07-09 (5)** (#009a stale/pre-fixed, #009b guard-in-place,
   #037 unified prefixedName arm, #010b FORMERR split with theorem-pinned anti-reflection).
7. ✅ ~~Item 4 / 002~~ (Phase 5) — **COMPLETE 2026-07-09**: #002 done; stages A/B/C1/C2 (the
   full 0x20 half) done; **stage D (per-retry TXID) done 2026-07-09 (8)** — the
   `retryOption_pure` rework collapsed to deleting the below-boundary same-datagram retry
   (proof cost zero; loop-level fresh-secrets retransmission was already in place and pinned).
   **The anti-spoof entropy class is closed.**
8. ✅ ~~Phase 6~~ **DONE 2026-07-09 (9)** — #008 pinned (TC=1 ⇒ cache byte-identical,
   RFC-linked), #007/#010a RD echo, #001/#014 provenance closed (W-mutant now red),
   #012/#013 delivered-authority residual scrubbed; #003 deferred with a mapped M-sized fix
   (0x20 case restore through both scrub halves), #016 + rebind scoped out with rationale.
   **All review findings are now fixed, theorem-pinned, or explicitly scoped/deferred —
   the remediation plan is complete.** Remaining live threads: ~~#003 case restore~~ (**done
   2026-07-09 (10)** — the last deferred item; nothing mapped remains), TCP/EDNS0 if
   requirements change, and the pre-review deferred items 5 (LRU) / 6 (qname-min) tracked
   outside this plan.
9. ✅ **#003** (the one deferred item) — **DONE 2026-07-09 (10)**: owner case-normalization
   through both scrub halves via the pointwise `NamesCorr` lockstep; capstone `Sublist`
   conjunct traded for the scrub-exactness equality (statement change accepted and documented).
   **Every finding in the review is now closed or explicitly scoped out.**

Classification tally: **impl-only** ~~017~~(FFI, done), ~~009a/009b/037/010b~~(done — #037 grew
canonicity-proof arms and #010b policy theorems, but neither touched a capstone statement),
~~007/010a~~ + ~~012/013-residual~~(done 2026-07-09 (9) — both genuinely impl-only: named-builder
redefinitions the run-inversion proofs never see). **verified-core** ~~015~~(done), ~~036~~(done),
~~004~~(done), ~~item-4~~(done) — the coordinated model+impl+re-proof items, none
capstone-*unfolding* like LRU/qname-min (they're the referral-guard-leniency pattern: tighten a
rule, re-prove its consumers; #036, #012/013 and #004 all confirmed the pattern — capstone
statements untouched every time, and item-4's stage D even came in at zero proof diff).
**spec-decisions** ~~036~~/~~004~~ (and ~~012/013~~'s model half) are all done — each resolved by
the standing `prefer-rfc-real-impl` preference: tighten toward unbound. **coverage/provenance**
~~008~~/~~001/014~~(done 2026-07-09 (9)). **Every review class is closed**: availability
(Phase 1, exc. scoped TCP), egress (Phase 2), cache-injection (Phase 3), parser-hardening
(Phase 4), anti-spoof entropy (Phase 5), conformance/provenance (Phase 6), and ~~#003~~
(done 2026-07-09 (10) — verified-core, the one capstone-statement change of the whole
remediation: a dropped conjunct subsumed by a kept equality). Open by choice:
#006/#016 TCP+EDNS0 and the rebind filter (scoped out).

> ⚠️ **Reclassification lesson (from #021):** #021 was tallied "impl-only" but landed as
> *verified-core* — a guard added at the **call site** is pattern-matched by the operational
> soundness/refinement proofs even when it's a semantic no-op (a `Transit.lost` subset). Any
> remaining "impl-only" item that changes control flow the `ioResumeLoop`/`resolveWithIO` inversion
> proofs step through (e.g. **017**'s recv-loop is below the boundary and safe, but a Lean-side
> egress/guard/branch is not) should be expected to touch `FreeIO`/`IoResumeSound`/`ResolveWithIOSound`.
> Put guards **below** the refinement boundary (FFI/`forwardQuery` internals) to keep them cheap.
