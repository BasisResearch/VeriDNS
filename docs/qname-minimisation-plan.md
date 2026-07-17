# QNAME minimisation (deferred item 6) — implementation plan

> **UPDATE 2026-07-17 (findings 051/052/064 — strict mode REVERSED to relaxed):** the
> external review rig showed strict RFC 8020 denial NXDOMAINing *existing* names behind
> ENT-mishandling servers (051/064, HIGH) and probe timeouts burning the whole retry budget
> (052). Locked decisions 2 and 3 below are superseded: the resolver now follows RFC 9156
> §3 step 6d's **non-strict** branch (unbound `qname-minimisation-strict: no`, the default) —
> a minimised-probe NXDOMAIN is consumed and the loop re-probes with the **full** qname
> (`revealed` jumps to `labelCount sname`, so at most one fallback per sname); a probe-round
> timeout (or unusable reply: accept/decode/sanitize failure) likewise falls back via
> `Server.fallbackRevealed`. Only a full-name NXDOMAIN is delivered to the client
> (`run_ioResumeLoop_nxdomain` requires `probeRoundB … = false`); the probe arm's pin is
> `run_ioResumeLoop_probeNxdomainFallsBack`. `storeProbeNegative` is no longer invoked by the
> loop (the probe denial is not believed), and the client-level negative is cached for the
> full qname at the serve boundary as before. The model KEEPS the strict `ancestorDenied`
> rule (sound for cooperative servers); the impl simply no longer exercises it. Mocks:
> `fullNameNxdomainFinal`, `probeNxdomainEntRecovered` (existing-name-behind-ENT-NXDOMAIN
> resolves), `probeTimeoutFallsBackToFull`, `retransmitFreshSecrets` (updated). Flagships
> re-verified: `ioResumeLoop_sent_minimised`/`_sent_egress`/`_sent_fresh`,
> `ioResumeLoop_sound`, `resume_ne_maxIterations` (untouched — the fallback lives at the
> IO-loop layer, not in the pure step functions).
>
> **Same pass, finding 055 (RFC 6891 §6.2.2):** an upstream FORMERR to an OPT-bearing
> sub-query now sets a per-resolution `noEdns` flag on `Resolver.State` (one new loop arm,
> fires at most once) and `buildSubQuery` omits the OPT for the rest of the resolution —
> instead of retry-looping the same EDNS query to SERVFAIL. `SentShape` holds verbatim
> (the stripped query is a `buildSubQuery` image of the flagged state). Mock:
> `formerrRetriesWithoutEdns`. See the ScopeLedger 051/052/064/055 block for the full
> proof-cost map and the per-server-vs-per-resolution residue note.

RFC 9156 (obsoletes 7816): the iterative resolver should reveal to each upstream server only as
much of the client's QNAME as that server needs — one label below the current delegation cut —
instead of the full name. Privacy hardening (root/TLD servers stop seeing full names) plus a
smaller per-hop data exposure.

Triaged against HEAD `35c1454` (post review-remediation closure; #003's owner-normalized scrub
and item-4's 0x20/per-retry-TXID machinery are in place and interact with this plan — see Q3).

## Locked decisions (user, 2026-07-10)

1. **Probe QTYPE = A** (unbound's choice, confirmed from `iterator/iterator.c`:
   `iq->qinfo_out.qtype = LDNS_RR_TYPE_A;` while minimising; the original qtype is restored
   only when minimisation ends and `qinfo_out = qchase`). The final full-name query uses the
   client's original qtype.
2. **Strict mode** (unbound `qname-minimisation-strict: yes` semantics): never fall back to
   sending the full QNAME to a potentially broken server. An NXDOMAIN answering a minimised
   query is **final** — the denial of an ancestor denies the whole subtree (RFC 8020). This is
   the semantically stronger and proof-heavier variant; unbound's own manpage warns it breaks
   badly-configured domains — acceptable here (we are building the reference-correct resolver,
   and the differential rig will show exactly which corpus names diverge from the non-strict
   unbound baseline).
3. **Retry = unbound's choice**: a timed-out minimised query is retransmitted with the **same
   minimised name** (unbound keeps `minimise_count` across timeouts; in strict mode
   minimisation continues regardless of the timeout count). Each retransmission still draws
   fresh `rid`+`cid` per round — the item-4 stage-D machinery — so no RFC 5452 entropy
   regression.
4. **Scope**: main resolution loop only. Glueless NS-address sub-resolutions are their own
   `resolveWithIO` runs and minimise for free; `primeRootHints` queries `.` (already minimal);
   nothing else sends.

---

## Recon facts the design rests on (verified 2026-07-09/10)

1. **`buildSubQuery` is already per-round and state-dependent** (`Impl/Resolver.lean:514`): it
   builds the upstream question from `s.resources.sname` + the original qtype/qclass, and is
   called *inside* each `ioResumeLoop` round (`Impl/Server.lean:583`). Minimisation changes the
   question it picks, not the loop's shape.
2. **FreeIO round lemmas are hypothesis-shaped** over `buildSubQuery` (`Proof/FreeIO.lean:268,
   336, 384, 487, 544…`): changing what the function computes reroutes the *exports* about the
   sent question (currently "sent qname = `randomizeCase cid sname`", original qtype), not the
   lemma skeletons.
3. **The loop already has the guard pattern needed**: `unfollowableDelegationB` sits between
   `acceptResponse` and `afterResume` with an "ignore → continue" arm; its threading through
   FreeIO + both capstones + NameTreeComplete is a proven recipe (the #021 lesson prices it).
4. **Ancestors are byte suffixes.** Names are canonical wire format; the ancestor of `sname`
   with k labels is a *suffix* of the ByteArray, so the minimised name is an `extract` —
   canonicity (`CanonicalName`) is inherited, no re-encoding.
5. **Strict-mode state does NOT need a `State`/`Resources` field.** The minimisation state
   machine (revealed-label count) threads as **new `ioResumeLoop` parameters**, exactly like
   `deadline`/`depth`/`fuel` — universally quantified in every reduction lemma and capstone
   induction already. This avoids the generated-`Resources` surgery and, critically, leaves
   every state literal in the run-inversion proofs untouched (the cost driver behind the
   original "multi-week" estimate). The pure resolver (`Resolver.resolve`, `step*`) never
   sends, so it needs nothing.
6. `rfc/` has neither RFC 9156 nor RFC 8020 — both needed for the coverage layer (8020 backs
   the strict-NXDOMAIN rule).

---

## Design (locked): strict minimisation as a loop-parameter state machine

**Loop state.** `ioResumeLoop` gains `revealed : Nat` (labels of `sname` currently revealed).
Seeded at `resolveWithIO` from the paused state: `revealed₀ := slist.matchCount + 1`.

**Per-round question** (`buildSubQuery` gains the input; the computed name is a **named,
semi-reducible def** — the #004 whnf lesson):
- if `revealed < labels sname`: probe — qname := `minimisedName sname revealed` (the wire
  suffix at `revealed` labels), **qtype := A**, qclass unchanged;
- else: full — qname := `sname`, original qtype (today's question exactly; all existing
  analysis paths apply verbatim).

**Probe-round response handling** (probe-ness is a loop-level boolean, `revealed < labels
sname` — no response inspection needed; the byte-exact acceptance gate already pins the echoed
question to the sent probe):
- **followable referral** → existing `afterResume` referral path; on the new cut `mc'`,
  `revealed := max revealed (mc' + 1)` (never decreases);
- **NXDOMAIN** (acceptable denial shape, SOA owner at/above the probe name — the #012/#013
  owner check applies unchanged since `clientQname resp` = the probe) → **final NXDOMAIN for
  the client query** (RFC 8020: the ancestor does not exist, so no descendant does), delivered
  through the negative-delivery path; negative-cached keyed at the **probe** name (safe: entry
  key = echoed question, exactly what `storeNegativeIfCacheable` already does);
- **anything else** — NOERROR with or without an answer (the probe name may genuinely exist
  with A records), a CNAME at the probe name, an unfollowable referral — →
  `revealed := revealed + 1`, continue. Probe answers are **never delivered, never cached,
  never chased** (a probe CNAME is deliberately not followed: chasing would steer egress off
  the owner-checked #036 path; treating it as an opaque "this name exists, reveal more" is
  both RFC-legal and the anti-poison-safe reading — re-check against the RFC 9156 §2.2 text in
  Q0 and record the reading in the coverage module);
- **timeout** → same round machinery as today (least-tried re-selection); `revealed`
  unchanged, so the retry re-sends the **same** minimised name with fresh secrets (decision 3).

**Reveal schedule.** `+1` label per non-referral probe outcome, with a step cap: after
`maxMinimiseSteps` (10, unbound's `MAX_MINIMISE_COUNT`) increments, set `revealed := labels
sname` (reveal everything). Documented simplification vs unbound's `MINIMISE_ONE_LAB`/
`MINIMISE_MULTIPLE_LABS` multi-label jump schedule — RFC 9156 allows any schedule; the jumps
are a latency optimization, adoptable later impl-only. Progress/termination: `revealed` is
strictly monotone on every non-referral probe outcome and bounded by `labels sname ≤ 127`,
referral outcomes advance `matchCount` (existing strict-progress guard) — fuel bounds
recomputed in Q3 (expect default `fuel := 40` → `64`; fuel is an argument, not a pinned
literal, so capstone statements are unaffected).

**Model: probe parameter + one new rule.**
- Datagram-sending `Resolves` rules gain `(probe : Name) (probeType : QType)` with premise
  `(probe = q.qname ∧ probeType = q.qtype) ∨ ProbeFor probe q.qname cut` (ancestor strictly
  between cut and qname, `probeType = A`); `out := queryDatagram … {q with qname := probe,
  qtype := probeType}`, honest reply = `ServerAnswers` at the probe query. Every existing
  derivation, example walk, and producer instantiates the left disjunct and stays green
  unchanged (the item-4 stage-B widening trick). Referral guards (`inBailiwick q.qname`,
  `descendsBelow`) are stated against the true target and remain satisfiable (cut ⊑ probe ⊑
  qname). The answer/answerCname/negative rules keep the left disjunct **forced** — the model
  half of "only referrals and denials are consumed from probes".
- **New rule `ancestorDenied`** (RFC 8020 / RFC 9156 strict): from an accepted NXDOMAIN reply
  to a probe (denial shape, SOA owned at/above the probe), conclude the NXDOMAIN verdict for
  `q` itself and `absorbNeg` at the probe name. Security posture: forging it needs the same
  id+port+full-question race as any spoof (`accepts` unchanged; probe names have fewer letters,
  so 0x20 entropy on probe rounds is lower — id/port entropy unchanged; state this trade-off in
  architecture.md); blast radius = subtree denial for the negative TTL, which is exactly the
  RFC 8020 semantic and is what "strict" means.

**The flagship theorems (Q4).**
- `ioResumeLoop_sent_minimised`: every sent datagram's qname is a CI-ancestor of the session
  `sname`; a probe round reveals exactly `revealed < labels sname` labels. The resolver
  provably never sends more of the client's name than the current reveal floor.
- `ancestorDenied` grounding: the strict NXDOMAIN delivery is justified by a genuine accepted
  denial at the ancestor (extends `resolves_nxdomain_justified`).

---

## Stages (each lands green; `ioResumeLoop_sound`/`serveDatagram_verdict_sound` statements
untouched except where the plan explicitly says otherwise — acceptance criterion)

### Q0 — RFC text + behaviour pinning + consumer sweep — **S**
- Land `rfc/rfc-9156.txt` + `rfc/rfc-8020.txt`; identify the load-bearing ranges (9156 §2.2
  algorithm & CNAME-at-probe reading, §2.3 QTYPE, §3 ENT breakage; 8020 §2 subtree denial).
- Live-capture unbound with `qname-minimisation-strict: yes` against the rig corpus (probe
  qtypes, reveal schedule, NXDOMAIN finality) to fix parity expectations and the deviation list
  (our +1-with-cap schedule; our no-chase probe-CNAME reading).
- Grep sweep of `questionMatches_fields`/`questionMatches_facts` consumers (the C2
  hidden-consumer lesson) — enumerate every site that today consumes "sent question =
  (sname, original qtype)" before Q3 starts.

### Q1 — pure additions, zero risk (item-4 stage-A shape) — **S**
- `DomainName.minimisedName` (wire-suffix extract by label walk) + lemmas: suffix-of-canonical
  is canonical; `labels (minimisedName s k) = min (labels s) k`; `isAncestorB`;
  `minimisedName_full`; CI-stability under `foldNameCase`.
- Model `ProbeFor` + `isAncestor` glue; `maxMinimiseSteps` constant.
- Committed unused (like `withSecrets` was).

### Q2 — model widening + the `ancestorDenied` rule — **M**
- Probe/probeType parameters through the datagram-sending rule family with the defaulting
  disjunction; all consumers re-elaborate at the left disjunct — expected near-first-pass
  green (stage-B experience).
- `ancestorDenied` rule + its model-side security/grounding theorems (extend
  `resolves_nxdomain_justified`, `resolves_negcache_grounded`; `offpath_cannot_cache` is
  probe-agnostic). This half is genuinely new model surface — budget a full session.

### Q3a — impl flip: probe rounds + reveal state — **L, 1–2 sessions**
- `ioResumeLoop` gains `revealed`; `buildSubQuery` gains the probe input; recursion sites pass
  the updated value (referral/max-bump/+1 rules above).
- New probe-round guard in the `unfollowableDelegationB` slot (non-referral, non-NXDOMAIN probe
  outcomes → reveal+1 + continue) → one new reduction-lemma family arm + one new `rcases` arm
  in `IoResumeSound`, `ResolveWithIOSound`, `NameTreeComplete` (the #021 recipe, fourth reuse).
- FreeIO: `hbuild` shape gains the arg; `withSecrets subQuery₀` oracle-key literals retarget
  (C2 recipe); the retry-lemma family restates cleanly under decision 3 — **same minimised
  name, fresh secrets** (`randomizeCase (cid') (minimisedName sname revealed)`), which is the
  *same shape* as today's pin, just at the probe name.
- `questionMatches_*` exports become the probe/full dichotomy in qname AND qtype; full-round
  consumers (answer/cname/negative arms) recover today's facts from the round's probe-ness
  boolean.
- Completeness: the induction routes probe rounds (tree-consistent servers answer probes with
  referrals/NODATA per `treeLookup` at the probe name); fuel lower bounds recomputed.

### Q3b — strict NXDOMAIN: the new terminal arm — **L, 1–2 sessions**
- Impl: NXDOMAIN-at-probe → final negative delivery (reuses the existing negative finalize
  path with the client question; negative-cache write keyed at the probe name — owner checks
  hold as-is). This is a **new delivery terminal in the loop** → new reduction lemma + new
  terminal arm in both capstone inductions + `HasVerdict` production via `ancestorDenied`.
- The one candidate capstone-statement touch lives here: the verdict produced is at `qm` (the
  client query) via `ancestorDenied`, so the statement should survive; if the negative-cache
  refinement needs a probe-keyed conjunct, prefer a new invariant (the `CacheNegSoaOwner`
  pattern) over widening the statement.
- Mocks red/green per arm as it lands.

### Q4 — flagship pins + coverage + tests + docs — **M**
- `ioResumeLoop_sent_minimised` + `rfc_proves` links in new `Spec/QnameMinimisation.lean`
  (via-discharged against rfc-9156/8020 ranges).
- Mocks (`Test/Loop`): `probeSequenceMinimised` (exchanged qnames: strictly growing
  CI-ancestors, qtype A until full, final = full name + original qtype);
  `probeNodataRevealsMore` (NODATA at probe → same server re-queried with one more label);
  `probeStrictNxdomainFinal` (NXDOMAIN at probe → client gets NXDOMAIN, negative cached at
  probe name, NO full-name query ever sent — the strict pin; a fallback mutant is red);
  `probeAnswerNotDelivered` (plausible A answer at the probe name → ignored, not cached, not
  delivered — the anti-poison pin); `probeCnameNotChased` (CNAME at probe → no query to the
  target); `probeTimeoutSameName` (timeout → retransmit same minimised name, fresh secrets).
- Runtime: `lake build veri-dns` (stale-exe gotcha), rig vs **strict** unbound (flip the rig's
  unbound to `qname-minimisation-strict: yes` for parity; keep a non-strict run to document
  the expected divergences), dig sweep + packet capture confirming reveal floors.
- Update `docs/architecture.md` (loop, 0x20-entropy trade-off on probe rounds, RFC 8020
  posture), `docs/assurance-roadmap.md`, memory.

Revised estimate: **5–8 sessions** (strict adds Q3b and the `ancestorDenied` model surface
relative to the lax variant's 4–6).

---

## Q0 findings (2026-07-10)

### RFC texts landed

`rfc/rfc-9156.txt` (BOM stripped to match repo convention) + `rfc/rfc-8020.txt`. The macro maps
`[num]` → `rfc/rfc-{num}.txt` automatically (`RFC/Check.lean:112`) — no registration needed.

**Load-bearing ranges** (raw file line numbers; the plan's section guesses corrected):
- 9156 `[136:168]` §2 — what minimised queries contain (QNAME one label below the cut, obscured
  QTYPE);
- 9156 `[170:192]` **§2.1** QTYPE Selection (not §2.3 as guessed) — A/AAAA "always good
  candidates"; backs locked decision 1;
- 9156 `[194:207]` §2.2 QNAME Selection — zone-cut probing (NOT the CNAME reading; see below);
- 9156 `[209:270]` §2.3 query-count limitation — "MUST implement a mechanism to limit the
  number of outgoing queries" `[211:215]`; MAX_MINIMISE_COUNT=10 RECOMMENDED `[241:249]`; the
  MINIMISE_ONE_LAB jump schedule `[259:270]` (ours deviates: +1-with-cap);
- 9156 `[284:354]` §3 the algorithm — **(6c) `[342:345]` is the probe-CNAME/answer text** (the
  plan guessed §2.2): "All other NOERROR answers (including NODATA). **Cache this answer.**
  Regardless of the answered RRset type, including CNAMEs, continue…from step 3". Note "cache"
  — our locked no-cache/no-deliver/no-chase reading is a **documented deviation** from the
  letter of (6c). It is not a MUST (algorithm prose, no RFC 2119 keyword), and the "continue,
  don't chase" half agrees with us; only the caching differs, and skipping the cache write is
  the strictly-safer anti-poison posture (probe answers never enter the cache, so they can
  never be served). Record this reading in `Spec/QnameMinimisation.lean` (Q4).
  (6d) `[347:350]` NXDOMAIN + RFC 8020 → "return an NXDOMAIN response to the original query,
  and stop" — the strict rule verbatim. (6e) `[352:354]` timeout "may choose to retry step 6
  with a different ANCESTOR name server" — permits decision 3's same-name retry.
- 9156 `[423:443]` §5 performance — the NXDOMAIN-cut fewer-queries argument;
- 9156 `[445:465]` §6 security — query-storm vector, dampened by §2.3;
- 8020 `[159:217]` §2 Rules — core subtree denial `[161:165]` (SHOULD-level), the
  foo.example/bar.foo.example worked example `[203:217]`; descendant-vs-sibling caveat
  `[213:217]`;
- 8020 `[233:243]` §3.1 — ENT clarification (ENTs answer NODATA, not NXDOMAIN — why NODATA at
  a probe means "reveal more", not "dead");
- 8020 `[245:263]` §3.2 — the RFC 2308 §5 revision (negative cache answers descendant queries)
  — the model justification for `absorbNeg` at the probe name serving the client's deeper qname.

### Consumer sweep — every site consuming "sent question = (sname, original qtype)"

**Definition sites** (change in Q3a):
- `Impl/Resolver.lean:514` `buildSubQuery` — question is
  `#[{qname := s.resources.sname, qtype := qu.qtype (original), qclass}]`; gains the probe input;
- `Impl/Server.lean:583` — the loop's sole call site (`ioResumeLoop` round);
- `Impl/Server.lean:60` `questionMatches` — byte-CI acceptance gate; **unchanged** (it compares
  echoed vs sent, whatever was sent).

**Inversion/transfer lemmas — the exports whose statements change** (probe/full dichotomy):
- `Proof/IoResumeSound.lean:1373` `buildSubQuery_inv` — pins sent qname = `sname` + original
  qtype; consumed at IoResumeSound 2606, 4284, 4428, 4486, 4525, 6745;
- `Proof/IoResumeSound.lean:1394` `questionMatches_fields` — CI-transfer sent→response
  question; consumed at 4285, 4429, 4487, 4527, 6747;
- `Proof/Refinement.lean:1367` `αQuery_buildSubQuery` — **the biggest hidden consumer**: its
  `hqt` hypothesis derives the sub-query's qtype from `lastQuery`'s original qtype and
  concludes `αQuery sub = some q` (the model query). On probe rounds the conclusion must be
  the probe query (qname := probe, qtype := A) — this is exactly where the model widening's
  right disjunct plugs in. Consumed at IoResumeSound 4046, 4978;
- `Proof/NameTreeComplete.lean:2922` `buildSubQuery_question` (private) + `:2909`
  `questionMatches_facts` (private) — consumed at 3087–3088 (completeness induction; the C2
  `positive_answer_covered` lesson lives here);
- `Proof/AnswerTerminal.lean:132` (`αType` transfer), `:202` (`positive_answer_covered` input),
  `:238` `acceptResponse_questionMatches` — qtype-transfer across the gate; the first two
  consume "response qtype = original qtype" and only fire on full rounds after Q3a.

**Shape-agnostic** (compare echoed vs sent, no sname/qtype literal — expected untouched):
- `Proof/Server.lean:228, 276–289` (acceptResponse filter lemmas); `Proof/Cache.lean:258–263`
  (negated gate).

**FreeIO** (hypothesis-shaped over `hbuild`; oracle-key literals retarget, C2 recipe):
13 sites — round lemmas at 268/336/384 (+467 no-build arm at 487), `run_round_bind_eq` family
at 544/607/629/654, retry lemmas at 735–770. All take `hbuild : buildSubQuery state = some
subQuery₀` and key the oracle at `withSecrets subQuery₀ …` — they never inspect the question
fields, so they survive with the extra argument threaded.

**Case-split sites** (the `cases hbuild :` pattern — mechanical):
`ResolveWithIOSound.lean:1964, 2810`; `IoResumeSound.lean:2603, 3918` (+ the per-arm reuses
counted above).

Totals: FreeIO 13, IoResumeSound 15, NameTreeComplete 4, ResolveWithIOSound 2.

### Strict-unbound live capture (homebrew unbound, `qname-minimisation-strict: yes`,
`harden-below-nxdomain: yes`, verbosity 4, loopback port; 2026-07-10)

Observed traces (from `info: sending query:` lines):

1. **`www.cs.ox.ac.uk A`** — probe ladder `uk. A → ac.uk. A → ox.ac.uk. A → cs.ox.ac.uk. A →
   www.cs.ox.ac.uk. A`, one label per round, QTYPE=A throughout. Glueless NS sub-resolutions
   (ja.net, uu.net, surfnet.nl, …) each minimise independently with their own ladders —
   confirms locked decision 4's scope claim for free.
2. **`_dmarc.google.com TXT`** — `google.com. A → _dmarc.google.com. A → _dmarc.google.com.
   TXT`. **New fact: unbound probes the FULL name at QTYPE=A before restoring the original
   qtype** (RFC 9156 §3: step 6 queries CHILD==QNAME at the selected qtype, and only the
   subsequent step-3 pass issues the original query; Table 2's "'a' may be delegated" row).
   **Deviation (ours):** the locked design sends full+original-qtype as soon as
   `revealed = labels sname` — one query cheaper, original QTYPE exposed to the final server
   one round earlier (it would see the full QNAME anyway; QTYPE obscuring is non-normative
   §2.1 "possibly obscure"). Client-visible answers identical, so difftest parity is
   unaffected; only probe-trace comparison shows it. If leaf-side delegation exists, the
   full+original query gets the referral and is re-sent to the child — same resolution result.
3. **`foo.bar.<nonexistent>.com A` (strict NXDOMAIN)** — exactly ONE probe
   (`<nonexistent>.com. A`), NXDOMAIN answered to the client, **no fuller name ever sent** —
   the strict pin, verbatim what Q4's `probeStrictNxdomainFinal` mock asserts.
4. **8020 cache reuse gated on DNSSEC in unbound**: a follow-up query for a *sibling* under
   the denied ancestor was sent upstream (full name) despite `harden-below-nxdomain: yes` —
   unbound applies the RFC 8020 §2 validating-resolver exception (`[175:183]`: MAY restrict
   NXDOMAIN-cut to DNSSEC-validated denials), and this instance has no trust anchor.
   **Deviation (ours):** we take the base SHOULD (deny descendants from the cached unvalidated
   ancestor NXDOMAIN) — *more* aggressive subtree denial than unvalidated unbound, but exactly
   RFC 8020's default posture and consistent with our no-DNSSEC scope. Expect rig divergence
   only in query *counts*, not client-visible rcodes (unbound still answers NXDOMAIN, via
   re-query).
5. **Deep name (34-label ip6.arpa PTR)** — 9 probes: one-label steps early, then +4…+6 label
   jumps, full-name-at-A, then full-name-at-PTR; total ≤ MAX_MINIMISE_COUNT=10. Confirms the
   §2.3 MINIMISE_ONE_LAB/proportional schedule. **Deviation (ours, already documented):**
   +1-per-round with reveal-all after `maxMinimiseSteps = 10` — a 34-label name reveals fully
   at step 10 rather than jumping; more probe rounds saved for pathological names, more
   revealed per late round for deep legitimate ones.

**Parity expectations for Q4's rig run**: strict-unbound comparison should be on client-visible
status/answers (existing difftest form) — expected 100% parity there, including strict-NXDOMAIN
names. Probe-trace comparison (new capture mode) will show exactly deviations 2/4/5 above and
nothing else.

## Q2 landed (2026-07-10)

**Model widening + `ancestorDenied`, build 285 green, axiom-clean** (standard three only on
`resolves_nxdomain_justified` / `ex_strict_ancestor_denied`). Deviations from the plan's sketch,
all cost-driven and behaviour-preserving:

- **`(probe, probeType)` became a single `pq : Query` field** + `hprobe : ProbeQuery pq q`, with
  `ProbeQuery pq q := (qname/qtype/qclass agree) ∨ StrictProbe pq q` and the delegation `cut`
  **existentially closed inside `StrictProbe`** (any cut strictly above the probe witnesses it —
  the root always qualifies, so the content is "proper, non-root ancestor at QTYPE=A"). One
  fewer field per constructor/induction arm; the left disjunct is field-wise (NOT `pq = q`) and
  `rd` is unpinned so `resolves_rd_irrelevant` reconstructs verbatim.
- **Widened rules**: refer, referForget, trustedReferral, rejectSpoof, badResponse,
  unfollowableReferral — wire literals (`hans`/`hacc`/`hwire`) keyed at `pq`; guards
  (`hbail`/`hdesc`/`hunfollow`), cache-write bailiwicks, `hsl`, and recursion stay at `q`.
  **Exception: `trustedReferral.hcut` moved to `pq.qname`** — the `TrustedReferralCache` escape
  packs the accepted wire query, so the anti-poison cut bound must be judged against what was
  sent (left-disjunct producers pass `pq := q` literally, so nothing changed for them).
- **`badResponse.hbad` weakened to `servFail ∨ StrictProbe pq q`** — this is the model image
  Q3a needs for the "non-referral, non-NXDOMAIN probe outcome → reveal+1 + continue" arm
  (9156 §3 (6c) reading: probe answers discarded unconsumed). No other rule covers an
  accepted-but-ignored NOERROR probe reply. answer/trustedReply/answerCname/trustedCname are
  untouched (left disjunct forced by construction).
- **`ancestorDenied` is trusted-shaped** (accepts + Transit from arbitrary origin, no
  `ServerAnswers`/`OnWire`), covering honest AND spoofed strict denials with ONE rule — a
  spoofed strict NXDOMAIN writes the negative cache, which `trustedReply`'s slots (negHit-equal
  image) provably cannot represent. Write slots: `cf0`/`cf` `WriteRefines` over the
  **absorbNeg-only image** `c.absorbNeg now pq reply.msg` (NXDOMAIN answer sections are empty on
  the honest wire; the positive-absorb half is dropped) with `cf0 = c` for uncacheable denials.
  Terminal: `cout = cf`, response `{reply.msg with aa := false}`, empty trace/path.
- **Statement extensions** (both had zero downstream proof consumers, verified):
  `resolves_negcache_grounded` and `resolves_negHitNx_justified` gain `∨ TrustedReplyNxdomain`
  (the ∃-disjunct parenthesized). `resolves_nxdomain_justified`'s statement is UNCHANGED (it
  already carried the escape); its gluelessNs arm gains the third rcases case. All other
  grounding walks (`cout_grounded`, `answer_grounded`, `response_grounded`,
  `cache_in_bailiwick`, `answer_authoritative`, `data_needs_acceptance`, `untruncated`) absorb
  ancestorDenied via trustedReply-shaped arms (absorbNeg_topServed collapses the image reads).
- **`ex_strict_ancestor_denied`** — the right-disjunct walk (probe `MIL. A` for `WWW.FOO.MIL`,
  accepted NXDOMAIN, client NXDOMAIN, no fuller name sent; 8020 worked example transposed).
  Everything else in the repo instantiates the left disjunct, so this is the non-vacuity pin.
  Gotcha: pass `q`/`pq`/`c` EXPLICITLY in the walk — a `_` for `q` gets unified with `pq` by the
  `rfl` fields of `hprobe` before the goal pins it.
- **Consumer sweep actual cost**: NetworkSemantics 12 inductions (arm binder lists via sed on
  the shared binder-prefix patterns — watch the `hmsg`-named variants in time_monotone) + 6
  rd_irrelevant reconstructions (widened rules no longer need `serverAnswers_rd_irrelevant` —
  `hans` is at `pq`, which doesn't mention `q.rd`) + 10 example-walk constructor sites;
  NetworkSim `resolves_cache_congr` (6 arms + 6 calls + new arm via `MatchMaxEquiv.absorbNeg`);
  Refinement 7 `*_hasVerdict/At` producers + WorldNetwork 1 — all at the left disjunct with
  `ProbeQuery.refl q`, signatures unchanged. IoResumeSound/ResolveWithIOSound/FreeIO/
  AnswerTerminal/DeliveredAuthentic: zero edits (hypothesis-threading only). Grounding packs
  quantify the query existentially, so `hfind, q, _, tr, ref, hans` → `pq` was mechanical.

NEXT: Q3a (impl flip: `revealed` loop parameter + `buildSubQuery` probe input + FreeIO retarget).

## Q3a landed (2026-07-10)

**Impl flip complete; build 285 green, zero sorries, capstones axiom-clean; `veri-dns` exe
builds.** Deviations/decisions beyond the plan sketch:

- **Guard shape**: the plan's "non-referral probe outcomes" needed sharpening — the analyzer
  checks the CNAME branch *before* the bizarre branch, so a SERVFAIL reply carrying a chaseable
  CNAME would be chased, not retried. The guard's pass-through set is
  `probePassableB := referralShapedB ∨ retryShapedB` with
  `retryShapedB := cnameToChase.isNone ∧ (servFail ∨ ¬classifiable)` — a CNAME-bearing probe
  reply of ANY rcode is consumed by the guard. `referralShapedB` = the `stepAnalyzeResponse`
  referral branch conditions as one boolean (new defs in Impl/Server.lean).
- **`probeRoundB` includes `0 < revealed`** — makes StrictProbe's non-root requirement
  computational instead of a threaded invariant (seed = matchCount+1 ≥ 1, so dead in practice).
- **Reveal cap folded into the single parameter**: `bumpRevealed` = if `maxMinimiseSteps ≤
  revealed` then labelCount sname else revealed+1 — at most 10 probe increments ever, no second
  step counter. Unfollowable delegations on probe rounds keep today's arm (revealed unchanged) —
  documented deviation from the plan's +1 (monotone, fuel-bounded either way).
- **CNAME restarts re-seed** the floor for the new name (`revealedAfterContinue`: max-bump on
  same sname, `matchCount+1` reseed on sname change) — plan was silent; keeping the old floor
  would over-reveal the chase target.
- **Completeness (NameTreeComplete)**: `StateOK.respMatch` became conditional on
  `probePassableB r = false` — vacuous on probe rounds, recovered on full rounds by per-arm
  shape refutations (`probePassable_false_of_chase/_of_guards/_of_not4b`). This is the
  probe/full dichotomy the plan predicted for `questionMatches_*`, landing at the invariant.
- **Soundness (IoResumeSound)**: `buildSubQuery_inv` concludes at `subQuestion`;
  `subQuestion_full/_probe` specialize per round. Delivery arms derive full-round-ness ONCE via
  `afterResume_finished_probePassable_false` (.finished ⟹ not passable ⟹ guard-false forces
  ¬probeRound). **Probe referrals are justified via `trustedReferral` at `pq`** (hcut at
  pq.qname — Q2's retarget), NOT `refer`: refer's `hdesc` is pinned at `serverBailiwick srv
  q.qname`, not derivable when ServerAnswers is at pq. Consequence: honest probe-round referral
  cache writes fall under the `TrustedReferralCache` escape in grounding theorems. If a future
  pin needs honest-probe-referral grounding, `refer.hdesc` must generalize to an existential
  frontier (model change; out of scope). The driver's consumed-probe arm needs NO model step
  (markQueried-only, Subperm-framed retry arm); `badResponse`'s StrictProbe disjunct remains
  the model image elsewhere.
- **New helper lemmas**: `αQuery_buildSubQuery_probe` (probe αQuery + StrictProbe witness at
  cut := root via `αName_minimisedName` + `isAncestor_drop_ancestor`),
  `trustedReferralProbe_hasVerdictAt` (Refinement), `probeRoundB_facts`, `labelCount_of_αName`,
  `inBailiwick_of_ancestor`.
- **Mocks**: probe ladders scripted into 17 Test/Loop mocks; `retransmitFreshSecrets` now pins
  locked decision 3 verbatim (same minimised name, fresh secrets); `treeChased` shows the
  CNAME-restart re-probe (probe answers never cached). Client-visible answers unchanged.
- **Q3a-temporary behavior**: NXDOMAIN at a probe → guard consumes it (reveal+1); the client
  still gets NXDOMAIN via the eventual full-name query (extra queries, non-strict trace). Q3b
  replaces this with the `ancestorDenied` terminal.

NEXT: Q3b (strict NXDOMAIN terminal), then Q4 (flagship `ioResumeLoop_sent_minimised`, RFC
coverage module with the (6c) no-cache reading, mocks incl. `probeStrictNxdomainFinal`,
rig-vs-strict-unbound).

## Q3b landed (2026-07-10)

**Strict NXDOMAIN terminal complete; build 285 green, zero sorries, capstone statements
untouched, capstones axiom-clean; exe builds; `probeStrictNxdomainFinal` green.** Deviations
and load-bearing findings beyond the plan sketch:

- **`strictDenialB` gained a `cnameToChase.isNone` conjunct** (beyond rcode/tc): RFC 6604 — the
  RCODE refers to the LAST name of the answer's CNAME chain, so an NXDOMAIN carrying a CNAME at
  the probe name asserts the chain *target* is missing, not the probe ancestor. Such replies go
  to the reveal+1 guard instead. Disjoint from `probePassableB` by rcode, so guard/terminal arm
  ordering costs nothing.
- **`storeProbeNegative` is PURE** (unlike the monadic `storeNegativeIfCacheable`) — keyed at
  `subQuery₀.question[0]` (the CLEAN pre-0x20 probe question), expiry from `state.now` (the
  loop's cache clock, in lockstep with the model rule's `now` via `StateModels`' `αTime`
  clause). Keeps `run_ioResumeLoop_strictNxdomain` a log+pure reduction (m+7, probeConsumed's
  shape). No `boundExpiryClasses` on this path: the write never touches positive `records`.
- **Two WriteRefines-equality obstacles forced model amendments** (both `prefer-rfc-real-impl`
  strengthenings, both invisible to every other rule because no other impl path writes
  negatives inside the refinement boundary):
  1. **`absorbNeg` now caps at `maxNegativeTtl := 10800`** (RFC 2308 §5 [515:521], = impl
     `capNegativeTtl`, = BIND `max-ncache-ttl` default). Restated
     `absorbNeg_ttl_is_soa_minimum`/`absorbNeg_nodata_typed` (ttl `min m maxNegativeTtl`);
     zero other consumers.
  2. **`ancestorDenied`'s second slot is `NegWriteRefines`** (new relation): WriteRefines'
     positive clauses + negHit/negHitNx IMPLICATIONS (impl-hit ⟹ model-hit) instead of
     equalities. The impl store REPLACES same-key entries and FIFO-evicts at capacity — vs the
     prepend-only `absorbNeg` image these only SHRINK the served-denial window, which is the
     sound direction (RFC 2308 §5 explicitly allows arbitrary negative-caching limits; a
     fabricated denial is the only unsoundness). Grounding walks consume the implication
     directly (`have hn := hcf.2.2.1 … hn` replaces the old `rw`). Driver instantiates
     `cf := αCache cout` so the conclusion's `CacheRefines (αCache cout) coutM` is refl.
- **WorldModels' SPOOFED disjunct gained an unconditional
  `αSection resp.authority = reply.msg.authority`** (was referral-guarded): the `absorbNeg`
  image reads the reply's SOA, so the negative TTL must line up between the impl bytes and the
  model datagram. WorldModels is an assumed environment relation (never constructed in-repo);
  this is the same α-fidelity the honest disjunct already carried. ~10 destructure sites
  gained a component slot.
- **`αRData` gained the type-6 (SOA) branch** (`αSoa`) — SOA records previously did NOT
  abstract, so WorldModels' authority-validity conjuncts excluded every realistic negative
  response and the terminal's write case would have been vacuous. Fallout: `αRData_rtype`,
  NS/A rdata inversions, 2 GlueConnector spots.
- **The two driver bricks**: `soaNegTtl_extractSoaNegative` (first-match SOA lockstep,
  pointwise via `isAncestorB_eq` + `computeNegativeTtl_eq_min`; the impl extraction and model
  `soaNegTtl` agree as `Option.map (·.1.toNat)`) and `storeProbeNegative_negWriteRefines`
  (no-SOA path = refl chain through `MatchMaxEquiv`; write path = single-prepend lemma +
  `capNegativeTtl_toNat = min · 10800` + `uint32_add_ttl_toNat` under `hclock`).
- **Completeness (NameTreeComplete)**: new arm via `nodeAt_prefix_none` +
  `nodeAtName_none_of_minimisedName_none` — the RFC 8020 fact AT THE TREE (dead ancestor ⟹
  dead subtree, since `nodeAt` walks root-first and the probe's reversed label list is a
  prefix of sname's). Delivered NXDOMAIN justified by `answersFromTree_of_terminal` at
  `treeLookup = .nameError`; the probe-keyed entry keeps `NegativesFaithful` via
  `nameErrorDeserved` CI-transferred through the byte-exact gate + 0x20 fold back to the
  clean probe name (`probeAbsent_of_strictDenial`, public in NameTree.lean).
- **Tree-level soundness (NameTree.lean ShimSound driver)**: same absence transfer;
  `cacheAgrees_storeProbeNegative`.
- **FreeIO threading**: full-round lemmas took a third `if_neg (by simp [hprobe])` (same
  tactic discharges both new ifs); `probeConsumed` gained `hstrictF`; `continue` gained
  `hsguard`; bizarre lemmas derive `strictDenialB = false` from their own shape
  (`strictDenialB_false_of_bizarre`: NXDOMAIN is classifiable and not SERVFAIL).
- **Mock**: `probeStrictNxdomainFinal` (Test/Loop) — 5-label name under a missing ancestor:
  exactly 3 exchanges (`size == 3` IS the fallback-mutant detector; pre-Q3b behaviour used 5),
  client NXDOMAIN, and a follow-up query for the probe name itself served from the negative
  cache with zero traffic. NOTE: the impl does NOT do descendant negative lookup (RFC 8020
  §3.2's "answer descendant queries from the ancestor NXDOMAIN" read-side is not implemented —
  only exact-name hits); a SIBLING under the denied ancestor re-probes and re-terminates.
  Candidate future impl item (unbound's `harden-below-nxdomain` read side).
- Heavy soundness sweep (bricks + driver arm + ResolveWithIOSound sites) done by one
  subagent from a detailed brief (agent a60c3fb8625482c5d), as in Q3a — worked again.

NEXT: Q4 — flagship `ioResumeLoop_sent_minimised`, `Spec/QnameMinimisation.lean` coverage
(incl. the (6c) no-cache deviation reading and the RFC 6604 strictDenialB reading), remaining
mocks (`probeAnswerNotDelivered`, `probeCnameNotChased`, `probeSequenceMinimised`,
`probeNodataRevealsMore`), rig vs strict unbound + packet capture.

## Q4 landed (2026-07-10) — item 6 COMPLETE

**Flagship + coverage + mocks + rig; build 287 green, exe builds, flagship axiom-clean
(standard three), capstone statements untouched.**

- **Flagship (`Proof/SentMinimised.lean`, in `lake build` via `VeriDNS.lean`).** The plan's
  run-relative sketch was upgraded to a *program-tree* statement: new inductive
  `AllSent P : Prog α → Prop` (every `.exchange` reachable under ANY sequence of environment
  responses satisfies `P`) — no `World`, no oracle hypotheses, strictly stronger than any
  per-run form, and the timeout/spoof/glueless/blocked-egress arms are covered by the same
  `∀ r` quantification instead of per-arm oracle case analysis. Three layers:
  `ioResumeLoop_sent_shape` (the closure: the ONLY egress shape is
  `encode (withSecrets (buildSubQuery st revealed) rid cid)` at some loop state),
  `sent_question_minimised` (session-anchored: single question, `isAncestorB qname sname`,
  probe ⟹ qtype=A ∧ exactly `min (labels sname) revealed = revealed` labels via the Q1
  lemmas, full ⟹ `nameEqCI qname sname` + original qtype), and the headline
  `ioResumeLoop_sent_minimised` (mono-composition) + `resolveWithIO_sent_minimised` wrapper.
  Proof cost was LOW (~370 lines, one session): the induction is on `depth + fuel ≤ n` with
  a `dsimp only [letFun]` normalization (the do-elaborator's `__do_jp` join points must be
  inlined before `split` can see the ifs/matches — the blocked-egress and probe-guard arms
  then reduce definitionally). ⚠ `rw [Server.ioResumeLoop]` picks a CONDITIONAL equation
  lemma (leaving an unprovable pattern-refutation side goal and silently deleting the
  glueless arm) — use `rw [Server.ioResumeLoop.eq_def]`. The reveal *schedule* is
  deliberately NOT in the per-datagram predicate (an ∃-bound floor can't pin it); the ladder
  mocks pin it end-to-end. New reusable lemma: `isAncestorB_congr_left` (CI-congruence in
  the descendant argument, mirror of `isAncestorB_congr`).
- **Coverage (`Spec/QnameMinimisation.lean`).** `check_rfc_doc`/`rfc_proves`(+`via`) over the
  Q0 load-bearing ranges of 9156+8020; module docstring records the five documented
  deviations ((6c) no-cache; +1-with-cap schedule; early qtype restore; 8020 base-SHOULD
  sans DNSSEC gate; §3.2 read side unimplemented) and the RFC 6604 reading, pinned by new
  small theorems `strict_denial_excludes_cname`, `nodata_not_strict_denial`,
  `reveal_cap_after_max`/`reveal_step_below_cap`/`max_minimise_count_recommended`,
  `probe_qtype_is_A`. (6c)/(6d)/(6e) discharge to the FreeIO reductions
  (`run_ioResumeLoop_probeConsumed`/`_strictNxdomain`/`_timeout`); 8020 §2 + the worked
  example discharge to `storeProbeNegative_negWriteRefines`, `probeAbsent_of_strictDenial`,
  and `ex_strict_ancestor_denied`.
- **Mocks (Test/Loop, all green).** `probeSequenceMinimised` (the ladder: 3 exchanges,
  strictly growing CI-ancestors, qtype A on probes / 16 restored on the full round — new
  `txt.example.com` TXT node in `theTree`), `probeNodataRevealsMore` (8020 §3.1),
  `probeAnswerNotDelivered` (evil on-owner A at the probe: not delivered AND a follow-up
  query goes back upstream — not cached), `probeCnameNotChased` (on-owner CNAME bait at the
  probe: no exchanged datagram ever carries the attacker name). NOTE the harness gotcha: an
  EMPTY script records nothing in `exchanged` (the `[] => pure none` arm doesn't push), so
  "went upstream" must be asserted with a scripted follow-up, not an empty one.
- **Rig (live network, 2026-07-10).** Baseline (non-strict unbound): 12/12 corpus parity.
  **Strict unbound** (`qname-minimisation: yes` + `-strict: yes` + `harden-below-nxdomain:
  yes`): **12/12 — 100% client-visible parity**, zero diffs, exactly the Q0 prediction
  (deviations 2/4/5 live only in probe traces/query counts). Live traces:
  `www.cs.ox.ac.uk A` → NOERROR with one probe-consumed round visible
  (`probe outcome (rcode=0) consumed … revealing more`); `foo.bar.<random>.com A` → client
  NXDOMAIN after only 2 exchanges with the strict line
  (`strict NXDOMAIN at probe ancestor: denying subtree … (RFC 8020)`) + `negative cache
  store (ttl 900)` and ZERO further queries for that sname — the walk cut at the `.com`
  ancestor; `_dmarc.google.com TXT` → NOERROR in 2 exchanges off the warm `.com` referral.
  0x20 case entropy visible in the sent server names, as designed.
- **Docs**: architecture.md gained the flagship+coverage bullets; assurance-roadmap.md gained
  the 2026-07-10 addendum (egress side now pinned; documented residuals: 8020 §3.2 read side,
  probe-round 0x20 entropy).

**Item 6 is complete.** Actual cost: 6 sessions (Q0, Q1, Q2, Q3a, Q3b, Q4) — inside the 5–8
estimate. Candidate follow-ups (not planned): RFC 8020 §3.2 read side (descendant negative
lookup; unbound `harden-below-nxdomain`), MINIMISE_ONE_LAB-style multi-label jumps
(impl-only), underscore-label grouping (9156 §2.3 MAY).

## Risk register

| Risk | Mitigation |
|---|---|
| New terminal arm (strict NXDOMAIN) is the largest single item — a new delivery path through both capstones | isolated as Q3b with its own session budget; model rule proven first (Q2) so the impl arm has its verdict producer ready |
| Loop-level guards are verified-core (#021) | priced in; mirror `unfollowableDelegationB`; probe-ness is a loop boolean, not response inspection |
| Inlined compound name in state literals → whnf timeouts (#004) | `minimisedName` and the per-round question are named semi-reducible defs from day one |
| Retry pin shape | decision 3 keeps it same-shape (same name, fresh secrets) — cheaper than the lax variant's probe/full retry split |
| qtype-A probes double the `questionMatches` dichotomy (qname AND qtype) | Q0 consumer sweep before Q3; exports carry one probe-ness disjunction, not two |
| NameTreeComplete hidden consumers (the C2 `positive_answer_covered` experience) | Q0 sweep; completeness fuel bounds recomputed explicitly |
| Strict mode breaks real-world names (unbound manpage warning) | rig runs against strict unbound for parity; divergence list documented, not silently absorbed |
| Model widening breaks `ex_*` walks | defaulting disjunct keeps `probe := q.qname` instances definitionally available |
