# VeriDNS review — interim summary (upstream 26b5849)

**Status: PAUSED mid-run, stopped by hand during hunt Round 7.** Not a dry
terminus — the loop was still producing findings. Nothing is lost: all finding
files are on disk, tracked source (`VeriDNS/`, `ffi/`) is clean, and the workflow
can resume from cache (`resumeFromRunId: wf_bc6ca418-b55`). This file is an
interim deliverable; the canonical `REPORT.md` synthesis step did **not** run yet.

## What this run is

The prior review (branch `review/bug-hunt`, commit `8e4e16d`) found ~53 issues.
Upstream answered with a single large commit **`26b5849`** whose
`docs/remediation-plan.md` claims *"every review finding is now fixed,
theorem-pinned, or scoped out with rationale."* This run has two jobs:

- **(A) Test that claim** — re-run each prior finding's reproduction on a live rig
  and check whether it still reproduces vs unbound.
- **(B) Hunt the new surface** the prior review never saw — DNS-over-TCP, EDNS0,
  QNAME-minimisation, and the new adequacy/completeness capstones.

Method unchanged from the harness: every claim bottoms out in an observable,
**differential** experiment (veri-dns vs unbound over a controlled root→TLD→leaf
hierarchy), plus mutation testing (revert/break a definition, read the pair
*does the proof still pass? does the server misbehave?*).

## Bottom line so far

1. **The verification is substantially load-bearing on this upstream — more so
   than the prior review found.** Of ~19 mutations aimed at the new code and the
   remediation fixes, **~14 broke a real theorem statement** (`proof-caught-semantic`):
   TCP big-endian framing, QNAME-minimisation privacy (even a 1-label leak), the
   delivered error rcode (SERVFAIL/REFUSED/FORMERR all pinned), the cache-hit
   answer path, the `finalizeAnswer` TC bit, and — decisively — the **015 DoS fix
   is theorem-pinned** (`impl_algorithm_sbelt_fallback`), overturning an earlier
   suspicion that it rested only on a mock test.

2. **The remediation is real where it engaged, but the plan's completeness claim
   is false.** Everything upstream *triaged* is genuinely fixed, and most fixes are
   pinned by a theorem that goes red if reverted. But ~20 prior findings — almost
   all from the Round 5–8 "long tail" the plan never mentions — **still reproduce
   verbatim on the rig**.

3. **Two remediation fixes are behaviorally present but pinned by nothing.** The
   do-not-query egress filter (021) and the query-ID entropy (002) can each be
   neutered with the proofs staying fully green. An unpinned fix can silently
   regress — that is itself a finding (062, and the mask off-by-one 060).

4. **The residual bugs cluster in three places:** (a) **EDNS0 message sizing** —
   the single `clientCap_le` theorem pins only an upper bound, so the cap is wrong
   in all three directions (049/050/063); (b) **availability/liveness** — soundness
   proofs cannot see a SERVFAIL/hang/slow-loris, and the new TCP path shipped with
   the same gap (057/067/058); (c) **the `sendTo = pure ()` modelling gap** — the
   `Prog` capstones ignore the actual bytes sent, so several delivery mutations are
   caught only by `#eval` conformance tests, not by theorems.

**Verdict for a truster:** a VeriDNS answer, when given, is well-defended against
the poisoning/injection class — and on this upstream that defense is now largely
theorem-backed, including several fixes the prior review flagged as unpinned. You
still may **not** infer availability or RFC-completeness: there is a confirmed
liveness cluster (now including DNS-over-TCP), an EDNS0 sizing spec that is broken
in three directions, and two review-remediation fixes that no theorem holds.

## (A) Remediation scorecard

Re-tested on the renumbered rig, restarting both resolvers before each
differential. "Pinned" = reverting the fix turns the build red.

### Genuinely fixed — and theorem-pinned (reverting breaks a proof)
`001/014` case-fold (W under-fold now dies at `namespace_casefold_exact`) ·
`004` answer-subdomain cache injection (`ownerRaws`) · `008` TC negative-cache
gate · `012/013` negative-cache SOA owner (+ `scrubAuthorityB`) · **`015` the
`. NS` DoS** (`impl_algorithm_sbelt_fallback`) · `025` the ex-orphan capstone is
now consumed · `036` off-owner CNAME egress (owner check).

### Genuinely fixed on the rig, but the FIX is UNPINNED (can silently regress)
`021` do-not-query egress filter — neutering `blockedEgress` builds fully green
(new finding **062**; mask off-by-one **060**) · `002` query-ID entropy —
constant-ID builds green, guarded only by the new `id-entropy-test`.

### Fixed but code-only / partial
`006/015b` DNS-over-TCP genuinely shipped **both directions** (plan's "scoped out"
row is stale) · `009b`,`010b`,`029` parser hardening fixed · `016` EDNS0 partial
(upstream advertise works; client OPT echo + BADVERS missing) · `031` upstream cap
bumped 512→1232 but `MSG_TRUNC` still ignored · `018` authority scrub added,
additional still leaks · `037` name-compression fixed, A/AAAA rdata-length still
unvalidated · `022` QNAME-minimisation shipped and pinned.

### Still reproduces verbatim (the long tail the plan is silent on)
`017` FFI junk-datagram from the legit source still drops the reply · `019`
CNAME-conduit injection · `023` opcode 3–7 black-holed (no NOTIMP) · `024`
negcache aa-blindness (spec *forbids* the hardening) · `030` `acceptResponse`
ignores QR/OPCODE (weaponizable poisoning primitive) · `032` client TC bit
reflected · `033` multi-question FORMERR over-echo · `034` phantom-value TTL ·
`035` multi-homed failover broken · `038` promiscuous NS subtree redirect · `039`
CNAME-target NXDOMAIN poisons all types · `040` AA=1 referral not followed · `041`
bare empty NOERROR accepted no-retry · `042` non-empty-sections query answered vs
FORMERR · `044a/b` delivered TC unconstrained / meta-QTYPE recursed · `045` lame
first-server spurious NODATA for an existing name · `047` out-of-bailiwick
ADDITIONAL delivered verbatim.

## (B) New findings from this run (049–069)

All build green with the proofs passing unless noted; all confirmed differentially
vs unbound. Finding-file numbers collide (parallel agents) — three distinct `060`s.

**Severity axis.** For `impl-bug`, severity = impact on the *running* server today.
For `bad-spec`/`coverage-gap` where the shipped binary is actually correct and the
mutation only shows *no theorem pins it*, severity reflects **regression risk + what
is exposed if it regresses**, not current breakage — these are marked `(spec)` and a
"medium (spec)" is not "broken today." Severities are this review's assessment.

**Ranked digest:**
- **High:** 053, 060c (client-inducible resource-exhaustion DoS) · 051, 064
  (wrong answer — existing names denied) · 069 (amplification + egress to the real
  roots) · 061 (spec — the new liveness proofs are vacuous; the audit's central finding).
- **Medium:** 055, 066 (EDNS interop / dropped queries) · 057, 067 (TCP slow-loris DoS)
  · 059, 060a, 068 (resolution/correctness) · 052 (QNAME-min no fallback) · 062 (spec —
  the SSRF egress filter is pinned by nothing).
- **Low:** 049, 050, 063 (EDNS sizing) · 056, 058, 065 (RFC conformance) · 054, 060b
  (spec — currently benign, unpinned).

| # | Finding | Class | Severity |
|---|---------|-------|----------|
| 049 | non-EDNS UDP cap floor (512) unpinned — legacy client gets a 1194B TC=0 answer | bad-spec | low |
| 050 | EDNS small advertised buffer ignored (over-large reply) | bad-spec | low |
| 051 | QNAME-min strict NXDOMAIN, no full-name fallback | impl-bug | high |
| 052 | QNAME-min probe timeout, no fallback (re-sends until budget expires) | coverage-gap | medium |
| 053 | 0x20-cased RDATA names defeat cache dedup → client-inducible RRset duplication | impl-bug | high |
| 054 | TCP send payload unpinned — proofs green while the wire frame echoes the query | bad-spec | low (spec) |
| 055 | no EDNS fallback: FORMERR to an OPT query loops to SERVFAIL | impl-bug | medium |
| 056 | multiple OPT RRs not rejected (RFC 6891 §6.1.1 FORMERR) | bad-spec | low |
| 057 | TCP serve loop serial/single-shot — slow-loris DoS | impl-bug | medium |
| 058 | TCP no connection reuse — RST/EOF on pipelined 2nd query (RFC 7766) | impl-bug | low |
| 059 | DS query at a zone cut routed to the child zone when cached | impl-bug | medium |
| 060a | DNAME (type 39) stripped by the CNAME-only delivery scrub (RFC 6672) | impl-bug | medium |
| 060b | egress do-not-query mask off-by-one un-blocks the upper half of every range | coverage-gap | low (spec) |
| 060c | large-RRset reply assembly is ≈cubic — CPU-spin DoS at ~24KB/300 records | impl-bug | high |
| 061 | **frozen-clock liveness capstones are vacuous** — deadline test unseeable in the model | bad-spec | high (spec) |
| 062 | egress filter (021's remediation) unpinned — deleting `blockedEgress` builds green | coverage-gap | medium (spec) |
| 063 | EDNS large advertised buffer ignored → over-truncation of an 802B answer | bad-spec | low |
| 064 | QNAME-min RFC 8020 strict denial NXDOMAINs an existing name | impl-bug | high |
| 065 | EDNS version not checked — no BADVERS for version>0 (RFC 6891) | coverage-gap | low |
| 066 | inbound UDP recv capped at 512B — drops valid EDNS queries >512B as FORMERR | coverage-gap | medium |
| 067 | TCP slow-loris confirmed differentially (serial accept + 3s blocking read) | impl-bug | medium |
| 068 | qtype-blind answer acceptance: wrong-type same-owner RR delivered vs NODATA | coverage-gap | medium |
| 069 | QCLASS never validated — non-IN class recursed to real roots, ~1:80 amplification | coverage-gap | high |

**Two headline items among the new set:**
- **061 (frozen-clock vacuity)** is the sharpest spec finding: the new
  adequacy/liveness capstones run against a frozen `Prog` clock, so any per-round
  deadline test is decidably false *in the model* — the proofs structurally cannot
  witness a timeout, and a SERVFAIL-on-deadline mutant stays green. This is exactly
  the "unreasonable premise that makes the theorem miss real workloads" the review
  brief asked us to hunt.
- **The `clientCap` trio (049/050/063)** shows one under-constrained theorem
  (`clientCap_le`, a one-sided upper bound) leaving the EDNS0 response size wrong in
  three independent directions — the weakest single spec in the new code.

## Positive load-bearing results (mutation broke a real theorem statement)

TCP framing byte-order (incl. >65535 oversize) · QNAME-min privacy incl. a
single-label off-by-one leak · delivered error rcode = SERVFAIL/REFUSED/FORMERR
(`replyForResolution_run_err_inv`, `hygiene_refused`) · cache-hit answer path can't
servfail · `finalizeAnswer` TC bit (used 6× in the completeness capstone) · warm-
cache network-servfail guard (`run_resolveWithIO_networkAnswer`) · **the 015 sbelt
fallback** · ANY-scrub qtype exclusion · empty-send caught by conformance vectors.

Axiom audit: **clean** — zero `sorry`/`admit`/bespoke `axiom`/`unsafe`; all 37
capstones reduce to `propext`/`Classical.choice`/`Quot.sound`.

## Refuted (kept for honesty — the method working)
Apex-ANY SOA-only (both resolvers agree, cold) · ANY-over-TCP SOA-only (same) ·
per-IP rate limiter inert (unbound also does none) · RD=0 → REFUSED (unbound too,
anti-snooping). Each was a warm-vs-cold or trust-model artifact, not a bug.

## Method notes / caveats
- **Rig renumbered 10.53.0.0/24 → 203.0.113.0/24.** Upstream's new `doNotQueryNets`
  egress filter blocks 10/8, so the old rig addresses are unreachable to veri-dns.
  TEST-NET-3 is unfiltered, keeping the shipped filter **active** (not bypassed via
  `VERI_DNS_ALLOW_LOOPBACK_EGRESS`, which would mask real egress bugs). The
  client/attacker had to move to 192.168.53.99 — veri-dns's ingress ACL is a subset
  of its egress filter, so no single subnet can be both an allowed client and a
  queryable target.
- **Run interrupted three times** (a session exit that killed the VM, a
  StructuredOutput schema fault, a manual stop). Each resumed losslessly from cache;
  the regression phase was independently re-run on the rebuilt rig and **replicated
  its verdicts**, which strengthens rather than duplicates them.
- **Not a dry terminus.** Stopped by hand mid-Round-7. The finder re-discovery rate
  was climbing (Round 6–7 candidates increasingly collapsed to known findings), so
  the meaningful space is largely covered, but the loop is formally unfinished. To
  resume: bring the rig up (`review/env/up.sh`) then
  `Workflow({scriptPath:"review/workflows/regression-and-hunt.mjs", resumeFromRunId:"wf_bc6ca418-b55"})`.
- **`REPORT.md` (the canonical synthesis) was not generated** — the run stopped
  before the Report phase. This interim file stands in until a resumed run produces it.
