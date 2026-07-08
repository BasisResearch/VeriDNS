# 020 — QTYPE=ANY client-delivery scrub bypass leaks foreign answer records (coverage-gap)

## Classification
coverage-gap — build stays GREEN, resolver is observably wrong, and no theorem's
statement constrains `replyForResolution`'s delivered answer for the star case.

## Mutation (M-scrub-callsite-bypass-star)
`VeriDNS/Impl/Server.lean:469`, in `replyForResolution`:

```
-    let scrubbed := Resolver.scrubAnswerB (RR := ResourceRecord) qname resp.answer
+    let scrubbed := if (query.question[0]?).any (fun qu => qu.qtype == 255) then resp.answer else Resolver.scrubAnswerB (RR := ResourceRecord) qname resp.answer
```

For QTYPE=ANY (255) the client-delivery scrub is skipped; the raw upstream
`resp.answer` (which `finalizeAnswer` passes through un-filtered — it only
prepends the CNAME chain, `Resolver.lean:172`) is delivered verbatim. Typed
(IN-class) queries still go through `scrubAnswerB`.

## Build result: GREEN
`lake build` → `Build completed successfully (279 jobs).` No proof broke.

## Why nothing caught it
`scrubAnswerB` (the delivery guard) drops answer records whose owner is not
CNAME-reachable from `qname` (`Impl/AnswerScrub.lean:47`). The in-loop
`bailiwickRaws` filters only what gets **cached** (`Resolver.lean:378,426`), not
the delivered `resp.answer`; `finalizeAnswer` does not filter either. So the
delivery scrub is the sole guard on client-facing answer records, and no
semantic theorem is composed with `replyForResolution`'s output:

- `IoResumeSound.ioResumeLoop_sound` (`Proof/IoResumeSound.lean:2810`) is the
  only oracle-free network-agreement theorem, but its premise
  `q.qtype ≠ QType.star` (:2846) discharges exactly this case vacuously — the
  star branch is never handled, so even a lockstep repair could not make it
  catch this. It is also orphaned: imported only by `VeriDNS.lean:81`, applied
  by no theorem.
- The published `resolveWithIO_sound` carries no star premise but does not cover
  `replyForResolution`'s delivery step.

This is the same composition gap as the unconditional scrub-bypass mutant; the
star scoping additionally shows the `IoResume` star restriction buys nothing.

## Reproduction (controlled rig)
Rogue authoritative leaf `penn-testing/_vmdns/anyinject.py` bound at
10.53.0.12:53 injects an occluded foreign-owner record into
`example.test`'s answer for qtype A(1) and ANY(255):

```
example.test.      3600 IN A 10.53.0.100   (honest)
sub.example.test.  3600 IN A 6.6.6.6        (foreign owner; not qname, not CNAME-reachable)
```

dig sends ANY over TCP by default (RFC 8482 era) and veri-dns is UDP-only, so
`+notcp` is required to exercise the UDP path.

| query | resolver | delivered answer |
|-------|----------|------------------|
| `example.test ANY` (+notcp) | **veri-dns MUTATED** @10.53.0.2:5300 | `example.test A 10.53.0.100` **and `sub.example.test A 6.6.6.6` (LEAKED)** |
| `example.test A` (typed control) | veri-dns MUTATED | `example.test A 10.53.0.100` only (scrubbed — hardened) |
| `example.test ANY` (+notcp) | **veri-dns BASELINE** (unmutated) | `example.test A 10.53.0.100` only (`sub.example.test` scrubbed) |
| `example.test ANY` (+notcp) | unbound (reference) @10.53.0.3:5301 | `example.test A 10.53.0.100` + SOA only (no leak) |

The mutated binary leaks the foreign record only on ANY; the typed control and
the unmutated baseline both scrub it; unbound never leaks it. Mutation is causal.

## Cleanup
`git checkout -- .`, `lake build`, `restart-verid.sh`; rogue-leaf stopped and the
real `veridns-auth-leaf` nsd unit recreated; baseline confirmed
(`host.example.test A = 10.53.0.101`, `example.test ANY` = honest SOA, no leak).
