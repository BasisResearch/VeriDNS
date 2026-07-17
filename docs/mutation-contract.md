# The mutation contract

Written 2026-07-15 alongside the W5 validation gate. This document states the
contract the validation harness (`test/ci_gate.sh`) is meant to enforce, and the
obligation it places on anyone changing the resolver.

## The contract

> **Any mutation that changes the resolver's byte-level behaviour while keeping the
> proofs green MUST break a differential test or a W2 model invariant.**
>
> Equivalently: a green proof build plus a green harness is a claim that the impl,
> the model, and a reference resolver all agree on observable behaviour. If you can
> change what bytes go on the wire without any of those three going red, the harness
> has a hole — and a green mutation with a red rig is the intended signal that a
> *model* property is missing (not a nuisance).

Refinement (`ioResumeLoop_sound`, `serveDatagram_verdict_sound`) proves the impl
matches the *model*. It says nothing about whether the model matches the RFC. The
two ways that gap has bitten (see `docs/model-strengthening-plan.md`) are:

1. the model was weaker than the RFC (an under-constrained predicate that both the
   impl and the model shared, so a fault stayed green under refinement); and
2. coverage stopped at a boundary the capstone never mentioned (parsing below the
   refinement line, an assumed premise, one direction of an iff).

The proofs cannot catch either class on their own. The differential harness and the
RFC-text pins are the external check. The mutation contract is the discipline that
keeps that check load-bearing: every byte-behaviour-changing degree of freedom must
be pinned by *something* that goes red — a diff test, an RFC-text pin, or (best) a
model invariant that makes the fault unrepresentable.

## What the harness pins

`test/ci_gate.sh` runs, per finding:

| Surface | Rig | Sub-test |
|---|---|---|
| id-source unpredictability (002 / W2 entropy) | `id-entropy-test` | distinct ≥ 3850 / 4096, bit balance, non-sequential |
| live recursion parity | `difftest.sh` | corpus vs recursive unbound |
| subdomain rider on an answer (004) | `inject_difftest.sh` #1 | rider dropped; ridden name not cached |
| unsolicited additional / Kaminsky | `inject_difftest.sh` #2 | glue never promoted to the answer cache |
| off-owner CNAME (036) | `inject_difftest.sh` #3 | CNAME not chased |
| off-owner / foreign SOA (012/013) | `inject_difftest.sh` #4 | foreign SOA not delivered in authority |
| qtype=ANY (served, uncovered) | `inject_difftest.sh` #5 | veri==unbound, locked |
| class=CHAOS (served, uncovered) | `inject_difftest.sh` #6 | veri=SERVFAIL / unbound=REFUSED, locked |
| upstream TC→TCP fallback | `tcp_difftest.sh` | forced-TC parity, oversized fallback, degrade |
| client TCP serving | `tcp_serve_difftest.sh` | oversized answer delivered in full over TCP |

Each adversarial case is a mock zone datum (`test/mock_auth.py`) plus a `dig`
assertion, mirroring the existing script style; the mock stays a **flat authoritative
root** (a collapsed root+child topology provokes a descent hang), which is fine
because entitlement scrubbing is about the delivered answer relative to the client's
qname and needs no delegation depth.

## Two flavours of pin

* **"Both drop it" (parity) pins** — the injection cases. veri-dns and a reference
  unbound are both validating resolvers, so a correct veri-dns delivers exactly what
  unbound delivers (the poison dropped). The assertion is `veri == unbound`. A
  mutation that stops scrubbing makes veri deliver the rider/CNAME/SOA that unbound
  drops → the equality breaks → red.

* **"Locked divergence" pins** — where veri-dns and unbound genuinely differ today
  and the point is to *document and freeze* the current byte-behaviour so it cannot
  drift silently. `class=CHAOS` is the live example: veri-dns resolves the non-IN
  query upstream, the authoritative server REFUSEs it, and veri surfaces that as
  SERVFAIL, whereas unbound answers REFUSED directly. The W4 hypothesis audit
  (`docs/audit/w4-server-codec.md`, finding #2) flags this exact surface as served
  with zero theorem coverage. The pin asserts the specific pair
  (`veri=SERVFAIL ∧ unbound=REFUSED`); if the audit's suggested fix lands (refuse CH
  locally to match unbound) the pin flips red and must be updated deliberately —
  which is the signal that the behaviour changed.

## Worked example — the `W` under-fold mutant

The canonical demonstration that a byte-behaviour change must go red *somewhere* is
the case-folding provenance work (findings 001 / 014, `docs/remediation-plan.md`).

RFC 1035 §2.3.3 requires name comparison to be ASCII-case-insensitive. The impl folds
each byte with `foldCaseByte`. Before the provenance fix, correctness rested on a hand
lemma (`NameTree.foldCaseByte_toNat`) that the RFC-generated coverage props did not
actually consume — so the following **surgical mutant stayed green**:

```
-- honest fold: lower-case every ASCII upper-case letter A..Z (0x41..0x5A)
foldCaseByte b = if 0x41 ≤ b ∧ b ≤ 0x5A then b + 0x20 else b

-- the mutant: exempt exactly the letter 'W' (0x57 = 87) from folding
foldCaseByte b = if (0x41 ≤ b ∧ b ≤ 0x5A) ∧ b ≠ 87 then b + 0x20 else b
```

This changes byte-level behaviour: `Www.example` and `www.example` now compare
unequal, so a case-varying glue record or a case-varying query is handled wrong for
exactly one letter. Under the old coverage every RFC-linked property still built
green — the classic "model weaker than the RFC" hole.

The fix (`namespace_casefold_exact` / `foldCaseByte_casefold_exact` and the five
`via`-discharged case predicates) made the fold *provably exact*. Now the `W`
under-fold mutant **fails at `foldCaseByte_casefold_exact`** — the proof goes red, as
the contract demands. This is the model-invariant flavour of the contract: the fault
is unrepresentable because a theorem pins the whole function, not a sampled point.

The differential-test flavour is the same shape at the wire boundary: a case-fold
mutant that survived the proofs would also make a case-varying glue owner mismatch
its NS name and drop the glue — a divergence a delegation diff test against unbound
would catch. Either the invariant or the rig must go red; the contract is that at
least one always does.

## Using the contract

When you change anything that can alter what bytes veri-dns emits — a scrub, a guard,
a cache-acceptance rule, the fold, a truncation boundary — and `lake build` stays
green:

1. Run `test/ci_gate.sh`. If it stays green too, ask *why nothing pinned the change*.
2. If the change was intended and correct, some pin should have moved — extend the
   diff corpus (one case per behaviour) so the new behaviour is locked.
3. If the change was a regression, a parity pin should already be red; if it is not,
   the model is missing the corresponding invariant (a W2 obligation) — file it.

A green mutation with a green harness is not "fine". It is a gap in the harness.
