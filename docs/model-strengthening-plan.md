# Model-strengthening plan

Written 2026-07-15 against `main` (`26b5849`). The verified core proves *refinement*: the
executable resolver implements the RFC-derived model (`ioResumeLoop_sound`,
`serveDatagram_verdict_sound`), and the recent liveness arc adds the converse on cooperative
networks (`resolveWithIO_spine_adequate`). 

Refinement is a relative guarantee. It says the impl matches a model;
it says nothing about whether the model matches the RFC, and it says
nothing about the directions and boundaries a capstone does not
mention.

The proofs guarantee internal consistency between two artefacts, and
the external validity (model versus RFC) came from the diff rig plus
the RFC-text pins. Two structural causes recur:

1. *The model was weaker than the RFC.* Model and impl shared an under-constrained predicate
   (`isAncestorB` bailiwick, type-only `answersQuery`, an owner-blind `cnameRR`), so refinement
   held while the model authorised the fault. A mutation that keeps impl equal to model stays
   green.
2. *Coverage was one-directional or stopped at a boundary.* Soundness alone is satisfied by a
   resolver that fails every query; an assumed premise the proof never discharges is trusted
   glue; parsing done below the refinement boundary is never seen.

This plan attacks the causes, not the ten instances. 

Five workstreams: 

a single validating parser (W0), 

one non-interference theorem that subsumes the owner-check family
(W1), 

a model invariant layer that makes the model provably meet the
RFC (W2), 

the adequacy duals made systematic (W3), 

and a fleet audit of every theorem's hypotheses (W4). 

A validation-harness gate (W5) provides a mechanism to catch the
faults in the first place.

## W0 — one validating parser, the other proven redundant on its domain

There are two record decoders.

- `Message.decode` (`Impl/Message.lean:70`) is the only ingress path
(`Impl/Server.lean:385,394,783,806`); it runs `decodeRRCanonical`
(`Impl/Message.lean:12`) per record, which decompresses every embedded
name, re-serialises each record into a canonical pointer-free blob,
and checks rdlength for
NS/CNAME/PTR/SOA/MX/SRV.

- `ResourceRecord.decode` (`Impl/ResourceRecord.lean:10`) and
`RData.decodeSoa` run afterwards, inside the cache and resolver
(`Impl/Cache.lean:605,613`, `Impl/Resolver.lean:205`,
`Impl/Server.lean:81,100,304`, `Impl/Edns.lean:19`), on the blobs the
ingress parser already produced.

The second decoder is lenient (it reads rdlength bytes and
re-validates nothing), and today its safety rests on an informal fact:
every raw it ever sees is a `decodeRRCanonical` output.

This fix makes that fact a theorem, after which the ingress parser is
the single trust root and the internal decoder is its inverse on
canonical blobs.

- Define `CanonicalRaw b` (message): `b` is a `decodeRRCanonical` output, equivalently an
  `encode` image of a canonical record (`rrWire` shape, expanded names, rdlength agreeing with
  content).
  - message: pin the exact byte shape the internal decoder is safe on.

- Prove `ResourceRecord.decode` is total and inverse on `CanonicalRaw` (`decode_encode` is the
  half that exists; add the totality and the round-trip on the canonical image).

- Prove `CanonicalRaw` holds of every raw that reaches the internal decoder: cache stores only
  `decodeRRCanonical` outputs (`storeChecked`/`cacheRRs` inputs), and the resolver reads only from
  the cache or from freshly decoded messages.
  - flow: a store-side invariant `CacheRawsCanonical` threaded like the existing cache
    invariants, established at ingest and preserved by every write.

- Outcome: the lenient decoder becomes provably equivalent to the validating one on its actual
  domain, so 037's rdlength gap is closed for all internal reads, and either decoder can be
  expressed as a corollary of the other. If the equivalence collapses one to a wrapper, delete it.

## W1 — one non-interference theorem for the owner-check family
Owner-check faults are one property in disguise: an off-entitlement record placed in a
response changes what the resolver delivers, caches, or asks next. 

State that the observable behaviour depends only on the records the
query is entitled to, prove it once over the model, and each fault
becomes an instantiation while any future omission of an owner check
fails the proof.

- Define `Entitled q rr` per response role, one relation with role cases.
  - answer: owner equals `q.qname` or a link on the CNAME chain rooted at `q.qname`.
  - negative authority: SOA owner is an ancestor of `q.qname`.
  - referral and glue: owner in the bailiwick of the delegation.
  - message: entitlement is what the resolver is allowed to act on, per RFC 2181 §5.4.1 and
    RFC 2308 §3.
- State non-interference over the model's response handler `handle : Response → State →
  (Delivered, CacheDelta, NextQuery)`.
  - theorem `handle_frame`: for any `rr` with `¬ Entitled q rr` and any section, `handle (resp
    with rr inserted) s = handle resp s`. Inserting or deleting a non-entitled record changes no
    observable output.
  - flow: prove by the model's own section-filter being an `Entitled` filter; the filtered
    multiset is invariant under non-entitled edits.
- Transport through refinement so the impl inherits the frame (the impl's scrub refines the
  model's filter, already the shape of `scrubAnswer_no_foreign`).
- Corollaries, each one line:
  - 004: a subdomain rider on an answer is dropped from the delivered set and the cache.
  - 036: an off-owner CNAME is not chased (it is not entitled, so `NextQuery` is unchanged).
  - 012 / 013: an off-owner SOA is neither served nor cached negatively.
  - answer-injection (the earlier finding): foreign answer records never reach the client.
- Seed: `scrubAnswer_no_foreign` (`Spec/AnswerAuthenticity.lean`) is the answer-role special case;
  generalise its statement to the role-parameterised `Entitled` and re-derive it as a corollary.

## W2 — a model invariant layer

Add a layer that checks the model against the RFC: 
- closure properties of the model's own transition relation, each
proven `∀ step, Inv s → Inv (step s)`, so any new model rule must
preserve every invariant or fail to build.

This turns the RFC MUSTs the model is meant to satisfy into
obligations the model discharges.

- Bundle the invariants as one `ModelInvariant` record over model states, with a `preserved_by`
  obligation per rule.
  - message: one place to read what the model guarantees, one obligation per rule to keep it.
- The enumerated family, each linked to its RFC clause through the existing `check_rfc_doc` /
  `rfc_proves` blueprint so coverage means "the model satisfies the MUST", not "the text is
  quoted":
  - Bailiwick closure: no modelled deliver or cache step introduces an owner outside the query's
    bailiwick. This is the model-side twin of W1 and the root cause of 004/012/013/036.
  - Credibility monotonicity (RFC 2181 §5.4.1): a cache write never replaces a datum with a
    strictly less trustworthy one.
  - Name canonicity: every owner and every name-bearing rdata target stays a canonical wire name
    (≤255 octets, valid labels).
  - Negative-cache owner: a negatively cached name's SOA owner is an ancestor of the queried name.
  - TTL bounds: cached TTLs are clamped to the configured ceiling and never revive past expiry.
  - Entropy obligation (the 002 premise): the unpredictability the anti-forgery proofs consume
    becomes a named `ModelInvariant` field, discharged for the model and, at the FFI boundary,
    listed in the trust manifest with a runtime property test (W5) rather than silently assumed.
- Discharge generically: prove each rule preserves the bundle once; a new rule inherits the
  obligation shape and cannot land un-checked.
  - flow: this is the systematic version of the July tightenings, which each patched one
    predicate. The invariant layer makes the property hold for the whole transition system.

## W3 — the adequacy duals
Make a standing discipline: every soundness capstone must have an
adequacy dual, and the pair states the iff on the cooperative path, so
"fails every query" is not representable for any capstone.

- Enumerate the soundness theorems and their dual status.
  - paired already: `ioResumeLoop_sound` with `resolveWithIO_spine_adequate`;
    `serveDatagram_verdict_sound` with `serveDatagram_depth1_adequate`.
  - missing: the cache-hit terminal, the NXDOMAIN terminal, the referral terminal at general
    depth, and the TCP serve boundary.
- Produce each missing dual as `HasVerdictAt v ↔ delivered v` on the cooperative path, reusing the
  descent toolkit.
- Register the pairing so it is checkable.
  - a small `dual_of` annotation (sibling of `rfc_proves`) linking a soundness capstone to its
    adequacy converse; a soundness capstone with no registered dual is flagged in the build
    report.
  - message: a new capstone without its converse is visible, not silent.
- Generalise adequacy coverage to the shapes soundness already has: multi-NS cuts (a `SlistShape`
  generalisation) and the remaining terminal families, so the iff holds wherever soundness does.

## W4 — audit every theorem's hypotheses

This task focuses on looking across all theorems, and identifying
which hypotheses are unnecessary, which are unrealistically strong,
and which quietly narrow a conclusion below what its role
claims. 

Answer it by sweeping the whole proof corpus with subagents on
restricted contexts, one slice each, and ranking the findings.

- Partition the proof files into slices (by directory cluster, sized for one context each). Each
  subagent gets its slice plus the signatures it depends on, not the whole repo.
- Per theorem in the slice, classify every explicit hypothesis:
  - *Unused*: removable without breaking the proof. Confirm with `lean_minimal_hypotheses`. A
    removable premise strengthens the theorem for free.
  - *Unrealistic*: a premise real inputs never satisfy, making the theorem vacuous or scoped away
    from the running system (a cache assumed empty where it never is, a network assumed honest
    where soundness needs the adversarial arm, fuel bounds that cannot hold, class-IN-only or
    `qtype ≠ ANY` gates that hide the general case).
  - *Over-scoped conclusion*: the theorem name or role promises more than the statement delivers
    (a capstone silently assuming the cooperative arm, a soundness lemma gated to one rcode).
  - *Load-bearing and fair*: a genuine precondition, recorded as such.
- Each subagent returns a table: theorem, hypothesis, class, evidence, suggested action. A
  meta-subagent dedups across slices and ranks by severity, worst offenders first.
- Feed the results back: an assumed-oracle premise becomes a W2 model obligation; an over-scoped
  conclusion becomes a W3 dual or a generalisation; an unused premise is deleted.
- Tools: `lean_minimal_hypotheses` per theorem, `lean_verify` for the axiom footprint, and the
  diff rig to check whether a "simplifying" premise actually holds on real traffic.

## W5 — validation harness

Differential testing is where review faults are often caught, so it
should be part of CI. Grow the corpus and wire it into the gate.

- Promote `test/difftest.sh` and the TCP rigs to a CI gate against a reference resolver, with an
  adversarial corpus grown by one case per finding.
- Mutation contract: any mutation that changes byte-level behaviour while keeping the proofs green
  must break a diff test or a W2 model invariant. A green mutation with a red rig is the signal
  that a model property is missing.
- Add the entropy runtime test (the existing `IdEntropy` sampler) as a gate, discharging the W2
  entropy obligation at the boundary Lean cannot reach.

## Sequencing

- W4 first and in parallel; it is read-only, and its output scopes W2 and W3.
- W0 in parallel; it is self-contained.
- W1 and W2's bailiwick-closure together; they are the two sides of entitlement, one over the
  handler and one over the transition system.
- W3 after W2; the duals reuse the invariants.
- W5 throughout, as each property lands.

## Relationship to existing work

| Existing | This plan |
|---|---|
| `ioResumeLoop_sound`, `serveDatagram_verdict_sound` (refinement) | W3 pairs each with its adequacy dual |
| `scrubAnswer_no_foreign` (answer role) | W1 generalises it to role-parameterised entitlement |
| `check_rfc_doc` / `rfc_proves` (text coverage) | W2 upgrades coverage to "model satisfies the MUST" |
| liveness arc (cooperative adequacy) | W3 makes the dual a standing discipline |
| `decodeRRCanonical` (ingress validation) | W0 proves the internal decoder redundant on its domain |
| `test/difftest.sh` (side rig) | W5 promotes it to a gate with a mutation contract |
