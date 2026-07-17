# Systematic correctness plan

Written 2026-07-15. A differential rig found eight bugs the verified resolver still has. The right
response is not eight fixes. It is to ask why a *verified* resolver has any behavioural bug at all,
and to close the reason.

## The target is one theorem

A verified resolver should have one top-level correctness theorem, total over its inputs, in both
directions:

> For every query `q`, every cache state the running system reaches, and every network behaviour
> (honest or adversarial), the response the resolver returns is exactly the RFC-determined response
> for `q`: every record it delivers is authorised (soundness), and whenever the authoritative data
> reachable on honest paths determines an answer, a NODATA, an NXDOMAIN, or a referral, that is
> what it returns and nothing else (completeness), and no adversary changes the outcome
> (security).

If that theorem holds with no scope hypothesis, a behavioural bug is a counterexample to it, so it
cannot exist. Every bug the rig found exists because the theorem we actually proved has a hole the
bug fits through.

## Bugs are not instances, they are open scope hypotheses

The current top capstone is `serveSeq_total_primed`. Read its hypotheses. Each one is a door left
open, and each open door is a class of bug, not a single bug.

- `qu.qtype.toNat ≠ 255` (`ServeSequence.lean:60`). ANY queries are out of scope. Every ANY bug
  lives here. The rig's ANY divergence is one; there are others we have not looked for.
- `αClass qu.qclass = some RRClass.in`. Non-IN queries are out of scope. The CHAOS
  SERVFAIL-vs-REFUSED divergence lives here.
- The statement is soundness and totality. It has no completeness half. So a resolver that returns
  the wrong answer, a NODATA for a name that exists, satisfies it. 041/045 lives here, and 040,
  because misclassifying a response is a completeness fault the soundness half cannot see.
- Underneath, adequacy uses a single-NS `SlistShape`. Multi-homed delegations are out of scope.
  035 lives here.
- Soundness is stated against `WorldModels`, the adversary model. It only rules out attacks
  `WorldModels` enumerates. An attack outside the disjunction is not covered. 038 (subtree
  hijack) and 017 (junk from the legitimate source) may be attacks the model does not represent.
- Entitlement (W1) frames the answer, cache, and next-query outputs, over the answer, authority,
  and glue roles. The additional section as delivered is not yet framed. 047 lives here.

Two doors were open last week and are now closed, which is the proof the method works:

- The empty-cache base case. `serveSeq_total` held only for `DnsCache.empty`; the running system
  serves from a primed cache. W2a closed it with `serveSeq_total_primed`.
- The content-free error verdict. `Resolves.gaveUp` was unconditional, so any SERVFAIL satisfied
  the error arm. W2b closed it with a failure witness.

Neither was fixed as an instance. Each was an open hypothesis, and closing it eliminated every bug
that needed that door.

## The escape-hatch ledger

The systematic programme is to enumerate every open door in the top capstone and shut it. This is
the whole plan. The ledger is the backlog; the reproducing findings are evidence for specific
rows, not the backlog itself.

| Hatch | Open door in the capstone | Bug class it admits | Findings seen | Close by |
|---|---|---|---|---|
| Query shape | ~~`qtype ≠ ANY`, `qclass = IN`, `rd = false`~~ **CLOSED 2026-07-16** | any behaviour on ANY / non-IN / RD-shaped queries | CHAOS, ANY | **CLOSED at the serve boundary.** non-IN → REFUSED at `queryProblem` ingress (RFC-correct policy REFUSED, `Server.hygiene_refused_class`), so `qclass=IN` is *derived* from `queryProblem = none`. QTYPE=ANY → RFC 8482 §4.2 synthesized minimal HINFO RRset via a `serveDatagram` serve arm (`Server.serveDatagram_any`, `synthAnyResponse`; `Spec.AnyMinimal`), so ANY is *handled* not excluded. `rd = false` was found to be the iterative-upstream-query convention (`buildSubQuery` clears rd; client rd echoed back, review #007/#010a), NOT a real client-input gate — recursive rd=1 clients are fully served. The serve capstones (`serveSeq_total{,_mkSbelt,_primed}`, `serveDatagram_total`, `serveTcpDatagram_total`) are now query-shape-CLEAN; the resolver-core capstones keep IN/rd/non-ANY as `justified_scope` below-boundary premises. |
| Direction | soundness with no completeness dual | wrong answers: spurious NODATA, misclassified referral | 040, 041/045 | a total `Classify` theorem + completeness corollary (name exists ⇒ delivered; NODATA only when truly empty) |
| Topology | single-NS `SlistShape` | failover, multi-homed delegation | 035 | set-valued `SlistShape'` + failover adequacy |
| Adversary model | soundness only vs the `WorldModels` disjunction | attacks not enumerated in the model | 038, 017 | prove the adversary model complete: every wire datagram realises some disjunct, so no attack is unmodelled |
| Entitlement coverage | answer/authority/glue roles only | off-entitlement records in unframed sections | 047 | extend `Entitled` to the additional section and the shadow-a-subtree role |
| Boundary | C TCB, transport source-acceptance | junk accepted below the shim | 017 | model source-and-content acceptance at the shim edge; C is the named floor |
| State | specific terminals, primed-only | untested cache shapes | (none yet) | duals for every terminal; invariants as transition closure |

Closing a row is class elimination. It removes the finding named in the row and the siblings we
have not found, because the theorem now quantifies over the whole class.

## The acceptance criterion is mechanical

The programme is done, in the verified core, when the top capstone's hypothesis list contains only
genuine facts about the running system, and none of these:

- no restriction on `q` (any qtype including ANY, any qclass including CH, any RD),
- no restriction on topology (any number of NS per cut),
- no restriction on cache state beyond the invariants the system actually maintains,
- both directions present (sound and complete),
- the adversary model proven complete, so soundness against it is soundness against every wire.

A hypothesis that narrows any of these is a door, and a door is where the next rig run will find a
bug. The criterion is checkable by reading the signature, so it is enforceable: extend the
`rfc_proves` blueprint with a lint that flags any capstone hypothesis matching a scope pattern
(`qclass =`, `qtype ≠`, `SlistShape`, `Cooperative`, a specific `Rcode`) unless it carries an
explicit `justified_scope` annotation with a reason. An unjustified scope gate fails the build.

## What cannot be proven away, and how it is bounded

Two reservoirs are irreducible, and honesty requires naming them rather than claiming zero bugs.

- The C TCB. `recvfrom`, the sockets, the FFI. These are trusted, listed in the manifest, and
  shrunk where possible. A bug here is not a counterexample to any theorem.
- The model-versus-RFC gap. The RFC is prose. The bridge is the `rfc_proves` text pins plus the
  diff rig. No theorem closes this; it is validated, not verified.

So the maximal honest claim is not "no bugs". It is: every behavioural bug in the verified core is
a counterexample to the total theorem and therefore cannot exist; the only reservoirs left are the
named C TCB and the model-RFC gap, both bounded by the manifest and probed continuously by the
discovery harness. When the harness finds divergences only in those two places and never in the
core, the core is systematically closed.

## The discovery harness is the standing check on the residue

The rig found these bugs because it explores. The verified core will always have a residue (the two
reservoirs), so the explorer is permanent, not a one-off.

- It mutates honest responses over a real topology and checks the output against RFC-derived
  properties (no reference resolver needed) and against unbound (where present).
- Every divergence it finds is triaged to a ledger row. If the row is already closed, the
  divergence is in the residue (a TCB or model-RFC issue) and updates the manifest. If the row is
  open, it is proof the door is still open.
- It runs continuously, not once per finding. This is the difference from the first plan, whose
  harness only replayed known findings.

## Sequencing

- The ledger is the plan. Work the rows, not the findings.
- Direction (the completeness dual) is the highest-value row: it is the largest open door and the
  one that admits wrong answers. The `Classify` theorem plus completeness corollary closes 040 and
  041/045 together and gives the resolver its first general "the answer is correct" statement.
- Adversary-model completeness is the deepest row: it converts soundness-against-a-model into
  soundness-against-every-wire, and subsumes the class 038 and 017 belong to.
- Query shape, topology, entitlement coverage, boundary: each a row, each closed by quantifying
  over the class.
- The scope-gate lint lands first, so no new door opens silently while the old ones close.
- The discovery harness runs throughout.

## Status

Closed doors: empty-cache base (W2a), content-free error verdict (W2b), second parser (W0),
WorldModels non-vacuity (witness world). In flight: the two glue entitlement leaks (W1-fix),
transport source-acceptance (017), the discovery harness (D). Held for W1-fix's merge because they
share proof arms: the `Classify` completeness theorem, the entitlement extension, the 015 pin.
