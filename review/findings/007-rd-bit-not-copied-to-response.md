# Finding 007: RD bit in client replies is unconstrained by the spec (coverage gap)

**Classification:** coverage-gap (build fully green under a mutation that violates RFC 1035 §4.1.1)
**Mutation id:** M-rd-echo-force0

## Mutation

`VeriDNS/Impl/Server.lean:31`, in `finalizeForClient`:

```diff
-  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }
+  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0, rd := 0 } }
```

This forces RD=0 on every reply sent to a client, even when the client's query
carried RD=1.

## Build result

`lake build` — **Build completed successfully (279 jobs)**, zero errors, no
proof repairs needed. (`lake build veri-dns` also green, 560 jobs.)

## RFC violation

RFC 1035 §4.1.1 (rfc/rfc-1035.txt:1464-1465):

> RD  Recursion Desired - this bit may be set in a query and
>     is copied into the response.

The mutated resolver never copies RD; it hard-clears it.

## Observable reproduction (attacker ns, dig default sends RD=1)

Mutated veri-dns @10.53.0.2:5300:

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 13029
;; flags: qr ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0
host.example.test.  3572  IN  A  10.53.0.101
```

Reference unbound @10.53.0.3:5301, same query:

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 25494
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
```

veri-dns answers `qr ra` (RD=0) where unbound answers `qr rd ra`: a wire-visible
header divergence. Strict stub resolvers/monitoring tools that check the RD echo
would flag or mis-handle these replies.

## Why the proofs are blind

- `finalizeForClient_flags` (VeriDNS/Proof/Refinement.lean:8685) and the
  cluster `finalizeForClient_qr/ra/aa/id/z` (VeriDNS/Proof/Refinement.lean:8683-8696,
  plus Proof/Server.lean:138-151 users) pin qr=1, aa=0, ra=1, z=0 and id
  preservation — **rd is never mentioned**.
- `serverAnswers_rd_irrelevant` (VeriDNS/Spec/NetworkModel.lean:810) explicitly
  proves the network-model answer relation is invariant under the query's rd
  bit, so the semantic spec cannot see this bit at all.

There is no theorem of the shape
`(finalizeForClient resp).header.rd = query.header.rd` anywhere in the tree.

## Suggested obligation

Add to the finalizeForClient cluster (and thread through the shim soundness
statement) a lemma tying the emitted header's rd to the client query's rd, e.g.
have finalizeForClient take the original query (or assert at the call site in
the serve loop) and prove `reply.header.rd = query.header.rd`, citing
rfc/rfc-1035.txt:1464-1465 via `rfc_proves`.

## Note

The RD bit is what actually gates recursion in the spec's client-side
predicates (queryProblem/performsRequestedOperation require RD=1), so the echo
being unmodeled also means the "this reply is a recursive answer to a recursive
question" wire signal is unverified — this strengthens the RD differential
noted in prior findings.
