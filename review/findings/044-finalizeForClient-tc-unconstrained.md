# Finding 044: Delivered-header spec leaves TC unconstrained; forced TC=1 bricks all resolution (coverage-gap)

## Classification
coverage-gap (delivered-header spec omits the truncation bit)

## Mutation
- id: M-finalizeForClient-tc-force
- target: `VeriDNS/Impl/Server.lean:31` (`finalizeForClient` body)
- diff:
```
-  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }
+  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0, tc := 1 } }
```

## Build result
GREEN. `lake build` -> "Build completed successfully (279 jobs)." No theorem broke.

## Why verification did not catch it
`finalizeForClient_flags` (`VeriDNS/Proof/Refinement.lean:8685`) is the ONLY theorem about
the delivered client header. It states exactly:

```
(Server.finalizeForClient resp).header.qr = 1
  ∧ (Server.finalizeForClient resp).header.aa = 0
  ∧ (Server.finalizeForClient resp).header.ra = 1
  ∧ (Server.finalizeForClient resp).header.z = 0
```

proved by `⟨rfl, rfl, rfl, rfl⟩`. The truncation bit `tc` is not one of the four conjuncts,
so setting `tc := 1` changes none of qr/aa/ra/z and all four `rfl`s still hold. `grep` over
the proof tree confirms no theorem anywhere asserts `(finalizeForClient _).header.tc = 0`
(or any delivered-tc constraint). This is a pure spec/coverage gap, NOT brittleness: no proof
mentions the delivered tc bit, so nothing needed repairing to stay green. Direct analogue of
the rd/qr/aa/ra/z-style delivered-header findings, extended to tc.

## Reproduction (attacker ns, veri-dns@10.53.0.2:5300 vs unbound@10.53.0.3:5301)

veri-dns, UDP, complete <512B answer:
```
$ dig +noedns +ignore @10.53.0.2 -p 5300 www.example.test A
;; flags: qr tc rd ra; QUERY: 1, ANSWER: 2, AUTHORITY: 0, ADDITIONAL: 0
;; ANSWER SECTION:
example.test.   3592  IN  A  10.53.0.100
```
TC=1 is set even though the answer is complete (ANSWER: 2, records present, well under 512B).

Without `+ignore`, dig honors the truncation signal and fails:
```
$ dig +noedns @10.53.0.2 -p 5300 www.example.test A
;; Truncated, retrying in TCP mode.
;; Connection to 10.53.0.2#5300 ... failed: connection refused.
;; no servers could be reached
```
veri-dns has no TCP listener (RFC 7766 MUST; KB findings 042/043), so the mandated TCP retry
is connection-refused and resolution is fully bricked for every client.

unbound (reference), same query, no false truncation:
```
$ dig +noedns @10.53.0.3 -p 5301 www.example.test A
;; flags: qr rd ra; QUERY: 1, ANSWER: 2, AUTHORITY: 0, ADDITIONAL: 0
```

## Recommended fix
Add a conjunct `(Server.finalizeForClient resp).header.tc = 0` to `finalizeForClient_flags`
(or pin the delivered tc to a faithful truncation predicate). As written the resolver always
delivers a complete UDP payload, so tc=0 is the correct invariant; the spec should require it.

## Baseline restored
`git checkout -- .`; `lake build` green; `restart-verid.sh` -> active; baseline resolves
(`host.example.test` -> `10.53.0.101`). `git status` clean.
