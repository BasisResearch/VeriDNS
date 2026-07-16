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

---

## REGRESSION 2026-07-15 (post-remediation 26b5849) — SPEC GAP UNFIXED (symptom not currently triggered by this exact mutation)

`finalizeForClient_flags` (`VeriDNS/Proof/Refinement.lean:7939-7944`) STILL pins
only `qr=1 ∧ aa=0 ∧ ra=1 ∧ z=0` — no delivered-`tc` conjunct — and its proof is
still `⟨rfl, rfl, rfl, rfl⟩`. The original M-finalizeForClient-tc-force mutation
would therefore STILL build green. The coverage gap is unfixed at the spec level.

The observable symptom of *this specific mutation* is absent only because upstream
did not apply it: `finalizeForClient` (`Impl/Server.lean:30-32`) does not force
`tc`, so a normal fitting answer is delivered with tc=0 (verified:
`www.example.test A` +ignore -> flags `qr rd ra`, no tc). But the delivered-tc bit
remains unconstrained by any theorem, and finding 043 shows a reachable path
(`truncateUdp` m2) where veri-dns delivers `tc=1` on a *complete* answer with the
build green — the exact class of defect this coverage-gap predicts. Shared root
cause with the still-present 032. Recommended fix (pin
`(finalizeForClient resp).header.tc` to a faithful truncation predicate) not
applied.

## REGRESSION 2026-07-16 — STILL PRESENT, now confirmed by EXECUTING the mutation

The 2026-07-15 note above reasoned from code-reading that "the original
M-finalizeForClient-tc-force mutation would therefore STILL build green". That
prediction has now been **executed and confirmed**, not merely inferred:

```
VeriDNS/Impl/Server.lean:32
-  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }
+  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0, tc := 1 } }

$ lake build
Build completed successfully (300 jobs).
```

Fully GREEN — no theorem statement, no `rfc_proves` line, and no `#guard` mock in
`VeriDNS/Test/Loop.lean` rejects a delivered header that falsely claims truncation.
`finalizeForClient_flags` (`VeriDNS/Proof/Refinement.lean:7939-7944`) still pins only
`qr=1 ∧ aa=0 ∧ ra=1 ∧ z=0` with proof `⟨rfl, rfl, rfl, rfl⟩`; the four `rfl`s are
undisturbed by `tc := 1`. Every `header.tc` occurrence in `Proof/` is a *hypothesis*
(`resp.header.tc = 0 → …`, e.g. `NameTreeComplete.lean:1250,2253,2591,2893`), never a
constraint **on** the delivered header.

`docs/remediation-plan.md` does not mention finding 044 anywhere, so this gap is
neither fixed, pinned, nor scoped out — it is simply absent from the plan, contradicting
the plan's headline claim at line 32.

Baseline (unmutated) behaviour re-verified on the renumbered rig — the symptom of *this*
mutation is latent, not live, because upstream did not apply it:

```
$ ip netns exec attacker dig +noedns +ignore @203.0.113.2 -p 5300 www.example.test A
;; flags: qr rd ra; QUERY: 1, ANSWER: 2      <-- no tc, correct
```

Recommended fix (add a `(finalizeForClient resp).header.tc = 0` conjunct, or pin delivered
tc to a faithful truncation predicate) remains unapplied. Finding 043 still exhibits the
reachable instance of this defect class.
