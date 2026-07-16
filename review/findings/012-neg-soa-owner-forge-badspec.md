# Finding: Negative-cache SOA owner is attacker-substitutable (spec under-models the served SOA)

> **REGRESSION RE-TEST vs upstream 26b5849 (2026-07-15): FIXED (spec half).** The model now
> constrains the negative-proof SOA's owner: `soaNegTtl (qname) (resp)`
> (`Spec/NetworkSemantics.lean:833`) keeps an authority SOA only `if isAncestor r.owner qname`,
> and `Cache.absorbNeg` passes `q.qname`. The impl mirror is `extractSoaNegative`
> (`Impl/Server.lean:78`). The wire half is re-verified in `013-*.md` (poison SOA no longer
> served or cached; unbound agrees). The mutation of *this* finding (rewriting the stored SOA's
> owner to `.`) is now expected to break the build — NOT re-run here (this stage may not build);
> see 013 for the runtime evidence.

- ID: M-neg-soa-owner-forge
- Classification: **bad-spec** (green build + observable wrong behavior on the wire)
- Severity: high — RFC 2308 §3 bailiwick of the negative-proof SOA is unconstrained by the spec
- Build: **GREEN** (`lake build` → 279 jobs, completed successfully)

## Mutation

`VeriDNS/Impl/Server.lean:450-451`, in `storeNegativeIfCacheable`:

```
-        (some { soaRR with ttl := capped }) (nowT + capped.toNat.toUInt32))
+        (some { soaRR with ttl := capped, name := ByteArray.mk #[0] }) (nowT + capped.toNat.toUInt32))
```

The SOA that is stored for the negative-cache entry has its **owner name** rewritten to the
root `.` (a single zero label). The SOA rdata (MNAME/RNAME/serial/…) is left intact; only the
owner name — the field that RFC 2308 §3 requires to be the queried zone — is forged.

## Build result: GREEN

The mutation compiles with no proof breakage. Nothing in the verification constrains
`NegativeEntry.soa`'s owner name.

## Reproduction (differential vs unbound)

veri-dns @10.53.0.2:5300, cache-served NODATA (note TTL 3584 < 3600 ⇒ served from cache):

```
;; QUESTION SECTION:
;example.test.			IN	AAAA
;; AUTHORITY SECTION:
.			3584	IN	SOA	ns.example.test. hostmaster.example.test. 1 3600 900 604800 3600
```

unbound @10.53.0.3:5301, same cache-served NODATA:

```
;; AUTHORITY SECTION:
example.test.		3599	IN	SOA	ns.example.test. hostmaster.example.test. 1 3600 900 604800 3600
```

veri-dns delivers authority SOA owner `.` (root); unbound (and the real zone) delivers
`example.test.`. The owner of the negative-proof SOA served to the client is
attacker-substitutable end to end, and the wrong owner is cached and replayed.

## Why verification did not catch it (spec gap)

The abstract negative-cache entry does not model the SOA record at all:

- `VeriDNS/Spec/NetworkSemantics.lean:512` — `structure NegRR` has only
  `qname / qtype / insertedAt / ttl`. There is **no owner field and no rdata** for the SOA.
- `VeriDNS/Proof/Refinement.lean:2844` — `αNegRR` builds the abstract entry purely from
  `e.name / e.rcode / e.qtype / e.expiry` and **completely ignores `e.soa`**
  (`VeriDNS/Impl/Cache.lean:31`, the concrete `NegativeEntry.soa` field).

Because the served SOA record's owner/content is invisible to every refinement obligation,
no theorem STATEMENT constrains it. The soundness capstone is silent on the identity of the
SOA delivered in the authority section, so an attacker-chosen owner (or, by the same gap,
attacker-chosen rdata) passes verification unchallenged.

## RFC citation

RFC 2308 §3 ("Negative Answers from Authoritative Servers" / negative caching): the SOA
record placed in the authority section of a negative answer is the SOA of the zone that owns
the queried name (its apex must be an ancestor of, or equal to, the queried name). Serving a
root-owned SOA as the negative proof for `example.test` violates this bailiwick requirement.

## Recommended spec fix

Extend `NegRR` to carry the SOA owner (at minimum) and add a negative-caching soundness
obligation requiring that owner to be an ancestor of (or the zone apex of) the queried name,
and requiring the served authority SOA to be exactly that stored record. Thread `e.soa`
through `αNegRR` so the refinement can see it.
