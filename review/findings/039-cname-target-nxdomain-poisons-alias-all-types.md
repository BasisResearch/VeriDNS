# 039 — NXDOMAIN from a CNAME target is negatively cached against the ORIGINAL alias, type-agnostically, denying a live CNAME name for every RR type

- **Severity:** high (correctness + cross-zone denial-of-existence / cache-poisoning vector)
- **Component:** negative caching of CNAME-chain NXDOMAIN
- **Verdict:** impl-bug — confirmed on the rig with a differential vs unbound
- **Classification:** impl-bug

## Summary

When veri-dns resolves `alias A`, where `alias` is a live CNAME pointing at a
target that yields NXDOMAIN, it caches the NXDOMAIN **against the alias name
itself** (not the target), **ignoring qtype**. Because the negative-cache
NXDOMAIN lookup is type-agnostic, a subsequent query for the *same alias* at
*any other type* (AAAA / MX / TXT / …) is answered from cache as a bare
NXDOMAIN — `ANSWER: 0`, the CNAME dropped — **with zero upstream egress**,
even though the alias provably exists as a CNAME. The SOA replayed in the
cached denial is the **target zone's** SOA, which is out of bailiwick for the
alias.

Net effect: a name that exists (as a CNAME) is asserted non-existent for its
full negative TTL, for every RR type. If a CDN/alias target is decommissioned
(legit NXDOMAIN), the alias is nuked for all types; an operator/attacker
controlling the target zone can, with a single legitimate NXDOMAIN, deny any
alias CNAMEd to them across all types (compounds with finding 013's
out-of-bailiwick negative SOA).

unbound instead keeps the CNAME and attributes the NXDOMAIN to the **target**
name, so its cached answer preserves the CNAME and the denial is semantically
about the target, not the alias.

## Root cause (code)

- `VeriDNS/Impl/Resolver.lean:482` — `State.lastQuery` is set once to the
  original client query and **never updated** across the CNAME chase
  (`stepAnalyzeResponse` advances `sname := target` but not `lastQuery`).
- `VeriDNS/Impl/Resolver.lean:172-178` — `finalizeAnswer` forces the delivered
  response's `question := lastQuery.question` = the **alias**.
- `VeriDNS/Impl/Server.lean:442-451` — `storeNegativeIfCacheable` calls
  `storeNegative qu.qname qu.qtype …` with `qu = resp.question[0]` = the alias.
  `negativelyCacheable` (`Server.lean:87-90`) only requires `rcode == nameError`
  and does **not** require an empty answer section, so a CNAME-in-answer
  NXDOMAIN is still cached.
- `VeriDNS/Impl/Cache.lean:76-82` — `DnsCache.lookupNxdomain` matches on
  name + class + expiry + `rcode == nameError` and **ignores qtype**, so the
  single stored negative denies the alias for *all* query types.

## Reproduction (rig)

Setup — add a cross-zone broken CNAME to the leaf zone
(`/opt/dnsenv/nsd/zones/example.test.zone`, bump SOA serial, restart
`veridns-auth-leaf`):

```
broken  IN CNAME nothere.test.
```

`nothere.test` does not exist in the `test.` zone, so the tld server
(10.53.0.11) returns NXDOMAIN with the **`test.`** SOA in authority (out of
bailiwick for `broken.example.test`). Restart both resolvers to clear caches.

### veri-dns (@10.53.0.2:5300) — under test

Q1 `broken.example.test A` (prime):
```
;; ->>HEADER<<- status: NXDOMAIN;  ANSWER: 1, AUTHORITY: 1
broken.example.test.  3600 IN CNAME nothere.test.
test.                 3600 IN SOA   a.tld.test. ... 1 3600 900 604800 3600
```

Q2 `broken.example.test AAAA` (different type) — tcpdump on `v-verid` shows
**ZERO upstream packets**:
```
;; ->>HEADER<<- status: NXDOMAIN;  ANSWER: 0, AUTHORITY: 1
test.                 3598 IN SOA   a.tld.test. ... 1 3600 900 604800 3600
   (SOA TTL 3598 = aged => cache hit; CNAME dropped, ANSWER: 0)
```

Q3 `broken.example.test MX`, Q4 `broken.example.test TXT` — identical bare
NXDOMAIN, `ANSWER: 0`, `test.` SOA at aged TTL (3526 / 3503), **zero upstream
egress** (full pcap empty). Meanwhile the leaf still serves
`broken.example.test` as a live CNAME (`dig @10.53.0.12 ... +short` -> `nothere.test.`).

### unbound (@10.53.0.3:5301) — reference

Q1 `broken.example.test A`:
```
;; ->>HEADER<<- status: NXDOMAIN;  ANSWER: 1
broken.example.test.  3600 IN CNAME nothere.test.
test.                 3600 IN SOA   ...
```

Q2 `broken.example.test AAAA`:
```
;; ->>HEADER<<- status: NXDOMAIN;  ANSWER: 1
broken.example.test.  3599 IN CNAME nothere.test.   <-- CNAME PRESERVED
test.                 3599 IN SOA   ...
```

unbound keeps the CNAME in the answer and attributes the denial to the target
`nothere.test`; the negative is keyed to the target, not the alias.

## Why veri-dns's behavior is wrong

- It asserts `broken.example.test` **does not exist** (NXDOMAIN, `ANSWER: 0`,
  no CNAME) for AAAA/MX/TXT, while `broken.example.test` provably exists as a
  CNAME (its own Q1 answer and unbound's Q2 both carry the CNAME). Dropping the
  CNAME discards the fact that the name is an alias.
- The denial is **type-agnostic** and keyed on the **alias** name, so it
  survives across all RR types and for the full negative TTL, served with zero
  egress. If the target later comes into existence, veri-dns keeps denying the
  alias for the remaining TTL (the negative is not keyed to the target, unlike
  unbound).
- The negative-cache SOA is the **target zone's** SOA (`test.`), out of
  bailiwick for the denied name (`broken.example.test` lives in
  `example.test.`) — a cross-zone denial-of-existence surface (compounds 013).

## Reference

- RFC 1034 §3.6.2 / §5.2.2 (CNAME chase: the resolver restarts the query at the
  canonical name; the alias itself is not the subject of the target's answer).
- unbound `iterator/iterator.c` CNAME query-restart (`processDNSSECAlignment` /
  QUERYTARGETS restart): NXDOMAIN is attributed to the restarted target qname,
  and the CNAME is retained in the returned message.
- Contrast with veri-dns keying `storeNegative` on `resp.question[0]` = the
  original alias (`Server.lean:450`) and `lookupNxdomain` ignoring qtype
  (`Cache.lean:76-82`).

## Notes

Rig left pristine: `example.test.zone` restored to its original 4-record form
(serial 1, no `broken` record) and `veridns-auth-leaf` / `veridns-verid` /
`veridns-ref` restarted. To re-reproduce, re-add the `broken IN CNAME
nothere.test.` line, bump the serial, restart the leaf, and clear resolver
caches.
