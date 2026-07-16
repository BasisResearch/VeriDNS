# 045 — Bare empty NOERROR from the first-tried (lame) server yields a spurious NODATA for a name that EXISTS; unbound fails over to the good server and returns the real record

---

## ⚠️ REGRESSION STATUS 2026-07-15 (vs upstream 26b5849): **STILL PRESENT — never addressed. This is a WRONG ANSWER.**

`docs/remediation-plan.md` **does not mention finding 045 anywhere**. Neither
fixed, nor pinned, nor scoped out — despite being the batch's only confirmed
*wrong answer* (not merely an availability loss).

Both cited causes are **unchanged in the current source**:
- `VeriDNS/Impl/Resolver.lean:360` — `classifiableB` still returns true for any
  `rcode == Rcode.noError`, so a bare-empty NOERROR never routes back to
  `.sendQueries` at `:391`.
- `VeriDNS/Impl/Resolver.lean:435-436` — the catch-all
  `else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty then
  .answer (finalizeAnswer s resp) s` still accepts it as final on first receipt.

Note the contrast with **026/046**, which *were* fixed in this same function (the
`.error "4b: no NS records in authority"` terminal became
`.goto .sendQueries`). That fix covers the *non-empty-authority* shape only; the
bare-empty shape (authority empty ⇒ the `:394` branch is not entered at all)
still falls to `:435`. The remediation reached the neighbouring line and stopped.

### Re-run of the ORIGINAL repro on the current rig

Two-nameserver delegation for `flaky.test.`, lame server listed **first** in the
TLD zone (so it heads veri-dns's SLIST):
```
flaky           IN NS ns1.flaky.test.    ; 203.0.113.20 LAME: bare empty NOERROR
flaky           IN NS ns2.flaky.test.    ; 203.0.113.21 GOOD: www/v45 A 203.0.113.111
```
Lame server direct probe — `qr aa`, ANSWER/AUTHORITY/ADDITIONAL all 0:
```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 50237
;; flags: qr aa; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
```

Both resolvers restarted cold; `v45.flaky.test` is a never-before-seen name that
**exists** (A 203.0.113.111 on ns2):
```
-- veri-dns --
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 13632
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
VERIDNS: lame-ns1 hits=1  good-ns2 hits=0      <- accepts the lame reply, never tries ns2

-- unbound --
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 25291
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
v45.flaky.test.		3600	IN	A	203.0.113.111
UNBOUND: lame-ns1 hits=0  good-ns2 hits=1
```
veri-dns denies a name that exists; unbound serves it. Rig restored afterwards.

---

- **Component:** `VeriDNS/Impl/Resolver.lean` `stepAnalyzeResponse` (:434-435), `classifiableB` (:353-358); server selection `VeriDNS/Impl/SList.lean` `bestWithAddress`/`pickBest` (:76-87)
- **Class:** bad-spec — build green, proofs pass, yet the resolver returns an observably wrong answer (denies an existing record). The verification is not load-bearing for this behaviour.
- **Status:** CONFIRMED on the rig — differential vs unbound reproduced deterministically.
- **Relation to 041:** strengthens finding 041. That finding used a *single* nameserver, where both resolvers ultimately return NODATA (unbound only after 2 retries), so it was scored a robustness coverage-gap. This finding shows the *2-NS delegation* case, where the difference is no longer retry-count but the **final answer**: veri-dns denies a record that exists; unbound serves it.

## Summary

`stepAnalyzeResponse` accepts a wholly-empty NOERROR (ancount = nscount =
arcount = 0, no SOA, no NS) as a final answer on first receipt (:434):

```
else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty then
  .answer (finalizeAnswer s resp) s
```

`classifiableB` (:357) marks any NOERROR classifiable, so the response never
routes back to `.sendQueries` (:388) — there is no throwaway and no failover to
another server in the delegation's SLIST. Because `bestWithAddress` deterministically
picks the *first* SLIST entry that carries an address (`pickBest` keeps the
incumbent on a transmissionCount tie, SList.lean:83-84), whichever nameserver the
parent lists first is the only one veri-dns ever consults for that name. If that
server emits a bare empty NOERROR, veri-dns answers NODATA and stops — even
though a second, healthy nameserver in the same delegation holds the real record.

unbound classifies the bare-empty message as `RESPONSE_TYPE_THROWAWAY`
(`iter_resptype.c`, an=0&&ns=0&&ar=0), does not accept it, and re-queries —
including the *other* nameserver — so it recovers the real answer.

Impact: a single lame/broken nameserver in a multi-NS delegation (a common
real-world condition), or an off-path attacker who wins the RFC 5452 id+port
race with a bare NOERROR (**no SOA required**, unlike the SOA-forge negative-cache
vectors in findings 012/013), makes veri-dns deny the existence of a name that
actually resolves. unbound is immune.

## Reproduction (on the rig)

Two-nameserver delegation for `example.test.`:
- `ns2.example.test` = `10.53.0.13` — lame server, returns a bare empty NOERROR
  (qr=1, aa=1, rcode=0, qdcount=1 echo, an=ns=ar=0) for every query
  (`penn-testing/_vmdns/bare_noerror.py 10.53.0.13`).
- `ns.example.test`  = `10.53.0.12` — the real leaf nsd (`host.example.test A 10.53.0.101`).

`test.zone` was rewritten to list **ns2 first** in the delegation (so the
referral's authority section, and hence veri-dns's SLIST, has the lame server at
the front):

```
example             IN NS ns2.example.test.
example             IN NS ns.example.test.
ns2.example.test.   IN A 10.53.0.13
ns.example.test.    IN A 10.53.0.12
```

Both resolvers cold-cache (unbound flushed via restart, veri-dns restarted), then
`dig host.example.test A`, 3 iterations:

```
iter 1  VERIDNS[status: NOERROR ANSWER: 0]  UNBOUND[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits=1
iter 2  VERIDNS[status: NOERROR ANSWER: 0]  UNBOUND[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits=2
iter 3  VERIDNS[status: NOERROR ANSWER: 0]  UNBOUND[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits=2
```

- **veri-dns**: every time returns `NOERROR / ANSWER: 0` (spurious NODATA) for
  `host.example.test`, which **exists** (A = 10.53.0.101). The responder log shows
  it queried `10.53.0.13` exactly once and never tried `10.53.0.12`.
- **unbound**: every time returns the real `A 10.53.0.101`.

unbound recovers *even when it itself queries the lame server first* — a
unbound-only probe (cache flushed each round) shows it hits `10.53.0.13` in every
round yet still returns the A:

```
unbound iter 1: answer=[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits-this-iter=1
unbound iter 2: answer=[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits-this-iter=1
unbound iter 3: answer=[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits-this-iter=1
unbound iter 4: answer=[host.example.test. 3600 IN A 10.53.0.101]  bare.13-hits-this-iter=1
```

i.e. unbound throws the bare NOERROR away and fails over to `10.53.0.12`; veri-dns
accepts it and denies the name.

### Control: single-server case matches 041 (both return NODATA)

With the lame responder as the *sole* leaf server (bound on `10.53.0.12`, leaf
nsd stopped), both resolvers return NODATA (unbound after 2 retry datagrams,
veri-dns after 1). This is the weaker scenario 041 documented and is why 041 was
scored coverage-gap. The 2-NS delegation above is what turns it into an
observably wrong answer.

Full rig restored afterward (original `test.zone`, `10.53.0.13` removed, leaf
nsd + both resolvers back to baseline; `host.example.test A` = 10.53.0.101 on
both).

## Why bad-spec (verification not load-bearing)

The build is green and every RFC-semantic theorem passes, yet the resolver
returns a wrong answer. Accepting the bare NOERROR at Resolver.lean:434 without
consulting the remaining SLIST servers is behaviour the spec permits: there is no
theorem requiring failover across a delegation's nameservers on an
uninformative/empty response, and (as in 041) the empty message carries no SOA so
`storeNegativeIfCacheable` no-ops and nothing is proven about it. The
verification therefore does not constrain the one place where veri-dns diverges
observably from a correct resolver. Compare finding 035 (multihomed-NS failover
broken): the same missing-failover shape, here triggered by an empty NOERROR
rather than a network error.

## Citations

- unbound `iterator/iter_resptype.c`: an=0 && ns=0 && ar=0 → `(*empty_nodata_found)++`,
  `RESPONSE_TYPE_THROWAWAY` (do not accept a bare empty NOERROR).
- unbound `iterator/iterator.c`: throwaway → try next target / next server.
- unbound `iterator/iterator.h`: `EMPTY_NODATA_RETRY_COUNT` = 2.
- RFC 1034 §5.3.3 / RFC 2308: a resolver holds the full SLIST of a delegation's
  servers and should not conclude a name does not exist from one uninformative
  reply while other authoritative servers remain untried.
