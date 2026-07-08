# 026 — Upstream REFUSED/FORMERR/NOTIMP carrying an authority record aborts the whole resolution with SERVFAIL — no failover to sibling nameservers

- **Classification:** impl-bug (observable client-visible divergence from unbound)
- **Component:** `VeriDNS/Impl/Resolver.lean:388-421` (`stepAnalyzeResponse`), terminal `.error "4b: no NS records in authority"` at :421; delivered as SERVFAIL via `VeriDNS/Impl/Server.lean:426-427` → `replyForResolution` error→serverFailure.
- **Trigger set:** an upstream answer with `rcode ∈ {1 FORMERR, 4 NOTIMP, 5 REFUSED}`, empty ANSWER, and a **non-empty AUTHORITY that is not a followable delegation** (e.g. a lone SOA — the classic lame-server shape).

## Summary

When one of several nameservers for a zone answers with a non-NOERROR/NXDOMAIN
rcode (REFUSED/FORMERR/NOTIMP) **and** includes an authority record that is not
a strictly-closer in-bailiwick NS (a lone SOA is the common case), veri-dns
terminates the entire resolution with SERVFAIL instead of trying the remaining
nameservers in the SLIST. A single lame/misconfigured/malicious authoritative
server therefore denies the whole name, even when a sibling NS would answer
correctly. unbound throws the response away (`RESPONSE_TYPE_THROWAWAY`,
`iterator/iter_resptype.c`) and fails over to the next server.

## Why (code path)

In `stepAnalyzeResponse` (Resolver.lean:388):

- `resp.header.rcode == serverFailure || !classifiableB resp` → retry (`goto sendQueries`).
  `classifiableB` (line 353) is **true** whenever `!resp.authority.isEmpty`, so a
  REFUSED/FORMERR/NOTIMP response that carries a SOA is "classifiable" and does
  **not** take the retry path.
- The `!answersQueryB && !nameError && answer.isEmpty && !authority.isEmpty`
  block (line 391) is entered. Its delegation sub-branch requires
  `rcode == noError` (line 398) → skipped; its NODATA sub-branch also requires
  `rcode == noError` (line 419) → skipped; control falls to
  `.error "4b: no NS records in authority"` (line 421).
- That `.error` propagates `Resolver.resume` → `afterResume` (Server.lean:281,
  `.finished (.error …)`) → SERVFAIL to the client, **without** consulting the
  other SLIST servers.

The upstream gate `unfollowableDelegationB` (Server.lean:144) only fires on
delegation-**shaped** responses (NS present in authority), so a SOA-only
authority slips straight through to `afterResume`. And `dropIfBizarre`
(Server.lean:267) only removes the server / enables retry when
`rcode == serverFailure || !classifiableB` — again false for REFUSED+SOA.

## Reproduction on the rig

Setup: `example.test.` delegated by the TLD to **two** nameservers, both glued,
lame listed first:

```
example           IN NS ns1.example.test.   ; 10.53.0.13  LAME (tried first)
example           IN NS ns.example.test.    ; 10.53.0.12  GOOD authoritative leaf
ns1.example.test. IN A  10.53.0.13
ns.example.test.  IN A  10.53.0.12
```

`ns1` (10.53.0.13) runs `lame.py` (pure-stdlib UDP responder,
`penn-testing/_vmdns/lame.py`): every query → `rcode=REFUSED, AA=0, ANSWER=0,
AUTHORITY=[SOA example.test.], ADDITIONAL=0`. `ns` (10.53.0.12) is the real
authoritative leaf nsd. Both resolver caches flushed before each query.

Lame server (direct probe):
```
;; ->>HEADER<<- opcode: QUERY, status: REFUSED, id: 6791
;; flags: qr; QUERY: 1, ANSWER: 0, AUTHORITY: 1, ADDITIONAL: 0
;; AUTHORITY SECTION:
example.test.  3600  IN  SOA  ns.example.test. hostmaster.example.test. 1 3600 900 604800 3600
```

Query `host.example.test A`:

| resolver | rcode = 5 (REFUSED) | rcode = 1 (FORMERR) | rcode = 4 (NOTIMP) |
|----------|---------------------|---------------------|--------------------|
| **veri-dns** @10.53.0.2:5300 | **SERVFAIL** | **SERVFAIL** | **SERVFAIL** |
| **unbound** @10.53.0.3:5301 | NOERROR, A 10.53.0.101 | NOERROR, A 10.53.0.101 | NOERROR, A 10.53.0.101 |

veri-dns log (REFUSED run) — it queries the lame `ns1`, gets `rcode=5 ns=1`, and
gives up without ever trying `ns.example.test`:
```
[veri-dns] query host.example.test → a.tld.test (fuel 38)
[veri-dns] resp: rcode=0 an=0 ns=2 ar=2 tc=0x0
[veri-dns] query host.example.test → ns1.example.test (fuel 37)
[veri-dns] resp: rcode=5 an=0 ns=1 ar=0 tc=0x0
[veri-dns] SERVFAIL: 4b: no NS records in authority
```

### Control — isolates the trigger to the non-empty authority

Same topology, but the lame server sends REFUSED with an **empty** authority
(`--no-soa`, `AUTHORITY: 0`). Now `classifiableB` is false, the retry path fires,
and veri-dns fails over correctly:
```
[veri-dns] query host.example.test → ns1.example.test (fuel 37)
[veri-dns] resp: rcode=5 an=0 ns=0 ar=0 tc=0x0
[veri-dns] query host.example.test → ns.example.test (fuel 36)
[veri-dns] resp: rcode=0 an=1 ns=1 ar=1 tc=0x0
```
veri-dns: NOERROR, A 10.53.0.101 — identical to unbound. The single differentiator
is whether the throw-away response carries an authority record.

## Impact

Availability / robustness. Any one lame server (REFUSED/FORMERR/NOTIMP + SOA is a
widespread real-world misconfiguration) among a zone's nameservers makes veri-dns
deny the name, and a malicious in-bailiwick nameserver can force a targeted
SERVFAIL denial-of-service by returning REFUSED+SOA. A correct iterative resolver
must treat these rcodes as a failed server and move on.

## Citation

- **unbound** `iterator/iter_resptype.c` — `response_type_from_server`: any rcode
  other than NOERROR/NXDOMAIN is `RESPONSE_TYPE_THROWAWAY`; the iterator then tries
  the next target in the delegation point rather than failing the query.
- **RFC 1034 §5.3.3 / RFC 1035 §7.2** — the resolver keeps a SLIST of all
  nameservers for the zone and is expected to try alternatives when one fails to
  give a useful answer; a server-side error from one nameserver is not a verdict
  on the name.

## Repro artifacts

- `penn-testing/_vmdns/lame.py` — lame UDP responder (`--rcode`, `--no-soa`).
- `penn-testing/_vmdns/nsd/zones/test-lame.zone` — two-NS delegation (lame first).
- Both staged into the VM at `/opt/dnsenv/`; lame server run as transient unit
  `veridns-lame` in the `auth` netns on 10.53.0.13:53.
