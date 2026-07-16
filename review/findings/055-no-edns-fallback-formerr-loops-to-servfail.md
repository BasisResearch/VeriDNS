# 055 — No EDNS fallback: an EDNS-intolerant upstream (FORMERR to an OPT query) never gets a plain-DNS retry → SERVFAIL

**Status:** CONFIRMED (unbound disagrees on the identical path against identical data, cold caches on both)
**Component:** `VeriDNS/Impl/Resolver.lean` — `buildSubQuery` (468–486), `classifiableB` (356), `stepAnalyzeResponse` (391)
**Severity:** interop / availability — names served only by EDNS-intolerant nameservers are unresolvable by veri-dns, resolvable by unbound.

## Summary

Every upstream sub-query veri-dns emits is built by `buildSubQuery`, which
**unconditionally** sets `arcount = 1` and
`additional := #[Edns.optRRBytes Edns.advertisedUdpSize]` — i.e. every query and
every retry carries an OPT RR. A legacy authoritative server or middlebox that
cannot parse EDNS answers such a query with FORMERR (rcode 1). veri-dns has **no
plain-DNS fallback path**: it never strips the OPT and re-sends without EDNS, so
it can never resolve a name whose nameservers are EDNS-intolerant. It returns
SERVFAIL.

`classifiableB` treats a FORMERR with empty answer/authority and `tc=0` as
UNclassifiable, so `stepAnalyzeResponse` takes the `!classifiableB → .goto
.sendQueries` branch and re-queries — but the re-query goes through
`buildSubQuery` again and re-attaches the OPT, reproducing the same FORMERR.
There is no branch anywhere that removes the OPT RR.

unbound implements the RFC 6891 §6.2.2 interop requirement
(`services/outside_network.c`, `serviced_query_UDP_EDNS` →
`serviced_query_UDP_EDNS_fallback`): on FORMERR/NOTIMP/malformed-EDNS to an EDNS
query it re-sends the same query **without** EDNS and caches noEDNS for that
server. It therefore resolves the name.

## Reproduction

Rig: `review/ENV.md`. Fake hierarchy root/tld/leaf on 203.0.113.10/.11/.12.
I replaced the leaf authoritative server (`example.test.` on 203.0.113.12:53)
with an **EDNS-intolerant** responder that mimics a legacy middlebox:

- query **with** an OPT RR (`arcount > 0`) → FORMERR (rcode 1), no OPT echoed;
- query **without** OPT (`arcount == 0`) → proper authoritative answer.

Responder: `penn-testing/_vmdns/ednsbad_leaf.py` (run in the `auth` netns bound
to 203.0.113.12:53, replacing `veridns-auth-leaf`). Direct probe confirming the
responder behaves like a real EDNS-intolerant server:

```
$ dig @203.0.113.12 -p53 example.test A +edns=0    -> status: FORMERR
$ dig @203.0.113.12 -p53 example.test A +noedns     -> status: NOERROR, A 203.0.113.100
```

Differential (both resolvers restarted for cold caches — rule 3):

```
===== veri-dns (SUT)  @203.0.113.2:5300 =====
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 9438
;; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0

===== unbound (oracle) @203.0.113.3:5301 =====
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 53536
;; ANSWER SECTION:
example.test.   3600  IN  A  203.0.113.100
```

Wire evidence from the responder log, per resolver:

```
# veri-dns query -> ONE query, carries OPT, gets FORMERR, no plain-DNS retry:
[ednsbad] FORMERR (had OPT, arcount=1) -> ('203.0.113.2', 37558) qtype=1 b'\x07ExAmPlE\x04TeST\x00'
   (FORMERR count=1, no-OPT ANSWER count=0)   => SERVFAIL

# unbound query -> OPT query FORMERRs, then RETRIES the SAME query WITHOUT OPT:
[ednsbad] FORMERR (had OPT, arcount=1)  -> ('203.0.113.3', 45148) qtype=1 b'\x07example\x04test\x00'
[ednsbad] ANSWER (no OPT)               -> ('203.0.113.3', 17339) qtype=1 b'\x07example\x04test\x00'
   (FORMERR count=1, no-OPT ANSWER count=1)   => NOERROR / A 203.0.113.100
```

(The `ExAmPlE` casing on veri-dns's query is its 0x20 DNS-cookie randomisation —
unrelated; the point is the OPT RR is present on it and every retry.)

## Root cause

`buildSubQuery` (Resolver.lean:475–486):

```lean
some {
  header := { origQuery.header with ... arcount := 1 }
  question := #[subQuestion s.resources.sname revealed qu]
  answer := #[]; authority := #[]
  additional := #[Edns.optRRBytes Edns.advertisedUdpSize] }   -- OPT always attached
```

No resolver state records "this server is EDNS-intolerant, drop the OPT", and no
`stepAnalyzeResponse` branch produces a no-OPT re-query. FORMERR flows into
`!classifiableB → .goto .sendQueries`, which rebuilds an identical OPT-bearing
query; with a single leaf server the retries exhaust and veri-dns SERVFAILs.

## Citation

- RFC 6891 §6.2.2: "If [the responder] does not support EDNS ... the requestor
  SHOULD retry the query without EDNS." Fallback is mandatory for interop.
- unbound `services/outside_network.c` `serviced_query_UDP_EDNS_fallback`:
  FORMERR/NOTIMP/malformed-EDNS to an EDNS query triggers a no-EDNS re-send,
  caching noEDNS per server.

## unboundDiffers

**Yes.** Identical path, identical data, cold caches: unbound returns
NOERROR/203.0.113.100 via a no-EDNS fallback; veri-dns returns SERVFAIL and never
strips the OPT. Not the DNS trust model — a missing interop fallback.

## Cleanup

Responder stopped, `veridns-auth-leaf` (nsd) restarted, both resolvers
restarted; baseline `example.test A -> 203.0.113.100` restored. No tracked
source files were edited.
