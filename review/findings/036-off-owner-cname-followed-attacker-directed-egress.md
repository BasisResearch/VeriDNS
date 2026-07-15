# 036 — Off-owner CNAME in an answer is followed (attacker-directed recursive resolution / egress)

**Severity:** impl-bug (security-relevant divergence from unbound; RFC 1034/2181 CNAME-chain violation)
**Component:** `VeriDNS/Impl/Resolver.lean` — `extractCname` (43–47), `cnameToChase` (80–82),
`stepAnalyzeResponse` CNAME arm (365–385)
**Status:** CONFIRMED by live differential experiment on the rig.

## Summary

`extractCname` returns the rdata of the **first** type-5 (CNAME) record in a response's
answer section with **no check that the record's owner name equals the current query
name** (`s.resources.sname`). `cnameToChase` returns that target whenever the query type
is not directly answered, and `stepAnalyzeResponse` then sets `sname := <target>`, resets
`slist := default`, and relaunches a fresh recursive resolution of the attacker-chosen
target from the root hints. The only pre-chase guard (line 373) tests the CNAME *target*
against the visited set — never the CNAME *owner*.

Consequently an authoritative (or spoofing) server that veri-dns queries for
`example.test A` can reply with a single CNAME whose **owner is an unrelated name**
(`x.attacker.test`) and whose rdata is an **attacker-chosen target** (`probe.attacker.test`).
veri-dns follows it and issues real egress queries for the attacker-named target.

unbound's `scrub_normalize` (iterator/iter_scrub.c:584-591) strips any answer RRset whose
owner != the current chain sname **before** the chain-follow, so unbound never follows an
off-owner CNAME and emits no query for the target.

## Reproduction (live rig)

A rogue authoritative (`review/env/rogue_auth.py`, staged into the VM) replaced the leaf
nsd on `10.53.0.12:53`. It answers `example.test A` with `aa=1, NOERROR, ancount=1`, a
single CNAME RR whose **owner = `x.attacker.test`** (deliberately != `example.test`) and
**rdata = `probe.attacker.test`**; everything else → REFUSED.

Both resolvers were restarted (caches cleared) and queried for `example.test A` while
tcpdump captured their egress.

### veri-dns @10.53.0.2:5300 — FOLLOWS the off-owner CNAME

Client answer: `status: NXDOMAIN` (the NXDOMAIN of the attacker-chosen target
`probe.attacker.test`, not of `example.test` — proof the target was resolved).

Egress capture:
```
Out 10.53.0.2 > 198.41.0.4.53:  A? example.test.
In  198.41.0.4.53 > 10.53.0.2:  0/1/1                 (referral to tld)
Out 10.53.0.2 > 10.53.0.11.53:  A? example.test.
In  10.53.0.11.53 > 10.53.0.2:  0/1/1                 (referral to leaf)
Out 10.53.0.2 > 10.53.0.12.53:  A? example.test.
In  10.53.0.12.53 > 10.53.0.2:  1/0/0 CNAME probe.attacker.test.   <- off-owner CNAME
Out 10.53.0.2 > 10.53.0.11.53:  A? probe.attacker.test.           <- ATTACKER-DIRECTED egress
In  10.53.0.11.53 > 10.53.0.2:  NXDomain
```
The last two lines are the harm: a **new recursive resolution of the attacker-named
`probe.attacker.test`**, driven entirely by the injected off-owner CNAME.

### unbound @10.53.0.3:5301 — STRIPS the off-owner CNAME (reference behaviour)

Client answer: `status: NOERROR, ANSWER: 0`.

Egress capture (received the identical off-owner CNAME, retried once, **never** queried
the target):
```
Out 10.53.0.3 > 10.53.0.12.53:  A? example.test.
In  10.53.0.12.53 > 10.53.0.3:  1/0/0 CNAME probe.attacker.test.  <- same off-owner CNAME
Out 10.53.0.3 > 10.53.0.12.53:  A? example.test.   (retry to same server)
In  10.53.0.12.53 > 10.53.0.3:  1/0/0 CNAME probe.attacker.test.
```
No `A? probe.attacker.test` ever leaves unbound.

## Impact

- **Attacker-directed recursive resolution (SSRF-ish / reconnaissance):** one injected
  off-owner CNAME per hop steers veri-dns to resolve a name the answering server fully
  controls, from the root down. Compounds with the missing do-not-query filter
  (finding 021) and in-bailiwick loopback glue (016).
- **Egress amplification:** each CNAME hop is one extra full resolution, bounded only by
  resolve fuel (64) / IO fuel (40).
- The bogus CNAME is dropped by `bailiwickRaws` before caching and the client-facing
  answer here is NXDOMAIN/empty, so the client is not directly poisoned — the divergence
  is the attacker-directed **egress** itself.

## Root cause / fix direction

`extractCname` / `cnameToChase` must require the CNAME record's **owner** to equal the
current chain name (`s.resources.sname`, updated across each hop) before treating it as a
chain link — the wire-byte analogue of unbound's `dname_pkt_compare(pkt, sname,
rrset->dname) == 0` gate in `scrub_normalize`. As written, only the target is validated
(loop guard, line 373); the owner is never checked.

## Citations

- unbound `iterator/iter_scrub.c:584-591` (`scrub_normalize`): strips answer RRsets whose
  owner != current chain sname before following the CNAME chain.
- RFC 1034 §3.6.2 / RFC 2181 §10.1: a CNAME's owner is the aliased name; a chain follows
  from the owner, not an arbitrary name.

## Artifacts

- `review/env/rogue_auth.py` (staged to `/opt/dnsenv/rogue_auth.py` in the VM).
- Rig restored afterward: leaf nsd recreated, both resolvers verified answering
  `example.test A 10.53.0.100` / `host.example.test A 10.53.0.101`.
