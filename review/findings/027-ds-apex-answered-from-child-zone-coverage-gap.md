# 027: DS query at a zone apex is answered from the CHILD zone, not the parent side of the cut

**Classification:** coverage-gap (RFC 4034 §5 / RFC 4035 §3.1.4.1 not modeled; observable wrong-zone negative answer)

**Location:** `VeriDNS/Impl/Resolver.lean` — `stepFindServers` / `walkNs` (lines ~296-345)

## Summary

DS records live on the **parent** side of a zone cut (RFC 4034 §5: "The DS
resource record ... appears only on the upper (parental) side of a
delegation"; RFC 4035 §3.1.4.1 describes the special DS-at-delegation server
selection a resolver/server must apply). veri-dns has no DS special case:
`walkNs` starts the NS walk at the qname itself for every qtype, so for a DS
query at a delegation point it finds the child's own NS RRset and sends the
query to the **child's** authoritative server. The child has no DS at its
apex and returns NODATA with its own apex SOA — a negative proof from the
wrong zone. A DNSSEC-aware downstream asking veri-dns for a delegation's DS
receives a denial that the child could never legitimately authenticate
(only the parent can deny/assert the child's DS).

## Reproduction (rig, 2026-07-08)

Cold cache (`review/env/restart-verid.sh`), then:

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 example.test DS +noall +comments +authority
;; ->>HEADER<<- ... status: NOERROR ... ANSWER: 0, AUTHORITY: 1
;; AUTHORITY SECTION:
example.test.  3600  IN  SOA  ns.example.test. hostmaster.example.test. 1 3600 900 604800 3600
```

Reference (unbound):

```
$ ip netns exec attacker dig @10.53.0.3 -p 5301 example.test DS +noall +comments +authority
;; ->>HEADER<<- ... status: NOERROR ... ANSWER: 0, AUTHORITY: 1
;; AUTHORITY SECTION:
test.          3600  IN  SOA  a.tld.test. hostmaster.tld.test. 1 3600 900 604800 3600
```

verid attaches the **child** apex SOA (`example.test.`); unbound attaches the
**parent** SOA (`test.`), because the DS NODATA proof belongs to the parent
zone. Deterministic; identical warm-cache (TTL decays: `3574 IN SOA
ns.example.test. ...` on repeat).

Control — non-delegation name inside the zone agrees on both servers:

```
$ dig @10.53.0.2 -p 5300 host.example.test DS  ->  example.test. SOA   (verid)
$ dig @10.53.0.3 -p 5301 host.example.test DS  ->  example.test. SOA   (unbound)
```

Upstream capture proves the wrong-zone descent (tcpdump in netns `verid`
during the cold-cache query; 10.53.0.11 = tld/parent, 10.53.0.12 = leaf/child):

```
15:13:43.726431 v-verid Out IP 10.53.0.2.53591 > 10.53.0.12.53: 32366 DS? example.test. (30)
15:13:43.726517 v-verid In  IP 10.53.0.12.53 > 10.53.0.2.53591: 32366*- 0/1/0 (80)
```

The DS query goes to **10.53.0.12** (ns.example.test, the child) instead of
10.53.0.11 (the parent, which holds/denies the DS).

## Code

`stepFindServers.walkNs` (Resolver.lean:296-345) selects servers by walking
up from `s.resources.sname` looking for cached NS RRsets, with no qtype
inspection. For qtype DS at a zone cut the child's NS RRset (cached from the
delegation / prior resolution) matches first, so the query is routed below
the cut. RFC 4035 requires the walk for DS to start at the parent
(equivalently: strip one label from the qname before server selection, or
never use the qname's own zone for a DS query).

## Verification-surface note

`grep -rn 'DNSSEC\|4034\|4035'` over `VeriDNS/Spec/` shows no modeling of
DS parent-side semantics (only an incidental comment in
NetworkSemantics.lean:2040). RFC 4034/4035 are outside the verified spec, so
no theorem could have caught this: it is a coverage gap, not a violated
proof. The RFC 1034 sname-driven server-selection algorithm that IS modeled
is faithfully implemented — DNSSEC changed the rule for DS specifically.

## References

- RFC 4034 §5: DS RR "appears only on the upper (parental) side of a delegation."
- RFC 4035 §3.1.4.1: "Because the DS RR appears only on the parental side of a
  zone cut ... a resolver targeting a DS query at the child's apex ... the
  child's server cannot generate an authoritative answer for the DS RRset";
  special server-selection required.
- Unbound implements this via `iter_operate`'s DS-parent special case
  (`processDSNSFind` in iterator.c), producing the parent-zone SOA observed above.
