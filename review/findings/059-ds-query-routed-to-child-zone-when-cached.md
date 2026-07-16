# 059: DS query at a zone cut is routed to the CHILD zone's servers once the child NS RRset is cached

**Status:** CONFIRMED (runtime, wire-level, differential vs unbound)
**Location:** `VeriDNS/Impl/Resolver.lean:295-326` (`stepFindServers`), reported at :459
**Class:** impl-bug (cache-state-dependent zone-cut confusion for QTYPE=DS)

## Summary

DS records reside on the **parent** side of a zone cut (RFC 4035 §3.1.4.1: "The DS
resource record set resides at the parent"; RFC 4034 §5: DS "is stored at the
delegation point in the parent zone"). A resolver must therefore direct
`<child> DS` queries to the **parent** zone's servers — the child is never
authoritative for its own DS and cannot authoritatively deny it.

`stepFindServers` selects upstream servers by walking the cache for the closest
enclosing NS RRset of the qname (`walkNs s.resources.sname ...`) and never
consults the qtype. On a cold cache the walk stops at the parent (`test.`)
delegation and the answer is correct. But after *any* query that caches the
child's own NS RRset (`example.test NS`), the walk matches the child zone
itself and the DS query is sent to the child's authoritative server, which
returns NODATA with the **child** SOA in AUTHORITY.

Unbound returns the parent SOA in every cache state (it special-cases DS by
resolving it from one label up).

## Reproduction (rig, 203.0.113.0/24; veri-dns @203.0.113.2:5300, unbound @203.0.113.3:5301)

### Cold cache — parity (both parent SOA)

```
systemctl restart veridns-verid veridns-ref; sleep 2
ip netns exec attacker dig @203.0.113.2 -p 5300 example.test DS
  ;; AUTHORITY: TeSt. 3600 IN SOA a.tld.TeSt. hostmaster.tld.TeSt. 1 3600 900 604800 3600
ip netns exec attacker dig @203.0.113.3 -p 5301 example.test DS
  ;; AUTHORITY: test. 3600 IN SOA a.tld.test. hostmaster.tld.test. 1 3600 900 604800 3600
```

### Warm cache — divergence

```
systemctl restart veridns-verid veridns-ref; sleep 2
ip netns exec attacker dig @203.0.113.2 -p 5300 example.test A +short   # 203.0.113.100 (warms child NS)
ip netns exec attacker dig @203.0.113.3 -p 5301 example.test A +short   # 203.0.113.100

ip netns exec attacker dig @203.0.113.2 -p 5300 example.test DS
  ;; AUTHORITY: exaMPlE.TesT. 3600 IN SOA ns.exaMPlE.TesT. hostmaster.exaMPlE.TesT. ...   # CHILD SOA — WRONG
ip netns exec attacker dig @203.0.113.3 -p 5301 example.test DS
  ;; AUTHORITY: test. 3600 IN SOA a.tld.test. hostmaster.tld.test. ...                    # parent SOA — correct
```

Warming via NXDOMAIN (`nonexist.example.test A`) triggers the same divergence.

### Wire-level proof of the misrouted upstream query

tcpdump in the `verid` netns during the DS query:

```
# warm cache: DS query goes to the CHILD auth server (203.0.113.12 = example.test.)
20:16:23 v-verid Out IP 203.0.113.2.42997 > 203.0.113.12.53: 12128 [1au] DS? EXaMPle.TesT.
20:16:23 v-verid In  IP 203.0.113.12.53 > 203.0.113.2.42997: 12128*- 0/1/1

# cold cache: DS query goes to the PARENT auth server (203.0.113.11 = test. tld)
20:16:45 v-verid Out IP 203.0.113.2.45572 > 203.0.113.11.53: 2739 [1au] DS? EXaMPlE.tEst.
```

## Impact

- Owner/TTL divergence from unbound on the negative-DS SOA in every warm-cache state.
- For a DNSSEC validator this is load-bearing: a negative DS proof must come from
  the parent zone (RFC 4035 §3.1.4.1); a child-zone SOA/NSEC cannot prove the
  absence of a DS and would make insecure-delegation proofs unverifiable. The
  child also cannot be trusted to answer its own DS (a compromised/rogue child
  could deny or forge its own security status).

## Fix sketch

In server selection, when `stype == DS (43)` and the qname equals a zone apex
known to the cache (i.e. the walk would stop exactly at `sname`), resolve via
the servers for the parent (strip one label before `walkNs`), as unbound does
(`iterator.c`, DS handling in `processDSNSFind`).
