# 013 — Negative-response SOA is cached/served with an out-of-bailiwick owner (live wire reproduction of the RFC 2308 §3 gap)

- **Classification:** bad-spec (build GREEN, behaviour observably wrong on the wire).
- **Severity:** high — RFC 2308 §3 requires the negative-proof SOA to be the SOA
  of the zone that owns the queried name; veri-dns accepts, caches (up to the
  3 h cap), and replays an SOA whose owner is an arbitrary, unrelated name.
- **On/off-path:** on-path / rogue-upstream. A server reached via the delegation
  chain (here a server delegated `victim.test.`, or via finding 005's lenient
  answer path any server in the chain) needs no spoofing/txid guessing.
- **Relation to 012:** same root cause as finding 012
  (`012-neg-soa-owner-forge-badspec.md`), which proved via a source *mutation*
  that nothing in the verification constrains `NegativeEntry.soa`'s owner. This
  finding reproduces the identical defect **on the running rig with the
  unmodified shipped binary** — a real rogue authoritative server, a real
  NXDOMAIN carrying a foreign SOA, and a differential against unbound — so the
  spec gap is demonstrated end-to-end, not just by mutation.

## Root cause (code)

`extractSoaNegative` (`VeriDNS/Impl/Server.lean:70-82`) selects the first
authority-section record with `type == 6` and decodes it as the negative-proof
SOA **with no comparison of the SOA owner name to the query name**.
`storeNegativeIfCacheable` (`:442-458`) then caches a negative entry keyed on the
client qname together with that SOA and its (attacker-influenced, MINIMUM-capped)
TTL; `DnsCache.lookupNegativeSoa` / `NegativeEntry.authority`
(`VeriDNS/Impl/Cache.lean:148-165`) replay exactly that SOA in the authority
section of every future NXDOMAIN/NODATA answer. Because a negative response is
not `delegationShapedB` (`Server.lean:117-121`, which requires
`!(rcode == nameError)`), the IO-loop bailiwick gate
`unfollowableDelegationB` (`Server.lean:420,144-146`) is bypassed — the only
`respInBailiwick` check is wired solely to referral-shaped responses. There is no
check that the SOA owner is an ancestor-or-equal of the qname.

## Reproduction (on the rig)

**Malicious upstream.** `badauth.py` (staged at `/opt/dnsenv/badauth.py`, run in
the `auth` ns bound to `10.53.0.20:53`) answers every query with
`rcode=NXDOMAIN, AA=1`, no answer, and one authority SOA owned by
`poison.attacker.test.` (MINIMUM=10800, TTL=10800, no NS). The tld zone
(`/opt/dnsenv/nsd/zones/test.zone`) was given a delegation
`victim IN NS ns.victim.test.` / `ns.victim.test. IN A 10.53.0.20`, so the
resolver reaches `10.53.0.20` legitimately via the delegation chain
(root → tld referral to `victim.test.` NS).

Direct check — the rogue server emits an out-of-zone SOA:

```
$ dig @10.53.0.20 -p53 leaf.victim.test A +norecurse
;; ->>HEADER<<- status: NXDOMAIN; ANSWER: 0, AUTHORITY: 1
;; AUTHORITY SECTION:
poison.attacker.test.  10800  IN  SOA  ns.poison.attacker.test. hostmaster.poison.attacker.test. 1 3600 900 604800 10800
```

### veri-dns — POISONED (accepts, serves, and caches the out-of-zone SOA)

```
$ ip netns exec attacker dig @10.53.0.2 -p5300 leaf.victim.test A     # query 1 (upstream)
;; ->>HEADER<<- status: NXDOMAIN; ANSWER: 0, AUTHORITY: 1
;; AUTHORITY SECTION:
poison.attacker.test.  10800  IN  SOA  ns.poison.attacker.test. ... 10800

$ ip netns exec attacker dig @10.53.0.2 -p5300 leaf.victim.test A     # query 2 (cache)
;; ->>HEADER<<- status: NXDOMAIN; ANSWER: 0, AUTHORITY: 1
;; AUTHORITY SECTION:
poison.attacker.test.  10779  IN  SOA  ns.poison.attacker.test. ... 10800
```

`poison.attacker.test.` is **not** an ancestor of `leaf.victim.test`. On query 2
the TTL has decremented (10800 → 10779) and a simultaneous
`tcpdump -i v-verid host 10.53.0.20 or host 10.53.0.11` captured **zero** upstream
packets — the forged SOA is served straight from the negative cache and will be
for up to the 10800 s (3 h) cap.

### unbound — CLEAN (scrubs the out-of-zone SOA)

```
$ ip netns exec attacker dig @10.53.0.3 -p5301 leaf.victim.test A
;; ->>HEADER<<- status: NXDOMAIN; ANSWER: 0, AUTHORITY: 0        <- SOA stripped
```

unbound follows the same delegation, receives the same NXDOMAIN, and
`scrub_sanitize` (`iterator/iter_scrub.c:1098`,
`if(!pkt_sub(pkt, rrset->dname, zonename))`) removes the SOA whose owner is not a
subdomain of the tracked zone `victim.test.`. It neither serves nor caches the
poison SOA (AUTHORITY: 0 on both the first and repeated query).

## Why verification did not catch it

Per finding 012: the abstract negative-cache entry (`NegRR`,
`VeriDNS/Spec/NetworkSemantics.lean:512`) carries only `qname/qtype/insertedAt/ttl`
— no SOA owner or rdata — and `αNegRR` (`VeriDNS/Proof/Refinement.lean:2844`)
ignores the concrete `NegativeEntry.soa` entirely. No theorem STATEMENT constrains
the owner of the served SOA, so the green build says nothing about it.

## RFC / reference citations

- RFC 2308 §3: the SOA in the authority section of a negative answer is the SOA
  of the zone that owns the queried name; its apex must be an ancestor-or-equal
  of the queried name.
- RFC 5452 §6: a resolver must accept only expected data.
- unbound `iterator/iter_scrub.c` `scrub_sanitize` (out-of-zone RRsets, SOA
  included, are dropped).

## Fix sketch

In `extractSoaNegative` / `storeNegativeIfCacheable`, reject (do not cache) a
negative response whose SOA owner is not an ancestor-or-equal of the qname (and
within the delegation point the server was selected for) — the same
ancestor/suffix check `respInBailiwick` already applies to NS owners on the
referral path. Extend `NegRR` to carry the SOA owner and add a negative-caching
soundness obligation binding it, then re-prove.

## Artifacts

- Malicious server: `penn-testing/_vmdns/badauth.py` (VM: `/opt/dnsenv/badauth.py`).
- Delegation: `victim.test.` added to `penn-testing/_vmdns/nsd/zones/test.zone`.
- Impl paths: `VeriDNS/Impl/Server.lean:70-82,442-458,117-121,144-146,420`;
  `VeriDNS/Impl/Cache.lean:148-165`.
