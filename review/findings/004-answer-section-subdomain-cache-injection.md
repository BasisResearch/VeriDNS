# 004 — Answer-section caching admits any subdomain of the query name (occluded/delegated-child cache injection)

- **Severity:** high (cache poisoning / injection — an authoritative server can pre-load or override cache entries for names it should not control).
- **Class:** bad-spec. The Lean model's `Cache.absorb` `keep := isAncestor bw r.owner` (at-or-below the bailiwick) is strictly weaker than unbound's answer rule (owner **==** qname). The implementation (`bailiwickRaws`) faithfully matches the model, so the on-path soundness theorems prove conformance to a spec that *permits* this injection. Build is green; behaviour is observably wrong.
- **On/off-path:** on-path (a malicious/compromised authoritative answer, no spoofing needed).

## Claim

VeriDNS gates every cached answer section only through `bailiwickRaws bw raws`
(`VeriDNS/Impl/Resolver.lean:111`), which keeps a record iff `isAncestorB bw owner`
— owner is at or below `bw`. For the answer-caching paths `bw = s.resources.sname`
(the current query/canonical name), e.g. `Resolver.lean:378` (CNAME chase) and
`Resolver.lean:426` (`answersQueryB` positive answer). `answersQueryB`
(`Resolver.lean:75`) only checks that *some* answer record carries the qtype — no
owner constraint. So a positive authoritative answer for `example.test A` whose
answer section *also* contains `sub.example.test A 6.6.6.6` (a strict subdomain,
hence `isAncestorB` true) is cached at `credAnswer = authoritativeSection`
(`Resolver.lean:180`), the highest non-local rank, and later served from cache.

Unbound instead removes, from the ANSWER section, every RRset whose owner differs
from the (CNAME-chain-updated) qname: `dname_pkt_compare(pkt, sname, rrset->dname)
!= 0 -> remove_rrset` in `scrub_normalize` (`iterator/iter_scrub.c:584`) and again
in `scrub_sanitize` (`iter_scrub.c:1046`).

## Reproduction (on the rig)

A fake authoritative leaf for `example.test.` (staged at
`penn-testing/_vmdns/fakeleaf.py`, run in the `auth` ns bound on the leaf NS
address `10.53.0.12:53`, replacing `veridns-auth-leaf`) answers `example.test/A`
with an injected extra in-bailiwick record and answers everything else honestly:

```
example.test.     3600 IN A 10.53.0.100
sub.example.test. 3600 IN A 6.6.6.6      <-- injected; sub.example.test does NOT exist
```

Any other in-zone name (incl. `sub.example.test`) is answered **NXDOMAIN** with the
zone SOA. Both resolvers' caches were flushed (restart) before the run.

### veri-dns — POISONED

```
# Q1 primes the cache
$ ip netns exec attacker dig +short @10.53.0.2 -p 5300 example.test A
10.53.0.100

# Q2 — never leaves the resolver; served from the injected cache entry
$ ip netns exec attacker dig @10.53.0.2 -p 5300 sub.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 62950
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, ...
;; ANSWER SECTION:
sub.example.test.	3600	IN	A	6.6.6.6
;; Query time: 0 msec
```

### unbound — CLEAN

```
$ ip netns exec attacker dig +short @10.53.0.3 -p 5301 example.test A
10.53.0.100

$ ip netns exec attacker dig @10.53.0.3 -p 5301 sub.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NXDOMAIN, id: 55654
;; AUTHORITY SECTION:
example.test.	3600	IN	SOA	ns.example.test. hostmaster.example.test. 1 ...
```

### Smoking gun — the fake leaf's query log

```
q example.test/1     from 10.53.0.2  (veri-dns Q1)
                     <-- veri-dns NEVER queries sub.example.test: served from poisoned cache
q example.test/1     from 10.53.0.3  (unbound  Q1)
q sub.example.test/1 from 10.53.0.3  (unbound  Q2 -> honest NXDOMAIN)
```

veri-dns cached the injected `sub.example.test A 6.6.6.6` from Q1 and answered Q2
entirely from cache (0 ms, no packet to the server). Unbound scrubbed the injected
record out of Q1's answer, never cached it, and re-resolved Q2 to the truthful
NXDOMAIN.

## Why the verification didn't catch it

`bailiwickRaws` is definitionally the model's `keep := isAncestor bw owner`
(`Resolver.lean:106-114`), and `bw = s.resources.sname` on the answer paths. The
soundness theorems prove the implementation matches this model, so they are green.
The defect is in the specification: at-or-below-bailiwick is the *referral* rule,
not the *answer* rule. A positive answer must additionally require owner name ==
qname (after CNAME chasing); otherwise a server authoritative for a parent zone can
inject records for names below a delegation it does not own ("occluded data"). The
model never uses a per-server `zonename`/delegation-point scrub at all, so the
theorems faithfully certify a rule strictly weaker than unbound's.

## Fix sketch

On the answer-caching paths, restrict the cached answer RRset to owner == the
current canonical name (qname after CNAME chasing) rather than `isAncestorB sname`,
mirroring unbound's `scrub_normalize`/`scrub_sanitize`. CNAME chain targets are
already tracked (`s.cnameChain`, `cnameToChase`), so the canonical owner is
available. This tightening must be reflected in the model's `absorb`/`keep` for the
answer case, and the soundness theorems re-proven against the stronger spec.

## References

- unbound `iterator/iter_scrub.c:584` (`scrub_normalize`), `:1046`
  (`scrub_sanitize`): answer RRsets with owner != qname are removed.
- RFC 5452 §6 (resilience to forged answers; accept only expected records) and RFC
  2181 §5.4.1 (ranking) — cached answer data must be tied to the queried name, not
  merely be in-bailiwick of the answering zone.
- RFC 2181 §5.2/§6 (occluded names): data at a parent that is below a delegation is
  not authoritative and must not be served.

## Artifacts

- Fake leaf server: `penn-testing/_vmdns/fakeleaf.py`
- Impl: `VeriDNS/Impl/Resolver.lean:75,111,378,426`; spec: `Cache.absorb` `keep`.
