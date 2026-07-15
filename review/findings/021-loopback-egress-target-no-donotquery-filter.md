# 021 — No do-not-query filter on upstream targets: veri-dns emits real DNS queries to loopback (127.0.0.0/8) glue addresses

- **Severity:** medium (query-redirection / SSRF & reflection egress primitive; divergence from **default** unbound)
- **Classification:** coverage-gap (missing egress-target defense; no RFC MUST is violated, but it is a default-behavior divergence from unbound)
- **Status:** CONFIRMED on the running rig
- **Component:** `VeriDNS/Impl/Resolver.lean:310-322` (referral glue extraction), `VeriDNS/Impl/Server.lean:395-404` (`ipv4ToAddr` → `forwardQuery`)
- **Reference:** unbound `iterator/iter_donotq.c` (default `127.0.0.0/8` + `::1`), `util/config_file.c` `do-not-query-localhost=yes` default, `iterator/iter_utils.c` `donotq_lookup` → skip server.

## Claim

Every upstream server address veri-dns queries comes from either referral glue
(`Resolver.lean:310-322`) or a glueless A-record resolution. **None** of these
paths vet the *address range*: the 4 raw rdata bytes become a `BitVec 32`, go
into the SLIST, then straight into `ipv4ToAddr` (fixed port 53) → `forwardQuery`.
`respInBailiwick` / `bailiwickRaws` check only NS/glue *owner names*, never the
address. A repo-wide grep for egress-target vetting is empty:

```
grep -rniE '127|loopback|donotq|private|isLoopback|do-not-query' VeriDNS/Impl/
# -> only Cache.lean 'boundFifo' / a 'private' Lean keyword; no address filtering
```

Consequently an attacker-controlled (or attacker-influenced) zone that emits
in-bailiwick glue `ns.sub.<zone> A 127.0.0.1` makes veri-dns emit an **actual
DNS query to 127.0.0.1:53** — its own loopback / any loopback-bound service.
This is a query-redirection / SSRF & reflection primitive.

This is the **egress-target** analog of finding 016 (which is about loopback
*answer rdata* cached and served to clients — a different code path, different
unbound defense `priv_rrset_bad`). It is **more severe** than 016 on one axis:
unbound's egress defense `do-not-query-localhost` is **ON by default**, whereas
016's `private-address` strip is **OFF by default**. So this is a divergence from
a *default* unbound, not only a hardened one.

## Reproduction (on the rig)

Added a loopback-glue delegation to the leaf zone `example.test.` (served by
`nsd` @10.53.0.12), then bumped SOA serial and restarted `veridns-auth-leaf`:

```
sub     IN NS  ns.sub.example.test.
ns.sub  IN A   127.0.0.1
```

Leaf now returns the referral directly (`dig +norec @10.53.0.12 www.sub.example.test A`):

```
;; AUTHORITY SECTION:
sub.example.test.     3600 IN NS ns.sub.example.test.
;; ADDITIONAL SECTION:
ns.sub.example.test.  3600 IN A  127.0.0.1
```

### veri-dns — emits real queries to 127.0.0.1:53

`tcpdump -n -i lo` inside the `verid` netns while querying
`dig @10.53.0.2 -p 5300 www.sub.example.test A`:

```
14:20:33.756293 IP 127.0.0.1.58656 > 127.0.0.1.53: 1244 A? www.sub.example.test. (38)
14:20:35.763025 IP 127.0.0.1.52877 > 127.0.0.1.53: 1244 A? www.sub.example.test. (38)
14:20:37.810789 IP 127.0.0.1.40082 > 127.0.0.1.53: 1244 A? www.sub.example.test. (38)
```

veri-dns took the loopback glue as an upstream and fired three real UDP queries
at 127.0.0.1:53 (its own loopback).

### unbound — DEFAULT config refuses (zero loopback egress, SERVFAIL)

The rig's `unbound.conf` had `do-not-query-localhost: no` (added only so unbound
can talk to on-link private/fake-root upstreams). With that override, unbound
*also* queries 127.0.0.1 — an unfaithful comparison for this defense. Flipping it
to the **unbound default** `do-not-query-localhost: yes` and restarting
`veridns-ref`:

`tcpdump -n -i lo` inside the `unbound` netns during
`dig @10.53.0.3 -p 5301 www.sub.example.test A`:

```
(no packets — unbound never sends to 127.0.0.1)
```

Client result:

```
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 1849
```

Default unbound puts 127.0.0.0/8 on the do-not-query list, skips the only
available server, and SERVFAILs instead of emitting to loopback.

## Impact

An in-bailiwick glue record (or a glueless NS whose A record resolves) pointing
at `127.0.0.1` (or any 127/8, or by extension any address the operator would not
want probed) turns veri-dns into an SSRF / reflection engine: it will send
attacker-shaped DNS queries to loopback-bound services in its own netns/host.
Only the glue *owner name* is bailiwick-checked; the *address* is never vetted.

## Fix direction

Add an egress-target filter analogous to unbound's `iter_donotq`: before
`ipv4ToAddr`/`forwardQuery`, reject SLIST addresses in `127.0.0.0/8` (and `::1`,
and ideally a configurable do-not-query list) — dropping the server and
continuing to the next, SERVFAILing if none remain. The check belongs where glue
becomes an upstream address (`Resolver.lean:310-322` glue extraction and the
glueless `addAddress` path), covering both entry points into the SLIST.

## Rig state

Both the leaf zone and `unbound.conf` were restored to their originals after the
experiment (unbound back to `do-not-query-localhost: no`, leaf zone back to the
committed form); `veridns-ref` and `veridns-auth-leaf` restarted; both resolvers
re-verified answering `host.example.test A 10.53.0.101`.
