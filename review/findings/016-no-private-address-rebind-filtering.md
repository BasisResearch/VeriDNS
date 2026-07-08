# 016 — No private-address / anti-rebinding filtering: VeriDNS caches and serves loopback (127.0.0.0/8) A rdata from a public zone

- **Severity:** low / info (opt-in hardening gap, not a default-behavior divergence)
- **Classification:** coverage-gap
- **Status:** CONFIRMED on the running rig (clean read after isolating concurrent-agent interference)
- **Component:** `VeriDNS/Impl/Resolver.lean` (answer-section filtering / caching), `VeriDNS/Impl/Server.lean` (A-record extraction)

## Claim

VeriDNS applies **only a name-bailiwick check** to answer records; it performs no
vetting of the *rdata address range*. An A record for a public name whose rdata
falls in loopback (`127.0.0.0/8`), RFC1918, or link-local (`169.254.0.0/16`)
space is cached and returned to the client verbatim. Unbound supports stripping
such answers via `priv_rrset_bad` / the `private-address` option as a
DNS-rebinding defense; VeriDNS has no equivalent capability at all.

This is **low/info** on purpose: unbound ships `private-address` **commented out**
by default (`doc/example.conf.in`), so a default unbound does **not** strip these
either. The divergence exists only against a *hardened* unbound. It is recorded
as a resolver-hardening feature VeriDNS lacks entirely, not a default divergence.

## Source

`VeriDNS/Impl/Resolver.lean`, `bailiwickRaws` — the only filter on answer rdata is
the owner-*name* ancestor check; rdata is never inspected:

```
def bailiwickRaws [RRParse RR] (bw : ByteArray) (raws : Array ByteArray) : Array ByteArray :=
  raws.filter fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => isAncestorB bw (RRParse.rrName rr)   -- name only; no rdata range check
    | none => false
```

`cacheRRs` / `cacheUnlessTruncated` then accept any parsed RR into the cache.
A repo-wide grep for address-range vetting is empty (all `private` hits are the
Lean access-modifier keyword, none are `rfc1918`/`loopback`/`rebind`/`127.0.0`):

```
grep -rniE "private-addr|rfc1918|loopback|rebind|127\.0\.0|169\.254|reserved" VeriDNS/   # -> no filtering code
```

## Reproduction (on the rig)

Authoritative leaf `example.test.` was given a public name pointing at loopback:

```
rbz9   IN A 127.0.0.9        # served by nsd leaf @10.53.0.12
```

Direct authoritative check:

```
$ dig +short @10.53.0.12 rbz9.example.test A
127.0.0.9
```

VeriDNS under test (@10.53.0.2:5300), confirmed healthy first
(`host.example.test A 10.53.0.101`, NOERROR), then:

```
$ dig @10.53.0.2 -p 5300 rbz9.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 54860
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0
;; ANSWER SECTION:
rbz9.example.test.  3587  IN  A  127.0.0.9      <-- loopback served verbatim, cached (TTL counting down from 3600)
```

Reference unbound (@10.53.0.3:5301, `private-domain: "test."` permitting the fake
zone, `private-address` NOT configured) returns the same:

```
$ dig @10.53.0.3 -p 5301 rbz9.example.test A
;; ->>HEADER<<- status: NOERROR ...
rbz9.example.test.  3600  IN  A  127.0.0.9
```

So **against the running reference config the two resolvers agree** — neither
strips the loopback address. The divergence appears only if unbound is hardened
with `private-address: 127.0.0.0/8` (then unbound returns NODATA/filtered while
VeriDNS still returns `127.0.0.9`). VeriDNS has no configuration that could ever
produce the filtered result.

Corroborating baseline: VeriDNS already serves RFC1918 `10.53.0.x` rdata
(`10.53.0.100`, `10.53.0.101`) for `example.test`/`host.example.test` verbatim —
i.e. private-range answer rdata is passed through as a matter of course.

## Rig-contention caveat (why the first reads were noisy)

The shared rig had a concurrent agent overwriting the leaf zone file and
restarting `veridns-verid`/`veridns-auth-leaf` during testing. Early queries
showed transient SERVFAILs (VeriDNS in a broken glueless-priming state — it also
SERVFAILed the known-good `host.example.test`, so that was rig breakage, not a
filtering decision) and stale wrong-address cache hits (`10.53.0.101` returned
for `rebind`). The result above was captured in a window where VeriDNS was
verified healthy (baseline `host` query NOERROR) immediately before the loopback
query, so it is a clean read.

## Impact

Classic DNS-rebinding exposure against a co-located service: a rogue
authoritative server for a public name can point clients at `127.0.0.1` /
`192.168.x.x` / `169.254.169.254` (cloud metadata) and VeriDNS will cache and
serve it. VeriDNS offers no opt-in like unbound's `private-address` to defend a
security-conscious deployment. Not an RFC violation (serving the address
verbatim is RFC-correct default behavior), hence a coverage-gap for a well-known
resolver hardening rather than an implementation bug.

## References

- unbound `iterator/iter_scrub.c` `priv_rrset_bad` — strips A/AAAA/SVCB/HTTPS
  records whose rdata falls in configured private ranges.
- unbound `doc/example.conf.in` — `private-address` documented but shipped
  commented out (opt-in), which is why default unbound does not strip either.
- RFC 1918 (private IPv4), RFC 3927 (169.254/16 link-local), RFC 1122 (127/8
  loopback).
