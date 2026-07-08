# 022: No QNAME minimization — full query name sent to root and every intermediate server

**Classification:** coverage-gap (privacy divergence from RFC 9156 / unbound default; no spec or theorem covers upstream QNAME construction)

## Claim

veri-dns builds every upstream sub-query with the client's full QNAME
(`buildSubQuery`, `VeriDNS/Impl/Resolver.lean:463`: `qname := s.resources.sname`),
where `sname` is only ever the full client query name (`initFromQuery`) or a
CNAME target — never truncated to the minimal label needed for the next
delegation hop. The root and TLD servers therefore see the entire lookup name.
unbound defaults to QNAME minimization (RFC 9156):
`unbound/util/config_file.c:363` (`cfg->qname_minimisation = 1;`).

## Reproduction (rig, 2026-07-08)

Cold cache: `systemctl restart veridns-verid veridns-ref` inside the VM.
Capture on the bridge in the root netns while querying from the attacker ns.

### veri-dns (@10.53.0.2:5300), query `secret1.b.c.example.test A`

```
tcpdump -n -i brdns udp port 53   # excerpt, veri-dns upstream queries
14:24:49.077947 IP 10.53.0.2.40299 > 198.41.0.4.53:  39920 A? secret1.b.c.example.test. (42)   <- ROOT sees full name
14:24:49.078105 IP 10.53.0.2.49657 > 10.53.0.11.53:  34926 A? secret1.b.c.example.test. (42)   <- TLD sees full name
14:24:49.078253 IP 10.53.0.2.49712 > 10.53.0.12.53:    298 A? secret1.b.c.example.test. (42)   <- leaf (legitimately)
```

### unbound with its shipped default (`qname-minimisation: yes`), query `secret3.b.c.example.test A`

Note: the rig's `review/env/unbound/unbound.conf:26` sets
`qname-minimisation: no`, overriding unbound's default; for the reference run
the in-VM copy was flipped to `yes` (the upstream default), then restored.

```
14:25:44.556657 IP 10.53.0.3.63699 > 198.41.0.4.53:  45664% [1au] A? test. (33)                     <- ROOT sees one label
14:25:44.556691 IP 10.53.0.3.20178 > 10.53.0.11.53:  39246% [1au] A? example.test. (41)             <- TLD sees two labels
14:25:44.556842 IP 10.53.0.3.22469 > 10.53.0.12.53:   7789% [1au] A? c.example.test. (43)           <- leaf, minimised walk
14:25:44.556950 IP 10.53.0.3.29799 > 10.53.0.12.53:  21669% [1au] A? secret3.b.c.example.test. (53) <- full name only at the authoritative leaf
```

Both resolvers return the same final verdict (NXDOMAIN) — the divergence is
purely on the wire, invisible to the client.

## Impact

Every ancestor server (root, TLD, any intermediate) learns the full lookup
name, e.g. `secret.internal.corp.example.test`. RFC 9156 ("DNS Query Name
Minimisation to Improve Privacy", standards-track, obsoleting RFC 7816)
exists precisely to prevent this leak; unbound, BIND, and Knot all minimise
by default. RFC 9156 §2: "instead of sending the full QNAME ... upstream,
send them a QNAME that is the original QNAME stripped to just one label more
than the zone for which the server is authoritative."

## Why the proofs did not catch it

The Spec/Proof layers constrain what veri-dns *accepts and caches* and what
it answers to the client; no spec predicate constrains the QNAME of the
sub-queries it *emits* upstream. `buildSubQuery` is effectively
specification-free on this axis, so full-name leakage type-checks and proves
clean.

## Fix sketch

Track the current delegation point (deepest NS cut known in cache) and set
the sub-query QNAME to one label below it, falling back to the full name on
NXDOMAIN/NOTIMP from minimised queries (RFC 9156 §2.3 relaxed mode), as
unbound's `INIT_MINIMISE_STATE` does (`unbound/iterator/iterator.c`).
