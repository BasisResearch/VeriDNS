# 015 — A single benign `. NS` query permanently bricks all root-descending resolution

**Severity:** High (remote, unauthenticated, persistent DoS of the whole resolver)
**Component:** `VeriDNS/Impl/Resolver.lean:296-329` (`stepFindServers`) +
`VeriDNS/Impl/Server.lean:346-367` (`ioResumeLoop` glueless recovery)
**Classification:** impl-bug
**Status:** CONFIRMED on the rig (binary md5 `fa2edf6f6a22c2451e3debd02b99c400`)

## Summary

Issuing one ordinary recursive query for `. NS` against veri-dns causes it to
cache the root's own `NS` RRset (with no glue). From that point on, every name
whose delegation chain must be (re)fetched from the root returns **SERVFAIL with
zero egress** — the resolver emits no packets at all — until the process is
restarted. A single unauthenticated recursive query (the kind any resolver
priming, monitoring probe, or attacker sends) permanently disables the resolver.

unbound is unaffected: after the same `. NS` query it continues resolving
normally.

## Reproduction (on the rig)

All commands via `penn-testing/vm/ssh.sh`, querying from the `attacker` ns.
Each "cold" run stops `veridns-verid`, re-launches the same on-disk binary as a
transient unit (fresh empty cache), waits 2 s.

### Control — cold, no `. NS` first
```
dig @10.53.0.2 -p5300 host.example.test A
  -> status: NOERROR
     host.example.test. 3593 IN A 10.53.0.101
```

### Poison — cold, `. NS` first
```
dig @10.53.0.2 -p5300 . NS
  -> status: NOERROR
     . 3600 IN NS a.root-servers.net. ... e.root-servers.net.
dig @10.53.0.2 -p5300 host.example.test A
  -> status: SERVFAIL          (was 10.53.0.101)
dig @10.53.0.2 -p5300 newB1.example.test A     (never-seen name)
  -> status: SERVFAIL
```

### Isolation — the trigger is caching the root NS RRset specifically, not root contact
```
cold; dig @10.53.0.2 -p5300 . SOA   -> status: NOERROR
      dig @10.53.0.2 -p5300 host.example.test A
        -> status: NOERROR ; host.example.test. 3600 IN A 10.53.0.101
```
`. SOA` reaches the root and caches a root record too, yet does **not** poison —
only caching the `(., NS)` RRset does.

### unbound is unaffected (reference resolver @10.53.0.3:5301)
```
dig @10.53.0.3 -p5301 . NS               -> status: NOERROR
dig @10.53.0.3 -p5301 host.example.test A
  -> status: NOERROR ; host.example.test. 224 IN A 10.53.0.101
```

### tcpdump proves zero egress on the poisoned query
`ip netns exec verid tcpdump -n -i v-verid 'udp and dst port 53'`:
```
during  . NS               : 1 egress pkt  10.53.0.2.49935 > 198.41.0.4.53: NS? .
during  host.example.test A: 0 egress pkts  (SERVFAIL returned with no packets sent)
```

## Mechanism

1. `stepFindServers` (Resolver.lean:302) calls `walkNs`, which climbs the qname
   `host.example.test -> example.test -> test -> .` looking for the nearest
   cached `NS` RRset. Once `. NS` has been cached, this walk stops at the root
   and returns `some (rootNsNames, mc=0)`.
2. Because `walkNs` returned `some`, control takes the `some` branch
   (Resolver.lean:303-323) and builds a SLIST from the cached root NS names. It
   fills addresses only from cached glue via `CacheSpec.lookupTopCred ... aType`
   (Resolver.lean:309-320). The cached root NS RRset has **no** accompanying A
   glue, so the SLIST is addressless.
3. The `none` branch (Resolver.lean:324-329) — the *only* path that falls back
   to `s.resources.sbelt`, i.e. the hardcoded root hints that carry usable
   addresses — is **never reached** when `walkNs` succeeds. So the real root
   addresses in `sbelt` are ignored.
4. `ioResumeLoop`'s glueless recovery (Server.lean:346-367) then tries to obtain
   the root servers' addresses by calling the **pure, cache-only**
   `@Resolver.resolve` (Server.lean:351), which cannot perform network I/O. It
   finds nothing, drops every root server, produces an empty SLIST, and the
   resolver returns SERVFAIL without sending a packet.

`sbelt` (root hints) and a cached root `NS` RRset are treated as mutually
exclusive rather than as interchangeable address sources: caching the root NS
shadows the only branch that reads the hints, and the cached NS carries no
addresses of its own.

## Why this is a bug (RFC + unbound)

RFC 1034 §5.3.3 and the resolver algorithm treat the safety belt (`SBELT`, the
root hints) as an always-available fallback: "SLIST ... is initialized from a
configuration file ... SBELT ... a special SLIST ... used to start a fresh
resolution." The hints exist precisely so the resolver can always reach the root
even when cached delegation data is unusable. A cached root `NS` RRset must
**augment**, never **replace and disable**, the configured root addresses.

unbound demonstrates correct behavior: it holds root hints and any learned root
`NS`/glue together, so a cached root NS never removes its ability to reach a root
server (verified above — it still returns `10.53.0.101` after `. NS`).

## Impact

Remote, unauthenticated, deterministic, persistent (until restart) denial of
service of the entire resolver. The trigger — a recursive `. NS` query — is
completely benign and routinely issued by resolver priming, health checks, and
monitoring, so this can also fire accidentally. After it fires, no name
requiring a fresh root-descending lookup can be resolved and the resolver sends
no traffic at all.
