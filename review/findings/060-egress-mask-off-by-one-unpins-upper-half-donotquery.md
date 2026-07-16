# 060 — Egress do-not-query mask arithmetic is unpinned: a shift off-by-one narrows every blocked net to its lower half and builds fully green

- **Severity:** medium (egress-target / SSRF-reflection primitive; divergence from **default** unbound)
- **Classification:** coverage-gap (sharpens finding 021 — not merely "no whole-predicate theorem", the mask BIT-ARITHMETIC itself is unconstrained)
- **Status:** CONFIRMED on the running rig (mutation builds green; live differential vs unbound)
- **Component:** `VeriDNS/Impl/Server.lean:144-146` (`AclEntry.matches`), `:336-355` (`doNotQueryNets` / `blockedEgress`), consumed at `:647`
- **Reference:** unbound `iterator/iter_donotq.c:130` (`do-not-query-localhost` inserts the WHOLE `127.0.0.0/8`), RFC 5735 (127/8 reserved loopback, never a valid query target)

## Claim

`AclEntry.matches` computes the compared prefix width as `let s := 32 - min e.plen 32`
then tests `(ip >>> s) == (e.net >>> s)`. This shift amount is the ONLY arithmetic
that turns a `(net, plen)` pair into a membership test, and it is used by both the
ingress client ACL (`permitted`) and the egress do-not-query filter
(`blockedEgress = doNotQueryNets.any (·.matches ip)`).

Nothing in `Proof/` constrains it. Per `review/pathmap.md` §4, `doNotQueryNets` has
zero mentions in `Proof/`, `blockedEgress` appears only as `= false` hypotheses, and
`AclEntry.matches` has no correctness lemma. Consequently a one-bit error in the shift
amount is invisible to the whole proof stack **and to every executable `#guard`**.

## Mutation (single character) — builds GREEN

```diff
 def AclEntry.matches (e : AclEntry) (ip : BitVec 32) : Bool :=
-  let s := 32 - min e.plen 32
+  let s := 31 - min e.plen 32
   (ip >>> s) == (e.net >>> s)
```

Effect: every prefix is compared one bit too wide, i.e. `/plen` behaves like `/plen+1`.
This NARROWS every do-not-query net to its lower half: `127/8 → 127.0.0.0/9`,
`10/8 → 10.0.0.0/9`, `192.168/16 → 192.168.0.0/17`. The upper half of each block
(`127.128.0.1`, `10.128.0.1`, `192.168.128.1`, …) is no longer blocked.

```
lake build  →  Build completed successfully (300 jobs).   # incl. Test.Loop, all #guards
lake build veri-dns  →  Build completed successfully (448 jobs).
```

All 24 MockM resolution `#guard`s in `Test/Loop.lean` still pass (public root/TLD/auth
IPs are in the lower half of no blocked net, so real resolution is unaffected), and
`ResolveWithIOSound`'s `by_cases hblk : blockedEgress ipAddr` handles both truth values,
so no theorem STATEMENT changed. The narrowing is completely unpinned.

## Reproduction (live rig)

Target address `127.128.0.1` — upper half of loopback `127.0.0.0/8`, which the mutant
no longer blocks. A rogue leaf responder (`penn-testing/_vmdns/probe_egress.py`, bound
to the leaf IP `203.0.113.12:53` in place of the leaf nsd) returns, for any name under
`example.test`, a downward referral whose in-bailiwick glue is
`ns-egress.<qname> A 127.128.0.1`. Query: `leak.probe.example.test A`.

For a faithful egress comparison, unbound was set to its DEFAULT
`do-not-query-localhost: yes` (the rig ships `no` only so it can reach on-link
upstreams; none of the legitimate rig upstreams are in 127/8, so the flip changes
nothing else — same precedent as finding 021). Both resolvers restarted (cold cache)
before each dig.

### Mutant veri-dns @203.0.113.2:5300 — LEAKS to 127.128.0.1

`tcpdump -n -i any host 127.128.0.1` in the `verid` netns:
```
127.0.0.1.46529 > 127.128.0.1.53: A? LEak.PROBE.EXaMPLE.teST.   <- real egress query
127.128.0.1 > 127.0.0.1: ICMP udp port 53 unreachable
127.0.0.1.55752 > 127.128.0.1.53: A? LeaK.PrObe.ExAmPLe.TESt.   (retry)
127.0.0.1.32960 > 127.128.0.1.53: A? lEAK.PRoBe.exAMplE.TEST.   (retry)
```
Resolver log: `query ... → ns-egress.probe.example.test` with **no** egress-blocked line.
Client: timeout / no answer.

### Baseline veri-dns (reverted binary) — BLOCKS 127.128.0.1

Identical setup, committed `AclEntry.matches`:
```
=== baseline packets to 127.128.0.1 === packet lines: 0
[veri-dns] egress blocked (do-not-query address) to ns-egress.probe.example.test for leak.probe.example.test
```
Client: `status: SERVFAIL`, zero packets. Proves the behaviour is load-bearing on the
one-bit mask change.

### unbound @203.0.113.3:5301 (default do-not-query-localhost) — BLOCKS, reference

```
=== DIG unbound ===  ;; ->>HEADER<<- status: SERVFAIL
=== unbound packets to 127.128.0.1 === packet lines: 0
```
unbound puts the FULL `127.0.0.0/8` on its do-not-query list
(`iter_donotq.c:130 donotq_str_cfg(dq, "127.0.0.0/8")`), so `127.128.0.1` is refused —
zero packets, SERVFAIL. **unbound agrees with the BASELINE veri-dns, not the mutant.**

## Impact

The shipped mask is correct, but its correctness rests on unverified integer arithmetic
in a single security-critical line shared by the ingress ACL and the egress filter. A
one-bit slip (easy to introduce in a refactor, e.g. inclusive vs exclusive prefix width)
silently unblocks the upper half of every do-not-query net — reopening the finding-021
SSRF/reflection egress primitive for 10.128/9, 127.128/9, 172.24/13, 192.168.128/17,
etc. — while the entire proof stack and every `#guard` stay green. It simultaneously
would deny legitimate clients in the upper half of each `defaultAcl` net (ingress),
another silent regression.

## Fix direction

Add an executable pin and a lemma for the mask:
- `#guard blockedEgress 0x7F800001 = true` (127.128.0.1), `#guard blockedEgress 0x0A800001 = true`
  (10.128.0.1), plus one canonical member per `doNotQueryNets` entry and a non-member.
- A soundness lemma `AclEntry.matches e ip = true ↔ (ip &&& mask) == e.net` with
  `mask = prefixMask e.plen`, tying the shift arithmetic to prefix semantics, and a
  theorem that `blockedEgress` is `true` on a representative set of reserved addresses.

## Rig state / cleanup

- `VeriDNS/Impl/Server.lean` reverted (`git checkout --`, single file), `lake build`
  green (300 jobs), baseline binary reloaded via `restart-verid.sh`.
- `unbound.conf` restored to `do-not-query-localhost: no`; `probe-egress` unit stopped
  and the leaf nsd (`veridns-auth-leaf`) restarted; both resolvers restarted and
  re-verified: `host.example.test A 203.0.113.101`, `www.example.test CNAME → 203.0.113.100`.

## Artifacts

- `penn-testing/_vmdns/probe_egress.py` (untracked; rogue leaf returning upper-half
  loopback glue).
