# 062 — The do-not-query egress filter (021's remediation) is unpinned: deleting `blockedEgress` builds green, re-enabling loopback SSRF

- **Severity:** medium (SSRF / reflection egress primitive; divergence from **default** unbound)
- **Classification:** coverage-gap (the egress-target defense exists in the impl but no theorem constrains it; mutation testing shows verification is not load-bearing here)
- **Status:** CONFIRMED on the running rig (mutation `M3-egress-disabled`)
- **Component:** `VeriDNS/Impl/Server.lean:354-355` (`blockedEgress`), `doNotQueryNets` (`:336-345`)
- **Reference:** unbound `iterator/iter_donotq.c` + `util/config_file.c` `do-not-query-localhost=yes` **default**; this finding is the mutation-test reconfirmation of finding 021, targeting the remediation that upstream 26b5849 added.

## Claim

Upstream 26b5849 remediated finding 021 (loopback egress / SSRF) by adding a
runtime do-not-query filter: `blockedEgress ip` returns true for
`doNotQueryNets` (0/8, 127/8, 10/8, RFC1918, link-local, etc.), and the SLIST /
forward path refuses to emit to a blocked address. The shipped binary now
correctly declines to query loopback glue.

**But that remediation is a runtime-only patch — no theorem pins it.** `pathmap
§4` records that `doNotQueryNets` has zero mentions in `Proof/` and
`blockedEgress` appears only as `= false` *hypotheses*. Removing the entire
defense therefore changes no theorem statement: every soundness/adequacy lemma
that carries `blockedEgress ip = false` as a hypothesis keeps its statement
verbatim (the hypothesis just becomes trivially provable), and **no** theorem
asserts `blockedEgress` is ever true for a blocked address. The verification is
blind to whether the egress ACL is present or absent.

## Mutation (the proof signal)

`VeriDNS/Impl/Server.lean:354-355`:

```
-def blockedEgress (ip : BitVec 32) : Bool :=
-  !egressBypassEnabled && doNotQueryNets.any (fun e => e.matches ip)
+def blockedEgress (_ip : BitVec 32) : Bool :=
+  false
```

`lake build` → **GREEN, 300/300 jobs, zero proof edits.** The complete
do-not-query ACL is now dead code and every upstream address — including
127.0.0.1 — is queryable, yet not one theorem broke. A pinned defense (e.g. an
`AllSent`-style claim constraining the destination address) would have failed to
compile here; nothing did.

## Reproduction (on the rig)

Ephemeral loopback-glue delegation added to the leaf zone `example.test.`
(served by nsd @203.0.113.12), serial bumped, leaf restarted:

```
sub     IN NS  ns.sub.example.test.
ns.sub  IN A   127.0.0.1
```

`dig +norec @203.0.113.12 www.sub.example.test A` → referral with
`ns.sub.example.test. A 127.0.0.1` in ADDITIONAL.

### Mutant veri-dns — emits real DNS queries to 127.0.0.1:53 (SSRF)

`tcpdump -n -i lo` inside the `verid` netns during
`dig @203.0.113.2 -p 5300 www.sub.example.test A`:

```
07:46:18 IP 127.0.0.1.46784 > 127.0.0.1.53: 596 [1au] A? WWw.sub.EXampLE.TEst. (49)
07:46:20 IP 127.0.0.1.46623 > 127.0.0.1.53: 17755 [1au] A? WWW.SUb.ExAmpLe.TESt. (49)
```

The mutant took the loopback glue as an upstream and fired real UDP queries at
127.0.0.1:53 (0x20-randomized qname). Client dig times out (nothing answers on
loopback:53).

### Shipped (unmutated) veri-dns — refuses (filter works)

Same query, reverted+rebuilt binary: **zero loopback packets**, SERVFAIL. The
`blockedEgress` filter correctly declines the loopback target.

### Reference unbound — DEFAULT config also refuses

Unbound at its shipping default `do-not-query-localhost: yes`
(`dig @203.0.113.3 -p 5301 www.sub.example.test A`): **zero loopback packets**,
SERVFAIL. (The rig's `unbound.conf` sets `do-not-query-localhost: no` only so
unbound can reach on-link private-range upstreams — 203.0.113.x, never loopback
— so flipping it to the default does not impair the oracle; it faithfully models
a deployed unbound, which refuses loopback egress.)

## Why it is wrong

`unboundDiffers = true`: a default unbound refuses loopback egress where the
mutant veri-dns performs it. The shipped veri-dns also refuses — the defense is
real code — but it is **certified by nothing**. The soundness/adequacy corpus
would remain green if a future refactor silently dropped or weakened the ACL,
exactly as this mutation demonstrates. This is the residual gap behind finding
021: the fix landed in the impl but never entered the spec. A positive theorem
of the form "the resolver never emits an upstream datagram to an address in
`doNotQueryNets`" (an `AllSent` destination constraint) is required to make the
egress defense load-bearing.

## Build result proving proofs stayed green

`lake build` after the mutation: `Build completed successfully (300 jobs).` —
no proof file edited, no `sorry`, no statement changed.

## Cleanup

Reverted per-file (`git checkout -- VeriDNS/Impl/Server.lean`), rebuilt green,
reloaded shipped binary, restored the ephemeral leaf zone. Baseline: verid and
unbound both resolve `host.example.test → 203.0.113.101`; `sub` delegation gone.
