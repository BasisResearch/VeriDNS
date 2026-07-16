# 052: QNAME minimisation has no fallback on a persistently dropped/timed-out minimised probe — VeriDNS SERVFAILs where unbound resolves via the full QNAME

- **Component:** `VeriDNS/Impl/Server.lean:657-658` (`ioResumeLoop`, the `upstreamResp = none` branch), with probe construction `Resolver.subQuestion`/`buildSubQuery` (Resolver.lean:457-487) and `bumpRevealed` (Resolver.lean:465-466).
- **Class:** coverage-gap (robustness/interoperability divergence vs. reference resolver; no theorem constrains the failure path)
- **Verdict:** CONFIRMED by isolated wire-level differential, cold caches on both resolvers.
- **Sibling:** distinct from finding 051 (which covers a minimised probe that *receives* an NXDOMAIN). This one covers a minimised probe that *gets no answer at all* (dropped / timed out) — the exact scenario unbound handles with `MAX_MINIMISE_TIMEOUT_COUNT`.

## The defect

When a minimised sub-query gets no reply (`upstreamResp = none` — the upstream was
egress-blocked, or the packet/response was dropped), `ioResumeLoop` recurses with the
**same** `revealed`:

```lean
let some resp₀ := upstreamResp
  | ioResumeLoop sbelt state deadline depth fuel' revealed   -- Server.lean:657-658
```

`markQueried` (SList.lean:79-81) only increments the server's `transmissionCount`; it does
not remove the server, and `bestWithAddress` still returns it. So every loop iteration
re-sends the identical minimised probe (same QNAME = the intermediate label, QTYPE=A) to the
same server. There is **no timeout counter** and **no mechanism to disable minimisation and
fall back to the full QNAME**. The loop simply re-probes until the 5 s query budget
(`deadline`) is exceeded, at which point `ioResumeLoop` returns
`"resolveWithIO: query deadline exceeded"` → SERVFAIL. The full-QNAME query that would
succeed is never sent.

Contrast unbound: `MAX_MINIMISE_TIMEOUT_COUNT = 3` (iterator.h:77-79); after 3 timeouts on a
minimised query, `iq->minimisation_state = DONOT_MINIMISE_STATE` (iterator.c ~2709-2712) and
it drops to the full query. VeriDNS's minimisation is effectively always-strict on timeout.

## Reproduction (against the rig, cold caches on both resolvers)

Rig renumbered to 203.0.113.0/24. veri-dns @203.0.113.2:5300, unbound @203.0.113.3:5301,
leaf auth nsd @203.0.113.12 serving `example.test.`.

**Setup** (staged in the VM, reverted afterward):
1. Add a deep name to the leaf zone so an intermediate label is an ENT:
   `target.sub IN A 203.0.113.150` (so `sub.example.test` is an empty non-terminal,
   `target.sub.example.test` resolves to `203.0.113.150`). Bump SOA serial, reload leaf.
2. Move leaf nsd to `203.0.113.12@5312`; run a selective-drop middlebox
   (`middlebox.py`) on `203.0.113.12:53` that forwards everything to nsd EXCEPT it
   **silently drops any A query whose QNAME is exactly `sub.example.test`** — a firewall /
   middlebox that blocks the minimised ENT probe.

**Verified the middlebox does exactly that:**
```
dig +short @203.0.113.12 target.sub.example.test A   -> 203.0.113.150   (forwarded)
dig +tries=1 +time=2 @203.0.113.12 sub.example.test A -> ;; no servers could be reached (dropped)
```

**Baseline with NO middlebox (both restart cold):** both resolve the deep name —
```
veri-dns  target.sub.example.test A -> NOERROR  203.0.113.150
unbound   target.sub.example.test A -> NOERROR  203.0.113.150
```

**Differential with middlebox active (both restart cold):**
```
# veri-dns
dig +tries=1 +time=15 @203.0.113.2 -p 5300 target.sub.example.test A
;; ->>HEADER<<- status: SERVFAIL

# leaf tcpdump during the veri-dns query — ONLY minimised ENT probes, never the full name:
203.0.113.2.50056 > 203.0.113.12.53: A? suB.eXAMPLE.TEST.   (18:36:05)
203.0.113.2.54415 > 203.0.113.12.53: A? SUb.eXAMpLE.teST.   (18:36:07)
203.0.113.2.40162 > 203.0.113.12.53: A? sUb.ExaMplE.TEsT.   (18:36:09)
# 3 re-probes of the dropped intermediate ~2 s apart, then 5 s budget exhausted -> SERVFAIL.
# The full QNAME target.sub.example.test was NEVER sent.

# unbound
dig +tries=1 +time=15 @203.0.113.3 -p 5301 target.sub.example.test A
;; ->>HEADER<<- status: NOERROR
target.sub.example.test. 3600 IN A 203.0.113.150

# leaf tcpdump during the unbound query:
203.0.113.3.xxxxx > 203.0.113.12.53: A? target.sub.example.test.   (full QNAME, answered)
```

**Divergence:** veri-dns SERVFAIL vs unbound NOERROR/answer, on the identical name against
identical data with cold caches. veri-dns never falls back off the minimised probe.

## Honesty note on the oracle

unbound in this rig has `qname-minimisation: no`, so it sends the full QNAME directly and
never minimises — it is not exercising `MAX_MINIMISE_TIMEOUT_COUNT` here. But the observable
result is the same one that mechanism produces: default (modern) unbound with minimisation
*on* probes the intermediate up to 3 times, then disables minimisation and sends the full
QNAME — resolving successfully. Either configuration of unbound resolves the name; veri-dns
does not. The divergence is a genuine VeriDNS robustness gap, not a rig artifact.

## Spec gap

`VeriDNS/Spec/QnameMinimisation.lean` proves `query_storm_dampened` and the reveal-cap /
`bumpRevealed` progression, but only along the path where probes are *answered*. No theorem
constrains behaviour when a minimised probe is persistently unanswered, so no proof catches
this. A best-effort fallback (disable minimisation after N unanswered probes, send the full
QNAME) is unspecified and unimplemented.

## Cleanup

Middlebox stopped and removed; leaf nsd restored to `:53`; zone restored (deep name gone,
now NXDOMAIN); both resolvers restarted; `host.example.test` resolves on both. No tracked
source files were edited (all changes were VM-side copies, reverted from backups).
