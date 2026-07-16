# 051: QNAME minimisation applies strict RFC 8020 subtree denial on a minimised-probe NXDOMAIN — no full-QNAME fallback; spurious NXDOMAIN (and self-poisoned cache) for names that exist behind an ENT-NXDOMAIN server

- **Component:** `VeriDNS/Impl/Server.lean:691-696` (`ioResumeLoop` probe-round strict-denial branch), with `strictDenialB` (Server.lean:235-238), `storeProbeNegative` (Server.lean:240-249), probe construction `subQuestion` (Resolver.lean:457-463).
- **Class:** impl-bug (interoperability/correctness divergence vs. reference resolver on its shipped default)
- **Verdict:** CONFIRMED by isolated wire-level differential, cold caches on both resolvers.

## The defect

In `ioResumeLoop`, once a minimised probe is in flight
(`Resolver.probeRoundB state.resources.sname revealed`), any response with
`strictDenialB resp` — no CNAME to chase, rcode = NXDOMAIN, TC = 0 — is treated
as a denial of the whole subtree:

```lean
else if Resolver.probeRoundB state.resources.sname revealed
    && strictDenialB resp then do
  ...  -- "strict NXDOMAIN at probe ancestor: denying subtree ... (RFC 8020)"
  pure (.ok (Resolver.finalizeAnswer state resp),
    storeProbeNegative state.resources.cache subQuery₀ resp state.now)
```

`finalizeAnswer` re-owns the NXDOMAIN to the client's full query name, and
`storeProbeNegative` caches the negative under the *probe* name. There is no
AA check and — decisively — **no branch anywhere in the loop that abandons
minimisation and re-issues the full QNAME after a minimised-probe NXDOMAIN.**
This is `qname-minimisation-strict: yes` behaviour applied unconditionally, on
unsigned data.

Unbound's shipped default is the opposite (`util/config_file.c`:
`qname_minimisation = 1`, `qname_minimisation_strict = 0`): in
`iterator.c` (`processQueryResponse`, MINIMISE handling), a non-NOERROR reply
to a minimised query sets `minimisation_state = DONOT_MINIMISE_STATE` and
re-enters QUERYTARGETS_STATE — i.e. it stops minimising and re-sends the FULL
original QNAME to the same delegation, only trusting the intermediate NXDOMAIN
when DNSSEC proves it. RFC 9156 §2.4.1 documents exactly this hazard
("some name servers ... return NXDOMAIN for an ENT") and recommends the
fallback; RFC 8020 §2 makes subtree denial safe to rely on only for correct
servers, which is why unbound gates strictness behind an off-by-default knob.

## Consequence

Against an authoritative server that returns NXDOMAIN for an empty non-terminal
(historically common: old BIND ENT handling, various CDN/wildcard frontends),
veri-dns returns NXDOMAIN to the client for a name that **exists**, and
self-poisons its negative cache (probe name + client name), serving the wrong
NXDOMAIN with zero egress until the negative TTL expires. Default unbound
resolves the same name correctly over the identical path.

## Reproduction (rig, 2026-07-15)

Setup: leaf authoritative `nsd` for `example.test.` (203.0.113.12) replaced by
an ENT-broken mock (`penn-testing/_vmdns/entmock.py`, run in netns `auth` as
transient unit `veridns-entmock`) serving:

- `a.b.example.test. A` -> NOERROR aa=1, `A 203.0.113.150`
- `b.example.test.` (any type) -> NXDOMAIN aa=1 + SOA  (the ENT, wrongly denied)
- `example.test.` A/NS/SOA -> normal answers

unbound switched to its *shipped default* `qname-minimisation: yes`
(the rig config has it off; strict remains default `no`). Root/TLD nsd
unchanged. Mock verified directly before the differential:

```
$ ip netns exec verid dig @203.0.113.12 b.example.test A +norec | grep status
;; ->>HEADER<<- ... status: NXDOMAIN ...   (aa, SOA example.test)
$ ip netns exec verid dig @203.0.113.12 a.b.example.test A +norec | grep "IN.A"
a.b.example.test.	60	IN	A	203.0.113.150
```

Both resolvers cold-restarted (`systemctl restart veridns-verid veridns-ref; sleep 2`),
packet capture on the auth namespace, then one query each:

```
=== veri-dns (cold) a.b.example.test A ===
;; ->>HEADER<<- opcode: QUERY, status: NXDOMAIN, id: 20174
example.test.  60  IN  SOA  ns.example.test. hostmaster.example.test. ...

=== unbound (cold, qname-minimisation: yes, strict: no) a.b.example.test A ===
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 33131
a.b.example.test.  60  IN  A  203.0.113.150
```

The capture shows the mechanism exactly (ALL queries that reached the leaf):

```
18:28:56.364168 IP 203.0.113.2.53156 > 203.0.113.12.53: A? B.exAMPLe.TeST.     <- veri-dns probe; STOPS here
18:28:56.387113 IP 203.0.113.3.19809 > 203.0.113.12.53: A? b.example.test.     <- unbound probe
18:28:56.387218 IP 203.0.113.3.37740 > 203.0.113.12.53: A? a.b.example.test.   <- unbound non-strict fallback: full QNAME, 105 us later
```

veri-dns log confirms the code path and the cache self-poisoning:

```
[veri-dns] query a.b.example.test → ns.ExAmPLe.tESt (fuel 37)
[veri-dns] resp: rcode=3 an=0 ns=1 ar=0 tc=0x0#1
[veri-dns] strict NXDOMAIN at probe ancestor: denying subtree for a.b.example.test (RFC 8020)
[veri-dns] negative cache store (ttl 60)
[veri-dns] negative cache store (ttl 42)
```

Repeat `dig @203.0.113.2 -p 5300 a.b.example.test A` -> NXDOMAIN again with
**zero** new packets to the leaf in the capture (3 total for the whole window):
the spurious denial is served from the probe negative cache.

## Why this is a veri-dns bug and not "the DNS trust model"

Unbound, on the identical path against identical data, with a cold cache, and
minimising just like veri-dns, returns the correct answer. The divergence is
purely veri-dns's missing non-strict fallback. Note the rig's usual unbound
config has `qname-minimisation: no`, which also resolves correctly — the
differential above deliberately used unbound's shipped default (`yes`) so both
resolvers walked the same minimised path.

## Fix sketch

On `strictDenialB` during a probe round, do not finalize: disable minimisation
for this resolution (reveal all remaining labels, i.e. `revealed :=
DomainName.labelCount sname`) and re-enter the loop so the full QNAME is sent
to the same delegation; only treat the probe NXDOMAIN as final if operating in
an explicit strict mode. Do not `storeProbeNegative` unsigned probe NXDOMAINs.

## Citations

- RFC 9156 §2.4.1 ("NXDOMAIN from empty non-terminals") and §3 (fallback guidance).
- RFC 8020 §2 (subtree denial semantics assume correct authoritative servers).
- unbound `util/config_file.c` defaults (`qname_minimisation=1`, `qname_minimisation_strict=0`);
  `iterator.c` minimise state machine: non-NOERROR on minimised query -> `DONOT_MINIMISE_STATE`
  -> re-query full QNAME unless DNSSEC-validated.

## Cleanup

Baseline restored and verified: `veridns-entmock` stopped, `veridns-auth-leaf`
(nsd) recreated, `qname-minimisation: no` restored in `/opt/dnsenv/unbound/unbound.conf`,
both resolvers restarted; `host.example.test` -> 203.0.113.101 on both and
`a.b.example.test` -> NXDOMAIN on both (correct: not in the real zone).
No Lean source was modified; no build was run (rule 6).
