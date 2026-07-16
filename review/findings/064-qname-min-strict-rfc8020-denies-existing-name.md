# 064 — QNAME-minimisation applies RFC 8020 strict subtree denial unconditionally: an intermediate-name NXDOMAIN denies an EXISTING name that unbound resolves

- **Component:** `VeriDNS/Impl/Server.lean:691-696` (`strictDenialB`, Server.lean:235) via the QNAME-minimisation probe loop in `ioResumeLoop`.
- **Class:** over-strict denial of existing names / availability (misconfiguration- or attacker-triggerable NXDOMAIN for a name that exists).
- **Verdict:** CONFIRMED at the wire. veri-dns returns NXDOMAIN; unbound returns NOERROR + the record, on an identical cold-cache path against identical authoritative data — and unbound does so *whether or not* it is itself minimising.

## Summary

During QNAME minimisation, `ioResumeLoop` gates on
`Resolver.probeRoundB … && strictDenialB resp` (Server.lean:691). `strictDenialB`
(Server.lean:235) fires on any response with `rcode == nameError`, `tc == 0`,
and no CNAME to chase. That response is the reply to the **minimised,
intermediate** probe name (qtype forced to A in `Resolver.subQuestion`,
Resolver.lean:457-461). On a hit it immediately returns
`.ok (finalizeAnswer state resp)` = NXDOMAIN **for the original qname** and
caches `storeProbeNegative` — with no fallback to the full query and no DNSSEC
gate (veri-dns has no DNSSEC).

This is RFC 8020 *strict* behaviour. unbound does the opposite by default:
`qname-minimisation-strict: no` (default) — on a minimised query whose answer is
not NOERROR it drops minimisation (`DONOT_MINIMISE_STATE`) and re-sends the FULL
original query, trusting an intermediate NXDOMAIN as final only for a signed
zone (`iq->dnssec_expected`). That is exactly the tolerance RFC 9156 §2.2 / §3
prescribes for zone cuts / empty non-terminals that legacy servers mishandle.

Consequence: for a name whose empty-non-terminal ancestor is served by a
server that answers NXDOMAIN (instead of RFC-2308 NODATA) for the qtype=A probe
— a well-known class of deployed/legacy servers, and precisely why unbound
defaults to non-strict — veri-dns denies a name that **exists**, while unbound
answers it.

## Reproduction

Rig: renumbered 203.0.113.0/24. Client in `attacker` ns (192.168.53.99).

### Broken authoritative leaf

Replaced `nsd-leaf` (203.0.113.12:53, authoritative for `example.test`) with
`review/env/brokenent_responder.py`, which models a legacy server:

- `example.test A` → NOERROR aa=1 `203.0.113.100` (apex, positive — advances minimisation)
- `bar.foo.example.test TXT` → NOERROR aa=1 `"it-exists"` (**a name that exists**)
- everything else, including the empty-non-terminal `foo.example.test` → **NXDOMAIN aa=1 + SOA**

`foo.example.test` genuinely exists in the tree (it has the child
`bar.foo.example.test`); a correct server would answer NODATA, this broken one
answers NXDOMAIN.

Direct queries to the responder confirm the setup:

```
$ dig +norecurse @203.0.113.12 foo.example.test A
;; ->>HEADER<<- status: NXDOMAIN
$ dig +norecurse @203.0.113.12 bar.foo.example.test TXT
;; ->>HEADER<<- status: NOERROR
bar.foo.example.test.  3600  IN  TXT  "it-exists"
```

### Differential (cold caches — both resolvers restarted, `sleep 2`)

```
$ dig @203.0.113.2 -p 5300 bar.foo.example.test TXT +tries=1      # veri-dns
;; ->>HEADER<<- status: NXDOMAIN ; ANSWER: 0, AUTHORITY: 1

$ dig @203.0.113.3 -p 5301 bar.foo.example.test TXT +tries=1      # unbound
;; ->>HEADER<<- status: NOERROR ; ANSWER: 1
bar.foo.example.test.  3600  IN  TXT  "it-exists"
```

veri-dns log confirms the strict-denial path fired at the minimised probe:

```
[veri-dns] query bar.foo.example.test → ns.EXaMPLe.TEST (fuel 37)
[veri-dns] resp: rcode=3 an=0 ns=1 ar=0 tc=0x0#1
[veri-dns] strict NXDOMAIN at probe ancestor: denying subtree for bar.foo.example.test (RFC 8020)
```

### unbound falls back even while itself minimising

To rule out "unbound wins only because the rig disables its minimisation", I
enabled `qname-minimisation: yes` (strict stays off = default) and restarted it:

```
$ dig @203.0.113.3 -p 5301 bar.foo.example.test TXT +tries=1      # unbound, qname-min ON
;; ->>HEADER<<- status: NOERROR ; ANSWER: 1
bar.foo.example.test.  3600  IN  TXT  "it-exists"
```

Still NOERROR: on the intermediate NXDOMAIN unbound drops minimisation and
re-queries the full name — the RFC 9156 §2.2/§3 fallback. veri-dns has no such
fallback.

## Why this is a veri-dns bug and not the trust model (rule 2)

unbound genuinely disagrees on the identical cold path against identical data,
in *both* of its configurations (minimising and not). The intermediate server
is standards-non-compliant (RFC 2308: an ENT is NODATA, not NXDOMAIN), but such
servers are deployed and are the entire reason RFC 9156 and unbound default to
non-strict minimisation. veri-dns implements RFC 8020 strict, unconditionally
and without a DNSSEC gate, so it converts a broken-but-existing name into a hard
NXDOMAIN — and negatively caches it (`storeProbeNegative`, Server.lean:696).

## Fix direction

Make the probe path non-strict by default (mirror RFC 9156 / unbound): on an
NXDOMAIN (or any non-NOERROR) reply to a *minimised intermediate* probe, do not
finalise — drop minimisation and re-issue the full original qname; only treat an
intermediate NXDOMAIN as final when the zone is signed and validated. Today
`strictDenialB` short-circuits to `finalizeAnswer` at Server.lean:691-696 with
no fallback.

## Rig restoration

- `brokenent_responder` stopped, `nsd-leaf` restarted.
- `unbound.conf` reverted to `qname-minimisation: no`, unbound restarted.
- Both resolvers restarted for cold caches.
- No tracked source files edited (behaviour is stock upstream 26b5849).
