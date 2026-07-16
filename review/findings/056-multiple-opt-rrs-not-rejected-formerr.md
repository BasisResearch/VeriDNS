# 056 — Multiple OPT RRs in a client query are not rejected (RFC 6891 §6.1.1 FORMERR)

**Severity:** low (protocol non-conformance; no integrity/poisoning impact, reply size ≤ request)
**Status:** CONFIRMED (differential vs unbound, cold caches)
**Location:** `VeriDNS/Impl/Edns.lean:39` (`findOptSize`), `VeriDNS/Impl/Server.lean:118` (`queryProblem`)

## Claim

RFC 6891 §6.1.1:

> If a query message with more than one OPT RR is received, a FORMERR
> (RCODE=1) MUST be returned.

veri-dns never counts OPT RRs. `findOptSize` (Edns.lean:39-43) does
`section_.findSome?` over the additional section and returns the *first* OPT's
advertised size; `queryProblem`/`supportsQueryKind` (Server.lean:109-122) check
only `qdcount==1`, `opcode==query`, and `rd==1`. A query carrying two (or more)
OPT RRs is therefore accepted and answered normally, using the first OPT's
advertised UDP size for `clientCap`. unbound returns FORMERR.

## Setup

Rig per `review/ENV.md`. veri-dns @203.0.113.2:5300 (netns `verid`), unbound
@203.0.113.3:5301 (netns `unbound`), client/attacker netns @192.168.53.99.
`dig` cannot emit two OPT RRs, so a raw datagram was hand-built with plain
`python3`/`struct`:

- Header: `id`, flags `0x0100` (qr=0, opcode=QUERY, rd=1), qdcount=1,
  ancount=0, nscount=0, **arcount=N**.
- Question: `host.example.test A IN`.
- Additional: **N** OPT RRs, each `name=root(0x00), type=41, class=4096,
  ttl=0, rdlength=0`.

Script staged at `/opt/dnsenv/multi_opt.py` (source:
`penn-testing/_vmdns/multi_opt.py`) sends N ∈ {0,1,2,3} and prints the reply
header. Both resolvers restarted for cold caches before each run
(`systemctl restart veridns-verid veridns-ref; sleep 2`).

## Reproduction + output

```
== unbound ==
unbound num_opt=0: len=51 qr=1 rcode=0 qd=1 an=1 ns=0 ar=0
unbound num_opt=1: len=62 qr=1 rcode=0 qd=1 an=1 ns=0 ar=1
unbound num_opt=2: len=12 qr=1 rcode=1 qd=0 an=0 ns=0 ar=0   <-- FORMERR
unbound num_opt=3: len=12 qr=1 rcode=1 qd=0 an=0 ns=0 ar=0   <-- FORMERR
== verid ==
verid num_opt=0: len=140 qr=1 rcode=0 qd=1 an=1 ns=1 ar=1
verid num_opt=1: len=68  qr=1 rcode=0 qd=1 an=1 ns=0 ar=0
verid num_opt=2: len=68  qr=1 rcode=0 qd=1 an=1 ns=0 ar=0    <-- NOERROR, answered
verid num_opt=3: len=68  qr=1 rcode=0 qd=1 an=1 ns=0 ar=0    <-- NOERROR, answered
```

Result stable across two independent cold-restart cycles.

## Divergence

- **unbound** (RFC 6891 §6.1.1 conformant): ≥2 OPT RRs → `rcode=1` (FORMERR),
  empty body (qd=0, an=0).
- **veri-dns**: ≥2 OPT RRs → `rcode=0` (NOERROR) and answers the query normally
  (an=1, `host.example.test A 203.0.113.101`), using the first OPT's advertised
  size for `clientCap`. No FORMERR is ever emitted.

The single-OPT (N=1) and no-OPT (N=0) cases both answer NOERROR on both
resolvers, isolating the difference to the multi-OPT condition. (The N=0
authority/additional-count difference — verid ns=1/ar=1 vs unbound ns=0/ar=0 —
is unrelated to this finding.)

## Fix sketch

`queryProblem` should reject a query whose additional section contains more than
one type-41 (OPT) RR with `Rcode.formatError`, per RFC 6891 §6.1.1. `findOptSize`
already parses the additional section; a companion `optCount > 1` check gates the
FORMERR.

## Cleanup

No source or rig config was mutated; only a read-only crafted-packet script was
staged (`/opt/dnsenv/multi_opt.py`). Both resolvers left running with cold
caches. Tracked source clean.
