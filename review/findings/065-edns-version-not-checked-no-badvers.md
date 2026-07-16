# 065 — EDNS VERSION field never checked: version>0 query answered NOERROR instead of BADVERS (RFC 6891 §6.1.3)

**Severity:** low (protocol non-conformance; no integrity/poisoning impact)
**Status:** CONFIRMED (differential vs unbound, cold caches)
**Location:** `VeriDNS/Impl/Edns.lean:39` (`findOptSize`), `VeriDNS/Impl/Server.lean` (`serveDatagram`/`queryProblem`)

## Claim

RFC 6891 §6.1.3 (EDNS versioning):

> If a responder does not implement the VERSION level of the request, then it
> MUST respond with RCODE=BADVERS. ... The ext-RCODE ... is set to BADVERS(16).

veri-dns's only inspection of a client OPT RR is `findOptSize` (Edns.lean:39-43),
which reads `rr.class.toNat` — the advertised UDP size — and nothing else. The
EDNS VERSION field (the second byte of the OPT TTL) is never read anywhere in the
query pipeline; `serveDatagram`/`queryProblem` gate only on `qdcount==1`,
`opcode==query`, and `rd==1`. A client that requests EDNS version 1 is therefore
resolved normally at NOERROR (and, notably, veri-dns emits **no OPT RR at all** in
the reply). unbound answers such a query with RCODE BADVERS (ext-rcode 16),
carrying an OPT that advertises the version it does support (0).

unbound reference: `worker.c` — `if(edns.edns_present && edns.edns_version != 0)`
→ `extended_error_encode(..., EDNS_RCODE_BADVERS, ...)` and return, before any
resolution.

## Setup

Rig per `review/ENV.md`. veri-dns @203.0.113.2:5300 (netns `verid`), unbound
@203.0.113.3:5301 (netns `unbound`), client/attacker netns @192.168.53.99. Both
resolvers restarted for cold caches before the differential
(`systemctl restart veridns-verid veridns-ref; sleep 2`).

## Reproduction + output

`dig` with `+edns=1` requests EDNS version 1. `+noednsnegotiation` stops dig's
auto-retry so the raw first reply is shown.

```
== unbound (203.0.113.3:5301) ==
$ dig @203.0.113.3 -p 5301 example.test A +edns=1 +noednsnegotiation +tries=1
;; ->>HEADER<<- opcode: QUERY, status: BADVERS, id: 18638
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 1232          <-- responder advertises version 0
;; QUESTION SECTION:
;example.test.            IN  A
;; (no answer section)

== veri-dns (203.0.113.2:5300) ==
$ dig @203.0.113.2 -p 5300 example.test A +edns=1 +noednsnegotiation +tries=1
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 22677
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0
;; ANSWER SECTION:
example.test.        3586  IN  A  203.0.113.100    <-- answered, no BADVERS, no OPT
```

Also confirmed with dig's default EDNS negotiation, where dig prints
`;; BADVERS, retrying with EDNS version 0.` for unbound and never for veri-dns.

Raw-datagram cross-check (hand-built `struct` query, OPT ttl version byte = 1):

```
ver1 -> veri-dns: reply base-rcode=0 ancount=1 arcount=0   (answered)
ver1 -> unbound : reply base-rcode=0 ancount=0 arcount=1   (BADVERS in OPT ext-rcode)
```

## Divergence

- **unbound** (RFC 6891 §6.1.3 conformant): EDNS version 1 → `status: BADVERS`,
  no answer, OPT echoing supported version 0.
- **veri-dns**: EDNS version 1 → `status: NOERROR` with the A record and no OPT RR
  in the reply. The VERSION field is never examined.

## Related (already filed)

The suspected-bug report bundled two adjacent EDNS-conformance gaps on the same
`findOptSize` surface:
- Multiple OPT RRs (arcount≥2, all type-41) not rejected FORMERR → **finding 056**
  (already CONFIRMED).
- A query with an extra non-OPT additional RR (arcount>1, OPT + bogus A) is also
  resolved by veri-dns (base-rcode=0, an=1) whereas unbound returns FORMERR
  (rcode=1, empty body) — same root cause as 056 (no arcount discipline / owner
  check in `findOptSize`). Recorded here for completeness; not re-filed.

This finding (065) covers only the previously-undocumented **VERSION** check.

## Fix sketch

Before resolution, `queryProblem`/`serveDatagram` should read the OPT TTL's
version byte; if the client OPT is present and its version ≠ 0, return a reply
with ext-rcode BADVERS(16) and an OPT advertising version 0, per RFC 6891 §6.1.3
— mirroring unbound's pre-resolution short-circuit. `findOptSize` already locates
the OPT RR; a companion accessor for the version byte gates the BADVERS path.

## Cleanup

No source or rig config was mutated; only a read-only crafted-packet script was
staged transiently under `penn-testing/_vmdns/` and removed. Both resolvers left
running with cold caches. Tracked source clean.
