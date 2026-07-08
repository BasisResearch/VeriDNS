# 015 — Upstream TC=1 (truncated) responses are delivered to the client; no upstream TCP fallback

**Status:** confirmed (impl-bug).

## Summary

When an authoritative server answers veri-dns's UDP query with the TC
(truncation) bit set, veri-dns **delivers that truncated response straight to
the client** instead of re-issuing the query over TCP. RFC 1035 §4.2.1 and RFC
2181 §9 require that a TC=1 UDP answer be treated as possibly incomplete and
re-fetched over TCP. veri-dns has no TCP transport anywhere (no client listener
— see finding 006 — and no upstream TCP client), so a name whose RRset exceeds
what fits in veri-dns's non-EDNS 512-byte UDP query is **effectively
unresolvable** via veri-dns, while unbound returns the complete RRset.

Observed differentially on the rig: a fresh name with a 40-record A RRset
(~700 bytes) is returned in full by unbound (NOERROR, 40 answers) but yields a
TC=1 empty response from veri-dns; the client's mandated TCP retry to veri-dns
then fails with connection refused, so the name cannot be resolved.

## Environment

Controlled rig in the penn-testing VM (see `review/ENV.md`):
- veri-dns (under test) @10.53.0.2:5300, netns `verid`.
- unbound (reference) @10.53.0.3:5301, netns `unbound`.
- authoritative leaf `nsd` for `example.test.` @10.53.0.12:53, netns `auth`.
- client: netns `attacker` 10.53.0.99.

**Setup:** a big A RRset was added to the leaf zone so a *non-EDNS* 512-byte UDP
query is truncated by nsd. Example added record set (fresh, uncached names
`tcpa..tcpe.example.test`, 40 A records each, `10.53.2.1 .. 10.53.2.40`):

```
tcpc    IN A     10.53.2.1
...     (40 A records)
tcpc    IN A     10.53.2.40
```

**Contamination caveat:** a concurrent review agent was actively running
`spoof.py` against the *same shared rig* during this session and repeatedly
bound `python3` to the leaf's `10.53.0.12:53`, crashing/masking the real `nsd`
and injecting poisoned answers. All results below are taken from a clean window
(~20:19 local) in which the genuine `nsd` (pid 4795) served the queries; later
poisoned/ICMP observations are discarded (same rig-sharing hazard finding 006
documented).

## Reproduction

### 1. The authoritative server truncates veri-dns's non-EDNS UDP query

veri-dns sends **no EDNS0** (finding 009), so its query advertises the classic
512-byte UDP limit; nsd must truncate the 40-record answer and set TC. On the
wire (auth ns), the non-EDNS UDP response is TC=1 with **zero** answers:

```
10.53.0.99.59734 > 10.53.0.12.53: 54626+ A? tcpc.example.test. (35)
10.53.0.12.53 > 10.53.0.99.59734: 54626*-| 0/0/0 (35)      # '-|' = TC=1, 0/0/0 answers, 35 bytes
```

### 2. veri-dns delivers the TC=1 response to the client; no upstream TCP

Querying veri-dns over UDP, its reply to the client has TC set (dig reports
"Truncated"), and the mandated TCP retry to veri-dns is refused (no TCP
listener). Deterministic across three fresh names:

```
$ dig +notcp +noedns +tries=1 +time=4 @10.53.0.2 -p 5300 tcpc.example.test A
;; Truncated, retrying in TCP mode.
;; Connection to 10.53.0.2#5300(10.53.0.2) for tcpc.example.test failed: connection refused.
;; no servers could be reached
                                            # identical for tcpd, tcpe
```

Upstream capture (auth ns) during the veri-dns query — **UDP only, no TCP SYN**
to the leaf; veri-dns receives TC=1 / 0 answers and gives up:

```
10.53.0.2.44179 > 10.53.0.12.53: 55352 A? tcpc.example.test. (35)
10.53.0.12.53 > 10.53.0.2.44179: 55352*-| 0/0/0 (35)       # TC=1, 0 answers — veri-dns opens no TCP, does not retry
```

(An earlier run of the same scenario returned SERVFAIL from veri-dns instead of
a TC=1 passthrough; either way the name is unresolvable and no upstream TCP is
attempted.)

### 3. unbound resolves the same name completely

```
$ dig +notcp +noedns +tries=1 +time=4 @10.53.0.3 -p 5301 tcpc.example.test A
;; ->>HEADER<<- status: NOERROR, ...
;; flags: qr rd ra; QUERY: 1, ANSWER: 40, AUTHORITY: 0, ADDITIONAL: 0
tcpc.example.test.  3600  IN  A  10.53.2.1 ... (all 40 records)
```

On the wire, unbound queries the leaf with **EDNS0** (`[1au]` OPT record
advertising a large UDP buffer), so nsd is not forced to truncate and returns
the full RRset in one UDP datagram:

```
10.53.0.3.43053 > 10.53.0.12.53: 6630% [1au] A? tcpb.example.test. (46)   # '[1au]' = EDNS OPT
```

**Mechanism note (accuracy):** in *this* rig unbound avoids truncation via
EDNS0 (the ~700-byte answer fits its advertised buffer), so unbound's own
TCP-fallback path was not exercised here. Had the RRset exceeded unbound's EDNS
buffer, unbound would receive TC=1 and re-query over TCP (unbound
`outside_network.c`: on `LDNS_TC_WIRE` it discards partial UDP contents and
calls `serviced_tcp_initiate`). The confirmed veri-dns defect is independent of
that detail: veri-dns receives TC=1 from the authoritative server and performs
**no** TCP retry — it hands the client the truncated answer.

## Root cause (code)

`VeriDNS/Impl/Resolver.lean` `stepAnalyzeResponse`: on `resp.header.tc == 1` the
resolver returns `.answer (finalizeAnswer s resp)` (around lines 370 and 437) —
the truncated upstream response is finalized and delivered. `finalizeForClient`
pins qr/ra/aa/z but never clears TC, and `cacheUnlessTruncated`
(`Resolver.lean:194`) merely *skips caching* the truncated response; it does not
trigger a TCP re-fetch. `IoResumeSound.lean:1503-1506` concedes "TC→TCP retry
lives at the transport layer" — but no such layer exists: the only upstream
transport is the UDP `veri_dns_exchange`
(`VeriDNS/Impl/Server.lean` / `UdpSocket.lean`), and `ss -tlnp`/`ss` show no TCP
socket in either direction (finding 006). There is no `serviced_tcp_initiate`
equivalent.

## RFC / reference citation

- **RFC 1035 §4.2.1:** "If the total response ... does not fit in the 512 byte
  limit, ... the TC bit is set ... The requestor ... may repeat the query using
  TCP." A resolver that honours DNS semantics must fetch the complete RRset over
  TCP rather than surface a truncated answer.
- **RFC 2181 §9:** a response with TC set has had "some data ... omitted" and
  MUST be treated as incomplete.
- **RFC 7766 §5:** general-purpose DNS implementations MUST support TCP
  transport (veri-dns supports neither client nor upstream TCP).
- **unbound** `services/outside_network.c` (`LDNS_TC_WIRE` → discard partial UDP
  → `serviced_tcp_initiate`) re-queries over TCP on truncation; combined with
  EDNS0 it always returns the complete RRset — the differential baseline.

## Relationship to prior findings

- **006 (no DNS-over-TCP):** documented the missing *client-facing* TCP listener.
  This finding is the *upstream* side — veri-dns also never opens TCP toward
  authoritative servers, so it cannot recover a truncated upstream answer.
- **009 (no EDNS0):** the reason veri-dns is truncated in the first place; a
  non-EDNS query caps the server at 512 bytes.

Composed: no EDNS0 (009) forces upstream truncation → no upstream TCP retry
(this finding) means veri-dns cannot recover → no client TCP listener (006)
means the client cannot recover either → the name is unresolvable via veri-dns
but resolvable via unbound.
