# 004 — veri-dns implements no DNS-over-TCP; QTYPE=ANY appears "refused"

**Status:** confirmed (impl-bug). Re-characterises the reported finding: the
reported *mechanism* ("ICMP port-unreachable", "silently un-answered", "no code
path produces a valid response for qtype 255") is **refuted**; the true,
reproducible defect underneath the same symptom is **veri-dns has no TCP
listener at all** (RFC 7766 §5 makes DNS-over-TCP a MUST).

## Summary

A default `dig host.example.test ANY @veri-dns` fails with
`;; ... failed: connection refused` while unbound answers NOERROR. The reported
finding attributed this to veri-dns silently dropping the ANY datagram / no
qtype-255 path / an ICMP port-unreachable. On the wire that is wrong:

- **dig 9.20 sends ANY queries over TCP by default.** The "connection refused"
  is a **kernel TCP RST**, not an ICMP port-unreachable, and not a silent drop.
- **veri-dns listens only on UDP 5300 — there is no TCP socket.** So *every*
  TCP query is refused, not just ANY. `dig +tcp host.example.test A` against
  veri-dns is refused identically.
- **Over UDP, veri-dns does answer ANY** — it returns a well-formed DNS
  response. So there *is* a code path that produces a response for qtype 255.

The user-visible symptom (default `dig ... ANY` fails vs. unbound) is real and
reproducible; the root cause is the missing TCP transport, not anything
ANY-specific.

## Environment

Controlled rig in the penn-testing VM (see `review/ENV.md`):
- veri-dns (under test) @10.53.0.2:5300, netns `verid`.
- unbound (reference) @10.53.0.3:5301, netns `unbound`.
- client: netns `attacker` 10.53.0.99.

Note: a concurrent review agent was running cache-poisoning experiments against
the *same* shared rig during this session (journal shows `poison2.example.test`
/ `evil.example.test` queries, and the UDP ANY answer for `host.example.test`
was observed as poisoned `A 6.6.6.6`). Cache-*content* observations are
therefore contaminated and are NOT relied on below. The TCP defect is transport-
level and cache-independent.

## Reproduction

### 1. Default dig ANY is refused (TCP RST), unbound answers

```
$ ip netns exec attacker dig +noedns +tries=1 +time=2 @10.53.0.2 -p 5300 host.example.test ANY
;; Connection to 10.53.0.2#5300(10.53.0.2) for host.example.test failed: connection refused.
;; no servers could be reached
                                                          # deterministic 3/3

$ ip netns exec attacker dig +noedns +tries=1 +time=2 @10.53.0.3 -p 5301 host.example.test ANY
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 25267
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0
host.example.test.  3579  IN  A  10.53.0.101
```

### 2. On the wire it is a TCP SYN → RST, no UDP, no ICMP

`tcpdump -i any` in the `verid` ns while the default `dig ... ANY` runs:

```
v-verid In  IP 10.53.0.99.57065 > 10.53.0.2.5300: Flags [S],  ... length 0   # dig SYN (TCP!)
v-verid Out IP 10.53.0.2.5300 > 10.53.0.99.57065: Flags [R.], ... length 0   # kernel RST
```

No UDP packet is sent by dig for the default ANY query, and no ICMP is emitted.

### 3. Not ANY-specific: ALL TCP queries are refused

```
$ ip netns exec attacker dig +noedns +tcp +tries=1 +time=3 @10.53.0.2 -p 5300 host.example.test A
;; Connection to 10.53.0.2#5300(10.53.0.2) for host.example.test failed: connection refused.
;; no servers could be reached

$ ip netns exec attacker dig +noedns +tcp +tries=1 +time=3 @10.53.0.3 -p 5301 host.example.test A
host.example.test.  3600  IN  A  10.53.0.101        # unbound serves A over TCP
```

### 4. No TCP listener exists

```
$ ip netns exec verid ss -tlnp        # TCP listeners
State ...  Local Address:Port ...     # (empty — nothing)
$ ip netns exec verid ss -ulnp        # UDP listeners
UNCONN 0 0 0.0.0.0:5300 ... users:(("veri-dns",pid=1384,fd=11))
```

### 5. Over UDP, veri-dns *does* answer ANY (mechanism refuted)

Forcing UDP with `+notcp`, veri-dns returns a valid DNS response for qtype 255
(RCODE / record content varied during the run because a concurrent agent was
poisoning the cache; the point is a response is produced, deterministically):

```
$ ip netns exec attacker dig +noedns +notcp +tries=1 +time=3 @10.53.0.2 -p 5300 host.example.test ANY
;; ->>HEADER<<- opcode: QUERY, status: NOERROR/NXDOMAIN, id: ...
;; flags: qr ra; QUERY: 1, ANSWER: ...
```

### 6. Not a crash / not a DoS

`MainPID` is stable across both UDP-ANY and TCP-ANY queries (RST is emitted by
the kernel, veri-dns is never involved):

```
PID before UDP ANY: 1417 → after: 1417 → after TCP ANY: 1417
```

## Root cause (code)

`VeriDNS/Impl/Server.lean` `serveOne` (line 485) reads exclusively from a single
UDP socket via `UdpSocket.recvFrom clientSock 512`; the reply is UDP-truncated
by `truncateUdp` (line 501). There is no `listen`/`accept` TCP path anywhere in
the server, and `Main.lean` binds only the UDP socket (confirmed at runtime by
the empty `ss -tlnp`). Compounding the RFC problem: `truncateUdp` sets the TC
bit when a response exceeds 512 bytes (line 204/501), but because no TCP
transport is offered, a client that honours TC and retries over TCP can never
retrieve the full answer.

## RFC / reference citation

- **RFC 7766 §5 (DNS Transport over TCP):** "All general-purpose DNS
  implementations MUST support both UDP and TCP transport." veri-dns supports
  only UDP — a MUST violation.
- **RFC 1035 §4.2 / §4.2.2:** DNS is defined over both UDP and TCP; TCP is the
  fallback for responses that do not fit UDP (TC bit).
- **unbound** (reference) serves both A and ANY over TCP (§3 above), and answers
  ANY over UDP with the record — the differential baseline.

## Corrections to the reported finding

| reported | actual |
|---|---|
| "returns ICMP port-unreachable" | kernel **TCP RST** (dig defaults ANY→TCP) |
| "silently un-answered" | veri-dns **answers ANY over UDP** |
| "no code path produces a valid response for qtype 255" | UDP qtype-255 path exists and responds |
| ANY-specific | **all** TCP queries refused; not ANY-specific |
