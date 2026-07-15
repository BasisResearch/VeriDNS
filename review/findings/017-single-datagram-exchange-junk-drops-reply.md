# 017 — Upstream exchange reads exactly ONE datagram then closes the socket: one early junk datagram on the ephemeral port drops the in-flight reply and forces a re-query (unbound tolerates it)

**Classification:** impl-bug (robustness / availability; spoof-race window). Observably weaker than unbound.

## Summary

`veri_dns_exchange` (the FFI that performs one upstream UDP round) does a single
`recvmsg` and then immediately `close(fd)`s the socket, returning whatever one
datagram arrived first. If a junk/spoofed datagram reaches the resolver's fresh
ephemeral port *before* the authoritative reply, the Lean gate rejects it
(`datagramMatches` / `Message.decode` / `acceptResponse` fail), `forwardQuery`
returns `none`, and the genuine reply that arrives ~milliseconds later is lost
because the socket is already closed. veri-dns then re-queries with a fresh
socket + new random id. If the junk keeps arriving first on every attempt, the
IO loop exhausts its round budget and returns **SERVFAIL**.

unbound instead tolerates the unwanted datagram: it counts/drops it and leaves
the shared comm point open, so the genuine answer for the still-pending query is
still delivered on the same socket.

## Code

- `ffi/recvfrom.c:291-292` — `ssize_t n = recvmsg(fd, &msg, 0); close(fd);`
  exactly one datagram, then the socket is closed unconditionally.
- `VeriDNS/Impl/Server.lean:241-251` — `forwardQuery`: `exchange` → `acceptExchanged`
  → `Message.decode`; any failure yields `none`.
- `VeriDNS/Impl/Server.lean:409-416` — on `upstreamResp = none` or `acceptResponse`
  reject, the whole round is re-queried via `ioResumeLoop … fuel'`.
- Reference: unbound `services/outside_network.c` (`comm_point_udp_callback` /
  unwanted-reply path): an unsolicited/unwanted UDP reply is counted
  (`unwanted_replies`) and dropped, the callback returns, and the comm point
  stays open to receive the pending query's real reply.

## Reproduction (on the review rig)

Responder used: `penn-testing/_vmdns/dblsend.py` — an authoritative leaf for
`10.53.0.12:53` that answers any A query for `*.example.test` with
`A=10.53.0.101`, `AA=1`. In `double` mode it sends 12 bytes of junk to the
resolver's source port, sleeps 5 ms, then sends the real answer. In `single`
mode it sends only the answer (control).

Setup: warm both resolvers (`dig host.example.test` so the `example.test`
delegation glue `ns.example.test A 10.53.0.12` is cached), then stop
`veridns-auth-leaf` and bind `dblsend.py` on the same `10.53.0.12:53`. The
resolvers then query the responder directly (no root priming needed), which
isolates the leaf exchange as the only variable.

### DOUBLE mode (junk datagram first, then answer)

```
-- veri-dns d1.example.test --
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 11113
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
-- unbound  d1.example.test --
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 45474
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
d1.example.test.	300	IN	A	10.53.0.101
```

dblsend log — veri-dns re-queried from a *fresh ephemeral port* each round
(fresh-socket-per-exchange), every attempt getting junk first:

```
JUNK+ANSWER -> ('10.53.0.2', 52645) qtype=1
JUNK+ANSWER -> ('10.53.0.2', 34576) qtype=1
JUNK+ANSWER -> ('10.53.0.2', 39220) qtype=1
... (7+ distinct source ports) ...
```

veri-dns log — the re-query loop burning the round budget to zero:

```
[veri-dns] query d1.example.test → ns.example.test (fuel 6)
[veri-dns] query d1.example.test → ns.example.test (fuel 5)
... down to ...
[veri-dns] query d1.example.test → ns.example.test (fuel 0)
[veri-dns] SERVFAIL: resolveWithIO: max IO rounds
```

### SINGLE mode (answer only — control, identical setup)

```
-- veri-dns c9.example.test --
;; ->>HEADER<<- status: NOERROR ...
c9.example.test.	300	IN	A	10.53.0.101      # dblsend saw exactly 1 query from 10.53.0.2
-- unbound  c9.example.test --
;; ->>HEADER<<- status: NOERROR ...
c9.example.test.	300	IN	A	10.53.0.101
```

The *only* difference between the SERVFAIL run and the NOERROR run is whether a
single junk datagram precedes the answer on the resolver's ephemeral port. That
isolates the single-`recvmsg`-then-`close` behavior of `veri_dns_exchange` as
the cause, independent of root priming.

## Impact / severity

Robustness and availability, not a direct injection vector:

- An **off-path** attacker must still guess the unpredictable ephemeral port
  (fresh unconnected socket per exchange, RFC 5452 §9.2) to land a first packet,
  and veri-dns re-randomizes id + port on each retry, so this is not a cache
  poisoning primitive on its own.
- An **on-path** or **controlled/misbehaving authoritative** party, or anyone who
  can flood the ephemeral-port space, can convert a would-be success into repeated
  re-queries and ultimately SERVFAIL — a denial of resolution that unbound shrugs
  off. This is the behavior demonstrated above.

## Fix direction

After a rejected datagram, keep the socket open and continue receiving (loop
`recvmsg` until the RCVTIMEO deadline) rather than `close`-ing after the first
datagram, mirroring unbound's "drop unwanted, keep listening" comm-point model.
