# 054 — serveTcpDatagram TCP reply payload is unpinned: proofs stay green while the wire frame is wrong

**Classification:** bad-spec (spec/coverage gap: the TCP-adequacy capstone never constrains the bytes actually handed to `tcpSend`)
**Severity:** high — over TCP the resolver returns no usable answer; the query is echoed back to the client.
**unboundDiffers:** YES — same path, same data, cold caches: unbound returns the correct A record over TCP; veri-dns echoes the query (QR=0, ANSWER 0).

---

## The claim under test

`VeriDNS/Proof/ServeTcp.lean` is the TCP capstone. Two theorems look like they pin
the TCP reply:

- `serveTcpDatagram_served` (:11) recomputes, in its RHS,
  `UdpSocket.tcpSend connSock (TcpFraming.frameTcp (Message.encode response))`.
- `serveTcpDatagram_total` (:272) / `serveTcpDatagram_verdict_sound` (:34) prove
  (lines 353-360) that for the response
  `unframeTcp (frameTcp (encode (deliveredResponse query resp))) = some (encode …)`
  and `decode (encode (deliveredResponse query resp)) = .ok (deliveredResponse query resp)`
  — a "client-recoverable framing" round-trip.

These read as a guarantee that what goes on the TCP wire is the framed, encoded,
client-recoverable answer.

## Why the guarantee is vacuous for the actual send

In the proof model `Prog` the transport is a no-op:
`VeriDNS/Proof/FreeIO.lean:54` — `tcpSend _ _ := .pure ()`. The byte argument to
`tcpSend` is **discarded**: `(fun a => …) <$> tcpSend connSock ARG` reduces to
`pure …` for *any* `ARG`. So:

- `serveTcpDatagram_served`'s equation holds regardless of the argument passed to
  `tcpSend` (both sides collapse through `tcpSend → pure ()`).
- The round-trip fact at lines 353-360 is stated about the **abstract**
  `deliveredResponse query resp` recomputed *inside the existential*, never about
  the actual `ByteArray` handed to `tcpSend` in the implementation.
- `serveTcpDatagram_verdict_sound`'s run hypothesis `Prog.run n (…) w = some (cacheOut, w')`
  is independent of the send argument for the same reason.

Nothing in the proof relates the encoded/framed response to the bytes the running
binary actually writes to the TCP socket. Contrast: at runtime the transport is the
real `tcpSendRaw` (`VeriDNS/Impl/UdpSocket.lean:62`), so the send argument *is*
observable on the wire.

## Mutation (diff)

`VeriDNS/Impl/Server.lean:821-822`, inside `serveTcpDatagram` — replace the framed
encoded response with the framed *query* bytes (echo):

```
   UdpSocket.tcpSend (M := M) (Sock := Sock) (Addr := ByteArray) connSock
-    (TcpFraming.frameTcp (Message.encode response))
+    (TcpFraming.frameTcp queryBytes)
```

## Build result — proofs stay GREEN

`lake build` first broke only at `VeriDNS/Proof/ServeTcp.lean:30` (a **tactic**
failure in `serveTcpDatagram_served`: after `simp` the two `do`-blocks now differ
syntactically in the `tcpSend` argument). This is BRITTLE, not semantic — the
statement is still true because `tcpSend` ignores its argument. A one-line minimal
repair makes `simp` unfold `tcpSend` so both sides collapse:

```
VeriDNS/Proof/ServeTcp.lean:29
-  simp [hperm, hdec, hqp, -Prog.bind_def, -Prog.pure_def]
+  simp [hperm, hdec, hqp, VeriDNS.Spec.UdpSocket.tcpSend,
+    -Prog.bind_def, -Prog.pure_def]
```

With this repair `lake build` completes: **`Build completed successfully (300 jobs).`**
No theorem STATEMENT was weakened — `serveTcpDatagram_served`, `serveTcpDatagram_total`
and `serveTcpDatagram_verdict_sound` all still hold verbatim, with the implementation
sending the wrong bytes. That is the bad-spec: the capstone is satisfiable by an
implementation that sends the query instead of the answer.

## Reproduction (cold caches, both resolvers restarted)

```
# after: lake build veri-dns; review/env/restart-verid.sh;
#        ssh 'systemctl restart veridns-verid veridns-ref; sleep 2'

ip netns exec attacker dig +tcp @203.0.113.2 -p 5300 host.example.test A   # veri-dns
ip netns exec attacker dig +tcp @203.0.113.3 -p 5301 host.example.test A   # unbound
```

veri-dns (TCP):
```
;; Warning: query response not set
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 6876
;; flags: rd ad; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
;; QUESTION SECTION:
;host.example.test.		IN	A
                       (no ANSWER section — the client's own query is echoed back)
```

unbound (TCP):
```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 26550
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
;; ANSWER SECTION:
host.example.test.	3600	IN	A	203.0.113.101
```

Control — the mutation is TCP-specific; UDP is unaffected:
```
ip netns exec attacker dig +short @203.0.113.2 -p 5300 host.example.test A
203.0.113.101
```

The echoed frame carries QR=0 (dig: "query response not set"), so it is not a valid
DNS *response* at all; a stub resolver gets no answer over TCP. Reproduced for
`host.example.test` and `example.test`.

## Why it is wrong (RFC / oracle)

- RFC 1035 §4.1.1: the QR bit "specifies whether this message is a query (0), or a
  response (1)." A server's reply MUST set QR=1 and carry the answer; echoing the
  query (QR=0) is not a conformant response.
- RFC 7766 §8: DNS-over-TCP is mandatory to support and must carry the same answers
  as UDP; the 2-byte length-prefixed message must be the response.
- unbound, on the identical path against identical zone data with a cold cache,
  returns the correct `A 203.0.113.101` over TCP. veri-dns does not. This is a
  VeriDNS defect, not the DNS trust model.

## Takeaway

The TCP adequacy proof reasons entirely about the *abstract recomputed* response and
its framing round-trip; it never ties that abstract object to the concrete byte
argument passed to `tcpSend`, because the proof-model `tcpSend` is `pure ()` and
drops the argument. To be load-bearing, `serveTcpDatagram_served` (and the total
capstone) should state the send argument *equals* `frameTcp (Message.encode
(deliveredResponse …))` in a transport model where the argument is retained
(e.g. a trace/emit effect), rather than one where it is discarded. The equivalent
response-CONSTRUCTION path *is* pinned (mutating `deliveredResponse`/`scrubAnswerB`
would falsify lines 333-335); only the SEND is un-pinned.
