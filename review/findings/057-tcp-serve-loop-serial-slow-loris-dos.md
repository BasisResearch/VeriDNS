# 057 — TCP serve loop is single-shot + serial: one stalled partial-frame connection blocks all other TCP clients (slow-loris DoS)

**Severity:** medium (availability). TCP DNS service can be held permanently
unavailable by a single attacker with negligible resources. UDP is unaffected.

**Component:** `VeriDNS/Main.lean:104-128` (`tcpServeLoop`), spawned once at
`Main.lean:145`. FFI recv deadline in `ffi/recvfrom.c:440-442, 460-489`.

## Root cause

`tcpServeLoop` is a single, recursive, single-threaded task (spawned exactly
once via `IO.asTask (tcpServeLoop …) Task.Priority.dedicated`, Main.lean:145).
Each iteration is fully serial:

```
tcpAccept listenSock        -- accept ONE connection
  → tcpRecvMsg conn         -- ONE blocking framed read, inline in the loop
  → serveTcpDatagram …      -- resolve + answer
  → tcpClose conn
→ recurse to accept the NEXT connection
```

The framed read (`veri_dns_tcp_recv_msg`, recvfrom.c:460) reads a 2-byte length
prefix, then loops `recv()` until it has that many body bytes. The accepted
socket has `SO_RCVTIMEO = 3s` (recvfrom.c:441). An attacker who sends a length
prefix promising a full frame but only a few body bytes, then holds the socket
open, parks the *entire* listener inside that recv loop until the 3s deadline
fires. Because accept and recv are inline in the same serial task, **no other
TCP client can be accepted or served during that window.** Opening one fresh
stalled connection every <3s keeps veri-dns's TCP service permanently down.

This is the TCP analogue of the known UDP head-of-line finding (017): same
serial serve-loop architecture, reached here through the TCP framing recv
deadline.

## Reproduction

Rig: veri-dns @203.0.113.2:5300 (netns `verid`), unbound @203.0.113.3:5301
(netns `unbound`), attacker netns. Test script:
`penn-testing/_vmdns/loris.py` — opens a TCP conn, sends `struct.pack('>H',
len(q))` then only `q[:3]`, holds it, then times a second full TCP query on a
*new* connection.

Both resolvers restarted for cold caches before every measurement
(`systemctl restart veridns-verid veridns-ref; sleep 2`).

### Baseline — no stall, cold cache (TCP resolution is instant on both)
```
[verid]   BASELINE (no stall) 130B in 0.00s
[unbound] BASELINE (no stall)  46B in 0.00s
```

### Slow-loris — one stalled partial-frame connection, then a 2nd full client
```
[verid]   second client got 130B answer (anc=1) in 2.51s   <-- blocked ~3s
[unbound] second client got  46B answer (anc=1) in 0.00s   <-- unaffected
```
Reproduced (run 2): verid 2.53s, unbound 0.00s.

Since the no-stall baseline is 0.00s, the entire ~2.5s on veri-dns is the
stalled connection blocking the accept loop until `SO_RCVTIMEO` fires — not
resolution cost. The delta tracks the 3s recv deadline exactly.

### UDP is a separate path — stays fast during a TCP stall
```
UDP during TCP stall (verid): 0.00s
```
A background stalled TCP connection does not affect UDP (served by the separate
`udpServeLoop` task, Main.lean:151), confirming the block is TCP-specific and
architectural, not a shared-lock issue.

## Why unbound differs (oracle)

unbound handles TCP connections asynchronously via its libevent comm layer:
each accepted TCP connection is an independent event-driven state machine
(`comm_point`), and a connection blocked mid-frame simply sits in the
readable/timeout wait set while other connections and queries continue to be
serviced. A single stalled partial-frame connection therefore has zero effect
on other TCP clients (measured 0.00s). unbound additionally bounds concurrent
TCP with `incoming-num-tcp` and per-connection `tcp-idle-timeout`, so even
resource exhaustion is bounded rather than a total serial blackout.

## RFC context

RFC 7766 §6.2.3 (DNS Transport over TCP) explicitly warns resolvers to mitigate
exactly this: "To mitigate the risk of unintentional server overload, DNS
clients MUST take care … Similarly, DNS servers … SHOULD … limit the number of
concurrent TCP connections" and recommends per-connection idle timeouts and
concurrent-connection handling. A serial single-connection-at-a-time accept
loop with a 3s blocking read per connection is the failure mode that guidance
is written against.

## Suggested fix

Handle each accepted TCP connection in its own task (`IO.asTask … conn` per
connection) so `tcpAccept` returns to the accept loop immediately, and/or bound
the number of concurrent TCP connections and shorten/idle-timeout partial-frame
reads. The cache mutex already serializes shared state, so per-connection tasks
are safe.

## Cleanup

Test artifact `penn-testing/_vmdns/loris.py` is untracked (inside the untracked
`penn-testing/` tree); no tracked source was modified, no `lake build` was run.
Both resolvers restarted to a clean baseline after the experiment.
