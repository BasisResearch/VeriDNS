# 058 — TCP: exactly one query per connection; no reuse, RST on pipelined queries (RFC 7766 violation)

**Classification:** impl-bug (also a spec/coverage gap: no proof constrains multi-query TCP connection handling)
**Severity:** medium (interoperability / correctness). A conforming DNS-over-TCP
client that reuses a connection or pipelines queries loses every query after the
first; pipelined data is discarded with a RST.
**unboundDiffers:** YES — same path, same data, cold caches on both: unbound
answers both queries on a reused connection and both pipelined queries; veri-dns
answers only the first and drops/RSTs the rest.

**Component:** `VeriDNS/Main.lean:104-128` (`tcpServeLoop`).

Related but distinct from **057** (which frames the same single-shot loop as a
*serial slow-loris DoS*). This finding is the **RFC 7766 interoperability**
consequence of the same root cause: connection reuse and pipelining are simply
unsupported.

---

## Root cause

`tcpServeLoop` accepts one connection, reads **exactly one** framed message with
`tcpRecvMsg`, serves it, and then *unconditionally* closes the connection —
there is no inner loop over further messages on the same connection:

```lean
match ← tcpRecvMsg conn with          -- Main.lean:113  (reads ONE frame)
| none => pure rb2
| some queryBytes =>
  ...
  serveTcpDatagram ... queryBytes ...  -- Main.lean:117  (answers that ONE frame)
  ...
finally
  tcpClose conn                        -- Main.lean:122  (ALWAYS closes)
```

After the single answer is written, `tcpClose conn` runs in the `finally`, so:

- A second query written on the same connection is never read → the server has
  already sent FIN → client sees EOF (`None`).
- Any bytes the client pipelined into the same segment behind the first query
  are still sitting in the kernel receive buffer when the socket is closed →
  the close turns into a **RST** (`ECONNRESET`) at the client.

## Reproduction

Rig: veri-dns @203.0.113.2:5300 (netns `verid`), unbound @203.0.113.3:5301
(netns `unbound`). Both restarted for cold caches immediately before each run:

```
systemctl restart veridns-verid veridns-ref; sleep 2
```

Driver: `scratchpad/tcp2.py` (copied into the VM as `/tmp/tcp2.py`). It opens a
TCP connection, sends a length-prefixed query, reads the framed answer, then
(a) sends a second query on the *same* socket, and separately (b) pipelines two
length-prefixed queries in a single `send()`. Answers are printed as
`(frame_len, qid, rcode, ancount)`.

```
$ ip netns exec attacker python3 /tmp/tcp2.py 203.0.113.2 5300   # veri-dns
--- 203.0.113.2:5300 sequential-reuse (RFC7766) ---
  q1 answer: (130, '0x1111', 0, 1)
  q2 answer (same conn): None                                    # <-- FIN, query dropped
--- 203.0.113.2:5300 pipelined ---
  first frame: (58, '0x3333', 0, 1)
  second frame EXC: ConnectionResetError: [Errno 104] Connection reset by peer

$ ip netns exec attacker python3 /tmp/tcp2.py 203.0.113.3 5301   # unbound
--- 203.0.113.3:5301 sequential-reuse (RFC7766) ---
  q1 answer: (46, '0x1111', 0, 1)
  q2 answer (same conn): (51, '0x2222', 0, 1)                    # <-- both answered
--- 203.0.113.3:5301 pipelined ---
  first frame: (46, '0x3333', 0, 1)
  second frame: (51, '0x4444', 0, 1)                            # <-- both answered
```

Result is stable across repeated cold-cache restarts.

## Why it is a bug (RFC citation)

RFC 7766 §6.2.1 ("Connection Reuse"): *"In order to achieve performance on par
with UDP, DNS clients SHOULD support connection reuse by sending multiple
queries and responses over a single persistent TCP connection."* — and
correspondingly a server **must** be able to read more than one query per
connection. RFC 7766 §6.2.1.1 ("Query Pipelining"): *"In order to achieve the
best performance ... clients MAY send multiple queries before receiving any of
the outstanding responses ... To avoid deadlocks, servers ... MUST process the
pipelined queries."* veri-dns supports neither: it services exactly one query
and then closes, so reuse yields EOF on the second query and pipelining yields a
RST that discards the already-buffered second query.

unbound, on the identical wire path against identical zone data with a cold
cache, supports both — demonstrating this is an implementation shortfall, not
the DNS trust model.

## Spec gap

No theorem in `VeriDNS/Proof/ServeTcp.lean` constrains multi-query TCP
connection handling; the capstone reasons only about a single
`serveTcpDatagram` invocation. So the one-shot loop builds green — the spec
never demanded connection reuse or pipelining.

## Re-verification (independent, 2026-07-16)

Independently reproduced by a separate runtime-verification pass with a fresh
driver (`/tmp/tcpreuse.py`), both resolvers restarted cold immediately before
each run (`systemctl restart veridns-verid veridns-ref; sleep 2`):

```
$ ip netns exec attacker python3 /tmp/tcpreuse.py 203.0.113.2 5300   # veri-dns
  q1 answer: (130, '0x1111', 0, 1)
  q2 answer (same conn): None                                        # FIN/EOF
  pipelined first frame: (58, '0x3333', 0, 1)
  pipelined second EXC: ConnectionResetError(104, 'Connection reset by peer')

$ ip netns exec attacker python3 /tmp/tcpreuse.py 203.0.113.3 5301   # unbound
  q1 answer: (46, '0x1111', 0, 1)
  q2 answer (same conn): (51, '0x2222', 0, 1)                        # both answered
  pipelined: (46, '0x3333', 0, 1) then (51, '0x4444', 0, 1)          # both answered
```

Identical divergence; finding stands.

## Second independent re-verification (2026-07-16)

A further isolated pass with a new driver (`/tmp/tcpreuse3.py`, distinct qnames
per query: q1 `example.test`, q2 `host.example.test`), both resolvers restarted
cold immediately beforehand (`systemctl restart veridns-verid veridns-ref;
sleep 2`; both `active`):

```
$ ip netns exec attacker python3 /tmp/tcpreuse3.py 203.0.113.2 5300 VERID
--- Test A: sequential reuse ---
  q1 reply: (130, '0xaaaa', 0, 1)
  q2 reply (same conn): None                                   # FIN/EOF, query lost
--- Test B: pipelined (one send) ---
  frame1: (58, '0xcccc', 0, 1)
  frame2 EXC: ConnectionResetError(104, 'Connection reset by peer')

$ ip netns exec attacker python3 /tmp/tcpreuse3.py 203.0.113.3 5301 UNBOUND
--- Test A: sequential reuse ---
  q1 reply: (46, '0xaaaa', 0, 1)
  q2 reply (same conn): (51, '0xbbbb', 0, 1)                   # both answered
--- Test B: pipelined (one send) ---
  frame1: (46, '0xcccc', 0, 1)
  frame2: (51, '0xdddd', 0, 1)                                 # both answered
```

Same divergence a third time; CONFIRMED.

## Rig hygiene

No source was edited and no responder/config was staged. Only a throwaway driver
`/tmp/tcp2.py` was written inside the VM. Tracked source is unchanged.
