# 067 — TCP slow-loris: one stalled connection wedges all DNS-over-TCP service

**Severity:** High (denial of service against the mandatory TC=1 → TCP fallback path)
**Component:** `VeriDNS/Main.lean:104` (`tcpServeLoop`), `ffi/recvfrom.c` (`veri_dns_tcp_accept` / `veri_dns_tcp_recv_msg`)
**Classification:** impl-bug (architecture) — confirmed by differential vs unbound
**Status:** CONFIRMED — unbound disagrees on the identical path against identical data with a cold cache.

## Summary

veri-dns serves DNS-over-TCP from a single, strictly serial accept loop
(`tcpServeLoop`, spawned once as one `IO.asTask` in `main`). Each iteration:

1. `tcpAccept listenSock` — accept exactly one connection (FFI sets a 3s
   `SO_RCVTIMEO` on the accepted socket, `ffi/recvfrom.c:440-441`).
2. `tcpRecvMsg conn` — **blocking** framed read of the 2-byte length prefix +
   body (`ffi/recvfrom.c:466,478`), up to the 3s recv timeout.
3. serve one datagram, `tcpClose conn`, then recurse.

There is no per-connection concurrency. A client that connects and sends nothing
holds the one accept-loop thread inside the blocking `recv()` for the full ~3s
timeout, during which **no other TCP client can be accepted or served**. A
sustained trickle of such connections denies DNS-over-TCP to everyone —
including the mandatory TC=1 → TCP-retry fallback for answers too large for UDP.

Note also: the blocking `tcpRecvMsg` at `Main.lean:113` runs *before* the
`permitted acl clientAddr` ACL check inside `serveTcpDatagram`
(`Impl/Server.lean`), so a host that can merely reach TCP port 5300 occupies the
loop even if the client ACL would ultimately reject it — the ACL never gets a
chance to run.

## Reproduction

Rig: renumbered to 203.0.113.0/24. veri-dns @203.0.113.2:5300 (netns `verid`),
unbound @203.0.113.3:5301 (netns `unbound`), client in netns `attacker`. Both
resolvers cold-restarted (`systemctl restart veridns-verid veridns-ref; sleep 2`)
before each run.

Scripts: `scratchpad/loris.py` (3 stalled conns for 4s, one concurrent timed
+tcp query) and `scratchpad/loris2.py` (sustained trickle of 6 conns, 4
concurrent queries).

### 3 stalled connections (loris.py)

```
# ip netns exec attacker python3 /tmp/loris.py 203.0.113.2 5300 VERID
===== VERID =====
  baseline legit +tcp query: 0.00s  reply=OK
   opened 3 stalled TCP connections (sending nothing)
  DURING stall, legit +tcp query: 3.70s  reply=OK      <-- blocked behind stallers
  AFTER stall, legit +tcp query: 0.00s  reply=OK

# ip netns exec attacker python3 /tmp/loris.py 203.0.113.3 5301 UNBOUND
===== UNBOUND =====
  baseline legit +tcp query: 0.00s  reply=OK
   opened 3 stalled TCP connections (sending nothing)
  DURING stall, legit +tcp query: 0.00s  reply=OK      <-- served concurrently
  AFTER stall, legit +tcp query: 0.00s  reply=OK
```

### Sustained trickle (loris2.py) — full DoS

```
=== VERID persistent-loris ===
  legit +tcp query #0 during sustained stall: 8.01s reply=ERR:timed out   <-- query FAILS entirely
  legit +tcp query #1 during sustained stall: 1.50s reply=OK
  legit +tcp query #2 during sustained stall: 0.00s reply=OK
  legit +tcp query #3 during sustained stall: 0.00s reply=OK

=== UNBOUND persistent-loris ===
  legit +tcp query #0 during sustained stall: 0.00s reply=OK
  legit +tcp query #1 during sustained stall: 0.00s reply=OK
  legit +tcp query #2 during sustained stall: 0.00s reply=OK
  legit +tcp query #3 during sustained stall: 0.00s reply=OK
```

Under a sustained trickle, veri-dns's first legitimate +tcp query timed out
completely (8s dig timeout, no answer) while unbound served every concurrent
query at 0.00s.

## Why this is a veri-dns defect, not the DNS trust model

unbound, on the identical rig, identical path, identical data, cold cache,
serves legitimate DNS-over-TCP queries concurrently with the stalled
connections — it multiplexes TCP clients (poll/event loop + per-client state) and
enforces per-connection idle timeouts without wedging the whole service. veri-dns
blocks. The behaviors differ, so this is an implementation defect in veri-dns's
serial single-threaded TCP loop, not an inherent property of DNS.

RFC 7766 §6.2.1 ("DNS Transport over TCP — Implementation Requirements")
explicitly requires servers to handle concurrent TCP connections and to apply
idle timeouts precisely so that a single slow/idle client cannot deny service:
"To mitigate the risk of unintentional server overload, DNS clients MUST take
care to minimise the number of concurrent TCP connections... Similarly, DNS
servers SHOULD... support the concurrent processing of multiple requests." A
single serial accept loop with a 3s blocking recv before any per-client timeout
management violates the availability intent of this requirement.

## Root cause

`tcpServeLoop` (`Main.lean:104-128`) is a recurse-per-connection structure with
no concurrency; the blocking `recv()` in `veri_dns_tcp_recv_msg` under the 3s
`SO_RCVTIMEO` set by `veri_dns_tcp_accept` (`ffi/recvfrom.c`) means each stalled
connection monopolizes the sole loop thread for up to 3s. Fix direction: serve
each accepted connection on its own task (bounded pool), and/or move the ACL
check ahead of the blocking read, and/or shorten the pre-first-byte idle timeout.

## Cleanliness

No source was mutated; this is a runtime/architecture defect observed against the
shipped binary. Both resolvers left cold-restarted at baseline. Rig tracked
source clean.
