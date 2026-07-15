# 031 - Upstream UDP receive buffer hard-capped at 512 bytes silently clips larger TC=0 datagrams -> decode failure -> SERVFAIL

- **Severity:** medium (availability / interop)
- **Class:** impl-bug (observable wrong behaviour vs. reference resolver)
- **Component:** `ffi/recvfrom.c` (`veri_dns_exchange`) -> `VeriDNS/Impl/Server.lean` (`forwardQuery` -> `Message.decode`)
- **Reproduced on the rig:** yes (differential vs. unbound, with tcpdump proof)

## Summary

The upstream UDP exchange FFI receives every authoritative reply into a
**fixed 512-byte** buffer and ignores the datagram-truncation flag the kernel
reports. When an authoritative server returns a single UDP datagram larger than
512 bytes with **TC=0** (a full, untruncated answer), the kernel delivers the
whole datagram to veri-dns, but the FFI copies only the first 512 bytes, sets
the Lean byte-array size to the clipped count, and drops the `MSG_TRUNC`
indication. The clipped buffer cuts a resource record mid-way, so
`Message.decode` fails, `forwardQuery` returns `none`, and the resolver
re-queries in a tight loop and ultimately answers the client **SERVFAIL**.

unbound, receiving the identical datagram, decodes it whole and returns the
answer.

This is a **distinct mechanism** from:
- 009 (no EDNS0 advertised) - here the auth server sends a full TC=0 datagram
  regardless of EDNS; the loss happens inside veri-dns after the kernel already
  delivered every byte.
- 015 (no TCP fallback on TC=1) - here TC=0; there is nothing telling the
  resolver to retry over TCP, and no truncation is even detected.
- 017 (junk single-datagram drop) - the datagram is well-formed and complete on
  the wire; it is veri-dns's own receive path that corrupts it.

## Offending code

`ffi/recvfrom.c`, in `veri_dns_exchange` (approx. lines 277-297):

```c
lean_object *buf = lean_alloc_sarray(1, 0, 512);          /* 512-byte cap   */
struct iovec iov = { .iov_base = lean_sarray_cptr(buf), .iov_len = 512 };
...
ssize_t n = recvmsg(fd, &msg, 0);                          /* flags = 0      */
close(fd);
if (n < 0) { ... }
lean_to_sarray(buf)->m_size = (size_t)n;                   /* clipped size,  */
                                                           /* msg.msg_flags  */
                                                           /* (MSG_TRUNC)    */
                                                           /* never checked  */
```

For a 1011-byte datagram, `recvmsg` returns `n = 512`, sets `MSG_TRUNC` in
`msg.msg_flags` (ignored), and the remaining 499 bytes are discarded. The
resulting 512-byte buffer ends in the middle of a record, so `rdlength` /
`readBytes` overruns and decode fails.

## Reproduction on the controlled rig

A fake authoritative leaf (`review/env/../_vmdns/bigresp.py`, staged in the VM)
replaced `nsd-leaf` on `10.53.0.12:53` and answered `*.example.test A` with a
**single 1011-byte UDP datagram, 61 A records, TC=0** (first record is the
genuine `10.53.0.101`). Root and TLD `nsd` were left untouched so the normal
referral chain still reaches the fake leaf. Fresh (uncached) qnames were used.

Orchestration script: `penn-testing/_vmdns/run-big.sh` (mode `big` = >512B TC=0;
mode `small` = 53B control). Both resolvers were queried from the `attacker` ns.

### Oversized (>512B, TC=0)

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 big2.example.test A     # veri-dns
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 39444
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0

$ ip netns exec attacker dig @10.53.0.3 -p 5301 u-big2.example.test A   # unbound
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 62440
;; flags: qr rd ra; QUERY: 1, ANSWER: 61 ...
u-big2.example.test. 300 IN A 10.53.0.101   (+ 60 more)   ;; MSG SIZE rcvd: 1024
```

tcpdump on veri-dns's own interface (`v-verid`) proves the **full 1011-byte
TC=0 datagram is delivered by the kernel** to veri-dns's ephemeral ports:

```
IP 10.53.0.12.53 > 10.53.0.2.47642: 20322* 61/0/0 A 10.53.0.101, A 10.53.1.0, ... (1011)
IP 10.53.0.12.53 > 10.53.0.2.53715: 21341* 61/0/0 A 10.53.0.101, ...           (1011)
   ... (veri-dns re-queried the leaf ~40 times, each got the full 1011 bytes) ...
```

The fake leaf's log shows unbound resolved it with **one** upstream query
(port 59041, `replied 1013 bytes`) while veri-dns fired **~40** queries
(decode-fail -> `forwardQuery none` -> re-query loop) before giving up with
SERVFAIL.

### Control (<512B, TC=0) - same responder, only size changed

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 small1.example.test A   # veri-dns
;; ->>HEADER<<- status: NOERROR ...
small1.example.test. 300 IN A 10.53.0.101
```

With a 53-byte reply from the *identical* responder, veri-dns resolves
correctly with a **single** upstream query. The only variable between success
and SERVFAIL is the datagram exceeding 512 bytes -> the FFI clip is the
confirmed cause.

## Why this matters / RFC + reference basis

- **RFC 1035 sec. 4.2.1**: 512 bytes is the limit for UDP *when EDNS0 is not in
  use and the server chooses to truncate*; a server that returns a larger UDP
  datagram is signalling (via TC) whether more data exists. A resolver must
  either honour the truncation flag or accept the bytes it is given - not
  silently discard payload it already received.
- **RFC 6891 (EDNS0)**: the modern remedy is to advertise a larger requestor
  UDP payload size; veri-dns advertises none (009) *and* additionally cannot
  even ingest a large datagram that arrives, because of this 512-byte copy cap.
- **unbound** (`services/listen_dnsport`, `outside_network`) sizes its receive
  buffers to the advertised EDNS bufsize (default `msg-buffer-size` / 1232+) and
  checks `MSG_TRUNC`; it ingested the same 1011-byte datagram intact and
  answered NOERROR.
- Real-world triggers: large TXT/SPF/DKIM RRsets, DNSSEC responses, or any auth
  server (or middlebox) that emits an oversized UDP answer without setting TC.
  Against such servers veri-dns degrades to SERVFAIL where a conformant resolver
  succeeds - a self-inflicted availability failure, and a needless upstream
  amplification (the ~40x re-query storm observed).

## Suggested fix

Size the receive buffer to at least the advertised EDNS payload (or 65535 for a
generous cap), and inspect `msg.msg_flags & MSG_TRUNC`: on truncation either
accept up to the real length or fail the exchange explicitly and fall back to
TCP (see 015). Do not set the Lean array size to a count that severs a record.

## Artifacts

- Fake leaf responder: `penn-testing/_vmdns/bigresp.py`
- Orchestration: `penn-testing/_vmdns/run-big.sh` (`big` / `small` modes)
- Rig restored afterwards: `nsd-leaf` relaunched, `host.example.test A
  10.53.0.101` served again.
