# 032 — Client's TC (truncation) bit is reflected verbatim into cache-hit / REFUSED replies

**Classification:** impl-bug (confirmed on the running rig)
**Severity:** medium — a single spoofable UDP flag turns an otherwise-good cached
answer into an unusable "truncated" reply; veri-dns has no TCP listener to fall back to.

## Summary

`finalizeForClient` (`VeriDNS/Impl/Server.lean:29-31`) rewrites only
`qr:=1, ra:=1, aa:=0, z:=0` and never clears the **TC** bit, while
`buildResponse` (`Server.lean:13-24`) seeds every locally-built reply from the
**client's** `query.header`. So a client that sets TC=1 in its *query* gets that
bit reflected straight back into:

- **cache-hit answers** (a full, non-truncated A record delivered with TC=1), and
- **REFUSED** replies (rcode=5 with TC=1).

Per RFC 1035 §4.1.1 the TC bit means "this message was truncated". Returning a
complete answer with TC=1 is a semantic contradiction; per RFC 1035 §4.2.1 /
RFC 7766 a stub that sees TC=1 MUST discard the UDP answer and retry over TCP —
which veri-dns has no listener for — so the good cached answer is thrown away.

unbound rejects any query with TC set in the query header outright with FORMERR.

## Environment

Controlled rig per `review/ENV.md`. veri-dns @10.53.0.2:5300 (verid ns),
unbound @10.53.0.3:5301 (unbound ns), queries from the attacker ns.
`host.example.test A` is primed in both caches first.

Probe script staged at `penn-testing/_vmdns/tcprobe.py` -> `/opt/dnsenv/tcprobe.py`;
it sends a raw UDP query with an arbitrary 16-bit flags word and decodes the
response header. Flags byte layout: `QR|Opcode(4)|AA|TC|RD | RA|Z(3)|RCODE(4)`.

## Reproduction

Prime the cache:
```
ip netns exec attacker dig +short @10.53.0.2 -p 5300 host.example.test A   # 10.53.0.101
```

### Cache-hit path — TC+RD query (flags 0x0300)
```
$ ip netns exec attacker python3 /opt/dnsenv/tcprobe.py 10.53.0.2 5300 0x0300 host.example.test
SENT flags=0x0300 -> tc=1 rd=1
RECV id=0x1234 QD=1 AN=1 NS=0 AR=0 flags=0x8380 {qr=1 aa=0 tc=1 rd=1 ra=1 z=0 rcode=0}
RAW 68 bytes: 12348380...00000acf00040a350065   (0a350065 = 10.53.0.101)

$ ip netns exec attacker python3 /opt/dnsenv/tcprobe.py 10.53.0.3 5301 0x0300 host.example.test
SENT flags=0x0300 -> tc=1 rd=1
RECV id=0x1234 QD=0 AN=0 NS=0 AR=0 flags=0x8101 {qr=1 tc=0 rd=1 ra=0 rcode=1}   # FORMERR, 12 bytes
```
veri-dns returns a **full A record (10.53.0.101)** with **TC=1** — a complete
answer falsely marked truncated. unbound returns FORMERR (RCODE=1), TC cleared.

### REFUSED path — TC set, RD=0 (flags 0x0200)
```
$ ip netns exec attacker python3 /opt/dnsenv/tcprobe.py 10.53.0.2 5300 0x0200 host.example.test
SENT flags=0x0200 -> tc=1 rd=0
RECV id=0x1234 QD=1 AN=0 NS=0 AR=0 flags=0x8285 {qr=1 tc=1 rd=0 ra=1 rcode=5}   # REFUSED, tc=1

$ ip netns exec attacker python3 /opt/dnsenv/tcprobe.py 10.53.0.3 5301 0x0200 host.example.test
SENT flags=0x0200 -> tc=1 rd=0
RECV id=0x1234 QD=0 AN=0 NS=0 AR=0 flags=0x8001 {qr=1 tc=0 rd=0 ra=0 rcode=1}   # FORMERR, tc=0
```
veri-dns reflects TC=1 into a REFUSED reply; unbound returns FORMERR with TC=0.

### Control — clean RD-only query (flags 0x0100)
```
$ ip netns exec attacker python3 /opt/dnsenv/tcprobe.py 10.53.0.2 5300 0x0100 host.example.test
SENT flags=0x0100 -> tc=0 rd=1
RECV id=0x1234 QD=1 AN=1 flags=0x8180 {qr=1 aa=0 tc=0 rd=1 ra=1 z=0 rcode=0}   # correct: tc=0, full answer
```
With TC=0 in the query, veri-dns correctly emits TC=0. This is **selective**: the
Z region (AD/CD/Z) is stripped (`z=0` in every response, from `finalizeForClient`'s
`z:=0`), only the TC (and RD, intentionally echoed) bit leaks — confirming the
missing TC-clear in `finalizeForClient`, not a blanket header echo.

## Root cause

`Server.lean:29-31`:
```lean
def finalizeForClient (resp : Format) : Format :=
  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }
```
TC is never reset. Every client-facing reply is built either from
`buildResponse query …` (which starts from `query.header`, carrying the client's
TC — the REFUSED/error path) or from the resolver's `resp` (cache-hit path), and
`finalizeForClient` is the last touch before send. A resolver's own responses set
TC only via `truncateUdp` (real 512-byte overflow); the client's requested TC must
be zeroed. The fix is to add `tc := 0` in `finalizeForClient` (the genuine-overflow
TC is applied afterward in `serveOne` via `truncateUdp`, so this is safe).

## Distinctness

Distinct from KB 015/031 (upstream TC handling on the network path — those reflect
the *authoritative* server's TC) and from the RD-echo item. This is the *client's*
own TC bit leaking into *locally-built* (cache-hit / REFUSED) replies. Cache-miss /
network path is unaffected because the upstream response's TC is used there instead.

## Citations

- RFC 1035 §4.1.1: "TC — TrunCation — specifies that this message was truncated
  due to length greater than that permitted on the transmission channel."
- RFC 1035 §4.2.1 / RFC 7766 §5: a client receiving a TC=1 response over UDP
  discards it and retries over TCP. veri-dns has no TCP listener (KB TCP-RST).
- unbound reference behavior: rejects query-header TC with FORMERR (observed above).
