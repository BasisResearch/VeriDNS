# 030 — acceptResponse validates only id + question, never the QR bit or OPCODE of the upstream datagram

**Classification:** impl-bug (confirmed, observable)
**Component:** `VeriDNS/Impl/Server.lean` — `acceptResponse` (:43-47), applied at `ioResumeLoop` (:412); `prepareResponse` (:30-31)
**Reference:** RFC 1035 §4.1.1 (QR=1 defines a response; OPCODE is copied from the request); unbound `services/outside_network.c` reply handling (drops query-shaped / opcode-mismatched datagrams before treating their sections as answer data)

## Summary

The upstream-response gate accepts any datagram whose transaction id and
question match the outstanding query, without checking that it is actually a
*response* (`QR=1`) or that its `OPCODE` equals the query's:

```
def acceptResponse (sent : Format) (resp : Format) : Option Format :=
  if resp.header.id == sent.header.id
      && questionMatches resp.question sent.question then
    some resp
  else none
```

`questionMatches` only compares qname/qtype/qclass. Neither `resp.header.qr`
nor `resp.header.opcode` is inspected. A query-shaped datagram (`QR=0`) or a
non-QUERY-opcode datagram that matches id+question and passes the transport
gate `datagramMatches` (:230, source == queried server IP:port) is fed straight
into `afterResume` as if it were a legitimate answer. Separately,
`prepareResponse` (:30-31) rewrites `qr/ra/aa/z` on the client-facing reply but
**not** `opcode`, so a forged upstream opcode leaks through to the stub client.

## Reproduction (on the rig)

The upstream transport (`ffi/recvfrom.c`, `veri_dns_exchange`) uses a fresh
**unconnected** socket per exchange and accepts the *first* datagram from any
source; the Lean gate then decides acceptance. To isolate the QR/OPCODE check,
the leaf authoritative server (`10.53.0.12`, reached by referral) was replaced
with a responder that returns the correct txid + question but with a chosen QR
bit / opcode plus a forged `A` record (`review/env/qr0responder.py`).

```
# stop the real leaf, run the malicious responder on the leaf address
systemctl stop veridns-auth-leaf
systemd-run --unit=veridns-qr0 --collect \
  ip netns exec auth python3 /opt/dnsenv/qr0responder.py 6.6.6.6 --qr 0 --opcode 0
```

### Case A — QR=0 (query-shaped) datagram, fully observable poison

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 poison1.example.test A     # veri-dns
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 60366
;; flags: qr ra; QUERY: 1, ANSWER: 1, ...
poison1.example.test.  300  IN  A  6.6.6.6           <-- forged answer ACCEPTED

$ ip netns exec attacker dig @10.53.0.3 -p 5301 poison1.example.test A     # unbound
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 55051   <-- rejected
```

Responder log — veri-dns issued **one** query and accepted the one qr=0 reply;
unbound issued **many** retries (it drops each non-response) and then SERVFAILed:

```
replied to ('10.53.0.2', 56497) txid=2f13 qtype=1 qr=0 -> 6.6.6.6   (veri-dns: 1 packet)
replied to ('10.53.0.3', 52606) txid=9445 qtype=1 qr=0 -> 6.6.6.6   (unbound: retry 1)
replied to ('10.53.0.3', 33173) txid=000e qtype=1 qr=0 -> 6.6.6.6   (unbound: retry 2)
... (10+ more unbound retries) ...
```

### Case B — OPCODE=2 (STATUS), QR=1

```
systemd-run --unit=veridns-qr0 --collect \
  ip netns exec auth python3 /opt/dnsenv/qr0responder.py 7.7.7.7 --qr 1 --opcode 2

$ ip netns exec attacker dig @10.53.0.2 -p 5300 poison3.example.test A     # veri-dns
;; Warning: Opcode mismatch: expected QUERY, got STATUS
```

Responder log confirms veri-dns accepted the opcode-2 upstream datagram
(`replied to ('10.53.0.2', 57896) txid=9749 qtype=1 qr=1 -> 7.7.7.7`) and built
a client reply whose header carried `opcode: STATUS` — leaked verbatim from the
forged upstream response because `prepareResponse` never normalizes opcode.
(dig then discards that malformed reply client-side, so Case B is a
correctness/robustness divergence rather than a landed poison; Case A is the
landed poison.) unbound returned nothing for the same responder.

## Impact

RFC 1035 §4.1.1 makes `QR=1` the definition of a response and specifies OPCODE
is echoed from the query; a hardened resolver (unbound) discards a datagram that
is query-shaped or opcode-mismatched *before* parsing its answer/authority
sections. veri-dns treats such datagrams as authoritative answers. Because the
transport socket is unconnected and accepts the first matching datagram, an
off-path attacker who wins the id + source-IP:port match already had a poisoning
primitive; this gap additionally lets *query-shaped* forgeries through, and lets
a forged non-QUERY opcode corrupt the client-facing header. Defense-in-depth
divergence from unbound, directly observable as A/B above.

## Fix sketch

In `acceptResponse`, also require `resp.header.qr == 1` and
`resp.header.opcode == sent.header.opcode`. Separately, `prepareResponse`
should force `opcode := Opcode.query` (or echo the client's request opcode) so a
forged upstream opcode can never reach the stub.

## Rig cleanup

`systemctl stop veridns-qr0` and restart the real leaf:
`systemd-run --unit=veridns-auth-leaf --collect ip netns exec auth nsd -c /opt/dnsenv/nsd/nsd-leaf.conf -d`.
Verified restored: `host.example.test A` → `10.53.0.101` on both resolvers;
`poison9.example.test` → NXDOMAIN.

## Regression re-verification (2026-07-15, post-remediation commit 26b5849)

STILL PRESENT. `acceptResponse` (Server.lean:51-55) is verbatim the flagged
code: checks only `resp.header.id == sent.header.id && questionMatches`, never
QR or opcode. Re-run on the renumbered rig with a crafted leaf responder
(qr0responder2.py on 203.0.113.12), both resolvers restarted:
- Case A (QR=0 query-shaped forgery): veri-dns returns `poison2.example.test A
  6.6.6.6` (NOERROR, landed poison); unbound SERVFAILs. Responder log shows
  veri-dns sent ONE query and accepted the qr=0 reply; unbound retried ~7x and
  refused every non-response.
- Case B (opcode=2 STATUS, QR=1): veri-dns accepts and lands `7.7.7.7`; the
  forged STATUS opcode leaks into the client reply (dig warns "Opcode mismatch:
  got STATUS"). `prepareResponse`/`finalizeForClient` still never normalize
  opcode. Not in the remediation plan; unpinned, unfixed. This is the highest-
  severity item in the parser batch: a landed off-path poisoning primitive.
