# 009: No EDNS0 support — OPT ignored, no BADVERS on unsupported EDNS version (RFC 6891)

**Classification:** coverage-gap
**Component:** `VeriDNS/Impl/Server.lean` (UDP receive capped at 512, line 485; reply builders emit no OPT); spec side `VeriDNS/Spec/NetworkSemantics.lean:439` models `negotiatedUdp` only for the *upstream* leg and cites RFC 1035 only.
**Observable:** Yes — client-visible on every query carrying an OPT RR.

## Summary

veri-dns implements no client-facing EDNS0 (RFC 6891) at all:

1. It never emits an OPT pseudo-RR in responses, so it advertises no UDP payload
   size and remains pinned to the RFC 1035 legacy 512-byte limit
   (`UdpSocket.recvFrom clientSock 512`, Server.lean:485; truncation thresholds
   hard-coded to 512 at Server.lean:205-215).
2. A query with an OPT RR of an unsupported EDNS version (version 1) is silently
   ignored and answered NOERROR with data, instead of RCODE 16 (BADVERS) as
   RFC 6891 §6.1.3 requires of EDNS-aware responders.

This is a conformance/interop divergence, not falsified verification: nothing in
`VeriDNS/Spec/` or `rfc/` covers RFC 6891 (grep for `edns|6891|BADVERS|OPT` finds
only the abstract upstream `ednsBuf`/`negotiatedUdp` model, proved against RFC
1035 [1756:1766]). A pure RFC 1035 legacy responder that ignores OPT is
technically grandfathered, but every modern resolver (unbound, BIND) answers
BADVERS and advertises a payload size; the lack of EDNS also forecloses DNS
cookies (RFC 7873) and DNSSEC (DO bit), and forces TCP fallback for any response
over 512 bytes.

## Reproduction (2026-07-07, rig per review/ENV.md)

EDNS version 0 — veri-dns returns no OPT pseudosection; unbound advertises udp 1232:

```
$ ./vm/ssh.sh 'ip netns exec attacker dig +edns=0 +time=3 +tries=1 @10.53.0.2 -p 5300 example.test A'
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 1811
;; flags: qr ra; QUERY: 1, ANSWER: 1, AUTHORITY: 1, ADDITIONAL: 1
   (no OPT PSEUDOSECTION; ADDITIONAL is ns.example.test glue A)

$ ./vm/ssh.sh 'ip netns exec attacker dig +edns=0 +time=3 +tries=1 @10.53.0.3 -p 5301 example.test A'
;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 1232
```

EDNS version 1 (`+noednsneg` to suppress dig's automatic downgrade) — veri-dns
ignores the OPT and answers the question; unbound returns BADVERS with an
empty answer and a version-0 OPT:

```
$ ./vm/ssh.sh 'ip netns exec attacker dig +edns=1 +noednsneg +time=3 +tries=1 @10.53.0.2 -p 5300 example.test A'
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 1976
;; ANSWER: 1 ... example.test. 3589 IN A 10.53.0.100
   (no OPT in reply)

$ ./vm/ssh.sh 'ip netns exec attacker dig +edns=1 +noednsneg +time=3 +tries=1 @10.53.0.3 -p 5301 example.test A'
;; ->>HEADER<<- opcode: QUERY, status: BADVERS, id: 50810
;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 1232
```

## Code anchors

- `VeriDNS/Impl/Server.lean:485` — `UdpSocket.recvFrom clientSock 512` (legacy cap on the client socket).
- `VeriDNS/Impl/Server.lean:205-215` — truncation decided against the constant 512, never against a client-advertised EDNS buffer.
- No OPT (type 41) construction or parsing anywhere under `VeriDNS/Impl/`.
- `VeriDNS/Spec/NetworkSemantics.lean:439` — `negotiatedUdp` exists only for the resolver-to-authoritative leg and is `rfc_proves`'d against RFC 1035 [1756:1766]; RFC 6891 is absent from `rfc/`.

## Citations

- RFC 6891 §6.1.3: "If a responder does not implement the VERSION level of the
  request, then it MUST respond with RCODE=BADVERS."
- RFC 6891 §6.2.3/§7: responders lacking EDNS elicit requestor fallback, but a
  responder that supports EDNS must include an OPT advertising its payload size.
- Reference behavior: unbound 10.53.0.3:5301 (above) returns EDNS v0 / udp 1232
  and BADVERS on version 1.

## Why verification did not catch it

The verified spec's EDNS model (`ednsBuf` / `negotiatedUdp`) covers only the
upstream query path and is anchored to RFC 1035's 512-byte text; RFC 6891 is not
among the RFCs in `rfc/`, so no theorem constrains the client-facing OPT
handling. Closing the gap requires importing RFC 6891 and specifying
responder-side OPT echo + BADVERS.
