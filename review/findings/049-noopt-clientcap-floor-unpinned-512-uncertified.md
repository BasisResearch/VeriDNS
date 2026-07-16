# 049 — Non-EDNS client UDP cap floor (512) is unpinned; RFC 1035 §4.2.1 uncertified

**Classification:** bad-spec (spec gap; proofs stay green, wire behavior diverges from unbound)
**Mutation:** `M1-edns-noopt-floor`
**unboundDiffers:** YES

## Claim

`Edns.clientCap` decides how many octets a UDP answer may carry to the client
before the resolver must truncate (set TC=1). RFC 1035 §4.2.1 fixes that limit
at **512 octets** for a *traditional* (non-EDNS, no OPT RR) client. VeriDNS only
proves `clientCap_le : clientCap q ≤ advertisedUdpSize` (≤ 1232). Nothing pins
the value from **below** for the no-OPT case, so the RFC-1035 512-octet ceiling
is *uncertified*: the entire truncation obligation
(`encode(deliveredResponse) ≤ Edns.clientCap query`, discharged in
`ServeSequence.serveSeq_total` / `ResolveWithIOSound.serveDatagram_total`) is
monotone in the cap — raising the floor to 1232 only makes it *easier* to
satisfy, so no theorem statement becomes false.

## Mutation diff

`VeriDNS/Impl/Edns.lean:49`, inside `clientCap`:

```
   match findOptSize q.additional with
-  | none => 512
+  | none => advertisedUdpSize        -- 1232; keeps clientCap ≤ 1232
   | some adv => max 512 (min adv advertisedUdpSize)
```

One token. `clientCap_le` still holds (1232 ≤ 1232).

## Build result (proofs stayed GREEN)

```
$ lake build
...
✔ [293/300] Built VeriDNS.Proof.ResolveWithIOSound (3.3s)
✔ [295/300] Built VeriDNS.Proof.ServeSequence (1.0s)
✔ [296/300] Built VeriDNS.Proof.ServeAdequacy (690ms)
✔ [299/300] Built VeriDNS (601ms)
Build completed successfully (300 jobs).
```

No theorem became false and no tactic broke — a pure bad-spec: `clientCap`'s
no-OPT value is a free parameter anywhere in `[512, 1232]` as far as the
verification is concerned.

## Reproduction (wire)

Test datum: `big.example.test A` served by the leaf auth (203.0.113.12) with 34
A records. Uncompressed that answer encodes ~1122–1194 octets — above the
512-octet traditional limit but below veri-dns's 1232 advertised size, so the
mutated floor changes the truncation decision. Query with `+noedns` (no OPT RR)
and `+ignore` (report the raw UDP datagram, suppress dig's TC→TCP retry). Both
resolvers restarted cold beforehand (rule 3).

```
======== MUTANT VERI-DNS (+noedns +notcp +ignore) ========
;; flags: qr rd ra; QUERY: 1, ANSWER: 34, AUTHORITY: 1, ADDITIONAL: 1
;; MSG SIZE  rcvd: 1194
======== UNBOUND (+noedns +notcp +ignore) ========
;; flags: qr tc rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
;; MSG SIZE  rcvd: 34

======== WIRE (tcpdump, udp) ========
203.0.113.2.5300 > client: UDP, length 1194     # mutant veri-dns: TC=0, >512 in one datagram
203.0.113.3.5301 > client: UDP, length 34       # unbound: TC=1, truncated, expects TCP retry
```

The **mutant** delivers a **1194-byte UDP datagram with TC=0** to a client that
sent no OPT RR. **Unbound**, on the identical cold-cache path against the
identical data, returns a **34-byte response with TC=1** (empty answer,
signalling "retry over TCP"). The stock/baseline veri-dns binary, tested on the
same 34-record answer immediately before the mutant was loaded, also truncated
to a 34-byte TC=1 reply — confirming the divergence is caused solely by the
mutated `clientCap` floor and is reachable at runtime.

## Why the mutant is wrong (citation)

- **RFC 1035 §4.2.1:** "Messages carried by UDP are restricted to 512 bytes (not
  counting the IP or UDP headers). Longer messages are truncated and the TC bit
  is set in the header." A client that sends no OPT RR has not opted into EDNS0
  and is entitled to no more than 512 octets over UDP.
- **RFC 6891 §6.2.3 / §6.2.5:** a responder may only send UDP payloads larger
  than 512 octets when the requestor advertised a larger buffer via an OPT RR.
  Absent OPT, the 512 fallback is mandatory.
- **Unbound** implements exactly this: no OPT ⇒ truncate at 512 with TC=1.

Emitting a 1194-octet non-EDNS UDP response risks IP fragmentation / drops on
legacy paths and is a spec violation the proofs do not catch.

## Fix direction

Pin the floor in the spec: strengthen the truncation obligation (or add a
`clientCap_noopt` lemma) so that when `findOptSize q.additional = none`,
`clientCap q = 512` is *required*, not merely `≤ 1232`. Then this mutation makes
a theorem statement false.
