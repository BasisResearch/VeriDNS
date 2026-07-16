# 050 — EDNS requestor's advertised UDP buffer is not honored; RFC 6891 §6.2.3 uncertified

**Classification:** bad-spec (spec gap; proofs stay green, wire behavior diverges from unbound)
**Mutation:** `M4-edns-ignore-advertised`
**unboundDiffers:** YES
**Same root gap as finding 049 (M1):** `Edns.clientCap`'s value is a free parameter — only `clientCap_le : clientCap q ≤ advertisedUdpSize` (≤ 1232) is proved; nothing pins the cap to the requestor's stated buffer. 049 and 050 are ONE bad-spec with two independently-reachable wire repros (no-EDNS client vs small-buffer EDNS client) and two distinct RFC clauses (1035 §4.2.1 vs 6891 §6.2.3).

## Claim

`Edns.clientCap` decides how many octets a UDP answer may carry to the client
before the resolver must truncate (set TC=1). RFC 6891 §6.2.3 requires the
responder to honor the **requestor's advertised** UDP payload size: a client
that sends an OPT RR advertising a 512-octet receive buffer must not be sent
UDP payloads larger than 512 octets. VeriDNS's spec only proves the cap is
`≤ advertisedUdpSize` (1232, the resolver's *own* max). Nothing ties the cap to
the value the client actually advertised, so the mutant that replaces
`max 512 (min adv advertisedUdpSize)` with a flat `advertisedUdpSize` builds
with all proofs green while sending 1232-octet payloads to clients that asked
for 512.

## Mutation diff

`VeriDNS/Impl/Edns.lean:50`, inside `clientCap`:

```
   match findOptSize q.additional with
   | none => 512
-  | some adv => max 512 (min adv advertisedUdpSize)
+  | some adv => advertisedUdpSize        -- 1232; ignore the requestor's advertised size
```

`clientCap_le` still holds (`advertisedUdpSize ≤ advertisedUdpSize`), so the
truncation obligation `encode(deliveredResponse) ≤ Edns.clientCap query`
(discharged in `ServeSequence.serveSeq_total` /
`ResolveWithIOSound.serveDatagram_total`) is still satisfiable — it is monotone
in the cap, and raising the cap from `adv` to 1232 only makes it easier.

## Build result (proofs stayed GREEN)

```
$ lake build
...
✔ [293/300] Built VeriDNS.Proof.ResolveWithIOSound (3.1s)
✔ [295/300] Built VeriDNS.Proof.ServeSequence (938ms)
✔ [296/300] Built VeriDNS.Proof.ServeAdequacy (638ms)
✔ [299/300] Built VeriDNS (500ms)
Build completed successfully (300 jobs).
```

No theorem became false and no tactic broke — a pure bad-spec: `clientCap`'s
value is a free parameter anywhere in `[512, 1232]` regardless of what the
requestor advertised.

## Reproduction (wire)

Test datum: `big.example.test A`, served by the leaf auth (203.0.113.12) with 34
A records; the uncompressed answer encodes to a 1194-octet datagram — above the
client's advertised 512-octet buffer but below veri-dns's 1232 max, so honoring
vs ignoring the advertised size changes the truncation decision. The client
(`dig +bufsize=512`) sends an OPT RR advertising a 512-octet receive buffer;
`+ignore` reports the raw UDP datagram and suppresses dig's TC→TCP retry. Both
resolvers restarted cold beforehand (rule 3).

```
==== MUTANT VERI-DNS (+bufsize=512 +ignore) ====
;; flags: qr rd ra; QUERY: 1, ANSWER: 34, AUTHORITY: 1, ADDITIONAL: 1
;; MSG SIZE  rcvd: 1194
==== UNBOUND (+bufsize=512 +ignore) ====
;; flags: qr tc rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
; EDNS: version: 0, flags:; udp: 1232
;; MSG SIZE  rcvd: 45
```

Wire (tcpdump on the client link, identical cold-cache path against identical data):

```
203.0.113.2.5300 > client: UDP, length 1194     # mutant veri-dns: TC=0, full 34-record answer in one 1194-byte datagram
203.0.113.3.5301 > client: UDP, length 45       # unbound: TC=1, truncated, empty answer -> retry over TCP
```

The **mutant** delivers a **1194-byte UDP datagram with TC=0** to a client that
explicitly advertised a **512-octet** receive buffer. **Unbound**, on the
identical cold-cache path against the identical data, honors the advertised 512
and returns a **45-byte response with TC=1** (empty answer, "retry over TCP").
The divergence is caused solely by the mutated `clientCap` and is reachable at
runtime from an ordinary EDNS query.

## Why the mutant is wrong (citation)

- **RFC 6891 §6.2.3:** "The requestor's UDP payload size (encoded in the RR
  CLASS field) is the number of octets of the largest UDP payload that can be
  reassembled and delivered in the requestor's network stack. ... Note that path
  MTU ... may impose a smaller limit ... but the values are chosen ... The
  responder ... MUST NOT send UDP responses larger than the requestor's
  advertised buffer size." Sending 1194 octets to a client that advertised 512
  violates this.
- **RFC 1035 §4.2.1:** longer messages are truncated and the TC bit is set.
- **Unbound** implements exactly this: advertised 512 ⇒ truncate at 512 with TC=1.

Emitting a 1194-octet UDP response to a 512-buffer client risks IP fragmentation
/ drops on constrained paths and is a spec violation the proofs do not catch.

## Fix direction

Pin the cap to the requestor's advertisement in the spec: strengthen the
truncation obligation (or add a `clientCap_advertised` lemma) so that when
`findOptSize q.additional = some adv`, `clientCap q = max 512 (min adv 1232)` is
*required*, not merely `≤ 1232`. Combined with the finding-049 no-OPT floor,
this makes both M1 and M4 turn a theorem statement false.
