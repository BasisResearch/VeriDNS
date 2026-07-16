# 063 — EDNS large advertised buffer is not honored (over-truncation); RFC 6891 §6.2.4 honoring-direction uncertified

**Classification:** bad-spec (spec gap; proofs stay green with zero edits, wire behavior diverges from unbound and from stock veri-dns)
**Mutation:** `M4-edns-clientcap-ignored`
**unboundDiffers:** YES
**Same root gap as findings 049 (M1) and 050 (M4-ignore-advertised):** `Edns.clientCap`'s value is a free parameter — only `clientCap_le : clientCap q ≤ advertisedUdpSize` (≤ 1232) is proved. That bound is **one-sided (upper only)**. Nothing pins the cap from **below** to the requestor's advertised buffer, so both the *over-delivery* direction (050: cap raised to 1232, deliver too much) **and** this *over-truncation* direction (cap floored to 512, truncate too eagerly) build green. 049/050/063 are ONE bad-spec with three independently-reachable wire repros.

## Claim

`Edns.clientCap` decides how many octets a UDP answer may carry to the client
before the resolver must truncate (set TC=1). RFC 6891 §6.2.4 lets a requestor
that sends an OPT RR advertising a large UDP buffer receive UDP payloads up to
that size (bounded by the responder's own max, 1232 here) in a single datagram
without truncation. VeriDNS only proves the cap is `≤ advertisedUdpSize`;
nothing requires it to *rise to* the advertised value. The mutant that replaces
`max 512 (min adv advertisedUdpSize)` with a flat `512` builds with **all proofs
green and zero proof edits**, then truncates (TC=1) every UDP answer over 512
octets — even for a client that advertised a 4096-octet buffer — forcing an
unnecessary TCP retry.

## Mutation diff

`VeriDNS/Impl/Edns.lean:50`, inside `clientCap`:

```
   match findOptSize q.additional with
   | none => 512
-  | some adv => max 512 (min adv advertisedUdpSize)
+  | some _ => 512        -- ignore the requestor's advertised buffer; always cap at 512
```

`clientCap_le` still holds (`512 ≤ 1232`) and its proof
`unfold clientCap advertisedUdpSize; split <;> omega` still closes (both arms are
now literal `512`). No theorem statement became false; no tactic broke.

## Build result (proofs stayed GREEN, zero edits)

```
$ lake build
...
✔ [293/300] Built VeriDNS.Proof.ResolveWithIOSound (2.9s)
✔ [295/300] Built VeriDNS.Proof.ServeSequence (906ms)
✔ [296/300] Built VeriDNS.Proof.ServeAdequacy (615ms)
✔ [299/300] Built VeriDNS (504ms)
Build completed successfully (300 jobs).
```

A pure bad-spec: `clientCap`'s value is a free parameter anywhere in `[512, 1232]`
regardless of what the requestor advertised. The truncation obligation
`encode(deliveredResponse) ≤ Edns.clientCap query` (discharged in
`ServeSequence.serveSeq_total` / `ResolveWithIOSound.serveDatagram_total`) is
*antitone* in the cap — lowering the cap to 512 only makes truncation happen
*more*, and the obligation is still satisfiable (a smaller message trivially
fits a smaller cap), so nothing is violated.

## Reproduction (wire)

Test datum: `fat.example.test A`, served by a transient leaf responder on
203.0.113.12 (the leaf-NS address reached via referral) returning an
authoritative (aa=1) answer of **24 A records**. VeriDNS does not name-compress
its answer, so it encodes that RRset to **802 octets** — above the 512 floor but
below veri-dns's own 1232 max, so honoring vs ignoring the advertised buffer
changes the truncation decision. The client (`dig +bufsize=4096`) advertises a
4096-octet buffer; `+ignore` reports the raw UDP datagram and suppresses dig's
TC→TCP retry. Both resolvers restarted cold beforehand (rule 3). The leaf
responder and the whole run are self-contained and torn down (nsd-leaf restored)
in the same shell — no persistent rig state changed.

Stock (un-mutated) veri-dns, measured on the identical path immediately before
loading the mutant, delivers the full answer (a record-count sweep):

```
N=12  VERID[flags: qr rd ra ; MSG SIZE 418]   (TC=0, full)
N=18  VERID[flags: qr rd ra ; MSG SIZE 610]   (TC=0, full)
N=24  VERID[flags: qr rd ra ; MSG SIZE 802]   (TC=0, full)   <- datum used
N=30  VERID[flags: qr rd ra ; MSG SIZE 994]   (TC=0, full)
```

Mutant veri-dns vs unbound at N=24 (both cold, identical responder data):

```
==== VERI-DNS @203.0.113.2:5300 (+bufsize=4096 +ignore) ====
;; flags: qr tc rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
;; MSG SIZE  rcvd: 34
==== UNBOUND @203.0.113.3:5301 (+bufsize=4096 +ignore) ====
;; flags: qr rd ra; QUERY: 1, ANSWER: 24, AUTHORITY: 0, ADDITIONAL: 1
; EDNS: version: 0, flags:; udp: 1232
;; MSG SIZE  rcvd: 429
```

Wire (tcpdump on the client link, identical cold-cache path against identical data):

```
203.0.113.2.5300 > 192.168.53.99: UDP, length 34    # mutant veri-dns: TC=1, answer stripped -> forces TCP retry
203.0.113.3.5301 > 192.168.53.99: UDP, length 429   # unbound: TC=0, full 24-record answer in one datagram
```

The **mutant** sets **TC=1** and strips the answer to a **34-byte** empty
response for a client that advertised a **4096-octet** buffer. **Stock veri-dns**
(802 octets, TC=0) and **unbound** (429 octets, TC=0), on the identical
cold-cache path against the identical data, both deliver the **full 24-record
answer in one UDP datagram**. The divergence is caused solely by the mutated
`clientCap` and is reachable at runtime from an ordinary EDNS query.

## Why the mutant is wrong (citation)

- **RFC 6891 §6.2.3 / §6.2.4:** the requestor's advertised OoP UDP payload size
  is "the number of octets of the largest UDP payload that can be reassembled and
  delivered in the requestor's network stack"; a responder that has computed an
  answer that fits the requestor's advertised size (and its own limits) sends it
  in one UDP datagram rather than truncating. Truncating an 802-octet answer to a
  client that advertised 4096 defeats the purpose of EDNS0 and forces a needless
  TCP fallback.
- **RFC 1035 §4.2.1:** TC / truncation is for messages that *exceed* the usable
  UDP limit — not a message that fits the negotiated buffer.
- **Unbound** implements exactly this: advertised 4096 ⇒ deliver the full 429-octet
  answer with TC=0.

Gratuitous TC=1 on answers that fit the negotiated buffer forces every such
client onto TCP, a latency and load regression, and is a spec violation the
proofs do not catch.

## Fix direction

Pin the honoring direction in the spec: strengthen the truncation obligation (or
add a `clientCap_advertised` lemma) so that when `findOptSize q.additional = some
adv`, `clientCap q = max 512 (min adv advertisedUdpSize)` is *required*, not
merely `≤ advertisedUdpSize`. Combined with the finding-049 no-OPT floor and the
finding-050 upper-honoring requirement, this makes `clientCap` a *pinned*
function of the requestor's advertisement, and turns M1/M4(both directions) into
false theorem statements.
