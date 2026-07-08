# 018 — Non-IN QCLASS recursed through IN root hints: SERVFAIL where unbound REFUSES, and upstream `version.bind` CH TXT relayed to clients

- **Severity:** low/medium (wrong rcode semantics invite client retries; upstream software-version disclosure; class-mixing scope slip)
- **Classification:** impl-bug
- **Status:** CONFIRMED on the running rig (veri-dns @10.53.0.2:5300 vs unbound @10.53.0.3:5301, wire capture of the upstream leg included)
- **Component:** `VeriDNS/Impl/Server.lean` — client question forwarded verbatim into resolution (`serveOne`/`resolveWithIO` path); glue leg `mkAddressQuery` hardcodes `qclass := 1` (line 57)

## Claim

veri-dns has no QCLASS scope check. A client query in CHAOS (or any non-IN)
class is fed verbatim into the IN-rooted recursive machinery:

1. **CH query the IN root cannot answer** (`example.test A` in class CH):
   veri-dns walks the IN root hints, gets no CH data, and returns **SERVFAIL**
   (rcode 2, "transient server failure" — clients retry). unbound returns
   **REFUSED** (rcode 5, policy, non-retryable), its default for a class it
   does not serve.
2. **CH query the upstream authoritative DOES answer** (`version.bind CH TXT`):
   veri-dns recurses it to the root nsd and **relays nsd's version string to
   the client** (`"NSD 4.14.3"`). unbound answers such CH queries locally from
   its own built-in (`"unbound 1.25.1"`) and never forwards them.
3. **Class mixing:** the main query leg carries the client's QCLASS, but the
   glueless NS-address leg is hardcoded to `qclass = 1`
   (`Server.lean:57`, `mkAddressQuery`), so a single resolution can issue
   queries in two different classes against the same delegation tree. DNS
   classes are independent namespaces (RFC 6895 §3.2); the IN root hints
   (RFC 1034 §5.3.3 SBELT) carry no CH delegation, so recursing CH through
   them is semantically wrong, not merely unusual.

## Reproduction (on the rig)

CH-class recursive query, veri-dns vs unbound:

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 -c CH example.test A
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 41025
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
;example.test.			CH	A

$ ip netns exec attacker dig @10.53.0.3 -p 5301 -c CH example.test A
;; ->>HEADER<<- opcode: QUERY, status: REFUSED, id: 35979
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
;example.test.			CH	A
```

`version.bind` CH TXT — veri-dns relays the upstream authoritative's version,
unbound answers with its own:

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 version.bind CH TXT
;; ->>HEADER<<- status: NOERROR ... flags: qr ra; QUERY: 1, ANSWER: 1
version.bind.		0	CH	TXT	"NSD 4.14.3"      <-- upstream nsd's banner, recursed

$ ip netns exec attacker dig @10.53.0.3 -p 5301 version.bind CH TXT
;; ->>HEADER<<- status: NOERROR ... flags: qr rd ra; QUERY: 1, ANSWER: 1
version.bind.		0	CH	TXT	"unbound 1.25.1"  <-- unbound's built-in local answer
```

Wire capture in the `verid` netns during the veri-dns `version.bind` query
proves the CH question is forwarded upstream to the IN root hint address:

```
$ ip netns exec verid tcpdump -r /tmp/ch-upstream.pcap -n
20:54:41.936535 v-verid Out IP 10.53.0.2.35880 > 198.41.0.4.53: 24225 TXT CHAOS? version.bind. (30)
20:54:41.936680 v-verid In  IP 198.41.0.4.53 > 10.53.0.2.35880: 24225- 1/0/0 CHAOS TXT "NSD 4.14.3" (53)
```

## Source

`VeriDNS/Impl/Server.lean:49-57` — the glue/address leg is pinned to IN while
the main leg inherits the client's class:

```lean
def mkAddressQuery (name : ByteArray) : Format :=
  { header := { ... }
    question := #[{ qname := name, qtype := 1, qclass := 1 }]   -- hardcoded IN
    ... }
```

No code path inspects the client's `qclass` to gate service; the specs thread
`qclass` through generically (`Spec/Question.lean`, `Spec/NetworkSemantics.lean`
even defaults `qclass : RRClass := RRClass.in` in its query model) and no
theorem constrains which classes the resolver may recurse — which is why the
proofs did not catch this.

## Impact

- **Wrong rcode semantics:** SERVFAIL is retryable; stub resolvers will re-ask
  (often across all configured servers). REFUSED is the correct terminal
  signal for "I do not serve this class" (RFC 1035 §4.1.1 rcode 5 = policy
  refusal; RFC 8906 §3.1 expects servers to answer out-of-scope queries with
  REFUSED rather than fail).
- **Information disclosure:** any client of the recursive can fingerprint the
  upstream authoritative software (`version.bind`/`version.server` CH TXT is a
  well-known reconnaissance probe; RFC 4892 notes operators deliberately
  restrict it). unbound never forwards CH; veri-dns turns the recursive into a
  CH relay to whatever server its IN root hints point at.
- **Cross-class scope slip:** one resolution mixes CH (main leg) and IN (glue
  leg) queries against an IN-only delegation tree, violating class
  independence (RFC 6895 §3.2 / RFC 2929 §3.2: each class is an independent
  name space).

## References

- RFC 1035 §4.1.1 — rcode 2 (Server failure) vs rcode 5 (Refused: "The name
  server refuses to perform the specified operation for policy reasons").
- RFC 6895 §3.2 (and RFC 2929 §3.2) — DNS CLASSes are independent name spaces;
  IN root hints carry no CHAOS delegation.
- RFC 1034 §5.3.3 — SBELT/root-hint priming is per the configured (IN) root.
- RFC 4892 — `version.bind`/`id.server` CH TXT server-instance identification;
  version disclosure is commonly restricted for security reasons.
- RFC 8906 §3.1 — servers should respond (REFUSED) to queries they will not
  serve rather than fail or time out.
- unbound `daemon/worker.c` — `answer_chaos()` serves `version.bind`/
  `version.server`/`id.server`/`hostname.bind` locally; any other non-IN class
  query is answered REFUSED (`LDNS_RCODE_REFUSED`) before iteration. Matches
  the rig observation.
