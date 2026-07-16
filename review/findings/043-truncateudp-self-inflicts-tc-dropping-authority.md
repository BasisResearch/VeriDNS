# 043 — truncateUdp self-inflicts TC=1 when it drops the AUTHORITY section, making a complete, sub-512 answer unresolvable

## Classification
impl-bug (confirmed on the running rig, differential vs unbound)

## Summary
`truncateUdp` (VeriDNS/Impl/Server.lean:204-219) stages UDP size reduction in
three steps but couples "drop AUTHORITY" with "set TC=1":

```
m1: drop ADDITIONAL, arcount:=0                     (tc stays 0)
m2: drop AUTHORITY,  nscount:=0, tc:=1              <-- sets TC even though ANSWER is untouched
m3: drop ANSWER,     ancount:=0, tc:=1
```

There is no "drop authority, TC=0" stage. Because `Message.encode` performs **no
name compression**, veri-dns re-encodes an upstream reply larger than the
compressed datagram it received. Any positive answer whose
`question + ANSWER` fits in 512 but whose `question + ANSWER + AUTHORITY`
(uncompressed) exceeds 512 is emitted with a **complete ANSWER** yet **TC=1**.
A stub that honors TC discards the UDP answer and retries over TCP (RFC 1035
§4.2.1, RFC 7766), which veri-dns refuses — it has no TCP listener (finding
006) — so the name becomes unresolvable via veri-dns while unbound resolves it.

This is distinct from echoing the client's TC (finding 032) and from upstream-TC
handling (015/031): here veri-dns sets TC=1 on its **own** complete, sub-512
reply.

## Root cause (code)
- `VeriDNS/Impl/Server.lean:213` — `m2` sets `tc := 1, nscount := 0, authority := #[]`
  but leaves `answer` untouched; the answer alone fits in 512.
- `replyForResolution` (:466-481) forwards the upstream AUTHORITY (NS RRset)
  verbatim via `finalizeForClient` (:29-31, authority passed through).
- `Message.encode` uses no compression, so the forwarded RRset re-encodes far
  larger than the compressed wire form the resolver received.
- `serveOne` (:501-502) calls `truncateUdp` on the encoded reply and sends the
  TC=1 datagram over UDP only.

## Reproduction (on the rig)

Upstream: a responder on the leaf IP 10.53.0.12:53 (`fatauth_responder.py`,
staged in `penn-testing/_vmdns/`) that answers `example.test A` with a positive,
complete answer (aa=1, ANSWER=1, A 10.53.0.100) PLUS a 13-record apex NS
AUTHORITY section, all name-compressed so the datagram is **475 bytes on the
wire** (no TC). This models a classic non-minimal authoritative server (BIND
default) that includes the apex NS RRset in a positive answer's authority. (The
rig's nsd defaults to minimal-responses and omits it — hence the custom
responder.)

Leaf responder (compressed, fits < 512, no TC):
```
$ dig +noedns @10.53.0.12 -p 53 example.test A
;; flags: qr aa; QUERY: 1, ANSWER: 1, AUTHORITY: 13, ADDITIONAL: 0
;; MSG SIZE  rcvd: 475
```

veri-dns @10.53.0.2:5300 (cache-miss), UDP reply captured with +ignore:
```
$ dig +ignore @10.53.0.2 -p 5300 example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 5383
;; flags: qr tc ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0
;; ANSWER SECTION:
example.test.  3600  IN  A  10.53.0.100
;; MSG SIZE  rcvd: 58
```
TC=1 on a **58-byte** reply that carries the **complete, correct answer** and an
empty authority — there is nothing to truncate. A normal (TCP-fallback) stub:
```
$ dig @10.53.0.2 -p 5300 example.test A
;; Truncated, retrying in TCP mode.
;; Connection to 10.53.0.2#5300(10.53.0.2) for example.test failed: connection refused.
;; no servers could be reached
```
veri-dns has no TCP listener (`ss -tlnp` in netns verid: none on 5300; only a
UDP socket), so resolution fails.

unbound @10.53.0.3:5301 against the same upstream:
```
$ dig @10.53.0.3 -p 5301 example.test A
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
;; ANSWER SECTION:
example.test.  2524  IN  A  10.53.0.100
;; MSG SIZE  rcvd: 57
```
No TC, complete answer, resolves. (unbound uses minimal-responses and, even
when including optional sections, only sets TC if the *answer itself* cannot fit
— it never sets TC merely because it dropped an optional AUTHORITY/ADDITIONAL
section; cf. unbound `util/data/msgencode.c:784` omit-authority-for-positive and
`:809` "no need to set TC bit, this is the additional".)

## Impact
For any positive answer where the (uncompressed) authority section pushes the
reply over 512 while the answer alone fits, veri-dns returns TC=1. TC-honoring
stubs then fail (no TCP). The trigger is upstream-controlled (an authoritative
server that ships a fat NS RRset in a positive answer's authority), so a name
that resolves everywhere else is unresolvable through veri-dns.

## Fix direction
Only set TC when the reduction actually drops the **ANSWER** section (the m3
stage). Dropping ADDITIONAL or AUTHORITY to fit a datagram whose ANSWER already
fits must leave TC=0 (matching msgencode.c:784/:809). Better still: compress
names in `Message.encode`, and/or scrub the optional authority on the positive
answer path before size-checking.

## RFC / reference
- RFC 1035 §4.1.1 (TC = "this message was truncated ... longer than permitted");
  §4.2.1 (retry over TCP on TC). Setting TC when nothing of the answer was
  omitted misrepresents the message as truncated.
- RFC 7766 §5 (TCP fallback expected when TC set).
- unbound `util/data/msgencode.c:784, :809`.

---

## REGRESSION 2026-07-15 (post-remediation 26b5849) — SELF-INFLICTED TC STILL PRESENT; availability impact mitigated by new TCP listener

The offending coupling is unchanged: `truncateUdp` stage `m2`
(`VeriDNS/Impl/Server.lean:326`) still does `tc := 1, nscount := 0, authority := #[]`,
and `Message.encode` (`VeriDNS/Impl/Message.lean:88`) still performs **no name
compression**, so a positive answer whose ANSWER fits <512 but whose
(uncompressed) ANSWER+AUTHORITY exceeds the client cap is emitted with a complete
ANSWER yet TC=1.

Re-reproduced with a leaf responder (`penn-testing/_vmdns/trunc_responder.py`,
`fatns*` names: 1 A answer + 15 NS authority, 458 bytes compressed on the wire,
TC=0) standing in for `nsd-leaf` on 203.0.113.12:53. Non-EDNS client:

```
verid  (+noedns +ignore):  flags: qr tc rd ra;  ANSWER: 1  (203.0.113.100 present)  72 bytes  <- FALSE TC=1
unbound(+noedns +ignore):  flags: qr rd ra;     ANSWER: 1  (203.0.113.100)          53 bytes  <- no TC
```

Unbound still disagrees (drops the optional authority silently, TC=0), so this
remains a genuine VeriDNS bug: a complete sub-cap answer is falsely flagged
truncated.

**What changed:** upstream shipped a client-facing TCP listener
(`Impl/TcpFraming.lean`, `serveTcpDatagram`). So a TC-honoring stub now retries
over TCP and *succeeds*:

```
verid  (+noedns):  ;; Truncated, retrying in TCP mode.  -> NOERROR ANSWER:1 203.0.113.100 (TCP)
```

Impact is therefore downgraded from "unresolvable / bricked" to a **spurious TC=1
that forces an unnecessary TCP round-trip** (and still trips any UDP-only stub
that does not retry). The self-inflicted-TC defect and its unpinned spec gap
(see 044) are unfixed.
