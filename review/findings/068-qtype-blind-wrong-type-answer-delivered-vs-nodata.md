# 068 — qtype-blind answer acceptance: a wrong-type same-owner RR is delivered where unbound returns NODATA (coverage-gap)

## Classification
coverage-gap — build stays GREEN, resolver is observably wrong on the wire, and no
theorem constrains the qtype of a delivered answer record. Delivery-hygiene bug
(not cached on this arm → not a poisoning vector), but a clear differential vs unbound.

## Summary
A NOERROR response whose ANSWER section contains a record of the **wrong type**
(no CNAME, owner = qname) is accepted verbatim and delivered to the stub as the
final answer. A conforming resolver treats the same-owner non-qtype record as
*not an answer* and returns NODATA (empty answer). Confirmed on the rig against a
cold cache; unbound disagrees on the identical path against identical data.

Client asks `weird.example.test IN A`; the authoritative stand-in returns
`NOERROR, aa=1, ancount=1` carrying a single `TXT weird.example.test` in the
answer (and no CNAME). veri-dns delivers `ANSWER: 1 … TXT "hello-wrong"`; unbound
delivers `ANSWER: 0` (NODATA).

## Root cause
- `stepAnalyzeResponse` (`VeriDNS/Impl/Resolver.lean:435`): after the
  delegation-shaped and `answersQueryB` arms are ruled out, the catch-all
  `else if !resp.answer.isEmpty || rcode == nameError then .answer (finalizeAnswer s resp) s`
  fires whenever the answer section is non-empty — with **no check that any RR
  matches the queried qtype** and no CNAME at qname. The whole answer section is
  accepted as the final answer.
- The client-delivery scrub does not filter it out. `scrubAnswerB`
  (`VeriDNS/Impl/AnswerScrub.lean:35`) authenticates a record by CNAME-reachability
  from the seed set `#[qname]` (`reachableNamesB … qname`, line 29-30). A record
  whose **owner == qname** is in that seed set unconditionally, so a same-owner
  wrong-type RR survives the scrub and is delivered. `scrubAnswerB` performs no
  qtype test.

Unbound's `iter_scrub.c` / `scrub_normalize` follows the CNAME chain and drops a
same-owner record that is neither the queried qtype nor a chain CNAME; the A
lookup is then NODATA.

## Reproduction (rig, cold cache)
Stand-in leaf `review/env/wrongtype_auth.py` bound to `203.0.113.12:53` (nsd-leaf
stopped). For `weird.example.test IN A` it returns `qr=1 aa=1 NOERROR ancount=1`
with one `TXT weird.example.test 300 "hello-wrong"`; it serves example.test
NS/A/SOA normally so both resolvers reach it via referral.

```
# stop nsd-leaf, launch responder in the auth ns
systemctl stop veridns-auth-leaf.service
systemd-run --unit=veridns-wrongtype --collect ip netns exec auth python3 /opt/dnsenv/wrongtype_auth.py

# cold caches (rule 3)
systemctl restart veridns-verid veridns-ref; sleep 2

ip netns exec attacker dig @203.0.113.2 -p 5300 weird.example.test A   # veri-dns
ip netns exec attacker dig @203.0.113.3 -p 5301 weird.example.test A   # unbound
```

### veri-dns (system under test) — delivers the wrong-type RR
```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 35095
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0
;; ANSWER SECTION:
weird.example.test.	300	IN	TXT	"hello-wrong"
```

### unbound (reference oracle) — NODATA
```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 36999
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
```

Direct query to the stand-in confirms the injected shape:
```
ip netns exec auth dig @203.0.113.12 weird.example.test A
;; status: NOERROR ; ANSWER SECTION:
weird.example.test.	300	IN	TXT	"hello-wrong"
```

## RFC / oracle citation
RFC 2308 §2.2 (NODATA): a name that exists but holds no RR of the queried type is
an empty NOERROR answer, indicated by an empty answer section with an SOA in the
authority section. A TXT RR is not an answer to an A query. Unbound's answer
normalization removes same-owner records outside the qtype/CNAME chain, yielding
NODATA — the RFC-correct result. veri-dns hands the stub the TXT verbatim.

## Distinct from prior findings
- #020 is QTYPE=ANY bypassing the scrub for **foreign-owner** records; here the
  scrub runs normally and still keeps a **same-owner wrong-type** record because
  `scrubAnswerB` seeds reachability with `#[qname]` and never checks qtype.
- #038 is NS-in-answer subtree caching; #045 is empty-NOERROR from a lame server.
  This is the qtype-blindness of the inbound answer-acceptance fallback + scrub.

## Notes
This arm (`:435`) does not cache (unlike the `answersQueryB` arm at `:427`), so it
is a per-query delivery-hygiene divergence, not a cache-poisoning vector.
