# 018 — Cache-miss (network) path forwards the upstream authoritative server's AUTHORITY (NS) + ADDITIONAL (glue) sections to the client unscrubbed

- **Component:** `VeriDNS/Impl/Server.lean` — `replyForResolution` (network/`.ok` branch, ~:466-481) and `finalizeForClient` (:29-31)
- **Class:** impl-bug (response hygiene / non-minimal responses; unscrubbed pass-through surface)
- **Severity:** low — benign against the honest rig, but any record a queried server places in AUTHORITY/ADDITIONAL reaches the client verbatim
- **Status:** CONFIRMED on the running rig (differential vs unbound)
- **REGRESSION RE-TEST vs upstream 26b5849 (2026-07-15): PARTIALLY FIXED — the leak persists.**
  `deliveredResponse` (`VeriDNS/Impl/Server.lean:743-752`) now applies `scrubAuthorityB`, but that
  filter only keeps `isAncestorB rr.name qname` — i.e. it strips **out-of-bailiwick** authority
  (the #012/#013 poison-SOA case, now genuinely fixed) while the ordinary in-bailiwick delegation
  NS still passes, and **`resp.additional` is untouched entirely** (see #047; `arcount` is not even
  recomputed). Re-run on the honest 203.0.113.0/24 rig, cache-miss, both resolvers cold:

  ```
  # veri-dns — still non-minimal
  ;; ANSWER: 1, AUTHORITY: 1, ADDITIONAL: 1
  host.example.test.  3600  IN  A   203.0.113.101
  EXAmPLe.TEst.       3600  IN  NS  ns.EXAmPLe.TEst.     <-- authority leaked
  ns.EXAmPLe.TEst.    3600  IN  A   203.0.113.12         <-- glue leaked
  # unbound — minimal-responses
  ;; ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1   (ADDITIONAL is the EDNS OPT only)
  ```

  The severity remains low on its own, but #047 shows the same unscrubbed additional path carries
  **arbitrary attacker-chosen out-of-bailiwick records**. Note also the `EXAmPLe.TEst.` casing: the
  resolver's 0x20 upstream randomisation is leaking into the client-delivered authority/additional
  (see the new candidate on 0x20 case leakage).

## Summary

On a **cache miss**, veri-dns scrubs only the ANSWER section (`Resolver.scrubAnswerB`)
and copies the last-hop authoritative response's **AUTHORITY** and **ADDITIONAL**
sections into the client reply verbatim. Unbound (reference) returns minimal
responses (`iter_scrub` / `minimal-responses`): AUTHORITY/ADDITIONAL are stripped
to nothing (only the EDNS OPT pseudo-record remains). After the entry is warm,
veri-dns serves from cache and the extras disappear.

## Root cause (code)

`replyForResolution` (`VeriDNS/Impl/Server.lean:466-481`), `.ok resp` branch:

```lean
let scrubbed := Resolver.scrubAnswerB (RR := ResourceRecord) qname resp.answer
let response := finalizeForClient
  { resp with
    answer := scrubbed                     -- ANSWER scrubbed
    header := { resp.header with
      id := query.header.id
      ancount := BitVec.ofNat 16 scrubbed.size } }
```

The record spread `{ resp with answer := scrubbed, ... }` keeps `resp.authority`
and `resp.additional` untouched, so `nscount`/`arcount` and the section bytes are
whatever the upstream server emitted. `finalizeForClient` only rewrites header
flags (`qr/ra/aa/z`), not the sections. There is no analogue of `scrubAnswerB`
for the authority/additional sections on the client-facing path.

## Reproduction (rig)

Cache cleared by restarting only the resolver-under-test unit (no rebuild):

```
systemctl stop veridns-verid; systemd-run --unit=veridns-verid --collect \
    ip netns exec verid /opt/dnsenv/veri-dns
```

### veri-dns, COLD miss — `www.example.test A`

```
ip netns exec attacker dig @10.53.0.2 -p 5300 www.example.test A

;; flags: qr ra; QUERY: 1, ANSWER: 2, AUTHORITY: 1, ADDITIONAL: 1

;; ANSWER SECTION:
www.example.test.   3588 IN CNAME example.test.
example.test.       3600 IN A     10.53.0.100

;; AUTHORITY SECTION:
example.test.       3600 IN NS    ns.example.test.      <-- leaked
;; ADDITIONAL SECTION:
ns.example.test.    3600 IN A     10.53.0.12            <-- leaked glue
```

### unbound, same query

```
ip netns exec attacker dig @10.53.0.3 -p 5301 www.example.test A

;; flags: qr rd ra; QUERY: 1, ANSWER: 2, AUTHORITY: 0, ADDITIONAL: 1

;; ANSWER SECTION:
www.example.test.   1793 IN CNAME example.test.
example.test.       1752 IN A     10.53.0.100
;; ADDITIONAL: OPT pseudosection only — no NS, no glue
```

### veri-dns, WARM re-query — extras drop, rd flips on

```
;; flags: qr rd ra; QUERY: 1, ANSWER: 2, AUTHORITY: 0, ADDITIONAL: 0
```

The AUTHORITY/ADDITIONAL leak is **upstream-dependent**: it surfaces whatever the
last-hop server put in those sections. `example.test A` (the CNAME target /
zone apex) is answered by the leaf `nsd` with its NS set + glue, so the CNAME
chase to it drags the NS+glue into the client reply. A direct
`host.example.test A` cold query, where the leaf emits no authority section,
shows `AUTHORITY: 0, ADDITIONAL: 0` on veri-dns — confirming veri-dns is a raw
pass-through, not an injector.

## Why it matters

- **Non-minimal responses.** Unbound deliberately strips authority/additional on
  the answer path (`minimal-responses: yes`, default; `iter_scrub`). veri-dns has
  no equivalent, so it emits larger replies and a wider content surface.
- **Unscrubbed pass-through.** The ANSWER section gets bailiwick scrubbing
  (`scrubAnswerB`); the AUTHORITY/ADDITIONAL sections handed to the client get
  none. Whatever NS records / glue A records a queried authoritative server
  emits in those sections reach the client as-is. Against the honest rig this is
  benign, but it is exactly the surface minimal-responses exists to shrink.

## Reference

- Unbound `minimal-responses` (default `yes`) and `iter_scrub` remove
  non-essential authority/additional records from answers.
- RFC 1035 §7.3 / §7.4 treat additional-section data as advisory; a recursive
  resolver is not required to relay the authority/additional an upstream server
  sends, and hardened resolvers strip them.

## Classification

impl-bug — reproduced behavioral defect vs the reference resolver: the
network/miss path forwards the upstream authority + additional sections to the
client unscrubbed, whereas unbound returns minimal responses.
