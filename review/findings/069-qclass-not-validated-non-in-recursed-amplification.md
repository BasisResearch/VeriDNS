# 069 — QCLASS never validated: non-IN class queries are recursed to the real roots (SERVFAIL + ~1:80 egress amplification) vs unbound REFUSED

## Summary

`queryProblem` (`VeriDNS/Impl/Server.lean:118`) is the sole front-door
sanity gate on a client query. It rejects exactly three defects:

- `qdcount != 1` → FORMERR
- `opcode != query` → NOTIMPL
- `rd == 0` → REFUSED

It performs **no QCLASS check**. A query whose class is anything other than
IN (1) therefore falls straight through into `resolveWithIO` and is recursed
down the real delegation chain, with QNAME-minimisation and 0x20 case
randomisation, carrying the bogus class on the wire. The five hardcoded roots
do not serve non-IN classes, so they REFUSE; veri-dns then retries across all
five roots and across every minimisation reveal, exploding one client query
into ~80 upstream packets before giving up with SERVFAIL.

unbound REFUSEs the identical query instantly and emits zero upstream packets.

This is a reflection/amplification + resource-exhaustion vector reachable by
any client inside the default ACL, and in production the egress targets the
**real root servers** (198.41.0.4 / 199.9.14.201 / 192.33.14.30 / 199.7.91.13
/ 192.203.230.10 — hardcoded in `Main.lean`).

It is entirely outside the verified envelope: the verdict-soundness / adequacy
capstones assume `qclass = 1` as a hypothesis
(`ResolveWithIOSound.lean:3483` `have hcls1 : qu.qclass = 1 := alphaClass_in_one hqc`;
`IoResumeSound.lean:3759`), so no theorem constrains resolver behaviour for
non-IN classes.

## Rig

- veri-dns (SUT) @203.0.113.2:5300 in netns `verid`; unbound (oracle)
  @203.0.113.3:5301 in netns `unbound`. Both restarted for cold caches before
  each differential.
- nsd roots also bind the 5 real root IPs, which veri-dns hardcodes.
- attacker/client netns `attacker` (192.168.53.99), inside the default ACL.

## Reproduction

Cold caches (`systemctl restart veridns-verid veridns-ref; sleep 2`), then a
single HS-class query with egress capture on the verid netns:

```
=== VERID HS ===
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 57617
=== UNBOUND HS ===
;; ->>HEADER<<- opcode: QUERY, status: REFUSED, id: 57475
=== EGRESS BY DEST (verid netns, upstream :53) ===
     16 > 192.203.230.10.53:
     16 > 192.33.14.30.53:
     16 > 198.41.0.4.53:
     16 > 199.7.91.13.53:
     16 > 199.9.14.201.53:
```

One client HS query → **80 upstream queries** distributed across the five real
root IPs (16 each). unbound → REFUSED, **zero** upstream packets.

### Bogus class preserved on the wire

```
203.0.113.2.45157 > 198.41.0.4.53:    13967 [1au] A HS? Test. (33)
203.0.113.2.52806 > 199.9.14.201.53:  34680 [1au] A HS? TESt. (33)
203.0.113.2.43243 > 192.33.14.30.53:  62839 [1au] A HS? TeSt. (33)
203.0.113.2.49336 > 199.7.91.13.53:   41925 [1au] A HS? tESt. (33)
203.0.113.2.40148 > 192.203.230.10.53:65153 [1au] A HS? TEsT. (33)
```

The HS class and 0x20-randomised QNAME are both forwarded to the real roots.

### Class-generalisation batch (cold caches each iteration)

```
class=CH      VERID SERVFAIL  |  UNBOUND REFUSED
class=NONE    VERID SERVFAIL  |  UNBOUND REFUSED
class=CLASS5  VERID SERVFAIL  |  UNBOUND REFUSED
class=ANY     VERID NOERROR   |  UNBOUND NOERROR   (agree)
class=IN      VERID NOERROR   |  UNBOUND NOERROR   (agree)
```

Every non-IN, non-ANY class diverges: veri-dns recurses+amplifies+SERVFAILs
where unbound REFUSEs at the door.

Commands:

```
ip netns exec verid tcpdump -ni any 'port 53 and not port 5300' -w /tmp/hs.pcap &
ip netns exec attacker dig +tries=1 +time=5 -c HS @203.0.113.2 -p 5300 example.test A
ip netns exec attacker dig +tries=1 +time=5 -c HS @203.0.113.3 -p 5301 example.test A
```

## Why this is a bug (unbound disagrees)

unbound refuses unknown/non-IN classes immediately (a query for a class the
resolver does not implement is answered REFUSED, no recursion). RFC 1035 §3.2.4
defines CLASS with IN as the operative Internet class; a recursive resolver has
nothing to resolve for CH/HS/NONE/arbitrary classes against Internet
delegation and must not blast the roots to discover that. veri-dns instead
treats class as opaque, recurses, and amplifies 1:80 against the real root
servers.

## Fix

Add a class arm to `queryProblem` (`Server.lean:118`) mirroring unbound:

```lean
else if q.question[0]!.qclass != 1 && q.question[0]!.qclass != 255 then
  some Rcode.refused
```

(IN=1 resolves; ANY=255 already agrees with unbound as NOERROR; everything
else REFUSED before any egress.)

## Cleanup

No tracked source files were modified (Server.lean read-only). Both resolvers
left restarted with cold caches; pcap written to VM `/tmp` only.
