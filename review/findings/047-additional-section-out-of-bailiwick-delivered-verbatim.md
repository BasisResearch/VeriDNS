# 047 — Attacker-injected out-of-bailiwick ADDITIONAL A records are delivered to the client verbatim; unbound strips the entire injected additional section

**Classification:** impl-bug (observable client-visible divergence from unbound; forged-record delivery to stub resolvers / additional-trusting apps)

**Component:** `VeriDNS/Impl/Server.lean` `replyForResolution` (:460-481) + `finalizeForClient` (:29-31)

## Summary

On the cache-miss resolution path, `replyForResolution` scrubs **only** the
answer section for bailiwick:

```lean
let scrubbed := Resolver.scrubAnswerB (RR := ResourceRecord) qname resp.answer
let response := finalizeForClient
  { resp with
    answer := scrubbed
    header := { resp.header with
      id := query.header.id
      ancount := BitVec.ofNat 16 scrubbed.size } }
```

`resp.authority` and `resp.additional` are carried through **unchanged**, and
`finalizeForClient` (`:29-31`) only rewrites the `qr/aa/ra/z` header flags. No
per-record bailiwick scrub is ever applied to the delivered ADDITIONAL section.
Consequently whatever an upstream server (a compromised/on-path authoritative,
or any server in the resolution path) places in the additional section is
handed to the client verbatim — including records for names entirely outside the
queried zone.

This deepens KB finding **026** (`026-refused-with-authority-servfail-no-failover.md`
characterized related leakage of upstream AUTHORITY/ADDITIONAL glue). The live
test here shows the leaked additional is not limited to legitimate delegation
glue: it carries **arbitrary attacker-controlled records, including
out-of-bailiwick ones**.

unbound performs a per-record bailiwick scrub of the additional section against
the delegation-point zone (`iter_scrub.c: scrub_message` → `pkt_sub` /
`msg_rrset_remove_rr` against `zonename`), so all injected additional RRs are
removed before the answer is returned to the client.

## Rig setup

- Stopped the real leaf: `systemctl stop veridns-auth-leaf`.
- Bound a Python responder (`/opt/dnsenv/inject_responder.py`) in the `auth`
  netns on `10.53.0.12:53` that answers every A query with:
  - ANSWER: `<qname> A 10.53.0.101` (aa=1, legit-looking), plus a forged
  - ADDITIONAL:
    - `bank.example.test.  A 6.6.6.6`  (in-bailiwick, unrelated to qname)
    - `evil.attacker.test. A 6.6.6.6`  (**OUT-OF-BAILIWICK** — not under `example.test.`)

## Reproduction

```
# stop real leaf, start injector
systemctl stop veridns-auth-leaf
systemd-run --unit=inject-responder --collect \
  ip netns exec auth python3 /opt/dnsenv/inject_responder.py 10.53.0.12

# veri-dns (under test) — fresh name so it resolves upstream (cache miss)
ip netns exec attacker dig @10.53.0.2 -p 5300 poisonA.example.test A +additional
# unbound (reference) — same-shaped fresh name
ip netns exec attacker dig @10.53.0.3 -p 5301 poisonB.example.test A +additional
```

### veri-dns output (forged additional delivered verbatim)

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 56319
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 2

;; ANSWER SECTION:
poisonA.example.test.	300	IN	A	10.53.0.101

;; ADDITIONAL SECTION:
bank.example.test.	300	IN	A	6.6.6.6
evil.attacker.test.	300	IN	A	6.6.6.6      <-- out-of-bailiwick, verbatim
```

### unbound output (entire injected additional stripped)

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 22270
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
;; OPT PSEUDOSECTION:                    <-- ADDITIONAL: 1 is only the EDNS OPT RR
;; ANSWER SECTION:
poisonB.example.test.	300	IN	A	10.53.0.101
```

## Exploitability is bounded to client-delivery

The injected additional does **not** poison veri-dns's answerable cache. After
stopping the responder and restoring the real leaf (where `bank.example.test` is
NXDOMAIN), veri-dns returns NXDOMAIN for `bank.example.test`, not `6.6.6.6`:

```
systemctl stop inject-responder
systemd-run --unit=veridns-auth-leaf --collect \
  ip netns exec auth nsd -c /opt/dnsenv/nsd/nsd-leaf.conf -d
ip netns exec attacker dig @10.53.0.2 -p 5300 bank.example.test A
# ->>HEADER<<- ... status: NXDOMAIN
```

The additional is cached only at non-answerable/glue credibility (consistent
with KB 026), so it is never promoted to an answer. The risk is therefore to
**client delivery only**: a compromised/on-path authoritative server, or any
server in the resolution path, can hand a stub resolver or an additional-trusting
application forged A records for **any** name (e.g. a bank's real domain) in the
additional section, and veri-dns forwards them unscrubbed.

## RFC / reference citation

- RFC 5452 §6 ("Forgery Resilience"): a resolver must accept only in-bailiwick
  data; out-of-zone records in a response must not be used or propagated.
- RFC 2181 §5.4.1 (ranking of data) / the long-standing bailiwick rule: records
  not within the zone of the answering server are untrusted and must be
  discarded, not relayed.
- unbound implementation: `iter_scrub.c` (`scrub_message`/`pkt_sub` against the
  delegation `zonename`) removes out-of-bailiwick RRs from the additional
  section before returning the answer.

## Suggested fix

Apply the same per-record bailiwick scrub used on `resp.answer`
(`Resolver.scrubAnswerB` / `bailiwickRaws` against the delegation zone) to
`resp.authority` and `resp.additional` before `finalizeForClient`, rather than
carrying those sections through verbatim.
