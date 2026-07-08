# 005 — Answer-section records accepted from any queried server without a per-server bailiwick / delegation-point check (root can answer for any zone)

> **FINAL VERDICT: REFUTED (controlled differential, hand-run).** With the fake
> ROOT nsd made authoritative for `example.test` (rogue zone: `evil A 6.6.6.6`,
> `host A 6.6.6.6`; the real leaf returns NXDOMAIN for `evil`), and BOTH resolvers
> restarted with fresh caches:
> ```
> evil.example.test A   veri-dns -> NOERROR 6.6.6.6   unbound -> NOERROR 6.6.6.6
> host.example.test A   veri-dns -> 6.6.6.6           unbound -> 6.6.6.6
> ```
> **unbound accepts the rogue root's direct authoritative answer IDENTICALLY to
> veri-dns.** It is not a veri-dns-specific bug — accepting an in-bailiwick
> authoritative answer from a server you were configured/referred to reach is the
> standard non-DNSSEC trust model. A later loop agent reported unbound returning
> NXDOMAIN here, but that run was on the *shared* rig while concurrent agents were
> poisoning it (the loop's own evidence flags this) — an unreliable observation.
> The controlled, isolated re-run above is authoritative. **NOT a finding.**
>
> ---
> *(superseded) earlier reconciliation:*
> **RECONCILIATION (downgraded — DISPUTED, likely NOT a veri-dns-specific bug).**
> This contradicts Round 1's *differential* result, which reproduced the same
> scenario and found **unbound accepts the ancestor's in-bailiwick answer
> identically** (both returned the injected record). An ancestor server *is*
> in-bailiwick for its descendants — that is the standard iterative-resolution
> trust model, not a defect — and veri-dns's `isAncestorB` gate *does* reject a
> genuinely out-of-bailiwick answer (e.g. `.test` answering for `example.com`).
> So the "root can answer for any zone" framing describes normal, unbound-shared
> behavior: querying only servers reached via the delegation chain, each trusted
> within its own subtree. **Not accepted as a distinct finding.** (The related,
> genuinely divergent issue — *extra subdomain* RRs piggybacked on an answer,
> which unbound strips and veri-dns keeps — is finding 004, which stands.)
> A definitive re-run of the ancestor-answer differential vs unbound is queued
> for the resumed loop; absent a veri-dns-vs-unbound divergence there, 005 is refuted.

- **Severity:** ~~high~~ → disputed/likely-informational (see reconciliation above). A server queried anywhere
  in the delegation chain — including the **root**, which is *always* the first
  server contacted — can return an authoritative ANSWER for a name in a zone it
  was never delegated, and veri-dns accepts it, returns it, and caches it.
- **Class:** bad-spec. The Lean model's answer-acceptance rule
  (`answersQueryB`, `Resolver.lean:75`, gating the terminal `.answer` at
  `Resolver.lean:423`) only checks that *some answer RR carries the qtype for
  qname*. It never checks that the **responding server** is authoritative for
  (at or below its delegation point for) the answered name. The only bailiwick
  guard, `respInBailiwick` (`Server.lean:131`), is wired *solely* to
  referral-shaped responses via `unfollowableDelegationB`
  (`Server.lean:146`, reached only under `delegationShapedB`). Answer-shaped
  responses bypass it entirely. Build is green; behaviour is observably wrong.
- **On/off-path:** on-path / rogue-upstream (a malicious or compromised server
  legitimately in the delegation path — no spoofing, no txid guessing needed).
- **Relation to 004:** distinct. 004 concerns *extra* subdomain RRs piggybacked
  on an answer whose source is otherwise the correct leaf, and the cache
  keep-rule. This finding concerns the **primary answer for the queried name
  itself** being accepted from a server high in the tree that is not
  authoritative for it — veri-dns terminates resolution at the root and never
  descends the delegation chain at all. Both share the root cause: no per-server
  delegation-point scrub on answers.

## Claim

When veri-dns is iteratively resolving `NAME` and the current server returns a
response with `answersQueryB` true (an answer RR of the requested type for
`NAME`), the resolver terminates at `Resolver.lean:423`:

```
else if answersQueryB (RR := RR) resp then
  let cache' := cacheUnlessTruncated ... (bailiwickRaws sname resp.answer) (credAnswer (aa==1)) ...
  .answer (finalizeAnswer s resp) { s with ... cache := cache' }
```

`answersQueryB` (`Resolver.lean:75`) inspects only the answer RRs vs the qname —
it does not know or check *which* server replied or whether that server is inside
the zone it is authoritative for. `acceptResponse` (`Server.lean:43`) gates the
datagram on `header.id` + question match only. `unfollowableDelegationB`
(`Server.lean:420` / `:146`) — the only path that consults `respInBailiwick` —
fires only when `delegationShapedB resp` is true (NS in authority, **no** answer).
An answer-shaped response therefore never reaches any bailiwick check.

Consequence: the very first server veri-dns contacts (a root server, from the
hardcoded hints) can answer authoritatively for *any* name in *any* zone and
veri-dns takes it. Unbound rejects this — a root/parent server is not
authoritative below a delegation, so its direct answer for a child-zone name is
out of bailiwick and discarded; unbound follows the real delegation instead.

## Reproduction (on the rig)

The fake **root** nsd (`auth` ns, listening on the hardcoded root IPs incl.
`198.41.0.4` and `10.53.0.10`) was made **rogue**: additionally authoritative for
`example.test.` with forged data, modeling a compromised server high in the
delegation chain.

`review/env/nsd/zones/rogue-example.test.zone` (staged into the VM at
`/opt/dnsenv/nsd/zones/`):

```
$ORIGIN example.test.
@     IN SOA ns.example.test. hostmaster.example.test. ( 99 3600 900 604800 3600 )
@     IN NS  ns.example.test.
ns    IN A   10.53.0.12
host  IN A   6.6.6.6      ; real leaf serves 10.53.0.101 — this POISONS it
evil  IN A   6.6.6.6      ; does NOT exist on the real leaf (leaf -> NXDOMAIN)
```

added to `nsd-root.conf` as a second `zone:` and `systemctl restart
veridns-auth-root`. Both resolver caches flushed (restart) before the run.
The honest tld (`.11`) and leaf (`.12`) servers were left untouched — the real
`example.test.` zone still serves `host A 10.53.0.101` and NXDOMAIN for `evil`.

Direct sanity check — rogue root answers authoritatively, honest leaf does not:

```
$ dig @10.53.0.10 evil.example.test A +norecurse
;; ->>HEADER<<- status: NOERROR ;; flags: qr aa; ANSWER: 1        <- rogue root, authoritative
$ dig @10.53.0.12 evil.example.test A +norecurse
;; ->>HEADER<<- status: NXDOMAIN ;; flags: qr aa; ANSWER: 0       <- real leaf: no such name
```

### veri-dns — POISONED

```
$ ip netns exec attacker dig +noall +comments +answer @10.53.0.2 -p 5300 evil.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 29326
;; flags: qr ra; QUERY: 1, ANSWER: 1, AUTHORITY: 1, ADDITIONAL: 1
;; ANSWER SECTION:
evil.example.test.  3600  IN  A  6.6.6.6         <- forged; name does not exist

$ ip netns exec attacker dig +noall +comments +answer @10.53.0.2 -p 5300 host.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 20735
;; flags: qr ra; QUERY: 1, ANSWER: 1, AUTHORITY: 1, ADDITIONAL: 1
;; ANSWER SECTION:
host.example.test.  3600  IN  A  6.6.6.6         <- POISONED; real value is 10.53.0.101
```

### unbound — CLEAN

```
$ ip netns exec attacker dig +noall +comments +answer @10.53.0.3 -p 5301 evil.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NXDOMAIN, id: 8075         <- rejects rogue root, follows real delegation
;; (no ANSWER)

$ ip netns exec attacker dig +noall +comments +answer @10.53.0.3 -p 5301 host.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 24018
;; ANSWER SECTION:
host.example.test.  3576  IN  A  10.53.0.101     <- correct value from the real leaf
```

### Smoking gun — veri-dns upstream capture (`tcpdump -tt -n -i v-verid`)

```
10.53.0.2.40998 > 198.41.0.4.53: 39771 A? evil.example.test. (35)
198.41.0.4.53 > 10.53.0.2.40998: 39771*- 1/1/1 A 6.6.6.6 (84)      <- root answers, aa(*), veri-dns accepts
```

veri-dns sent the query to the **root IP** `198.41.0.4`, received a direct
authoritative answer, and **never queried the tld (`10.53.0.11`) or leaf
(`10.53.0.12`)** — it terminated resolution at the root. The `6.6.6.6` value only
exists on the rogue root, so veri-dns demonstrably accepted the root's
out-of-bailiwick answer.

## Why the verification didn't catch it

The soundness theorems certify the implementation against a model whose
answer-acceptance predicate (`answersQueryB`) has *no notion of the answering
server's zone*. The model never carries a per-server `zonename`/delegation-point
and never scrubs an answer by "is the server authoritative here?", so a
verified-green resolver still accepts the root answering for a leaf zone. The
`respInBailiwick` check exists but is deliberately scoped to referrals only
(`unfollowableDelegationB` is guarded by `delegationShapedB`). The spec is too
weak, not the proof.

## Fix sketch

Before terminating at `Resolver.lean:423`, require that the answering server is
in bailiwick for the answered name: the current delegation point / zone cut used
to select the server (available as the referral cut, cf. `referralCutRaw` and the
slist the query was sent to) must be an ancestor-or-equal of the answer owner,
and the answer owner must equal the (CNAME-chased) qname. Equivalently, run the
same delegation-point bailiwick scrub unbound applies in
`scrub_normalize`/`scrub_sanitize` on the answer section before accepting. Reflect
the tightened rule in the model's answer case and re-prove soundness.

## References

- unbound `iterator/iter_scrub.c` `scrub_normalize` / `scrub_sanitize`: answer
  RRsets outside the delegation-point bailiwick (and with owner != qname) are
  removed; a parent/root server's direct answer for a child zone is discarded.
- RFC 5452 §6: a resolver must accept only expected data; answers from a server
  not authoritative for the name are a forgery vector.
- RFC 2181 §5.4.1 (ranking) and §6 (occluded names): authoritative-answer data
  must come from the server authoritative for the name's zone, not a parent that
  has delegated it away.

## Artifacts

- Rogue zone: `review/env/nsd/zones/rogue-example.test.zone`
  (staged in VM at `/opt/dnsenv/nsd/zones/rogue-example.test.zone`); rogue
  `zone:` stanza appended to `/opt/dnsenv/nsd/nsd-root.conf`.
- Impl paths: `VeriDNS/Impl/Resolver.lean:75,423`;
  `VeriDNS/Impl/Server.lean:43,131,144-146,420`.
