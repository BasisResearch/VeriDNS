# 028 — Cache hit serves the FIRST writer's owner-name case; answer owner is never re-canonicalized to the client's QNAME

- **Severity:** low (cosmetic / protocol hygiene; RDATA and resolution identical to reference).
- **Class:** coverage-gap (refines finding 003; the verified spec models names up-to-case-fold, so no theorem obligates the answer owner's case, and the cache-serving path is entirely outside the verified case surface).
- **On/off-path:** client-delivery boundary, cache-hit path (`Server.replyForResolution` serving a `DnsCache` RRset stored with first-seen owner bytes).

## Refinement over finding 003

Finding 003 established the *miss-path* case divergence (veri-dns delivers the upstream owner bytes; unbound echoes the client's QNAME case). The KB entry "case not preserved" only ever tested same-case or single-query flows. This finding adds the *cache-hit* dimension: when the cache is primed by a query of one case and then hit by a query of a DIFFERENT case, veri-dns serves the **first cacher's** case in the ANSWER owner name. The served case is therefore a function of *cache history*, not of the current question — a property no single-query test can see.

Note the miss-path detail also observed here: on a cold miss veri-dns echoed the client's case (`EXAMPLE.TEST.` came back uppercase, TTL 3600) because it forwards the client's case verbatim upstream and nsd's answer owner is a compression pointer to the echoed QNAME. So veri-dns is not "always lowercase" — it is "whatever case the *first* resolver-side fetch happened to carry", frozen for the RRset's TTL.

## Reproduction (rig, 2026-07-08)

Fresh veri-dns cache via `review/env/restart-verid.sh` (its sanity query primes `host.example.test` lowercase). All queries from netns `attacker`.

Direction 1 — prime lowercase, hit UPPERCASE (veri-dns @10.53.0.2:5300):

```
$ dig @10.53.0.2 -p 5300 host.example.test A +noall +answer
host.example.test.	3586	IN	A	10.53.0.101
$ dig @10.53.0.2 -p 5300 HOST.EXAMPLE.TEST A +noall +answer
host.example.test.	3586	IN	A	10.53.0.101      <-- cached lowercase served, not query case
$ dig @10.53.0.2 -p 5300 HoSt.ExAmPlE.tEsT A +noall +answer
host.example.test.	3542	IN	A	10.53.0.101      <-- TTL decrement proves cache hit
```

Direction 2 — prime UPPERCASE (cold name since restart), hit lowercase/mixed:

```
$ dig @10.53.0.2 -p 5300 EXAMPLE.TEST A +noall +answer
EXAMPLE.TEST.		3600	IN	A	10.53.0.100      <-- cold miss: client case echoed
$ dig @10.53.0.2 -p 5300 example.test A +noall +answer
EXAMPLE.TEST.		3511	IN	A	10.53.0.100      <-- cache hit serves FIRST writer's case
$ dig @10.53.0.2 -p 5300 eXaMpLe.TeSt A +noall +answer
EXAMPLE.TEST.		3509	IN	A	10.53.0.100
```

Reference unbound (@10.53.0.3:5301), same prime+hit sequence — answer owner always rewritten to the client's QNAME case, including on a proven cache hit:

```
$ dig @10.53.0.3 -p 5301 host.example.test A +noall +answer
host.example.test.	3600	IN	A	10.53.0.101
$ dig @10.53.0.3 -p 5301 HOST.EXAMPLE.TEST A +noall +answer
HOST.EXAMPLE.TEST.	3600	IN	A	10.53.0.101
$ dig @10.53.0.3 -p 5301 ExAmPlE.TeSt A +noall +answer
ExAmPlE.TeSt.		3600	IN	A	10.53.0.100
$ sleep 3; dig @10.53.0.3 -p 5301 HOST.EXAMPLE.TEST A +noall +answer
HOST.EXAMPLE.TEST.	3586	IN	A	10.53.0.101      <-- hit (TTL 3586) yet query case echoed
```

## Mechanism (source)

- `VeriDNS/Impl/Cache.lean`: all store/lookup/merge paths compare owners with `nameEqCI` / `foldNameCase` (lines 52, 64, 79, 88, 94, 111, ...). An RRset is stored once with the owner bytes as first seen; a later different-case question matches case-insensitively and the stored bytes are returned untouched.
- `VeriDNS/Impl/Server.lean:29` `finalizeForClient` only rewrites header flags (`qr`, `ra`, `aa`, `z`); no code on the `replyForResolution` (line 460) reply path rewrites answer owner names to the current question's QNAME.

## RFC / reference basis

RFC 1035 §4.1.2 + §2.3.3: the response carries the question and, per §2.3.3, "When you receive a domain name or label, you should preserve its case" — the conventional reading (implemented by unbound, BIND) is that owner names in the answer that are equal to the QNAME are echoed in the *client's* case (on the wire this typically falls out of compressing the answer owner as a pointer to the question). SHOULD-level, so no MUST is violated; RFC 4343 reaffirms case-insensitive equivalence. Practical edge: a stub doing DNS-0x20-style byte-comparison of the answer owner against its encoded QNAME would reject veri-dns cache-hit responses.

## Why the proofs are silent

The spec deliberately models names up-to-fold (finding 001), so "answer owner case equals question case" is not expressible as a spec obligation; the cache-hit serve path preserves everything the theorems talk about (RDATA, TTL semantics, case-insensitive name identity). Scope gap, not a broken proof.

## Verdict

CONFIRMED, both directions, with TTL-decrement proof of cache hits, against a reference unbound that rewrites to the query case. Cosmetic / coverage-gap.

## Addendum (independent re-verification, 2026-07-08, second pass)

Reproduced from scratch on the live rig; two extensions beyond the original write-up:

1. **CNAME-chain owners also serve first-writer case.** Prime `WwW.eXaMpLe.TeSt` (cold miss, mixed-case echoed and cached), then query lowercase `www.example.test` — veri-dns cache hit (TTL 3582) serves:

   ```
   $ dig @10.53.0.2 -p 5300 www.example.test A +noall +answer
   WwW.eXaMpLe.TeSt.	3582	IN	CNAME	eXaMpLe.TeSt.
   example.test.		3556	IN	A	10.53.0.100
   ```

   unbound, same sequence: both records rewritten to the client's lowercase (`www.example.test. CNAME example.test.` / `example.test. A`, TTLs 3581/3555 proving hits).

2. **A single response can mix owner cases from different cache-write histories.** In the reply above, the CNAME RR carries mixed case (first writer of the `www` RRset) while the chained A RR carries lowercase (first writer of the `example.test` A RRset) — neither matching the client's query case. Similarly `AlIaS.eXaMpLe.TeSt` (after lowercase alias warm and mixed-case host warm) returned `alias.example.test. CNAME host.example.test.` + `HoSt.ExAmPlE.TeSt. A 10.53.0.101` (TTL 3581, hit). unbound's reply to the identical query: `AlIaS.eXaMpLe.TeSt. CNAME host.eXaMpLe.TeSt.` + `host.eXaMpLe.TeSt. A` — it propagates the client's case through the chain by suffix.

3. Reverse direction re-proven with `host`: mixed-case cold prime `HoSt.ExAmPlE.TeSt` (TTL 3600), then both `host.example.test` and `HOST.EXAMPLE.TEST` hits (TTL 3582/3581) each returned `HoSt.ExAmPlE.TeSt.` — the served case is a pure function of cache history, invariant under the client's case in either direction.
