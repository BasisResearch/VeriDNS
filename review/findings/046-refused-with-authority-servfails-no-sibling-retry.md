# 046 — REFUSED (non-NOERROR/non-NXDOMAIN) response carrying a non-empty authority section is not thrown away; veri-dns SERVFAILs the whole query instead of trying the next nameserver

---

## ✅ REGRESSION STATUS 2026-07-15 (vs upstream 26b5849): **FIXED — verified on the rig, and theorem-pinned**

Re-ran the original repro on the current rig (binary md5 `aecb30f9033559304160e082a145ee39`).
The terminal `.error "4b: no NS records in authority"` is **gone from the tree entirely**;
`VeriDNS/Impl/Resolver.lean` now ends that branch with
`else .goto .sendQueries { s with lastResponse := none }`, i.e. the throw-away-and-retry
path unbound takes.

Rig: `flaky.test.` delegated to two glued nameservers, lame ns1 (203.0.113.20) listed
FIRST, good ns2 (203.0.113.21) second. ns1 answers `rcode, aa=0, ANSWER=0, AUTHORITY=[SOA]`.
Both resolvers restarted cold before each run.

**The old repro no longer reproduces** — veri-dns now fails over to ns2 across the whole
trigger set:

| ns1 rcode | veri-dns (was) | veri-dns (now) | unbound |
|-----------|----------------|----------------|---------|
| 5 REFUSED | SERVFAIL | **NOERROR, A 203.0.113.111** | NOERROR, A 203.0.113.111 |
| 1 FORMERR | SERVFAIL | **NOERROR, A 203.0.113.111** | NOERROR, A 203.0.113.111 |
| 4 NOTIMP  | SERVFAIL | **NOERROR, A 203.0.113.111** | NOERROR, A 203.0.113.111 |

Per-server hit counts on the REFUSED run confirm the failover is real (lame ns1 tried,
then good ns2 reached): `ns1 hits=2, ns2 hits=3`.

### Fix quality: load-bearing

`stepAnalyzeResponse_lame` (`VeriDNS/Proof/Refinement.lean:5499`) states that under exactly
this response shape `stepAnalyzeResponse s = .goto .sendQueries { s with lastResponse := none }`.
Reverting the impl to `.error` makes that theorem's **statement false** ⇒ build red. This is a
genuine pin, not a shape-only cases lemma.

**Note the carve-out:** the theorem's hypothesis `hnodata : (rcode == noError && answer.isEmpty) = false`
explicitly *excludes* the bare-empty-NOERROR shape. The pin therefore stops precisely where
findings **041 / 045** begin — those remain STILL-PRESENT (045 is a wrong answer). The
remediation fixed the non-empty-authority shape and the theorem documents that it went no further.


**Classification:** impl-bug (observable client-visible divergence from unbound; DoS/downgrade)

**Component:** `VeriDNS/Impl/Resolver.lean` `stepAnalyzeResponse`

## Summary

When a delegation nameserver answers a leaf query with rcode **REFUSED** (or any
rcode other than NOERROR/NXDOMAIN) **and a non-empty authority section** (e.g. a
lone SOA), veri-dns classifies the response as `classifiableB = true` (authority
is non-empty), so the retry guard at `Resolver.lean:388`
(`rcode == serverFailure || !classifiableB`) is **skipped**. The response then
enters the referral branch at `:391` (`!answersQueryB && rcode != nameError &&
answer.isEmpty && !authority.isEmpty`), but every sub-branch there is gated on
`rcode == noError` (`:398`, `:419`), so control falls through to
`else .error "4b: no NS records in authority"` at `:421`. That resolver `.error`
is turned into `.finished (.error)` by the IO shim (`Server.lean:281-285`) and
`replyForResolution` emits **SERVFAIL** to the client. `dropIfBizarre`
(`Server.lean:267`) does **not** shed the server for these rcodes (it only sheds
`serverFailure` / `!classifiableB`), so the sibling nameserver is never tried.

unbound (iterator `iter_resptype.c`: any rcode != NOERROR after NXDOMAIN handling
→ `RESPONSE_TYPE_THROWAWAY`; `iterator.c`: THROWAWAY → recycle to
QUERYTARGETS_STATE, try next target) discards the REFUSED and moves to the next
nameserver, resolving the name normally.

Consequence: a single delegation NS returning REFUSED-with-any-content — or an
off-path spoofer who wins the id+question race with a REFUSED+junk-authority
datagram — makes veri-dns SERVFAIL the entire query even though a sibling NS
would answer. unbound resolves.

## Rig setup

Fake TLD `test.` (nsd @10.53.0.11) delegates `flaky.test.` to two glued
nameservers. A small Python responder (`/opt/dnsenv/flaky_ns.py`) binds both:

- **ns1 = 10.53.0.20 (BAD):** replies `rcode=REFUSED`, answer empty, **one SOA in
  the authority section** (`flaky.test. SOA …`), aa=0, id+question echoed.
- **ns2 = 10.53.0.21 (GOOD):** replies `rcode=NOERROR`, aa=1,
  `www.flaky.test. A 10.53.0.111`.

tld referral lists `ns1.flaky.test.`(=.20) **first**, `ns2.flaky.test.`(=.21)
second, both with glue. veri-dns's SLIST (`SList.lean` `bestWithAddress`) picks
the first-listed server deterministically, i.e. **ns1 (BAD) first**.

Direct probes confirm each server:
```
dig @10.53.0.20 www.flaky.test A  -> status: REFUSED ; AUTHORITY: 1 (SOA)
dig @10.53.0.21 www.flaky.test A  -> status: NOERROR ; ANSWER: 1  A 10.53.0.111
```

## Reproduction — two NS, ns1 bad ns2 good

### veri-dns (@10.53.0.2:5300) — SERVFAILs, never tries ns2
```
$ dig @10.53.0.2 -p 5300 www.flaky.test A
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 40933

# tcpdump on the auth side (host 10.53.0.20 or 10.53.0.21):
15:39:46 IP 10.53.0.2.58772 > 10.53.0.20.53: 35447 A? www.flaky.test.
15:39:46 IP 10.53.0.20.53 > 10.53.0.2.58772: 35447 Refused- 0/1/0
#  -> exactly ONE exchange. ns2 (10.53.0.21) is NEVER contacted.
```

### unbound (@10.53.0.3:5301) — resolves the name
```
$ dig @10.53.0.3 -p 5301 www.flaky.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR
www.flaky.test.  3600  IN  A  10.53.0.111
```

## Reproduction — BOTH NS bad (isolates the throwaway-vs-hard-error behavior)

`flk3.test.` delegated to two nameservers that BOTH return REFUSED+SOA
(10.53.0.24, 10.53.0.25).

### veri-dns — one query, then SERVFAIL
```
$ dig @10.53.0.2 -p 5300 www.flk3.test A   -> status: SERVFAIL
# tcpdump: exactly ONE request/REFUSED exchange (to .24); sibling .25 untouched.
15:42:45 IP 10.53.0.2.48019 > 10.53.0.24.53: A? www.flk3.test.
15:42:45 IP 10.53.0.24.53 > 10.53.0.2.48019: Refused- 0/1/0
```

### unbound — throws away each REFUSED and tries the next target exhaustively
```
$ dig @10.53.0.3 -p 5301 www.flk3.test A   -> status: SERVFAIL
# tcpdump: DOZENS of exchanges — unbound queries BOTH .24 and .25 repeatedly
# (throwaway → next target) and even re-resolves ns1/ns2 addresses before
# finally SERVFAILing. (full capture in the session log)
```

The contrast is exact: on a REFUSED+authority response veri-dns takes the
`.error "4b"` hard-error path after a single query, whereas unbound treats the
rcode as THROWAWAY and cycles through every sibling target.

## Root cause (code)

`VeriDNS/Impl/Resolver.lean`:
- `:353 classifiableB` returns `true` when `!resp.authority.isEmpty` — so a
  REFUSED-with-authority response is "classifiable".
- `:388` retry guard is `rcode == serverFailure || !classifiableB` → not taken.
- `:391` referral branch entered (answer empty, authority non-empty), but
- `:398` and `:419` both require `rcode == Rcode.noError`; REFUSED fails both →
- `:421 else .error "4b: no NS records in authority"`.
- `VeriDNS/Impl/Server.lean:267` `dropIfBizarre` sheds only
  `serverFailure`/`!classifiableB`, so the server is not dropped and no sibling
  is tried; `:281-285` turns the resolver `.error` into `.finished (.error)` →
  SERVFAIL.

## Fix direction

Treat any rcode ∉ {NOERROR, NXDOMAIN} as a "throwaway" that drops the current
server and retries the next SLIST entry (as `serverFailure` already is at `:388`
and in `dropIfBizarre`), rather than falling into the `.error "4b"` hard-error
path. Equivalently, generalize the `:388` retry guard / `dropIfBizarre` predicate
from `rcode == serverFailure` to `rcode ∉ {noError, nameError}`.

## Reference

- unbound `iterator/iter_resptype.c` — any rcode != NOERROR (after NXDOMAIN
  handled) → `RESPONSE_TYPE_THROWAWAY`.
- unbound `iterator/iterator.c` — THROWAWAY recycles to QUERYTARGETS_STATE and
  tries the next target.
- RFC 1034 §5.3.3 / RFC 2308: a resolver keeps trying other servers in the SLIST
  on a failed/unusable response rather than failing the whole query.
