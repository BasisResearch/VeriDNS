# 041 — Entirely-empty NOERROR accepted as final NODATA on first receipt (no retry); unbound throws it away and re-queries

---

## ⚠️ REGRESSION STATUS 2026-07-15 (vs upstream 26b5849): **STILL PRESENT — never addressed**

`docs/remediation-plan.md` **does not mention finding 041 anywhere**. Neither
fixed, nor pinned, nor scoped out. `classifiableB` (`Resolver.lean:360`) and the
catch-all accept at `Resolver.lean:435-436` are unchanged. See **045** for the
2-NS escalation of this same defect into a wrong answer.

### Re-run of the ORIGINAL repro on the current rig

To force unbound onto a lame server (rather than letting it pick a healthy
sibling), **both** nameservers of the `flaky.test.` delegation were bound to the
bare-empty-NOERROR responder. Both resolvers restarted cold; upstream exchanges
for the test name counted from the responder logs:

```
=== veri-dns (both NS bare) ===
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 209
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
VERIDNS upstream exchanges for the test name: ns1=1 ns2=0 TOTAL=1

=== unbound (both NS bare) ===
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 21953
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
UNBOUND upstream exchanges for the test name: ns1=1 ns2=1 TOTAL=2
```

Both return NODATA (as the original finding noted for the single-server case —
hence coverage-gap, not a wrong answer *here*), but the retry-count divergence is
reproduced exactly: veri-dns accepts on **1** datagram; unbound throws the bare
message away and re-queries the **sibling** (`EMPTY_NODATA_RETRY_COUNT` = 2).
That discarded-and-retried datagram is precisely what rescues unbound in 045.

---

- **Component:** `VeriDNS/Impl/Resolver.lean` `stepAnalyzeResponse` (:434-435), `classifiableB` (:353-358)
- **Class:** coverage-gap (robustness / anti-spoofing hardening absent; the answer itself is RFC-2308-legal)
- **Status:** CONFIRMED on the rig — differential vs unbound reproduced.

## Summary

When an upstream response is a *completely empty* NOERROR (ancount = nscount =
arcount = 0, tc = 0) that passes `acceptResponse` (id + question match),
veri-dns returns it to the client as a final NODATA after a **single** upstream
datagram. It falls through every referral/answer branch of
`stepAnalyzeResponse` to the catch-all at :434:

```
else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty then
  .answer (finalizeAnswer s resp) s
```

`classifiableB` (:357, `resp.header.rcode == Rcode.noError`) makes a bare-empty
NOERROR classifiable, so it never routes back to `.sendQueries`. There is no
retry, and no second server or second datagram is consulted.

unbound treats a fully-empty message as suspicious: it increments
`empty_nodata_found` and returns `RESPONSE_TYPE_THROWAWAY` for the first
`EMPTY_NODATA_RETRY_COUNT` (=2) occurrences, re-querying before it will accept
an empty NODATA (`iterator/iter_resptype.c` an=0&&ns=0&&ar=0 handling;
`iterator/iterator.h` `EMPTY_NODATA_RETRY_COUNT`; `iterator/iterator.c`
re-query on throwaway).

Impact: (1) robustness — a single dropped-payload / truncated-to-header packet
ends the query as NODATA with no second try; (2) spoofing downgrade — an
off-path attacker who wins the id+port race with a 12-byte-style empty NOERROR
forces veri-dns to answer NODATA, where unbound's mandatory retry would keep
looking for the legitimate answer.

## Reproduction (on the rig)

Responder used: `penn-testing/_vmdns/empty_nodata_responder.py` — binds
`10.53.0.12:53` (ns.example.test) in the `auth` ns, replacing the leaf nsd. It
answers the delegation bookkeeping (example.test NS/SOA, ns.example.test A)
normally so the referral chain completes, and returns a bare empty NOERROR
(qr=1, aa=1, ra=1, rcode=0, qdcount=1 echo, an=ns=ar=0, tc=0) for the test name.

Setup:
```
# stop leaf nsd, run the empty responder in the auth ns, cold-cache verid
systemctl stop veridns-auth-leaf
systemd-run --unit=empty-responder --collect \
  ip netns exec auth python3 /opt/dnsenv/empty_nodata_responder.py
systemctl restart veridns-verid
```

### veri-dns — ONE upstream exchange, returns NODATA

```
$ ip netns exec attacker dig +time=3 +tries=1 @10.53.0.2 -p 5300 foo.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 60938
;; flags: qr ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 0
;; QUESTION SECTION:
;foo.example.test.		IN	A

# responder log — exactly ONE query for the test name:
[empty] query txid=0x3e26 foo.example.test. type=1
responder queries before: 0   /   after: 1
```

### unbound — retries (2 exchanges) before accepting

```
$ ip netns exec attacker dig +time=5 +tries=1 @10.53.0.3 -p 5301 foo.example.test A
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 13773
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1

# responder log — TWO queries for the test name during a single client resolve:
[empty] query txid=0xf68f foo.example.test. type=1
[empty] query txid=0x12d3 foo.example.test. type=1
delta = 2   (EMPTY_NODATA_RETRY: threw away the first, re-queried)
```

Same responder, same name, cold cache on both sides: veri-dns issues **1**
upstream exchange and immediately answers NODATA; unbound issues **2** (it
re-queries the empty NOERROR rather than trusting a single datagram). The
single-exchange acceptance pinpoints `Resolver.lean:434`.

## Notes on classification

The NODATA answer veri-dns returns is itself RFC-2308-legal (NODATA = NOERROR
with an empty answer), and because there is no SOA it is not negatively cached
(`storeNegativeIfCacheable` no-ops), so nothing poisonous is persisted. The gap
is the absence of unbound's defensive **retry** for a wholly-empty message —
defense-in-depth against dropped payloads and single-datagram spoofing — which
is a hardening heuristic, not an RFC MUST. Hence coverage-gap rather than a
correctness impl-bug.

## Citations

- unbound `iterator/iter_resptype.c`: an=0 && ns=0 && ar=0 →
  `(*empty_nodata_found)++`, `RESPONSE_TYPE_THROWAWAY`.
- unbound `iterator/iterator.h`: `EMPTY_NODATA_RETRY_COUNT` = 2.
- unbound `iterator/iterator.c`: re-query same/next server on throwaway.
- RFC 2308 §2.2: NODATA is NOERROR with empty answer (so accepting one is legal;
  the robustness/retry behaviour is unbound hardening, not an RFC requirement).
