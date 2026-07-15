# Finding 010: RD echo depends on cache state — dropped on every cache-miss reply (impl-bug, unmutated binary)

**Classification:** impl-bug (observable on the pristine implementation; no mutation involved)
**Relation to 007:** Finding 007 showed the proofs are blind to RD under a
deliberate mutation of `finalizeForClient`. This finding shows the *unmutated*
implementation already violates RFC 1035 §4.1.1 on the network/cache-miss path,
via a different mechanism: header inheritance from the upstream response.

## Mechanism (source, commit 5ea5109, clean working tree)

- `VeriDNS/Impl/Server.lean:29-31` — `finalizeForClient` sets
  `qr := 1, ra := 1, aa := 0, z := 0` and never touches `rd`.
- `VeriDNS/Impl/Server.lean:460-475` — `replyForResolution` builds the client
  reply from the **upstream** response `resp`, restoring only `id` (and
  `ancount`) from the client query. `rd` is inherited from the upstream server's
  reply header.
- `VeriDNS/Impl/Server.lean:49-54` — `mkAddressQuery` sends upstream iterative
  queries with `rd := 0`, so authoritative answers come back with rd=0, and
  that 0 is forwarded to the client.
- Cache-hit replies, by contrast, are synthesized from the client query via
  `buildResponse` (`Server.lean:13-24`, `{ query.header with ... }`), which
  preserves the client's rd=1.

Net effect: the RD bit of the reply is a function of cache state, not of the
client query.

## RFC violation

RFC 1035 §4.1.1 (rfc/rfc-1035.txt:1464-1465):

> RD  Recursion Desired - this bit may be set in a query and
>     is copied into the response.

## Reproduction (live rig, dig defaults to RD=1)

NXDOMAIN path, fresh random name (cache miss) then same name (cache hit):

```
$ N=fresh476822913.example.test
$ ip netns exec attacker dig +time=3 +tries=1 @10.53.0.2 -p 5300 $N A | grep flags:
;; flags: qr ra; QUERY: 1, ANSWER: 0, AUTHORITY: 1, ADDITIONAL: 0      # rd DROPPED
$ ip netns exec attacker dig +time=3 +tries=1 @10.53.0.2 -p 5300 $N A | grep flags:
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 1, ADDITIONAL: 0   # rd kept (cached)
```

NOERROR path after restarting veri-dns (cache flush), name example.test:

```
$ ip netns exec attacker dig ... @10.53.0.2 -p 5300 example.test A | grep flags:
;; flags: qr ra; ...        # first query after restart: rd DROPPED
$ ip netns exec attacker dig ... @10.53.0.2 -p 5300 example.test A | grep flags:
;; flags: qr rd ra; ...     # second query: rd kept
```

Reference unbound @10.53.0.3:5301, same fresh-then-repeat protocol:

```
;; flags: qr rd ra; ...     # first (cache miss)
;; flags: qr rd ra; ...     # second (cache hit)
```

unbound echoes rd on both; veri-dns diverges on every cache miss. The
divergence is wire-visible in the flags word of every first-contact answer.

## Impact

Every answer that required network resolution mislabels itself as a
non-recursion-desired response. Strict stubs and middleboxes that validate the
RD echo (a common response-matching sanity check) will flag or discard exactly
the freshly resolved answers, while cached answers pass — an inconsistency that
is also a cache-state oracle for a remote observer.

## Fix sketch

In `replyForResolution` (Server.lean:470-475), restore `rd := query.header.rd`
alongside `id`; or have `finalizeForClient` take the client query and copy its
rd. Then add the missing proof obligation from Finding 007
(`reply.header.rd = query.header.rd`, citing rfc/rfc-1035.txt:1464-1465).
