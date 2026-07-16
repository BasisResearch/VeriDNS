# 060 — DNAME (type 39) records stripped from delivered answers by the CNAME-only delivery scrub

**Severity:** low (resolution still succeeds via the synthesized CNAME; the DNAME
record itself is silently dropped, so a DNAME-aware / validating downstream loses it)

**Component:** `VeriDNS/Impl/AnswerScrub.lean` (delivery scrub), reached from
`VeriDNS/Impl/Server.lean:743` (`deliveredResponse` → `scrubAnswerB`)

**Status:** CONFIRMED against the rig. unbound delivers the DNAME; veri-dns omits it.

---

## What happens

The delivery scrub builds a "reachable names" set starting from `#[qname]` and
grows it by following **only** CNAME (type-5) records:

```
-- VeriDNS/Impl/AnswerScrub.lean:15-20
def reachTarget? (reach) (bytes) : Option ByteArray :=
  match RRParse.parseRaw bytes with
  | some rr =>
    if RRParse.rrType rr == (5 : BitVec 16) && nameMemB (RRParse.rrName rr) reach
    then some (RRParse.rrRdata rr) else none
  | none => none
```

`scrubAnswerB` (`:35`) then keeps an answer RR only if its owner name matches one of
those reachable names. For a DNAME response (RFC 6672 §3.2) the authoritative server
returns:

- the **DNAME** RR, owner = the DNAME node (a *strict ancestor* of qname),
- a synthesized **CNAME**, owner = qname,
- the terminal A for the CNAME target.

The synthesized CNAME (owner = qname) is kept and its target is chased, so the CNAME
and the A are delivered. But the DNAME RR's owner is a strict ancestor of qname and
never enters `reachableNames` (nothing follows a DNAME edge), so `scrubAnswerB`
filters it out. The delivered answer is missing the DNAME.

RFC 6672 §3.2 ("The DNAME Substitution") and §5.3.2 require the DNAME RR to be
present in the answer alongside the synthesized CNAME. unbound's `iter_scrub.c`
(`scrub_normalize`) keeps the DNAME rrset and the synthesized CNAME and delivers both.

---

## Reproduction

### Setup

Added a DNAME to the leaf zone (`review/env/nsd/zones/example.test.zone`, SOA serial
bumped 1→2), served natively by nsd which synthesizes the CNAME:

```
old     IN DNAME new.example.test.
x.new   IN A     203.0.113.150
```

Brought the rig up with `review/env/up.sh` (fresh caches on both resolvers).

### The authoritative answer (nsd leaf, direct)

```
$ ip netns exec attacker dig @203.0.113.12 -p 53 x.old.example.test A +norecurse
;; ANSWER SECTION:
old.example.test.	3600	IN	DNAME	new.example.test.
x.old.example.test.	3600	IN	CNAME	x.new.example.test.
x.new.example.test.	3600	IN	A	203.0.113.150
```

### veri-dns (system under test) — DNAME MISSING

```
$ ip netns exec attacker dig @203.0.113.2 -p 5300 x.old.example.test A
;; flags: qr rd ra; QUERY: 1, ANSWER: 2, AUTHORITY: 1, ADDITIONAL: 1
;; ANSWER SECTION:
x.old.example.test.	3600	IN	CNAME	x.new.ExampLe.TesT.
x.new.ExampLe.TesT.	3600	IN	A	203.0.113.150
```

ANSWER: 2 — the CNAME and A are present, the `old.example.test. DNAME
new.example.test.` record is gone. (The `ExampLe.TesT` casing on the delivered owner
names is a separate cosmetic artifact of `setOwnerB` rewriting owners to the matched
reachable-name bytes; not the subject of this finding.)

### unbound (reference oracle) — DNAME PRESENT

```
$ ip netns exec attacker dig @203.0.113.3 -p 5301 x.old.example.test A
;; flags: qr rd ra; QUERY: 1, ANSWER: 3, AUTHORITY: 0, ADDITIONAL: 1
;; ANSWER SECTION:
old.example.test.	3600	IN	DNAME	new.example.test.
x.old.example.test.	3600	IN	CNAME	x.new.example.test.
x.new.example.test.	3600	IN	A	203.0.113.150
```

ANSWER: 3 — DNAME + CNAME + A, all three delivered.

Both resolvers were cold-restarted immediately before the differential (rule 3),
both resolve the name to 203.0.113.150; the sole observable difference is the
presence of the DNAME RR in the answer section.

---

## Impact

Resolution succeeds — the redirect is carried by the synthesized CNAME — so the
severity is low. But a DNAME-aware or DNSSEC-validating downstream that expects to
see the DNAME RR (to re-synthesize/verify the CNAME, or to cache the DNAME for
sibling names) loses it. The delivered answer is not what the authoritative server
sent and differs observably from unbound.

## Root cause / fix sketch

`reachTarget?` recognizes only type-5 (CNAME). To keep the DNAME RR, the reachable
set must also admit an RR whose owner is a proper ancestor of a reachable name and
whose type is DNAME (39) — i.e. the DNAME node that generated a kept synthesized
CNAME should itself be treated as reachable. unbound's normalize does exactly this.

---

## Cleanup

Rig zone edit and staged copy reverted; `review/env/up.sh` re-run to restore the
baseline `example.test.` zone (SOA serial back to 1, DNAME/x.new records removed).
