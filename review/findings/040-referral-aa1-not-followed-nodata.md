# 040 — Referral with AA=1 is not followed: veri-dns returns spurious NOERROR/NODATA

---

## ⚠️ REGRESSION STATUS 2026-07-15 (vs upstream 26b5849): **STILL PRESENT — never addressed**

`docs/remediation-plan.md` **does not mention finding 040 anywhere**. Neither
fixed, nor pinned, nor scoped out.

The cited gate is **verbatim unchanged** — `VeriDNS/Impl/Resolver.lean:397-400`:
```lean
if hasRRTypeIn (RR := RR) resp.authority 2
    && resp.header.aa == 0                     -- <-- still here
    && resp.header.rcode == Rcode.noError
    && !hasRRTypeIn (RR := RR) resp.authority 6 then
```
and the NODATA fallthrough it drops into still sits at `:421-422`
(`else if resp.header.rcode == Rcode.noError && resp.answer.isEmpty then
.answer (finalizeAnswer s resp) s`).

### Re-run of the ORIGINAL repro on the current rig

`tld_referral.py` impersonates the fake TLD on `203.0.113.11:53` (nsd-tld stopped)
and returns an identical delegation for every query — NOERROR, ANCOUNT=0,
AUTHORITY `example.test. NS ns.example.test.`, ADDITIONAL glue
`ns.example.test. A 203.0.113.12`. The **only** variable is the AA bit. Both
resolvers restarted cold before each run.

**Control — AA=0 (both follow the referral):**
```
-- veri-dns -- status: NOERROR ; ANSWER: 1 ; host.example.test. 3600 IN A 203.0.113.101
-- unbound  -- status: NOERROR ; ANSWER: 1 ; host.example.test. 3600 IN A 203.0.113.101
```

**Bug — same referral, AA=1:**
```
-- veri-dns --
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 63934
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 1, ADDITIONAL: 1
example.test.		3600	IN	NS	ns.example.test.
   --> spurious NODATA; never descends to the leaf.

-- unbound --
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 391
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
host.example.test.	3600	IN	A	203.0.113.101
   --> follows the AA=1 referral, returns the real record.
```

The AA bit remains the sole differentiator, exactly as originally reported.

---

- **Component:** `VeriDNS/Impl/Resolver.lean` `stepAnalyzeResponse`, referral branch
- **Location:** `VeriDNS/Impl/Resolver.lean:396-421`; gate at `:397` `&& resp.header.aa == 0`; NODATA fallthrough at `:419-420`
- **Reference:** unbound `iterator/iter_resptype.c` — a below-origzone NS set is classified `RESPONSE_TYPE_REFERRAL` *regardless of the AA bit* (the AA-forces-ANSWER branch is deliberately commented out).
- **Classification:** impl-bug (observable interop failure + attacker-exploitable downgrade)
- **Status:** CONFIRMED on the rig by differential test vs unbound.

## Summary

veri-dns only treats an authority-section NS delegation as a *followable
referral* when the response header has `AA == 0`. A delegation-shaped response
that carries `AA == 1` (NS RRset in AUTHORITY, empty ANSWER, NOERROR, no SOA)
passes the anti-poison gates and reaches `stepAnalyzeResponse`, but the referral
sub-branch at `Resolver.lean:396-399` is skipped because of the `aa == 0`
conjunct. Control falls through to `:419` (`rcode==noError && answer.isEmpty`)
and returns `finalizeAnswer s resp` — a NOERROR message with an empty ANSWER
section and the NS records in AUTHORITY. The client receives a **NODATA-shaped
answer for a name that actually exists below the delegation**, and resolution
never descends to the child servers.

unbound classifies the same below-origzone NS set as a referral and follows it,
returning the real record.

## Reproduction (on the rig)

A custom UDP responder impersonated the fake TLD server `10.53.0.11:53` (the
`veridns-auth-tld` nsd was stopped for the duration) and answered every query
for `host.example.test A` with an identical delegation:

```
rcode NOERROR, ANCOUNT=0
AUTHORITY:  example.test. 3600 IN NS ns.example.test.
ADDITIONAL: ns.example.test. 3600 IN A 10.53.0.12   (glue)
```

The **only** variable changed between runs is the header AA bit. Both resolvers
were cold-cache restarted before each query.
(Responder: `penn-testing/_vmdns/tld_referral.py`, env `AA=0` / `AA=1`.)

### Control — referral with AA=0 (both follow it)

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 host.example.test A   # veri-dns
;; ->>HEADER<<- status: NOERROR ... ANSWER: 1
host.example.test. 3600 IN A 10.53.0.101

$ ip netns exec attacker dig @10.53.0.3 -p 5301 host.example.test A   # unbound
;; ->>HEADER<<- status: NOERROR ... ANSWER: 1
host.example.test. 3600 IN A 10.53.0.101
```

### Bug — same referral with AA=1

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 host.example.test A   # veri-dns
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 11065
;; flags: qr ra; QUERY: 1, ANSWER: 0, AUTHORITY: 1, ADDITIONAL: 1
;; AUTHORITY SECTION:
example.test.    3600 IN NS ns.example.test.
;; ADDITIONAL SECTION:
ns.example.test. 3600 IN A  10.53.0.12
   --> NODATA. host.example.test A is NOT resolved; never descends to the leaf.

$ ip netns exec attacker dig @10.53.0.3 -p 5301 host.example.test A   # unbound
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 47239
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1
;; ANSWER SECTION:
host.example.test. 3600 IN A 10.53.0.101
   --> follows the AA=1 referral to the leaf, returns the real A record.
```

### Isolation — flip AA back to 0 on the same responder

```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 host.example.test A   # veri-dns
;; ->>HEADER<<- status: NOERROR ... ANSWER: 1
host.example.test. 3600 IN A 10.53.0.101
```

veri-dns resolves again the moment AA=0, confirming the `aa == 0` conjunct at
`Resolver.lean:397` is the sole cause.

## Impact

1. **Interop failure:** against any parent/TLD authoritative server that
   (mis)sets AA on its referrals, the entire delegated subtree becomes
   unresolvable via veri-dns while unbound resolves it normally.
2. **Targeted downgrade / denial:** an attacker able to spoof or control a
   parent-zone response that already passes id + question + bailiwick checks can
   force veri-dns to answer NODATA for a delegated child simply by setting AA=1
   on the referral. unbound would still descend and return the real record.

## Fix direction

Classification of a delegation-shaped response as a followable referral should
not be gated on `AA == 0`. Mirror unbound: a below-origzone NS RRset in the
authority section (no answer, no CNAME, no SOA, in-bailiwick, closer than the
current SLIST) is a referral irrespective of the AA bit. The `AA` bit should
only affect cache credibility, not whether the delegation is followed.
