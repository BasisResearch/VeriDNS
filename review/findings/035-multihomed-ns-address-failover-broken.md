# 035 — Multi-homed nameserver address failover is broken: veri-dns re-queries the first glue address forever (or drops both on one REFUSED) and never tries a sibling address of the same NS

---

## ⚠️ REGRESSION STATUS 2026-07-15 (vs upstream 26b5849): **STILL PRESENT — never addressed**

`docs/remediation-plan.md` **does not mention finding 035 anywhere** (the plan was
triaged against `47efe79` and stops at #037 + "Item 4"). The claim that *"every
review finding is now fixed, theorem-pinned, or scoped out with rationale"* does
not hold for this finding: it is neither fixed, nor pinned, nor scoped out.

The cited root cause is **unchanged in the current source**:
- `VeriDNS/Impl/SList.lean:79-81` — `markQueried` still keys on `e.name == name`,
  so it bumps `transmissionCount` on *every* address entry sharing that NS name.
- `VeriDNS/Impl/SList.lean:26-27` — `removeServer` still keys on `e.name != name`.
- `VeriDNS/Impl/Server.lean:655` — `slist.markQueried entry.name` (name, not address).
- `VeriDNS/Impl/Server.lean:684`, `:414` — `removeServer entry.name` / `entryName`.
There is still no per-address `attempts` counter and no address-level splice.

### Re-run of the ORIGINAL repro on the current rig (renumbered to 203.0.113.0/24)

TLD hands out two glue A records for the single NS `ns.example.test.`, dead
address first (verified via `dig @203.0.113.11`):
```
ns.example.test.	3600	IN	A	203.0.113.6     ; dead (nobody answers ARP)
ns.example.test.	3600	IN	A	203.0.113.12    ; real nsd
```

**veri-dns**, cold — SERVFAIL after ~6 s; capture on `v-verid` filtered to both
glue addresses:
```
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 3389
;; Query time: 6147 msec

to 203.0.113.6 : 6      <- every attempt goes to the dead address
to 203.0.113.12: 0      <- the live sibling is NEVER contacted
```

**unbound**, same zone, 5 cold restarts (fresh cache each; PID verified to change)
— it tries the dead `.6`, fails over to `.12`, and answers every time:
```
unbound iter 1: ->.6=0 ->.12=1  answer=[host.example.test. 3600 IN A 203.0.113.101]
unbound iter 2: ->.6=1 ->.12=1  answer=[host.example.test. 3600 IN A 203.0.113.101]
unbound iter 3: ->.6=1 ->.12=1  answer=[host.example.test. 3600 IN A 203.0.113.101]
unbound iter 4: ->.6=1 ->.12=1  answer=[host.example.test. 3600 IN A 203.0.113.101]
unbound iter 5: ->.6=1 ->.12=1  answer=[host.example.test. 3600 IN A 203.0.113.101]
```
Iterations 2-5 are the airtight comparison: unbound sends exactly one datagram to
the dead address, then one to the live sibling, and resolves. veri-dns sends six
to the dead address and none to the sibling.

Rig restored to baseline afterwards (single glue A, both resolvers agreeing).

---

- **Classification:** impl-bug (observable client-visible divergence from unbound)
- **Component:**
  - `VeriDNS/Impl/SList.lean:58-65` (`fromNsWithGlueAll` — one `SlistEntry` per address, all sharing the same `name`)
  - `VeriDNS/Impl/SList.lean:76-87` (`pickBest`/`bestWithAddress` — stable tie-break keeps the earlier entry)
  - `VeriDNS/Impl/SList.lean:89-91` (`markQueried` — filters on `e.name == name`, so it bumps the count of *every* address entry of that name equally)
  - `VeriDNS/Impl/Server.lean:404-410` (timeout path: `upstreamResp = none` → `markQueried entry.name` → re-loop) and the `removeServer`/dropIfBizarre path (REFUSED case removes both address entries because it is name-keyed)
- **Trigger:** a nameserver with **two or more glue A records**, where the address selected first is unreachable/refusing and a sibling address of the *same* NS name would answer.

## Summary

A referral for a single NS host that has multiple glue addresses is expanded by
`fromNsWithGlueAll` into one `SlistEntry` per address, all carrying the **same**
`name` (e.g. `⟨ns.example.test, 10.53.0.6⟩` and `⟨ns.example.test, 10.53.0.12⟩`).
Every SLIST mutation that veri-dns performs after a failed exchange is keyed by
**name**, not by address, so the two sibling entries are indistinguishable and
are mutated together. The consequence is that veri-dns never advances from a
dead first address to a live sibling address of the same nameserver:

- **No reply / timeout:** `markQueried entry.name` (Server.lean:406-407) bumps
  `transmissionCount` on **both** entries equally. `pickBest`
  (`if e.transmissionCount < b.transmissionCount then e else b`, SList.lean:84)
  keeps the earlier entry on every tie, so the *same* first address is
  re-selected every round until the ~5 s deadline → SERVFAIL. Zero packets ever
  reach the second address.
- **REFUSED (fast negative):** the name-keyed removal path strips *both* address
  entries on the single REFUSED from address #1, leaving "no servers with
  addresses in SLIST" → immediate SERVFAIL, again without ever contacting
  address #2.

Failover across distinct NS **names** works (each name is marked/removed
independently); the defect is specific to multiple addresses of one nameserver
name — a very common real-world config (multi-homed authoritative servers, one
leg down).

unbound tracks attempts and dead state **per address** (`delegpt_addr.attempts`,
`iter_delegpt.c`; splice-out in `iter_utils.c`) and advances to the next address
of the same name, answering correctly.

## Reproduction (on the rig)

Rig delegates `example.test.` to the single NS `ns.example.test.`. I added a
second glue A record so the referral lists a dead address **first** and the real
nsd (`10.53.0.12`) **second**, then queried cold-cache.

### A. No-reply first address (`10.53.0.6` unrouted/black-holed)

TLD zone additional section (verified via `dig @10.53.0.11`):

```
ns.example.test.  3600  IN  A  10.53.0.6      ; dead (ARP never resolves)
ns.example.test.  3600  IN  A  10.53.0.12     ; real nsd
```

veri-dns (`10.53.0.2:5300`), cold:

```
;; ->>HEADER<<- opcode: QUERY, status: SERVFAIL, id: 1744
;; Query time: 6153 msec
```

veri-dns log:

```
query host.example.test → a.tld.test (fuel 38)
resp: rcode=0 an=0 ns=1 ar=2 tc=0x0
query host.example.test → ns.example.test (fuel 37)
SERVFAIL: resolveWithIO: query deadline exceeded
```

tcpdump on `brdns` filtered to both glue addresses — **every** attempt goes to
`10.53.0.6`, **zero** packets to `10.53.0.12`:

```
16:47:15.690419 ARP, Request who-has 10.53.0.6 tell 10.53.0.2
16:47:16.722617 ARP, Request who-has 10.53.0.6 tell 10.53.0.2
16:47:17.746757 ARP, Request who-has 10.53.0.6 tell 10.53.0.2
16:47:19.795254 ARP, Request who-has 10.53.0.6 tell 10.53.0.2
16:47:20.818781 ARP, Request who-has 10.53.0.6 tell 10.53.0.2
16:47:21.842777 ARP, Request who-has 10.53.0.6 tell 10.53.0.2
```

unbound (`10.53.0.3:5301`), same zone, cold:

```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR
host.example.test.  3600  IN  A  10.53.0.101
;; Query time: 1130 msec
```

unbound capture — after failing `10.53.0.6` it advances to `10.53.0.12`:

```
16:48:04.127433 IP 10.53.0.3.33900 > 10.53.0.12.53: A? host.example.test.
16:48:04.127939 IP 10.53.0.12.53 > 10.53.0.3.33900: A 10.53.0.101
```

### B. REFUSED first address (a `10.53.0.6` responder returning RCODE=5)

veri-dns:

```
query host.example.test → ns.example.test (fuel 37)
resp: rcode=5 an=0 ns=0 ar=0 tc=0x0
SERVFAIL: resolveWithIO: no servers with addresses in SLIST
```

Capture — one query to `10.53.0.6`, REFUSED, then give up; `10.53.0.12` never
tried:

```
16:49:29.974760 IP 10.53.0.2.47531 > 10.53.0.6.53: A? host.example.test.
16:49:29.974910 IP 10.53.0.6.53 > 10.53.0.2.47531: Refused- 0/0/0
```

unbound, same setup — tries `10.53.0.6` (REFUSED), fails over to `10.53.0.12`:

```
16:49:49.126751 IP 10.53.0.3.27882 > 10.53.0.6.53: A? host.example.test.
16:49:49.126864 IP 10.53.0.6.53 > 10.53.0.3.27882: Refused-
16:49:49.126943 IP 10.53.0.3.19993 > 10.53.0.12.53: A? host.example.test.
16:49:49.127016 IP 10.53.0.12.53 > 10.53.0.3.19993: A 10.53.0.101
```

### C. Control — swap glue order (working address first)

With `10.53.0.12` listed first, veri-dns succeeds instantly (`Query time: 0
msec`, `A 10.53.0.101`), confirming the failure is specifically first-address
selection and the absence of per-address failover.

## Root cause

`SlistEntry` identity for every post-exchange mutation is the NS **name**, but
`fromNsWithGlueAll` produces multiple entries sharing one name:

- `markQueried` (SList.lean:89-91): `if e.name == name then … +1` — bumps all
  sibling addresses, so `pickBest`'s strict-`<` tie-break (SList.lean:84) never
  rotates off the first address.
- name-keyed `removeServer` (SList.lean:26-27, `e.name != name`) removes *all*
  addresses of the name on a single bizarre/REFUSED response.

There is no per-address `attempts`/dead marker and no address-level splice, so a
timed-out or refusing address is never individually retired.

## RFC / reference

- RFC 1034 §5.3.3 and RFC 1035 §7.2: a resolver's SLIST holds the addresses of
  the servers, and it is expected to try alternative addresses when one does not
  respond ("keep track of … which have been tried" is per address, since the
  transmission is to an address).
- unbound: `delegpt_addr.attempts` is per-address (`iter_delegpt.c`); after
  `outbound_msg_retry` attempts the address is spliced out of the result list
  and the next address selected (`iter_utils.c`, `iter_resptype.c`
  `RESPONSE_TYPE_THROWAWAY` for REFUSED).

## Impact

Any multi-homed authoritative nameserver with one dead/refusing address leg
causes veri-dns to SERVFAIL the entire name, even though a correct resolver
(and unbound) resolves it via the sibling address. This is a common operational
configuration, so the availability impact is real, not merely theoretical.
