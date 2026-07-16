# 037 — Fixed-length rdata (A/AAAA) is never length-validated: veri-dns caches and serves mis-sized records; unbound strips them

- **Component:** `VeriDNS/Impl/ResourceRecord.lean` (decode), `VeriDNS/Impl/Message.lean` (decodeRRCanonical fall-through), cache path `VeriDNS/Impl/Resolver.lean`, delivery `VeriDNS/Impl/Server.lean`
- **Class:** impl-bug (missing RFC 1035 §3.4.1 / RFC 3596 §2.2 fixed-length rdata validation)
- **Severity:** low–moderate — requires a malicious/broken authoritative or on-path responder, but is a deterministic, wire-observable divergence: veri-dns delivers a malformed RRset a stub cannot parse and caches it; unbound sanitizes it away.

## Summary

veri-dns's RR decoder reads exactly `RDLENGTH` bytes for **any** RR type and
stores/serves them unchanged. Nothing on the on-path pipeline (decode →
bailiwick → cache → normalize → scrub → cap-TTL → re-encode) checks that an
`A` record's rdata is 4 bytes or an `AAAA`'s is 16 bytes. A crafted
authoritative response of `bad.example.test A` with `RDLENGTH=16` (16 bytes of
rdata) is decoded, cached, and re-emitted to the stub verbatim as a malformed
16-byte A record.

`VeriDNS/Impl/ResourceRecord.lean:17`:
```
let rdata ← DnsParser.readBytes rdlength.toNat   -- no per-type length check
```

unbound rejects such records during sanitize
(`iterator/iter_scrub.c` `scrub_sanitize_rr_length`: an A rrset entry must be
6 bytes = 2 (rdlen) + 4, an AAAA 18 = 2 + 16, else `remove_rrset` +
EDE "records of inappropriate length").

## Reproduction (on the review rig)

`nsd` cannot emit a mis-sized fixed-length record, so the leaf authoritative
(10.53.0.12) was temporarily replaced with a raw responder
(`penn-testing/_vmdns/badlen_responder.py`) that mimics the real
`example.test.` zone but answers three crafted names with wrong-length rdata:

| name | qtype | RDLENGTH emitted | correct |
|------|-------|------------------|---------|
| `bad.example.test`     | A    | 16 | 4  |
| `bad7.example.test`    | A    | 7  | 4  |
| `badaaaa.example.test` | AAAA | 4  | 16 |

Setup:
```
# in the auth netns, stop the leaf nsd and run the responder on 10.53.0.12:53
systemctl stop veridns-auth-leaf
systemd-run --unit=badlen-resp --collect \
  ip netns exec auth python3 /opt/dnsenv/badlen_responder.py 10.53.0.12
```
Baseline sanity (both resolvers, through the responder):
`host.example.test A` → `10.53.0.101` on both. Then:

### Case 1 — `bad.example.test A`, RDLENGTH=16

veri-dns (`@10.53.0.2:5300`) — dig cannot even parse the reply:
```
;; Got bad packet: extra input data
78 bytes
... 03 62 61 64 07 65 78 61 6d 70 6c 65 04 74 65 73 74 00   (bad.example.test)
   00 01 00 01 00 00 0e 10 00 10 00 01 02 03 04 05 06 07    (A IN ttl=3600 RDLENGTH=0x0010 + 16 rdata bytes)
   08 09 0a 0b 0c 0d 0e 0f
```
The answer RR is TYPE=0x0001 (A), RDLENGTH=0x0010 (16), 16 rdata bytes — a
malformed A record on the wire.

unbound (`@10.53.0.3:5301`):
```
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 47502
;; flags: qr rd ra; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1
```
NOERROR with the record stripped (`ANSWER: 0`).

### Case 2 — `bad7.example.test A`, RDLENGTH=7

veri-dns: `;; Got bad packet: extra input data` — RR is A with
RDLENGTH=0x07 + 7 rdata bytes (`... 00 01 00 01 00 00 0e 10 00 07 00 01 02 03 04 05 06`).
unbound: `status: NOERROR ... ANSWER: 0` (stripped).

### Case 3 — `badaaaa.example.test AAAA`, RDLENGTH=4

veri-dns: `status: NOERROR ... ANSWER: 1` with `;; WARNING: Message has 4 extra
bytes at end` — the 4-byte AAAA is served (malformed; the 4 rdata bytes trip
dig's trailing-byte check).
unbound: `status: NOERROR ... ANSWER: 0` (stripped).

### Cache persistence

Re-querying `bad.example.test A` a second time still returns the malformed A
record, now with a **decremented TTL** (`0x00000e10` = 3600 →`0x00000e02` = 3586),
proving veri-dns cached the mis-sized record and served it from cache — not just
a transparent pass-through.

## Root cause

`ResourceRecord.decode` and `Message.decodeRRCanonical` read `RDLENGTH` bytes for
any type and re-serialize with `rdlength := rdata.size`. `extractAAddress`
(`Server.lean`) enforces `size == 4` only when using an A record as a **glue
address**, never for caching/serving it as an answer. There is no per-type
fixed-length gate for A (4) or AAAA (16) anywhere on the answer path.

## Fix direction

During sanitize/normalize (before cache insert and before delivery), drop any
`IN A` RR whose rdata length != 4 and any `IN AAAA` RR whose rdata length != 16
(cf. unbound `scrub_sanitize_rr_length`), optionally emitting EDE "records of
inappropriate length".

## Citations

- RFC 1035 §3.4.1: A RDATA is a 32-bit (4-byte) internet address.
- RFC 3596 §2.2: AAAA RDATA is a 128-bit (16-byte) address.
- unbound `iterator/iter_scrub.c` `scrub_sanitize_rr_length` (A→6, AAAA→18, else
  `remove_rrset`), invoked from `scrub_message`.

## Rig restored

`badlen-resp` stopped, `veridns-auth-leaf` (nsd) restarted; `host.example.test A`
→ `10.53.0.101` on veri-dns again. Responder script left at
`penn-testing/_vmdns/badlen_responder.py` for re-runs.

## Regression re-verification (2026-07-15, post-remediation commit 26b5849)

**STILL PRESENT.** Re-run on the renumbered rig (verid @203.0.113.2:5300 vs
unbound @203.0.113.3:5301), both resolvers restarted, leaf `nsd` replaced by
`penn-testing/_vmdns/badlen_responder2.py` on 203.0.113.12. Baseline through the
responder first: `host.example.test A` → 203.0.113.101 on veri-dns.

```
=== bad A (RDLENGTH=16) ===
  VERID:   ;; Got bad packet: extra input data
  UNBOUND: status: NOERROR, ANSWER: 0            (record stripped)
=== bad7 A (RDLENGTH=7) ===
  VERID:   ;; Got bad packet: extra input data
  UNBOUND: status: NOERROR, ANSWER: 0            (record stripped)
=== badaaaa AAAA (RDLENGTH=4) ===
  VERID:   status: NOERROR, ANSWER: 1
           ;; WARNING: Message has 4 extra bytes at end
  UNBOUND: status: NOERROR, ANSWER: 0            (record stripped)
```

Identical to the original observation: veri-dns delivers the mis-sized A/AAAA
records to the stub (unparseable for the two A cases), unbound sanitizes them
away. `ResourceRecord.decode` still does `readBytes rdlength.toNat` with no
per-type fixed-length gate.

**Numbering note — this file is NOT the "037" of `REPORT.md`.** `REPORT.md:81`
lists 037 as "name-bearing RDATA for MX/SRV forwarded verbatim with compression
pointers", which is the subject of finding **029** and which upstream **did**
fix (verified: MX exchange now decompressed, rdlen 9 → 21, no pointer in the
re-emitted rdata). The remediation plan's "### 037 — name-bearing RDATA
forwarded with compression pointers intact — ✅ FIXED" therefore closes the
*MX/SRV* issue and says nothing about A/AAAA rdata length validation. This
fixed-length-rdata finding is **unaddressed and unmentioned** by the plan — it
is not covered by the plan's "every review finding is now fixed, theorem-pinned,
or scoped out" claim under any number. Unpinned, unfixed.
