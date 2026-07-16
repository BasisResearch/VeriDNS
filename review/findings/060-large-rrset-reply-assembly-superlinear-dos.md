# 060 — Large-RRset reply assembly is super-linear (≈cubic): a few-hundred-record answer pegs a CPU and never replies (DoS)

**Severity:** High (remote DoS: one small query burns minutes of CPU and delivers nothing)
**Surface:** reply pipeline `resolveWithIO → replyForResolution → deliveredResponse (scrubAnswerB / positive caching) → Message.encode` — hit on **both UDP and TCP**.
**Status:** CONFIRMED by wire-level differential vs unbound on identical data with cold caches.

## Relationship to the suspected bug (TCP length-prefix wrap)

This investigation started from the suspicion that `TcpFraming.lenPrefix` (`VeriDNS/Impl/TcpFraming.lean:8`) wraps mod 65536, so a >65535-byte TCP reply would carry a length prefix disagreeing with its payload. **That specific mechanism is NOT reachable at runtime** and could not be observed: veri-dns cannot assemble a reply anywhere near 65535 bytes. It spins at ~100% CPU during reply assembly and fails to emit *any* frame for responses far below the wrap threshold (already ~27 s of CPU for a ~24 KB / 300-record answer; never completes for ~47 KB / 600 records). The length-prefix wrap is therefore masked behind a far more severe, more easily reached defect — a super-linear blowup in reply assembly. The wrap remains a latent code fact (`n/256, n%256` via `toUInt8`), but is dominated by this finding.

## Setup

Rig per `review/ENV.md` (renumbered 203.0.113.0/24). One large A RRset added to the leaf zone `example.test.` (owner label = 50×`b`, distinct rdata per record so nothing dedups):

```
<50×b>.example.test.        1500 × A   (1.0.x.y)      # nsd TCP answer: 24128 B compressed
m6<50×b>.example.test.       600 × A   (2.0.x.y)      # nsd TCP answer:  9727 B
m9<50×b>.example.test.       900 × A                  # nsd TCP answer: 14527 B
h3<50×b>.example.test.       300 × A   (5.0.x.y)      # ~24 KB uncompressed at veri-dns
h1<50×b>.example.test.       100 × A   (4.0.0.i)      # ~8 KB uncompressed at veri-dns
```

nsd (leaf, 203.0.113.12) serves every one of these correctly over TCP (e.g. 1500 records = 24128 B). Both resolvers restarted cold before each measurement (rule 3).

## Reproduction — veri-dns wall time vs answer size (cold cache, `dig +tcp`)

```
h1 (100 recs, ~8 KB) : ANSWER: 100,  Query time  1033 msec   OK
h3 (300 recs, ~24 KB): ANSWER: 300,  Query time 26978 msec   OK (but 27 s of CPU)
m6 (600 recs, ~47 KB): communications error ... timed out    NEVER (>90 s, CPU pegged)
1500 recs (~120 KB)  : communications error ... timed out    NEVER (CPU pegged 80+ s and climbing)
```

Scaling 100→300 records (3×): 1.03 s → 27.0 s ≈ **26×** — roughly cubic. 300→600 already exceeds a 90 s ceiling. Confirmed CPU-bound, not blocked: `/proc/<pid>/stat` utime climbs ~100 jiffies/s (100% of one core) throughout, e.g. 7765→8166 over 4 s wall.

The hang is **after** the upstream answer is fully received. tcpdump on the auth side shows veri-dns's upstream UDP query truncated (TC=1), its **TCP fallback succeeding** (full 24128 B transferred and ACKed, FIN clean), and then — on the client-facing interface — veri-dns sending the client **zero payload bytes** for the entire 30 s before the client's own FIN:

```
# client side (v-verid): client SYN/query in, veri-dns ACKs the 106-B query, then NOTHING back:
192.168.53.99.36092 > 203.0.113.2.5300: P. seq 1:107  (query)
203.0.113.2.5300 > 192.168.53.99.36092: . ack 107     (ack, no data ever follows)
... 30 s later ...
192.168.53.99.36092 > 203.0.113.2.5300: F.            (dig gives up)
```

**Not TCP-specific:** the same 600-record name over **UDP** also times out — `serveDatagram` calls `Message.encode response` on the *full* untruncated response *before* `truncateUdp` runs (`Impl/Server.lean:797`), so the blowup hits the UDP path identically.

## unbound differs (cold cache, identical data)

```
$ dig +tcp @203.0.113.3 -p 5301 <50×b>.example.test A
;; ->>HEADER<<- ... status: NOERROR
;; flags: qr rd ra; QUERY: 1, ANSWER: 1500, ...
;; Query time: 0 msec        (TCP)
```

unbound returns all 1500 records over TCP in **0 msec**; likewise for 600/300/100. It never spins and never fails to answer.

## Mechanism (code)

The DNS serializer is `StateM ByteArray` with `writeBytes bs := modify (· ++ bs)` and `writeUInt8 b := modify (·.push b)` (`VeriDNS/Impl/Parsec.lean:72,85`). `ByteArray.++`/`.push` are O(1) amortised only while the buffer is *uniquely referenced*; if the reference is shared each `modify` copies the whole accumulator, making a section of N records O(N²) — and the full pipeline (`scrubAnswerB` CNAME-reachability over the answer, `Message.encode`'s per-RR `writeBytes`, positive-cache `ownerRaws`) stacks into the ≈cubic curve measured. `Message.encode` performs **no name compression** (`Impl/Message.lean:88`), so veri-dns's own working set is larger than the compressed bytes nsd sent, amplifying the cost. unbound compresses and streams, staying flat.

## Why it matters / RFC

A recursive resolver must serve large but legal RRsets. RFC 1035 §4.2.2 mandates TCP for messages that don't fit UDP precisely so large answers remain deliverable; veri-dns instead consumes unbounded CPU and delivers nothing. A single unauthenticated query for any name backed by a few-hundred-record RRset (large A/AAAA/TXT sets, round-robin pools, some DNSBL/anti-spam zones) pins a worker at 100% CPU for tens of seconds to minutes, on both UDP and TCP — a cheap remote DoS. The verified boundary does not cover it: no theorem bounds reply-assembly cost, and `serveTcpDatagram_total`'s ≤65535 framing hypothesis is vacuously safe here only because assembly never terminates to reach the wrap.

## Cleanup

Leaf zone restored from backup (13 lines), `veridns-auth-leaf`/`veridns-verid`/`veridns-ref` restarted, baseline reverified: both resolvers return `host.example.test A 203.0.113.101`. No repo source edited; no build performed.
