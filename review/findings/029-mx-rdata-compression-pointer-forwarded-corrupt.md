# 029 — MX (and all non-{NS,CNAME,PTR,SOA}) RDATA compression pointers are forwarded verbatim, corrupting the packet

**Status:** CONFIRMED (live differential repro on the rig)
**Severity:** impl-bug — client receives an unparseable/corrupt answer for ordinary MX lookups against compressing authoritative servers (BIND, etc.)
**Component:** `VeriDNS/Impl/Message.lean:20-41` (`decodeRRCanonical`)
**Reference:** RFC 1035 §3.3.9 (MX EXCHANGE is a `<domain-name>`, subject to compression per §4.1.4), RFC 3597 §4 (a resolver MUST NOT emit a compression pointer that does not correctly reference a prior name in the *outgoing* message); unbound `iter_scrub` / `util/data/msgparser` decompresses all name-bearing RDATA.

## The defect

`decodeRRCanonical` fully decompresses and re-canonicalizes the domain name
inside RDATA only for rrtype 2 (NS), 5 (CNAME), 12 (PTR) and 6 (SOA):

```
let rdata ← if rrtype == 2 || rrtype == 5 || rrtype == 12 then …decodeName…   -- :20-28
            else if rrtype == 6 then …two names + 20 bytes…                    -- :29-39
            else DnsParser.readBytes rdlen.toNat                               -- :41  <-- MX/SRV/NAPTR/RP/KX…
```

Every other name-bearing type — MX(15), SRV(33), NAPTR(35), RP(17), KX(36),
etc. — falls to `readBytes rdlen` and is re-emitted verbatim at :43-47. RFC 1035
permits (and BIND routinely emits) a **compression pointer** for the MX EXCHANGE
name. The pointer's 14-bit offset is only meaningful in the *upstream* packet's
byte layout.

The owner name (`rrName`, :13-14) *is* decompressed and re-expanded, so when
veri-dns rebuilds its own message the byte offsets shift. The copied pointer
bytes (`0xC0 0xXX`) now dereference into the wrong location of veri-dns's own
packet — mid-field garbage — corrupting the embedded name. Owner-name/bailiwick
handling is unaffected, which is why the bug is silent to the cache logic.

## Reproduction (on the rig)

`nsd` does not compress RDATA names, so a crafted authoritative responder is
required. `review/env/../penn-testing/_vmdns/mx_responder.py` binds
`10.53.0.12:53` (the delegated leaf NS, after stopping `nsd-leaf`) and answers
`MX example.test` with:

- ANSWER: `example.test MX 10 <exchange>` where the exchange RDATA =
  `00 0a`(pref=10) `04 'mail'` `c0 33`(compression pointer → offset 0x33).
- AUTHORITY: `bigmailserver.example.test A 10.53.0.222` — this name begins at
  offset **0x33** in the *upstream* packet.

So the true exchange name is `mail.bigmailserver.example.test`.

Bring-up:
```
# stop the honest leaf, run the crafted responder in its place
systemctl stop veridns-auth-leaf
systemd-run --unit=mx-responder --collect ip netns exec auth \
    python3 /opt/dnsenv/mx_responder.py 10.53.0.12
systemctl restart veridns-verid        # clear negative-MX cache
```

### veri-dns (under test) — CORRUPT
```
$ ip netns exec attacker dig @10.53.0.2 -p 5300 example.test MX
;; Got bad packet: bad label type
105 bytes
f5 ff 81 80 00 01 00 01 00 01 00 00  07 65 78 61   ...header/question…
6d 70 6c 65 04 74 65 73 74 00 00 0f  00 01 07 65   example…
78 61 6d 70 6c 65 04 74 65 73 74 00  00 0f 00 01   answer owner EXPANDED example.test
00 00 0e 10 00 09 00 0a 04 6d 61 69  6c c0 33 0d   …ttl,rdlen,pref,04 mail, C0 33 ← raw ptr
62 69 67 6d 61 69 6c 73 65 72 76 65  72 07 65 78   bigmailserver.ex
61 6d 70 6c 65 04 74 65 73 74 00 00  01 00 01 00   ample.test…
00 0e 10 00 04 0a 35 00 de                          …A 10.53.0.222
```
veri-dns copied the exchange RDATA byte-for-byte (`04 6d 61 69 6c c0 33`). But it
**expanded the answer owner** from the upstream's 2-byte pointer to the full
14-byte `example.test`, shifting every subsequent offset by +12. In veri-dns's
packet, offset 0x33 (51) now lands in the **middle of the TTL field** (byte
`0x10`), not the authority owner. dig follows the pointer into garbage and
rejects the whole datagram: `Got bad packet: bad label type`.

### unbound (reference) — CORRECT
```
$ ip netns exec attacker dig @10.53.0.3 -p 5301 example.test MX
;; ANSWER SECTION:
example.test.  3600  IN  MX  10 mail.bigmailserver.example.test.
```
unbound decompresses the exchange on ingest and re-emits a valid, self-consistent
packet.

## Impact

Any MX (or SRV/NAPTR/RP/KX/…) answer whose RDATA name is compressed by the
authoritative server is delivered to the client corrupt — either an unparseable
datagram (as here) or, depending on where the stale offset lands, a *silently
wrong* exchange/target hostname. This breaks ordinary mail routing and SRV-based
service discovery against RFC-compliant compressing authoritatives (BIND is the
common case). The fix is to decompress name-bearing RDATA for all such types
(cf. RFC 3597 §4 / unbound `iter_scrub`), not just the four special-cased types.

## Notes / rig hygiene

- Repro artifact: `penn-testing/_vmdns/mx_responder.py` (staged to
  `/opt/dnsenv/mx_responder.py` in the VM).
- Rig restored afterward: `mx-responder` stopped, `veridns-auth-leaf` re-launched
  via `systemd-run`, `veridns-verid` restarted; `host.example.test A` →
  10.53.0.101 and `www.example.test` → example.test A 10.53.0.100 confirmed.
