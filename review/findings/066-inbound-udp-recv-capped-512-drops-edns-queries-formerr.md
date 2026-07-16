# 066 — Inbound UDP recv buffer hard-capped at 512 bytes truncates and FORMERRs valid EDNS queries >512 octets

**Classification:** coverage-gap (unverified IO glue; the sound spine starts at an already-decoded `Format`, nothing links the 512 recv literal to `Edns.clientCap`'s 1232)
**unboundDiffers:** YES
**Distinct from 063:** finding 063 is the *egress/reply* direction (`Edns.clientCap` over-truncating the **answer**). This is the *ingress/query* direction: the UDP serve loop reads at most **512 octets of the client datagram**, so a query larger than 512 is silently clipped by the kernel, `Message.decode` fails on the truncated OPT tail, and the datagram is rejected as FORMERR. Different code path, different data flow, independently reachable.

## Claim

`udpServeLoop` reads the client datagram with a fixed 512-octet buffer:

- `VeriDNS/Main.lean:87` — `UdpSocket.recvFrom (M := IO) (Sock := UInt32) clientSock 512`
- the FFI backing it (`ffi/recvfrom.c:78-105`, `veri_dns_recvfrom`) calls `recvfrom(fd, buf, maxBytes=512, ...)`. UDP `recvfrom` with a buffer shorter than the datagram **discards the excess** (returns `n = 512`), so `queryBytes` is the first 512 octets only.

veri-dns advertises EDNS and honors client OPT sizes up to 1232 on the reply side (`Edns.clientCap`, `Impl/Edns.lean`), but it cannot **receive** a query larger than 512 octets. When the datagram is clipped, `Message.decode` fails on the truncated OPT rdata, `serveDatagram` falls through to `rawDatagramReply` (`Impl/Server.lean:124`) which — because the 12-byte header still decodes with `qr=0`/`opcode=query` — emits FORMERR with all sections zeroed.

Legitimate EDNS queries exceed 512 octets in practice: EDNS(0) PADDING (RFC 7830/8467), EDNS client-subnet (RFC 7871), DNS cookies, and stacked options. There is no covering theorem: the verified spine begins at an already-decoded `Format`; nothing constrains the ingress buffer size or links the `512` recv literal to the advertised 1232.

## Reproduction (wire, both resolvers cold)

Both resolvers restarted cold immediately before the differential (rule 3):

```
$ systemctl restart veridns-verid veridns-ref; sleep 2   # both active
$ ip netns exec attacker dig @203.0.113.2 -p 5300 example.test A +short   # 203.0.113.100
$ ip netns exec attacker dig @203.0.113.3 -p 5301 example.test A +short   # 203.0.113.100
```

Raw single UDP datagram: an `A example.test` query carrying one OPT RR
(class/udpsize=1232) with an EDNS(0) PADDING option (code 12) sized to push the
datagram just over 512 octets. Sent to veri-dns:5300 and unbound:5301; reply
rcode read off the wire (script `/tmp/ednsbig.py`, padding length as argv[1]).

Boundary sweep — the divergence is exactly at 512 vs 513 octets:

```
# datagram size = 511 bytes (padding=466)
veri-dns: sent 511 bytes -> reply 58 bytes, qr=1, rcode=NOERROR, ancount=1
unbound : sent 511 bytes -> reply 57 bytes, qr=1, rcode=NOERROR, ancount=1

# datagram size = 512 bytes (padding=467)
veri-dns: sent 512 bytes -> reply 58 bytes, qr=1, rcode=NOERROR, ancount=1
unbound : sent 512 bytes -> reply 57 bytes, qr=1, rcode=NOERROR, ancount=1

# datagram size = 513 bytes (padding=468)
veri-dns: sent 513 bytes -> reply 12 bytes, qr=1, rcode=FORMERR, ancount=0
unbound : sent 513 bytes -> reply 57 bytes, qr=1, rcode=NOERROR, ancount=1

# datagram size = 605 bytes (padding=560)   (the rationale's ~600B example)
veri-dns: sent 605 bytes -> reply 12 bytes, qr=1, rcode=FORMERR, ancount=0
unbound : sent 605 bytes -> reply 57 bytes, qr=1, rcode=NOERROR, ancount=1
```

Identical OPT-bearing query under the cap (445 octets) is answered by **both**
NOERROR+1 — isolating the 512-octet recv buffer as the sole cause:

```
# datagram size = 445 bytes (padding=400)
veri-dns: sent 445 bytes -> reply 58 bytes, qr=1, rcode=NOERROR, ancount=1
unbound : sent 445 bytes -> reply 57 bytes, qr=1, rcode=NOERROR, ancount=1
```

At and below 512 octets veri-dns == unbound (NOERROR, A record). At 513 octets
and above veri-dns returns a 12-byte FORMERR while unbound returns the correct
NOERROR answer, on the identical cold-cache path against identical data.

## Why veri-dns is wrong (citation)

- **RFC 6891 §6.2.5 / §6.2.4:** a responder advertising/honoring EDNS UDP buffer
  sizes must be able to *receive* requestor messages up to the negotiated size in
  a single UDP datagram. Sizing the inbound buffer at 512 while advertising 1232
  makes the honoring one-directional and rejects well-formed EDNS queries.
- **RFC 1035 §4.2.1** bounds *non-EDNS* UDP messages at 512; EDNS(0) exists
  precisely to lift that limit, and a query using OPT is entitled to exceed 512.
  A truncated read is not a malformed message — FORMERR misattributes the fault.
- **Unbound** sizes its inbound buffer from `msg-buffer-size` (default 65536) and
  answers the 513/605-octet EDNS query NOERROR with the A record.

The consequence: any EDNS client whose padded/optioned/cookie-bearing query
crosses 512 octets gets FORMERR from veri-dns and a correct answer from unbound —
an EDNS-surface interop break with no covering theorem.

## Fix direction

Size the inbound UDP recv buffer to at least the advertised EDNS max (1232, the
same `VERI_DNS_UPSTREAM_BUFSIZE` already used for upstream reads in
`ffi/recvfrom.c`), not 512. Then thread a spec obligation linking the ingress
buffer size to `Edns.advertisedUdpSize` so the recv literal cannot silently drop
back below the advertised cap.

## Rig hygiene

No tracked source edited (source-level + wire confirmation only; no mutation
required). Only ephemeral `/tmp/ednsbig.py` staged inside the VM. Rig baseline
unchanged; both resolvers left running.
