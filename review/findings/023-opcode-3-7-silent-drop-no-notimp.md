# 023: Standard opcodes 3-7 (incl. NOTIFY/UPDATE) are silently black-holed instead of answered NOTIMP

**Classification:** coverage-gap
**Observable:** yes (dig timeout vs NOTIMP, from attacker vantage)
**Component:** `VeriDNS/Spec/Header.lean:19-25` (`Opcode.ofCode`), `VeriDNS/Impl/Enum.lean:12-13` (`Opcode.ofBV4`), `VeriDNS/Impl/Header.lean:16-18` (decode → `DnsParser.fail`), `VeriDNS/Impl/Server.lean:115` (`rawDatagramReply = none`)

## Summary

`VeriDNS.Spec.Opcode` has only three constructors — `query(0)`, `iquery(1)`, `status(2)`.
`Opcode.ofCode` returns `Except.error` for every other value of the 4-bit OPCODE field,
and `Impl/Header.lean:16-18` promotes that error to `DnsParser.fail`, making the entire
message undecodable. An undecodable datagram takes the hardened silent-drop path
(`rawDatagramReply = none`, `Server.lean:115`), so a syntactically perfect DNS query
carrying opcode 3, NOTIFY(4), UPDATE(5), 6, or 7 gets **no reply at all**.

Meanwhile the NOTIMP machinery (`supportsQueryKind` / `queryProblem`,
`Server.lean:92-105`) does exist and fires for IQUERY and STATUS — proving partial
opcode support and making the 3-7 black-hole an inconsistency, not a uniform policy.

## Why the proofs did not catch it

`hygiene_notImplemented` (`VeriDNS/Proof/Server.lean:299-305`) proves that any
interpretable query failing `supportsQueryKind` gets `Rcode.notImplemented`. But it is
quantified over `Format`, whose header opcode field has type `Spec.Opcode` — a type in
which opcodes 3-7 are **unrepresentable**. Those wire values are excluded at the parser
boundary before the verified property's domain begins, so the theorem is true yet
vacuous for exactly the packets at issue. The doc comment at `Server.lean:107-114`
("decodable-but-malformed queries ... still receive a proper FORMERR/NOTIMPL/REFUSED")
is therefore not honored for well-formed NOTIFY/UPDATE packets: they are classified as
UNdecodable purely because the enum is incomplete.

## Reproduction (rig, 2026-07-07)

```
for op in IQUERY STATUS 3 NOTIFY UPDATE 6 7:
  ./penn-testing/vm/ssh.sh "ip netns exec attacker dig +noedns +opcode=$op \
      +tries=1 +time=2 @10.53.0.2 -p 5300 example.test A"
```

veri-dns (10.53.0.2:5300):

| opcode | result |
|---|---|
| IQUERY (1) | `status: NOTIMP` |
| STATUS (2) | `status: NOTIMP` |
| 3 | `;; communications error to 10.53.0.2#5300: timed out` (no reply) |
| NOTIFY (4) | timed out (no reply) |
| UPDATE (5) | timed out (no reply) |
| 6 | timed out (no reply) |
| 7 | timed out (no reply) |

unbound reference (10.53.0.3:5301), same queries:

| opcode | result |
|---|---|
| NOTIFY (4) | `status: REFUSED` (unbound implements NOTIFY with an ACL; unauthorized source → REFUSED) |
| 3 | timed out (silent drop) |
| UPDATE (5) | timed out (silent drop) |
| 6 | timed out (silent drop) |
| 7 | timed out (silent drop) |

So the hard divergence vs unbound is NOTIFY only; unbound also drops the other unknown
opcodes silently. The internal inconsistency of veri-dns remains regardless: it answers
NOTIMP for opcodes 1/2 but black-holes 3-7, and its own code comment promises otherwise.

## RFC citation

- RFC 1035 §4.1.1: RCODE 4 "Not Implemented - The name server does not support the
  requested kind of query"; OPCODE values 3-15 are "reserved for future use" — they are
  legal wire values, not malformed packets.
- RFC 6895 §2.2 records opcodes 4 (NOTIFY, RFC 1996) and 5 (UPDATE, RFC 2136) as
  standard assignments; a resolver that does not implement them should signal
  NOTIMP (as BIND does), or at minimum respond (unbound: REFUSED for NOTIFY),
  rather than be indistinguishable from a dead host.

## Re-verification (rig, 2026-07-08)

Independent re-run reproduced the table above exactly (veri-dns: NOTIMP for 1/2,
timeout for 3-7; unbound: REFUSED for NOTIFY(4) only, silent drop for 1,2,3,5,6,7).
Packet-level confirmation that the drop is a true black-hole (no reply datagram, not an
ICMP or malformed response):

```
$ ip netns exec attacker tcpdump -n -r /tmp/notify.pcap   # filter: host 10.53.0.2 and port 5300
17:09:00.364738 v-attacker Out IP 10.53.0.99.50055 > 10.53.0.2.5300: UDP, length 30
```

One packet on the wire — the NOTIFY query out; zero bytes back from 10.53.0.2:5300.

## Suggested fix direction

Represent the full 4-bit opcode space (e.g. an `unassigned (BitVec 4)` constructor or
keep the raw code) so header decode never fails on opcode alone; then `supportsQueryKind`
and the already-proved `hygiene_notImplemented` naturally extend to opcodes 3-15 and the
NOTIMP path becomes reachable for them.
