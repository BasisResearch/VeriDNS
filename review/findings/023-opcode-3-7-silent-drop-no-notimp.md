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

## Regression re-verification (2026-07-15, post-remediation commit 26b5849)

STILL PRESENT. Re-run on renumbered rig (verid @203.0.113.2:5300, unbound
@203.0.113.3:5301), both resolvers restarted first. veri-dns: NOTIMP for
opcodes 1/2, NO REPLY (timeout) for 3-7. The 010b FORMERR fix does NOT help
here: `rawDatagramReply` (Server.lean:124) itself calls `Header.decode`, which
routes opcode through `Opcode.ofBV4` → `Opcode.ofCode` (Spec/Header.lean:19-24,
only 0/1/2 representable) → parse error → the "undecodable header" drop branch.
So a well-formed NOTIFY/UPDATE is still classified undecodable and black-holed.
Not in the remediation plan; unpinned, unfixed.

### Correction (2026-07-15, second independent regression pass)

An earlier appended note on this file claimed "this unbound answers NOTIMP for
opcodes 3,5,6,7 and REFUSED for NOTIFY(4) — veri-dns replies to NONE of 3-7",
i.e. that the divergence had WIDENED. **That claim is wrong** and is retracted.
Independently re-measured on the renumbered rig, both resolvers restarted:

```
opcode=QUERY   verid=  status: NOERROR          unbound= status: NOERROR
opcode=IQUERY  verid=  status: NOTIMP           unbound= timed out
opcode=STATUS  verid=  status: NOTIMP           unbound= timed out
opcode=3       verid=  timed out                unbound= timed out
opcode=NOTIFY  verid=  timed out                unbound= status: REFUSED
opcode=UPDATE  verid=  timed out                unbound= timed out
opcode=6       verid=  timed out                unbound= timed out
opcode=7       verid=  timed out                unbound= timed out
```

unbound **silently drops** opcodes 3, 5, 6 and 7 — exactly as the original
2026-07-07 and 2026-07-08 observations recorded. Per the review's own rule
("a finding is not a finding until unbound disagrees"), the only genuine
reference divergence here is **NOTIFY(4)**: unbound REFUSED vs veri-dns silent
drop. For 3/5/6/7 veri-dns and unbound behave identically, so that part is the
DNS trust model, not a veri-dns defect.

What survives, and why this stays open as a coverage-gap:
1. **NOTIFY(4)**: real divergence vs unbound (REFUSED vs black-hole).
2. **Internal inconsistency**: veri-dns answers NOTIMP for opcodes 1/2 but
   black-holes 3-7, and its own comment at `Impl/Server.lean:107-114` promises
   decodable-but-unsupported queries "still receive a proper
   FORMERR/NOTIMPL/REFUSED". Opcodes 3-7 are legal wire values (RFC 6895 §2.2),
   not malformed packets; they are classed undecodable only because
   `Spec.Opcode` cannot represent them.
3. The **010b FORMERR fix does not reach this path**: `rawDatagramReply`
   (Server.lean:124) itself calls `Header.decode`, which routes opcode through
   `Opcode.ofBV4` → `Opcode.ofCode` (Spec/Header.lean:19-24, only 0/1/2
   representable) → parse error → the "header undecodable" drop branch.

Severity is therefore **lower** than the retracted note implied: one opcode of
real divergence plus an internal-consistency/coverage gap, not a blanket
regression against the reference.
