# 044 — Meta/pseudo QTYPEs (OPT/MAILA/MAILB/AXFR/IXFR) are recursed as ordinary query types; verid emits a malformed OPT-typed query on the wire

- Status: CONFIRMED (impl-bug)
- Component: `VeriDNS/Impl/Question.lean:12` (qtype kept as a raw `BV16`, never validated) + `VeriDNS/Impl/Server.lean:91-104` (`supportsQueryKind`/`interpretableQuery`/`performsRequestedOperation`/`queryProblem` gate only opcode, question count, and RD — no QTYPE screening)
- Observed on the rig: veri-dns @10.53.0.2:5300 (netns `verid`) vs unbound @10.53.0.3:5301 (netns `unbound`)

## Summary

A recursive resolver must not treat DNS *meta* / *pseudo* RR types as answerable RR
types in the question section:

- **OPT (41)** is a pseudo-RR (RFC 6891 §6.1.1) that may only appear in the *additional*
  section; it is never a legal QTYPE. RFC 6895 §3.1 classifies it as a meta-type.
- **MAILB (253) / MAILA (254) / AXFR (252) / IXFR (251)** are "QTYPE only" request codes
  (RFC 1035 §3.2.3, RFC 6895 §3.1). MAILA/MAILB are obsolete; AXFR/IXFR are zone-transfer
  operations, not recursive lookups.

verid does **no** QTYPE screening. `Question.decode` keeps `qtype` as a raw 16-bit value,
and `queryProblem` only inspects opcode (`supportsQueryKind`), question count
(`interpretableQuery`), and the RD bit (`performsRequestedOperation`). Every meta type is
therefore recursed as if it were an ordinary RR type. Worse, for OPT/MAILA/MAILB verid
forwards the meta QTYPE **onto the wire** to the authoritative server, generating a
malformed upstream query.

## Reproduction

Meta-type screening comparison (fresh names, so no cache short-circuit):

```
$ penn-testing/vm/ssh.sh 'for qt in 41 253 254 252 251; do \
    ip netns exec attacker python3 /root/dev/_vmdns/probeq.py 10.53.0.2 5300 mc$qt-a.example.test $qt; done'
qt=41  qc=1: 123B rcode=NXDOMAIN rd=0 ra=1 aa=0 AN=0 NS=1 AR=0
qt=253 qc=1: 124B rcode=NXDOMAIN rd=0 ra=1 aa=0 AN=0 NS=1 AR=0
qt=254 qc=1: 124B rcode=NXDOMAIN rd=0 ra=1 aa=0 AN=0 NS=1 AR=0
qt=252 qc=1: 38B  rcode=SERVFAIL rd=1 ra=1 aa=0 AN=0 NS=0 AR=0
qt=251 qc=1: 38B  rcode=SERVFAIL rd=1 ra=1 aa=0 AN=0 NS=0 AR=0

$ penn-testing/vm/ssh.sh 'for qt in 41 253 254 252 251; do \
    ip netns exec attacker python3 /root/dev/_vmdns/probeq.py 10.53.0.3 5301 mc$qt-b.example.test $qt; done'
qt=41  qc=1: 37B rcode=FORMERR rd=1 ra=0 aa=0 AN=0 NS=0 AR=0
qt=253 qc=1: 38B rcode=FORMERR rd=1 ra=0 aa=0 AN=0 NS=0 AR=0
qt=254 qc=1: 38B rcode=FORMERR rd=1 ra=0 aa=0 AN=0 NS=0 AR=0
qt=252 qc=1: 38B rcode=REFUSED rd=1 ra=0 aa=0 AN=0 NS=0 AR=0
qt=251 qc=1: 38B rcode=REFUSED rd=1 ra=0 aa=0 AN=0 NS=0 AR=0
```

- verid recurses OPT/MAILB/MAILA to a full NXDOMAIN (with a SOA in the authority section,
  NS=1) — i.e. it answers a meta-type as if it were a real RR type.
- unbound rejects all five: **FORMERR** for OPT/MAILA/MAILB, **REFUSED** for AXFR/IXFR.
- On AXFR/IXFR over UDP verid returns SERVFAIL (it tried to recurse and failed) instead of
  a clean REFUSED.

### Malformed OPT egress on the wire

tcpdump on `v-verid` while a fresh QTYPE=41 query arrives:

```
$ penn-testing/vm/ssh.sh 'ip netns exec verid tcpdump -n -i v-verid -c 12 udp & \
    sleep 2; ip netns exec attacker python3 /root/dev/_vmdns/probeq.py 10.53.0.2 5300 freshopt-eg2.example.test 41; sleep 3'
14:00:05.095179 IP 10.53.0.99.39935 > 10.53.0.2.5300:  UDP, length 43
14:00:05.095941 IP 10.53.0.2.47709  > 10.53.0.12.53:   51693 OPT? freshopt-eg2.example.test. (43)
14:00:05.096279 IP 10.53.0.12.53    > 10.53.0.2.47709: 51693 NXDomain*- 0/1/0 (93)
14:00:05.096378 IP 10.53.0.2.5300   > 10.53.0.99.39935: UDP, length 129
```

The second line is verid emitting `OPT? freshopt-eg2.example.test.` — a question-section
OPT QTYPE — to the authoritative server 10.53.0.12. OPT is not a legal QTYPE; this is
malformed egress that verid should never have generated.

## Root cause

`VeriDNS/Impl/Question.lean:12`
```lean
  let qtype ← readBV16      -- raw 16-bit value, never validated as an answerable RR type
```

`VeriDNS/Impl/Server.lean:91-104`
```lean
def supportsQueryKind (q : Format) : Bool := q.header.opcode == Opcode.query
def interpretableQuery (q : Format) : Bool := q.question.size == 1
def performsRequestedOperation (q : Format) : Bool := q.header.rd == 1
def queryProblem (q : Format) : Option Rcode :=
  if !interpretableQuery q then some Rcode.formatError
  else if !supportsQueryKind q then some Rcode.notImplemented
  else if !performsRequestedOperation q then some Rcode.refused
  else none
```

`queryProblem` — the single admission gate — never inspects `question[0].qtype`. There is
no notion of "meta-type" anywhere in the impl, so OPT/MAILA/MAILB/AXFR/IXFR all flow
straight into `treeResolve`.

## Impact

1. Correctness/interop: meta QTYPEs are answered/recursed instead of being rejected
   (FORMERR for OPT/MAILA/MAILB, REFUSED for AXFR/IXFR per unbound's behavior).
2. Malformed egress: verid puts an OPT QTYPE into an upstream question, violating
   RFC 6891 — a well-behaved authoritative server may FORMERR or drop, and verid is
   emitting non-conformant traffic under its own source address.

This is distinct from the existing "no EDNS0" KB item (OPT ignored in the *additional*
section). Here OPT is the *question* QTYPE and is actively recursed.

## References

- RFC 6891 §6.1.1 — OPT is a pseudo-RR carried only in the additional section.
- RFC 6895 §3.1 — OPT(41) is a meta-type; 251-254 are "QTYPE only" request codes.
- RFC 1035 §3.2.3 — AXFR(252), MAILB(253), MAILA(254 obsolete) are QTYPE-only.
- Reference resolver: unbound returns FORMERR (OPT/MAILA/MAILB) / REFUSED (AXFR/IXFR).

## Regression re-verification (2026-07-15, post-remediation commit 26b5849)

STILL PRESENT. Re-run on renumbered rig, both resolvers restarted.
- QTYPE=41 (OPT): veri-dns recurses to NXDOMAIN (123B, NS=1 SOA); unbound
  FORMERR.
- QTYPE=253/254 (MAILB/MAILA): veri-dns NXDOMAIN; unbound FORMERR.
- QTYPE=252/251 (AXFR/IXFR): veri-dns SERVFAIL; unbound REFUSED.
Malformed OPT egress confirmed on the wire (tcpdump v-verid):
`203.0.113.2.48342 > 203.0.113.12.53: 25550 [1au] OPT? fREshoPt-EG11.exaMPle.TesT.`
— veri-dns still emits a question-section OPT QTYPE upstream (now additionally
0x20-case-randomized). `queryProblem` still screens only opcode/qcount/RD, never
`question[0].qtype`. Not in the remediation plan; unpinned, unfixed.
