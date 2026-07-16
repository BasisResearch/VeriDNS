# 009 — Question-name parser accepts a compression pointer into the 12-byte header and resolves the fabricated name (unbound returns FORMERR)

- Severity: impl-bug (malformed-packet handling / RFC 1035 §4.1.4 violation)
- Component: `VeriDNS/Impl/DomainName.lean:19-30` (`decodeNameAux` pointer branch) via `VeriDNS/Impl/Question.lean:11` (`decodeName` for the question)
- Observed against the rig: veri-dns @10.53.0.2:5300 (verid ns) vs unbound @10.53.0.3:5301 (unbound ns)

## Summary

`decodeNameAux` accepts *any* backward compression pointer. The only guard is
`offset < pos` (DomainName.lean:25); there is no lower bound keeping the pointer
target out of the fixed 12-byte DNS header. When the question name of an incoming
query is the two bytes `C0 02` (a pointer to offset 2), the target `2 < 12` is
below the start of the question (offset 12), so the resolver dereferences into its
own header, re-parses header bytes as a domain name, fabricates a name, and runs a
full recursive resolution on it.

Per RFC 1035 §4.1.4 a compression pointer references "a prior occurrence of the same
name." A single-question query has no prior name occurrence, and any offset < 12
lands inside the header — so a pointer in a query question is malformed. unbound
rejects the packet with FORMERR; veri-dns resolves the garbage name.

## Reproduction

Query with qname = `C0 02` (pointer to header offset 2), QTYPE=A, QCLASS=IN:

```
cd /home/yiyun/Experiments/VeriDNS/penn-testing
./vm/ssh.sh 'ip netns exec attacker python3 -c "import socket,struct; s=socket.socket(2,2); s.settimeout(3); s.sendto(struct.pack(\">HHHHHH\",0x4242,0x0100,1,0,0,0)+b\"\\xc0\\x02\"+struct.pack(\">HH\",1,1),(\"10.53.0.2\",5300)); d,_=s.recvfrom(4096); print(len(d), d.hex())"'
```

### veri-dns (10.53.0.2:5300) — ACCEPTS, resolves fabricated name

```
99
42428183 0001 0000 0001 0000   ; id=0x4242 qr=1 rd=1 ra=1 rcode=3(NXDOMAIN) QD=1 AN=0 NS=1 AR=0
00 0001 0001                    ; echoed question: qname='.' (root), A, IN
00 0006 0001 00000e04 0045 ...  ; authority: root SOA
  a.root-servers.net. hostmaster.root-servers.net. ...
```

The pointer was dereferenced into the header, a name was fabricated, and the
resolver ran a recursive lookup that bottomed out at the root and returned the
root SOA in the authority section (NXDOMAIN).

### unbound (10.53.0.3:5301) — REJECTS

```
12
42428101 0000 0000 0000 0000    ; id=0x4242 qr=1 rcode=1(FORMERR) QD=0
```

Exact one-line A/B (matches the reported observation):

```
verid   -> 99 42428183   (NXDOMAIN, QD=1, root SOA in authority)
unbound -> 12 42428101   (FORMERR, QD=0)
```

## Root cause

`VeriDNS/Impl/DomainName.lean:25`:

```lean
if offset < pos then
  ...accept and recurse to decodeNameAux buf offset ...
else .error "domain name: forward or self compression pointer (RFC 1035 §4.1.4)"
```

The guard rejects forward/self pointers but not pointers whose target lies inside
the header (or, more generally, before the position where the name being decoded
began). For a query, the question name starts at offset 12, so any accepted pointer
with `offset < 12` re-interprets header octets as name labels.

## Fix direction

When decoding the question name of a query, a compression pointer should be
rejected outright (a query question has no prior name to point at). More generally,
a pointer target must reference the start of an earlier name already seen in the
message, and must never be `< 12` (inside the header). Threading the name's own
start offset and refusing `offset < headerLen` (or `offset >= nameStart`) closes
this.

## RFC / reference

- RFC 1035 §4.1.4: a pointer is "a prior occurrence of the same name"; the 12-byte
  header is not a name and a single-question query has no prior name.
- unbound treats a query question carrying a compression pointer as malformed and
  answers FORMERR (rcode 1), as reproduced above.

## Regression re-verification (2026-07-15, post-remediation commit 26b5849)

**FIXED — verified on the rig.** `Impl/DomainName.lean:30` now guards
`if 12 ≤ offset ∧ offset < pos`, rejecting pointers into the 12-byte header as
well as forward/self pointers. The original wire repro no longer reproduces.
Renumbered rig, both resolvers restarted:

```
ptr009b       (qname = C0 02, ptr -> header offset 2)
  verid   203.0.113.2:5300  len=12 id=0x4242 qr=1 rd=1 ra=1 rcode=1 QD=0 AN=0 NS=0 AR=0
                            hex=424281810000000000000000
  unbound 203.0.113.3:5301  len=12 id=0x4242 qr=1 rd=1 ra=0 rcode=1 QD=0 AN=0 NS=0 AR=0
                            hex=424281010000000000000000
ptr009b_off0  (C0 00)  verid: FORMERR QD=0 12B   unbound: FORMERR QD=0 12B
ptr009b_off11 (C0 0B, last header byte)
                       verid: FORMERR QD=0 12B   unbound: FORMERR QD=0 12B
cptrloop      (C0 0C, self)
                       verid: FORMERR QD=0 12B   unbound: FORMERR QD=0 12B
good          (control) verid: NOERROR QD=1 AN=1 -> host.example.test A 203.0.113.101
```

The old behaviour (99-byte NXDOMAIN, QD=1, fabricated root name, root SOA in
authority, full recursion run) is gone: veri-dns now returns a 12-byte FORMERR
and **matches unbound's rcode and QD=0**. The boundary case `C0 0B` (offset 11,
the last header byte) is correctly rejected, so the `12 ≤ offset` bound is
exact, and the positive control still resolves — the guard did not over-reject.

Residual nit (not this finding): veri-dns's FORMERR carries `ra=1` where
unbound sends `ra=0`. That is the error-flag-hygiene class tracked by finding
033, not a regression of 009b.

**Fix quality:** the remediation plan states the guard was tightened in place
with "**zero proof diff**" — i.e. no theorem constrains `12 ≤ offset`. Reverting
that one conjunct would build green; only the `headerPointerRejected` /
`compressionStillAccepted` unit tests stand behind it. Correct at runtime but
**unpinned** — a coverage-gap that can silently regress.
