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
