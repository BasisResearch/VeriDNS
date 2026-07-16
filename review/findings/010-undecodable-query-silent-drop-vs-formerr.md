# 010 — Undecodable queries silently dropped (no reply) where unbound answers FORMERR

- **Status:** CONFIRMED (behavioural divergence; silent drop is RFC-legal)
- **Classification:** coverage-gap
- **Component under test:** veri-dns @10.53.0.2:5300 (netns `verid`)
- **Reference:** unbound @10.53.0.3:5301 (netns `unbound`)
- **Source:** `VeriDNS/Impl/Server.lean:115` (`rawDatagramReply` hardcoded `none`),
  gated at `VeriDNS/Impl/Server.lean:487-490` (`serveOne`); locked by
  `VeriDNS/Proof/Server.lean:486-487` (`rawDatagramReply_drops`).

## Summary

For several malformed query datagrams that fail `Message.decode`, veri-dns
sends **no reply at all**, while unbound returns **FORMERR (rcode=1)**. The
undecodable path in `serveOne` calls `rawDatagramReply queryBytes`, which is
defined to always return `none` (proven by `rawDatagramReply_drops`), so the
datagram is dropped silently.

This is a legal choice under RFC 1035 (a resolver may drop malformed input),
so it is **not a hard RFC violation** — but it is a clear, observable
divergence from the reference implementation, and it suppresses the malformed-
input signal that a well-behaved resolver returns.

Additionally, the source comment justifying the drop policy
(`Impl/Server.lean:107-114`) asserts that "hardened resolvers (unbound)
silently drop such datagrams." **This is empirically false** — unbound replies
FORMERR to every undecodable case tested below. The verified drop policy rests
on an incorrect premise about the reference.

## Reproduction

Rig helper `rawq.py` is staged at `/opt/dnsenv/rawq.py` inside the VM.

```
cd /home/yiyun/Experiments/VeriDNS/penn-testing
for c in trunclabel badlablen cptrloop twoq good; do
  ./vm/ssh.sh "ip netns exec attacker python3 /opt/dnsenv/rawq.py $c 10.53.0.2 5300"
  ./vm/ssh.sh "ip netns exec attacker python3 /opt/dnsenv/rawq.py $c 10.53.0.3 5301"
done
```

Output (veri-dns first, unbound second in each pair):

```
trunclabel  10.53.0.2:5300  NO REPLY (timeout)
trunclabel  10.53.0.3:5301  REPLY rcode=1(FORMERR) qd=0 an=0 ns=0 ar=0 len=12
badlablen   10.53.0.2:5300  NO REPLY (timeout)
badlablen   10.53.0.3:5301  REPLY rcode=1(FORMERR) qd=0 an=0 ns=0 ar=0 len=12
cptrloop    10.53.0.2:5300  NO REPLY (timeout)
cptrloop    10.53.0.3:5301  REPLY rcode=1(FORMERR) qd=0 an=0 ns=0 ar=0 len=12
twoq        10.53.0.2:5300  REPLY rcode=1(FORMERR) qd=2 an=0 ns=0 ar=0 len=48
twoq        10.53.0.3:5301  REPLY rcode=1(FORMERR) qd=0 an=0 ns=0 ar=0 len=12
good        10.53.0.2:5300  REPLY rcode=0(NOERROR) qd=1 an=0 ns=1 ar=0 len=116
good        10.53.0.3:5301  REPLY rcode=0(NOERROR) qd=1 an=0 ns=1 ar=0 len=80
```

Cases (from `rawq.py`):
- `trunclabel`  — label length byte says 10 but only 3 bytes follow, packet ends.
- `badlablen`   — label length byte `0x40` (reserved top-bits `01`, neither `00` label nor `11` pointer).
- `cptrloop`    — qname is a compression pointer `0xC00C` pointing at itself (loop).
- `twoq`        — QDCOUNT=2 with two well-formed questions.

### Not a resource-DoS

The self-referential compression-pointer loop does **not** hang or spin
veri-dns. After firing it, the process stays idle and answers normal queries
immediately:

```
./vm/ssh.sh "ip netns exec attacker python3 /opt/dnsenv/rawq.py cptrloop 10.53.0.2 5300"
   -> cptrloop 10.53.0.2:5300  NO REPLY (timeout)
./vm/ssh.sh "ip netns exec attacker dig +time=3 +tries=1 @10.53.0.2 -p 5300 example.test A"
   -> status: NOERROR ... Query time: 0 msec
./vm/ssh.sh "ip netns exec verid top -bn1"
   -> PID 1714 veri-dns  TIME+ 0:00.05  (50 ms total CPU over 33 min uptime)
```

So the divergence is purely a *silent drop*, not a decode-side infinite loop.

## Secondary observation — `twoq` count echo

For the QDCOUNT=2 packet, veri-dns correctly returns FORMERR but **echoes
`qd=2`** (does not zero the count and leaves 48 bytes of echoed question),
whereas unbound returns FORMERR with `qd=0` and a bare 12-byte header. RFC 1035
does not mandate zeroing counts on FORMERR, so this too is legal but divergent
and mildly information-leaking.

## Assessment

- **RFC 1035 §4.1.1 / operational practice:** replying to undecodable input can
  turn a resolver into a spoofed-source reflector and a fingerprinting oracle;
  silently dropping is a defensible hardening choice. So the *behaviour* is
  legal.
- **Divergence:** unbound answers FORMERR for these same packets, so veri-dns is
  observably less informative than its reference. Operators/monitors that expect
  FORMERR on malformed input see a timeout instead.
- **Documentation defect:** the in-source rationale claims unbound drops these
  datagrams; the experiment shows unbound replies FORMERR. The verified
  `rawDatagramReply_drops` policy is therefore justified by a false claim about
  the reference implementation.

Classified **coverage-gap** rather than impl-bug because silent drop is legal
under RFC 1035; the finding is the reference divergence plus the incorrect
design rationale, not a hard correctness violation.

## Reference

- unbound behaviour observed directly above (FORMERR rcode=1 on all three
  undecodable cases and on `twoq`).
- RFC 1035 §4.1 (message format / RCODE 1 = Format error).

## Regression re-verification (2026-07-15, post-remediation commit 26b5849)

**FIXED — verified on the rig.** `rawDatagramReply` (`Impl/Server.lean:124`) is
no longer the hardcoded `none`: it header-decodes the failed datagram and, for a
decodable **query** header (`qr == 0 && opcode == query`), emits a minimal
12-byte FORMERR with all four counts zeroed; header-undecodable / `QR=1` /
non-QUERY-opcode datagrams still drop (anti-reflection). The original silent-drop
repro no longer reproduces. Renumbered rig, both resolvers restarted:

```
trunclabel  verid 203.0.113.2:5300  len=12 rcode=1 QD=0 AN=0 NS=0 AR=0  (was: NO REPLY)
trunclabel  unbound 203.0.113.3:5301 len=12 rcode=1 QD=0
badlablen   verid   len=12 rcode=1 QD=0 AN=0 NS=0 AR=0                  (was: NO REPLY)
badlablen   unbound len=12 rcode=1 QD=0
cptrloop    verid   len=12 rcode=1 QD=0 AN=0 NS=0 AR=0                  (was: NO REPLY)
cptrloop    unbound len=12 rcode=1 QD=0
good        verid   len=68 rcode=0 QD=1 AN=1 (control, resolves normally)
```

veri-dns now reaches **unbound parity on rcode and QD=0** for every undecodable
case originally reported, and the reply is 12 bytes — never larger than the
request, so no amplification was introduced. The in-source rationale that used
to claim "hardened resolvers (unbound) silently drop such datagrams" (the
empirically false premise this finding called out) is gone along with the blanket
drop.

Residual divergence: veri-dns's FORMERR sets `ra=1`, unbound `ra=0`. Minor
error-flag hygiene, tracked under finding 033.

**Not fixed by this change (still open, separate findings):**
- `twoq` / QDCOUNT=2 still returns `QD=2` with both questions echoed and `ra=1`
  (finding **033**) — that path flows through `buildErrorResponse` /
  `finalizeForClient`, not `rawDatagramReply`, so the count-zeroing here does not
  reach it.
- Opcodes 3-7 still black-hole (finding **023**): `rawDatagramReply` calls
  `Header.decode`, which fails on an unrepresentable opcode, taking the
  header-undecodable drop branch before the FORMERR branch can fire.

**Fix quality:** genuinely **theorem-pinned**, unlike most of this batch. The
plan cites `rawDatagramReply_formerr` (pins the reply shape),
`_no_amplification`, `_headerUndecodable_drops` and `_response_drops`. The
anti-reflection policy that previously rested on a blanket `none` is now carried
by statements that would go red if the behaviour were reverted.
