# 042 - Standard query carrying non-empty ANSWER/AUTHORITY/ADDITIONAL sections is resolved (NOERROR) instead of rejected (FORMERR)

- **Component:** `VeriDNS/Impl/Server.lean` (Message.decode -> rawDatagramReply path),
  `VeriDNS/Impl/Message.lean` (`decodeRRCanonical` parses every declared section of the
  request), `VeriDNS/Impl/Question.lean` (only the question is consumed for resolution).
- **Class:** impl-bug (robustness / RFC-compliance divergence). **Not** a cache-poisoning
  vector -- the query-borne record is never ingested.
- **Severity:** low. Behavioral divergence from unbound and from RFC 1035 robustness
  expectations; no integrity impact observed.

## Claim

An OPCODE=0 (standard query) message whose ANCOUNT/NSCOUNT/ARCOUNT are > 0 should have
empty answer/authority/additional sections (RFC 1035 4.1.2). unbound treats a query with a
non-empty answer section as malformed and returns FORMERR. veri-dns instead parses the
whole request, ignores the extra records, resolves the question, and returns a normal
NOERROR answer.

## Reproduction (live rig)

Rig per `review/ENV.md`: veri-dns @10.53.0.2:5300 (netns `verid`), unbound @10.53.0.3:5301
(netns `unbound`), attacker vantage netns `attacker`. Script `_vmdns/rawq.py` builds a
standard query for `host.example.test A` with QDCOUNT=1 **and** ANCOUNT=1, riding an
injected `A 6.6.6.6` record (compression-pointer owner `c00c`) in the request's answer
section.

```
$ penn-testing/vm/ssh.sh 'ip netns exec attacker python3 /root/dev/_vmdns/rawq.py 10.53.0.2 5300'
=== query-with-ANCOUNT1-inject ===
  R: len=68 id=8738 qr=1 op=0 rcode=0 tc=0 QD=1 AN=1 NS=0 AR=0
    hex=22228180000100010000000004686f7374076578616d706c650474657374000001000104686f7374076578616d706c650474657374000001000100000daf0004...

$ penn-testing/vm/ssh.sh 'ip netns exec attacker python3 /root/dev/_vmdns/rawq.py 10.53.0.3 5301'
=== query-with-ANCOUNT1-inject ===
  R: len=12 id=8738 qr=1 op=0 rcode=1 tc=0 QD=0 AN=0 NS=0 AR=0   (FORMERR)
```

- **veri-dns:** rcode=0 (NOERROR), QD=1 AN=1. The answer owner is re-emitted **in full**
  (`04686f7374076578616d706c650474657374...` = host.example.test) rather than as the
  request's `c00c` pointer -- i.e. the answer was produced by veri-dns's own
  resolution/cache, and the rdata is the legitimate `10.53.0.101` (confirmed by
  `dig @10.53.0.2 -p 5300 host.example.test A +short` -> `10.53.0.101`), **not** the
  injected `6.6.6.6`.
- **unbound:** rcode=1 (FORMERR), QD=0 AN=0.

## Non-ingestion (no poisoning)

```
$ penn-testing/vm/ssh.sh 'ip netns exec attacker python3 /root/dev/_vmdns/qinject.py 10.53.0.2 5300 freshinj.example.test'
reply rcode=3 AN=0 ...                              # NXDOMAIN, injected record ignored

$ penn-testing/vm/ssh.sh 'ip netns exec attacker dig @10.53.0.2 -p 5300 freshinj.example.test A'
;; ->>HEADER<<- opcode: QUERY, status: NXDOMAIN     # still NXDOMAIN afterwards -- not poisoned
```

The query-borne `A 6.6.6.6` for a fresh name is never cached; the name still resolves to
NXDOMAIN. So the decoder parses and then discards the extra sections -- it does not treat
them as answers to store.

## Secondary observation (separate known silent-drop class)

Cases where the extra section is DECLARED but the body is absent/unparseable diverge the
other way (whole-message decode fails -> veri-dns silently drops; unbound answers FORMERR):

```
=== truncated-question ===   VERID: NO REPLY (timeout)   UNBOUND: rcode=1 FORMERR
=== qd2-but-one ===          VERID: NO REPLY (timeout)   UNBOUND: rcode=1 FORMERR
```

This is the already-catalogued silent-drop-vs-FORMERR class (findings 010, 017) and is not
the subject of this finding.

## RFC / reference

- RFC 1035 4.1.2: "the answer, authority, and additional sections ... are empty in a query."
  A standard query MUST NOT carry answer/authority/additional records.
- unbound rejects such a query with FORMERR (rcode=1, QD=0), as reproduced above.

veri-dns's decoder (`decodeRRCanonical` in `VeriDNS/Impl/Message.lean`) parses all declared
sections of the request but never validates that ANCOUNT/NSCOUNT/ARCOUNT are zero for an
OPCODE=0 query; if the trailing records happen to parse, `Server.lean` proceeds to resolve
the question and reply NOERROR.

## Verdict

**CONFIRMED** (impl-bug, low severity, no poisoning). veri-dns answers a malformed standard
query NOERROR where unbound answers FORMERR; the injected record is not ingested.
