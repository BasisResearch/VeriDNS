# 033 - Multi-question (QDCOUNT=2) FORMERR echoes both questions with QD=2 and ra=1

- **Component:** `VeriDNS/Impl/Server.lean` — `buildResponse` / `buildErrorResponse` / `finalizeForClient`, reached from the `queryProblem` FORMERR path.
- **Class:** coverage-gap (benign wire-format differential; error replies are not normalized)
- **Severity:** low. RCODE agrees with unbound (both FORMERR); reply length <= request length (no amplification). Purely a wire-format / section-hygiene divergence.
- **Status:** CONFIRMED on the rig (differential vs unbound).

## Summary

A query carrying two questions (`QDCOUNT=2`) is rejected as FORMERR by both
resolvers, but they build the error reply very differently:

- **veri-dns** returns `qr=1 rd=1 ra=1 RCODE=1 (FORMERR) QD=2 AN=0 NS=0 AR=0`
  and echoes **both** question RRs verbatim in the body.
- **unbound** returns `qr=1 rd=1 ra=0 RCODE=1 (FORMERR) QD=0 AN=0 NS=0 AR=0`
  with an empty body (12-byte header only).

veri-dns's error reply is built directly from the raw client header, so it
retains `QDCOUNT=2` and the original two questions, and the client-finalize step
unconditionally sets `ra=1` — even on a request the server refused to interpret.

## Reproduction (on the rig)

Packet: txid `0x2222`, flags `0x0100` (rd=1), `QDCOUNT=2`, questions
`host.example.test/A/IN` + `www.example.test/A/IN`.
Wire: `22220100 0002 0000 0000 0000  04686f7374076578616d706c650474657374 000001 0001  03777777076578616d706c6504746573740000010001`

Sender/parser: `penn-testing/_vmdns/qd2.py` (built for this test).

```
# veri-dns @10.53.0.2:5300
$ ip netns exec attacker python3 /root/dev/_vmdns/qd2.py 10.53.0.2 5300 host.example.test www.example.test
resp txid=0x2222 qr=1 opcode=0 aa=0 tc=0 rd=1 ra=1 rcode=1 QD=2 AN=0 NS=0 AR=0
wire: 22228181 0002 0000 0000 0000 04686f7374076578616d706c650474657374000001000103777777076578616d706c6504746573740000010001
len: 57

# unbound @10.53.0.3:5301  (same query bytes)
resp txid=0x2222 qr=1 opcode=0 aa=0 tc=0 rd=1 ra=0 rcode=1 QD=0 AN=0 NS=0 AR=0
wire: 22228101 0000 0000 0000 0000
len: 12
```

Control (single-question, same rig) is answered normally:
`qr=1 rd=1 ra=1 rcode=0 QD=1 AN=1` — so the divergence is specific to the
multi-question FORMERR path, not a general flag bug. A QD=2 with the *same*
name twice reproduces identically (QD=2 echoed, ra=1).

## Root cause

`VeriDNS/Impl/Server.lean`:

```lean
def buildResponse (query : Format) (rcode : Rcode)
    (answers authority additional : Array ByteArray) : Format :=
  { header := { query.header with            -- keeps query.header.qdcount (=2) unchanged
      qr := 1, rcode := rcode
      ancount := ..., nscount := ..., arcount := ... }   -- QD not touched
    question := query.question                -- echoes ALL questions verbatim
    ... }

def buildErrorResponse (query : Format) (rcode : Rcode) : Format :=
  buildResponse query rcode #[] #[] #[]

def finalizeForClient (resp : Format) : Format :=
  { resp with header := { resp.header with qr := 1, ra := 1, aa := 0, z := 0 } }  -- ra:=1 unconditionally
```

`buildResponse` overrides `ancount/nscount/arcount` but leaves `qdcount` at the
client's value, and copies `query.question` wholesale. `finalizeForClient` then
sets `ra=1` even for a query the server declined to interpret. The FORMERR reply
is therefore never normalized to a minimal form.

## Reference / expected behaviour

- **unbound** (reference resolver on the same rig) normalizes the error reply:
  `QDCOUNT=0`, no question echo, `ra=0`.
- **RFC 1035 §4.1.1**: `QDCOUNT` is the number of entries actually present in the
  question section; leaving it at 2 while unbound emits 0 is the observable
  differential. Setting `RA` on a request that was rejected as unparsable
  ("recursion available") is misleading, though not a hard MUST violation.

## Impact

Functionally benign: both resolvers signal FORMERR, and the veri-dns reply is
never larger than the request (no amplification vector). This is the same class
of error-path section/flag hygiene divergence as findings 007 (rd echo),
010/017 (undecodable-drop), and 032 (client TC reflected): veri-dns's error
responses are assembled from the raw client packet rather than emitted as a
minimal normalized error.
