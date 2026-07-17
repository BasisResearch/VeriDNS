#!/usr/bin/env python3
"""
mock_auth.py — hermetic mock authoritative nameserver for the TCP stage-U
differential test (docs/tcp-plan.md §U6).

Serves a tiny collapsed delegation (root `.` + a `veridns.` zone) on a single
loopback UDP+TCP port, so both veri-dns (root-hint-redirected to us) and a
reference unbound (forward-zone `.` pointing at us) resolve the whole tree
against this one process. It is deliberately authoritative for BOTH the root
and the `veridns.` zone from the same socket: a resolver's queries all arrive
here, and longest-zone matching answers each authoritatively (the delegation
collapses — delegation *depth* is covered by the live corpus, not by U6; what
U6 exercises is the UDP-truncation → TCP-retry fallback).

Truncation policy (the whole point):
  * UDP: build the full reply; if its wire length exceeds the requester's
    advertised EDNS UDP size (or 512 with no OPT), OR the owner is a
    force-TC name, set TC=1 and send a header-only truncated reply (RFC 1035
    §4.1.1) — exactly what a real authoritative server does.
  * TCP: always send the full reply (no truncation).

Every query is appended to --log as one JSON line
  {"transport": "udp"|"tcp", "qname": ..., "qtype": ..., "tc": 0|1}
so the rig can assert the decision logic (a UDP TC reply followed by a TCP
retry for the SAME qname/qtype) without needing a packet sniffer.
"""
import argparse
import json
import socket
import socketserver
import struct
import sys
import threading
import time

import dns.message
import dns.name
import dns.rrset
import dns.rdatatype
import dns.rcode
import dns.flags


BIG_TXT = ["veri-dns-tcp-fallback-oversized-rrset-marker-%03d" % i for i in range(40)]

# 060c repro: a ~24 KB RRset of 300 individual TXT records. Reply assembly
# must stay well under 100 ms (the old scrub path was ~quartic in the record
# count and span seconds of CPU on this shape).
HUGE_TXT = ["veri-dns-large-rrset-060c-%03d-" % i + "x" * 40 for i in range(300)]

ROOT = dns.name.root
A_ROOT = dns.name.from_text("a.root-servers.net.")

RECORDS = {
    ROOT: [
        (dns.rdatatype.NS, ["a.root-servers.net."]),
    ],
    A_ROOT: [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
    dns.name.from_text("big.veridns."): [
        (dns.rdatatype.TXT, [" ".join('"%s"' % s for s in BIG_TXT)]),
    ],
    dns.name.from_text("huge.veridns."): [
        (dns.rdatatype.TXT, ['"%s"' % s for s in HUGE_TXT]),
    ],
    dns.name.from_text("forcetc.veridns."): [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
    dns.name.from_text("small.veridns."): [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
    dns.name.from_text("slow.veridns."): [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
    dns.name.from_text("slow2.veridns."): [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
    # --- adversarial injection corpus (docs/model-strengthening-plan.md W5) ---
    # New owners, unused by the TCP rigs, that carry a legitimate answer alongside
    # an off-entitlement rider so the differential rig can assert veri-dns delivers
    # and caches only what the query is entitled to (W1 Entitled family).
    dns.name.from_text("rider.veridns."): [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
    dns.name.from_text("poison.veridns."): [
        (dns.rdatatype.A, ["127.0.0.1"]),
    ],
}

SLOW = {dns.name.from_text("slow.veridns."), dns.name.from_text("slow2.veridns.")}
SLOW_DELAY = 1.5

FORCE_TC = {dns.name.from_text("forcetc.veridns.")}

# --- poison owners and their off-entitlement riders (see build_response) ---
RIDER = dns.name.from_text("rider.veridns.")
RIDER_PIGGY = dns.name.from_text("piggyback.rider.veridns.")   # 004: subdomain rider on the answer
POISON = dns.name.from_text("poison.veridns.")
POISON_TARGET = dns.name.from_text("bankofsteal.veridns.")     # Kaminsky: unsolicited ADDITIONAL glue
ALIAS = dns.name.from_text("alias.veridns.")
ALIAS_OFFOWNER = dns.name.from_text("evil.veridns.")           # 036: off-owner CNAME owner (!= qname)
ALIAS_TARGET = dns.name.from_text("landing.veridns.")
GHOST = dns.name.from_text("ghost.veridns.")                   # 012/013: NXDOMAIN carrier
FOREIGN_SOA_OWNER = dns.name.from_text("evil.example.")        # SOA owner NOT an ancestor of ghost.veridns
FOREIGN_SOA = "ns.evil.example. hostmaster.evil.example. 1 3600 600 86400 3600"

ZONES = [ROOT]
SOA_BY_ZONE = {
    ROOT: ("a.root-servers.net. nstld. 1 3600 600 86400 3600"),
}
TTL = 3600


def is_empty_nonterminal(qname):
    """True if qname owns no records but is a strict ancestor of one that does —
    an empty non-terminal, which must answer NODATA (NOERROR), not NXDOMAIN, so a
    qname-minimising resolver keeps descending (RFC 8020)."""
    return any(owner != qname and owner.is_subdomain(qname) for owner in RECORDS)

LOG_LOCK = threading.Lock()
LOG_PATH = None


def log_query(transport, qname, qtype, tc):
    if LOG_PATH is None:
        return
    line = json.dumps({
        "transport": transport,
        "qname": qname.to_text(),
        "qtype": dns.rdatatype.to_text(qtype),
        "tc": tc,
    })
    with LOG_LOCK:
        with open(LOG_PATH, "a") as f:
            f.write(line + "\n")


def owning_zone(qname):
    for z in ZONES:
        if qname == z or qname.is_subdomain(z):
            return z
    return None


def rrset_for(owner, rdtype):
    for (t, rdatas) in RECORDS.get(owner, []):
        if t == rdtype:
            rr = dns.rrset.from_text_list(owner, TTL, dns.rdataclass.IN, rdtype, rdatas)
            return rr
    return None


def all_rrsets_for(owner):
    out = []
    for (t, rdatas) in RECORDS.get(owner, []):
        out.append(dns.rrset.from_text_list(owner, TTL, dns.rdataclass.IN, t, rdatas))
    return out


def build_response(query):
    resp = dns.message.make_response(query)
    q = query.question[0]
    qname, qtype, qclass = q.name, q.rdtype, q.rdclass

    # A real authoritative nameserver refuses classes it is not authoritative for.
    # veri-dns and unbound must agree on how a CHAOS/HESIOD query is handled (W5 corpus).
    if qclass != dns.rdataclass.IN:
        resp.set_rcode(dns.rcode.REFUSED)
        return resp

    zone = owning_zone(qname)
    if zone is None:
        resp.set_rcode(dns.rcode.REFUSED)
        return resp

    resp.flags |= dns.flags.AA

    # 036 — off-owner CNAME: reply to alias.veridns with a CNAME whose OWNER is
    # evil.veridns (not the qname) plus the target's A. Entitlement says the CNAME
    # is not on the chain rooted at the qname, so a correct resolver must not chase it.
    if qname == ALIAS:
        cname = dns.rrset.from_text(ALIAS_OFFOWNER, TTL, dns.rdataclass.IN,
                                    dns.rdatatype.CNAME, ALIAS_TARGET.to_text())
        tgt_a = dns.rrset.from_text(ALIAS_TARGET, TTL, dns.rdataclass.IN,
                                    dns.rdatatype.A, "8.8.8.8")
        resp.answer.append(cname)
        resp.answer.append(tgt_a)
        return resp

    # qtype=ANY (RFC 8482 is out of scope here): return every RRset we own for the
    # owner, exactly what a naive authoritative server does. Locks veri-vs-unbound parity.
    if qtype == dns.rdatatype.ANY:
        rrsets = all_rrsets_for(qname)
        if rrsets:
            for rr in rrsets:
                resp.answer.append(rr)
            return resp
        # fall through to the negative path below

    ans = rrset_for(qname, qtype)
    if ans is not None:
        resp.answer.append(ans)
        if qtype == dns.rdatatype.NS:
            for rd in ans:
                tgt = rd.target
                glue = rrset_for(tgt, dns.rdatatype.A)
                if glue is not None:
                    resp.additional.append(glue)
        # 004 — subdomain rider: piggyback an extra in-bailiwick A (owner is a
        # strict subdomain of the qname) onto the legitimate answer section.
        if qname == RIDER:
            resp.answer.append(dns.rrset.from_text(
                RIDER_PIGGY, TTL, dns.rdataclass.IN, dns.rdatatype.A, "6.6.6.6"))
        # Kaminsky — unsolicited ADDITIONAL: attach a spoofed A for an unrelated
        # name so the rig can check it is never promoted into the answer cache.
        if qname == POISON:
            resp.additional.append(dns.rrset.from_text(
                POISON_TARGET, TTL, dns.rdataclass.IN, dns.rdatatype.A, "6.6.6.6"))
        return resp

    if qname not in RECORDS and not is_empty_nonterminal(qname):
        resp.set_rcode(dns.rcode.NXDOMAIN)

    # 012/013 — off-owner SOA: for ghost.veridns answer NXDOMAIN with a negative
    # SOA whose owner (evil.example.) is NOT an ancestor of the queried name.
    if qname == GHOST:
        resp.authority.append(dns.rrset.from_text(
            FOREIGN_SOA_OWNER, TTL, dns.rdataclass.IN, dns.rdatatype.SOA, FOREIGN_SOA))
        return resp

    soa = dns.rrset.from_text(zone, TTL, dns.rdataclass.IN, dns.rdatatype.SOA, SOA_BY_ZONE[zone])
    resp.authority.append(soa)
    return resp


def udp_limit(query):
    opt = query.opt
    if opt is not None:
        return max(512, query.payload)
    return 512


def handle(data, transport):
    try:
        query = dns.message.from_wire(data)
    except Exception:
        return None
    if not query.question:
        return None
    q = query.question[0]
    if q.name in SLOW:
        time.sleep(SLOW_DELAY)
    resp = build_response(query)

    wire = resp.to_wire(max_size=65535)
    tc = 0
    if transport == "udp":
        force = q.name in FORCE_TC
        if force or len(wire) > udp_limit(query):
            tc = 1
            resp.answer = []
            resp.authority = []
            resp.additional = []
            resp.flags |= dns.flags.TC
            wire = resp.to_wire(max_size=65535)
    log_query(transport, q.name, q.rdtype, tc)
    return wire


INJECT_JUNK = False


def junk_datagram(query):
    """A datagram that is byte-junk for the query: a well-formed-looking DNS
    header echoing the transaction id but carrying a DIFFERENT question, so it
    fails the resolver's id+question match. Modelled on finding 017's repro:
    junk that arrives from the LEGITIMATE source:port before the real reply."""
    try:
        q = dns.message.from_wire(query)
        txid = q.id
    except Exception:
        txid = 0
    # header: id, flags QR=1, qd=1, an=ns=ar=0
    hdr = struct.pack("!HHHHHH", txid, 0x8180, 1, 0, 0, 0)
    # question: bad.invalid. A IN  (never the queried name)
    qsec = b"\x03bad\x07invalid\x00" + struct.pack("!HH", 1, 1)
    return hdr + qsec


class UDPHandler(socketserver.BaseRequestHandler):
    def handle(self):
        data, sock = self.request
        out = handle(data, "udp")
        if out is not None:
            if INJECT_JUNK:
                # Finding 017: emit junk from THIS (legitimate) socket first, so
                # the client sees it from the expected source:port before the
                # genuine reply. A read-until-match resolver must skip it.
                try:
                    sock.sendto(junk_datagram(data), self.client_address)
                    sock.sendto(junk_datagram(data), self.client_address)
                except Exception:
                    pass
            sock.sendto(out, self.client_address)


class TCPHandler(socketserver.BaseRequestHandler):
    def handle(self):
        hdr = self._recvn(2)
        if hdr is None:
            return
        (mlen,) = struct.unpack("!H", hdr)
        body = self._recvn(mlen)
        if body is None:
            return
        out = handle(body, "tcp")
        if out is not None:
            self.request.sendall(struct.pack("!H", len(out)) + out)

    def _recvn(self, n):
        buf = b""
        while len(buf) < n:
            chunk = self.request.recv(n - len(buf))
            if not chunk:
                return None
            buf += chunk
        return buf


class ThreadingUDP(socketserver.ThreadingMixIn, socketserver.UDPServer):
    allow_reuse_address = True


class ThreadingTCP(socketserver.ThreadingMixIn, socketserver.TCPServer):
    allow_reuse_address = True


def main():
    global LOG_PATH, INJECT_JUNK
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=5354)
    ap.add_argument("--log", default=None)
    ap.add_argument("--no-tcp", action="store_true",
                    help="serve UDP only (negative control: TCP listener down)")
    ap.add_argument("--inject-junk", action="store_true",
                    help="finding 017: emit two junk datagrams from the "
                         "legitimate source:port before each real UDP reply")
    args = ap.parse_args()
    LOG_PATH = args.log
    INJECT_JUNK = args.inject_junk

    udp = ThreadingUDP((args.host, args.port), UDPHandler)
    threading.Thread(target=udp.serve_forever, daemon=True).start()
    sys.stderr.write("mock_auth: UDP %s:%d\n" % (args.host, args.port))

    if not args.no_tcp:
        tcp = ThreadingTCP((args.host, args.port), TCPHandler)
        threading.Thread(target=tcp.serve_forever, daemon=True).start()
        sys.stderr.write("mock_auth: TCP %s:%d\n" % (args.host, args.port))
    else:
        sys.stderr.write("mock_auth: TCP DISABLED (--no-tcp)\n")
    sys.stderr.flush()

    threading.Event().wait()


if __name__ == "__main__":
    main()
