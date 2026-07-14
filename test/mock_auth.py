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
}

SLOW = {dns.name.from_text("slow.veridns."), dns.name.from_text("slow2.veridns.")}
SLOW_DELAY = 1.5

FORCE_TC = {dns.name.from_text("forcetc.veridns.")}

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


def build_response(query):
    resp = dns.message.make_response(query)
    q = query.question[0]
    qname, qtype = q.name, q.rdtype

    zone = owning_zone(qname)
    if zone is None:
        resp.set_rcode(dns.rcode.REFUSED)
        return resp

    resp.flags |= dns.flags.AA
    ans = rrset_for(qname, qtype)
    if ans is not None:
        resp.answer.append(ans)
        if qtype == dns.rdatatype.NS:
            for rd in ans:
                tgt = rd.target
                glue = rrset_for(tgt, dns.rdatatype.A)
                if glue is not None:
                    resp.additional.append(glue)
        return resp

    if qname not in RECORDS and not is_empty_nonterminal(qname):
        resp.set_rcode(dns.rcode.NXDOMAIN)
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


class UDPHandler(socketserver.BaseRequestHandler):
    def handle(self):
        data, sock = self.request
        out = handle(data, "udp")
        if out is not None:
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
    global LOG_PATH
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=5354)
    ap.add_argument("--log", default=None)
    ap.add_argument("--no-tcp", action="store_true",
                    help="serve UDP only (negative control: TCP listener down)")
    args = ap.parse_args()
    LOG_PATH = args.log

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
