#!/usr/bin/env python3
"""Broken-ENT leaf responder for example.test on 203.0.113.12:53 (auth ns).

Models a LEGACY/broken authoritative server that returns NXDOMAIN for an
empty non-terminal (ENT) instead of the RFC-2308-correct NOERROR/NODATA.

Zone facts we serve authoritatively (aa=1):
  example.test.            A     203.0.113.100          (apex, positive)
  example.test.            SOA   ...                     (for negative authority)
  example.test.            NS    ns.example.test.
  bar.foo.example.test.    TXT   "it-exists"            (a name that EXISTS)

The intermediate empty non-terminal `foo.example.test` HAS a child
(bar.foo.example.test) so it genuinely exists in the tree, but this broken
server answers NXDOMAIN for it (any type) -- the classic case RFC 9156 warns
about and unbound tolerates by dropping minimisation.

Everything else under example.test -> NXDOMAIN.

Run inside 'auth' ns after stopping nsd-leaf:
    ip netns exec auth python3 brokenent_responder.py
"""
import socket, struct, sys

BIND = ("203.0.113.12", 53)

SOA_MNAME = "ns.example.test"
SOA_RNAME = "hostmaster.example.test"

def encode_name(name):
    out = b""
    for label in name.rstrip(".").split("."):
        if label == "":
            continue
        out += bytes([len(label)]) + label.encode()
    return out + b"\x00"

def parse_question(pkt):
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

def soa_rdata():
    return (encode_name(SOA_MNAME) + encode_name(SOA_RNAME)
            + struct.pack(">IIIII", 1, 3600, 900, 604800, 3600))

def soa_rr(owner="example.test"):
    rd = soa_rdata()
    return encode_name(owner) + struct.pack(">HHIH", 6, 1, 3600, len(rd)) + rd

def main():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(BIND)
    print(f"brokenent_responder listening on {BIND}", flush=True)
    while True:
        pkt, addr = s.recvfrom(4096)
        txid = struct.unpack(">H", pkt[:2])[0]
        try:
            qname, qtype, qclass, qend = parse_question(pkt)
        except Exception as e:
            print("parse error", e, flush=True)
            continue
        question = pkt[12:qend]
        qn = qname.lower().rstrip(".")
        print(f"query from {addr}: {qn} type={qtype} txid={txid:#06x}", flush=True)

        AA = 1 << 10
        QR = 1 << 15

        if qn == "example.test" and qtype == 1:  # apex A
            flags = QR | AA
            rr = encode_name("example.test") + struct.pack(">HHIH", 1, 1, 3600, 4) + socket.inet_aton("203.0.113.100")
            resp = struct.pack(">HH", txid, flags) + struct.pack(">HHHH", 1, 1, 0, 0) + question + rr
            print("  -> NOERROR example.test A 203.0.113.100", flush=True)

        elif qn == "example.test" and qtype in (2, 6):  # NS or SOA at apex
            flags = QR | AA
            if qtype == 6:
                rr = soa_rr("example.test")
            else:
                nsrd = encode_name("ns.example.test")
                rr = encode_name("example.test") + struct.pack(">HHIH", 2, 1, 3600, len(nsrd)) + nsrd
            resp = struct.pack(">HH", txid, flags) + struct.pack(">HHHH", 1, 1, 0, 0) + question + rr
            print(f"  -> NOERROR example.test type={qtype}", flush=True)

        elif qn == "bar.foo.example.test" and qtype == 16:  # the EXISTING deep name, TXT
            flags = QR | AA
            txt = b"\x09it-exists"  # 1-byte len prefix + "it-exists"
            rr = encode_name("bar.foo.example.test") + struct.pack(">HHIH", 16, 1, 3600, len(txt)) + txt
            resp = struct.pack(">HH", txid, flags) + struct.pack(">HHHH", 1, 1, 0, 0) + question + rr
            print("  -> NOERROR bar.foo.example.test TXT 'it-exists'", flush=True)

        elif qn == "bar.foo.example.test":  # exists but other type -> NODATA
            flags = QR | AA
            auth = soa_rr("example.test")
            resp = struct.pack(">HH", txid, flags) + struct.pack(">HHHH", 1, 0, 1, 0) + question + auth
            print("  -> NODATA bar.foo.example.test", flush=True)

        else:
            # BROKEN: NXDOMAIN for everything else, including the ENT foo.example.test
            flags = QR | AA | 3  # rcode=3 NXDOMAIN
            auth = soa_rr("example.test")
            resp = struct.pack(">HH", txid, flags) + struct.pack(">HHHH", 1, 0, 1, 0) + question + auth
            print(f"  -> NXDOMAIN {qn} type={qtype}", flush=True)

        s.sendto(resp, addr)

if __name__ == "__main__":
    sys.exit(main())
