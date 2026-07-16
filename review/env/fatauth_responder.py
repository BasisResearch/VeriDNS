#!/usr/bin/env python3
"""Fat-authority leaf responder: answers `example.test A` with a positive,
authoritative (aa=1) answer of ONE A record, PLUS a large apex-NS AUTHORITY
section, all name-compressed so the wire datagram fits under 512 (no TC).
Models a non-minimal authoritative server (BIND default) that includes the
apex NS RRset in a positive answer's authority.

Binds 203.0.113.12:53 (the leaf-NS address veri-dns/unbound reach via referral).
Run inside the 'auth' namespace after stopping nsd-leaf:
    ip netns exec auth python3 fatauth_responder.py [--count N] [--pad K]
"""
import socket, struct, sys, argparse

def qname_end(pkt, off):
    while True:
        l = pkt[off]
        if l == 0:
            return off + 1
        if l & 0xC0:
            return off + 2
        off += 1 + l

def enc_name_compressed(first_label, suffix_ptr):
    # first_label bytes then a compression pointer to example.test
    return bytes([len(first_label)]) + first_label.encode() + struct.pack(">H", suffix_ptr)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=13, help="number of NS records in authority")
    ap.add_argument("--pad", type=int, default=18, help="label length for each NS target")
    ap.add_argument("--answer-ip", default="203.0.113.100")
    ap.add_argument("--bind", default="203.0.113.12")
    a = ap.parse_args()

    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind((a.bind, 53))
    sys.stderr.write(f"fatauth bound {a.bind}:53 count={a.count} pad={a.pad}\n")
    sys.stderr.flush()

    while True:
        req, addr = s.recvfrom(4096)
        if len(req) < 12:
            continue
        txid = req[0:2]
        qend = qname_end(req, 12)
        qsection = req[12:qend + 4]          # qname + qtype(2) + qclass(2)

        # question qname sits at offset 12; example.test suffix = 0xC00C
        SUF = 0xC00C
        flags = (1 << 15) | (1 << 10)        # qr=1, aa=1
        ancount = 1
        nscount = a.count
        header = txid + struct.pack(">HHHHH", flags, 1, ancount, nscount, 0)

        # ANSWER: example.test A 203.0.113.100 (owner = ptr to question name)
        answer = (struct.pack(">H", SUF)
                  + struct.pack(">HHIH", 1, 1, 3600, 4)
                  + socket.inet_aton(a.answer_ip))

        # AUTHORITY: N x  example.test NS  <unique-long-label>.example.test
        authority = b""
        for i in range(a.count):
            lbl = ("ns%02d" % i) + ("x" * a.pad)
            nsname = enc_name_compressed(lbl, SUF)   # compressed on the wire
            rr = (struct.pack(">H", SUF)             # owner = example.test (ptr)
                  + struct.pack(">HHIH", 2, 1, 3600, len(nsname))  # NS
                  + nsname)
            authority += rr

        resp = header + qsection + answer + authority
        s.sendto(resp, addr)
        sys.stderr.write(f"replied {addr} txid={txid.hex()} wire={len(resp)} ns={a.count}\n")
        sys.stderr.flush()

if __name__ == "__main__":
    main()
