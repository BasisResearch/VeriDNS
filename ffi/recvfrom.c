/*
 * UDP socket FFI for veri-dns.
 * Provides: socket creation, bind, sendto, recvfrom.
 * All addresses use a 6-byte encoding: 4-byte IPv4 (big-endian) + 2-byte port (big-endian).
 */
#include <lean/lean.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <stdlib.h>

/* ----------------------------------------------------------------
 * veri_dns_udp_socket : IO UInt32
 * Creates a UDP (AF_INET, SOCK_DGRAM) socket, returns fd.
 * C ABI: (lean_obj_arg world) → lean_obj_res
 * ---------------------------------------------------------------- */
LEAN_EXPORT lean_obj_res veri_dns_udp_socket(lean_obj_arg world) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    /* SO_REUSEADDR for quick restart */
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* ----------------------------------------------------------------
 * veri_dns_upstream_socket : IO UInt32
 * Creates a UDP socket with SO_RCVTIMEO=2s for upstream queries.
 * ---------------------------------------------------------------- */
LEAN_EXPORT lean_obj_res veri_dns_upstream_socket(lean_obj_arg world) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    struct timeval tv;
    tv.tv_sec = 2;
    tv.tv_usec = 0;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* ----------------------------------------------------------------
 * veri_dns_bind : UInt32 → UInt16 → IO Unit
 * Binds socket fd to 0.0.0.0:port.
 * C ABI: (uint32_t fd, uint16_t port, lean_obj_arg world) → lean_obj_res
 * ---------------------------------------------------------------- */
LEAN_EXPORT lean_obj_res veri_dns_bind(uint32_t fd, uint16_t port, lean_obj_arg world) {
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(port);

    if (bind((int)fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* ----------------------------------------------------------------
 * veri_dns_sendto : UInt32 → @& ByteArray → @& ByteArray → IO Unit
 * Sends data to a 6-byte encoded address.
 * C ABI: (uint32_t fd, b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) → lean_obj_res
 * ---------------------------------------------------------------- */
LEAN_EXPORT lean_obj_res veri_dns_sendto(uint32_t fd, b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) {
    size_t dataLen = lean_sarray_size(data);
    uint8_t *dataPtr = lean_sarray_cptr(data);

    /* Decode 6-byte address: bytes 0-3 = IPv4, bytes 4-5 = port (big-endian) */
    uint8_t *ap = lean_sarray_cptr(addr6);
    struct sockaddr_in dest;
    memset(&dest, 0, sizeof(dest));
    dest.sin_family = AF_INET;
    uint32_t ip = ((uint32_t)ap[0] << 24) | ((uint32_t)ap[1] << 16) |
                  ((uint32_t)ap[2] << 8)  | (uint32_t)ap[3];
    dest.sin_addr.s_addr = htonl(ip);
    dest.sin_port = htons(((uint16_t)ap[4] << 8) | (uint16_t)ap[5]);

    ssize_t n = sendto((int)fd, dataPtr, dataLen, 0,
                       (struct sockaddr *)&dest, sizeof(dest));
    if (n < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* ----------------------------------------------------------------
 * veri_dns_recvfrom : UInt32 → USize → IO (ByteArray × ByteArray)
 * Receives a UDP datagram. Returns (data, 6-byte sender address).
 * C ABI: (uint32_t fd, size_t maxBytes, lean_obj_arg world) → lean_obj_res
 * ---------------------------------------------------------------- */
LEAN_EXPORT lean_obj_res veri_dns_recvfrom(uint32_t fd, size_t maxBytes, lean_obj_arg world) {
    int i_fd = (int)fd;

    /* Allocate receive buffer */
    lean_object *buf = lean_alloc_sarray(1, 0, maxBytes);

    struct sockaddr_in sender;
    socklen_t senderLen = sizeof(sender);
    memset(&sender, 0, sizeof(sender));

    ssize_t n = recvfrom(i_fd, lean_sarray_cptr(buf), maxBytes, 0,
                         (struct sockaddr *)&sender, &senderLen);
    if (n < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            /* Timeout: return empty ByteArray + zero address (Lean handles as decode failure) */
            lean_sarray_object *arrObj = lean_to_sarray(buf);
            arrObj->m_size = 0;
            lean_object *addrBuf = lean_alloc_sarray(1, 6, 6);
            memset(lean_sarray_cptr(addrBuf), 0, 6);
            lean_object *pair = lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(pair, 0, buf);
            lean_ctor_set(pair, 1, addrBuf);
            return lean_io_result_mk_ok(pair);
        }
        lean_dec_ref(buf);
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }

    /* Set actual received size */
    lean_sarray_object *arrObj = lean_to_sarray(buf);
    arrObj->m_size = (size_t)n;

    /*
     * Encode sender address as 6-byte ByteArray:
     *   bytes 0-3: IPv4 address (big-endian / network order octets)
     *   bytes 4-5: port (big-endian)
     */
    lean_object *addrBuf = lean_alloc_sarray(1, 6, 6);
    uint8_t *aptr = lean_sarray_cptr(addrBuf);
    uint32_t ip = ntohl(sender.sin_addr.s_addr);
    uint16_t port = ntohs(sender.sin_port);
    aptr[0] = (ip >> 24) & 0xFF;
    aptr[1] = (ip >> 16) & 0xFF;
    aptr[2] = (ip >>  8) & 0xFF;
    aptr[3] = ip & 0xFF;
    aptr[4] = (port >> 8) & 0xFF;
    aptr[5] = port & 0xFF;

    /* Construct Prod.mk : ByteArray × ByteArray */
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, buf);
    lean_ctor_set(pair, 1, addrBuf);

    return lean_io_result_mk_ok(pair);
}

/* Current Unix time in seconds (for cache TTL expiry, RFC 1035 §6.1.3). */
LEAN_EXPORT lean_obj_res veri_dns_now(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)time(NULL)));
}

/* Unpredictable 16-bit query ID (RFC 5452 resilience). */
LEAN_EXPORT lean_obj_res veri_dns_random_u16(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box((uint16_t)(arc4random() & 0xFFFF)));
}

/* Encode a (ip4, port) pair as a fresh 6-byte Lean ByteArray
 * (4-byte IPv4 big-endian + 2-byte port big-endian). ip and port are
 * in HOST byte order. */
static lean_object *mk_addr6(uint32_t ip, uint16_t port) {
    lean_object *buf = lean_alloc_sarray(1, 6, 6);
    uint8_t *p = lean_sarray_cptr(buf);
    p[0] = (ip >> 24) & 0xFF;
    p[1] = (ip >> 16) & 0xFF;
    p[2] = (ip >>  8) & 0xFF;
    p[3] = ip & 0xFF;
    p[4] = (port >> 8) & 0xFF;
    p[5] = port & 0xFF;
    return buf;
}

/* ----------------------------------------------------------------
 * veri_dns_exchange : @& ByteArray → @& ByteArray
 *   → IO (Option (ByteArray × ByteArray × ByteArray × ByteArray))
 * One query exchange on a fresh UNCONNECTED socket (RFC 5452 §9.2:
 * fresh socket per exchange → unpredictable ephemeral local port).
 *
 * This function makes NO acceptance decision. It returns the first
 * datagram (payload, source6, destination6, local6) and the Lean gate
 * (`datagramMatches`) decides the RFC 5452 §9.1 source/destination
 * match. The socket is briefly connect(2)-ed ONLY to learn the
 * kernel's local address selection for this destination (getsockname),
 * then dissolved (AF_UNSPEC) before the receive, so datagrams from any
 * source reach the Lean gate.
 *
 *   - source6: sender of the datagram (recvfrom)
 *   - destination6: destination IP from packet metadata
 *     (IP_RECVDSTADDR / IP_PKTINFO) + the socket's delivery port
 *   - local6: the socket's local binding when the query was sent
 *
 * Returns none on timeout (2s) or send/recv error.
 * C ABI: (b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) → lean_obj_res
 * ---------------------------------------------------------------- */
LEAN_EXPORT lean_obj_res veri_dns_exchange(b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    struct timeval tv = { .tv_sec = 2, .tv_usec = 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    /* Ask the kernel to report each datagram's destination address. */
    int on = 1;
#ifdef IP_RECVDSTADDR
    setsockopt(fd, IPPROTO_IP, IP_RECVDSTADDR, &on, sizeof(on));
#elif defined(IP_PKTINFO)
    setsockopt(fd, IPPROTO_IP, IP_PKTINFO, &on, sizeof(on));
#endif

    /* Decode 6-byte address: bytes 0-3 = IPv4, bytes 4-5 = port (big-endian) */
    uint8_t *ap = lean_sarray_cptr(addr6);
    struct sockaddr_in dest;
    memset(&dest, 0, sizeof(dest));
    dest.sin_family = AF_INET;
    uint32_t ip = ((uint32_t)ap[0] << 24) | ((uint32_t)ap[1] << 16) |
                  ((uint32_t)ap[2] << 8)  | (uint32_t)ap[3];
    dest.sin_addr.s_addr = htonl(ip);
    dest.sin_port = htons(((uint16_t)ap[4] << 8) | (uint16_t)ap[5]);

    /* Learn the local binding the kernel selects for this destination
     * (source IP by route, fresh ephemeral port), then dissolve the
     * association so the receive is unconnected: acceptance is decided
     * in Lean, not by kernel source-filtering. */
    if (connect(fd, (struct sockaddr *)&dest, sizeof(dest)) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0)); /* none */
    }
    struct sockaddr_in local;
    socklen_t localLen = sizeof(local);
    memset(&local, 0, sizeof(local));
    if (getsockname(fd, (struct sockaddr *)&local, &localLen) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0)); /* none */
    }
    struct sockaddr unspec;
    memset(&unspec, 0, sizeof(unspec));
    unspec.sa_family = AF_UNSPEC;
    /* Dissolving may "fail" with EAFNOSUPPORT on BSDs while still
     * disconnecting; ignore the return value. */
    (void)connect(fd, &unspec, sizeof(unspec));

    if (sendto(fd, lean_sarray_cptr(data), lean_sarray_size(data), 0,
               (struct sockaddr *)&dest, sizeof(dest)) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0)); /* none */
    }

    /* Receive ONE datagram from any source, with its metadata. */
    lean_object *buf = lean_alloc_sarray(1, 0, 512);
    struct sockaddr_in sender;
    memset(&sender, 0, sizeof(sender));
    struct iovec iov = { .iov_base = lean_sarray_cptr(buf), .iov_len = 512 };
    char cbuf[128];
    struct msghdr msg;
    memset(&msg, 0, sizeof(msg));
    msg.msg_name = &sender;
    msg.msg_namelen = sizeof(sender);
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cbuf;
    msg.msg_controllen = sizeof(cbuf);

    ssize_t n = recvmsg(fd, &msg, 0);
    close(fd);
    if (n < 0) {
        lean_dec(buf);
        return lean_io_result_mk_ok(lean_box(0)); /* none (timeout/error) */
    }
    lean_to_sarray(buf)->m_size = (size_t)n;

    /* Destination IP from control messages (0 if unavailable). */
    uint32_t dstIp = 0;
    for (struct cmsghdr *cm = CMSG_FIRSTHDR(&msg); cm != NULL;
         cm = CMSG_NXTHDR(&msg, cm)) {
#ifdef IP_RECVDSTADDR
        if (cm->cmsg_level == IPPROTO_IP && cm->cmsg_type == IP_RECVDSTADDR) {
            struct in_addr a;
            memcpy(&a, CMSG_DATA(cm), sizeof(a));
            dstIp = ntohl(a.s_addr);
        }
#elif defined(IP_PKTINFO)
        if (cm->cmsg_level == IPPROTO_IP && cm->cmsg_type == IP_PKTINFO) {
            struct in_pktinfo pi;
            memcpy(&pi, CMSG_DATA(cm), sizeof(pi));
            dstIp = ntohl(pi.ipi_addr.s_addr);
        }
#endif
    }

    uint16_t localPort = ntohs(local.sin_port);
    uint32_t localIp = ntohl(local.sin_addr.s_addr);
    /* The delivery port of the datagram is this socket's bound port
     * (UDP demultiplexing). */
    lean_object *src6 = mk_addr6(ntohl(sender.sin_addr.s_addr),
                                 ntohs(sender.sin_port));
    lean_object *dst6 = mk_addr6(dstIp, localPort);
    lean_object *loc6 = mk_addr6(localIp, localPort);

    /* (payload, (src6, (dst6, loc6))) */
    lean_object *p2 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p2, 0, dst6);
    lean_ctor_set(p2, 1, loc6);
    lean_object *p1 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p1, 0, src6);
    lean_ctor_set(p1, 1, p2);
    lean_object *p0 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p0, 0, buf);
    lean_ctor_set(p0, 1, p1);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, p0);
    return lean_io_result_mk_ok(some);
}
