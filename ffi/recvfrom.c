#define VERI_DNS_UPSTREAM_BUFSIZE 1232

#include <lean/lean.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <stdlib.h>
#ifdef __linux__
#include <fcntl.h>
#if defined(__has_include)
#if __has_include(<sys/random.h>)
#include <sys/random.h>
#define VERI_DNS_HAVE_GETRANDOM 1
#endif
#endif
#endif

LEAN_EXPORT lean_obj_res veri_dns_udp_socket(lean_obj_arg world) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

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

LEAN_EXPORT lean_obj_res veri_dns_sendto(uint32_t fd, b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) {
    size_t dataLen = lean_sarray_size(data);
    uint8_t *dataPtr = lean_sarray_cptr(data);

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

LEAN_EXPORT lean_obj_res veri_dns_recvfrom(uint32_t fd, size_t maxBytes, lean_obj_arg world) {
    int i_fd = (int)fd;

    lean_object *buf = lean_alloc_sarray(1, 0, maxBytes);

    struct sockaddr_in sender;
    socklen_t senderLen = sizeof(sender);
    memset(&sender, 0, sizeof(sender));

    ssize_t n = recvfrom(i_fd, lean_sarray_cptr(buf), maxBytes, 0,
                         (struct sockaddr *)&sender, &senderLen);
    if (n < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
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

    lean_sarray_object *arrObj = lean_to_sarray(buf);
    arrObj->m_size = (size_t)n;

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

    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, buf);
    lean_ctor_set(pair, 1, addrBuf);

    return lean_io_result_mk_ok(pair);
}

LEAN_EXPORT lean_obj_res veri_dns_now(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)time(NULL)));
}

LEAN_EXPORT lean_obj_res veri_dns_random_u16(lean_obj_arg world) {
    (void)world;
#ifdef __linux__
    uint16_t id;
#ifdef VERI_DNS_HAVE_GETRANDOM
    for (;;) {
        ssize_t r = getrandom(&id, sizeof(id), 0);
        if (r == (ssize_t)sizeof(id)) {
            return lean_io_result_mk_ok(lean_box(id));
        }
        if (r < 0 && errno == EINTR) continue;
        break;
    }
#endif
    {
        int rfd = open("/dev/urandom", O_RDONLY);
        if (rfd >= 0) {
            uint8_t b[2];
            size_t got = 0;
            while (got < 2) {
                ssize_t n = read(rfd, b + got, 2 - got);
                if (n > 0) { got += (size_t)n; continue; }
                if (n < 0 && errno == EINTR) continue;
                break;
            }
            close(rfd);
            if (got == 2) {
                id = (uint16_t)(((uint16_t)b[0] << 8) | (uint16_t)b[1]);
                return lean_io_result_mk_ok(lean_box(id));
            }
        }
    }
    return lean_io_result_mk_error(lean_decode_io_error(EIO, NULL));
#else
    return lean_io_result_mk_ok(lean_box((uint16_t)(arc4random() & 0xFFFF)));
#endif
}

static uint16_t veri_dns_upstream_port(uint16_t nominal) {
    const char *p = getenv("VERI_DNS_UPSTREAM_PORT");
    if (p != NULL && *p != '\0') {
        int v = atoi(p);
        if (v > 0 && v <= 0xFFFF) return (uint16_t)v;
    }
    return nominal;
}

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

LEAN_EXPORT lean_obj_res veri_dns_exchange(b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    struct timeval tv = { .tv_sec = 2, .tv_usec = 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    int on = 1;
#ifdef IP_RECVDSTADDR
    setsockopt(fd, IPPROTO_IP, IP_RECVDSTADDR, &on, sizeof(on));
#elif defined(IP_PKTINFO)
    setsockopt(fd, IPPROTO_IP, IP_PKTINFO, &on, sizeof(on));
#endif

    uint8_t *ap = lean_sarray_cptr(addr6);
    struct sockaddr_in dest;
    memset(&dest, 0, sizeof(dest));
    dest.sin_family = AF_INET;
    uint32_t ip = ((uint32_t)ap[0] << 24) | ((uint32_t)ap[1] << 16) |
                  ((uint32_t)ap[2] << 8)  | (uint32_t)ap[3];
    dest.sin_addr.s_addr = htonl(ip);
    uint16_t nominalPort = ((uint16_t)ap[4] << 8) | (uint16_t)ap[5];
    dest.sin_port = htons(veri_dns_upstream_port(nominalPort));

    if (connect(fd, (struct sockaddr *)&dest, sizeof(dest)) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0));
    }
    struct sockaddr_in local;
    socklen_t localLen = sizeof(local);
    memset(&local, 0, sizeof(local));
    if (getsockname(fd, (struct sockaddr *)&local, &localLen) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0));
    }
    struct sockaddr unspec;
    memset(&unspec, 0, sizeof(unspec));
    unspec.sa_family = AF_UNSPEC;
    (void)connect(fd, &unspec, sizeof(unspec));

    if (sendto(fd, lean_sarray_cptr(data), lean_sarray_size(data), 0,
               (struct sockaddr *)&dest, sizeof(dest)) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0));
    }

    lean_object *buf = lean_alloc_sarray(1, 0, VERI_DNS_UPSTREAM_BUFSIZE);
    struct sockaddr_in sender;
    struct iovec iov;
    char cbuf[128];
    struct msghdr msg;
    struct timespec start;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (;;) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        long remaining_ms = 2000
            - (long)(now.tv_sec - start.tv_sec) * 1000
            - (long)((now.tv_nsec - start.tv_nsec) / 1000000);
        if (remaining_ms <= 0) {
            close(fd);
            lean_dec(buf);
            return lean_io_result_mk_ok(lean_box(0));
        }
        struct timeval rtv = { .tv_sec = remaining_ms / 1000,
                               .tv_usec = (remaining_ms % 1000) * 1000 };
        setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &rtv, sizeof(rtv));

        memset(&sender, 0, sizeof(sender));
        iov.iov_base = lean_sarray_cptr(buf);
        iov.iov_len = VERI_DNS_UPSTREAM_BUFSIZE;
        memset(&msg, 0, sizeof(msg));
        msg.msg_name = &sender;
        msg.msg_namelen = sizeof(sender);
        msg.msg_iov = &iov;
        msg.msg_iovlen = 1;
        msg.msg_control = cbuf;
        msg.msg_controllen = sizeof(cbuf);

        ssize_t n = recvmsg(fd, &msg, 0);
        if (n < 0) {
            if (errno == EINTR) continue;
            close(fd);
            lean_dec(buf);
            return lean_io_result_mk_ok(lean_box(0));
        }
        if (sender.sin_addr.s_addr != dest.sin_addr.s_addr ||
            sender.sin_port != dest.sin_port)
            continue;
        lean_to_sarray(buf)->m_size = (size_t)n;
        break;
    }
    close(fd);

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
    lean_object *src6 = mk_addr6(ntohl(sender.sin_addr.s_addr), nominalPort);
    lean_object *dst6 = mk_addr6(dstIp, localPort);
    lean_object *loc6 = mk_addr6(localIp, localPort);

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

LEAN_EXPORT lean_obj_res veri_dns_tcp_exchange(b_lean_obj_arg data, b_lean_obj_arg addr6, lean_obj_arg world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    struct timeval tv = { .tv_sec = 2, .tv_usec = 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));

    uint8_t *ap = lean_sarray_cptr(addr6);
    struct sockaddr_in dest;
    memset(&dest, 0, sizeof(dest));
    dest.sin_family = AF_INET;
    uint32_t ip = ((uint32_t)ap[0] << 24) | ((uint32_t)ap[1] << 16) |
                  ((uint32_t)ap[2] << 8)  | (uint32_t)ap[3];
    dest.sin_addr.s_addr = htonl(ip);
    dest.sin_port = htons(veri_dns_upstream_port(((uint16_t)ap[4] << 8) | (uint16_t)ap[5]));

    if (connect(fd, (struct sockaddr *)&dest, sizeof(dest)) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0));
    }

    size_t qlen = lean_sarray_size(data);
    if (qlen > 0xFFFF) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0));
    }
    size_t framed = qlen + 2;
    uint8_t *sendbuf = (uint8_t *)malloc(framed);
    if (sendbuf == NULL) {
        close(fd);
        return lean_io_result_mk_ok(lean_box(0));
    }
    sendbuf[0] = (uint8_t)((qlen >> 8) & 0xFF);
    sendbuf[1] = (uint8_t)(qlen & 0xFF);
    memcpy(sendbuf + 2, lean_sarray_cptr(data), qlen);
    size_t sent = 0;
    while (sent < framed) {
        ssize_t s = send(fd, sendbuf + sent, framed - sent, 0);
        if (s <= 0) {
            if (s < 0 && errno == EINTR) continue;
            free(sendbuf);
            close(fd);
            return lean_io_result_mk_ok(lean_box(0));
        }
        sent += (size_t)s;
    }
    free(sendbuf);

    uint8_t lenbuf[2];
    size_t got = 0;
    while (got < 2) {
        ssize_t r = recv(fd, lenbuf + got, 2 - got, 0);
        if (r <= 0) {
            if (r < 0 && errno == EINTR) continue;
            close(fd);
            return lean_io_result_mk_ok(lean_box(0));
        }
        got += (size_t)r;
    }
    size_t rlen = ((size_t)lenbuf[0] << 8) | (size_t)lenbuf[1];

    lean_object *buf = lean_alloc_sarray(1, rlen, rlen);
    uint8_t *bufp = lean_sarray_cptr(buf);
    got = 0;
    while (got < rlen) {
        ssize_t r = recv(fd, bufp + got, rlen - got, 0);
        if (r <= 0) {
            if (r < 0 && errno == EINTR) continue;
            close(fd);
            lean_dec(buf);
            return lean_io_result_mk_ok(lean_box(0));
        }
        got += (size_t)r;
    }
    close(fd);

    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, buf);
    return lean_io_result_mk_ok(some);
}

#ifndef MSG_NOSIGNAL
#define MSG_NOSIGNAL 0
#endif

LEAN_EXPORT lean_obj_res veri_dns_tcp_listen(uint16_t port, lean_obj_arg world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(port);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        int e = errno; close(fd);
        return lean_io_result_mk_error(lean_decode_io_error(e, NULL));
    }
    if (listen(fd, 16) < 0) {
        int e = errno; close(fd);
        return lean_io_result_mk_error(lean_decode_io_error(e, NULL));
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res veri_dns_tcp_accept(uint32_t fd, lean_obj_arg world) {
    (void)world;
    struct sockaddr_in peer;
    socklen_t peerLen = sizeof(peer);
    memset(&peer, 0, sizeof(peer));
    int conn = accept((int)fd, (struct sockaddr *)&peer, &peerLen);
    if (conn < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    struct timeval tv = { .tv_sec = 3, .tv_usec = 0 };
    setsockopt(conn, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    setsockopt(conn, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
#ifdef SO_NOSIGPIPE
    int on = 1;
    setsockopt(conn, SOL_SOCKET, SO_NOSIGPIPE, &on, sizeof(on));
#endif
    lean_object *addrBuf = lean_alloc_sarray(1, 6, 6);
    uint8_t *aptr = lean_sarray_cptr(addrBuf);
    uint32_t ip = ntohl(peer.sin_addr.s_addr);
    uint16_t pport = ntohs(peer.sin_port);
    aptr[0] = (ip >> 24) & 0xFF; aptr[1] = (ip >> 16) & 0xFF;
    aptr[2] = (ip >>  8) & 0xFF; aptr[3] = ip & 0xFF;
    aptr[4] = (pport >> 8) & 0xFF; aptr[5] = pport & 0xFF;
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint32((uint32_t)conn));
    lean_ctor_set(pair, 1, addrBuf);
    return lean_io_result_mk_ok(pair);
}

LEAN_EXPORT lean_obj_res veri_dns_tcp_recv_msg(uint32_t fd, lean_obj_arg world) {
    (void)world;
    int i_fd = (int)fd;
    uint8_t lenbuf[2];
    size_t got = 0;
    while (got < 2) {
        ssize_t r = recv(i_fd, lenbuf + got, 2 - got, 0);
        if (r <= 0) {
            if (r < 0 && errno == EINTR) continue;
            return lean_io_result_mk_ok(lean_box(0));
        }
        got += (size_t)r;
    }
    size_t rlen = ((size_t)lenbuf[0] << 8) | (size_t)lenbuf[1];
    lean_object *buf = lean_alloc_sarray(1, rlen, rlen);
    uint8_t *bufp = lean_sarray_cptr(buf);
    got = 0;
    while (got < rlen) {
        ssize_t r = recv(i_fd, bufp + got, rlen - got, 0);
        if (r <= 0) {
            if (r < 0 && errno == EINTR) continue;
            lean_dec(buf);
            return lean_io_result_mk_ok(lean_box(0));
        }
        got += (size_t)r;
    }
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, buf);
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_obj_res veri_dns_tcp_send(uint32_t fd, b_lean_obj_arg data, lean_obj_arg world) {
    (void)world;
    int i_fd = (int)fd;
    size_t len = lean_sarray_size(data);
    uint8_t *p = lean_sarray_cptr(data);
    size_t sent = 0;
    while (sent < len) {
        ssize_t w = send(i_fd, p + sent, len - sent, MSG_NOSIGNAL);
        if (w <= 0) {
            if (w < 0 && errno == EINTR) continue;
            break;
        }
        sent += (size_t)w;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res veri_dns_tcp_close(uint32_t fd, lean_obj_arg world) {
    (void)world;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}
