# 000 — `veri-dns` fails to link on Linux (`arc4random`), inside the unverified FFI

- **Severity:** medium (build/portability); **class:** coverage-gap (unverified glue)
- **On/off-path:** OFF-PATH (FFI, outside the proof boundary) but blocks running the server at all.

## What it is
The server executable did not build on this Linux host:

```
ld.lld: error: undefined symbol: arc4random
>>> referenced by recvfrom.c
>>>               recvfrom.o:(veri_dns_random_u16) in archive .../libveri-dns-ffi.a
```

`ffi/recvfrom.c:163` used `arc4random()` for the RFC 5452 unpredictable query ID. The host glibc (2.43) *does* export `arc4random` (weak, `GLIBC_2.36`), but the Lean toolchain's bundled clang/link sysroot does not, so the final link fails. The **entire library and all 560 proof targets build clean** — only the `veri-dns` exe link fails.

## Why it matters
1. The "verified DNS resolver" could not be run as shipped on a stock Linux host — every dynamic/differential/pentest experiment (and the README's own `dig @127.0.0.1 -p 5300` demo) is blocked until this is fixed.
2. It sits in the FFI, which **no theorem constrains** (`pathmap.md` §3). The RFC 5452 query-ID unpredictability the anti-poisoning theorems *assume* rests entirely on this unverified C — a natural coverage-gap boundary case (see the `constant-query-id` mutation).

## Fix applied (to enable testing)
Replaced `arc4random()` with the kernel CSPRNG via `getrandom(2)`, falling back to `/dev/urandom` — both cryptographically strong, preserving the RFC 5452 §4.3 property. `ffi/recvfrom.c`:

```c
#include <fcntl.h>
#include <sys/random.h>
...
uint16_t r = 0;
ssize_t got = getrandom(&r, sizeof(r), 0);
if (got != (ssize_t)sizeof(r)) { int fd = open("/dev/urandom", O_RDONLY); if (fd>=0){ read(fd,&r,sizeof(r)); close(fd);} }
return lean_io_result_mk_ok(lean_box((uint16_t)(r & 0xFFFF)));
```

After the fix `lake build veri-dns` succeeds and the server starts and listens on UDP 5300.

## Reproduce
`git stash` the fix, `lake build veri-dns` → link error above. Restore → builds.
