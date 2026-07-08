# 002 — Coverage gap: constant upstream query ID (RFC 5452) is unverified glue

**Classification:** coverage-gap (unverified FFI glue; proofs stayed green)
**RFC claim under test:** RFC 5452 §4.3 / §9.2 — the 16-bit DNS query ID sent to
upstream servers MUST be unpredictable (a primary defense against off-path
cache poisoning / "Kaminsky" spoofing).
**Target:** `ffi/recvfrom.c`, `veri_dns_random_u16`.

## The mutation

`veri_dns_random_u16` normally draws 16 bits from the kernel CSPRNG
(`getrandom(2)`, falling back to `/dev/urandom`). The mutant replaces the random
draw with a hard-coded constant `0x1337` (= 4919):

```diff
 LEAN_EXPORT lean_obj_res veri_dns_random_u16(lean_obj_arg world) {
     (void)world;
-    uint16_t r = 0;
-    ssize_t got = getrandom(&r, sizeof(r), 0);
-    if (got != (ssize_t)sizeof(r)) {
-        int fd = open("/dev/urandom", O_RDONLY);
-        if (fd >= 0) {
-            ssize_t n = read(fd, &r, sizeof(r));
-            (void)n;
-            close(fd);
-        }
-    }
+    uint16_t r = 0x1337;
     return lean_io_result_mk_ok(lean_box((uint16_t)(r & 0xFFFF)));
 }
```

## Build result — proofs stayed GREEN

`lake build` completed successfully with the mutation in place:

```
Build completed successfully (279 jobs).
```

and `lake build veri-dns` linked the binary:

```
Build completed successfully (560 jobs).
```

No theorem, spec, or type obligation rejects a constant query ID. The Lean
verification stops at the FFI boundary: `veri_dns_random_u16` is an opaque
`@[extern]` IO action, so its cryptographic quality is assumed, never proven.
This confirms the on-path / off-path boundary — the random source is
**unverified glue**.

## Runtime reproduction (observable)

Loaded the mutant into the rig (`review/env/restart-verid.sh`, baseline test
answer `10.53.0.101` returned fine), then captured veri-dns's *outgoing*
upstream queries while sending three distinct uncached names from the attacker
namespace:

```
ip netns exec verid tcpdump -n -v -i v-verid "udp and port 53"
ip netns exec attacker dig @10.53.0.2 -p 5300 b1.example.test A
ip netns exec attacker dig @10.53.0.2 -p 5300 b2.example.test A
ip netns exec attacker dig @10.53.0.2 -p 5300 b3.example.test A
```

Mutant veri-dns — the DNS transaction ID (number before `A?`) is a **constant
4919 = 0x1337** on every query:

```
10.53.0.2.40286 > 10.53.0.12.53: 4919 A? b1.example.test. (33)
10.53.0.2.36061 > 10.53.0.12.53: 4919 A? b2.example.test. (33)
10.53.0.2.45744 > 10.53.0.12.53: 4919 A? b3.example.test. (33)
```

Reference resolver (unbound), same experiment — txids are **randomized**:

```
10.53.0.3.22795 > 10.53.0.12.53: 18403% [1au] A? c1.example.test. (44)
10.53.0.3.49483 > 10.53.0.12.53: 64550% [1au] A? c2.example.test. (44)
10.53.0.3.53116 > 10.53.0.12.53: 37593% [1au] A? c3.example.test. (44)
```

The mutant answers queries correctly (functional behavior unchanged), so nothing
in normal operation or in the proof suite flags the regression — only a packet
capture reveals it.

## Why it is undesirable

RFC 5452 §4.3 lists the query ID as one of the fields an off-path attacker must
guess to forge a response, and §9.2 recommends maximizing its entropy together
with source-port randomization. A constant query ID collapses that 16-bit search
space to a single known value (0x1337). Combined only with source-port guessing,
this makes the resolver dramatically easier to poison — precisely the
Kaminsky-class attack RFC 5452 exists to mitigate. unbound (the reference
resolver) draws a fresh random txid per query, as shown above.

Note that veri-dns's per-exchange source ports *do* still vary (40286 / 36061 /
45744 — a separate FFI, `veri_dns_exchange`'s fresh unconnected socket), so this
mutant isolates the query-ID entropy loss specifically.

## Boundary conclusion

This is a **coverage gap, not a bad spec**. The correct fix is not a new
theorem (the query ID's unpredictability is a property of a hardware/kernel
entropy source that cannot be established by Lean proof) but rather to treat
`veri_dns_random_u16` as trusted glue that needs out-of-band assurance: code
review, a link-time guarantee it calls a CSPRNG, and ideally a runtime/statistical
test in the test harness. The verification is genuinely silent here.
