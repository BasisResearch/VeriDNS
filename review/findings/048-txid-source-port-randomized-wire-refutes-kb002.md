# 048 — Refuted: the deployed rig binary randomizes BOTH upstream source port and DNS txid (corrects KB CONFIRMED-002 "constant query ID")

**Classification:** refuted (KB lead corrected for this build; FFI/unverified layer)
**RFC claim under test:** RFC 5452 §4.3 / §9.2 — the 16-bit upstream DNS query ID
MUST be unpredictable (with source-port randomization, the primary off-path
cache-poisoning / Kaminsky defence).
**Target:** the running `veri-dns` binary as linked into the rig
(`veri_dns_random_u16` query-ID FFI + `veri_dns_exchange` ephemeral-port FFI),
observed on netns `verid` iface `v-verid`, veri-dns @10.53.0.2:5300.

## What KB-002 recorded, and why this refutes it

Finding `002-mutation-constant-query-id.md` was a **mutation** experiment: it
force-patched `veri_dns_random_u16` to return the constant `0x1337` and showed
the proofs stayed green (a real coverage-gap). The KB lead "CONFIRMED-002
constant txid" was then, in shorthand, attached to the *deployed rig* as if the
shipped binary emitted a constant query ID. This capture on the **actual,
unmutated running binary** refutes that: the query ID varies per query, exactly
as the reference resolver's does.

## Runtime reproduction (observable)

tcpdump on veri-dns's upstream-facing veth while issuing six queries for six
distinct, uncached names from the attacker namespace:

```
ip netns exec verid tcpdump -n -i v-verid 'udp and dst port 53 and dst host 10.53.0.12'
# concurrently, six fresh recursions:
ip netns exec attacker dig @10.53.0.2 -p 5300 rnd<rand>xz<i>.example.test A
```

veri-dns upstream queries (src port before `>`, txid before `A?`):

```
10.53.0.2.39261 > 10.53.0.12.53: 43174 A? rnd19725xz1.example.test. (42)
10.53.0.2.47111 > 10.53.0.12.53:  6590 A? rnd22262xz2.example.test. (42)
10.53.0.2.37353 > 10.53.0.12.53: 41734 A? rnd32513xz3.example.test. (42)
10.53.0.2.40810 > 10.53.0.12.53: 32883 A? rnd28202xz4.example.test. (42)
10.53.0.2.35842 > 10.53.0.12.53: 39381 A? rnd8458xz5.example.test.  (41)
10.53.0.2.50895 > 10.53.0.12.53:  1468 A? rnd10188xz6.example.test. (42)
```

Source ports (39261/47111/37353/40810/35842/50895) and txids
(43174/6590/41734/32883/39381/1468) are **both randomized** across all six.

## Reference control (unbound), same experiment

```
10.53.0.3.23449 > 10.53.0.12.53: 39347% [1au] A? unb15424qz1.example.test. (53)
10.53.0.3.28537 > 10.53.0.12.53: 21168% [1au] A? unb11440qz2.example.test. (53)
10.53.0.3.19789 > 10.53.0.12.53: 65087% [1au] A? unb3055qz3.example.test.  (52)
10.53.0.3.29833 > 10.53.0.12.53:  3422% [1au] A? unb5447qz4.example.test.  (52)
10.53.0.3.53768 > 10.53.0.12.53:  6037% [1au] A? unb1595qz5.example.test.  (52)
```

unbound likewise varies both fields (it additionally sets EDNS `[1au]` and the
`%` checking-disabled flag; those are orthogonal to the txid entropy question).
On the txid + source-port axis under test, veri-dns matches the reference: an
off-path attacker must guess ~32 bits (16-bit txid + ephemeral-port range) per
forgery attempt, so blind response spoofing is infeasible on this rig.

## Boundary caveat (the coverage-gap KB-002 identified still stands)

This refutes only the "the shipped binary emits a constant query ID" reading. It
does **not** close the underlying coverage-gap: `veri_dns_random_u16` is an
opaque `@[extern]` IO action, so the Lean model still *assumes* rather than
*proves* this entropy. KB-002's mutation demonstrated that a constant-txid
regression would sail through the proof suite green. The correct standing status
is: on-wire entropy is present and verified-by-observation on this build, but it
remains trusted FFI glue needing out-of-band (code-review / link-time / runtime
statistical) assurance, not a theorem.

## Verdict

Refuted (for the deployed rig). Both upstream source port and DNS transaction ID
are randomized on the wire for the current `veri-dns` binary; the recorded
"constant query ID" lead does not describe this build.
