# 003 — Answer owner-name case not preserved (RFC 1035 §2.3.3 SHOULD); the "0x20 vs unbound" half is refuted

- **Severity:** low (cosmetic / defense-in-depth; NOT a correctness break — both resolvers resolve the same address).
- **Class:** coverage-gap / RFC-cosmetic (SHOULD-level). The Lean spec models names case-*insensitively* (a canonical fold, see finding 001) but never obligates *case preservation* on client-delivered owner names, so this divergence is entirely outside the verified surface.
- **On/off-path:** client-delivery boundary (`Server.replyForResolution` → `scrubAnswerB`). Functionally correct; only the echoed case differs.

## What was claimed (two parts) and what the rig shows

The source finding bundled two claims. Part A is **CONFIRMED**; part B (the "unbound uses 0x20, veri-dns doesn't" divergence) is **REFUTED** on this rig.

### Part A — answer owner-name case: CONFIRMED

Client sends a mixed-case query `ExAmPlE.TeSt A`. veri-dns returns the owner name **lowercased**; unbound **echoes the client's exact case**:

```
# veri-dns @10.53.0.2:5300
$ ip netns exec attacker dig +noedns @10.53.0.2 -p 5300 ExAmPlE.TeSt A
;; ANSWER SECTION:
example.test.		3589	IN	A	10.53.0.100      <-- normalized to lowercase

# unbound @10.53.0.3:5301  (reference)
$ ip netns exec attacker dig +noedns @10.53.0.3 -p 5301 ExAmPlE.TeSt A
;; ANSWER SECTION:
ExAmPlE.TeSt.		3600	IN	A	10.53.0.100      <-- client's case preserved
```

Both answer `10.53.0.100` — resolution is identical; only the owner-name case in the ANSWER SECTION differs.

**Reproduction caveat (important):** the divergence only appears through the *normal iterative path*. In a *single-hop* path where the root answers the apex directly (which happened earlier under a contaminated rig where a stale `nsd-root-merged.conf` made the root serve `example.test` authoritatively), veri-dns echoed the raw wire question owner `ExAmPlE.TeSt.` and looked case-preserving. That was an artifact of the merged-root contamination, not veri-dns's real behavior. On a *clean* hierarchy (root → tld → leaf), veri-dns delivers the authoritative/canonical lowercase owner name, as shown above.

### Part B — upstream 0x20 case randomization: REFUTED as a divergence

The claim was that veri-dns lacks DNS-0x20 case randomization *which unbound uses*. On this rig **neither resolver does 0x20**, and both forward the client's case **verbatim** upstream — so there is no veri-dns-vs-unbound divergence here.

`unbound.conf` has no `use-caps-for-id` (default = off). tcpdump on each resolver's egress veth:

```
# lowercase client input -> both forward lowercase (0x20 would randomize even lowercase input)
veri-dns  egress:  A? qq1.example.test.
unbound   egress:  A? qq2.example.test.

# MIXED-case client input -> both forward the SAME mixed case verbatim
veri-dns  egress:  A? Qq3.ExAmPlE.TeSt.
unbound   egress:  A? Qq4.ExAmPlE.TeSt.
```

veri-dns forwards the querier's case verbatim (no randomization); unbound (0x20 disabled) does the same. So the "anti-spoofing 0x20 gap relative to unbound" is not reproducible in this environment. (A separately-configured unbound with `use-caps-for-id: yes` would differ, but that is a config choice, not the shipped reference behavior here.)

## Mechanism

`scrubAnswerB` (`VeriDNS/Impl/AnswerScrub.lean:47`) only *filters* records by case-insensitive CNAME-reachability (`nameEqCI`); it does **not** rewrite the owner-name case. So the owner bytes delivered to the client are whatever the authoritative server served — the leaf `nsd` serves the zone lowercase, hence `example.test.`. unbound, by contrast, rewrites the queried owner name to match the case the stub used in the QUESTION section. The resolver-under-test's whole name pipeline is case-*insensitive* by design (`nameEqCI`/`foldNameCase`, `Impl/DomainName.lean`), so it never carries the querier's case forward onto the answer owner.

## RFC basis

RFC 1035 §2.3.3 (cited in-tree at `VeriDNS/Impl/AnswerScrub.lean:9`): *"When you receive a domain name or label, you should preserve its case. … comparisons … should be done in a case-insensitive manner."* This is a **SHOULD** for case preservation, not a MUST — veri-dns is fully case-insensitive-correct (the required behavior) and merely declines the SHOULD-level case echo. unbound honors it. RFC 4343 reaffirms case-insensitive equivalence with preserved echo. DNS-0x20 (draft-vixie-dnsext-dns0x20) is an *optional* defense-in-depth that *depends* on the SHOULD being honored end-to-end.

## Why this is not a correctness bug

- Both resolvers return the same RRset / address; no cache collision, no answer substitution.
- No RFC MUST is violated; DNS name comparison is case-insensitive everywhere downstream.
- The verified spec deliberately models names up-to-fold (finding 001), so an owner-name-case obligation is simply out of scope — this is a coverage-gap in *scope*, surfacing as a cosmetic wire difference, not a proof that slipped.

## Verdict

Part A **confirmed** (real, reproducible client-visible divergence; SHOULD-level RFC 1035 §2.3.3 case-preservation gap). Part B **refuted** (no 0x20 divergence from the reference unbound on this rig; both forward client case verbatim). Net: a low-severity cosmetic / defense-in-depth gap, not a correctness break.

## Rig notes (for reproduction)

The rig arrived contaminated from a prior experiment: a stale `veridns-auth-root` transient unit referenced a missing `nsd-root-merged.conf`, the running root nsd served `example.test A 6.6.6.6` authoritatively, and a leftover `p-auth` veth blocked clean bring-up. A full reset was required before the clean measurement above:

```
ip netns exec ... bash /root/dev/_vmdns/vm-down.sh
systemctl stop 'veridns*'; systemctl reset-failed 'veridns*'
rm -f /run/systemd/transient/veridns-*.service; systemctl daemon-reload
ip link del p-auth; ip link del brdns; ip netns del auth verid unbound attacker
review/env/up.sh    # then verify: root delegates test. (no aa apex A), leaf serves 10.53.0.100
```
