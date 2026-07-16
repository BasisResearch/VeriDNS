# The VeriDNS review harness

Everything needed to re-run the bug-finding pipeline from scratch. The pipeline
itself is a single Claude `Workflow` script — `review/workflows/full-review.mjs` —
that runs **end to end with no human and no main-agent step**. This document
explains what that harness *is*, so it can be understood, trusted, and repaired.

Read alongside: `ENV.md` (rig runbook), `REPORT.md` (findings), `REVIEW.org`
(methodology + rationale).

---

## 1. Why a rig at all

The central question is whether VeriDNS's *verification* is load-bearing. That
cannot be answered by reading proofs alone: a green proof over a weak spec is
indistinguishable from a green proof over a strong one until you **run** the code
and compare it to a mature reference. So every claim bottoms out in an
**observable, differential experiment**: veri-dns and `unbound` resolve the *same
name* against the *same authoritative data*, and we diff the wire.

## 2. Rig architecture

One VM (~2 GiB, under the 12 GiB host budget), all resolvers and servers in
Linux network namespaces on a bridge `brdns` (203.0.113.0/24) inside it:

| netns | address(es) | runs | port |
|---|---|---|---|
| `auth` | 203.0.113.10/.11/.12 **and the 5 real root IPs** (198.41.0.4, 199.9.14.201, 192.33.14.30, 199.7.91.13, 192.203.230.10) | 3× `nsd`: root `.`, tld `test.`, leaf `example.test.` | 53 |
| `verid` | 203.0.113.2 | **veri-dns** (system under test) | **5300** |
| `unbound` | 203.0.113.3 | **unbound** (reference oracle) | **5301** |
| `attacker` | **192.168.53.99** (not TEST-NET-3 — see below) | `dig`, `tcpdump`, `spoof.py`, crafted-packet responders | — |

### 2.1 Why two subnets (read this before "fixing" the addressing)

The rig was renumbered off `10.53.0.0/24`, and the client sits on a *different*
subnet from the servers. Both facts are forced by veri-dns itself — two ACLs in
`VeriDNS/Impl/Server.lean` that point in opposite directions:

| ACL | direction | covers |
|---|---|---|
| `doNotQueryNets` (~:336) | egress — refuses to **query** | 0/8, 127/8, **10/8**, 100.64/10, 169.254/16, **172.16/12**, **192.168/16**, 240/4 |
| `defaultAcl` (~:159) | ingress — only **accepts clients** from | 127/8, **10/8**, **172.16/12**, **192.168/16** |

`defaultAcl` is an exact **subset** of `doNotQueryNets`, so the set of addresses
veri-dns will both talk to *and* accept queries from is **empty**. One subnet
cannot host both roles:

- **Auth servers must be outside `doNotQueryNets`** → `203.0.113.0/24`
  (TEST-NET-3). On the old `10.53.0.0/24` the resolver refused to query its own
  auth servers and every test failed spuriously.
- **The client must be inside `defaultAcl`** → `192.168.53.99`. On
  `203.0.113.99` its queries are **silently dropped** by
  `if !permitted acl clientAddr then return cache` (UDP: timeout; TCP:
  accept-then-EOF). That is correct resolver behavior toward a stranger, not a
  bug — it just means the rig must split the two roles.

A client address is never an egress target, so putting the client in 192.168/16
does **not** weaken the egress filter. The filter stays **ACTIVE and honest**;
`VERI_DNS_ALLOW_LOOPBACK_EGRESS` is **not** set (setting it would disable the
shipped filter and mask real egress bugs). Both subnets share the one bridge, so
plain on-link routes carry traffic between them. `unbound.conf` mirrors the
split with `access-control: 192.168.53.0/24 allow` — omit it and the oracle
REFUSEs the very queries veri-dns answers.

**The key trick:** veri-dns has the real root-server IPs hardcoded
(`VeriDNS/Main.lean:12-18`) and the review may not patch the source. So the fake
root `nsd` **binds those exact IPs** and the resolver namespaces get `/32`
on-link routes to them — veri-dns's hardcoded root queries land on our fake root.
`unbound` is pointed at the same fake root via `root.hints`. Both resolvers
therefore descend an identical, fully-controlled hierarchy.

**One server per level is deliberate.** A single `nsd` serving all zones answers
grandchild names authoritatively from the root IP, which changes both resolvers'
behavior and destroys the differential. Root/TLD/leaf must be separate so real
referrals happen.

Zone data (`review/env/nsd/zones/`): `example.test A 203.0.113.100`,
`host.example.test A 203.0.113.101`, `www.example.test CNAME example.test`,
plus `rogue-example.test.zone` (attacker-controlled variant, activated by adding
a zone stanza to `nsd-root.conf` — used for rogue-ancestor experiments).

`.test` is RFC 6761 special-use: unbound returns a built-in NXDOMAIN for it, so
`local-zone: "test." nodefault` is required in `unbound.conf` or the reference
oracle is useless.

## 3. Scripts (`review/env/`)

| script | side | purpose |
|---|---|---|
| `up.sh` | host | **Idempotent full bring-up.** Stages configs + the built binary into the VM, installs packages, builds the netns topology, starts all 5 units. Safe to re-run after a reboot/suspend. |
| `down.sh` / `vm-down.sh` | host/VM | teardown |
| `restart-verid.sh` | host | **The mutation-observation primitive.** Copies `.lake/build/bin/veri-dns` into the VM, restarts *only* the resolver-under-test with a fresh cache, prints a verifying dig. |
| `query.sh <verid\|unbound> <name> <type>` | host | one-shot differential query helper |
| `spoof.py` | VM (`attacker`) | forged/off-path response injection |
| `rogue_auth.py`, `fatauth_responder.py`, `fakeleaf.py`, `badauth.py` | VM (`auth`) | crafted authoritative responders (inject extra RRs, out-of-bailiwick SOAs, oversized answers) |

Reach the rig **only** through `penn-testing/vm/ssh.sh <cmd>` (vsock). The netns
live inside the VM and are **not** reachable from the host.

## 4. The mutation-testing loop (the core mechanism)

A mutation is an **injected, observably-wrong implementation change**. The signal
is the *pair* (does the proof still pass?, does the server misbehave?):

| build | observable | verdict | meaning |
|---|---|---|---|
| **green** | **yes** | `bad-spec` | The spec is too weak: a wrong impl provably conforms. **The finding we most want.** |
| green | yes, but no theorem covers it | `coverage-gap` | Unverified surface (FFI, call-sites, unmodelled fields). |
| **broke** | — | `proof-caught-semantic` | A theorem *statement* became false → **verification is load-bearing here** (a positive result). |
| broke, but only a tactic failed | — | `proof-caught-brittle` | Statement still true; **weak evidence** — retry with a repaired script. |
| green | no | `not-observable` | Uninteresting. |

**Semantic vs brittle is the crux.** Early on, a naive over-collapse of the case
fold "broke the build" — but only because a tactic (`rw [hc.1]; simp`) assumed a
particular `if` shape, not because any obligation was violated. The mutation only
counts as *caught* if a theorem **statement** becomes false. Where breakage is
merely tactical, the weaponizer must attempt a **minimal, local proof-script
repair** and rebuild; if it then goes green with the impl still wrong, that is a
real `bad-spec` (this is exactly how finding `014` was settled).

**Observation path:** mutate source → `lake build` (the proof signal) →
`lake build veri-dns` → `review/env/restart-verid.sh` (loads the mutant into the
VM) → dig from `attacker` → compare to unbound → **revert + rebuild + restart**.

## 5. Hard-won constraints (violate these and the results are wrong)

1. **Revert PER-FILE, never tree-wide.** `git checkout -- .` is blocked by the
   harness safety classifier and silently killed ~15 mutations in the earlier run.
   Always `git checkout -- <exact files you edited>`.
2. **Serialize all rig access.** Concurrent poisoning experiments contaminate each
   other's caches. Running verifiers in `parallel` produced a **false positive**
   (finding `005`). Weaponize and verify stages must be serial.
3. **Restart BOTH resolvers before every differential.** A *warm* unbound (real
   delegation cached) vs a *cold* veri-dns is not a valid comparison — that
   asymmetry is what made `005` look like a divergence. It is not.
4. **Only the mutation stage may build.** Everything else uses the running rig, or
   it will race the shared `.lake` build tree.
5. **A finding is not a finding until unbound disagrees.** If unbound does the same
   thing on the same path, it is the DNS trust model, not a VeriDNS bug. ~9 candidate
   findings died this way — that is the harness working.
6. **API/network errors are not "no findings."** A finder returning null from a 529
   must never be counted as exhaustion (it once faked a dry terminus). Retry, and
   count a round toward "dry" only if the finders actually ran.
7. **Mutations must be reachable, not just source-editable.** A green-building
   mutant proves a *spec* gap; it is only a *bug* if the wrong behavior is
   reachable at runtime. Prefer wire-level repros.

## 6. Preflight facts a fresh run must re-establish

- **The FFI does not link on stock Linux** as shipped: `ffi/recvfrom.c` used
  `arc4random`, absent from the Lean toolchain's link sysroot → no binary → no
  testing at all. Fix: `getrandom(2)` with a `/dev/urandom` fallback (both CSPRNGs,
  preserving RFC 5452 §4.3). This is finding `000` *and* a prerequisite.
- **Axiom audit** (`#print axioms` on the capstones) must be clean
  (`propext`/`Classical.choice`/`Quot.sound` only) before any proof-based claim means
  anything.
- **Execution-path map** (`pathmap.md`) must exist first: it tells every later agent
  which code the server actually runs, so effort is not wasted mutating off-path or
  decorative definitions.

## 7. Resource budget

One VM at 2 GiB; mutation builds are serial (each `lake build` is multi-GB); total
stays well under the 12 GiB host ceiling. A full `lake build` from cold is ~2 min;
incremental after a one-file mutation is faster. The rig VM is throwaway — `up.sh`
rebuilds it idempotently after any reboot or suspend.

## 8. Which workflow script to run

| script | use |
|---|---|
| **`workflows/full-review.mjs`** | **The canonical entry point.** Self-contained end-to-end pipeline (preflight → rig → rounds → report). Run this for a fresh review, especially against a new upstream: `Workflow({ scriptPath: "review/workflows/full-review.mjs" })`. No human/main-agent step. |
| `workflows/bug-hunt.mjs` | The *historical* loop actually used for this review (run id `wf_e49938ec-5fb`). Keep it only to resume that specific cached run against commit `8e4e16d`. It assumes preflight/rig were done externally and its weaponize prompt still uses a tree-wide revert (safety-blocked) — superseded by `full-review.mjs`. |
| `workflows/mutation.mjs` | Superseded. The original one-shot curated mutation batch, kept for provenance; its curated targets are folded into `full-review.mjs`'s synthesis seeds. |

**Note on `agent` linter warnings:** `agent`, `log`, `phase`, `parallel` are
runtime globals injected by the Workflow harness; a TypeScript linter will flag
`Could not find name 'agent'` inside the `agentR` helper. That is a false positive.
