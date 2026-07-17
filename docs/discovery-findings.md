# Discovery-harness findings

Output of the discovery hunt (`test/discover.py`, wired via `test/discover.sh`
and stage 6 of `test/ci_gate.sh`), the workstream-D deliverable of
`docs/model-strengthening-plan-2.md §D`.

This is **not** a regression rig. The existing rigs (`inject_difftest.sh`,
`difftest.sh`, `tcp_*`) replay the triaged finding list and so caught nothing
new. This harness **explores**: it mutates an honest authoritative response for a
name that **exists** and asserts the resolver's output against RFC-derived
invariants that need no reference resolver. A property violation is a **candidate
finding**.

## What the harness does

Topology (`test/discover_mock.py`): a genuine two-phase delegation. A ROOT zone
`.` refers `veridns.` downward (NS in authority, glue in additional, AA=0); a
CHILD zone answers the leaves authoritatively (AA=1). Both roles share one
loopback socket (veri-dns pins every upstream query to one port, and only
127.0.0.1 is bindable without a root-only loopback alias), distinguished
statefully: the first look at a `(qname,qtype)` is a referral, subsequent looks
are the answer. The resolver therefore performs a real accept-referral →
set-up-slist → re-query descent (confirmed by the mock's `role` log:
`desc=['child','root']`).

Each scenario applies one named **mutation** from a catalogue to the otherwise
honest reply, restricted to the ROOT (referral) or CHILD (answer) reply so the
effect is attributable to a single edit:

`flip_aa`, `authority_off_cut`, `additional_off_cut`, `empty_answer`,
`second_ns_no_glue`, `second_ns_dead_glue`, `truncate_glue`, `duplicate_rrset`,
`reorder_rrset`, `off_owner_cname`, `off_owner_a`, `off_owner_soa`,
`junk_from_legit` (a malformed datagram from the expected source addr:port before
the real reply).

## Properties checked (primary — no reference resolver needed)

Hard invariants (a violation is a candidate finding):

1. **`exists_not_nodata`** — a name that *holds data of the queried type* is never
   answered NODATA (NOERROR + empty answer) nor NXDOMAIN (RFC 1034 §4.3.2,
   RFC 2308 §2). The harness owns the zone, so it knows the name exists.
2. **`delivered_in_bailiwick`** — no delivered ANSWER record has an owner off the
   query's own name (absent a legitimate CNAME chain).
3. **`no_off_cut_additional`** — no delivered ADDITIONAL owner is off the
   delegation cut / a foreign zone (047).
4. **`no_foreign_authority`** — no delivered AUTHORITY owner (e.g. a negative
   SOA) is a foreign zone that is not an ancestor of the qname (012/013).

Weak divergence (worth a look, not a hard entitlement violation):
`answer_matches_honest` — when a mutation should be transparent, the honest
answer is still delivered.

Differential (secondary, opt-in `--diff`) compares against unbound behind the
same mock. It is best-effort: the stateful single-socket mock is tuned to
veri-dns's query pattern, and unbound descends differently, so the comparison is
gated on unbound resolving the honest leaf and skipped (with a note) otherwise.
Property-based is what runs in CI.

## Results on this build (commit 26b5849, main)

16 scenarios; deterministic across four consecutive runs. **6 hard-property
violations, 2 weak divergences, 0 differential mismatches.** The hunt is
non-fatal — it reports these as candidate findings without failing the gate.

### Plan findings independently reproduced

| Plan finding | Scenario | Mutation | veri-dns output | Property failed |
|---|---|---|---|---|
| **040** AA=1 referral → spurious NODATA | `aa-flip-referral(040)` | `flip_aa @ root` | `NOERROR`, answer=`[]`, `desc=['root']` (never descended) | `exists_not_nodata` |
| **041/045** name-exists answered NODATA | `empty-answer(040/041)` | `empty_answer @ child` | `NOERROR`, answer=`[]` | `exists_not_nodata` |
| **047** out-of-bailiwick additional delivered | `additional-off-cut(047)` | `additional_off_cut @ child` | `NOERROR`, answer=`[mail.veridns. A 192.0.2.40]`, **additional owner `attacker.example.` delivered** | `no_off_cut_additional` |

- **040** is the exact fault the plan names (`Resolver.lean:400` requires `aa==0`
  for a referral; an AA=1 response carrying NS authority is rejected as a
  referral and falls through to the `noError && answer.isEmpty ⇒ finalizeAnswer`
  NODATA manufacture at `Resolver.lean:422`). `desc=['root']` confirms the
  resolver never descended to the child — it synthesised NODATA at the root
  referral instead of following the delegation.
- **041/045** is the same fall-through reached directly: an empty NOERROR reply
  for a name that exists becomes a believed NODATA rather than a retry.
- **047** is a genuine leak: `attacker.example. A 6.6.6.6`, an owner off the
  delegation cut, is delivered in the client's additional section alongside the
  correct answer.

### Additional candidate findings surfaced by the hunt

| Scenario | Mutation | veri-dns output | Reading |
|---|---|---|---|
| `off-owner-cname(036)` | `off_owner_cname @ child` | `NOERROR`, answer=`[]` | The off-owner CNAME is correctly **not** chased/delivered (good), but the resolver then manufactures a believed NODATA for a name that exists rather than retrying — the same empty-answer fall-through (`Resolver.lean:422`). |
| `off-owner-a` | `off_owner_a @ child` | `NOERROR`, answer=`[]` | An A for a different owner is correctly scrubbed (good), but again yields a spurious NODATA instead of a retry/SERVFAIL. |
| `off-owner-soa(012)` | `off_owner_soa @ child` | `NOERROR`, answer=`[]` | A spoofed foreign SOA is correctly not delivered (good, no foreign-authority leak), but the name-that-exists is answered NODATA. |
| `truncate-glue` | `truncate_glue @ root` | `SERVFAIL`, `desc=[]` (weak) | A glueless delegation (NS listed, no A glue) yields SERVFAIL. `ns1.veridns.` is in-bailiwick and resolvable, so a resolver could re-resolve the NS address; today it does not descend at all. |

The three `off-owner-*` HITs share one root cause with 041/045: whenever the
resolver has scrubbed an untrustworthy answer and is left with nothing, it takes
the `noError && answer.isEmpty` fall-through and **manufactures a believed
NODATA** for a name it knows nothing negative about. The safe behaviours diverge:
it correctly drops the poison, but then reports NODATA rather than
retrying/failing soft — precisely the empty-answer misclassification class the
plan describes (040/041), reached from the scrub path. These are candidate
findings for the classification-frame theorem, not new soundness leaks (nothing
untrustworthy is delivered).

### Behaviours confirmed CORRECT (no divergence)

- **035 multi-homed failover** (`second-ns-dead(035)`): ns1 glue dead, ns2 glue
  live — the resolver **failed over to ns2 and delivered** (`192.0.2.40`). On
  this delegation shape 035 does **not** reproduce as a failure; the failover
  path works. (The plan flags 035 as a `SlistShape` *proof-coverage* gap, not
  necessarily a runtime bug — consistent with this.)
- `second-ns-no-glue`: glueless second NS, resolver still delivers via ns1.
- `authority_off_cut @ root` and `additional_off_cut @ root`: an off-cut owner in
  the *referral* authority/additional is correctly filtered by the bailiwick
  scrub (`bailiwickRaws cut`) — delivered answers stay clean.
- `flip_aa @ child` (AA on the leaf answer): does not change which records are
  authorised — delivered correctly.
- `duplicate_rrset`, `reorder_rrset`: tolerated; answer delivered.
- `junk_from_legit @ child`: a malformed datagram from the expected server
  addr:port before the real reply is **not** mistaken for the answer — the real
  reply is delivered (`192.0.2.40`). On this shape 017 does not reproduce at the
  client boundary (the FFI source-match plus decode drop the junk here).

## How to run

```
# property-based hunt (primary; what CI stage 6 runs), no reference resolver:
test/discover.sh --json /tmp/discover.json

# add the (best-effort, gated) unbound differential:
test/discover.sh --diff

# a single scenario:
test/discover.sh --only 'additional-off-cut(047)'
```

Dependency policy mirrors `ci_gate.sh`: a missing dep (veri-dns exe / dnspython
venv / dig) SKIPS locally and FAILS in CI (`CI=1`). A property violation never
fails the gate — it is a discovery signal, surfaced as a PASS-with-note count in
stage 6.

## Where each candidate finding points in the code

- 040 / 041/045 / the three off-owner NODATA-after-scrub HITs → the empty-answer
  classifier fall-through, `VeriDNS/Impl/Resolver.lean:394-425` (esp. line 422).
  This is the classification frame the plan calls the highest-value single
  theorem.
- 047 → the delivered additional section (outside the current `Entitled` frame),
  `VeriDNS/Impl/Server.lean` reply assembly.
- truncate-glue SERVFAIL → glueless-delegation NS re-resolution in
  `stepFindServers` / the slist setup.
