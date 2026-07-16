# 061 — Frozen-clock liveness capstones are vacuous: a bogus per-round deadline test SERVFAILs cold deep resolutions and the adequacy proofs cannot see it

**Classification:** bad-spec (frozen-clock vacuity of the liveness/adequacy capstones)
**unboundDiffers:** yes
**Build after mutation + minimal repair:** GREEN (all proofs replay; no theorem statement became false)

## Claim

The adequacy / liveness capstones
(`ServeAdequacy.serveDatagram_depth1_adequate`,
`SpineAdequacy.resolveWithIO_spine_adequate` / `_no_starvation`,
`Adequacy.resolveWithIO_adequate_of_descent`)
are supposed to guarantee that a resolution the resolver *could* complete is in
fact delivered. They cannot reject a resolver that spuriously SERVFAILs, because
the model clock they run against is **frozen**: `Prog.run`'s `.now` command
returns `w.clock` without ever advancing it (`FreeIO.lean` `run_now_bind_eq`,
`w.clock` constant), and the resolve-entry time `state.now` equals that same
`w.clock`. Any deadline predicate that compares a *later* `now`-sample against
`state.now` is therefore decidably false in every model round and is invisible
to the proofs — even though on the wire `UdpSocket.now = (uint32_t)time(NULL)`
(one-second granularity, `ffi/recvfrom.c`) genuinely advances during real
multi-round resolution.

I demonstrate this by adding one such predicate. The mutant SERVFAILs any cold,
deep resolution whose descent crosses a one-second wall-clock boundary; unbound
completes the identical resolution on the identical data.

## Mutation

`VeriDNS/Impl/Server.lean:574`, inside `ioResumeLoop`:

```
-    if t ≥ deadline then
+    if t ≥ deadline || t > state.now then
       return (.error "resolveWithIO: query deadline exceeded", state.resources.cache)
```

`deadline = now + budget` (budget = 5 s). The new disjunct fires as soon as the
wall clock ticks past the second in which the resolve was entered — i.e. after a
single slow RTT — discarding the remaining ~4 s of budget.

## Why the proofs stay green (the load-bearing point)

`lake build` is GREEN after a purely mechanical repair. The repair threads one
extra hypothesis `hnow : ¬ (w.clock > state.now)` through the FreeIO reduction
lemmas and the adequacy lemmas, discharging the new `if` disjunct. Crucially the
hypothesis is **always dischargeable for free** in every capstone:

* `resolve` is entered with `state.now = w.clock`
  (new lemma `FreeIO.resolve_paused_now`: `resolve … now … = .ok (.paused st) → st.now = now`);
* every continuation preserves it
  (`FreeIO.afterResume_continue_now`, `dropIfBizarre_now`, and the
  `state.now = nowS` invariant already carried by `SpineAdequacy.spineDelegation_chain`).

So at each call site `hnow` is proved by `rw [resolve_paused_now …]; simp`
or `rw [hclk, hnow]` — never by any real timing argument. No capstone's
`= some ((.ok resp, …), …)` delivery conclusion changed; none became false. The
mutation is a spec gap, not a caught bug. (Per method rule 4 this minimal local
repair is exactly the test: green after repair + wire differential = bad-spec.)

Files repaired (mechanical `hnow` threading only): `FreeIO.lean`,
`Adequacy.lean`, `CooperativeNetwork.lean`, `Depth1Adequacy.lean`,
`SpineAdequacy.lean`, `ServeAdequacy.lean`, plus the three `*Sound.lean`
`by_cases` widenings.

## Reproduction (rig, TEST-NET-3 203.0.113.0/24)

Inject one-shot latency so a cold descent crosses a 1-second boundary while
staying well under the 5 s budget (all authoritative servers live in netns
`auth` on `v-auth`):

```
ip netns exec auth tc qdisc add dev v-auth root netem delay 700ms
```

Restart both resolvers cold, query the same fresh name:

```
# veri-dns MUTANT @203.0.113.2:5300 — 4 cold tries (restart before each):
;; ->>HEADER<<- status: SERVFAIL  ;; Query time: 701 msec
;; ->>HEADER<<- status: SERVFAIL  ;; Query time: 1403 msec
;; ->>HEADER<<- status: SERVFAIL  ;; Query time: 702 msec
;; ->>HEADER<<- status: SERVFAIL  ;; Query time: 701 msec

# unbound ORACLE @203.0.113.3:5301 — identical cold latent path:
;; ->>HEADER<<- status: NOERROR
host.example.test.  3585  IN  A  203.0.113.101
```

tcpdump on the mutant during a cold SERVFAIL proves it *reaches* upstream and
then abandons the descent after a single hop:

```
21:57:07.783247 v-verid Out 203.0.113.2 > 198.41.0.4.53: A? TESt. (qmin, cased)
21:57:08.483450 v-verid In  198.41.0.4.53 > 203.0.113.2: response (0/1/2 referral)
# RTT crossed the 07 -> 08 second boundary; next ioResumeLoop now-sample reads
# 08 > entry-second 07  ->  t > state.now  ->  SERVFAIL, ~4 s of budget unused.
```

Without latency (sub-second descent, `t == state.now`) the mutant answers
normally — the failure is specific to cold/deep/slow resolutions crossing a
second boundary, matching the frozen-clock blind spot exactly. Timing is coarse
(1 s), so the differential is intermittent at low latency and becomes
deterministic at ≥700 ms/hop.

## Why it is wrong (RFC / oracle)

A recursive resolver must pursue a resolution until it succeeds, is provably
negative, or its overall query budget is exhausted (RFC 1034 §5.3.3; RFC 1035
§7). Aborting because the wall clock advanced one second past *entry* — while
seconds of budget remain — turns every slow or deep delegation chain into a
spurious SERVFAIL. unbound, on the identical path against the identical zone
data with a cold cache, resolves it (NOERROR, 203.0.113.101). The divergence is
the resolver's, not the DNS trust model's.

## Takeaway

The liveness capstones are vacuously satisfied for any timeout/deadline logic
keyed on wall-clock progress, because the `Prog` model clock never advances and
`state.now = w.clock`. To make these proofs load-bearing for liveness, the model
must let `.now` advance across `Prog` steps (or budget must be modeled in
step-count), so that a `now`-sample can exceed `state.now` in the model and the
delivery conclusion can be put at risk.
