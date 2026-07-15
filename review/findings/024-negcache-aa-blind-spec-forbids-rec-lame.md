# 024 — Negative-cache spec MANDATES aa-blindness; hardening (REC_LAME) is proof-forbidden

- id: M-negcache-aa-harden-reveals-mandated-lameness
- classification: **bad-spec** (spec obligation forbids a security fix)
- build: **broke** (reverse probe: the mutation is a hardening, and verification rejects it)

## Mutation (a hardening, not a bug)

```diff
 def negativelyCacheable (resp : Format) : Bool :=
-  resp.header.tc == 0
+  resp.header.tc == 0 && resp.header.aa == 1
     && (resp.header.rcode == Rcode.nameError
         || (resp.header.rcode == Rcode.noError && resp.answer.isEmpty))
```
`VeriDNS/Impl/Server.lean:87`. This ADDS the missing RFC 2308 / REC_LAME-style
authority check: only AUTHORITATIVE (aa==1) NXDOMAIN/NODATA responses become
negatively cacheable.

## Build result — the finding

`lake build` FAILS at the single obligation:

```
error: VeriDNS/Proof/Refinement.lean:5868:48: unsolved goals
case noError  resp : Spec.Format  htc : resp.header.tc = 0#1
  ⊢ resp.answer = #[] → resp.header.aa = 1#1
case nameError  resp : Spec.Format  htc : resp.header.tc = 0#1
  ⊢ resp.header.aa = 1#1
```

`negativelyCacheable_iff_absorbNeg_trigger` (`Proof/Refinement.lean:5863-5871`)
is an IFF that pins

```
negativelyCacheable resp = true
  ↔ (rcode = nameError ∨ (rcode = noError ∧ answer.isEmpty))
```

with NO `aa` term. Adding `&& aa==1` strictly strengthens the LHS, so the `←`
direction becomes FALSE: an `aa==0` nameError/NODATA response satisfies the RHS
trigger but is no longer `negativelyCacheable`. The proof leaves `⊢ aa = 1`
unprovable. **The theorem STATEMENT is what fails — the spec obligation itself
requires the aa-blind behavior.**

This is the ONLY failure. In particular:
- `negativelyCacheable_nodata` (`Proof/Cache.lean:279-289`) still builds green:
  its proof destructures the conjunction with an anonymous `⟨_, …⟩` that absorbs
  the new `aa==1` conjunct, so it is agnostic to the mutation.
- No independent security/soundness theorem breaks. Nothing on the negative
  path reads `resp.header.aa`. Confirmed by rebuilding `VeriDNS.Proof.Cache`
  clean and by the single-error build of `VeriDNS.Proof.Refinement`.

Per the reverse-probe rule: the sole failures are the two theorems that encode
the aa-blind requirement (one breaks, one is structurally immune), and no
genuine-correctness theorem breaks ⇒ **bad-spec**: the specification forbids the
fix rather than being load-bearing on a good property.

## Why it is observably wrong (baseline)

`negativelyCacheable` (`Server.lean:87-90`) reads only `tc`, `rcode`, and
`answer` — it NEVER inspects `resp.header.aa`. The IFF above proves this is not
an accident but a fixed obligation. Consequently the unmutated resolver treats a
lame, non-authoritative (`aa==0`, `ra==1`) NXDOMAIN/NODATA as negatively
cacheable exactly like an authoritative one, and installs it in the negative
cache. RFC 2308 §5 ties negative caching to the SOA from the authoritative
server; a hardened resolver (unbound, REC_LAME) does not cache a lame negative.
The differential is definitionally certain from the impl + the pinning IFF;
prior rig observation on this env already showed veri-dns accepting and
negatively caching an `aa==0` lame negative that unbound rejects. (This round the
in-tree `spoof.py` only forges `aa==1` positive answers and nsd always sets AA
for its zones, so a fresh on-wire lame-negative injection was not re-run — the
evidence is the verification obligation itself.)

## Citations
- Impl: `VeriDNS/Impl/Server.lean:87-90` (`negativelyCacheable`, aa-blind)
- Spec obligation that forbids the fix: `VeriDNS/Proof/Refinement.lean:5863-5871`
  (`negativelyCacheable_iff_absorbNeg_trigger`)
- Structurally-immune sibling: `VeriDNS/Proof/Cache.lean:279-289`
  (`negativelyCacheable_nodata`)

## Restore
`git checkout -- VeriDNS/Impl/Server.lean` → `lake build` (green, 279 jobs) →
`restart-verid.sh` (active; host.example.test → 10.53.0.101). Baseline confirmed.
