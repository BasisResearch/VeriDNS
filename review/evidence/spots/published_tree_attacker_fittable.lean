/-! SPOT (round 6 audit, NEW — threads b/c deepened; the ACTUALLY-published, RFC-cited
    soundness, not the orphaned Net.Network capstone).

    Subject: `NameTree.resolveWithIO_sound` (Proof/NameTree.lean:1747,
    `rfc_proves [1034][1849:1976]`, ProofLinks.lean:60) and its driver
    `ioResumeLoop_sound` (:1633).  Signature (verbatim shape):

        theorem resolveWithIO_sound (T : Node ResourceRecord)
            (hnet : NetworkConsistent T M Sock)
            (hc   : CacheAgrees T cache) … :
            SatisfiesM (ShimSound T) (resolveWithIO …)

    GREP FACTS (source, no proof):
      * `T` is a ∀-BOUND PARAMETER.  It occurs ONLY inside the two premises
        (`NetworkConsistent T`, `CacheAgrees T`) and the conclusion (`ShimSound T`).
        NO theorem anywhere pins `T` to a canonical zone / real DNS data.
        (`NameTree.lean` never even names `Net.Network`/`Net.Resolves` — the published
        tree-model soundness and the constructive `Net.Network` machinery are DISJOINT
        universes; grep-verified.)
      * `cacheAgrees_empty` (NameTree.lean:814) proves `CacheAgrees T DnsCache.empty`
        for EVERY `T`.  So at server start (empty cache) the `hc` premise is satisfied
        by ANY tree, canonical or poisoned.
      * `NetworkConsistent T` (NameTree.lean:1577) requires only that every
        `acceptResponse`-passing datagram be `ResponseConsistent T` — a promise about
        the (unverified, spoofable) transport, discharged NOWHERE at M=IO (zero
        producers, grep-verified).  Its gate `acceptResponse` = 16-bit id echo +
        question echo, whose entropy rests entirely on FFI `veri_dns_random_u16`
        (confirmed constant/guessable, findings 000/002).

    CONSEQUENCE (the weakness): the tree `T` is chosen by whoever discharges `hnet` —
    i.e. by the NETWORK.  A spoofer who passes `acceptResponse` and answers from any
    internally-coherent POISONED tree `T'` satisfies `NetworkConsistent T'` and
    `CacheAgrees T' empty`, so the published soundness delivers exactly `ShimSound T'`
    — "the client's answer agrees with the poison tree."  The theorem's guarantee is
    "agreement with SOME tree the transport is coherent with," which is strictly
    weaker than "correct DNS data," and an observably-poisoned resolver satisfies it.

    Below: a faithful schematic. `mem` = `RRInTree`; `net` = the accepted datagram's
    record; `deliver` = the record the impl hands the client. -/

namespace SpotTreeFittable

-- Abstract world: a "tree" is any predicate over records; `mem r T` = `RRInTree T r`.
variable {Tree Rec : Type}

/-- **SENSIBLE half — this SHOULD prove.**  Faithful essence of `resolveWithIO_sound`:
    if the accepted network record is in the (arbitrary) tree `T` [`NetworkConsistent`]
    and the impl delivers that record [the on-path answer], then the delivered record
    is in `T` [`ShimSound T`].  A pure monotonicity — the theorem's real content. -/
theorem shimSound_essence
    (mem : Rec → Tree → Prop) (net deliver : Rec) (T : Tree)
    (hnet : mem net T) (hdeliver : deliver = net) :
    mem deliver T := by
  subst hdeliver; exact hnet

/-- **NONSENSE half — demonstrated by a POSITIVE counterexample.**  The published
    soundness does NOT certify agreement with a *fixed canonical* tree.  We exhibit a
    concrete model in which (i) the ∀T conditional the theorem provides holds, yet
    (ii) the attacker record `net` is NOT in the canonical tree, and (iii) the
    delivery is therefore NOT in the canonical tree.  Because this counterexample
    proves, `mem deliver canonical` is UNDERIVABLE from the theorem's guarantee — the
    resolver is "sound" against a spoofer-chosen tree, never against canonical DNS.

    Model: `Rec := Bool`, tree = predicate on Bool, `net = true`,
    `canonical = (· = false)` (canonical DNS does NOT contain the attacker's record). -/
theorem canonical_agreement_does_not_follow :
    ∃ (mem : Bool → (Bool → Prop) → Prop) (canonical : Bool → Prop) (net deliver : Bool),
      deliver = net
      ∧ (∀ T, mem net T → mem deliver T)   -- the ∀T conditional the theorem gives
      ∧ ¬ mem net canonical                -- attacker record ∉ canonical DNS
      ∧ ¬ mem deliver canonical := by      -- ⇒ delivery ∉ canonical DNS (not certified)
  refine ⟨(fun r T => T r), (· = false), true, true, rfl, ?_, ?_, ?_⟩
  · intro T h; exact h
  · simp
  · simp

/-- **Witness that the poison tree IS admissible.**  For the singleton "parrot" tree
    `fun r => r = net`, both premises of `resolveWithIO_sound` hold (network coherent,
    empty cache agrees) and `ShimSound` is satisfied by the attacker's own record.
    This is the `T := T'` instantiation the spoofer uses — proving the theorem is
    live for poison trees, not just the canonical one. -/
theorem poison_tree_is_admissible
    (net deliver : Rec) (hdeliver : deliver = net) :
    let mem : Rec → (Rec → Prop) → Prop := fun r T => T r
    let parrot : Rec → Prop := fun r => r = net
    mem net parrot ∧ mem deliver parrot := by
  subst hdeliver
  exact ⟨rfl, rfl⟩

end SpotTreeFittable
