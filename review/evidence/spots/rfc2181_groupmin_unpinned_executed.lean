/-! ============================================================================
    REFUTED (round 6, self-check): the hypothesis below is FALSE.  The impl min-ness
    IS pinned by a real theorem STATEMENT: `foldl_minTtl_props` (NameTreeComplete.lean
    :1051) conjunct-2 proves `∀ e ∈ L, p e → (foldl minTtlB .. s).toNat ≤ e.ttl.toNat`
    — i.e. groupMinTtl ≤ every same-key member (the lower bound), and conjunct-3
    proves it equals seed-or-a-member.  Together they characterize the LOWEST TTL.
    A `min ↦ max` impl mutation falsifies conjunct-2's STATEMENT (max ≤ member fails),
    and this theorem is used (groupMinTtl_congr :1104, groupMinTtl_le_seed
    IoResumeSound:15).  So the executed RFC 2181 §5.2 normalization is NOT a trusted-
    definition-only surface.  KEPT for the record; the schematic below is sound in
    isolation but MISSES foldl_minTtl_props, which is the missing lower-bound pin.
    ============================================================================ -/

/-! SPOT (round 6, NEW, distinct from rfc2181_ttl_uniform_phantom): the EXECUTED
    RRset TTL normalizer's "use the LOWEST TTL" property (RFC 2181 §5.2, lines
    227-229 "as if all TTLs ... set to the value of the LOWEST TTL") is pinned by
    NO theorem statement — only by the definitional `min` inside impl
    `groupMinTtl` / model `rrGroupMin`, plus the impl↔model correspondence.

    On-path chain (from source, grep-verified):
      * Impl   Cache.groupMinTtl (Cache.lean:327) folds `minTtlB` over same-key RRs.
      * Model  Net.rrGroupMin   (NetworkSemantics.lean:665) folds `min` over same-key.
      * groupMin_corr (Refinement.lean:2774): (groupMinTtl L r).toNat = rrGroupMin ..
        — the ONLY theorem relating the two; NOT rfc_proves'd.
      * Cache.absorb (NetworkSemantics.lean:675, rfc_proves [2181][343:383]) calls
        normalizeTTL → rrGroupMin, but its RFC link anchors the FUNCTION text, and
        checks nothing about min-ness.
      * The published RFC-2181 surface (Clarifications.lean:40/64-66,
        ProofLinks.lean:152) is `rrset_setAllTtls_uniform` over `RRSet.setAllTtls t`
        — an UNRELATED function with an ARBITRARY `t` (already flagged as a phantom).

    GREP FACT: no theorem anywhere states `rrGroupMin rrs r ≤ e.ttl` for a same-key
    member `e ∈ rrs`, nor `groupMinTtl .. ≤ member`. Min-ness is a trusted def.

    The two properties that ARE proven of the fold —
      (U) uniformity  : same-key members receive one common normalized TTL
                        (groupMinTtl_congr, NameTreeComplete.lean:1101)
      (C) correspondence: impl fold = model fold through αRR (groupMin_corr)
    — are BOTH invariant under replacing `min` with any other associative-
    commutative-idempotent op, e.g. `max`.  So a COORDINATED impl+model mutant
    `minTtlB`/`rrGroupMin` : min ↦ max keeps (U) and (C) TRUE as statements, and the
    published `rrset_setAllTtls_uniform` (different function) is untouched — yet the
    resolver now normalizes every RRset UP to its LARGEST member TTL.  An attacker
    who lands one high-TTL record in an RRset extends the cache lifetime of the whole
    set (stale/poisoned-record persistence), violating RFC 2181 §5.2 exactly. -/

-- Abstract stand-in for the per-key fold seeded by the record's own ttl, reducing
-- with a binary op `op` over same-key members.  `min` = spec-correct; `max` = mutant.
variable {T : Type}

def keyFold (op : Nat → Nat → Nat) (ttls : List Nat) (seed : Nat) : Nat :=
  ttls.foldl op seed

-- (C) CORRESPONDENCE is op-agnostic: if impl and model fold with the SAME op over
-- corresponding ttls, they agree — whether op is min or max.  So the correspondence
-- theorem's STATEMENT cannot distinguish a min-fold from a max-fold.
theorem correspondence_is_op_agnostic (op : Nat → Nat → Nat) (ttls : List Nat) (seed : Nat) :
    keyFold op ttls seed = keyFold op ttls seed := rfl

-- (U) UNIFORMITY is op-agnostic: any two same-key members fold the SAME list with the
-- SAME seed-relation, so they land on one value — for min OR max.  Model at the shared
-- key: both members reduce the identical multiset, so equal.  (Schematic: identical args.)
theorem uniformity_is_op_agnostic (op : Nat → Nat → Nat) (ttls : List Nat) (s : Nat) :
    keyFold op ttls s = keyFold op ttls s := rfl

-- NONSENSE: the `max` fold is a perfectly good "normalizer" as far as (U)+(C) can see.
-- Witness: with ttls = [10, 4000000] and seed 10, the min-fold gives 10 (RFC-correct),
-- the max-fold gives 4000000 (RFC-VIOLATING) — yet nothing in (U)/(C) rules max out.
theorem max_fold_survives_and_is_wrong :
    keyFold max [10, 4000000] 10 = 4000000
    ∧ keyFold min [10, 4000000] 10 = 10 := by
  constructor <;> decide

-- SENSIBLE: what a NON-vacuous RFC 2181 §5.2 obligation must state — the normalized
-- value is a LOWER BOUND of every same-key member (this is what pins `min` and REJECTS
-- `max`).  No such theorem exists in the codebase for rrGroupMin/groupMinTtl.
def IsLowestTtl (norm : List Nat → Nat) : Prop :=
  ∀ ttls, ttls ≠ [] → (∀ t ∈ ttls, norm ttls ≤ t)

-- the RFC-correct min-fold SATISFIES the lowest-TTL obligation on a sample RRset:
theorem min_satisfies_lowest_sample :
    (fun ts => List.foldl min (100 : Nat) ts) [10, 20] ≤ 10
    ∧ (fun ts => List.foldl min (100 : Nat) ts) [10, 20] ≤ 20 := by
  constructor <;> decide

-- and the `max` mutant FAILS that obligation (witness [10, 20]): foldl max 0 = 20 ≰ 10.
theorem max_fails_lowest :
    ¬ IsLowestTtl (fun ts => List.foldl max 0 ts) := by
  intro h
  have := h [10, 20] (by decide) 10 (by decide)
  simp only [List.foldl] at this
  omega
