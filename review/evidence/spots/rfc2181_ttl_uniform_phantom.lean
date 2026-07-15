import VeriDNS.Spec.Clarifications

open VeriDNS.Spec

/-! SPOT (round 8, NEW): RFC 2181 §5.2 published surface is a phantom tautology
    that does NOT encode the "lowest TTL" mandate and is disconnected from the
    executed normalizer.

    The RFC-ledger entries (Spec/Clarifications.lean:64-66):
      rfc_proves rrset_setAllTtls_uniform      [2181][203:214]
      rfc_proves rrset_setAllTtls_uniform      [2181][215:234]   <-- covers "lowest TTL"
      rfc_proves rrset_setAllTtls_preserves_records [2181][215:234]

    RFC 2181 §5.2, lines 227-229 (inside [215:234]):
      "the client should treat the RRs ... as if all TTLs in the RRSet had been
       set to the value of the LOWEST TTL in the RRSet."

    The published theorem `rrset_setAllTtls_uniform s t : (s.setAllTtls t).ttlsUniform`
    proves only that mapping every TTL to a single value `t` yields a uniform set —
    for an ARBITRARY, unconstrained `t`.  It never pins `t` to the lowest.
    `RRSet`/`setAllTtls`/`ttlsUniform` have ZERO references in Impl/ or Proof/
    (grep-verified); the executed normalizer is Impl/Cache.normRaws (per-key MIN). -/

-- The property the published theorem actually certifies, restated for an
-- explicit MAX-fold.  If this proves, `ttlsUniform` (the theorem's whole payload)
-- cannot distinguish the RFC-mandated LOWEST from the RFC-forbidden HIGHEST.
def setAllToConst (s : RRSet) (t : BitVec 32) : RRSet :=
  { s with ttls := s.ttls.map (fun _ => t) }

-- SENSIBLE control: the genuine uniformity guarantee is real (should prove).
theorem sensible_uniform_holds (s : RRSet) (t : BitVec 32) :
    (setAllToConst s t).ttlsUniform := by
  simp only [RRSet.ttlsUniform, setAllToConst, List.mem_map]
  rintro a ⟨_, _, rfl⟩ b ⟨_, _, rfl⟩; rfl

-- NONSENSE #1 (vacuity of the published payload): a normalizer that sets every
-- TTL to the MAXIMUM of the set — the exact behavior RFC 2181 §5.2 line 229
-- ("value of the LOWEST TTL") FORBIDS — satisfies the SAME `ttlsUniform`
-- property the published `rrset_setAllTtls_uniform` certifies.  It proves,
-- so the published theorem's payload places NO constraint favoring "lowest".
def setAllToMax (s : RRSet) : RRSet :=
  { s with ttls := s.ttls.map (fun _ => s.ttls.foldl (fun a b => if a.toNat < b.toNat then b else a) 0) }

theorem nonsense_max_fold_is_also_uniform (s : RRSet) :
    (setAllToMax s).ttlsUniform := by
  simp only [RRSet.ttlsUniform, setAllToMax, List.mem_map]
  rintro a ⟨_, _, rfl⟩ b ⟨_, _, rfl⟩; rfl

-- NONSENSE #2 (the "lowest" mandate is unencodable): the published guarantee is
-- `∀ t, (s.setAllTtls t).ttlsUniform` — universally quantified over EVERY target
-- value `t`, including any `t` STRICTLY GREATER than every original TTL in `s`.
-- A property that holds for all t cannot possibly pin t to the lowest.  This
-- one-liner is the whole point: the RFC-2181-§5.2-[215:234] ("value of the
-- LOWEST TTL") obligation is discharged by a theorem that is TTL-value-blind.
theorem uniform_holds_for_every_target_including_non_lowest :
    ∀ (s : RRSet) (t : BitVec 32), (setAllToConst s t).ttlsUniform :=
  sensible_uniform_holds
