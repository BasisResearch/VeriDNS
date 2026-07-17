import VeriDNS.RFC.Check
import VeriDNS.Proof.SentMinimised







namespace VeriDNS.Spec.QnameMinimisation

open VeriDNS.Spec VeriDNS.Impl

/--
   A resolver that implements QNAME minimisation obscures the QNAME and
   QTYPE in queries directed to an authoritative name server that is not
   known to be responsible for the original QNAME.
-/
def minimised_probe_contents (sname : ByteArray) (revealed : Nat) (qu : Question) : Prop :=
  Resolver.probeRoundB sname revealed = true →
    Resolver.subQuestion sname revealed qu
      = { qname := DomainName.minimisedName sname revealed,
          qtype := 1, qclass := qu.qclass }

/--
   the QNAME that is the original QNAME, stripped to just one label
      more than the longest matching domain name for which the name
      server is known to be authoritative
-/
def probe_reveals_exactly_floor (m : ByteArray) (keep : Nat) : Prop :=
  VeriDNS.Proof.DeliveredWire.CanonicalName m →
    DomainName.labelCount (DomainName.minimisedName m keep)
      = min (DomainName.labelCount m) keep

/--
   The A or AAAA QTYPEs are always good
   candidates to use because these are the least likely to raise issues
   in DNS software and middleboxes that do not properly support all
   QTYPEs.
-/
def probe_qtype_obscured (sname : ByteArray) (revealed : Nat) (qu : Question) : Prop :=
  Resolver.probeRoundB sname revealed = true →
    (Resolver.subQuestion sname revealed qu).qtype = 1

theorem probe_qtype_is_A (sname : ByteArray) (revealed : Nat) (qu : Question)
    (hp : Resolver.probeRoundB sname revealed = true) :
    (Resolver.subQuestion sname revealed qu).qtype = 1 := by
  rw [subQuestion_probe hp]

theorem reveal_cap_after_max (sname : ByteArray) (r : Nat)
    (h : Resolver.maxMinimiseSteps ≤ r) :
    Resolver.bumpRevealed sname r = DomainName.labelCount sname := by
  simp [Resolver.bumpRevealed, h]

theorem reveal_step_below_cap (sname : ByteArray) (r : Nat)
    (h : r < Resolver.maxMinimiseSteps) :
    Resolver.bumpRevealed sname r = r + 1 := by
  simp [Resolver.bumpRevealed, Nat.not_le.mpr h]

theorem max_minimise_count_recommended : Resolver.maxMinimiseSteps = 10 := rfl

/-! ### Relaxed fallback (RFC 9156 §3 step 6d, non-strict branch; findings 051/052/064)

The resolver follows the **non-strict** branch of RFC 9156 step 6d (matching
unbound's `qname-minimisation-strict: no` default): an NXDOMAIN answering a
*minimised probe* is NOT returned to the client — many real zones (broken
middleboxes, ENT-mishandling servers) deny an empty non-terminal even though
the full name exists.  Instead the loop re-probes with the **full** qname
against the same servers (`run_ioResumeLoop_probeNxdomainFallsBack`); only a
full-name NXDOMAIN — a non-probe round, `probeRoundB … = false` — is delivered
(`run_ioResumeLoop_nxdomain` requires exactly that hypothesis).  A probe-round
timeout likewise falls back to the full qname rather than burning the retry
budget on the probe (`Server.fallbackRevealed`, `run_ioResumeLoop_timeout`).
The RFC 8020 subtree-denial rule is retained in the MODEL (`ancestorDenied`,
sound for cooperative servers) but the implementation no longer exercises it
for probe rounds — a documented deviation from strict RFC 8020. -/

theorem probe_denial_falls_back (sname : ByteArray) (r : Nat)
    (h : Resolver.probeRoundB sname r = true) :
    Server.fallbackRevealed sname r = DomainName.labelCount sname := by
  simp [Server.fallbackRevealed, h]

theorem full_round_no_fallback (sname : ByteArray) (r : Nat)
    (h : Resolver.probeRoundB sname r = false) :
    Server.fallbackRevealed sname r = r := by
  simp [Server.fallbackRevealed, h]

/-- After the fallback the round is no longer a probe: `labelCount sname` fails
the `revealed < labelCount sname` conjunct of `probeRoundB`, so the re-probe
sends the FULL qname (see `Resolver.subQuestion`) and at most one fallback
happens per `sname`. -/
theorem fallback_round_is_full (sname : ByteArray) :
    Resolver.probeRoundB sname (DomainName.labelCount sname) = false := by
  simp [Resolver.probeRoundB]

open VeriDNS.Spec.Net in
/-- The relaxed-mode derivation exists in the MODEL too (lockstep with the
impl fallback): a strict-probe NXDOMAIN reply can be CONSUMED via
`Resolves.badResponse`'s `StrictProbe` disjunct and the resolution continues —
the probe denial is not forced to become the client's NXDOMAIN verdict (here
the continuation exhausts to SERVFAIL, so the final rcode is NOT nameError).
Dual of `ex_strict_ancestor_denied`: both the strict (RFC 8020
`ancestorDenied`) and the relaxed (RFC 9156 §3 (6d) fallback) readings are
derivable in the model; since 2026-07-17 the implementation exercises only the
relaxed one. -/
theorem ex_relaxed_probe_fallback :
    ∃ tr path tEnd cout resp,
      Resolves scenario allUp "127.0.0.1" 512 (fun _ => 0) 100 [] [] Cache.empty ["10.0.0.52"]
        ⟨N ["WWW","FOO","MIL"], .rr .a, .«in», false⟩ tr path tEnd cout resp
      ∧ resp.rcode ≠ RCode.nameError := by
  refine ⟨_, _, _, _, _,
    Resolves.badResponse "10.0.0.52" []
      ⟨N ["WWW","FOO","MIL"], .rr .a, .«in», false⟩
      ⟨N ["MIL"], .rr .a, .«in», false⟩
      _ _ _ _ Cache.empty Cache.empty 7 5300
      (replyDatagram
        (queryDatagram 7 "127.0.0.1" "10.0.0.52" 5300 512
          ⟨N ["MIL"], .rr .a, .«in», false⟩)
        { aa := true, rcode := RCode.nameError, answer := [],
          authority := [ rr ["MIL"] 86400
            (.soa (N ["SRI-NIC","ARPA"]) (N ["SRI-NIC","ARPA"]) 1 1 1 1 86400) ],
          additional := [] })
      (Or.inr ⟨⟨[], by decide⟩, rfl, rfl⟩)
      (Transit.deliver _ _ _ (by decide) (by decide))
      (accepts_reply _ _ _ _ _ _ _)
      (Or.inr (Or.inr ⟨⟨[], by decide⟩, rfl, rfl⟩))
      (Resolves.exhausted _ _),
    fun h => nomatch h⟩

/--
   The correct
   response to ENTs is NODATA (i.e., a response code of NOERROR and an
   empty answer section).
-/
def ent_nodata_not_final (resp : Format) : Prop :=
  resp.header.rcode = Rcode.noError → Server.strictDenialB resp = false

theorem nodata_not_strict_denial (resp : Format)
    (h : resp.header.rcode = Rcode.noError) :
    Server.strictDenialB resp = false := by
  have hne : (Rcode.noError == Rcode.nameError) = false := by decide
  simp [Server.strictDenialB, h, hne]

theorem strict_denial_excludes_cname (resp : Format)
    (h : (Resolver.cnameToChase (RR := ResourceRecord) resp).isSome = true) :
    Server.strictDenialB resp = false := by
  cases hc : Resolver.cnameToChase (RR := ResourceRecord) resp with
  | none => rw [hc] at h; simp at h
  | some _ => simp [Server.strictDenialB, hc]

/--
   A resolver using QNAME minimisation can possibly be used to cause a
   query storm to be sent to servers when resolving queries containing a
   QNAME with a large number of labels, as described in Section 2.3.
   That section proposes methods to significantly dampen the effects of
   such attacks.
-/
def query_storm_dampened (sname : ByteArray) (r : Nat) : Prop :=
  Resolver.maxMinimiseSteps ≤ r →
    Resolver.bumpRevealed sname r = DomainName.labelCount sname

end VeriDNS.Spec.QnameMinimisation



rfc_proves VeriDNS.Proof.SentMinimised.ioResumeLoop_sent_minimised [9156][136:168]
rfc_proves VeriDNS.Proof.SentMinimised.sent_question_minimised [9156][143:157]
check_rfc_doc VeriDNS.Spec.QnameMinimisation.minimised_probe_contents [9156][158:168]
  via subQuestion_probe
check_rfc_doc VeriDNS.Spec.QnameMinimisation.probe_reveals_exactly_floor [9156][158:168]
  via VeriDNS.Proof.QnameMin.labelCount_minimisedName

check_rfc_doc VeriDNS.Spec.QnameMinimisation.probe_qtype_obscured [9156][170:192]
  via VeriDNS.Spec.QnameMinimisation.probe_qtype_is_A

rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_probeConsumed [9156][194:207]

rfc_proves VeriDNS.Spec.QnameMinimisation.reveal_cap_after_max [9156][209:215]
rfc_proves VeriDNS.Spec.QnameMinimisation.max_minimise_count_recommended [9156][241:249]
rfc_proves VeriDNS.Spec.QnameMinimisation.reveal_step_below_cap [9156][241:249]
rfc_out_of_scope [9156][251:258]
rfc_out_of_scope [9156][259:270]


rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_continue [9156][335:336]
rfc_out_of_scope [9156][338:340]
rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_probeConsumed [9156][342:345]
-- Step 6d: the impl takes the NON-strict branch ("If the resolver does not
-- support [RFC8020], go to step 3") — a probe NXDOMAIN falls back to the full
-- qname (findings 051/064).  The strict branch remains derivable in the model
-- (`ancestorDenied` / `ex_strict_ancestor_denied`).
rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_probeNxdomainFallsBack [9156][347:350]
rfc_proves VeriDNS.Spec.Net.ex_strict_ancestor_denied [9156][347:350]
rfc_proves VeriDNS.Spec.QnameMinimisation.ex_relaxed_probe_fallback [9156][347:350]
rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_timeout [9156][352:354]
rfc_proves VeriDNS.Spec.QnameMinimisation.probe_denial_falls_back [9156][347:350]
rfc_proves VeriDNS.Spec.QnameMinimisation.full_round_no_fallback [9156][352:354]

rfc_out_of_scope [9156][423:443]

check_rfc_doc VeriDNS.Spec.QnameMinimisation.query_storm_dampened [9156][445:465]
  via VeriDNS.Spec.QnameMinimisation.reveal_cap_after_max



-- DEVIATION (findings 051/064): the impl no longer treats a probe-round
-- NXDOMAIN as a subtree denial (relaxed mode, RFC 9156 §3 step 6d non-strict
-- branch / unbound `qname-minimisation-strict: no`).  The 8020 subtree-denial
-- semantics are retained in the MODEL (`ancestorDenied`) and in the aux
-- theorems below, which remain valid statements about the strict machinery.
rfc_proves storeProbeNegative_negWriteRefines [8020][161:165]
rfc_proves VeriDNS.Proof.NameTree.probeAbsent_of_strictDenial [8020][161:165]
rfc_out_of_scope [8020][175:183]
rfc_proves VeriDNS.Spec.Net.ex_strict_ancestor_denied [8020][203:217]

check_rfc_doc VeriDNS.Spec.QnameMinimisation.ent_nodata_not_final [8020][233:243]
  via VeriDNS.Spec.QnameMinimisation.nodata_not_strict_denial

rfc_proves storeProbeNegative_negWriteRefines [8020][245:263]
