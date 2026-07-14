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
rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_strictNxdomain [9156][347:350]
rfc_proves VeriDNS.Spec.Net.ex_strict_ancestor_denied [9156][347:350]
rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_timeout [9156][352:354]

rfc_out_of_scope [9156][423:443]

check_rfc_doc VeriDNS.Spec.QnameMinimisation.query_storm_dampened [9156][445:465]
  via VeriDNS.Spec.QnameMinimisation.reveal_cap_after_max



rfc_proves VeriDNS.Proof.FreeIO.run_ioResumeLoop_strictNxdomain [8020][161:165]
rfc_proves storeProbeNegative_negWriteRefines [8020][161:165]
rfc_proves VeriDNS.Proof.NameTree.probeAbsent_of_strictDenial [8020][161:165]
rfc_out_of_scope [8020][175:183]
rfc_proves VeriDNS.Spec.Net.ex_strict_ancestor_denied [8020][203:217]

check_rfc_doc VeriDNS.Spec.QnameMinimisation.ent_nodata_not_final [8020][233:243]
  via VeriDNS.Spec.QnameMinimisation.nodata_not_strict_denial

rfc_proves storeProbeNegative_negWriteRefines [8020][245:263]
