import VeriDNS.Proof.ResolveWithIOSound
import VeriDNS.Proof.CooperativeNetwork

/-!
# World-model satisfiability witness

Every soundness capstone in this development (`ioResumeLoop_sound`,
`resolveWithIO_verdict_sound`, `serveDatagram_verdict_sound`, ...) is conditional on the
network axioms `WorldModels` / `WorldModelsTcp`: the assumption that whatever the world's
oracle delivers (once it survives the acceptance chain) agrees with what some model server
would say.  Until this file, no concrete world was ever shown to *satisfy* those packs —
the only trivially-satisfying world is the dead one (`oracle = fun _ _ => none`), so
nothing pinned the capstone stack against vacuity (audit finding W4 #1, severity 5).

This file constructs an explicit honest single-server world and discharges both packs for
it, then instantiates the verdict-soundness capstone at that world as the non-vacuity
certificate:

* The zone: apex `1.` (a digit-only label, so it is a fixpoint of 0x20 case
  randomization) holding one A record `1. 60 IN A 1.2.3.4`, plus the apex SOA/NS records
  required by `Zone.WF`.  The server lives at model address `5.6.7.8`
  (`witnessAddr = ipv4ToAddr 0x05060708`).
* The oracle (`witnessOracle` / `witnessTcpOracle`): decodes the query bytes, answers
  exactly the questions `1. IN A` (checking rcode/tc/authority hygiene — everything the
  honest arm of the pack needs), and replies with the canonical authoritative answer
  (`witnessRespond`, the `treeRespond` answer-arm shape).  All per-RR parse and
  canonicity conjuncts follow from the codec round-trip (`decode_encode`), mirroring how
  `tcpSpoofReply_of_honest` coerces an honest reply into the pack shape.
* `witnessOracle_WorldModels` / `witnessTcpOracle_WorldModelsTcp`: any world running this
  oracle satisfies the full pack against `witnessNet` — every conjunct discharged
  concretely, always through the *honest* disjunct (the spoof arm is never used).
* `witnessOracle_live`: the oracle is not dead — it answers the resolver's own probe
  (`withSecrets (mkAddressQuery witnessQnameWire) rid cid`) for every choice of TXID and
  0x20 seed.
* `resolveWithIO_verdict_sound_witness`: the capstone applied at the witness world with
  every world premise discharged (including `witnessNet_WF`), leaving only the run
  premise — the non-vacuity certificate for the soundness spine.
-/

open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Proof.Adequacy VeriDNS.Proof.WorldNetwork
open VeriDNS.Proof.Message VeriDNS.Proof.DeliveredWire
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache VeriDNS.Spec

namespace VeriDNS.Proof.WorldWitness

/-! # Witness world literals -/

def witnessLabel : ByteArray := ⟨#[0x31]⟩
def witnessName : VeriDNS.Spec.Net.Name := [witnessLabel]
def witnessQnameWire : ByteArray := ⟨#[1, 0x31, 0]⟩
def witnessAddrIp : BitVec 32 := 0x05060708
def witnessAddr : ByteArray := Server.ipv4ToAddr witnessAddrIp

def witnessRRimpl : VeriDNS.Spec.ResourceRecord :=
  { name := witnessQnameWire, type := 1, «class» := 1, ttl := 60, rdlength := 4,
    rdata := ⟨#[1, 2, 3, 4]⟩ }

def witnessIp : VeriDNS.Spec.Net.IPv4 := ⟨1, 2, 3, 4⟩
def witnessARR : VeriDNS.Spec.Net.RR :=
  { owner := witnessName, ttl := 60, rdata := .a witnessIp, cls := RRClass.in }
def witnessSoaRR : VeriDNS.Spec.Net.RR :=
  { owner := witnessName, ttl := 60,
    rdata := .soa witnessName witnessName 1 1 1 1 60, cls := RRClass.in }
def witnessNsRR : VeriDNS.Spec.Net.RR :=
  { owner := witnessName, ttl := 60, rdata := .ns witnessName, cls := RRClass.in }
def witnessZone : VeriDNS.Spec.Net.Zone :=
  { apex := witnessName, records := [witnessSoaRR, witnessNsRR, witnessARR],
    delegations := [], cls := RRClass.in }
def witnessServer : VeriDNS.Spec.Net.Server :=
  { name := witnessName, zones := [witnessZone], cache := [],
    addr := byteAddrToModel witnessAddr, recursionAvailable := false, rtt := 0 }
def witnessNet : VeriDNS.Spec.Net.Network := ⟨[witnessServer]⟩

def witnessRef : VeriDNS.Spec.Net.Response :=
  { aa := true, rcode := RCode.noError, answer := [witnessARR], authority := [],
    additional := [], ra := false, tc := false }

/-! # The witness oracle -/

def witnessGuard (query : Format) : Bool :=
  match query.question[0]? with
  | some qu =>
      qu.qname == witnessQnameWire && qu.qtype == (1 : BitVec 16)
        && qu.qclass == (1 : BitVec 16)
        && query.authority.isEmpty
        && (query.header.rcode == Rcode.noError)
        && (query.header.tc == 0)
  | none => false

def witnessRespond (query : Format) : Format :=
  { query with
      header := { query.header with qr := 1, aa := 1, ancount := 1, arcount := 0 },
      answer := #[VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl],
      additional := #[] }

def witnessOracle : ByteArray → ByteArray → Option (VeriDNS.Spec.Exchanged ByteArray) :=
  fun qb ab =>
    if ab == witnessAddr then
      match Message.decode qb with
      | .ok query =>
        if witnessGuard query then
          some (honestDatagram ab (Message.encode (witnessRespond query)))
        else none
      | .error _ => none
    else none

def witnessTcpOracle : ByteArray → ByteArray → Option ByteArray :=
  fun qb ab =>
    if ab == witnessAddr then
      match Message.decode qb with
      | .ok query =>
        if witnessGuard query then some (Message.encode (witnessRespond query)) else none
      | .error _ => none
    else none

def witnessWorld : World :=
  { clock := 0, ids := fun _ => 0, oracle := witnessOracle, tcpOracle := witnessTcpOracle,
    trace := [], idCtr := 0 }

/-! # Concrete facts about the witness literals -/

theorem witnessLabels_valid : VeriDNS.Proof.DomainName.ValidLabels #[witnessLabel] := by
  intro i h
  have hi : i = 0 := by simpa using h
  subst hi
  show 0 < witnessLabel.size ∧ witnessLabel.size ≤ 63
  decide

theorem witnessWire_labels :
    VeriDNS.Impl.DomainName.wireFormatToLabels witnessQnameWire = .ok #[witnessLabel] :=
  VeriDNS.Proof.DomainName.wireFormat_roundtrip #[witnessLabel] witnessLabels_valid

theorem witness_αName : αName witnessQnameWire = some witnessName := by
  unfold αName
  rw [witnessWire_labels]
  simp [witnessName]

theorem witness_RRWireCanon : RRWireCanon witnessRRimpl :=
  ⟨#[witnessLabel], witnessLabels_valid, by decide, rfl, rfl,
   CanonicalRdata.other (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide)⟩

theorem witness_parseRaw :
    VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord)
      (VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl)
      = some witnessRRimpl :=
  parseRaw_rrBytes witness_RRWireCanon

theorem witness_αRR : αRR witnessRRimpl = some witnessARR := by
  unfold αRR αRData
  rw [show witnessRRimpl.name = witnessQnameWire from rfl,
      show (witnessRRimpl.type.toNat) = 1 from rfl,
      witness_αName]
  rfl

theorem witness_αSection :
    αSection #[VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl]
      = [witnessARR] := by
  unfold αSection
  rw [show (#[VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl]
      : Array ByteArray).toList
    = [VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl] from by simp]
  simp only [List.filterMap_cons, List.filterMap_nil, witness_parseRaw, witness_αRR]

/-! # 0x20 case randomization fixes digit-only names -/

theorem toggle_fix_of_nonalpha {b c : UInt8}
    (h : VeriDNS.Impl.DomainName.toggleCaseByte b = c)
    (hc1 : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 90)) (hc2 : ¬ (97 ≤ c.toNat ∧ c.toNat ≤ 122)) :
    b = c := by
  unfold VeriDNS.Impl.DomainName.toggleCaseByte at h
  split at h
  · rename_i hcond
    exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
      show UInt8.toNat 65 = 65 from rfl, show UInt8.toNat 90 = 90 from rfl] at hcond
    have hh := congrArg UInt8.toNat h
    rw [UInt8.toNat_add] at hh
    simp only [show UInt8.toNat 32 = 32 from rfl] at hh
    omega
  · split at h
    · rename_i hcond
      exfalso
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
        show UInt8.toNat 97 = 97 from rfl, show UInt8.toNat 122 = 122 from rfl] at hcond
      have hh := congrArg UInt8.toNat h
      rw [UInt8.toNat_sub] at hh
      simp only [show UInt8.toNat 32 = 32 from rfl] at hh
      have hb := b.toNat_lt_size
      omega
    · exact h

theorem randomizeCase_witness_inv (seed : UInt16) (n : ByteArray)
    (h : VeriDNS.Impl.DomainName.randomizeCase seed n = witnessQnameWire) :
    n = witnessQnameWire := by
  unfold VeriDNS.Impl.DomainName.randomizeCase at h
  have hdata : n.data.mapIdx (fun i b =>
      if VeriDNS.Impl.DomainName.caseSeedBit seed i
      then VeriDNS.Impl.DomainName.toggleCaseByte b else b) = witnessQnameWire.data :=
    congrArg ByteArray.data h
  have hwsz : witnessQnameWire.data.size = 3 := rfl
  have hsz : n.data.size = 3 := by
    have h1 := congrArg Array.size hdata
    rw [Array.size_mapIdx] at h1
    omega
  have helem : ∀ (i : Nat), i < 3 → n.data[i]? = witnessQnameWire.data[i]? := by
    intro i hi
    have hq := congrArg (fun a => a[i]?) hdata
    simp only [Array.getElem?_mapIdx] at hq
    have hilt : i < n.data.size := by omega
    rw [Array.getElem?_eq_getElem hilt] at hq ⊢
    simp only [Option.map_some] at hq
    -- hq : some (if bit then toggle n.data[i] else n.data[i]) = witnessQnameWire.data[i]?
    have h012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h012 with rfl | rfl | rfl
    · rw [show witnessQnameWire.data[0]? = some 1 from rfl] at hq ⊢
      have hqv := Option.some.inj hq
      refine congrArg some ?_
      split at hqv
      · exact toggle_fix_of_nonalpha hqv (by decide) (by decide)
      · exact hqv
    · rw [show witnessQnameWire.data[1]? = some 0x31 from rfl] at hq ⊢
      have hqv := Option.some.inj hq
      refine congrArg some ?_
      split at hqv
      · exact toggle_fix_of_nonalpha hqv (by decide) (by decide)
      · exact hqv
    · rw [show witnessQnameWire.data[2]? = some 0 from rfl] at hq ⊢
      have hqv := Option.some.inj hq
      refine congrArg some ?_
      split at hqv
      · exact toggle_fix_of_nonalpha hqv (by decide) (by decide)
      · exact hqv
  apply ByteArray.ext
  apply Array.ext
  · omega
  · intro i hi₁ hi₂
    have h3 : i < 3 := by omega
    have := helem i h3
    rw [Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂] at this
    exact Option.some.inj this

/-! # Guard extraction -/

theorem witnessGuard_facts {query : Format} (hg : witnessGuard query = true) :
    ∃ qu, query.question[0]? = some qu
      ∧ qu.qname = witnessQnameWire ∧ qu.qtype = 1 ∧ qu.qclass = 1
      ∧ query.authority = #[]
      ∧ query.header.rcode = Rcode.noError
      ∧ query.header.tc = 0 := by
  unfold witnessGuard at hg
  split at hg
  · rename_i qu hq0
    refine ⟨qu, hq0, ?_⟩
    simp only [Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hg
    refine ⟨byteArray_beq_iff_eq.mp h1, by simpa using h2, by simpa using h3,
      ?_, ?_, by simpa using h6⟩
    · rwa [Array.isEmpty_iff] at h4
    · revert h5
      cases query.header.rcode <;> intro h5 <;> first | rfl | exact absurd h5 (by decide)
  · exact absurd hg (by simp)

/-! # Model-side: the witness server answers -/

theorem witnessServer_answers (now : VeriDNS.Spec.Net.Time) (rd : Bool) :
    ServerAnswers witnessServer now [] true
      ⟨witnessName, QType.rr RRType.a, RRClass.in, rd⟩
      [Step.findZone witnessZone.apex, Step.matchNode witnessName, Step.copyAnswer,
        Step.addAdditional]
      witnessRef := by
  have h := ServerAnswers.answer (s := witnessServer) (now := now) (seen := []) (o := true)
    ⟨witnessName, QType.rr RRType.a, RRClass.in, rd⟩ witnessZone
    [witnessSoaRR, witnessNsRR, witnessARR]
    rfl rfl rfl (Or.inl rfl)
    (by
      intro hh
      exact absurd (show ([witnessARR] : List VeriDNS.Spec.Net.RR) = [] from hh) (by decide))
  exact h

theorem witness_serverAt :
    serverAt witnessNet (byteAddrToModel witnessAddr) = some witnessServer := rfl

theorem witness_linkReach (ra : String) :
    linkReach witnessNet VeriDNS.Proof.WorldNetwork.allUp ra (byteAddrToModel witnessAddr) = true := by
  unfold linkReach
  rw [show reachOf witnessNet VeriDNS.Proof.WorldNetwork.allUp (byteAddrToModel witnessAddr) = true from rfl,
    Bool.or_true]

theorem witness_truncate (ednsBuf : Nat) (rd : Bool) :
    truncateToCap (negotiatedUdp ednsBuf)
      ⟨witnessName, QType.rr RRType.a, RRClass.in, rd⟩ witnessRef = (witnessRef, false) := by
  unfold truncateToCap
  rw [if_neg]
  intro hlt
  rw [Nat.blt_eq] at hlt
  have hfloor : udpMax ≤ negotiatedUdp ednsBuf := negotiatedUdp_floor ednsBuf
  have hmw : messageWire ⟨witnessName, QType.rr RRType.a, RRClass.in, rd⟩ witnessRef
      = messageWire ⟨witnessName, QType.rr RRType.a, RRClass.in, false⟩ witnessRef := rfl
  rw [hmw] at hlt
  have hle : messageWire ⟨witnessName, QType.rr RRType.a, RRClass.in, false⟩ witnessRef
      ≤ 512 := by decide
  have hudp : udpMax = 512 := rfl
  omega

/-! # Response codec round trip and sanitize identity -/

theorem witnessRespond_roundtrips {query : Format}
    (hsent : Message.decode (Message.encode query) = .ok query) :
    Message.decode (Message.encode (witnessRespond query)) = .ok (witnessRespond query) := by
  obtain ⟨hqd, han, hns, har, hvqf, hcaA, hcaN, hcaD⟩ := decode_ok_wire_facts hsent
  refine decode_encode _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hqd
  · show (1 : BitVec 16).toNat
      = (#[VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl]
          : Array ByteArray).size
    decide
  · exact hns
  · show (0 : BitVec 16).toNat = (#[] : Array ByteArray).size
    decide
  · exact validQuestionsOfForall hvqf
  · refine canonicalSection_validRRBytes ?_
    show CanonicalSection
      #[VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl]
    intro b hb
    have hbe : b = VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
        witnessRRimpl := by simpa using hb
    subst hbe
    exact canonicalRR_rrBytes witness_RRWireCanon
  · exact canonicalSection_validRRBytes hcaN
  · exact canonicalSection_validRRBytes canonicalSection_empty

theorem witnessRespond_sanitize {query : Format} (hauth : query.authority = #[]) :
    Server.sanitizeTtlsCap (witnessRespond query) = some (witnessRespond query) := by
  refine sanitizeTtlsCap_eq_self _ ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact absurd hb (by simp [witnessRespond])
  · show (0 : BitVec 16) = BitVec.ofNat 16 (#[] : Array ByteArray).size
    decide
  · intro b hb
    have hbe : b = VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord) witnessRRimpl := by
      simpa [witnessRespond] using hb
    subst hbe
    exact capTtlRR_rrBytes ⟨witness_RRWireCanon, by decide⟩
  · intro b hb
    rw [show (witnessRespond query).authority = query.authority from rfl, hauth] at hb
    exact absurd hb (by simp)
  · intro b hb
    exact absurd hb (by simp [witnessRespond])

/-! # The honest-arm core -/

theorem witness_honest_core
    (ra : String) (ednsBuf : Nat) (now : VeriDNS.Spec.Net.Time)
    (q : Format) (id cid : UInt16)
    (query : Format) (resp0 resp₀ resp : Format) (qm : VeriDNS.Spec.Net.Query)
    (hdq : Message.decode (Message.encode (Server.withSecrets q id cid)) = .ok query)
    (hg : witnessGuard query = true)
    (hdecode : Message.decode (Message.encode (witnessRespond query)) = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (hacc : Server.acceptResponse (Server.withSecrets q id cid) resp₀ = some resp)
    (hαq : αQuery q = some qm) :
    ∃ srv tr ref, serverAt witnessNet (byteAddrToModel witnessAddr) = some srv
      ∧ ServerAnswers srv now [] true qm tr ref
      ∧ RespAgree (αResp resp) ref
      ∧ linkReach witnessNet VeriDNS.Proof.WorldNetwork.allUp ra
          (byteAddrToModel witnessAddr) = true
      ∧ truncateToCap (negotiatedUdp ednsBuf) qm ref = (ref, false)
      ∧ (αResp resp).isReferral = ref.isReferral
      ∧ (VeriDNS.Spec.Net.cnameRR qm.qname (αResp resp).answer = none
          ↔ VeriDNS.Spec.Net.cnameRR qm.qname ref.answer = none)
      ∧ αSection resp.answer = ref.answer
      ∧ (∀ b ∈ resp.answer.toList, ∃ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
            ∧ αRR rr ≠ none)
      ∧ (∀ b ∈ resp.authority.toList, ∃ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
            ∧ αRR rr ≠ none)
      ∧ (∀ sname : ByteArray, VeriDNS.Impl.Server.respInBailiwick sname resp = true →
          VeriDNS.Impl.Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
            resp.authority sname = (VeriDNS.Spec.Net.referralCut ref).length)
      ∧ (∀ b ∈ resp.authority.toList, ∀ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == (2 : BitVec 16)) = true →
          ∃ na, αName rr.rdata = some na
            ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
            ∧ (∀ x ∈ na, x.size ≤ 63))
      ∧ (VeriDNS.Impl.Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord)
          resp.authority).toList.Nodup
      ∧ αSection resp.authority = ref.authority
      ∧ αSection resp.additional = ref.additional
      ∧ ((resp.header.aa == 1) = ref.aa)
      ∧ (∀ b ∈ resp.additional.toList, ∃ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr
            ∧ αRR rr ≠ none)
      ∧ ((resp.header.tc == 1) = ref.tc) := by
  obtain ⟨qu, hq0, hquname, hqutype, hquclass, hauth, hrcode, htcq⟩ := witnessGuard_facts hg
  -- identify resp0 with the canonical response
  have hsentQ : Message.decode (Message.encode query) = .ok query := decode_encode_of_decode hdq
  have hrt := witnessRespond_roundtrips hsentQ
  rw [hrt] at hdecode
  have hresp0 : resp0 = witnessRespond query := (Except.ok.inj hdecode).symm
  subst hresp0
  -- identify resp₀
  rw [witnessRespond_sanitize hauth] at hsani
  have hresp₀ : resp₀ = witnessRespond query := (Option.some.inj hsani).symm
  subst hresp₀
  -- identify resp, and extract the question-match facts
  unfold Server.acceptResponse at hacc
  split at hacc
  case isFalse => exact absurd hacc (by simp)
  rename_i hcond
  have hrespEq : resp = witnessRespond query := (Option.some.inj hacc).symm
  subst hrespEq
  simp only [Bool.and_eq_true] at hcond
  have hqmatch := hcond.1.1.2
  obtain ⟨qu₀, hq0', hn0, hqt0, hqc0⟩ := αQuery_fields hαq
  have hq0w : (witnessRespond query).question[0]? = some qu := hq0
  have hsq : (Server.withSecrets q id cid).question[0]?
      = some { qu₀ with qname := VeriDNS.Impl.DomainName.randomizeCase cid qu₀.qname } := by
    show (q.question.map (fun x =>
      { x with qname := VeriDNS.Impl.DomainName.randomizeCase cid x.qname }))[0]? = _
    rw [Array.getElem?_map, hq0']
    rfl
  unfold Server.questionMatches at hqmatch
  simp only [hq0w, hsq, Bool.and_eq_true] at hqmatch
  obtain ⟨⟨hbn, hbt⟩, hbc⟩ := hqmatch
  -- pin the pre-randomization question to the witness question
  have hqn0 : qu₀.qname = witnessQnameWire := by
    apply randomizeCase_witness_inv cid
    have h1 := byteArray_beq_iff_eq.mp hbn
    rw [hquname] at h1
    exact h1.symm
  have hqt0' : qu₀.qtype = 1 := by
    have h1 : qu.qtype = qu₀.qtype := by simpa using hbt
    rw [hqutype] at h1
    exact h1.symm
  have hqc0' : qu₀.qclass = 1 := by
    have h1 : qu.qclass = qu₀.qclass := by simpa using hbc
    rw [hquclass] at h1
    exact h1.symm
  -- pin the model query
  rw [hqn0, witness_αName] at hn0
  rw [hqt0'] at hqt0
  rw [hqc0'] at hqc0
  obtain ⟨qmn, qmt, qmc, qmrd⟩ := qm
  have hqmn : qmn = witnessName := (Option.some.inj hn0).symm
  have hqmt : qmt = QType.rr RRType.a := by
    have h1 : αQType (1 : BitVec 16) = some (QType.rr RRType.a) := rfl
    rw [h1] at hqt0
    exact (Option.some.inj hqt0).symm
  have hqmc : qmc = RRClass.in := by
    have h1 : αClass (1 : BitVec 16) = some RRClass.in := rfl
    rw [h1] at hqc0
    exact (Option.some.inj hqc0).symm
  subst hqmn hqmt hqmc
  -- assemble
  have hauthW : (witnessRespond query).authority = (#[] : Array ByteArray) := hauth
  refine ⟨witnessServer, _, witnessRef, witness_serverAt, witnessServer_answers now qmrd,
    ?_, witness_linkReach ra, witness_truncate ednsBuf qmrd, ?_, ?_, witness_αSection,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · -- RespAgree
    refine RespAgree.of_eq ?_ ?_
    · show αRCode (witnessRespond query).header.rcode = RCode.noError
      rw [show (witnessRespond query).header.rcode = query.header.rcode from rfl, hrcode]
      rfl
    · exact witness_αSection
  · -- isReferral
    have hLHS : (αResp (witnessRespond query)).isReferral = false :=
      isReferral_false_of_aa _ rfl
    rw [hLHS]
    rfl
  · -- cnameRR iff
    have hansA : (αResp (witnessRespond query)).answer = [witnessARR] := witness_αSection
    rw [hansA]
    exact Iff.rfl
  · -- per-RR answer facts
    intro b hb
    have hbe : b = VeriDNS.Spec.RRParse.rrBytes (RR := VeriDNS.Spec.ResourceRecord)
        witnessRRimpl := by simpa [witnessRespond] using hb
    subst hbe
    exact ⟨witnessRRimpl, witness_parseRaw, by rw [witness_αRR]; simp⟩
  · -- per-RR authority facts (vacuous)
    intro b hb
    rw [hauthW] at hb
    exact absurd hb (by simp)
  · -- delegation match count
    intro sname _
    rw [hauthW]
    rfl
  · -- NS-rdata canonicity (vacuous)
    intro b hb
    rw [hauthW] at hb
    exact absurd hb (by simp)
  · -- extractNsNames nodup
    rw [hauthW]
    simp [VeriDNS.Impl.Resolver.extractNsNames]
  · -- authority abstraction
    rw [hauthW]
    rfl
  · -- additional abstraction
    rfl
  · -- per-RR additional facts (vacuous)
    intro b hb
    exact absurd hb (by simp [witnessRespond])
  · -- tc
    show ((witnessRespond query).header.tc == 1) = witnessRef.tc
    rw [show (witnessRespond query).header.tc = query.header.tc from rfl, htcq]
    rfl

/-! # The witness world models the witness network -/

theorem witnessOracle_WorldModels (ra : String) (ednsBuf : Nat) (now : VeriDNS.Spec.Net.Time)
    (w : World) (hor : w.oracle = witnessOracle) :
    WorldModels witnessNet VeriDNS.Proof.WorldNetwork.allUp ra ednsBuf now w := by
  intro q id cid ab d bytes resp0 resp₀ resp qm horacle hd hdec hsan hacc hαq
  rw [hor] at horacle
  unfold witnessOracle at horacle
  split at horacle
  case isFalse => exact absurd horacle (by simp)
  rename_i habq
  have hab : ab = witnessAddr := byteArray_beq_iff_eq.mp habq
  subst hab
  split at horacle
  case h_2 => exact absurd horacle (by simp)
  rename_i query hdq
  split at horacle
  case isFalse => exact absurd horacle (by simp)
  rename_i hg
  have hdEq : honestDatagram witnessAddr (Message.encode (witnessRespond query)) = d :=
    Option.some.inj horacle
  rw [← hdEq, acceptExchanged_honestDatagram] at hd
  have hbytes : bytes = Message.encode (witnessRespond query) := (Option.some.inj hd).symm
  subst hbytes
  exact Or.inl (witness_honest_core ra ednsBuf now q id cid query resp0 resp₀ resp qm
    hdq hg hdec hsan hacc hαq)

theorem witnessTcpOracle_WorldModelsTcp (ra : String) (ednsBuf : Nat)
    (now : VeriDNS.Spec.Net.Time) (w : World) (hor : w.tcpOracle = witnessTcpOracle) :
    WorldModelsTcp witnessNet VeriDNS.Proof.WorldNetwork.allUp ra ednsBuf now w := by
  intro q id cid ab bytes resp0 resp₀ resp qm horacle hdec hsan hacc hαq
  rw [hor] at horacle
  unfold witnessTcpOracle at horacle
  split at horacle
  case isFalse => exact absurd horacle (by simp)
  rename_i habq
  have hab : ab = witnessAddr := byteArray_beq_iff_eq.mp habq
  subst hab
  split at horacle
  case h_2 => exact absurd horacle (by simp)
  rename_i query hdq
  split at horacle
  case isFalse => exact absurd horacle (by simp)
  rename_i hg
  have hbytes : bytes = Message.encode (witnessRespond query) := (Option.some.inj horacle).symm
  subst hbytes
  obtain ⟨srv, tr, ref, h1, h2, h3, h4, _, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18⟩ :=
    witness_honest_core ra ednsBuf now q id cid query resp0 resp₀ resp qm
      hdq hg hdec hsan hacc hαq
  exact ⟨srv, tr, ref, h1, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18⟩

theorem witnessWorld_WorldModels (ra : String) (ednsBuf : Nat) (now : VeriDNS.Spec.Net.Time) :
    WorldModels witnessNet VeriDNS.Proof.WorldNetwork.allUp ra ednsBuf now witnessWorld :=
  witnessOracle_WorldModels ra ednsBuf now witnessWorld rfl

theorem witnessWorld_WorldModelsTcp (ra : String) (ednsBuf : Nat)
    (now : VeriDNS.Spec.Net.Time) :
    WorldModelsTcp witnessNet VeriDNS.Proof.WorldNetwork.allUp ra ednsBuf now witnessWorld :=
  witnessTcpOracle_WorldModelsTcp ra ednsBuf now witnessWorld rfl

/-! # Witness network well-formedness -/

theorem witnessNet_WF : witnessNet.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hse : s = witnessServer := by simpa [witnessNet] using hs
    subst hse
    refine ⟨?_, ?_⟩
    · intro z₁ h₁ z₂ h₂ _ _
      have e₁ : z₁ = witnessZone := by simpa [witnessServer] using h₁
      have e₂ : z₂ = witnessZone := by simpa [witnessServer] using h₂
      rw [e₁, e₂]
    · intro z hz
      have hze : z = witnessZone := by simpa [witnessServer] using hz
      subst hze
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  · intro s hs z hz d hd
    have hse : s = witnessServer := by simpa [witnessNet] using hs
    subst hse
    have hze : z = witnessZone := by simpa [witnessServer] using hz
    subst hze
    exact absurd hd (by simp [witnessZone])
  · intro s hs z hz d hd
    have hse : s = witnessServer := by simpa [witnessNet] using hs
    subst hse
    have hze : z = witnessZone := by simpa [witnessServer] using hz
    subst hze
    exact absurd hd (by simp [witnessZone])

/-! # Non-vacuity certificate: the verdict-soundness capstone at the witness world -/

def witnessQuery : Format := Server.mkAddressQuery witnessQnameWire

def witnessQm : VeriDNS.Spec.Net.Query :=
  { qname := witnessName, qtype := QType.rr RRType.a, qclass := RRClass.in, rd := false }

theorem resolveWithIO_verdict_sound_witness
    (ra : String) (ednsBuf : Nat) (rttOf : String → Nat) (budget : UInt32)
    (n fuel' depth : Nat) (now0 : UInt32)
    (hclock : now0.toNat + 604800 < 2 ^ 32)
    (w w' : World) (resp : Format) (cout : DnsCache)
    (horacle : w.oracle = witnessOracle)
    (htcp : w.tcpOracle = witnessTcpOracle)
    (hrun : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        witnessQuery (default : DnsSList) DnsCache.empty now0 fuel' depth budget) w
      = some ((.ok resp, cout), w')) :
    ∃ slist v cOut coutM,
      CacheRefines cOut (αCache DnsCache.empty)
      ∧ VeriDNS.Proof.Refinement.HasVerdictAt witnessNet VeriDNS.Proof.WorldNetwork.allUp
          ra ednsBuf rttOf (αTime now0) [] [] cOut slist witnessQm v coutM
      ∧ (αResp resp).rcode = v.rcode
      ∧ (αResp resp).answer = v.answer
      ∧ CacheRefines (αCache cout) coutM
      ∧ WorldModels witnessNet VeriDNS.Proof.WorldNetwork.allUp ra ednsBuf (αTime now0) w' := by
  have hNegWf : CacheNegWf DnsCache.empty (1 : BitVec 16) := by
    intro e he
    simp [DnsCache.empty] at he
  obtain ⟨slist, v, cOut, coutM, hc1, hc2, hc3, hc4, hc5, hc6, _⟩ :=
    resolveWithIO_verdict_sound witnessNet VeriDNS.Proof.WorldNetwork.allUp ra ednsBuf rttOf
      (default : DnsSList) budget witnessNet_WF GluelessProv_default
      n witnessQuery ⟨witnessQnameWire, 1, 1⟩ witnessQm RRType.a depth fuel'
      DnsCache.empty w w' now0 resp cout
      rfl
      witness_αName
      rfl
      rfl
      (by decide)
      rfl
      rfl
      (by
        intro x hx
        have hxe : x = witnessLabel := by simpa [witnessQm, witnessName] using hx
        subst hxe
        decide)
      (by decide)
      rfl
      (by intro h; exact QType.noConfusion h)
      rfl
      (CacheWf_empty now0)
      CacheNsCanon_empty
      CacheCnameCanon_empty
      (fun _ he => absurd he (by simp [DnsCache.empty]))
      CacheNsDistinct_empty
      VeriDNS.Proof.NameTree.oneExpiry_empty
      (by simp [DnsCache.empty, DnsCache.capacity])
      hNegWf
      hclock
      (witnessOracle_WorldModels ra ednsBuf (αTime now0) w horacle)
      (witnessTcpOracle_WorldModelsTcp ra ednsBuf (αTime now0) w htcp)
      hrun
  exact ⟨slist, v, cOut, coutM, hc1, hc2, hc3, hc4, hc5, hc6⟩

/-! # The witness oracle is live: it answers the resolver's own probe -/

theorem randomizeCase_witness_fix (seed : UInt16) :
    VeriDNS.Impl.DomainName.randomizeCase seed witnessQnameWire = witnessQnameWire := by
  unfold VeriDNS.Impl.DomainName.randomizeCase
  apply ByteArray.ext
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [Array.getElem_mapIdx]
    have hws : witnessQnameWire.data.size = 3 := rfl
    have h3 : i < 3 := by omega
    have h012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h012 with rfl | rfl | rfl <;>
      (split
       · first
          | exact (show VeriDNS.Impl.DomainName.toggleCaseByte 1 = 1 by decide)
          | exact (show VeriDNS.Impl.DomainName.toggleCaseByte 0x31 = 0x31 by decide)
          | exact (show VeriDNS.Impl.DomainName.toggleCaseByte 0 = 0 by decide)
       · rfl)

theorem witnessProbe_question (rid cid : UInt16) :
    (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid).question
      = #[⟨witnessQnameWire, 1, 1⟩] := by
  show ((#[⟨witnessQnameWire, 1, 1⟩] : Array VeriDNS.Spec.Question).map
    (fun x => { x with qname := VeriDNS.Impl.DomainName.randomizeCase cid x.qname }))
      = #[⟨witnessQnameWire, 1, 1⟩]
  simp [randomizeCase_witness_fix]

theorem witnessProbe_roundtrips (rid cid : UInt16) :
    Message.decode (Message.encode
        (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid))
      = .ok (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid) := by
  refine decode_encode _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (1 : BitVec 16).toNat
      = (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid).question.size
    rw [witnessProbe_question]
    decide
  · show (0 : BitVec 16).toNat = (#[] : Array ByteArray).size
    decide
  · show (0 : BitVec 16).toNat = (#[] : Array ByteArray).size
    decide
  · show (0 : BitVec 16).toNat = (#[] : Array ByteArray).size
    decide
  · rw [show ValidQuestions
        (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid).question
      = ValidQuestions #[⟨witnessQnameWire, 1, 1⟩] from by rw [witnessProbe_question]]
    refine validQuestionsOfForall (fun i => ?_)
    have hq : (#[⟨witnessQnameWire, 1, 1⟩] : Array VeriDNS.Spec.Question)[i]
        = ⟨witnessQnameWire, 1, 1⟩ := by
      simp
    rw [hq]
    exact questionFromLabels_of_canonicalName
      ⟨#[witnessLabel], witnessLabels_valid, by decide, rfl⟩
  · exact canonicalSection_validRRBytes canonicalSection_empty
  · exact canonicalSection_validRRBytes canonicalSection_empty
  · exact canonicalSection_validRRBytes canonicalSection_empty

theorem witnessGuard_probe (rid cid : UInt16) :
    witnessGuard (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid) = true := by
  unfold witnessGuard
  rw [show (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid).question[0]?
    = some ⟨witnessQnameWire, 1, 1⟩ from by rw [witnessProbe_question]; rfl]
  rfl

theorem witnessOracle_live (rid cid : UInt16) :
    witnessOracle (Message.encode
        (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid)) witnessAddr
      = some (honestDatagram witnessAddr (Message.encode (witnessRespond
          (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid)))) := by
  unfold witnessOracle
  rw [if_pos (byteArray_beq_iff_eq.mpr rfl), witnessProbe_roundtrips]
  simp only [witnessGuard_probe rid cid, if_true]

theorem witnessTcpOracle_live (rid cid : UInt16) :
    witnessTcpOracle (Message.encode
        (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid)) witnessAddr
      = some (Message.encode (witnessRespond
          (Server.withSecrets (Server.mkAddressQuery witnessQnameWire) rid cid))) := by
  unfold witnessTcpOracle
  rw [if_pos (byteArray_beq_iff_eq.mpr rfl), witnessProbe_roundtrips]
  simp only [witnessGuard_probe rid cid, if_true]

end VeriDNS.Proof.WorldWitness
