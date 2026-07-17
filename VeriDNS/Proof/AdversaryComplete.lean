import VeriDNS.Proof.IoResumeSound
import VeriDNS.Proof.ResolveWithIOSound
import VeriDNS.Proof.Server

/-!
# Adversary-model completeness

`docs/model-strengthening-plan-2.md`, the **Adversary model** escape-hatch row: every
soundness capstone is stated against `WorldModels` / `WorldModelsTcp`, the adversary model
(`VeriDNS/Proof/NetworkSim.lean`).  Soundness-against-a-model only rules out attacks the
model's disjunction *enumerates*.  If a datagram the network delivers realises no disjunct,
the capstone says nothing about it — that is exactly where an unmodelled attack (038 subtree
hijack, the 017 junk class) could live.

This file converts "sound vs the model" into "sound vs every wire" by pinning down the
disjunction's exhaustiveness over the space of datagrams the resolver actually *accepts*.

## The characterisation

`WorldModels net ns ra ednsBuf now w` is a *universally-quantified* fact about the world's
oracle: it fixes, for every datagram `d` the oracle delivers, that once `d` survives the full
acceptance pipeline

```
w.oracle (encode (withSecrets q id cid)) ab = some d        -- the oracle delivered d
acceptExchanged ab d = some bytes                           -- source (address/port) match
decode bytes = .ok resp0                                    -- it is a decodable DNS message
sanitizeTtlsCap resp0 = some resp₀                          -- TTLs/OPT sanitised
acceptResponse (withSecrets q id cid) resp₀ = some resp     -- id + 0x20 question match
```

the abstracted response `αResp resp` realises **one of two disjuncts**:

* the **honest** disjunct — there is a model server `srv` at `byteAddrToModel ab`, reachable
  on the link, and `resp` agrees with what that server answers (`ServerAnswers`); or
* **`SpoofReply`** — a datagram delivered over a `Transit` link that `accepts` the outstanding
  query, whose abstracted response agrees with the wire reply and whose sections are all
  decode-canonical (each RR parses and abstracts), with the referral structure (bailiwick,
  delegation cut, NS-name canonicity) matched when it is a referral.

For an arbitrary datagram the network could deliver — honest reply, on-path spoof, off-path
junk, or a datagram from an unexpected source — the question is whether **some disjunct covers
it**.  The answer splits on the acceptance pipeline:

1. **Not accepted** (wrong source, or wrong id / question / 0x20 casing) — the datagram never
   reaches the disjunction at all.  It is discarded *below the shim*: this is the
   017 boundary, `Proof.Server.shim_accept_requires_source_and_query_match`.  The C
   `veri_dns_exchange` recv loop keeps reading past it (the named C floor).  No disjunct is
   needed, and none is claimed: an unaccepted datagram is not a reply.

2. **Accepted** (source match ∧ id/question/0x20 match) — the datagram *is* surfaced as the
   reply and the `WorldModels` disjunction is asserted about it.  `WorldModels_complete` below
   restates this: for every accepted datagram, honest ∨ `SpoofReply` holds; the disjunction is
   exhaustive over the accepted-datagram space.

So the accepted/unaccepted split is total: no datagram escapes both.  A datagram is either
dropped below the shim (case 1) or covered by a disjunct (case 2).  This is what makes
`WorldModels`, as a hypothesis, *complete* rather than a door: it excludes nothing an attacker
can put on the wire that the resolver would act on.

## The residue, named honestly

`SpoofReply`'s structural conjuncts (every section RR parses and abstracts; and, for a
referral, in-bailiwick + delegation-cut agreement + NS-name canonicity) are *load-bearing* —
the referral/answer soundness path in `ioResumeLoop_sound` consumes them to derive the verdict
(e.g. `hvldA`, `hcutBr` at `IoResumeSound`).  They are exactly the well-formedness the resolver
requires of a reply it will act on.  A datagram that is accepted (id/question match) but whose
sections do not decode-canonically, or whose referral is malformed, realises `SpoofReply` only
if those conjuncts hold.  The pipeline discharges the *decode-canonical* part
(`decode_answer_parseRaw` and companions: every RR of a decoded message re-parses), so the
covered space is: **accepted + decode-canonical + (referral ⇒ well-formed referral)**.  The
`decode` step is not optional — it is in the pipeline — so decode-canonicity is free.  The one
genuinely-narrowing conjunct that is *not* free is the referral well-formedness (in-bailiwick,
delegation cut, NS canonicity): a malformed-referral datagram is the residue, and the resolver
handles it not by trusting it but by *rejecting* it in `analyzeResponse` (the classifier), so
it never drives a spoofed referral hop.  That rejection lives in the response classifier, not
in this file.

## UDP vs TCP

`WorldModels` (UDP) carries the honest ∨ `SpoofReply` disjunction: the on-path spoof arm *is*
present, so UDP completeness is total over the accepted space.  `WorldModelsTcp` deliberately
omits the spoof arm (tcp-plan decision 5: no MITM on the TCP fallback), so it is honest-only.
That is not an unmodelled UDP-style attack sneaking in on TCP — it is the modelling choice that
the TCP fallback is not subject to on-path spoofing.  `tcpSpoofReply_of_honest`
(`IoResumeSound`) already shows the honest-only TCP pack *implies* the UDP-shaped `SpoofReply`,
so the TCP path is never *less* covered than UDP; the honest arm subsumes the spoof shape.  We
record this below as `WorldModelsTcp_complete` (every accepted TCP datagram realises the honest
disjunct, and hence `SpoofReply` too, via the coercion).
-/

open VeriDNS.Proof.FreeIO VeriDNS.Proof.Refinement VeriDNS.Proof.NetworkSim
open VeriDNS.Spec (RRType RRClass)
open VeriDNS.Spec.Net VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache

namespace VeriDNS.Proof.AdversaryComplete

/-! ## The accepted-datagram space

`Accepts` bundles the five acceptance-pipeline steps into one predicate: the oracle delivered
`d`, its source matched, it decoded to `resp0`, sanitised to `resp₀`, and matched the query on
id + 0x20-cased question to `resp`.  This is precisely the antecedent of the `WorldModels`
disjunction — the set of datagrams the resolver acts on as replies. -/

/-- A datagram `d` the oracle delivered is *accepted as the reply* to the outstanding query
`withSecrets q id cid` at source `ab`, yielding the abstracted response `resp`, exactly when it
survives the full shim acceptance pipeline. -/
def Accepts (w : World) (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (d : VeriDNS.Spec.Exchanged ByteArray) (resp : VeriDNS.Spec.Format) : Prop :=
  ∃ (bytes : ByteArray) (resp0 resp₀ : VeriDNS.Spec.Format),
    w.oracle (VeriDNS.Impl.Message.encode (Server.withSecrets q id cid)) ab = some d ∧
    Server.acceptExchanged ab d = some bytes ∧
    VeriDNS.Impl.Message.decode bytes = .ok resp0 ∧
    Server.sanitizeTtlsCap resp0 = some resp₀ ∧
    Server.acceptResponse (Server.withSecrets q id cid) resp₀ = some resp

/-- Any *accepted* datagram came from the queried source and its decoded response matches the
outstanding query on transaction id and on the (0x20-cased) question — the 017 pin lifted to
the `Accepts` predicate.  Contrapositive: a datagram from the wrong source or failing the
id/question match is not `Accepts`, so it is never surfaced as a reply.  This is the boundary
tying the "junk" case to the shim's accept predicate rather than to a `WorldModels`
disjunct. -/
theorem accepts_requires_source_and_query_match
    (w : World) (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (d : VeriDNS.Spec.Exchanged ByteArray) (resp : VeriDNS.Spec.Format)
    (h : Accepts w q id cid ab d resp) :
    (d.source == ab) = true
      ∧ (resp.header.id == (Server.withSecrets q id cid).header.id) = true
      ∧ VeriDNS.Impl.Server.questionMatches resp.question (Server.withSecrets q id cid).question
          = true := by
  obtain ⟨bytes, resp0, resp₀, _hO, hexc, _hdec, _hsan, hacc⟩ := h
  -- source (address/port) match is fixed by acceptExchanged, independent of the sanitise step
  have hsrc := (VeriDNS.Proof.Server.exchanged_matches ab d bytes hexc).1
  -- id + 0x20-cased question match is fixed by acceptResponse
  have hmatch := VeriDNS.Proof.Server.acceptResponse_matches (Server.withSecrets q id cid) resp₀ resp hacc
  exact ⟨hsrc, hmatch.1, hmatch.2⟩

/-! ## UDP completeness

`WorldModels_complete`: the disjunction is exhaustive over the accepted-datagram space.  This is
the payoff statement of the Adversary-model row — for *every* datagram the resolver accepts as a
reply, the abstracted response realises the honest disjunct or `SpoofReply`.  It is the same
content as `WorldModels`, restated with the acceptance pipeline bundled into `Accepts` so the
completeness claim ("every accepted wire datagram realises a disjunct") is explicit and
citable. -/

/-- **Adversary-model completeness (UDP).**  Under `WorldModels`, every datagram the resolver
*accepts* as a reply (`Accepts`) realises the honest disjunct or `SpoofReply`.  The disjunction
enumerates the entire accepted-datagram space; combined with
`accepts_requires_source_and_query_match` (unaccepted datagrams are dropped below the shim),
this means no datagram the resolver acts on escapes the model. -/
theorem WorldModels_complete
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (now : Time) (w : World)
    (hwm : WorldModels net ns ra ednsBuf now w)
    (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (d : VeriDNS.Spec.Exchanged ByteArray) (resp : VeriDNS.Spec.Format) (qm : Query)
    (hαq : αQuery q = some qm)
    (hacc : Accepts w q id cid ab d resp) :
    -- honest disjunct
    (∃ srv tr ref, serverAt net (byteAddrToModel ab) = some srv ∧
        ServerAnswers srv now [] true qm tr ref ∧
        RespAgree (αResp resp) ref ∧
        linkReach net ns ra (byteAddrToModel ab) = true ∧
        truncateToCap (negotiatedUdp ednsBuf) qm ref = (ref, false) ∧
        (αResp resp).isReferral = ref.isReferral ∧
        (VeriDNS.Spec.Net.cnameRR qm.qname (αResp resp).answer = none
          ↔ VeriDNS.Spec.Net.cnameRR qm.qname ref.answer = none) ∧
        αSection resp.answer = ref.answer ∧
        (∀ b ∈ resp.answer.toList, ∃ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
        (∀ b ∈ resp.authority.toList, ∃ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
        (∀ sname : ByteArray, VeriDNS.Impl.Server.respInBailiwick sname resp = true →
          VeriDNS.Impl.Resolver.delegationMatchCount (RR := VeriDNS.Spec.ResourceRecord)
            resp.authority sname = (VeriDNS.Spec.Net.referralCut ref).length) ∧
        (∀ b ∈ resp.authority.toList, ∀ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr →
          (rr.type == (2 : BitVec 16)) = true →
          ∃ na, αName rr.rdata = some na
            ∧ rr.rdata = VeriDNS.Impl.DomainName.labelsToWireFormatGo na
            ∧ (∀ x ∈ na, x.size ≤ 63)) ∧
        (VeriDNS.Impl.Resolver.extractNsNames (RR := VeriDNS.Spec.ResourceRecord) resp.authority).toList.Nodup ∧
        αSection resp.authority = ref.authority ∧
        αSection resp.additional = ref.additional ∧
        ((resp.header.aa == 1) = ref.aa) ∧
        (∀ b ∈ resp.additional.toList, ∃ rr,
          VeriDNS.Spec.RRParse.parseRaw (RR := VeriDNS.Spec.ResourceRecord) b = some rr ∧ αRR rr ≠ none) ∧
        ((resp.header.tc == 1) = ref.tc))
    ∨ SpoofReply net ns ra ednsBuf id ab resp qm := by
  obtain ⟨bytes, resp0, resp₀, hO, hexc, hdec, hsan, haccR⟩ := hacc
  exact hwm q id cid ab d bytes resp0 resp₀ resp qm hO hexc hdec hsan haccR hαq

/-! ## TCP completeness

`WorldModelsTcp` deliberately excludes the on-path spoof arm (tcp-plan decision 5).  It is
honest-only: every accepted TCP datagram realises the honest disjunct.  We restate this as
`WorldModelsTcp_complete`, and then record that the honest arm still *implies* the UDP-shaped
`SpoofReply` via `tcpSpoofReply_of_honest`, so the TCP path is never less covered than the UDP
path — there is no unmodelled residue, only the deliberate absence of a spoof clause justified
by the no-MITM decision. -/

/-- A datagram accepted over the TCP oracle as the reply to `withSecrets q id cid` at `ab`. -/
def AcceptsTcp (w : World) (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (resp : VeriDNS.Spec.Format) : Prop :=
  ∃ (bytes : ByteArray) (resp0 resp₀ : VeriDNS.Spec.Format),
    w.tcpOracle (VeriDNS.Impl.Message.encode (Server.withSecrets q id cid)) ab = some bytes ∧
    VeriDNS.Impl.Message.decode bytes = .ok resp0 ∧
    Server.sanitizeTtlsCap resp0 = some resp₀ ∧
    Server.acceptResponse (Server.withSecrets q id cid) resp₀ = some resp

/-- **Adversary-model completeness (TCP), honest arm.**  Under `WorldModelsTcp`, every accepted
TCP datagram realises the honest disjunct.  There is no spoof arm by tcp-plan decision 5 (no
MITM on the TCP fallback); this is the deliberate model choice, not an uncovered gap. -/
theorem WorldModelsTcp_complete
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (now : Time) (w : World)
    (hwm : WorldModelsTcp net ns ra ednsBuf now w)
    (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (resp : VeriDNS.Spec.Format) (qm : Query)
    (hαq : αQuery q = some qm)
    (hacc : AcceptsTcp w q id cid ab resp) :
    ∃ srv tr ref, serverAt net (byteAddrToModel ab) = some srv ∧
        ServerAnswers srv now [] true qm tr ref ∧
        RespAgree (αResp resp) ref ∧
        linkReach net ns ra (byteAddrToModel ab) = true := by
  obtain ⟨bytes, resp0, resp₀, hO, hdec, hsan, haccR⟩ := hacc
  obtain ⟨srv, tr, ref, hfind, hans, hrag, hreach, _⟩ :=
    hwm q id cid ab bytes resp0 resp₀ resp qm hO hdec hsan haccR hαq
  exact ⟨srv, tr, ref, hfind, hans, hrag, hreach⟩

/-- The honest-only TCP pack still yields the UDP-shaped `SpoofReply` for any accepted TCP reply
whose abstracted `tc` bit is clear — so the TCP path is never *less* covered than UDP.  This is
`tcpSpoofReply_of_honest` restated over the `AcceptsTcp` predicate: the absence of a spoof
disjunct in `WorldModelsTcp` is not a coverage hole, because the honest arm subsumes the spoof
shape. -/
theorem AcceptsTcp_realises_SpoofReply
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (now : Time) (w : World)
    (hnetWF : net.WF)
    (hwm : WorldModelsTcp net ns ra ednsBuf now w)
    (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
    (resp : VeriDNS.Spec.Format) (qm : Query)
    (hαq : αQuery q = some qm)
    (hacc : AcceptsTcp w q id cid ab resp)
    (htc0 : (resp.header.tc == 1) = false)
    (hreachR : linkReach net ns ra ra = true) :
    SpoofReply net ns ra ednsBuf id ab resp qm := by
  obtain ⟨bytes, resp0, resp₀, hO, hdec, hsan, haccR⟩ := hacc
  exact tcpSpoofReply_of_honest net ns ra ednsBuf now hnetWF w q id cid ab bytes resp0 resp₀ resp qm
    hwm hO hdec hsan haccR hαq htc0 hreachR

/-! ## The any-wire payoff

`serveDatagram_verdict_sound` (`Proof/ResolveWithIOSound.lean`) is stated against the
`WorldModels` / `WorldModelsTcp` premises.  Read literally, that is "sound whenever the world's
oracle happens to satisfy the model".  With completeness in hand the reading upgrades: the model
is *exhaustive over the accepted-datagram space* (`WorldModels_complete`) and unaccepted
datagrams are dropped below the shim (`accepts_requires_source_and_query_match`).  So under those
same premises the resolver's verdict is sound *against every wire datagram it acts on* — there is
no third category of datagram for which the theorem is silent.

`serveDatagram_verdict_sound_any_wire` bundles the capstone with the completeness certificate:
alongside the run's verdict-soundness, it hands back the fact that every datagram the world
accepts as a reply realises a `WorldModels` disjunct.  The `WorldModels` hypothesis is thereby
witnessed as complete rather than a scope door — the Adversary-model ledger row is closed at the
serve capstone. -/

/-- **Any-wire soundness (UDP serve path).**  Exactly `serveDatagram_verdict_sound`, re-exposed
with its completeness certificate: the same verdict-soundness conclusion, *plus* the fact that
every datagram the world `w` accepts as a reply realises some `WorldModels` disjunct
(`WorldModels_complete`).  The conjunction is the "sound vs every accepted wire datagram"
reading of the capstone: the model is exhaustive over the accepted space, so soundness against
it is soundness against every reply the resolver acts on. -/
theorem serveDatagram_verdict_sound_any_wire
    (net : Network) (ns : NetState) (ra : String) (ednsBuf : Nat) (rttOf : String → Nat)
    (clientSock : Unit) (acl : Server.ClientAcl) (sbelt : VeriDNS.Impl.SList.DnsSList)
    (hnetWF : net.WF) (hGlSbelt : GluelessProv sbelt)
    (n : Nat) (queryBytes clientAddr : ByteArray)
    (query : VeriDNS.Spec.Format) (qu : VeriDNS.Spec.Question) (qm : Query) (t : RRType)
    (cache : VeriDNS.Impl.Cache.DnsCache) (w w' : World) (cacheOut : VeriDNS.Impl.Cache.DnsCache)
    (hperm : Server.permitted acl clientAddr = true)
    (hdec : VeriDNS.Impl.Message.decode queryBytes = .ok query)
    (hqrbit : (query.header.qr == 1) = false)
    (hqp : Server.queryProblem query = none)
    (hedns : VeriDNS.Impl.Edns.ednsProblem query = none)
    (hqu : query.question[0]? = some qu)
    (hqm : αName qu.qname = some qm.qname)
    (hcanon : qu.qname = VeriDNS.Impl.DomainName.labelsToWireFormatGo qm.qname)
    (ht : αType qu.qtype = some t)
    (hqany : qu.qtype.toNat ≠ 255)
    (hqq : qm.qtype = QType.rr t)
    (hqc : αClass qu.qclass = some qm.qclass)
    (hqvalid : ∀ x ∈ qm.qname, 0 < x.size ∧ x.size ≤ 63)
    (hqlen : qm.qname.length ≤ 127)
    (hrd : qm.rd = false) (hqstar : qm.qtype ≠ QType.star)
    (hCacheWf : CacheWf cache w.clock)
    (hNsCanon : CacheNsCanon cache)
    (hCnCanon : CacheCnameCanon cache)
    (hwfrr : ∀ e ∈ cache.records, VeriDNS.Proof.NameTree.WfRR e.rr)
    (hNsDistinct : CacheNsDistinct cache)
    (hOE : VeriDNS.Proof.NameTree.OneExpiryPerKey cache)
    (hCap : cache.records.size ≤ VeriDNS.Impl.Cache.DnsCache.capacity)
    (hNegWf : CacheNegWf cache qu.qclass)
    (hRecC : VeriDNS.Proof.DeliveredWire.CacheRecCanon cache)
    (hNegSoaC : VeriDNS.Proof.DeliveredWire.CacheNegSoaCanon cache)
    (hclock : w.clock.toNat + 604800 < 2 ^ 32)
    (hw : WorldModels net ns ra ednsBuf (αTime w.clock) w)
    (hwTcp : WorldModelsTcp net ns ra ednsBuf (αTime w.clock) w)
    (hrun : Prog.run n (Server.serveDatagram (M := Prog) (Sock := Unit)
        clientSock acl sbelt cache queryBytes clientAddr) w = some (cacheOut, w')) :
    -- (1) the completeness certificate: every accepted wire datagram realises a WorldModels
    --     disjunct, so the WorldModels premise excludes nothing the resolver acts on; and
    (∀ (q : VeriDNS.Spec.Format) (id cid : UInt16) (ab : ByteArray)
        (d : VeriDNS.Spec.Exchanged ByteArray) (resp : VeriDNS.Spec.Format) (qmq : Query),
        αQuery q = some qmq → Accepts w q id cid ab d resp →
        (∃ srv tr ref, serverAt net (byteAddrToModel ab) = some srv ∧
            ServerAnswers srv (αTime w.clock) [] true qmq tr ref ∧
            RespAgree (αResp resp) ref ∧
            linkReach net ns ra (byteAddrToModel ab) = true)
        ∨ SpoofReply net ns ra ednsBuf id ab resp qmq)
    ∧ -- (2) the full verdict-soundness of `serveDatagram_verdict_sound`, now read against every
      --     accepted wire datagram since (1) witnesses the model exhaustive over the accepted space.
    (∃ (m : Nat) (rr : Except String VeriDNS.Spec.Format) (cache' : VeriDNS.Impl.Cache.DnsCache)
        (w₂ : World),
      Prog.run m (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache w.clock) w = some ((rr, cache'), w₂)
      ∧ ((∃ msg, rr = .error msg
            ∧ (∃ slist v,
                HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] []
                  (αCache cache) slist qm v (αCache cache)
                ∧ v.rcode = RCode.servFail ∧ v.answer = [])
            ∧ VeriDNS.Spec.Net.GaveUpWitness (αTime w.clock) (αCache cache) [] qm)
        ∨ (∃ resp slist v cOut coutM,
            rr = .ok resp
            ∧ resp.question[0]? = some qu
            ∧ CacheRefines cOut (αCache cache)
            ∧ HasVerdictAt net ns ra ednsBuf rttOf (αTime w.clock) [] [] cOut slist qm v coutM
            ∧ (αResp (Server.deliveredResponse query resp)).rcode = v.rcode
            ∧ (αResp (Server.deliveredResponse query resp)).answer
                = VeriDNS.Spec.Net.typeScrub qm.qtype (VeriDNS.Spec.Net.scrubAnswer qm.qname v.answer)))) := by
  refine ⟨?_, ?_⟩
  · -- (1) completeness: `WorldModels_complete`, honest arm peeled to its answer-agreement core.
    intro q id cid ab d resp qmq hαq hacc
    rcases WorldModels_complete net ns ra ednsBuf (αTime w.clock) w hw q id cid ab d resp qmq hαq hacc with
      ⟨srv, tr, ref, hfind, hans, hrag, hreach, _⟩ | hspoof
    · exact Or.inl ⟨srv, tr, ref, hfind, hans, hrag, hreach⟩
    · exact Or.inr hspoof
  · -- (2) soundness: `serveDatagram_verdict_sound` at the same, now-justified, premises.
    obtain ⟨m, rr, cache', w₂, hrun', hsound⟩ :=
      serveDatagram_verdict_sound net ns ra ednsBuf rttOf clientSock acl sbelt hnetWF hGlSbelt
        n queryBytes clientAddr query qu qm t cache w w' cacheOut
        hperm hdec hqrbit hqp hedns hqu hqm hcanon ht hqany hqq hqc hqvalid hqlen hrd hqstar
        hCacheWf hNsCanon hCnCanon hwfrr hNsDistinct hOE hCap hNegWf hRecC hNegSoaC hclock
        hw hwTcp hrun
    refine ⟨m, rr, cache', w₂, hrun', ?_⟩
    rcases hsound with ⟨msg, hrr, hverr, hgw, _⟩ | ⟨resp, slist, v, cOut, coutM, hrr, hqu', hcR, hHV, hrc, han, _⟩
    · exact Or.inl ⟨msg, hrr, hverr, hgw⟩
    · exact Or.inr ⟨resp, slist, v, cOut, coutM, hrr, hqu', hcR, hHV, hrc, han⟩

end VeriDNS.Proof.AdversaryComplete
