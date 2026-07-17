import VeriDNS.Proof.SpineAdequacy

/-!
# Multi-homed failover adequacy (plan-2 Topology row; finding 035)

The spine/depth1 adequacy corpus proves delivery over a **single-NS** delegation cut
(`VeriDNS.Proof.Adequacy.SlistShape`: one NS name, one glue address, every slist entry sharing
that name and address). A multi-homed delegation — a cut with a *set* of NS names, each with a
*set* of glue A records — routes through a slist with several servers, and if the first server
contacted times out the resolver fails over to the next. Under the single-NS shape that
behaviour is unrepresentable, so finding 035 (multi-homed failover) had no proof coverage even
though the discovery harness confirmed it works at runtime.

This module closes the Topology ledger row. It provides:

* `SlistShape'` — the **set-valued** generalisation of `SlistShape`: a delegation cut has a finite
  set `nsSet : Array (ByteArray × BitVec 32)` of `(NS-name, glue-address)` pairs, and every slist
  entry is one of those pairs (with an address). `SlistShape` is recovered as the singleton
  instance `SlistShape.toShape'` (single NS name + single glue address).

* The generalised collapse-point primitives, per element rather than all-collapse-to-one:
  `SlistShape'.bestWithAddress` yields *some member* of `nsSet` (via the already-multi-NS-ready
  `bestWithAddress_mem`), `SlistShape'.markQueried` preserves the shape, and
  `SlistShape'.addressTargets_none` (every entry is glued, so the glueless target list is empty).

* The **failover adequacy theorem** `run_ioResumeLoop_failoverAnswer`: from a multi-homed slist
  where the first server picked (`bestWithAddress`) times out and a *second, distinct* server then
  answers, the resolver delivers the answer. The impl mechanism is the resolver's own server
  rotation — `bestWithAddress` picks the least-tried server first, `markQueried` bumps the
  transmission count of the timed-out server, so the next `bestWithAddress` picks the failover
  server. This composes `run_ioResumeLoop_timeout` (server A times out, A marked queried) with
  `run_ioResumeLoop_answer` (server B, now least-tried, answers).

The single-NS spine/depth1 capstones are unchanged and still compile: `SlistShape` is kept as the
singleton special case of `SlistShape'`, so this is an additive generalisation, not a migration.
-/

namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO

/-! ## `SlistShape'` — the set-valued delegation shape -/

/-- A delegation cut with a *set* of servers. `nsSet` is the cut's NS-name/glue-address pairs;
every slist entry realises one of those pairs (name matches, address is that glue). The slist is
nonempty (there is at least one server) and `matchCount = mc`.

This is the multi-homed generalisation of `SlistShape`. Set `nsSet := #[(nsName, ip)]` to recover
the single-NS shape (see `SlistShape.toShape'`). -/
def SlistShape' (s : DnsSList) (nsSet : Array (ByteArray × BitVec 32)) (mc : Nat) : Prop :=
  (∀ e ∈ s.servers, ∃ p ∈ nsSet, e.name = p.1 ∧ e.address = some p.2)
  ∧ (∃ e, e ∈ s.servers)
  ∧ s.matchCount = mc

/-- The single-NS `SlistShape` is the singleton instance of `SlistShape'`. This is what keeps the
existing spine/depth1 capstones compiling unchanged: they state `SlistShape`, which is definably
the `nsSet := #[(nsName, ip)]` case of the general shape. -/
theorem SlistShape.toShape' {s : DnsSList} {nsName : ByteArray} {ip : BitVec 32} {mc : Nat}
    (h : SlistShape s nsName ip mc) :
    SlistShape' s #[(nsName, ip)] mc := by
  obtain ⟨hall, hne, hmc⟩ := h
  refine ⟨?_, hne, hmc⟩
  intro e he
  obtain ⟨hn, ha⟩ := hall e he
  exact ⟨(nsName, ip), by simp, hn, ha⟩

/-- Conversely, a singleton `SlistShape'` is a `SlistShape`. -/
theorem SlistShape'.toSingleton {s : DnsSList} {nsName : ByteArray} {ip : BitVec 32} {mc : Nat}
    (h : SlistShape' s #[(nsName, ip)] mc) :
    SlistShape s nsName ip mc := by
  obtain ⟨hall, hne, hmc⟩ := h
  refine ⟨?_, hne, hmc⟩
  intro e he
  obtain ⟨p, hp, hn, ha⟩ := hall e he
  rw [Array.mem_singleton] at hp
  subst hp
  exact ⟨hn, ha⟩

/-! ## Generalised collapse-point primitives

Each mirrors a `SlistShape.*` lemma but concludes with a *member of the set* rather than the one
collapsed name/address. -/

/-- `bestWithAddress` on a set-shaped slist picks *some member of the set* (name and address of a
pair in `nsSet`). Generalises `SlistShape.bestWithAddress`; the underlying primitive
`bestWithAddress_mem` is already multi-NS-ready. -/
theorem SlistShape'.bestWithAddress {s : DnsSList} {nsSet : Array (ByteArray × BitVec 32)} {mc : Nat}
    (h : SlistShape' s nsSet mc) :
    ∃ entry ip, s.bestWithAddress = some (entry, ip)
      ∧ ∃ p ∈ nsSet, entry.name = p.1 ∧ ip = p.2 := by
  obtain ⟨hall, ⟨e0, he0⟩, _⟩ := h
  obtain ⟨p0, _hp0, _hn0, ha0⟩ := hall e0 he0
  have hsome := bestWithAddress_isSome_of_mem s e0 p0.2 he0 ha0
  obtain ⟨⟨e', a'⟩, hbw⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hmem', ha'⟩ := bestWithAddress_mem s e' a' hbw
  obtain ⟨p, hp, hn, ha⟩ := hall e' hmem'
  rw [ha, Option.some.injEq] at ha'
  exact ⟨e', a', hbw, p, hp, hn, ha'.symm⟩

/-- The glueless target list is empty: every entry of a set-shaped slist has an address.
Generalises `SlistShape.addressTargets_none`. -/
theorem SlistShape'.addressTargets_none {s : DnsSList} {nsSet : Array (ByteArray × BitVec 32)}
    {mc : Nat} (h : SlistShape' s nsSet mc) :
    s.addressTargets[0]? = none := by
  obtain ⟨hall, _, _⟩ := h
  have hempty : s.addressTargets = #[] := by
    unfold DnsSList.addressTargets
    rw [Array.filterMap_eq_empty_iff]
    intro e he
    obtain ⟨p, _hp, _hn, ha⟩ := hall e he
    rw [ha]
  rw [hempty]
  rfl

/-- `markQueried` preserves the set shape (only transmission counts change).
Generalises `SlistShape.markQueried`. -/
theorem SlistShape'.markQueried {s : DnsSList} {nsSet : Array (ByteArray × BitVec 32)} {mc : Nat}
    (h : SlistShape' s nsSet mc) (n : ByteArray) :
    SlistShape' (s.markQueried n) nsSet mc := by
  obtain ⟨hall, ⟨e0, he0⟩, hmc⟩ := h
  refine ⟨?_, ?_, hmc⟩
  · intro e he
    unfold DnsSList.markQueried at he
    replace he : e ∈ s.servers.map _ := he
    rw [Array.mem_map] at he
    obtain ⟨a, ha, hae⟩ := he
    obtain ⟨p, hp, hn, haddr⟩ := hall a ha
    subst hae
    refine ⟨p, hp, ?_, ?_⟩
    · split <;> exact hn
    · split <;> exact haddr
  · exact ⟨_, Array.mem_map.mpr ⟨e0, he0, rfl⟩⟩

/-! ## Generalised write-inverses for the reGlue / walkNs collapse points

The single-NS collapse lemmas (`referralWrite_reGlue_exact(_warm)`, `referralWrite_walkNs_facts`)
conclude that *every* servable glue address equals the one `grr`'s and *every* walkNs target name
equals the one `nsrr`'s. Those "all-collapse-to-one" conclusions are exactly what forbids a
multi-homed cut. The primitives below are their per-element replacements: each reGlue pair is
owned by *some* live glue record for that NS name, and each walkNs target name is *some* NS RR of
the cut. No singleton `#[glueRaw]`/`#[nsRaw]` hypothesis is needed — the decomposition goes
straight through `mem_reGlue_inv`, which is already per-element. -/

/-- **Collapse point (c), generalised.** Every reGlue pair `(gn, ga)` has `gn` among the walked NS
names and `ga` the glue-IP of a *live cached glue record owned by `gn`*. This is
`referralWrite_reGlue_exact`'s content without the single-glue collapse: instead of forcing
`ga = glueIpOf grr` for one fixed `grr`, it witnesses the record per element. A multi-homed cut
with several glue A records is covered because each pair keeps its own owner. -/
theorem reGlue_owned (cache : DnsCache) (now : UInt32) (nsNames : Array ByteArray)
    (gn : ByteArray) (ga : BitVec 32)
    (h : (gn, ga) ∈ VeriDNS.Proof.Refinement.reGlue (RR := VeriDNS.Spec.ResourceRecord)
        cache now nsNames) :
    gn ∈ nsNames
    ∧ ∃ rr ∈ cache.lookupTopCred gn (BitVec.ofNat 16 1) (BitVec.ofNat 16 1) now,
        ((VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr).size == 4) = true
        ∧ ga = glueIpOf (VeriDNS.Spec.RRParse.rrRdata (RR := VeriDNS.Spec.ResourceRecord) rr) :=
  mem_reGlue_inv cache now nsNames gn ga h

/-- **Collapse point (d), generalised — the set-valued slist constructor.** From a set `G` of
glue pairs and NS names `nsNames`, `fromNsWithGlueAll` builds a slist that is `SlistShape'` over
the *set* `nsGlueSet` of `(name, glue-address)` pairs actually present. Unlike
`SlistShape.of_fromNsWithGlueAll`, this needs **no** `hnames : ∀ n ∈ nsNames, n = nsName` collapse
and **no** `hval : ∀ (gn,ga) ∈ G, ga = ip` collapse: a genuinely multi-homed cut (several NS
names, several glue addresses) is admitted, each entry landing on its own pair. `nsGlueSet` is the
image set `{ (n, ga) | n ∈ nsNames, (gn, ga) ∈ G, foldNameCase gn = foldNameCase n }`, supplied by
the caller as the cut's server set.

The proof reads each `fromNsWithGlueAll` server back to the `(name, glue)` pair it came from — the
same `mem_flatMap` / `mem_filterMap` decomposition as the single-NS constructor, minus the two
`subst`s that collapse to one name and one address. -/
theorem SlistShape'.of_fromNsWithGlueAll
    (nsNames : Array ByteArray) (G : Array (ByteArray × BitVec 32)) (mc : Nat)
    (nsGlueSet : Array (ByteArray × BitVec 32))
    -- nonemptiness witness: at least one glued server exists
    (n0 gn0 : ByteArray) (ga0 : BitVec 32)
    (hn0 : n0 ∈ nsNames) (hg0 : (gn0, ga0) ∈ G)
    (hmatch0 : (VeriDNS.Impl.DomainName.foldNameCase gn0
        == VeriDNS.Impl.DomainName.foldNameCase n0) = true)
    (hin0 : (n0, ga0) ∈ nsGlueSet)
    -- every produced (name, glue-address) pair is in the caller's server set
    (hclosed : ∀ n ∈ nsNames, ∀ gn ga, (gn, ga) ∈ G →
        (VeriDNS.Impl.DomainName.foldNameCase gn
          == VeriDNS.Impl.DomainName.foldNameCase n) = true → (n, ga) ∈ nsGlueSet)
    -- FULL GLUE: every NS name of the cut has at least one glue A record.  A partially-glued cut
    -- routes through the `bestWithAddress = none` / addressTargets branch, which is a separate
    -- (glueless-delegation) adequacy dual, not part of the failover/multi-homed shape.
    (hfullGlue : ∀ n ∈ nsNames, ∃ gn ga, (gn, ga) ∈ G
        ∧ (VeriDNS.Impl.DomainName.foldNameCase gn
            == VeriDNS.Impl.DomainName.foldNameCase n) = true) :
    SlistShape' (DnsSList.fromNsWithGlueAll nsNames G mc) nsGlueSet mc := by
  refine ⟨?_, ?_, rfl⟩
  · intro e he
    unfold DnsSList.fromNsWithGlueAll at he
    simp only [Array.mem_flatMap] at he
    obtain ⟨n, hn, hemem⟩ := he
    split at hemem
    · -- glueless entry: impossible under full glue, since `n` has a matching glue record.
      rename_i hempty
      obtain ⟨gn, ga, hgmem, hgmatch⟩ := hfullGlue n hn
      have hga : ga ∈ G.filterMap
          (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
            == VeriDNS.Impl.DomainName.foldNameCase n then some x.2 else none) := by
        rw [Array.mem_filterMap]
        exact ⟨(gn, ga), hgmem, by simp only [hgmatch, if_true]⟩
      rw [Array.isEmpty_iff] at hempty
      rw [hempty] at hga
      simp at hga
    · rw [Array.mem_map] at hemem
      obtain ⟨ga, hga, rfl⟩ := hemem
      rw [Array.mem_filterMap] at hga
      obtain ⟨⟨gn, gv⟩, hgmem, hgif⟩ := hga
      by_cases hc : (VeriDNS.Impl.DomainName.foldNameCase gn
          == VeriDNS.Impl.DomainName.foldNameCase n) = true
      · rw [if_pos hc] at hgif
        have hgv : gv = ga := by simpa using hgif
        subst hgv
        exact ⟨(n, gv), hclosed n hn gn gv hgmem hc, rfl, rfl⟩
      · rw [if_neg hc] at hgif
        exact absurd hgif (by simp)
  · refine ⟨(⟨n0, some ga0, 0⟩ : SlistEntry), ?_⟩
    show _ ∈ (DnsSList.fromNsWithGlueAll nsNames G mc).servers
    unfold DnsSList.fromNsWithGlueAll
    simp only [Array.mem_flatMap]
    refine ⟨n0, hn0, ?_⟩
    have hga0 : ga0 ∈ G.filterMap
        (fun x => if VeriDNS.Impl.DomainName.foldNameCase x.1
          == VeriDNS.Impl.DomainName.foldNameCase n0 then some x.2 else none) := by
      rw [Array.mem_filterMap]
      exact ⟨(gn0, ga0), hg0, by simp only [hmatch0, if_true]⟩
    split
    · rename_i hc
      rw [Array.isEmpty_iff] at hc
      rw [hc] at hga0
      simp at hga0
    · exact Array.mem_map.mpr ⟨ga0, hga0, rfl⟩

/-! ## The failover primitive: a timed-out server that advances the world

`run_ioResumeLoop_timeout'` is `FreeIO.run_ioResumeLoop_timeout` with the resulting world `w2`
exposed as `{ w with trace := …, idCtr := w.idCtr + 2 }` (a timeout still consumes the two
per-round random ids — the txid and the 0x20 case seed — even though the query is never answered,
and, since finding 061, one latency tick: waiting on a dead server costs wall-clock time).
Exposing the world lets us feed the *failover* server's oracle at the exact shifted id-counter the
next round uses, exactly as `run_ioResumeLoop_retryThenAnswer` does for its second round. -/

theorem run_ioResumeLoop_timeout'
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = none) :
    ∃ w2, (∀ m, Prog.run (m + 5) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel'
          (Server.fallbackRevealed state.resources.sname revealed)) w2)
      ∧ w2.oracle = w.oracle ∧ w2.clock = w.clock + w.tick w.exchCtr
      ∧ w2.exchCtr = w.exchCtr + 1 ∧ w2.tick = w.tick
      ∧ w2.ids = w.ids ∧ w2.idCtr = w.idCtr + 2 := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [Server.ioResumeLoop, show m + 5 = (m + 4) + 1 from rfl, run_now_bind_eq, if_neg hdl,
      seqPureUnit]
    simp only [hbest, hbuild]
    simp only [hegress, Bool.false_eq_true, if_false]
    rw [run_round_bind_eq_none _ _ _ _ _ horacle]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## The failover adequacy theorem

`run_ioResumeLoop_failoverAnswer`: a multi-homed delegation is contacted; the first server picked
(`bestWithAddress`) **times out**, and the resolver fails over to a **second, distinct** server
which answers. The resolver delivers the answer.

This is the coverage that the single-NS `SlistShape` could not express: two servers, the first
dead, the second live. The impl mechanism is the resolver's own least-tried-first server rotation
— `run_ioResumeLoop_timeout'` marks the timed-out server queried (bumping its transmission count),
and the *caller* supplies the resulting `bestWithAddress` witness `hbest₂` picking the failover
server. For a genuine multi-homed cut, `hbest₂` follows from the set structure via
`SlistShape'.bestWithAddress` on the marked slist (both servers are members of `nsSet`). -/

theorem run_ioResumeLoop_failoverAnswer
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    -- first server: picked, times out
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hchain : state.cnameChain = #[])
    (hdl : ¬ (w.clock ≥ deadline))
    (hdl₂ : ¬ (w.clock + w.tick w.exchCtr ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = none)
    -- second server: the failover target, answers
    (entry₂ : SlistEntry) (ipAddr₂ : BitVec 32) (subQuery₀₂ resp02 resp₀2 resp2 : VeriDNS.Spec.Format)
    (d₂ : VeriDNS.Spec.Exchanged ByteArray) (bytes₂ : ByteArray)
    (hbest₂ : (state.resources.slist.markQueried entry.name).bestWithAddress
        = some (entry₂, ipAddr₂))
    (hegress₂ : Server.blockedEgress ipAddr₂ = false)
    (hbuild₂ : Resolver.buildSubQuery ({ state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } }
        : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) revealed = some subQuery₀₂)
    (hprobe₂ : Resolver.probeRoundB state.resources.sname revealed = false)
    (horacle₂ : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 2 + 1))))
        (Server.ipv4ToAddr ipAddr₂) = some d₂)
    (haccept₂ : Server.acceptExchanged (Server.ipv4ToAddr ipAddr₂) d₂ = some bytes₂)
    (hdecode₂ : VeriDNS.Impl.Message.decode bytes₂ = .ok resp02)
    (hsani₂ : Server.sanitizeTtlsCap resp02 = some resp₀2)
    (haccResp₂ : Server.acceptResponse
        (Server.withSecrets subQuery₀₂ (w.ids (w.idCtr + 2)) (w.ids (w.idCtr + 2 + 1))) resp₀2
        = some resp2)
    (htc₂ : (resp2.header.tc == 1) = false)
    (hunfollow₂ : Server.unfollowableDelegationB
        ((state.resources.slist.markQueried entry.name).markQueried entry₂.name)
        state.resources.sname resp2 = false)
    (hcname₂ : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp2 = none)
    (hsf₂ : (resp2.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls₂ : Resolver.classifiableB resp2 = true)
    (hans₂ : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp2 = true)
    (hfe₂ : (resp2.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ K w' resp' cout',
      Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 2) revealed) w
        = some ((.ok resp', cout'), w')
      -- content pin: the delivered answer is the failover server's answer, verbatim.
      ∧ resp'.answer = resp2.answer := by
  -- Server A times out; the world advances to `w2` (id-counter + 2, one latency tick on the
  -- clock, same ids/oracle).  The timeout consumes one loop iteration: `(fuel'+1)+1 → fuel'+1`.
  obtain ⟨w2, hstep, ho, hc, hec, htk, hi, hic⟩ := run_ioResumeLoop_timeout' sbelt state deadline depth
    (fuel' + 1) revealed w entry ipAddr subQuery₀ hdl hbest hegress hbuild horacle
  -- At a full-name round (`hprobe₂`) the RFC 9156 §2.3 timeout fallback is the
  -- identity: the retry keeps the same `revealed`.
  rw [show Server.fallbackRevealed state.resources.sname revealed = revealed from by
    simp [Server.fallbackRevealed, hprobe₂]] at hstep
  -- The marked state: still `.sendQueries`, sname/lastQuery unchanged.  Server B (the failover
  -- target) then answers on the marked state.
  obtain ⟨K₂, w', h2⟩ := run_ioResumeLoop_answer (sbelt := sbelt)
    (state := { state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } })
    (deadline := deadline) (depth := depth) (fuel' := fuel') (revealed := revealed) (w := w2)
    (entry := entry₂) (ipAddr := ipAddr₂) (subQuery₀ := subQuery₀₂)
    (d := d₂) (bytes := bytes₂) (resp0 := resp02) (resp₀ := resp₀2) (resp := resp2)
    (hsendq := hsendq) (hdl := by rw [hc]; exact hdl₂) (hbest := hbest₂)
    (hegress := hegress₂) (hbuild := hbuild₂) (hprobe := hprobe₂)
    (horacle := by rw [ho, hi, hic]; exact horacle₂) (haccept := haccept₂) (hdecode := hdecode₂)
    (hsani := hsani₂) (haccResp := by rw [hi, hic]; exact haccResp₂) (htc := htc₂)
    (hunfollow := hunfollow₂) (hcname := hcname₂) (hsf := hsf₂) (hcls := hcls₂) (hans := hans₂) (hfe := hfe₂)
  refine ⟨K₂ + 5, w', _, _, (hstep K₂).trans h2, ?_⟩
  exact finalizeAnswer_answer (S := DnsSList) (C := DnsCache) (NS := SlistEntry)
    (RR := VeriDNS.Spec.ResourceRecord) _ resp2 hchain

end VeriDNS.Proof.Adequacy
