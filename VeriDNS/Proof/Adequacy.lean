import VeriDNS.Proof.FreeIO
import VeriDNS.Proof.NameTreeComplete







namespace VeriDNS.Proof.Adequacy

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.NameTree VeriDNS.Impl.NameTree




theorem resolveWithIO_cacheHit_adequate
    (query : Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    ∀ (w : World) (k : Nat),
      Prog.run k (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now fuel depth budget) w
        = some ((.ok (Resolver.finalizeAnswer
            { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry)
                (RR := VeriDNS.Spec.ResourceRecord) query sbelt now cache with cnameChain := chain }
            (Resolver.cacheResponse query rrs)), cache), w) :=
  fun w k => run_resolveWithIO_answerHit w k query sbelt cache now fuel depth budget
    qu sname chain rrs hqu hhit



theorem resolveWithIO_cacheHit_treeFaithful
    {T : Node VeriDNS.Spec.ResourceRecord} {cache : DnsCache}
    (hsane : TreeSane T) (hagree : CacheAgrees T cache) (hlc : LookupComplete T cache)
    (hone : OneExpiryPerKey cache) (hneg : NegativesFaithful T cache)
    (qu : VeriDNS.Spec.Question) (now : UInt32)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hhit : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    Reaches T qu.qtype qu.qname sname ∧
    (∃ matching, treeLookup T sname qu.qtype = .answer matching ∧
      ∀ trr ∈ matching.toList, ∃ rr' ∈ rrs, sameData rr' trr = true) ∧
    (∀ rr' ∈ rrs, RRInTree T rr' ∧ WfRR rr') := by
  have h := localAnswer_complete hsane hagree hlc hone hneg qu.qtype qu.qclass now 8 qu.qname #[]
    (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
  rw [hhit] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩




def Terminates {α : Type} (p : Prog α) (w : World) : Prop :=
  ∃ (K : Nat) (r : α × World), Prog.run K p w = some r

theorem terminates_pure {α} (a : α) (w : World) : Terminates (Prog.pure a) w :=
  ⟨0, (a, w), rfl⟩

theorem terminates_pure' {α} (a : α) (w : World) : Terminates (pure a : Prog α) w :=
  ⟨0, (a, w), rfl⟩

theorem terminates_bind {α β} (p : Prog α) (k : α → Prog β) (w : World)
    (hp : Terminates p w) (hk : ∀ (a : α) (w' : World), Terminates (k a) w') :
    Terminates (p >>= k) w := by
  obtain ⟨K, ⟨a, w'⟩, hK⟩ := hp
  obtain ⟨K', r, hK'⟩ := hk a w'
  exact ⟨K + K', r, run_bind hK k hK'⟩

theorem terminates_now_bind {α} (k : UInt32 → Prog α) (w : World)
    (h : Terminates (k w.clock) w) :
    Terminates ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w := by
  obtain ⟨K, r, hK⟩ := h; exact ⟨K + 1, r, run_now_bind k w hK⟩

theorem terminates_log_bind {α} (s : String) (k : Unit → Prog α) (w : World)
    (h : Terminates (k ()) { w with trace := w.trace ++ [s] }) :
    Terminates ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) w := by
  obtain ⟨K, r, hK⟩ := h; exact ⟨K + 1, r, run_log_bind s k w hK⟩

theorem terminates_randomId_bind {α} (k : UInt16 → Prog α) (w : World)
    (h : Terminates (k (w.ids w.idCtr)) { w with idCtr := w.idCtr + 1 }) :
    Terminates ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w := by
  obtain ⟨K, r, hK⟩ := h; exact ⟨K + 1, r, run_randomId_bind k w hK⟩

theorem terminates_forwardQuery_bind {α} (query : Format) (addr : ByteArray)
    (k : Option Format → Prog α) (w : World) (h : ∀ v, Terminates (k v) w) :
    Terminates ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w := by
  cases ho : w.oracle (VeriDNS.Impl.Message.encode query) addr with
  | none =>
    obtain ⟨K, r, hK⟩ := h none
    exact ⟨K + 1, r, by rw [run_forwardQuery_bind_eq_none query addr k w ho]; exact hK⟩
  | some d =>
    cases ha : Server.acceptExchanged addr d with
    | none =>
      obtain ⟨K, r, hK⟩ := h none
      exact ⟨K + 1, r, by rw [run_forwardQuery_bind_eq_acceptNone query addr k w d ho ha]; exact hK⟩
    | some bytes =>
      cases hd : VeriDNS.Impl.Message.decode bytes with
      | error e =>
        obtain ⟨K, r, hK⟩ := h none
        exact ⟨K + 1, r, by
          rw [run_forwardQuery_bind_eq_decodeError query addr k w d bytes e ho ha hd]; exact hK⟩
      | ok resp =>
        obtain ⟨K, r, hK⟩ := h (Server.sanitizeTtlsCap resp)
        exact ⟨K + 1, r, by
          rw [run_forwardQuery_bind_eq query addr k w d bytes resp ho ha hd]; exact hK⟩

theorem terminates_tcpForward_bind {α} (query : Format) (addr : ByteArray)
    (k : Option Format → Prog α) (w : World) (h : ∀ v, Terminates (k v) w) :
    Terminates ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) w := by
  cases ho : w.tcpOracle (VeriDNS.Impl.Message.encode query) addr with
  | none =>
    obtain ⟨K, r, hK⟩ := h none
    exact ⟨K + 1, r, by rw [run_tcpForward_bind_eq_none query addr k w ho]; exact hK⟩
  | some bytes =>
    cases hd : VeriDNS.Impl.Message.decode bytes with
    | error e =>
      obtain ⟨K, r, hK⟩ := h none
      exact ⟨K + 1, r, by rw [run_tcpForward_bind_eq_decodeError query addr k w bytes e ho hd]; exact hK⟩
    | ok resp =>
      obtain ⟨K, r, hK⟩ := h (Server.sanitizeTtlsCap resp)
      exact ⟨K + 1, r, by rw [run_tcpForward_bind_eq query addr k w bytes resp ho hd]; exact hK⟩

theorem terminates_gluelessUpdatedSlist_bind {α}
    (slist : DnsSList) (nsName : ByteArray) (sub : Except String Format)
    (k : DnsSList → Prog α) (w : World)
    (h : ∀ (sl : DnsSList) (w' : World), Terminates (k sl) w') :
    Terminates ((Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName sub) >>= k) w := by
  unfold Server.gluelessUpdatedSlist
  cases sub with
  | error e =>
    simp only [Prog.bind_assoc']
    exact terminates_log_bind _ _ _ (h (slist.removeServer nsName) _)
  | ok subResp =>
    cases hA : Server.extractAAddress subResp.answer with
    | some addr =>
      simp only [hA, Prog.bind_assoc']
      exact terminates_log_bind _ _ _ (h (slist.addAddress nsName addr) _)
    | none =>
      simp only [hA, Prog.bind_assoc']
      exact terminates_log_bind _ _ _ (h (slist.removeServer nsName) _)

theorem ioResumeLoop_terminates (sbelt : DnsSList) (deadline : UInt32) :
    ∀ (depth fuel : Nat)
      (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
      (revealed : Nat) (w : World),
      Terminates (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth fuel revealed) w := by
  intro depth
  induction depth using Nat.strongRecOn with
  | _ depth IHdepth =>
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel IHfuel =>
      intro state revealed w
      cases fuel with
      | zero => rw [Server.ioResumeLoop]; exact terminates_pure' _ _
      | succ fuel' =>
        rw [Server.ioResumeLoop]
        refine terminates_now_bind _ w ?_
        by_cases hdl : w.clock ≥ deadline
        · rw [if_pos hdl]; exact terminates_pure' _ _
        · rw [if_neg hdl]
          cases hbest : state.resources.slist.bestWithAddress with
          | none =>
            cases hat : state.resources.slist.addressTargets[0]? with
            | none => exact terminates_pure' _ _
            | some nsName =>
              cases depth with
              | zero => exact terminates_pure' _ _
              | succ depth' =>
                refine terminates_log_bind _ _ _ ?_
                split
                ·
                  exact terminates_gluelessUpdatedSlist_bind _ _ _ _ _
                    (fun sl w' => IHdepth depth' (by omega) fuel' _ revealed w')
                ·
                  exact terminates_gluelessUpdatedSlist_bind _ _ _ _ _
                    (fun sl w' => IHdepth depth' (by omega) fuel' _ revealed w')
                ·
                  refine terminates_bind _ _ _
                    (IHdepth depth' (by omega) fuel' _ _ _) ?_
                  intro __discr w'
                  refine terminates_gluelessUpdatedSlist_bind _ _ _ _ _ ?_
                  intro sl w''
                  split
                  · split
                    · split
                      · exact terminates_pure' _ _
                      · exact IHdepth depth' (by omega) fuel' _ revealed w''
                    · exact IHdepth depth' (by omega) fuel' _ revealed w''
                  · exact IHdepth depth' (by omega) fuel' _ revealed w''
          | some p =>
            obtain ⟨entry, ipAddr⟩ := p
            simp only []
            split
            ·
              refine terminates_log_bind _ _ _ ?_
              refine terminates_randomId_bind _ _ ?_
              refine terminates_randomId_bind _ _ ?_
              by_cases hbe : Server.blockedEgress ipAddr = true
              ·
                rw [if_pos hbe]
                refine terminates_log_bind _ _ _ ?_
                simp only []
                exact IHfuel fuel' (by omega) _ _ _
              ·
                rw [if_neg hbe]
                refine terminates_forwardQuery_bind _ _ _ _ ?_
                intro v
                split
                ·
                  split
                  ·
                    refine terminates_log_bind _ _ _ ?_
                    refine terminates_bind _ _ _ ?_ ?_
                    ·
                      split
                      ·
                        refine terminates_log_bind _ _ _ ?_
                        refine terminates_tcpForward_bind _ _ _ _ ?_
                        intro v2
                        split
                        · exact terminates_pure' _ _
                        · split
                          · exact terminates_pure' _ _
                          · exact terminates_pure' _ _
                      ·
                        exact terminates_pure' _ _
                    ·
                      intro __discr w'
                      split
                      ·
                        split
                        ·
                          refine terminates_log_bind _ _ _ ?_
                          exact IHfuel fuel' (by omega) _ _ _
                        · split
                          ·
                            refine terminates_log_bind _ _ _ ?_
                            exact terminates_pure' _ _
                          · split
                            ·
                              refine terminates_log_bind _ _ _ ?_
                              exact IHfuel fuel' (by omega) _ _ _
                            ·
                              split
                              · exact terminates_pure' _ _
                              · exact IHfuel fuel' (by omega) _ _ _
                      ·
                        refine terminates_log_bind _ _ _ ?_
                        exact IHfuel fuel' (by omega) _ _ _
                  ·
                    refine terminates_log_bind _ _ _ ?_
                    exact IHfuel fuel' (by omega) _ _ _
                ·
                  exact IHfuel fuel' (by omega) _ _ _
            ·
              exact terminates_pure' _ _

theorem resolveWithIO_terminates (query : Format) (sbelt : DnsSList) (cache : DnsCache)
    (now : UInt32) (fuel depth : Nat) (budget : UInt32) (w : World) :
    Terminates (Server.resolveWithIO (M := Prog) (Sock := Unit)
      query sbelt cache now fuel depth budget) w := by
  unfold Server.resolveWithIO
  split
  · exact terminates_pure' _ _
  · exact ioResumeLoop_terminates sbelt (now + budget) depth fuel _ _ w
  · exact terminates_pure' _ _




def Delivers (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel revealed : Nat) (w : World)
    (out : Except String VeriDNS.Spec.Format × DnsCache) : Prop :=
  ∃ (K : Nat) (w' : World), Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state deadline depth fuel revealed) w = some (out, w')




theorem Delivers_referral_step
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hpdeny : (Resolver.probeRoundB state.resources.sname revealed
        && Server.strictDenialB resp) = false)
    (hpconsume : (Resolver.probeRoundB state.resources.sname revealed
        && !Server.probePassableB resp) = false)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀
        = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcont : Server.afterResume { state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } } entry.name resp = .continue st)
    (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
        Delivers sbelt st deadline depth fuel'
          (Server.revealedAfterContinue state.resources.sname revealed st) w' out) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w out := by
  obtain ⟨w', htransfer, ho, hto, hids, hclk, hctr⟩ :=
    run_ioResumeLoop_referral_lift sbelt state deadline depth fuel' revealed w
      entry ipAddr subQuery₀ d bytes resp0 resp₀ resp st
      hdl hbest hegress hbuild hpdeny hpconsume horacle haccept hdecode hsani haccResp htc
      hunfollow hcont
  obtain ⟨K, w'', hK⟩ := hnext w' ho hto hids hclk hctr
  exact ⟨K + 6, w'', htransfer K (out, w'') hK⟩


theorem Delivers_probeConsume_step
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀
        = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hdeny : Server.strictDenialB resp = false)
    (hpass : Server.probePassableB resp = false)
    (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
        w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
        Delivers sbelt { state with resources := { state.resources with
            slist := state.resources.slist.markQueried entry.name } } deadline depth fuel'
          (Resolver.bumpRevealed state.resources.sname revealed) w' out) :
    Delivers sbelt state deadline depth (fuel' + 1) revealed w out := by
  obtain ⟨w', htransfer, ho, hto, hids, hclk, hctr⟩ :=
    run_ioResumeLoop_probeConsume_lift sbelt state deadline depth fuel' revealed w
      entry ipAddr subQuery₀ d bytes resp0 resp₀ resp
      hdl hbest hegress hbuild hprobe horacle haccept hdecode hsani haccResp htc
      hunfollow hdeny hpass
  obtain ⟨K, w'', hK⟩ := hnext w' ho hto hids hclk hctr
  exact ⟨K + 7, w'', htransfer K (out, w'') hK⟩


theorem resolveWithIO_delivers
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hd : Delivers sbelt state (now + budget) depth fuel (Server.seedRevealed state) w out) :
    ∃ (K : Nat) (w' : World), Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now fuel depth budget) w = some (out, w') := by
  obtain ⟨K, w', hK⟩ := hd
  refine ⟨K, w', ?_⟩
  unfold Server.resolveWithIO
  rw [hpause]
  exact hK





inductive DescentChain (sbelt : DnsSList) (deadline : UInt32) (depth : Nat)
    (out : Except String VeriDNS.Spec.Format × DnsCache) :
    Resolver.State DnsSList DnsCache SlistEntry ResourceRecord → Nat → Nat → World → Prop where
  | terminal {state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord}
      {fuel revealed : Nat} {w : World}
      (h : Delivers sbelt state deadline depth fuel revealed w out) :
      DescentChain sbelt deadline depth out state fuel revealed w
  | referral {state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord}
      {fuel' revealed : Nat} {w : World}
      {entry : SlistEntry} {ipAddr : BitVec 32} {subQuery₀ : VeriDNS.Spec.Format}
      {d : VeriDNS.Spec.Exchanged ByteArray} {bytes : ByteArray}
      {resp0 resp₀ resp : VeriDNS.Spec.Format}
      {st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord}
      (hdl : ¬ (w.clock ≥ deadline))
      (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
      (hegress : Server.blockedEgress ipAddr = false)
      (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
      (hpdeny : (Resolver.probeRoundB state.resources.sname revealed
          && Server.strictDenialB resp) = false)
      (hpconsume : (Resolver.probeRoundB state.resources.sname revealed
          && !Server.probePassableB resp) = false)
      (horacle : w.oracle (VeriDNS.Impl.Message.encode
          (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
          (Server.ipv4ToAddr ipAddr) = some d)
      (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
      (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
      (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
      (haccResp : Server.acceptResponse
          (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀
          = some resp)
      (htc : (resp.header.tc == 1) = false)
      (hunfollow : Server.unfollowableDelegationB
          (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
      (hcont : Server.afterResume { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } } entry.name resp = .continue st)
      (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
          w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
          DescentChain sbelt deadline depth out st fuel'
            (Server.revealedAfterContinue state.resources.sname revealed st) w') :
      DescentChain sbelt deadline depth out state (fuel' + 1) revealed w
  | probe {state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord}
      {fuel' revealed : Nat} {w : World}
      {entry : SlistEntry} {ipAddr : BitVec 32} {subQuery₀ : VeriDNS.Spec.Format}
      {d : VeriDNS.Spec.Exchanged ByteArray} {bytes : ByteArray}
      {resp0 resp₀ resp : VeriDNS.Spec.Format}
      (hdl : ¬ (w.clock ≥ deadline))
      (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
      (hegress : Server.blockedEgress ipAddr = false)
      (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
      (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
      (horacle : w.oracle (VeriDNS.Impl.Message.encode
          (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
          (Server.ipv4ToAddr ipAddr) = some d)
      (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
      (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
      (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
      (haccResp : Server.acceptResponse
          (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀
          = some resp)
      (htc : (resp.header.tc == 1) = false)
      (hunfollow : Server.unfollowableDelegationB
          (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
      (hdeny : Server.strictDenialB resp = false)
      (hpass : Server.probePassableB resp = false)
      (hnext : ∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
          w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
          DescentChain sbelt deadline depth out
            { state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } } fuel'
            (Resolver.bumpRevealed state.resources.sname revealed) w') :
      DescentChain sbelt deadline depth out state (fuel' + 1) revealed w


theorem DescentChain.delivers {sbelt : DnsSList} {deadline : UInt32} {depth : Nat}
    {out : Except String VeriDNS.Spec.Format × DnsCache}
    {state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord}
    {fuel revealed : Nat} {w : World}
    (h : DescentChain sbelt deadline depth out state fuel revealed w) :
    Delivers sbelt state deadline depth fuel revealed w out := by
  induction h with
  | terminal h => exact h
  | referral hdl hbest hegress hbuild hpdeny hpconsume horacle haccept hdecode hsani haccResp htc
      hunfollow hcont _ ih =>
    exact Delivers_referral_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hdl hbest hegress hbuild hpdeny hpconsume horacle haccept hdecode hsani haccResp htc
      hunfollow hcont ih
  | probe hdl hbest hegress hbuild hprobe horacle haccept hdecode hsani haccResp htc
      hunfollow hdeny hpass _ ih =>
    exact Delivers_probeConsume_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hdl hbest hegress hbuild hprobe horacle haccept hdecode hsani haccResp htc
      hunfollow hdeny hpass ih

theorem resolveWithIO_adequate_of_chain
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hchain : DescentChain sbelt (now + budget) depth out state fuel
        (Server.seedRevealed state) w) :
    ∃ (K : Nat) (w' : World), Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now fuel depth budget) w = some (out, w') :=
  resolveWithIO_delivers query sbelt cache now fuel depth budget w state out hpause
    hchain.delivers







theorem DescentChain.of_descent {sbelt : DnsSList} {deadline : UInt32} {depth : Nat}
    {out : Except String VeriDNS.Spec.Format × DnsCache}
    (Inv : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord → Nat → Nat → World → Prop)
    (μ : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord → Nat)
    (hstep : ∀ (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
        (fuel revealed : Nat) (w : World), Inv state fuel revealed w →
      Delivers sbelt state deadline depth fuel revealed w out
      ∨ ∃ (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
          (fuel' revealed' : Nat),
          fuel = fuel' + 1
          ∧ μ st < μ state
          ∧ (∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
              w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
              Inv st fuel' revealed' w')
          ∧ ((∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
                w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
                DescentChain sbelt deadline depth out st fuel' revealed' w')
              → DescentChain sbelt deadline depth out state (fuel' + 1) revealed w)) :
    ∀ (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
      (fuel revealed : Nat) (w : World), Inv state fuel revealed w →
      DescentChain sbelt deadline depth out state fuel revealed w := by
  have key : ∀ (n : Nat)
      (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
      (fuel revealed : Nat) (w : World), μ state = n → Inv state fuel revealed w →
      DescentChain sbelt deadline depth out state fuel revealed w := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n IH =>
      intro state fuel revealed w hμ hinv
      rcases hstep state fuel revealed w hinv with hterm | ⟨st, fuel', revealed', hfuel, hlt, hInv', hnode⟩
      · exact DescentChain.terminal hterm
      · subst hfuel
        exact hnode (fun w' ho hto hids hclk hctr =>
          IH (μ st) (by omega) st fuel' revealed' w' rfl (hInv' w' ho hto hids hclk hctr))
  intro state fuel revealed w hinv
  exact key (μ state) state fuel revealed w rfl hinv

theorem resolveWithIO_adequate_of_descent
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (out : Except String VeriDNS.Spec.Format × DnsCache)
    (Inv : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord → Nat → Nat → World → Prop)
    (μ : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord → Nat)
    (hstep : ∀ (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
        (fuel revealed : Nat) (w : World), Inv state fuel revealed w →
      Delivers sbelt state (now + budget) depth fuel revealed w out
      ∨ ∃ (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
          (fuel' revealed' : Nat),
          fuel = fuel' + 1
          ∧ μ st < μ state
          ∧ (∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
              w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
              Inv st fuel' revealed' w')
          ∧ ((∀ w' : World, w'.oracle = w.oracle → w'.tcpOracle = w.tcpOracle →
                w'.ids = w.ids → w'.clock = w.clock → w'.idCtr = w.idCtr + 2 →
                DescentChain sbelt (now + budget) depth out st fuel' revealed' w')
              → DescentChain sbelt (now + budget) depth out state (fuel' + 1) revealed w))
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hinv : Inv state fuel (Server.seedRevealed state) w) :
    ∃ (K : Nat) (w' : World), Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now fuel depth budget) w = some (out, w') :=
  resolveWithIO_adequate_of_chain query sbelt cache now fuel depth budget w state out hpause
    (DescentChain.of_descent Inv μ hstep state fuel (Server.seedRevealed state) w hinv)

end VeriDNS.Proof.Adequacy
