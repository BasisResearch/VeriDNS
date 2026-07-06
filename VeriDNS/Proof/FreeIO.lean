import VeriDNS.Proof.Refinement

namespace VeriDNS.Proof.FreeIO

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache

inductive DnsCmd where
  | now
  | randomId
  | exchange (q : ByteArray) (addr : ByteArray)
  | log (msg : String)

def DnsCmd.Res : DnsCmd → Type
  | .now => UInt32
  | .randomId => UInt16
  | .exchange _ _ => Option (VeriDNS.Spec.Exchanged ByteArray)
  | .log _ => Unit

inductive Prog (α : Type) : Type where
  | pure (a : α)
  | step (c : DnsCmd) (k : DnsCmd.Res c → Prog α)

def Prog.bind {α β} : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .step c k, f => .step c (fun r => (k r).bind f)

instance : Monad Prog where
  pure := Prog.pure
  bind := Prog.bind

@[simp] theorem Prog.pure_def {α} (a : α) : (pure a : Prog α) = Prog.pure a := rfl
@[simp] theorem Prog.bind_def {α β} (p : Prog α) (f : α → Prog β) : p >>= f = p.bind f := rfl

@[simp] theorem Prog.pure_bind {α β} (a : α) (f : α → Prog β) : (Prog.pure a) >>= f = f a := rfl

/-- The free monad `Prog` is associative under `bind` (needed to reassociate `(p >>= f) >>= g` so the
    `Prog`-stepping lemmas, which match a leading command `>>= k`, can fire). -/
theorem Prog.bind_assoc {α β γ : Type} (p : Prog α) (f : α → Prog β) (g : β → Prog γ) :
    (p.bind f).bind g = p.bind (fun x => (f x).bind g) := by
  induction p with
  | pure a => rfl
  | step c k ih => simp only [Prog.bind]; exact congrArg (Prog.step c) (funext fun r => ih r)

instance instUdp : UdpSocket Prog Unit ByteArray where
  recvFrom _ _ := .pure default
  sendTo _ _ _ := .pure ()
  now := .step .now .pure
  randomId := .step .randomId .pure
  exchange q a := .step (.exchange q a) .pure
  log s := .step (.log s) .pure

structure World where
  clock : UInt32
  ids : Nat → UInt16
  oracle : ByteArray → ByteArray → Option (VeriDNS.Spec.Exchanged ByteArray)
  trace : List String
  idCtr : Nat

def DnsCmd.run : (c : DnsCmd) → World → DnsCmd.Res c × World
  | .now, w => (w.clock, w)
  | .randomId, w => (w.ids w.idCtr, { w with idCtr := w.idCtr + 1 })
  | .exchange q a, w => (w.oracle q a, w)
  | .log s, w => ((), { w with trace := w.trace ++ [s] })

def Prog.run {α} : Nat → Prog α → World → Option (α × World)
  | _, .pure a, w => some (a, w)
  | 0, .step _ _, _ => none
  | n + 1, .step c k, w => let p := c.run w; Prog.run n (k p.1) p.2

@[simp] theorem run_pure {α} (n : Nat) (a : α) (w : World) :
    Prog.run n (Prog.pure a) w = some (a, w) := by cases n <;> rfl

/-- `pure`-syntactic-form companion of `run_pure`: lets `rw` fire on a do-block
`return`/`pure` (which elaborates to `Pure.pure`, not the `Prog.pure` constructor). -/
theorem run_pure' {α} (n : Nat) (a : α) (w : World) :
    Prog.run n (pure a : Prog α) w = some (a, w) := run_pure n a w

theorem run_step {α} (n : Nat) (c : DnsCmd) (k : DnsCmd.Res c → Prog α) (w : World) :
    Prog.run (n + 1) (Prog.step c k) w = Prog.run n (k (c.run w).1) (c.run w).2 := rfl

theorem run_mono {α} {n : Nat} {p : Prog α} {w : World} {r : α × World}
    (h : Prog.run n p w = some r) : ∀ m, Prog.run (n + m) p w = some r := by
  induction n generalizing p w r with
  | zero =>
    intro m; cases p with
    | pure a => simpa using h
    | step c k => simp [Prog.run] at h
  | succ n ih =>
    intro m; cases p with
    | pure a => simpa using h
    | step c k =>
      rw [run_step] at h
      rw [show n + 1 + m = (n + m) + 1 by omega, run_step]
      exact ih h m

theorem run_bind {α β} {n m : Nat} {p : Prog α} {w : World} {a : α} {w' : World} {r : β × World}
    (hp : Prog.run n p w = some (a, w')) (f : α → Prog β)
    (hf : Prog.run m (f a) w' = some r) :
    Prog.run (n + m) (p.bind f) w = some r := by
  induction n generalizing p w with
  | zero =>
    cases p with
    | pure a' =>
      simp only [run_pure, Option.some.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      rw [Nat.zero_add]; exact hf
    | step c k => simp [Prog.run] at hp
  | succ n ih =>
    cases p with
    | pure a' =>
      simp only [run_pure, Option.some.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      rw [show n + 1 + m = m + (n + 1) by omega]; exact run_mono hf (n + 1)
    | step c k =>
      rw [run_step] at hp
      show Prog.run (n + 1 + m) (Prog.step c (fun r => (k r).bind f)) w = some r
      rw [show n + 1 + m = (n + m) + 1 by omega, run_step]
      exact ih hp

open VeriDNS.Proof.Refinement in

theorem run_resolveWithIO_negHit (w : World) (k : Nat)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question) (rc : VeriDNS.Spec.Rcode)
    (soaAuth : Array VeriDNS.Spec.ResourceRecord) (chain : Array ByteArray)
    (hqu : query.question[0]? = some qu)
    (hneg : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .negative rc soaAuth chain) :
    Prog.run k (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now fuel depth budget) w
      = some ((.ok (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
              query sbelt now cache with cnameChain := chain }
          (Resolver.negativeResponse query rc soaAuth)), cache), w) := by
  rw [resolveWithIO_negHit (M := Prog) (Sock := Unit)
    query sbelt cache now fuel depth budget qu rc soaAuth chain hqu hneg]
  exact run_pure k _ w

open VeriDNS.Proof.Refinement in

theorem run_resolveWithIO_answerHit (w : World) (k : Nat)
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel depth : Nat) (budget : UInt32) (qu : VeriDNS.Spec.Question)
    (sname : ByteArray) (chain : Array ByteArray) (rrs : Array VeriDNS.Spec.ResourceRecord)
    (hqu : query.question[0]? = some qu)
    (hhit : Resolver.localAnswer (C := DnsCache) (RR := VeriDNS.Spec.ResourceRecord)
        cache qu.qtype qu.qclass now 8 qu.qname #[]
        (Resolver.cnameChaseVisited (RR := VeriDNS.Spec.ResourceRecord) qu.qname #[])
        = .answerHit sname chain rrs) :
    Prog.run k (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now fuel depth budget) w
      = some ((.ok (Resolver.finalizeAnswer
          { Resolver.initFromQuery (NS := VeriDNS.Spec.SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
              query sbelt now cache with cnameChain := chain }
          (Resolver.cacheResponse query rrs)), cache), w) := by
  rw [resolveWithIO_answerHit (M := Prog) (Sock := Unit)
    query sbelt cache now fuel depth budget qu sname chain rrs hqu hhit]
  exact run_pure k _ w

theorem run_forwardQuery (w : World) (k : Nat) (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray) (resp : VeriDNS.Spec.Format)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp) :
    Prog.run (k + 1) (Server.forwardQuery (M := Prog) (Sock := Unit) query addr) w
      = some (Server.sanitizeTtlsCap resp, w) := by
  unfold Server.forwardQuery
  simp only [bind]
  show Prog.run (k + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]
  simp only [DnsCmd.run, horacle, Prog.bind, haccept, hdecode]
  exact run_pure k _ w

theorem run_now (n : Nat) (w : World) :
    Prog.run (n + 1) (UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) w
      = some (w.clock, w) := by
  show Prog.run (n + 1) (Prog.step .now Prog.pure) w = _
  rw [run_step]; exact run_pure n _ _

theorem run_randomId (n : Nat) (w : World) :
    Prog.run (n + 1) (UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) w
      = some (w.ids w.idCtr, { w with idCtr := w.idCtr + 1 }) := by
  show Prog.run (n + 1) (Prog.step .randomId Prog.pure) w = _
  rw [run_step]; exact run_pure n _ _

theorem run_log (n : Nat) (s : String) (w : World) :
    Prog.run (n + 1) (UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) w
      = some ((), { w with trace := w.trace ++ [s] }) := by
  show Prog.run (n + 1) (Prog.step (.log s) Prog.pure) w = _
  rw [run_step]; exact run_pure n _ _

theorem run_now_bind {β} {m} (k : UInt32 → Prog β) (w : World) {r}
    (hk : Prog.run m (k w.clock) w = some r) :
    Prog.run (m + 1) ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = some r := by
  show Prog.run (m + 1) (Prog.step .now (fun x => (Prog.pure x).bind k)) w = some r
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]; exact hk

theorem run_now_bind_zero {β} (k : UInt32 → Prog β) (w : World) :
    Prog.run 0 ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = none := rfl

theorem run_log_bind {β} {m} (s : String) (k : Unit → Prog β) (w : World) {r}
    (hk : Prog.run m (k ()) { w with trace := w.trace ++ [s] } = some r) :
    Prog.run (m + 1) ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) w
      = some r := by
  show Prog.run (m + 1) (Prog.step (.log s) (fun x => (Prog.pure x).bind k)) w = some r
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]; exact hk

theorem run_randomId_bind {β} {m} (k : UInt16 → Prog β) (w : World) {r}
    (hk : Prog.run m (k (w.ids w.idCtr)) { w with idCtr := w.idCtr + 1 } = some r) :
    Prog.run (m + 1) ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = some r := by
  show Prog.run (m + 1) (Prog.step .randomId (fun x => (Prog.pure x).bind k)) w = some r
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]; exact hk

theorem run_forwardQuery_bind {β} {m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) {r}
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray) (resp : VeriDNS.Spec.Format)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp)
    (hk : Prog.run m (k (Server.sanitizeTtlsCap resp)) w = some r) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = some r := by
  unfold Server.forwardQuery
  simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = some r
  rw [run_step]
  simp only [DnsCmd.run, horacle, Prog.bind, haccept, hdecode]
  exact hk

theorem run_ioResumeLoop_fuel_zero (w : World) (n : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth : Nat) :
    Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth 0) w
      = some ((.error "resolveWithIO: max IO rounds", state.resources.cache), w) := by
  rw [Server.ioResumeLoop]
  exact run_pure n _ w

open VeriDNS.Proof.Refinement in
theorem ioResumeLoop_sound_zero
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (q : VeriDNS.Spec.Net.Query) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (deadline : UInt32) (depth n : Nat) (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hrun : Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth 0) w
        = some ((.ok resp, cout), w')) :
    HasVerdict net ns ra ednsBuf rttOf (αTime state.now) nseen seen
      (αCache state.resources.cache) slist q (αResp resp) := by
  rw [run_ioResumeLoop_fuel_zero] at hrun
  exact absurd hrun (by simp)

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_answer
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀
        = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),

          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              state.resources.sname resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundExpiryClasses), w') := by
  apply Exists.intro 5; apply Exists.intro
  rw [Server.ioResumeLoop]
  refine run_now_bind _ w ?_
  rw [if_neg hdl]
  simp only [Prog.pure_bind]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  refine run_log_bind _ _ w ?_
  refine run_randomId_bind _ _ ?_
  refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
  rw [hsani]
  dsimp only
  rw [haccResp]
  refine run_log_bind _ _ _ ?_
  rw [if_neg (by simp [hunfollow])]
  rw [afterResume_answer
      { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } }
      entry.name resp hsendq hcname hsf hcls hans]
  exact run_pure _ _ _

open VeriDNS.Proof.Refinement in

theorem run_resolveWithIO_networkAnswer
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel' depth : Nat) (budget : UInt32) (w : World)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ now + budget))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀
        = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = true) :
    ∃ K w', Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now (fuel' + 1) depth budget) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),

          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              state.resources.sname resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundExpiryClasses), w') := by
  unfold Server.resolveWithIO
  rw [hpause]
  exact run_ioResumeLoop_answer sbelt state (now + budget) depth fuel' w entry ipAddr subQuery₀
    d bytes resp0 resp₀ resp hsendq hdl hbest hglueless hbuild horacle haccept hdecode hsani
    haccResp hunfollow hcname hsf hcls hans

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_nxdomain
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀
        = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),
          (Server.boundStateCache
            ({ ({ state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } })
                with lastResponse := some resp, currentStep := .analyzeResponse }
                : Resolver.State DnsSList DnsCache SlistEntry
                    VeriDNS.Spec.ResourceRecord)).resources.cache), w') := by
  apply Exists.intro 5; apply Exists.intro
  rw [Server.ioResumeLoop]
  refine run_now_bind _ w ?_
  rw [if_neg hdl]
  simp only [Prog.pure_bind]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  refine run_log_bind _ _ w ?_
  refine run_randomId_bind _ _ ?_
  refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
  rw [hsani]
  dsimp only
  rw [haccResp]
  refine run_log_bind _ _ _ ?_
  rw [if_neg (by simp [hunfollow])]
  rw [afterResume_nameError
      { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } }
      entry.name resp hsendq hcname hsf hcls hnerr hans]
  exact run_pure _ _ _

@[simp] theorem World.ids_trace (w : World) (t) : ({ w with trace := t } : World).ids = w.ids := rfl
@[simp] theorem World.idCtr_trace (w : World) (t) :
    ({ w with trace := t } : World).idCtr = w.idCtr := rfl

theorem seqPureUnit {α} (X : Prog α) : (do pure PUnit.unit; X) = X := rfl

theorem run_now_bind_eq {β m} (k : UInt32 → Prog β) (w : World) :
    Prog.run (m + 1) ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = Prog.run m (k w.clock) w := by
  show Prog.run (m + 1) (Prog.step .now (fun x => (Prog.pure x).bind k)) w = _
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]

/-- **Deadline-exceeded terminal.** Once the clock has reached the query deadline the loop returns the
    deadline error without consuming any further IO. Mirror of `run_ioResumeLoop_fuel_zero` for the
    `fuel'+1` arm. NB: must `unfold` (not `rw [Server.ioResumeLoop]`) — the leaf-specific equation lemma
    `rw` would select carries the glueless-branch negation as an unprovable side goal; `unfold` keeps the
    full match body, and `simp only [if_pos hdl]` discards the (unreached) slist branch cleanly. -/
theorem run_ioResumeLoop_deadline (w : World) (m : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' : Nat) (hdl : w.clock ≥ deadline) :
    Prog.run (m + 1) (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth (fuel' + 1)) w
      = some ((.error "resolveWithIO: query deadline exceeded", state.resources.cache), w) := by
  unfold Server.ioResumeLoop
  rw [run_now_bind_eq]
  simp only [if_pos hdl]
  exact run_pure m _ w

/-- **No-servers terminal.** Before the deadline, with no SLIST entry carrying an address
    (`bestWithAddress = none`) and no glueless target to recurse on (`addressTargets[0]? = none`), the loop
    returns the no-servers error. Same `unfold` discipline as `run_ioResumeLoop_deadline`. -/
theorem run_ioResumeLoop_noserver (w : World) (m : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' : Nat) (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = none)
    (htgt : state.resources.slist.addressTargets[0]? = none) :
    Prog.run (m + 1) (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth (fuel' + 1)) w
      = some ((.error "resolveWithIO: no servers with addresses in SLIST", state.resources.cache), w) := by
  unfold Server.ioResumeLoop
  rw [run_now_bind_eq]
  simp only [if_neg hdl, hbest, seqPureUnit, htgt]
  exact run_pure m _ w

/-- **Cannot-build-sub-query terminal.** Before the deadline, with an addressed SLIST entry
    (`bestWithAddress = some (entry, ipAddr)`) but no constructible sub-query (`buildSubQuery = none`), the
    loop returns the build error. Same `unfold` discipline. -/
theorem run_ioResumeLoop_nobuild (w : World) (m : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' : Nat) (entry : SlistEntry) (ipAddr : BitVec 32)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hbuild : Resolver.buildSubQuery state = none) :
    Prog.run (m + 1) (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth (fuel' + 1)) w
      = some ((.error "resolveWithIO: cannot build sub-query", state.resources.cache), w) := by
  unfold Server.ioResumeLoop
  rw [run_now_bind_eq]
  simp only [if_neg hdl, hbest, seqPureUnit, hbuild]
  exact run_pure m _ w

theorem run_log_bind_eq {β m} (s : String) (k : Unit → Prog β) (w : World) :
    Prog.run (m + 1) ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) w
      = Prog.run m (k ()) { w with trace := w.trace ++ [s] } := by
  show Prog.run (m + 1) (Prog.step (.log s) (fun x => (Prog.pure x).bind k)) w = _
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]

theorem run_randomId_bind_eq {β m} (k : UInt16 → Prog β) (w : World) :
    Prog.run (m + 1) ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = Prog.run m (k (w.ids w.idCtr)) { w with idCtr := w.idCtr + 1 } := by
  show Prog.run (m + 1) (Prog.step .randomId (fun x => (Prog.pure x).bind k)) w = _
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]

theorem run_forwardQuery_bind_eq {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray) (resp : VeriDNS.Spec.Format)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k (Server.sanitizeTtlsCap resp)) w := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, haccept, hdecode]; rfl

theorem run_log_randomId_bind_eq {β m} (s : String) (k : UInt16 → Prog β) (w : World) :
    Prog.run (m + 2)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          k rid) w
      = Prog.run m (k (w.ids w.idCtr)) { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } := by
  rw [show m + 2 = (m + 1) + 1 from rfl,
    run_log_bind_eq (k := fun _ => UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray) >>= k),
    run_randomId_bind_eq]

theorem run_round_bind_eq {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray) (resp : VeriDNS.Spec.Format)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp) :
    Prog.run (m + 3)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr)
            >>= k rid) w
      = Prog.run m (k (w.ids w.idCtr) (Server.sanitizeTtlsCap resp))
          { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } := by
  rw [show m + 3 = (m + 1) + 2 from rfl,
    run_log_randomId_bind_eq (k := fun rid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr) >>= k rid),
    run_forwardQuery_bind_eq (Server.withRandomId subQuery₀ (w.ids w.idCtr)) addr (k (w.ids w.idCtr))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } d bytes resp horacle haccept hdecode]

/-- `forwardQuery` returns `none` when the oracle drops the datagram — the impl-side image of a lost
    reply (`Transit … none`). The `bind`-eq companion of `run_forwardQuery_bind_eq` for that case. -/
theorem run_forwardQuery_bind_eq_none {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = none) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind]; rfl

/-- `forwardQuery` returns `none` when the reply is delivered but `acceptExchanged` rejects it (the impl's
    source-address / wire-shape check) — still a `none` upstream, routed to the timeout retry. -/
theorem run_forwardQuery_bind_eq_acceptNone {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) (d : VeriDNS.Spec.Exchanged ByteArray)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = none) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, haccept]; rfl

/-- `forwardQuery` returns `none` when the accepted bytes fail to `decode` — a malformed reply, routed to
    the timeout retry. -/
theorem run_forwardQuery_bind_eq_decodeError {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) (d : VeriDNS.Spec.Exchanged ByteArray)
    (bytes : ByteArray) (errmsg : String)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .error errmsg) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, haccept, hdecode]; rfl

/-- The log+randomId+forwardQuery round when the oracle drops the datagram (timeout) — `run_round_bind_eq`
    for the `none` case. -/
theorem run_round_bind_eq_none {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        addr = none) :
    Prog.run (m + 3)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr)
            >>= k rid) w
      = Prog.run m (k (w.ids w.idCtr) none)
          { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } := by
  rw [show m + 3 = (m + 1) + 2 from rfl,
    run_log_randomId_bind_eq (k := fun rid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr) >>= k rid),
    run_forwardQuery_bind_eq_none (Server.withRandomId subQuery₀ (w.ids w.idCtr)) addr (k (w.ids w.idCtr))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } horacle]

/-- The round when the reply is delivered but `acceptExchanged` rejects it — `none` upstream (→ retry). -/
theorem run_round_bind_eq_acceptNone {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World) (d : VeriDNS.Spec.Exchanged ByteArray)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        addr = some d)
    (haccept : Server.acceptExchanged addr d = none) :
    Prog.run (m + 3)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr)
            >>= k rid) w
      = Prog.run m (k (w.ids w.idCtr) none)
          { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } := by
  rw [show m + 3 = (m + 1) + 2 from rfl,
    run_log_randomId_bind_eq (k := fun rid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr) >>= k rid),
    run_forwardQuery_bind_eq_acceptNone (Server.withRandomId subQuery₀ (w.ids w.idCtr)) addr (k (w.ids w.idCtr))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } d horacle haccept]

/-- The round when the accepted bytes fail to `decode` — `none` upstream (→ retry). -/
theorem run_round_bind_eq_decodeError {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World) (d : VeriDNS.Spec.Exchanged ByteArray)
    (bytes : ByteArray) (errmsg : String)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .error errmsg) :
    Prog.run (m + 3)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr)
            >>= k rid) w
      = Prog.run m (k (w.ids w.idCtr) none)
          { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } := by
  rw [show m + 3 = (m + 1) + 2 from rfl,
    run_log_randomId_bind_eq (k := fun rid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withRandomId subQuery₀ rid) addr) >>= k rid),
    run_forwardQuery_bind_eq_decodeError (Server.withRandomId subQuery₀ (w.ids w.idCtr)) addr (k (w.ids w.idCtr))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 1 } d bytes errmsg horacle haccept hdecode]

/-! ### Reverse-stepping inversion lemmas (for the soundness driver `ioResumeLoop_sound`)

  The forward `run_*_bind_eq` lemmas advance a *known* fuel `m+1`; the soundness driver instead has an
  *arbitrary* `Prog.run n (op >>= k) w = some r` and must (i) learn `n = m+1` (the op is a `Prog.step`, so
  `n = 0` would give `none ≠ some`) and (ii) advance to `Prog.run m (k …) w = some r`. These `_inv` lemmas
  package both: `obtain ⟨m, rfl, h⟩ := run_now_bind_inv … h` steps the hypothesis through one deterministic
  effect. `forwardQuery` only yields the fuel witness (its continuation argument depends on the oracle
  outcome — the driver then `cases`-es the oracle and rewrites with `run_forwardQuery_bind_eq`/`…_none`). -/

theorem run_now_bind_inv {β} {n : Nat} (k : UInt32 → Prog β) (w : World) {r : β × World}
    (h : Prog.run n ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w = some r) :
    ∃ m, n = m + 1 ∧ Prog.run m (k w.clock) w = some r := by
  cases n with
  | zero => rw [run_now_bind_zero] at h; exact absurd h (by simp)
  | succ m => exact ⟨m, rfl, by rw [← run_now_bind_eq]; exact h⟩

theorem run_log_bind_inv {β} {n : Nat} (s : String) (k : Unit → Prog β) (w : World) {r : β × World}
    (h : Prog.run n ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) w = some r) :
    ∃ m, n = m + 1 ∧ Prog.run m (k ()) { w with trace := w.trace ++ [s] } = some r := by
  cases n with
  | zero =>
    rw [show Prog.run 0 ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) w
      = none from rfl] at h
    exact absurd h (by simp)
  | succ m => exact ⟨m, rfl, by rw [← run_log_bind_eq]; exact h⟩

theorem run_randomId_bind_inv {β} {n : Nat} (k : UInt16 → Prog β) (w : World) {r : β × World}
    (h : Prog.run n ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w = some r) :
    ∃ m, n = m + 1 ∧ Prog.run m (k (w.ids w.idCtr)) { w with idCtr := w.idCtr + 1 } = some r := by
  cases n with
  | zero =>
    rw [show Prog.run 0 ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = none from rfl] at h
    exact absurd h (by simp)
  | succ m => exact ⟨m, rfl, by rw [← run_randomId_bind_eq]; exact h⟩

theorem run_forwardQuery_bind_inv {β} {n : Nat} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) {r : β × World}
    (h : Prog.run n ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w = some r) :
    ∃ m, n = m + 1 := by
  cases n with
  | zero =>
    rw [show Prog.run 0 ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = none from rfl] at h
    exact absurd h (by simp)
  | succ m => exact ⟨m, rfl⟩

/-- **Timeout-branch reduction of `ioResumeLoop`** (the impl-side step for the `timeout` model branch).
    When the oracle drops the datagram (`horacle = none`), one loop iteration `Prog.run`-reduces to the
    recursive call with the same `(depth, fuel')` and the current server marked queried — exactly the
    `Resolves.timeout` retry. A building block for the `(depth, fuel)` totality induction (`C3`): the
    timeout branch's reduction, the companion of `run_ioResumeLoop_bizarre_recurses`. -/
theorem run_ioResumeLoop_timeout
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = none) :
    ∃ w2, Prog.run (m + 4) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel') w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 4 = (m + 3) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  rw [run_round_bind_eq_none _ _ _ _ _ horacle]

/-- **rejectSpoof-branch reduction of `ioResumeLoop`** (the impl-side step for the `rejectSpoof` model
    branch, RFC 5452). When a reply is received and decoded but fails `acceptResponse`'s id/question
    anti-spoof gate (`haccResp = none`), one loop iteration `Prog.run`-reduces to the recursive call with
    the same `(depth, fuel')` and the server marked queried — exactly `Resolves.rejectSpoof`. Companion of
    `run_ioResumeLoop_timeout`; a building block for the C3 totality induction. -/
theorem run_ioResumeLoop_rejectSpoof
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀ = none) :
    ∃ w2, Prog.run (m + 5) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel') w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 5 = (m + 4) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]

/-- **Unfollowable-delegation (bailiwick-drop) reduction of `ioResumeLoop`.** When the accepted reply
    is an unfollowable delegation — not closer than the SLIST, or out of bailiwick (`hunfollow = true`,
    the executable image of the model's `descendsBelow`/`inBailiwick` guard) — it is *ignored* and
    resolution retries the next server. One iteration `Prog.run`-reduces to the recursive call with the
    server marked queried. This is the impl-side enforcement of the bailiwick discipline that the
    referral-poisoning fix added; in the totality induction it joins the retry family (no model state
    change beyond advancing the SLIST). -/
theorem run_ioResumeLoop_unfollowable
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀ = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = true) :
    ∃ w2, Prog.run (m + 6) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel') w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 6 = (m + 5) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  rw [show m + 5 = (m + 2) + 3 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq, if_pos (by simp [hunfollow]), run_log_bind_eq]

/-- **Send-success *continue* reduction of `ioResumeLoop`** (the impl-side step for the `refer` and
    `answerCname`/`cacheCname` model branches — the *state-changing* recursion). When the accepted reply
    is followable and `afterResume` returns `.continue st` (the resolver absorbed the response into a new
    state `st` — for a referral, the bailiwick-filtered cache + glue SLIST; for a CNAME, the chased
    target), one loop iteration `Prog.run`-reduces to the recursive call on `st` with the same depth and
    `fuel'`. Generic over `st`, so it covers both refer and cname (the model side supplies the concrete
    `st` via `afterResume_referral_continues` etc.). This is the non-trivial reduction — the cache/SLIST
    mutation that the referral-poisoning fix made bailiwick-safe rides through `st`. The last recursive
    reduction the C3 fuel induction needs (besides glueless). -/
theorem run_ioResumeLoop_continue
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀ = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcont : Server.afterResume
        { state with resources := { state.resources with
            slist := state.resources.slist.markQueried entry.name } } entry.name resp = .continue st) :
    ∃ w2, Prog.run (m + 5) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt st deadline depth fuel') w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 5 = (m + 4) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq, if_neg (by simp [hunfollow]), hcont]

/-- The SLIST-update step of the glueless branch, happy path: when the NS-address sub-resolution
    returns an answer containing an `A` record (`extractAAddress = some addr`), `gluelessUpdatedSlist`
    `Prog.run`-reduces to `slist.addAddress nsName addr` (the resolved glue is installed in the SLIST).
    A building block for the glueless (`gluelessNs`) reduction — its monadic SLIST mutation. -/
theorem run_gluelessUpdatedSlist_resolved (slist : DnsSList) (nsName : ByteArray)
    (subResp : VeriDNS.Spec.Format) (addr : BitVec 32) (m : Nat) (w : World)
    (haddr : Server.extractAAddress subResp.answer = some addr) :
    ∃ w2, Prog.run (m + 1) (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName
        (.ok subResp)) w
      = some (slist.addAddress nsName addr, w2) := by
  apply Exists.intro
  unfold Server.gluelessUpdatedSlist
  simp only [haddr]
  rw [run_log_bind_eq]
  exact run_pure m _ _

/-- The bind form of `run_gluelessUpdatedSlist_resolved` (the SLIST update inside a continuation `k`,
    as it appears in the glueless loop body): `gluelessUpdatedSlist … >>= k` `Prog.run`-reduces to `k`
    applied to the updated SLIST (`addAddress nsName addr`). Uses `Prog.bind_assoc` to reassociate the
    internal `log >>= pure` past the outer `>>= k`. The last stepping helper for the glueless reduction. -/
theorem run_gluelessUpdatedSlist_resolved_bind {β : Type} {m : Nat} (slist : DnsSList) (nsName : ByteArray)
    (subResp : VeriDNS.Spec.Format) (addr : BitVec 32) (k : DnsSList → Prog β) (w : World)
    (haddr : Server.extractAAddress subResp.answer = some addr) :
    ∃ w2, Prog.run (m + 1) (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName
        (.ok subResp) >>= k) w = Prog.run m (k (slist.addAddress nsName addr)) w2 := by
  apply Exists.intro
  unfold Server.gluelessUpdatedSlist
  simp only [haddr, Prog.bind_def, Prog.bind_assoc]
  rw [← Prog.bind_def, run_log_bind_eq]
  rfl

/-- **Glueless-branch reduction of `ioResumeLoop`** (the impl-side step for the `gluelessNs` model
    branch — the last per-branch reduction, completing the layer). When the SLIST has no addressed
    server (`bestWithAddress = none`) but a glueless NS target (`addressTargets[0]? = some nsName`,
    `depth = depth'+1`) whose address resolves in one shot (`Resolver.resolve … = .ok (.done subResp)`
    yielding an `A` record), one loop iteration `Prog.run`-reduces to the recursive call at `depth'`
    with `nsName`'s address installed in the SLIST (`addAddress`). Composes the sub-resolution dispatch,
    `run_gluelessUpdatedSlist_resolved_bind`, and the nested `bestWithAddress`/`depth`/`targets` match
    reductions (the `match`'s `heq` obligation is discharged by `htargets`). With this, **every impl
    branch of `ioResumeLoop` has a proven `Prog.run` reduction** — the impl-side half of the C3 fuel
    induction is complete. -/
theorem run_ioResumeLoop_glueless_done
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth' fuel' m : Nat) (w : World)
    (nsName : ByteArray) (subResp : VeriDNS.Spec.Format) (addr : BitVec 32)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = none)
    (htargets : state.resources.slist.addressTargets[0]? = some nsName)
    (subStF : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (hsub : @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord _ _ _ _ _ _ _ _
        (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache
        = .ok (.done subResp subStF))
    (haddr : Server.extractAAddress subResp.answer = some addr) :
    ∃ w2, Prog.run (m + 3) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline (depth' + 1) (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.addAddress nsName addr } } deadline depth' fuel') w2 := by
  rw [Server.ioResumeLoop, show m + 3 = (m + 2) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  rw [hbest]
  simp only [htargets]
  · rw [run_log_bind_eq, hsub]
    simp only [Prog.bind_def]
    exact run_gluelessUpdatedSlist_resolved_bind state.resources.slist nsName subResp addr _ _ haddr
  · exact htargets

/-- **Glueless `.paused` (network sub-resolution) reduction of `ioResumeLoop`.** When the SLIST
    has no addressed server (`bestWithAddress = none`) but a glueless NS target
    (`addressTargets[0]? = some nsName`, `depth = depth' + 1`) whose pure address resolution
    PAUSES (`Resolver.resolve … = .ok (.paused st)` — a network round is needed), one loop
    iteration `Prog.run`-reduces to the recursive sub-run `ioResumeLoop … st …` bound into the
    SLIST update (`gluelessUpdatedSlist` on the sub-result) and then the sub-result dispatch:
    a sub-run that produced a usable address (`extractAAddress = some`) goes through the
    RFC 1034 §5.3.3 cache-first re-check (`gluelessRecheck` on the sub-run's output cache `p.2`
    — a cached typed hit / negative for the MAIN query is delivered straight from the sub-run's
    cache; otherwise the main loop continues at `depth'` on `slist'`/`p.2`); a FAILED sub-run
    (error, or no usable A record) continues on the PRE-sub-run cache with the target dropped. -/
theorem run_ioResumeLoop_glueless_paused
    (sbelt : DnsSList) (state st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth' fuel' m : Nat) (w : World) (nsName : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = none)
    (htargets : state.resources.slist.addressTargets[0]? = some nsName)
    (hsub : @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord _ _ _ _ _ _ _ _
        (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache
        = .ok (.paused st)) :
    ∃ w2, Prog.run (m + 2) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline (depth' + 1) (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt st deadline depth' fuel'
          >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
            Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
              state.resources.slist nsName p.1 >>= fun slist' =>
            match p.1 with
            | .ok subResp =>
              match Server.extractAAddress subResp.answer with
              | some _ =>
                match Server.gluelessRecheck state p.2 with
                | some hit => pure (.ok hit, p.2)
                | none =>
                  Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                    { state with resources := { state.resources with
                        slist := slist', cache := p.2 } } deadline depth' fuel'
              | none =>
                Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                  { state with resources := { state.resources with
                      slist := slist' } } deadline depth' fuel'
            | .error _ =>
              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                { state with resources := { state.resources with
                    slist := slist' } } deadline depth' fuel') w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 2 = (m + 1) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  rw [hbest]
  simp only [htargets]
  · rw [run_log_bind_eq, hsub]
    rfl
  · exact htargets

/-- **Generic bind inversion for `Prog.run`**: a successful fueled run of `p >>= k` splits into a
    successful run of `p` (some prefix of the fuel) followed by a successful run of the
    continuation on `p`'s result and world — with the sub-fuels jointly bounded by the whole.
    The glueless `.paused` arm's workhorse (the inner `ioResumeLoop` sub-run is a `>>=` prefix of
    the composite body, not a single-command step like the `run_*_bind_inv` family). -/
theorem run_bind_inv {α β : Type} : ∀ {n : Nat} {p : Prog α} {k : α → Prog β} {w : World}
    {r : β × World},
    Prog.run n (p >>= k) w = some r →
    ∃ (m₁ m₂ : Nat) (x : α) (w₂ : World), m₁ + m₂ ≤ n
      ∧ Prog.run m₁ p w = some (x, w₂) ∧ Prog.run m₂ (k x) w₂ = some r := by
  intro n
  induction n with
  | zero =>
    intro p k w r h
    cases p with
    | pure a => exact ⟨0, 0, a, w, Nat.le_refl 0, run_pure 0 a w, h⟩
    | step c kk =>
      exact absurd h (by
        rw [show ((Prog.step c kk) >>= k) = Prog.step c (fun r0 => (kk r0).bind k) from rfl]
        simp [Prog.run])
  | succ n ih =>
    intro p k w r h
    cases p with
    | pure a => exact ⟨0, n + 1, a, w, by omega, run_pure 0 a w, h⟩
    | step c kk =>
      rw [show ((Prog.step c kk) >>= k) = Prog.step c (fun r0 => (kk r0) >>= k) from rfl,
        run_step] at h
      obtain ⟨m₁, m₂, x, w₂, hle, h1, h2⟩ := ih h
      exact ⟨m₁ + 1, m₂, x, w₂, by omega, by rw [run_step]; exact h1, h2⟩

/-- **A `Prog.run` mutates only `trace`/`idCtr`**: the oracle, clock, and id stream of the final
    world are the entry world's (`DnsCmd.run`: `now`/`exchange` leave the world untouched;
    `randomId` bumps `idCtr`; `log` appends to `trace`). Lets the driver re-export `WorldModels`
    (oracle-only) across an inner sub-run whose own driver exports are unavailable (a FAILED
    glueless sub-resolution, whose partial cache writes the impl drops). -/
theorem run_world_frame {α : Type} : ∀ {n : Nat} {p : Prog α} {w : World} {x : α} {w' : World},
    Prog.run n p w = some (x, w') →
    w'.oracle = w.oracle ∧ w'.clock = w.clock ∧ w'.ids = w.ids := by
  intro n
  induction n with
  | zero =>
    intro p w x w' h
    cases p with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact ⟨rfl, rfl, rfl⟩
    | step c k => exact absurd h (by simp [Prog.run])
  | succ n ih =>
    intro p w x w' h
    cases p with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact ⟨rfl, rfl, rfl⟩
    | step c k =>
      rw [run_step] at h
      have hrec := ih h
      cases c <;> exact hrec

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_bizarre_recurses
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32)
    (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀ = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    ∃ w2, Prog.run (m + 5) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          (Server.boundStateCache
            { Server.dropIfBizarre { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } } entry.name resp
              with lastResponse := none, currentStep := .sendQueries }) deadline depth fuel') w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 5 = (m + 4) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  case h.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq, if_neg (by simp [hunfollow])]
  rw [afterResume_bizarre { state with resources := { state.resources with
      slist := state.resources.slist.markQueried entry.name } } entry.name resp hstep hcname hbiz]

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_bizarre_recurses'
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32)
    (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀ = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    ∃ w2, (∀ m, Prog.run (m + 5) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1)) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          (Server.boundStateCache
            { Server.dropIfBizarre { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } } entry.name resp
              with lastResponse := none, currentStep := .sendQueries }) deadline depth fuel') w2)
      ∧ w2.oracle = w.oracle ∧ w2.clock = w.clock ∧ w2.ids = w.ids ∧ w2.idCtr = w.idCtr + 1 := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [Server.ioResumeLoop, show m + 5 = (m + 4) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
    simp only [hbest, hbuild]
    case refine_1.x_3 => intro d' n _ hn; rw [hglueless] at hn; simp at hn
    rw [show m + 4 = (m + 1) + 3 from rfl,
      run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
    dsimp only
    rw [haccResp, run_log_bind_eq, if_neg (by simp [hunfollow])]
    rw [afterResume_bizarre { state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } } entry.name resp hstep hcname hbiz]
  · rfl
  · rfl
  · rfl
  · rfl

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_retryThenAnswer
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel'' : Nat) (w : World)

    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hstep : state.currentStep = .sendQueries) (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hglueless : state.resources.slist.addressTargets[0]? = none)
    (hbuild : Resolver.buildSubQuery state = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode (Server.withRandomId subQuery₀ (w.ids w.idCtr)))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse (Server.withRandomId subQuery₀ (w.ids w.idCtr)) resp₀ = some resp)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true)

    (stateₐ : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)
    (hstateₐ : stateₐ = Server.boundStateCache
        { Server.dropIfBizarre { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } entry.name resp
          with lastResponse := none, currentStep := .sendQueries })
    (entry₂ : SlistEntry) (ipAddr₂ : BitVec 32) (subQuery₀₂ resp02 resp₀2 resp2 : VeriDNS.Spec.Format)
    (d₂ : VeriDNS.Spec.Exchanged ByteArray) (bytes₂ : ByteArray)
    (hstep₂ : stateₐ.currentStep = .sendQueries)
    (hbest₂ : stateₐ.resources.slist.bestWithAddress = some (entry₂, ipAddr₂))
    (hglueless₂ : stateₐ.resources.slist.addressTargets[0]? = none)
    (hbuild₂ : Resolver.buildSubQuery stateₐ = some subQuery₀₂)
    (horacle₂ : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withRandomId subQuery₀₂ (w.ids (w.idCtr + 1)))) (Server.ipv4ToAddr ipAddr₂) = some d₂)
    (haccept₂ : Server.acceptExchanged (Server.ipv4ToAddr ipAddr₂) d₂ = some bytes₂)
    (hdecode₂ : VeriDNS.Impl.Message.decode bytes₂ = .ok resp02)
    (hsani₂ : Server.sanitizeTtlsCap resp02 = some resp₀2)
    (haccResp₂ : Server.acceptResponse (Server.withRandomId subQuery₀₂ (w.ids (w.idCtr + 1))) resp₀2
        = some resp2)
    (hunfollow₂ : Server.unfollowableDelegationB
        (stateₐ.resources.slist.markQueried entry₂.name) stateₐ.resources.sname resp2 = false)
    (hcname₂ : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp2 = none)
    (hsf₂ : (resp2.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls₂ : Resolver.classifiableB resp2 = true)
    (hans₂ : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp2 = true) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel'' + 2)) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ stateₐ with resources := { stateₐ.resources with
                slist := stateₐ.resources.slist.markQueried entry₂.name } })
              with lastResponse := some resp2, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp2),

          (Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            stateₐ.resources.cache resp2
            (Resolver.bailiwickRaws (RR := VeriDNS.Spec.ResourceRecord)
              stateₐ.resources.sname resp2.answer)
            (Resolver.credAnswer (resp2.header.aa == 1)) stateₐ.now).boundExpiryClasses), w') := by
  subst hstateₐ
  obtain ⟨w2, heq, ho, hc, hi, hic⟩ := run_ioResumeLoop_bizarre_recurses'
    sbelt state deadline depth (fuel'' + 1) w entry ipAddr subQuery₀ resp0 resp₀ resp d bytes
    hstep hdl hbest hglueless hbuild horacle haccept hdecode hsani haccResp hunfollow hcname hbiz
  obtain ⟨K₂, w', h2⟩ := run_ioResumeLoop_answer sbelt _ deadline depth fuel'' w2
    entry₂ ipAddr₂ subQuery₀₂ d₂ bytes₂ resp02 resp₀2 resp2
    hstep₂ (by rw [hc]; exact hdl) hbest₂ hglueless₂ hbuild₂
    (by rw [ho, hi, hic]; exact horacle₂) haccept₂ hdecode₂ hsani₂
    (by rw [hi, hic]; exact haccResp₂) hunfollow₂ hcname₂ hsf₂ hcls₂ hans₂
  exact ⟨K₂ + 5, w', (heq K₂).trans h2⟩

end VeriDNS.Proof.FreeIO
