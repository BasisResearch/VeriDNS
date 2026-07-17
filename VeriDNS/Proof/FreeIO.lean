import VeriDNS.Proof.Refinement

namespace VeriDNS.Proof.FreeIO

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache

inductive DnsCmd where
  | now
  | randomId
  | exchange (q : ByteArray) (addr : ByteArray)
  | tcpExchange (q : ByteArray) (addr : ByteArray)
  | sendTo (data : ByteArray) (addr : ByteArray)
  | tcpSend (data : ByteArray)
  | log (msg : String)

def DnsCmd.Res : DnsCmd → Type
  | .now => UInt32
  | .randomId => UInt16
  | .exchange _ _ => Option (VeriDNS.Spec.Exchanged ByteArray)
  | .tcpExchange _ _ => Option ByteArray
  | .sendTo _ _ => Unit
  | .tcpSend _ => Unit
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

theorem Prog.bind_assoc {α β γ : Type} (p : Prog α) (f : α → Prog β) (g : β → Prog γ) :
    (p.bind f).bind g = p.bind (fun x => (f x).bind g) := by
  induction p with
  | pure a => rfl
  | step c k ih => simp only [Prog.bind]; exact congrArg (Prog.step c) (funext fun r => ih r)

theorem Prog.bind_assoc' {α β γ : Type} (p : Prog α) (f : α → Prog β) (g : β → Prog γ) :
    (p >>= f) >>= g = p >>= (fun x => f x >>= g) := Prog.bind_assoc p f g

instance instUdp : UdpSocket Prog Unit ByteArray where
  recvFrom _ _ := .pure default
  sendTo _ d a := .step (.sendTo d a) .pure
  now := .step .now .pure
  randomId := .step .randomId .pure
  exchange q a := .step (.exchange q a) .pure
  tcpExchange q a := .step (.tcpExchange q a) .pure
  tcpSend _ d := .step (.tcpSend d) .pure
  log s := .step (.log s) .pure

structure World where
  clock : UInt32
  ids : Nat → UInt16
  oracle : ByteArray → ByteArray → Option (VeriDNS.Spec.Exchanged ByteArray)
  tcpOracle : ByteArray → ByteArray → Option ByteArray
  trace : List String
  idCtr : Nat
  /-- Client-reply UDP sends (finding 054): every `UdpSocket.sendTo` the
  server performs is recorded as `(payload, destination)`. -/
  sent : List (ByteArray × ByteArray) := []
  /-- Client-reply TCP sends (finding 054): every `UdpSocket.tcpSend` payload
  (already TCP-framed) the server performs. -/
  tcpSent : List ByteArray := []
  /-- Latency schedule (finding 061): `tick i` is the wall-clock time the
  `i`-th network exchange costs.  `.exchange`/`.tcpExchange` advance `clock`
  by `tick exchCtr`, so `.now` reads a LIVE clock: deadline tests are
  genuinely bivalent (a slow schedule crosses the deadline mid-resolution, a
  zero schedule never does).  The default `fun _ => 0` is the zero-latency
  world, which reproduces the pre-061 frozen-clock behaviour exactly. -/
  tick : Nat → UInt32 := fun _ => 0
  /-- Number of network exchanges performed so far (indexes into `tick`). -/
  exchCtr : Nat := 0

/-- The world after one network exchange (finding 061): the latency schedule
advances the clock by `tick exchCtr` and the exchange counter by one. -/
def World.afterExchange (w : World) : World :=
  { w with clock := w.clock + w.tick w.exchCtr, exchCtr := w.exchCtr + 1 }

@[simp] theorem World.afterExchange_oracle (w : World) : w.afterExchange.oracle = w.oracle := rfl
@[simp] theorem World.afterExchange_tcpOracle (w : World) :
    w.afterExchange.tcpOracle = w.tcpOracle := rfl
@[simp] theorem World.afterExchange_ids (w : World) : w.afterExchange.ids = w.ids := rfl
@[simp] theorem World.afterExchange_idCtr (w : World) : w.afterExchange.idCtr = w.idCtr := rfl
@[simp] theorem World.afterExchange_trace (w : World) : w.afterExchange.trace = w.trace := rfl
@[simp] theorem World.afterExchange_sent (w : World) : w.afterExchange.sent = w.sent := rfl
@[simp] theorem World.afterExchange_tcpSent (w : World) :
    w.afterExchange.tcpSent = w.tcpSent := rfl
@[simp] theorem World.afterExchange_tick (w : World) : w.afterExchange.tick = w.tick := rfl
@[simp] theorem World.afterExchange_exchCtr (w : World) :
    w.afterExchange.exchCtr = w.exchCtr + 1 := rfl
@[simp] theorem World.afterExchange_clock (w : World) :
    w.afterExchange.clock = w.clock + w.tick w.exchCtr := rfl

def DnsCmd.run : (c : DnsCmd) → World → DnsCmd.Res c × World
  | .now, w => (w.clock, w)
  | .randomId, w => (w.ids w.idCtr, { w with idCtr := w.idCtr + 1 })
  | .exchange q a, w => (w.oracle q a, w.afterExchange)
  | .tcpExchange q a, w => (w.tcpOracle q a, w.afterExchange)
  | .sendTo d a, w => ((), { w with sent := w.sent ++ [(d, a)] })
  | .tcpSend d, w => ((), { w with tcpSent := w.tcpSent ++ [d] })
  | .log s, w => ((), { w with trace := w.trace ++ [s] })

def Prog.run {α} : Nat → Prog α → World → Option (α × World)
  | _, .pure a, w => some (a, w)
  | 0, .step _ _, _ => none
  | n + 1, .step c k, w => let p := c.run w; Prog.run n (k p.1) p.2

@[simp] theorem run_pure {α} (n : Nat) (a : α) (w : World) :
    Prog.run n (Prog.pure a) w = some (a, w) := by cases n <;> rfl

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

theorem run_agree {α} {n m : Nat} {p : Prog α} {w : World} {r r' : α × World}
    (h : Prog.run n p w = some r) (h' : Prog.run m p w = some r') : r = r' := by
  rcases Nat.le_total n m with hle | hle
  · have hm := run_mono h (m - n)
    rw [show n + (m - n) = m by omega] at hm
    exact Option.some.inj (hm.symm.trans h')
  · have hm := run_mono h' (n - m)
    rw [show m + (n - m) = n by omega] at hm
    exact Option.some.inj (h.symm.trans hm)

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
      = some (Server.sanitizeTtlsCap resp, w.afterExchange) := by
  unfold Server.forwardQuery
  simp only [bind]
  show Prog.run (k + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]
  simp only [DnsCmd.run, horacle, Prog.bind, haccept, hdecode]
  exact run_pure k _ _

theorem run_bind_pureSome {β} (m : Nat) (a : Option VeriDNS.Spec.Format) (k : Option VeriDNS.Spec.Format → Prog β)
    (w : World) : Prog.run m (pure a >>= k) w = Prog.run m (k a) w := rfl

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

theorem run_sendTo (n : Nat) (s : Unit) (d a : ByteArray) (w : World) :
    Prog.run (n + 1) (UdpSocket.sendTo (M := Prog) (Sock := Unit) s d a) w
      = some ((), { w with sent := w.sent ++ [(d, a)] }) := by
  show Prog.run (n + 1) (Prog.step (.sendTo d a) Prog.pure) w = _
  rw [run_step]; exact run_pure n _ _

theorem run_tcpSend (n : Nat) (s : Unit) (d : ByteArray) (w : World) :
    Prog.run (n + 1) (UdpSocket.tcpSend (M := Prog) (Sock := Unit) (Addr := ByteArray) s d) w
      = some ((), { w with tcpSent := w.tcpSent ++ [d] }) := by
  show Prog.run (n + 1) (Prog.step (.tcpSend d) Prog.pure) w = _
  rw [run_step]; exact run_pure n _ _

theorem run_sendTo_inv {n : Nat} {s : Unit} {d a : ByteArray} {w : World}
    {u : Unit} {w' : World}
    (h : Prog.run n (UdpSocket.sendTo (M := Prog) (Sock := Unit) s d a) w = some (u, w')) :
    w' = { w with sent := w.sent ++ [(d, a)] } := by
  match n with
  | 0 => exact nomatch h
  | n + 1 =>
    rw [run_sendTo n s d a w] at h
    exact (Prod.mk.injEq .. ▸ Option.some.inj h).2.symm ▸ rfl

theorem run_tcpSend_inv {n : Nat} {s : Unit} {d : ByteArray} {w : World}
    {u : Unit} {w' : World}
    (h : Prog.run n (UdpSocket.tcpSend (M := Prog) (Sock := Unit) (Addr := ByteArray) s d) w
      = some (u, w')) :
    w' = { w with tcpSent := w.tcpSent ++ [d] } := by
  match n with
  | 0 => exact nomatch h
  | n + 1 =>
    rw [run_tcpSend n s d w] at h
    exact (Prod.mk.injEq .. ▸ Option.some.inj h).2.symm ▸ rfl

theorem run_sendTo_bind {β} {m} (s : Unit) (d a : ByteArray) (k : Unit → Prog β) (w : World) {r}
    (hk : Prog.run m (k ()) { w with sent := w.sent ++ [(d, a)] } = some r) :
    Prog.run (m + 1) ((UdpSocket.sendTo (M := Prog) (Sock := Unit) s d a) >>= k) w
      = some r := by
  show Prog.run (m + 1) (Prog.step (.sendTo d a) (fun x => (Prog.pure x).bind k)) w = some r
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]; exact hk

theorem run_tcpSend_bind {β} {m} (s : Unit) (d : ByteArray) (k : Unit → Prog β) (w : World) {r}
    (hk : Prog.run m (k ()) { w with tcpSent := w.tcpSent ++ [d] } = some r) :
    Prog.run (m + 1)
      ((UdpSocket.tcpSend (M := Prog) (Sock := Unit) (Addr := ByteArray) s d) >>= k) w
      = some r := by
  show Prog.run (m + 1) (Prog.step (.tcpSend d) (fun x => (Prog.pure x).bind k)) w = some r
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]; exact hk

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
    (hk : Prog.run m (k (Server.sanitizeTtlsCap resp)) w.afterExchange = some r) :
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
    (deadline : UInt32) (depth revealed : Nat) :
    Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth 0 revealed) w
      = some ((.error "resolveWithIO: max IO rounds", state.resources.cache), w) := by
  rw [Server.ioResumeLoop]
  exact run_pure n _ w

open VeriDNS.Proof.Refinement in
theorem ioResumeLoop_sound_zero
    (net : VeriDNS.Spec.Net.Network) (ns : VeriDNS.Spec.Net.NetState) (ra : String) (ednsBuf : Nat)
    (rttOf : String → Nat) (nseen : List VeriDNS.Spec.Net.Name) (seen : List VeriDNS.Spec.Net.Name) (slist : List String)
    (q : VeriDNS.Spec.Net.Query) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache VeriDNS.Spec.SlistEntry VeriDNS.Spec.ResourceRecord)
    (deadline : UInt32) (depth n revealed : Nat) (w w' : World) (resp : VeriDNS.Spec.Format) (cout : DnsCache)
    (hrun : Prog.run n (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth 0 revealed) w
        = some ((.ok resp, cout), w')) :
    HasVerdict net ns ra ednsBuf rttOf (αTime state.now) nseen seen
      (αCache state.resources.cache) slist q (αResp resp) := by
  rw [run_ioResumeLoop_fuel_zero] at hrun
  exact absurd hrun (by simp)

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_answer
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
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
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),

          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundLru
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            state.now)), w') := by
  apply Exists.intro 6; apply Exists.intro
  rw [Server.ioResumeLoop]
  refine run_now_bind _ w ?_
  rw [if_neg hdl]
  simp only [Prog.pure_bind]
  simp only [hbest, hbuild]
  refine run_log_bind _ _ w ?_
  refine run_randomId_bind _ _ ?_
  refine run_randomId_bind _ _ ?_
  rw [if_neg (show ¬ (Server.blockedEgress ipAddr = true) by simp [hegress])]
  refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
  rw [hsani]
  dsimp only
  rw [haccResp]
  refine run_log_bind _ _ _ ?_
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
    if_neg (by simp [hprobe]), if_neg (by simp [hprobe])]
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
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state (Server.seedRevealed state) = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname (Server.seedRevealed state) = false)
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
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hans : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ K w', Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now (fuel' + 1) depth budget) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),

          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            state.resources.cache resp
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp) resp.answer)
            (Resolver.credAnswer (resp.header.aa == 1)) state.now).boundLru
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            state.now)), w') := by
  unfold Server.resolveWithIO
  rw [hpause]
  exact run_ioResumeLoop_answer sbelt state (now + budget) depth fuel' (Server.seedRevealed state)
    w entry ipAddr subQuery₀
    d bytes resp0 resp₀ resp hsendq hdl hbest hegress hbuild hprobe horacle haccept hdecode hsani
    haccResp htc hunfollow hcname hsf hcls hans hfe

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_nxdomain
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hsendq : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = false)
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
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hsf : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls : Resolver.classifiableB resp = true)
    (hnerr : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true)
    (hans : Resolver.answersQueryB (RR := VeriDNS.Spec.ResourceRecord) resp = false)
    (hemp : resp.answer.isEmpty = true) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ state with resources := { state.resources with
                slist := state.resources.slist.markQueried entry.name } })
              with lastResponse := some resp, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp),
          (Server.boundStateCache
            (Server.roundTouches { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } resp)
            ({ ({ state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } })
                with lastResponse := some resp, currentStep := .analyzeResponse }
                : Resolver.State DnsSList DnsCache SlistEntry
                    VeriDNS.Spec.ResourceRecord)).resources.cache), w') := by
  apply Exists.intro 6; apply Exists.intro
  rw [Server.ioResumeLoop]
  refine run_now_bind _ w ?_
  rw [if_neg hdl]
  simp only [Prog.pure_bind]
  simp only [hbest, hbuild]
  refine run_log_bind _ _ w ?_
  refine run_randomId_bind _ _ ?_
  refine run_randomId_bind _ _ ?_
  rw [if_neg (show ¬ (Server.blockedEgress ipAddr = true) by simp [hegress])]
  refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
  rw [hsani]
  dsimp only
  rw [haccResp]
  refine run_log_bind _ _ _ ?_
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  have hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false := by
    cases hrc : resp.header.rcode <;>
      first | rfl | (rw [hrc] at hnerr; exact absurd hnerr (by decide))
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
    if_neg (by simp [hprobe]), if_neg (by simp [hprobe])]
  rw [afterResume_nameError
      { state with resources := { state.resources with
          slist := state.resources.slist.markQueried entry.name } }
      entry.name resp hsendq hcname hsf hcls hnerr hans hemp]
  exact run_pure _ _ _



theorem run_ioResumeLoop_referral_lift
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
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
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ w',
      (∀ (K : Nat) (r : (Except String VeriDNS.Spec.Format × DnsCache) × World),
          Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt st deadline depth fuel'
              (Server.revealedAfterContinue state.resources.sname revealed st)) w' = some r →
          Prog.run (K + 6) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
              sbelt state deadline depth (fuel' + 1) revealed) w = some r)
      ∧ w'.oracle = w.oracle ∧ w'.tcpOracle = w.tcpOracle
      ∧ w'.ids = w.ids ∧ w'.clock = w.clock + w.tick w.exchCtr
      ∧ w'.exchCtr = w.exchCtr + 1 ∧ w'.tick = w.tick ∧ w'.idCtr = w.idCtr + 2 := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K r hk
    rw [Server.ioResumeLoop]
    refine run_now_bind _ w ?_
    rw [if_neg hdl]
    simp only [hbest, hbuild]
    refine run_log_bind _ _ w ?_
    refine run_randomId_bind _ _ ?_
    refine run_randomId_bind _ _ ?_
    rw [if_neg (show ¬ (Server.blockedEgress ipAddr = true) by simp [hegress])]
    refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
    rw [hsani]
    dsimp only
    rw [haccResp]
    refine run_log_bind _ _ _ ?_
    rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
    dsimp only []
    rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
      if_neg (by simp [hpdeny]), if_neg (by simp [hpconsume])]
    rw [hcont]
    exact hk
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem run_ioResumeLoop_probeConsume_lift
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
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
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ w',
      (∀ (K : Nat) (r : (Except String VeriDNS.Spec.Format × DnsCache) × World),
          Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
              { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } }
              deadline depth fuel'
              (Resolver.bumpRevealed state.resources.sname revealed)) w' = some r →
          Prog.run (K + 7) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
              sbelt state deadline depth (fuel' + 1) revealed) w = some r)
      ∧ w'.oracle = w.oracle ∧ w'.tcpOracle = w.tcpOracle
      ∧ w'.ids = w.ids ∧ w'.clock = w.clock + w.tick w.exchCtr
      ∧ w'.exchCtr = w.exchCtr + 1 ∧ w'.tick = w.tick ∧ w'.idCtr = w.idCtr + 2 := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K r hk
    rw [Server.ioResumeLoop]
    refine run_now_bind _ w ?_
    rw [if_neg hdl]
    simp only [hbest, hbuild]
    refine run_log_bind _ _ w ?_
    refine run_randomId_bind _ _ ?_
    refine run_randomId_bind _ _ ?_
    rw [if_neg (show ¬ (Server.blockedEgress ipAddr = true) by simp [hegress])]
    refine run_forwardQuery_bind _ _ _ _ d bytes resp0 horacle haccept hdecode ?_
    rw [hsani]
    dsimp only
    rw [haccResp]
    refine run_log_bind _ _ _ ?_
    rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
    dsimp only []
    rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
      if_neg (by simp [hprobe, hdeny]),
      if_pos (by simp [hprobe, hpass])]
    refine run_log_bind _ _ _ ?_
    exact hk
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

@[simp] theorem World.ids_trace (w : World) (t) : ({ w with trace := t } : World).ids = w.ids := rfl
@[simp] theorem World.idCtr_trace (w : World) (t) :
    ({ w with trace := t } : World).idCtr = w.idCtr := rfl

theorem seqPureUnit {α} (X : Prog α) : (do pure PUnit.unit; X) = X := rfl

theorem run_now_bind_eq {β m} (k : UInt32 → Prog β) (w : World) :
    Prog.run (m + 1) ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) w
      = Prog.run m (k w.clock) w := by
  show Prog.run (m + 1) (Prog.step .now (fun x => (Prog.pure x).bind k)) w = _
  rw [run_step]; simp only [DnsCmd.run, Prog.bind]

theorem run_ioResumeLoop_deadline (w : World) (m : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (hdl : w.clock ≥ deadline) :
    Prog.run (m + 1) (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth (fuel' + 1) revealed) w
      = some ((.error "resolveWithIO: query deadline exceeded", state.resources.cache), w) := by
  unfold Server.ioResumeLoop
  rw [run_now_bind_eq]
  simp only [if_pos hdl]
  exact run_pure m _ w

theorem run_ioResumeLoop_noserver (w : World) (m : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = none)
    (htgt : state.resources.slist.addressTargets[0]? = none) :
    Prog.run (m + 1) (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth (fuel' + 1) revealed) w
      = some ((.error "resolveWithIO: no servers with addresses in SLIST", state.resources.cache), w) := by
  unfold Server.ioResumeLoop
  rw [run_now_bind_eq]
  simp only [if_neg hdl, hbest, seqPureUnit, htgt]
  exact run_pure m _ w

theorem run_ioResumeLoop_nobuild (w : World) (m : Nat) (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (entry : SlistEntry) (ipAddr : BitVec 32)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hbuild : Resolver.buildSubQuery state revealed = none) :
    Prog.run (m + 1) (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt state deadline depth (fuel' + 1) revealed) w
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
      = Prog.run m (k (Server.sanitizeTtlsCap resp)) w.afterExchange := by
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

theorem run_log_randomId2_bind_eq {β m} (s : String) (k : UInt16 → UInt16 → Prog β) (w : World) :
    Prog.run (m + 3)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          let cid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          k rid cid) w
      = Prog.run m (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
          { w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } := by
  rw [show m + 3 = (m + 1) + 2 from rfl,
    run_log_randomId_bind_eq (k := fun rid =>
      UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray) >>= k rid),
    run_randomId_bind_eq]

theorem run_round_bind_eq {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray) (resp : VeriDNS.Spec.Format)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp) :
    Prog.run (m + 4)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          let cid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
            >>= k rid cid) w
      = Prog.run m (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)) (Server.sanitizeTtlsCap resp))
          ({ w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } : World).afterExchange := by
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_log_randomId2_bind_eq (k := fun rid cid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
        >>= k rid cid),
    run_forwardQuery_bind_eq (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) addr
      (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } d bytes resp horacle haccept hdecode]

theorem run_forwardQuery_bind_eq_none {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = none) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w.afterExchange := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind]; rfl

theorem run_forwardQuery_bind_eq_acceptNone {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) (d : VeriDNS.Spec.Exchanged ByteArray)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = none) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w.afterExchange := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, haccept]; rfl

theorem run_forwardQuery_bind_eq_decodeError {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) (d : VeriDNS.Spec.Exchanged ByteArray)
    (bytes : ByteArray) (errmsg : String)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode query) addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .error errmsg) :
    Prog.run (m + 1) ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w.afterExchange := by
  unfold Server.forwardQuery; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.exchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, haccept, hdecode]; rfl

theorem run_round_bind_eq_none {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        addr = none) :
    Prog.run (m + 4)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          let cid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
            >>= k rid cid) w
      = Prog.run m (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)) none)
          ({ w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } : World).afterExchange := by
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_log_randomId2_bind_eq (k := fun rid cid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
        >>= k rid cid),
    run_forwardQuery_bind_eq_none (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
      addr (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } horacle]

theorem run_round_bind_eq_acceptNone {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World)
    (d : VeriDNS.Spec.Exchanged ByteArray)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        addr = some d)
    (haccept : Server.acceptExchanged addr d = none) :
    Prog.run (m + 4)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          let cid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
            >>= k rid cid) w
      = Prog.run m (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)) none)
          ({ w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } : World).afterExchange := by
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_log_randomId2_bind_eq (k := fun rid cid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
        >>= k rid cid),
    run_forwardQuery_bind_eq_acceptNone
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) addr
      (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } d horacle haccept]

theorem run_round_bind_eq_decodeError {β m} (s : String) (subQuery₀ : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : UInt16 → UInt16 → Option VeriDNS.Spec.Format → Prog β) (w : World)
    (d : VeriDNS.Spec.Exchanged ByteArray)
    (bytes : ByteArray) (errmsg : String)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        addr = some d)
    (haccept : Server.acceptExchanged addr d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .error errmsg) :
    Prog.run (m + 4)
      (do UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s
          let rid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          let cid ← UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)
          (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
            >>= k rid cid) w
      = Prog.run m (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)) none)
          ({ w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } : World).afterExchange := by
  rw [show m + 4 = (m + 1) + 3 from rfl,
    run_log_randomId2_bind_eq (k := fun rid cid =>
      (Server.forwardQuery (M := Prog) (Sock := Unit) (Server.withSecrets subQuery₀ rid cid) addr)
        >>= k rid cid),
    run_forwardQuery_bind_eq_decodeError
      (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) addr
      (k (w.ids w.idCtr) (w.ids (w.idCtr + 1)))
      { w with trace := w.trace ++ [s], idCtr := w.idCtr + 2 } d bytes errmsg horacle haccept hdecode]



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



theorem run_tcpForward_bind_eq {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World)
    (bytes : ByteArray) (resp : VeriDNS.Spec.Format)
    (horacle : w.tcpOracle (VeriDNS.Impl.Message.encode query) addr = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp) :
    Prog.run (m + 1) ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k (Server.sanitizeTtlsCap resp)) w.afterExchange := by
  unfold Server.tcpForward; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.tcpExchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, hdecode]; rfl

theorem run_tcpForward_bind_eq_none {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World)
    (horacle : w.tcpOracle (VeriDNS.Impl.Message.encode query) addr = none) :
    Prog.run (m + 1) ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w.afterExchange := by
  unfold Server.tcpForward; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.tcpExchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind]; rfl

theorem run_tcpForward_bind_eq_decodeError {β m} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) (bytes : ByteArray) (errmsg : String)
    (horacle : w.tcpOracle (VeriDNS.Impl.Message.encode query) addr = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .error errmsg) :
    Prog.run (m + 1) ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) w
      = Prog.run m (k none) w.afterExchange := by
  unfold Server.tcpForward; simp only [bind]
  show Prog.run (m + 1) (Prog.step (.tcpExchange (VeriDNS.Impl.Message.encode query) addr) _) w = _
  rw [run_step]; simp only [DnsCmd.run, horacle, Prog.bind, hdecode]; rfl

theorem run_tcpForward_bind_inv {β} {n : Nat} (query : VeriDNS.Spec.Format) (addr : ByteArray)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) {r : β × World}
    (h : Prog.run n ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) w = some r) :
    ∃ m, n = m + 1 := by
  cases n with
  | zero =>
    rw [show Prog.run 0 ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) w
      = none from rfl] at h
    exact absurd h (by simp)
  | succ m => exact ⟨m, rfl⟩

theorem run_tcpFallbackGuard_inv {β} {n : Nat}
    (subQuery : VeriDNS.Spec.Format) (addr : ByteArray) (s1 : String)
    (k : Option VeriDNS.Spec.Format → Prog β) (w : World) {r : β × World}
    (h : Prog.run n ((do
          UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s1
          match ← Server.tcpForward (M := Prog) (Sock := Unit) subQuery addr with
          | none => pure none
          | some tcpResp =>
            match Server.acceptResponse subQuery tcpResp with
            | none => pure none
            | some tcpRespA =>
              pure (if tcpRespA.header.tc == 1 then none else some tcpRespA)) >>= k) w
        = some r) :
    (∃ m, n = m + 2 ∧ Prog.run m (k none)
        ({ w with trace := w.trace ++ [s1] } : World).afterExchange = some r) ∨
    (∃ m bytes raw tcpResp tcpRespA, n = m + 2 ∧
        w.tcpOracle (VeriDNS.Impl.Message.encode subQuery) addr = some bytes ∧
        VeriDNS.Impl.Message.decode bytes = .ok raw ∧
        Server.sanitizeTtlsCap raw = some tcpResp ∧
        Server.acceptResponse subQuery tcpResp = some tcpRespA ∧
        (tcpRespA.header.tc == 1) = false ∧
        Prog.run m (k (some tcpRespA))
          ({ w with trace := w.trace ++ [s1] } : World).afterExchange = some r) := by
  rw [Prog.bind_assoc'] at h
  obtain ⟨mLog, hmLog, h⟩ := run_log_bind_inv _ _ _ h
  rw [Prog.bind_assoc'] at h
  obtain ⟨mT, hmT⟩ := run_tcpForward_bind_inv _ _ _ _ h
  subst hmT
  have hOw : ({ w with trace := w.trace ++ [s1] } : World).tcpOracle
      (VeriDNS.Impl.Message.encode subQuery) addr
      = w.tcpOracle (VeriDNS.Impl.Message.encode subQuery) addr := rfl
  cases hO : w.tcpOracle (VeriDNS.Impl.Message.encode subQuery) addr with
  | none =>
    left
    rw [run_tcpForward_bind_eq_none _ _ _ _ (hOw.trans hO)] at h
    dsimp only [] at h
    exact ⟨mT, by omega, h⟩
  | some bytes =>
    cases hdec : VeriDNS.Impl.Message.decode bytes with
    | error e =>
      left
      rw [run_tcpForward_bind_eq_decodeError _ _ _ _ _ _ (hOw.trans hO) hdec] at h
      dsimp only [] at h
      exact ⟨mT, by omega, h⟩
    | ok raw =>
      rw [run_tcpForward_bind_eq _ _ _ _ _ _ (hOw.trans hO) hdec] at h
      cases hsan : Server.sanitizeTtlsCap raw with
      | none =>
        left
        rw [hsan] at h; dsimp only [] at h
        exact ⟨mT, by omega, h⟩
      | some tcpResp =>
        rw [hsan] at h; dsimp only [] at h
        cases hacc : Server.acceptResponse subQuery tcpResp with
        | none =>
          left
          rw [hacc] at h; dsimp only [] at h
          exact ⟨mT, by omega, h⟩
        | some tcpRespA =>
          rw [hacc] at h; dsimp only [] at h
          by_cases htc2 : (tcpRespA.header.tc == 1) = true
          · left
            rw [if_pos htc2] at h
            exact ⟨mT, by omega, h⟩
          · right
            rw [if_neg htc2] at h
            exact ⟨mT, bytes, raw, tcpResp, tcpRespA, by omega, rfl, hdec, hsan, hacc,
              by simpa using htc2, h⟩

/-- Finding 052 (RFC 9156 §2.3): a probe-round timeout falls back to the full
qname — the recursion resumes at `fallbackRevealed sname revealed`, which is
`labelCount sname` at a probe round and `revealed` (unchanged) otherwise. -/
theorem run_ioResumeLoop_timeout
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = none) :
    ∃ w2, Prog.run (m + 5) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel'
          (Server.fallbackRevealed state.resources.sname revealed)) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 5 = (m + 4) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [run_round_bind_eq_none _ _ _ _ _ horacle]

theorem run_ioResumeLoop_rejectSpoof
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = none) :
    ∃ w2, Prog.run (m + 6) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel' revealed) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 6 = (m + 5) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [show m + 5 = (m + 1) + 4 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]

theorem run_ioResumeLoop_unfollowable
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = true) :
    ∃ w2, Prog.run (m + 7) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel' revealed) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 7 = (m + 6) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [show m + 6 = (m + 2) + 4 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  rw [if_pos (by simp [hunfollow]), run_log_bind_eq]

theorem run_ioResumeLoop_continue
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hsguard : (Resolver.probeRoundB state.resources.sname revealed
        && Server.strictDenialB resp) = false)
    (hpguard : (Resolver.probeRoundB state.resources.sname revealed
        && !Server.probePassableB resp) = false)
    (hcont : Server.afterResume
        { state with resources := { state.resources with
            slist := state.resources.slist.markQueried entry.name } } entry.name resp = .continue st)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ w2, Prog.run (m + 6) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt st deadline depth fuel'
          (Server.revealedAfterContinue state.resources.sname revealed st)) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 6 = (m + 5) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [show m + 5 = (m + 1) + 4 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]), if_neg (by simp [hsguard]),
    if_neg (by simp [hpguard]), hcont]

theorem run_ioResumeLoop_probeConsumed
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (hstrictF : Server.strictDenialB resp = false)
    (hpassF : Server.probePassableB resp = false)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ w2, Prog.run (m + 7) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel'
          (Resolver.bumpRevealed state.resources.sname revealed)) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 7 = (m + 6) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [show m + 6 = (m + 2) + 4 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
    if_neg (by simp [hstrictF]), if_pos (by simp [hprobe, hpassF]), run_log_bind_eq]

/-- Findings 051/064 (RFC 9156 §2.3, unbound `qname-minimisation-strict: no`):
an NXDOMAIN answering a **minimised probe** is NOT delivered to the client —
the loop consumes it and re-probes with the **full** qname (`revealed` jumps to
`labelCount sname`) against the same (marked) server set.  Only a full-name
NXDOMAIN (a non-probe round, see `run_ioResumeLoop_nxdomain`, which requires
`probeRoundB … = false`) produces a client NXDOMAIN verdict. -/
theorem run_ioResumeLoop_probeNxdomainFallsBack
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hprobe : Resolver.probeRoundB state.resources.sname revealed = true)
    (hstrict : Server.strictDenialB resp = true) :
    ∃ w2, Prog.run (m + 7) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } deadline depth fuel'
          (VeriDNS.Impl.DomainName.labelCount state.resources.sname)) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 7 = (m + 6) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [show m + 6 = (m + 2) + 4 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  have hne : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true := by
    have h := hstrict
    unfold Server.strictDenialB at h
    exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2
  have hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false := by
    cases hrc : resp.header.rcode <;>
      first | rfl | (rw [hrc] at hne; exact absurd hne (by decide))
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
    if_pos (by simp [hprobe, hstrict]), run_log_bind_eq]

theorem run_gluelessUpdatedSlist_resolved (slist : DnsSList) (nsName : ByteArray)
    (subResp : VeriDNS.Spec.Format) (addr : BitVec 32) (m : Nat) (w : World)
    (haddr : Server.extractAAddress nsName subResp.answer = some addr) :
    ∃ w2, Prog.run (m + 1) (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName
        (.ok subResp)) w
      = some (slist.addAddress nsName addr, w2) := by
  apply Exists.intro
  unfold Server.gluelessUpdatedSlist
  simp only [haddr]
  rw [run_log_bind_eq]
  exact run_pure m _ _

theorem run_gluelessUpdatedSlist_resolved_bind {β : Type} {m : Nat} (slist : DnsSList) (nsName : ByteArray)
    (subResp : VeriDNS.Spec.Format) (addr : BitVec 32) (k : DnsSList → Prog β) (w : World)
    (haddr : Server.extractAAddress nsName subResp.answer = some addr) :
    ∃ w2, Prog.run (m + 1) (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName
        (.ok subResp) >>= k) w = Prog.run m (k (slist.addAddress nsName addr)) w2 := by
  apply Exists.intro
  unfold Server.gluelessUpdatedSlist
  simp only [haddr, Prog.bind_def, Prog.bind_assoc]
  rw [← Prog.bind_def, run_log_bind_eq]
  rfl

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
    (haddr : Server.extractAAddress nsName subResp.answer = some addr) (revealed : Nat) :
    ∃ w2, Prog.run (m + 3) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline (depth' + 1) (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          { state with resources := { state.resources with
              slist := state.resources.slist.addAddress nsName addr } } deadline depth' fuel' revealed) w2 := by
  rw [Server.ioResumeLoop, show m + 3 = (m + 2) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  rw [hbest]
  simp only [htargets]
  rw [run_log_bind_eq, hsub]
  simp only [Prog.bind_def]
  exact run_gluelessUpdatedSlist_resolved_bind state.resources.slist nsName subResp addr _ _ haddr

theorem run_ioResumeLoop_glueless_paused
    (sbelt : DnsSList) (state st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth' fuel' m : Nat) (w : World) (nsName : ByteArray)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = none)
    (htargets : state.resources.slist.addressTargets[0]? = some nsName)
    (hsub : @Resolver.resolve DnsSList DnsCache SlistEntry ResourceRecord _ _ _ _ _ _ _ _
        (Server.mkAddressQuery nsName) sbelt 64 state.now state.resources.cache
        = .ok (.paused st)) (revealed : Nat) :
    ∃ w2, Prog.run (m + 2) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline (depth' + 1) (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt st deadline depth' fuel'
            (Server.seedRevealed st)
          >>= fun (p : Except String VeriDNS.Spec.Format × DnsCache) =>
            Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit)
              state.resources.slist nsName p.1 >>= fun slist' =>
            match p.1 with
            | .ok subResp =>
              match Server.extractAAddress nsName subResp.answer with
              | some _ =>
                match Server.gluelessRecheck state p.2 with
                | some hit =>
                  pure (.ok hit, p.2.touchKeys (Server.recheckTouches state) state.now)
                | none =>
                  Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                    { state with resources := { state.resources with
                        slist := slist',
                        cache := p.2.touchKeys (Server.recheckTouches state) state.now } }
                    deadline depth' fuel' revealed
              | none =>
                Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                  { state with resources := { state.resources with
                      slist := slist' } } deadline depth' fuel' revealed
            | .error _ =>
              Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
                { state with resources := { state.resources with
                    slist := slist' } } deadline depth' fuel' revealed) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 2 = (m + 1) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  rw [hbest]
  simp only [htargets]
  rw [run_log_bind_eq, hsub]
  rfl

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

theorem run_world_frame {α : Type} : ∀ {n : Nat} {p : Prog α} {w : World} {x : α} {w' : World},
    Prog.run n p w = some (x, w') →
    w'.oracle = w.oracle ∧ w'.tick = w.tick ∧ w'.ids = w.ids := by
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

theorem run_world_tcpOracle_frame {α : Type} : ∀ {n : Nat} {p : Prog α} {w : World} {x : α} {w' : World},
    Prog.run n p w = some (x, w') → w'.tcpOracle = w.tcpOracle := by
  intro n
  induction n with
  | zero =>
    intro p w x w' h
    cases p with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
    | step c k => exact absurd h (by simp [Prog.run])
  | succ n ih =>
    intro p w x w' h
    cases p with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
    | step c k =>
      rw [run_step] at h
      have hrec := ih h
      cases c <;> exact hrec

/-- Zero-latency clock frame (finding 061): in a world whose latency schedule
is identically zero, the clock never moves — the pre-061 frozen-clock
behaviour is exactly the `tick ≡ 0` special case. -/
theorem run_world_clock_frame_tick0 {α : Type} :
    ∀ {n : Nat} {p : Prog α} {w : World} {x : α} {w' : World},
    (∀ i, w.tick i = 0) → Prog.run n p w = some (x, w') → w'.clock = w.clock := by
  intro n
  induction n with
  | zero =>
    intro p w x w' htick h
    cases p with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
    | step c k => exact absurd h (by simp [Prog.run])
  | succ n ih =>
    intro p w x w' htick h
    cases p with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
    | step c k =>
      rw [run_step] at h
      cases c with
      | exchange q a =>
        have hrec : w'.clock = w.afterExchange.clock := by refine ih ?_ h; exact htick
        rw [hrec]
        show w.clock + w.tick w.exchCtr = w.clock
        rw [htick, UInt32.add_zero]
      | tcpExchange q a =>
        have hrec : w'.clock = w.afterExchange.clock := by refine ih ?_ h; exact htick
        rw [hrec]
        show w.clock + w.tick w.exchCtr = w.clock
        rw [htick, UInt32.add_zero]
      | now => exact (by refine ih ?_ h; exact htick : w'.clock = w.clock)
      | randomId =>
        exact (by refine ih ?_ h; exact htick :
          w'.clock = ({ w with idCtr := w.idCtr + 1 } : World).clock)
      | sendTo d a =>
        exact (by refine ih ?_ h; exact htick :
          w'.clock = ({ w with sent := w.sent ++ [(d, a)] } : World).clock)
      | tcpSend d =>
        exact (by refine ih ?_ h; exact htick :
          w'.clock = ({ w with tcpSent := w.tcpSent ++ [d] } : World).clock)
      | log s =>
        exact (by refine ih ?_ h; exact htick :
          w'.clock = ({ w with trace := w.trace ++ [s] } : World).clock)

private theorem strictDenialB_false_of_bizarre {resp : VeriDNS.Spec.Format}
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true) :
    Server.strictDenialB resp = false := by
  by_cases hne : (resp.header.rcode == VeriDNS.Spec.Rcode.nameError) = true
  · exfalso
    have hcls : Resolver.classifiableB resp = true := by
      unfold Resolver.classifiableB
      simp [hne]
    rw [hcls] at hbiz
    simp only [Bool.not_true, Bool.or_false] at hbiz
    have h1 : resp.header.rcode = VeriDNS.Spec.Rcode.nameError := by
      cases hrc : resp.header.rcode <;>
        first | rfl | (rw [hrc] at hne; exact absurd hne (by decide))
    rw [h1] at hbiz
    exact absurd hbiz (by decide)
  · unfold Server.strictDenialB
    simp [hne]

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_bizarre_recurses
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' m revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32)
    (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ w2, Prog.run (m + 6) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          (Server.boundStateCache
            (Server.roundTouches (Server.dropIfBizarre { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } } entry.name resp) resp)
            { Server.dropIfBizarre { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } } entry.name resp
              with lastResponse := none, currentStep := .sendQueries }) deadline depth fuel'
          (Server.revealedAfterContinue state.resources.sname revealed
            (Server.boundStateCache
              (Server.roundTouches (Server.dropIfBizarre { state with resources := { state.resources with
                    slist := state.resources.slist.markQueried entry.name } } entry.name resp) resp)
              { Server.dropIfBizarre { state with resources := { state.resources with
                    slist := state.resources.slist.markQueried entry.name } } entry.name resp
                with lastResponse := none, currentStep := .sendQueries }))) w2 := by
  apply Exists.intro
  rw [Server.ioResumeLoop, show m + 6 = (m + 5) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
  simp only [hbest, hbuild]
  simp only [hegress, Bool.false_eq_true, if_false]
  rw [show m + 5 = (m + 1) + 4 from rfl,
    run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
  dsimp only
  rw [haccResp, run_log_bind_eq]
  rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
  dsimp only []
  rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
    if_neg (by simp [strictDenialB_false_of_bizarre hbiz]),
    if_neg (by simp [Server.probePassableB, Server.retryShapedB, hcname, hbiz])]
  rw [afterResume_bizarre { state with resources := { state.resources with
      slist := state.resources.slist.markQueried entry.name } } entry.name resp hstep hcname hbiz]

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_bizarre_recurses'
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32)
    (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hstep : state.currentStep = .sendQueries)
    (hdl : ¬ (w.clock ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ w2, (∀ m, Prog.run (m + 6) (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel' + 1) revealed) w
      = Prog.run m (Server.ioResumeLoop (M := Prog) (Sock := Unit) sbelt
          (Server.boundStateCache
            (Server.roundTouches (Server.dropIfBizarre { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } } entry.name resp) resp)
            { Server.dropIfBizarre { state with resources := { state.resources with
                  slist := state.resources.slist.markQueried entry.name } } entry.name resp
              with lastResponse := none, currentStep := .sendQueries }) deadline depth fuel'
          (Server.revealedAfterContinue state.resources.sname revealed
            (Server.boundStateCache
              (Server.roundTouches (Server.dropIfBizarre { state with resources := { state.resources with
                    slist := state.resources.slist.markQueried entry.name } } entry.name resp) resp)
              { Server.dropIfBizarre { state with resources := { state.resources with
                    slist := state.resources.slist.markQueried entry.name } } entry.name resp
                with lastResponse := none, currentStep := .sendQueries }))) w2)
      ∧ w2.oracle = w.oracle ∧ w2.clock = w.clock + w.tick w.exchCtr
      ∧ w2.exchCtr = w.exchCtr + 1 ∧ w2.tick = w.tick
      ∧ w2.ids = w.ids ∧ w2.idCtr = w.idCtr + 2 := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [Server.ioResumeLoop, show m + 6 = (m + 5) + 1 from rfl, run_now_bind_eq, if_neg hdl, seqPureUnit]
    simp only [hbest, hbuild]
    simp only [hegress, Bool.false_eq_true, if_false]
    rw [show m + 5 = (m + 1) + 4 from rfl,
      run_round_bind_eq _ _ _ _ _ d bytes resp0 horacle haccept hdecode, hsani]
    dsimp only
    rw [haccResp, run_log_bind_eq]
    rw [if_neg (show ¬((resp.header.tc == 1) = true) by rw [htc]; simp), run_bind_pureSome]
    dsimp only []
    rw [if_neg (by simp [hunfollow]), if_neg (by simp [hfe]),
      if_neg (by simp [strictDenialB_false_of_bizarre hbiz]),
      if_neg (by simp [Server.probePassableB, Server.retryShapedB, hcname, hbiz])]
    rw [afterResume_bizarre { state with resources := { state.resources with
        slist := state.resources.slist.markQueried entry.name } } entry.name resp hstep hcname hbiz]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

open VeriDNS.Proof.Refinement in

theorem run_ioResumeLoop_retryThenAnswer
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel'' revealed : Nat) (w : World)

    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ resp0 resp₀ resp : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (hstep : state.currentStep = .sendQueries) (hdl : ¬ (w.clock ≥ deadline))
    (hdl₂ : ¬ (w.clock + w.tick w.exchCtr ≥ deadline))
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state revealed = some subQuery₀)
    (horacle : w.oracle (VeriDNS.Impl.Message.encode
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))))
        (Server.ipv4ToAddr ipAddr) = some d)
    (haccept : Server.acceptExchanged (Server.ipv4ToAddr ipAddr) d = some bytes)
    (hdecode : VeriDNS.Impl.Message.decode bytes = .ok resp0)
    (hsani : Server.sanitizeTtlsCap resp0 = some resp₀)
    (haccResp : Server.acceptResponse
        (Server.withSecrets subQuery₀ (w.ids w.idCtr) (w.ids (w.idCtr + 1))) resp₀ = some resp)
    (htc : (resp.header.tc == 1) = false)
    (hunfollow : Server.unfollowableDelegationB
        (state.resources.slist.markQueried entry.name) state.resources.sname resp = false)
    (hcname : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp = none)
    (hbiz : (resp.header.rcode == VeriDNS.Spec.Rcode.serverFailure
              || !Resolver.classifiableB resp) = true)
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false)

    (stateₐ : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)
    (hstateₐ : stateₐ = Server.boundStateCache
        (Server.roundTouches (Server.dropIfBizarre { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } entry.name resp) resp)
        { Server.dropIfBizarre { state with resources := { state.resources with
              slist := state.resources.slist.markQueried entry.name } } entry.name resp
          with lastResponse := none, currentStep := .sendQueries })
    (revealedₐ : Nat)
    (hrevealedₐ : revealedₐ = Server.revealedAfterContinue state.resources.sname revealed stateₐ)
    (entry₂ : SlistEntry) (ipAddr₂ : BitVec 32) (subQuery₀₂ resp02 resp₀2 resp2 : VeriDNS.Spec.Format)
    (d₂ : VeriDNS.Spec.Exchanged ByteArray) (bytes₂ : ByteArray)
    (hstep₂ : stateₐ.currentStep = .sendQueries)
    (hbest₂ : stateₐ.resources.slist.bestWithAddress = some (entry₂, ipAddr₂))
    (hegress₂ : Server.blockedEgress ipAddr₂ = false)
    (hbuild₂ : Resolver.buildSubQuery stateₐ revealedₐ = some subQuery₀₂)
    (hprobe₂ : Resolver.probeRoundB stateₐ.resources.sname revealedₐ = false)
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
        (stateₐ.resources.slist.markQueried entry₂.name) stateₐ.resources.sname resp2 = false)
    (hcname₂ : Resolver.cnameToChase (RR := VeriDNS.Spec.ResourceRecord) resp2 = none)
    (hsf₂ : (resp2.header.rcode == VeriDNS.Spec.Rcode.serverFailure) = false)
    (hcls₂ : Resolver.classifiableB resp2 = true)
    (hans₂ : Resolver.entitledAnswerB (RR := VeriDNS.Spec.ResourceRecord) resp2 = true)
    (hfe₂ : (resp2.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ K w', Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth (fuel'' + 2) revealed) w
      = some ((.ok (Resolver.finalizeAnswer
          (({ ({ stateₐ with resources := { stateₐ.resources with
                slist := stateₐ.resources.slist.markQueried entry₂.name } })
              with lastResponse := some resp2, currentStep := .analyzeResponse }
              : Resolver.State DnsSList DnsCache SlistEntry VeriDNS.Spec.ResourceRecord)) resp2),

          ((Resolver.cacheUnlessTruncated (RR := VeriDNS.Spec.ResourceRecord)
            stateₐ.resources.cache resp2
            (Resolver.ownerRaws (RR := VeriDNS.Spec.ResourceRecord)
              (Resolver.echoedQname resp2) resp2.answer)
            (Resolver.credAnswer (resp2.header.aa == 1)) stateₐ.now).boundLru
            (Server.roundTouches { stateₐ with resources := { stateₐ.resources with
              slist := stateₐ.resources.slist.markQueried entry₂.name } } resp2)
            stateₐ.now)), w') := by
  subst hstateₐ
  subst hrevealedₐ
  obtain ⟨w2, heq, ho, hc, hec, htk, hi, hic⟩ := run_ioResumeLoop_bizarre_recurses'
    sbelt state deadline depth (fuel'' + 1) revealed w entry ipAddr subQuery₀ resp0 resp₀ resp d bytes
    hstep hdl hbest hegress hbuild horacle haccept hdecode hsani haccResp htc hunfollow hcname hbiz
    hfe
  obtain ⟨K₂, w', h2⟩ := run_ioResumeLoop_answer sbelt _ deadline depth fuel''
    (Server.revealedAfterContinue state.resources.sname revealed _) w2
    entry₂ ipAddr₂ subQuery₀₂ d₂ bytes₂ resp02 resp₀2 resp2
    hstep₂ (by rw [hc]; exact hdl₂) hbest₂ hegress₂ hbuild₂ hprobe₂
    (by rw [ho, hi, hic]; exact horacle₂) haccept₂ hdecode₂ hsani₂
    (by rw [hi, hic]; exact haccResp₂) htc₂ hunfollow₂ hcname₂ hsf₂ hcls₂ hans₂ hfe₂
  exact ⟨K₂ + 6, w', (heq K₂).trans h2⟩

/-! ### Finding 061: latency budgets, timeliness, and the deadline dual

The clock is LIVE: every `.exchange`/`.tcpExchange` advances `World.clock` by
`World.tick World.exchCtr`.  `tickSum`/`TimelyWorld` give the honest budget
account the adequacy capstones use ("the cooperative world responds fast
enough for the whole descent"), and `run_ioResumeLoop_deadline_after_referral`
is the DUAL: a world whose latency crosses the deadline mid-resolution REACHES
the deadline branch and gets the deadline error (delivered to the client as
SERVFAIL by `Server.replyForResolution`).  A mutant that deletes the deadline
check — or replaces its error with anything else — breaks the dual. -/

/-- Total latency (in `ℕ`, no wraparound) of the next `k` network exchanges
starting at exchange counter `e` under latency schedule `tick`. -/
def tickSum (tick : Nat → UInt32) (e : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (tick e).toNat + tickSum tick (e + 1) k

@[simp] theorem tickSum_zero (tick : Nat → UInt32) (e : Nat) : tickSum tick e 0 = 0 := rfl

theorem tickSum_succ (tick : Nat → UInt32) (e k : Nat) :
    tickSum tick e (k + 1) = (tick e).toNat + tickSum tick (e + 1) k := rfl

/-- The zero-latency schedule has zero total latency: `tick ≡ 0` worlds are
exactly the pre-061 frozen-clock worlds. -/
theorem tickSum_eq_zero {tick : Nat → UInt32} (htick : ∀ i, tick i = 0) (e k : Nat) :
    tickSum tick e k = 0 := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih => rw [tickSum_succ, htick, ih]; rfl

theorem tickSum_le_succ (tick : Nat → UInt32) (e k : Nat) :
    tickSum tick e k ≤ tickSum tick e (k + 1) := by
  induction k generalizing e with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [tickSum_succ, tickSum_succ tick e (k + 1)]
    exact Nat.add_le_add_left (ih (e + 1)) _

/-- **Timeliness (finding 061).** The clock plus the worst-case total latency
of the next `fuel` exchanges stays below the deadline — the honest premise
under which the adequacy capstones promise delivery.  It is FALSE for slow
worlds (see `run_ioResumeLoop_deadline_after_referral`), so the deadline test
is genuinely bivalent. -/
def TimelyWorld (clock : UInt32) (tick : Nat → UInt32) (e : Nat)
    (deadline : UInt32) (fuel : Nat) : Prop :=
  clock.toNat + tickSum tick e fuel < deadline.toNat

/-- A timely world has not yet hit the deadline. -/
theorem TimelyWorld.not_deadline {c : UInt32} {tk : Nat → UInt32} {e : Nat}
    {dl : UInt32} {fuel : Nat} (h : TimelyWorld c tk e dl fuel) : ¬ (c ≥ dl) := by
  intro hge
  have hle : dl.toNat ≤ c.toNat := UInt32.le_iff_toNat_le.mp hge
  have := h
  unfold TimelyWorld at this
  omega

/-- Timeliness survives one exchange: the clock advances by `tick e` (UInt32
addition can only lose to the ℕ bound on wraparound, so no side condition). -/
theorem TimelyWorld.step {c : UInt32} {tk : Nat → UInt32} {e : Nat}
    {dl : UInt32} {fuel : Nat} (h : TimelyWorld c tk e dl (fuel + 1)) :
    TimelyWorld (c + tk e) tk (e + 1) dl fuel := by
  unfold TimelyWorld at h ⊢
  rw [tickSum_succ] at h
  have hle : (c + tk e).toNat ≤ c.toNat + (tk e).toNat := by
    rw [UInt32.toNat_add]
    exact Nat.mod_le _ _
  omega

/-- In a zero-latency (`tick ≡ 0`) world, timeliness for ANY fuel is exactly
the old frozen-clock premise `¬ (clock ≥ deadline)`. -/
theorem TimelyWorld.of_tick0 {c : UInt32} {tk : Nat → UInt32} {e : Nat}
    {dl : UInt32} (htick : ∀ i, tk i = 0) (fuel : Nat) (hdl : ¬ (c ≥ dl)) :
    TimelyWorld c tk e dl fuel := by
  unfold TimelyWorld
  rw [tickSum_eq_zero htick]
  have : ¬ (dl.toNat ≤ c.toNat) := fun hle => hdl (UInt32.le_iff_toNat_le.mpr hle)
  omega

open VeriDNS.Proof.Refinement in
/-- **Finding 061 deadline dual (the mutant-killer).** In a world whose first
exchange's latency pushes the clock past the deadline, the loop takes one
referral round and the NEXT iteration returns the deadline error: the deadline
branch of `ioResumeLoop` is REACHED mid-resolution.  Deleting the deadline
check (or answering instead of erroring on deadline) falsifies this theorem. -/
theorem run_ioResumeLoop_deadline_after_referral
    (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel'' revealed : Nat) (w : World)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (hdl : ¬ (w.clock ≥ deadline))
    (hlate : w.clock + w.tick w.exchCtr ≥ deadline)
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
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ (K : Nat) (w' : World),
      Prog.run K (Server.ioResumeLoop (M := Prog) (Sock := Unit)
          sbelt state deadline depth (fuel'' + 2) revealed) w
        = some ((.error "resolveWithIO: query deadline exceeded", st.resources.cache), w')
      ∧ w'.clock = w.clock + w.tick w.exchCtr := by
  obtain ⟨w', htransfer, ho, hto, hids, hclk, hectr, htick, hctr⟩ :=
    run_ioResumeLoop_referral_lift sbelt state deadline depth (fuel'' + 1) revealed w
      entry ipAddr subQuery₀ d bytes resp0 resp₀ resp st
      hdl hbest hegress hbuild hpdeny hpconsume horacle haccept hdecode hsani haccResp htc
      hunfollow hcont hfe
  have hdeadline := run_ioResumeLoop_deadline w' 0 sbelt st deadline depth fuel''
    (Server.revealedAfterContinue state.resources.sname revealed st)
    (by rw [hclk]; exact hlate)
  exact ⟨(0 + 1) + 6, w', htransfer (0 + 1) _ hdeadline, hclk⟩

open VeriDNS.Proof.Refinement in
/-- Capstone-level deadline dual (finding 061): `resolveWithIO`, run in a world
whose first upstream round's latency crosses the query deadline, RETURNS the
deadline error.  `Server.replyForResolution` maps exactly this `.error` to the
client-visible SERVFAIL (`buildErrorResponse query .serverFailure`). -/
theorem run_resolveWithIO_deadline_witness
    (query : VeriDNS.Spec.Format) (sbelt : DnsSList) (cache : DnsCache) (now : UInt32)
    (fuel'' depth : Nat) (budget : UInt32) (w : World)
    (state st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (entry : SlistEntry) (ipAddr : BitVec 32) (subQuery₀ : VeriDNS.Spec.Format)
    (d : VeriDNS.Spec.Exchanged ByteArray) (bytes : ByteArray)
    (resp0 resp₀ resp : VeriDNS.Spec.Format)
    (hpause : Resolver.resolve (NS := SlistEntry) (RR := VeriDNS.Spec.ResourceRecord)
        query sbelt 64 now cache = .ok (.paused state))
    (hdl : ¬ (w.clock ≥ now + budget))
    (hlate : w.clock + w.tick w.exchCtr ≥ now + budget)
    (hbest : state.resources.slist.bestWithAddress = some (entry, ipAddr))
    (hegress : Server.blockedEgress ipAddr = false)
    (hbuild : Resolver.buildSubQuery state (Server.seedRevealed state) = some subQuery₀)
    (hpdeny : (Resolver.probeRoundB state.resources.sname (Server.seedRevealed state)
        && Server.strictDenialB resp) = false)
    (hpconsume : (Resolver.probeRoundB state.resources.sname (Server.seedRevealed state)
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
    (hfe : (resp.header.rcode == VeriDNS.Spec.Rcode.formatError) = false) :
    ∃ (K : Nat) (w' : World),
      Prog.run K (Server.resolveWithIO (M := Prog) (Sock := Unit)
          query sbelt cache now (fuel'' + 2) depth budget) w
        = some ((.error "resolveWithIO: query deadline exceeded", st.resources.cache), w')
      ∧ w'.clock = w.clock + w.tick w.exchCtr := by
  obtain ⟨K, w', hrun, hclk⟩ := run_ioResumeLoop_deadline_after_referral sbelt state
    (now + budget) depth fuel'' (Server.seedRevealed state) w entry ipAddr subQuery₀
    d bytes resp0 resp₀ resp st hdl hlate hbest hegress hbuild hpdeny hpconsume horacle
    haccept hdecode hsani haccResp htc hunfollow hcont hfe
  refine ⟨K, w', ?_, hclk⟩
  unfold Server.resolveWithIO
  rw [hpause]
  exact hrun

end VeriDNS.Proof.FreeIO
