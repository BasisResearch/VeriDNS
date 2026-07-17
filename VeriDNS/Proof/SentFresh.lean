import VeriDNS.Proof.SentMinimised

/-!
# TXID / case-seed freshness pin (finding 002)

`ioResumeLoop` draws two fresh secrets per upstream round
(`rid ← randomId; cid ← randomId`) and stamps them into the sub-query via
`Server.withSecrets`.  Until now this was pinned only by a runtime entropy
test (`Test/IdEntropy.lean`): a mutant that ignored the draws and sent a
constant TXID still built green, because `SentShape` quantifies the secrets
EXISTENTIALLY.

`SentFresh` is a program-tree predicate over `Prog` that THREADS the last
two `randomId` draws through the tree and requires every
`exchange`/`tcpExchange` payload to be predicated on those *drawn* values:
there is no constructor for an exchange whose payload is not a function of
the two immediately-preceding draws.  `ioResumeLoop_sent_fresh`
instantiates it with `FreshSecrets`: the payload IS
`Message.encode (Server.withSecrets sq rid cid)` for THE drawn `rid`/`cid`.
A constant-ID (or constant-case-seed) mutation of the loop makes this
theorem fail to compile, because `withSecrets sq k cid` with a constant `k`
differs from `withSecrets sq rid cid` at `header.id` for every `rid ≠ k`
(`withSecrets_id` below), and the theorem quantifies over all draw results.
-/

namespace VeriDNS.Proof.SentFresh

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO

/-- `SentFresh P r c p`: every `exchange`/`tcpExchange` reachable in the
program tree `p` satisfies `P rid cid payload addr` where `rid`/`cid` are the
SECOND-TO-LAST and LAST `randomId` results drawn on the path to that node
(threaded through the `r`/`c` indices; a draw shifts `(r, c) ↦ (c, drawn)`).
An exchange with fewer than two preceding draws is unsatisfiable (no
constructor). -/
inductive SentFresh (P : UInt16 → UInt16 → ByteArray → ByteArray → Prop) :
    {α : Type} → Option UInt16 → Option UInt16 → Prog α → Prop where
  | pure {α : Type} {r c : Option UInt16} (a : α) : SentFresh P r c (Prog.pure a)
  | now {α : Type} {r c : Option UInt16} {k : UInt32 → Prog α}
      (hk : ∀ t, SentFresh P r c (k t)) : SentFresh P r c (Prog.step .now k)
  | log {α : Type} {r c : Option UInt16} {s : String} {k : Unit → Prog α}
      (hk : ∀ u, SentFresh P r c (k u)) : SentFresh P r c (Prog.step (.log s) k)
  | randomId {α : Type} {r c : Option UInt16} {k : UInt16 → Prog α}
      (hk : ∀ i, SentFresh P c (some i) (k i)) : SentFresh P r c (Prog.step .randomId k)
  | exchange {α : Type} {rid cid : UInt16} {q addr : ByteArray}
      {k : Option (VeriDNS.Spec.Exchanged ByteArray) → Prog α}
      (hq : P rid cid q addr)
      (hk : ∀ o, SentFresh P (some rid) (some cid) (k o)) :
      SentFresh P (some rid) (some cid) (Prog.step (.exchange q addr) k)
  | tcpExchange {α : Type} {rid cid : UInt16} {q addr : ByteArray}
      {k : Option ByteArray → Prog α}
      (hq : P rid cid q addr)
      (hk : ∀ o, SentFresh P (some rid) (some cid) (k o)) :
      SentFresh P (some rid) (some cid) (Prog.step (.tcpExchange q addr) k)

/-- Bind with a continuation that is fresh at EVERY draw state (the common
case: the continuation re-draws before any exchange of its own). -/
theorem SentFresh.bind_any {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {α β : Type} {r c : Option UInt16} {p : Prog α} {f : α → Prog β}
    (hp : SentFresh P r c p)
    (hf : ∀ a (r' c' : Option UInt16), SentFresh P r' c' (f a)) :
    SentFresh P r c (p.bind f) := by
  induction hp with
  | pure a => exact hf a _ _
  | now _ ih => exact .now ih
  | log _ ih => exact .log ih
  | randomId _ ih => exact .randomId ih
  | exchange hq _ ih => exact .exchange hq ih
  | tcpExchange hq _ ih => exact .tcpExchange hq ih

private theorem sentFresh_pure {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {α : Type} {r c : Option UInt16} (a : α) :
    SentFresh P r c (pure a : Prog α) := .pure a

private theorem sentFresh_bind {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {α β : Type} {r c : Option UInt16} {p : Prog α} {f : α → Prog β}
    (hp : SentFresh P r c p)
    (hf : ∀ a (r' c' : Option UInt16), SentFresh P r' c' (f a)) :
    SentFresh P r c (p >>= f) := hp.bind_any hf

private theorem sentFresh_now {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {β : Type} {r c : Option UInt16} {k : UInt32 → Prog β}
    (hk : ∀ t, SentFresh P r c (k t)) :
    SentFresh P r c ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) := by
  show SentFresh P r c (Prog.step .now _)
  exact .now fun t => hk t

private theorem sentFresh_log {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {β : Type} {r c : Option UInt16} {s : String} {k : Unit → Prog β}
    (hk : ∀ u, SentFresh P r c (k u)) :
    SentFresh P r c ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) := by
  show SentFresh P r c (Prog.step (.log s) _)
  exact .log fun u => hk u

private theorem sentFresh_randomId {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {β : Type} {r c : Option UInt16} {k : UInt16 → Prog β}
    (hk : ∀ i, SentFresh P c (some i) (k i)) :
    SentFresh P r c
      ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) := by
  show SentFresh P r c (Prog.step .randomId _)
  exact .randomId fun i => hk i

private theorem sentFresh_forwardQuery {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {β : Type} {rid cid : UInt16} {query : Format} {addr : ByteArray}
    {k : Option Format → Prog β}
    (hq : P rid cid (Message.encode query) addr)
    (hk : ∀ o, SentFresh P (some rid) (some cid) (k o)) :
    SentFresh P (some rid) (some cid)
      ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) := by
  show SentFresh P (some rid) (some cid) (Prog.step (.exchange (Message.encode query) addr) _)
  refine .exchange hq fun r => ?_
  cases r with
  | none => exact hk none
  | some d =>
    show SentFresh P (some rid) (some cid) ((match Server.acceptExchanged addr d with
      | none => Prog.pure none
      | some bytes =>
        match Message.decode bytes with
        | .ok resp => Prog.pure (Server.sanitizeTtlsCap resp)
        | .error _ => Prog.pure none).bind k)
    split
    · exact hk none
    · split
      · exact hk _
      · exact hk none

private theorem sentFresh_tcpForward {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop}
    {β : Type} {rid cid : UInt16} {query : Format} {addr : ByteArray}
    {k : Option Format → Prog β}
    (hq : P rid cid (Message.encode query) addr)
    (hk : ∀ o, SentFresh P (some rid) (some cid) (k o)) :
    SentFresh P (some rid) (some cid)
      ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) := by
  show SentFresh P (some rid) (some cid)
    (Prog.step (.tcpExchange (Message.encode query) addr) _)
  refine .tcpExchange hq fun r => ?_
  cases r with
  | none => exact hk none
  | some d =>
    show SentFresh P (some rid) (some cid) ((match Message.decode d with
      | .ok resp => Prog.pure (Server.sanitizeTtlsCap resp)
      | .error _ => Prog.pure none).bind k)
    split
    · exact hk _
    · exact hk none

private theorem sentFresh_gluelessUpdatedSlist
    {P : UInt16 → UInt16 → ByteArray → ByteArray → Prop} {r c : Option UInt16}
    (slist : DnsSList) (nsName : ByteArray) (res : Except String Format) :
    SentFresh P r c (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName res) := by
  unfold Server.gluelessUpdatedSlist
  split
  · split
    · exact sentFresh_log fun _ => sentFresh_pure _
    · exact sentFresh_log fun _ => sentFresh_pure _
  · split
    · exact sentFresh_log fun _ => sentFresh_pure _
    · exact sentFresh_pure _

/-- The payload of an upstream exchange is the `buildSubQuery` image stamped
with THE two secrets drawn immediately before the send — `rid`/`cid` here are
bound by `SentFresh`'s threading to the actual `randomId` results, not
existentially chosen. -/
def FreshSecrets (rid cid : UInt16) (bytes : ByteArray) (_addr : ByteArray) : Prop :=
  ∃ (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) (revealed : Nat)
    (sq : Format),
    Resolver.buildSubQuery st revealed = some sq ∧
    bytes = Message.encode (Server.withSecrets sq rid cid)

private theorem ioResumeLoop_sent_fresh_aux :
    ∀ (n depth fuel : Nat), depth + fuel ≤ n →
    ∀ (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
      (deadline : UInt32) (revealed : Nat) (r c : Option UInt16),
      SentFresh FreshSecrets r c (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth fuel revealed) := by
  intro n
  induction n with
  | zero =>
    intro depth fuel hle sbelt state deadline revealed r c
    have hf : fuel = 0 := by omega
    subst hf
    rw [Server.ioResumeLoop]
    exact sentFresh_pure _
  | succ n ih =>
    intro depth fuel hle sbelt state deadline revealed r c
    match fuel with
    | 0 =>
      rw [Server.ioResumeLoop]
      exact sentFresh_pure _
    | fuel' + 1 =>
      rw [Server.ioResumeLoop.eq_def]
      dsimp only [letFun]
      refine sentFresh_now fun t => ?_
      split
      · exact sentFresh_pure _
      · refine sentFresh_bind (sentFresh_pure PUnit.unit) fun _ r' c' => ?_
        split
        ·
          split
          ·
            split
            ·
              rename_i nsName hns depth'
              refine sentFresh_log fun _ => ?_
              split
              ·
                refine sentFresh_bind (sentFresh_gluelessUpdatedSlist _ _ _)
                  fun slist' r'' c'' => ?_
                exact ih depth' fuel' (by omega) _ _ _ _ _ _
              ·
                refine sentFresh_bind (sentFresh_gluelessUpdatedSlist _ _ _)
                  fun slist' r'' c'' => ?_
                exact ih depth' fuel' (by omega) _ _ _ _ _ _
              ·
                refine sentFresh_bind (ih depth' fuel' (by omega) _ _ _ _ _ _)
                  fun sub r'' c'' => ?_
                obtain ⟨subResult, subCache⟩ := sub
                refine sentFresh_bind (sentFresh_gluelessUpdatedSlist _ _ _)
                  fun slist' r₃ c₃ => ?_
                split
                ·
                  split
                  ·
                    split
                    · exact sentFresh_pure _
                    · exact ih depth' fuel' (by omega) _ _ _ _ _ _
                  · exact ih depth' fuel' (by omega) _ _ _ _ _ _
                · exact ih depth' fuel' (by omega) _ _ _ _ _ _
            ·
              exact sentFresh_pure _
          ·
            exact sentFresh_pure _
        ·
          rename_i entry ipAddr
          split
          ·
            rename_i subQuery₀ hbuild
            refine sentFresh_log fun _ => ?_
            refine sentFresh_randomId fun rid => ?_
            refine sentFresh_randomId fun cid => ?_
            split
            ·
              refine sentFresh_log fun _ => ?_
              exact ih depth fuel' (by omega) _ _ _ _ _ _
            ·
              refine sentFresh_forwardQuery
                ⟨state, revealed, subQuery₀, hbuild, rfl⟩ fun o => ?_
              split
              ·
                split
                ·
                  refine sentFresh_log fun _ => ?_
                  refine sentFresh_bind ?_ fun o r'' c'' => ?_
                  ·
                    split
                    ·
                      refine sentFresh_log fun _ => ?_
                      refine sentFresh_tcpForward
                        ⟨state, revealed, subQuery₀, hbuild, rfl⟩ fun to => ?_
                      split
                      · exact sentFresh_pure _
                      · split
                        · exact sentFresh_pure _
                        · exact sentFresh_pure _
                    ·
                      exact sentFresh_pure _
                  ·
                    split
                    ·
                      split
                      ·
                        refine sentFresh_log fun _ => ?_
                        exact ih depth fuel' (by omega) _ _ _ _ _ _
                      · split
                        · -- 055 (RFC 6891 §6.2.2): FORMERR arm — EDNS-free retry recursion
                          refine sentFresh_log fun _ => ?_
                          exact ih depth fuel' (by omega) _ _ _ _ _ _
                        · split
                          · -- 051/064: the probe-NXDOMAIN arm now recurses (full-qname fallback)
                            refine sentFresh_log fun _ => ?_
                            exact ih depth fuel' (by omega) _ _ _ _ _ _
                          · split
                            ·
                              refine sentFresh_log fun _ => ?_
                              exact ih depth fuel' (by omega) _ _ _ _ _ _
                            ·
                              split
                              · exact sentFresh_pure _
                              · exact ih depth fuel' (by omega) _ _ _ _ _ _
                    ·
                      refine sentFresh_log fun _ => ?_
                      exact ih depth fuel' (by omega) _ _ _ _ _ _
                ·
                  refine sentFresh_log fun _ => ?_
                  exact ih depth fuel' (by omega) _ _ _ _ _ _
              ·
                exact ih depth fuel' (by omega) _ _ _ _ _ _
          ·
            exact sentFresh_pure _

/-- Flagship (finding 002): the TXID and case seed on every upstream wire are
the two `randomId` draws made immediately before the send.  A constant-ID or
draw-ignoring mutant of `ioResumeLoop` breaks this theorem. -/
theorem ioResumeLoop_sent_fresh (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel revealed : Nat) (r c : Option UInt16) :
    SentFresh FreshSecrets r c (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state deadline depth fuel revealed) :=
  ioResumeLoop_sent_fresh_aux (depth + fuel) depth fuel (Nat.le_refl _)
    sbelt state deadline revealed r c

theorem resolveWithIO_sent_fresh (query : Format) (sbelt : DnsSList)
    (cache : DnsCache) (now : UInt32) (fuel depth : Nat) (budget : UInt32)
    (r c : Option UInt16) :
    SentFresh FreshSecrets r c (Server.resolveWithIO (M := Prog) (Sock := Unit)
      query sbelt cache now fuel depth budget) := by
  unfold Server.resolveWithIO
  split
  · exact sentFresh_pure _
  · exact ioResumeLoop_sent_fresh _ _ _ _ _ _ _ _
  · exact sentFresh_pure _

/-- The stamped sub-query carries the drawn TXID in its header: `withSecrets`
sets `header.id := rid` (and only the case seed touches the question). With
`ioResumeLoop_sent_fresh` this ties the WIRE header id to the draw. -/
theorem withSecrets_id (sq : Format) (rid cid : UInt16) :
    (Server.withSecrets sq rid cid).header.id = VeriDNS.Impl.bv16OfUInt16 rid := rfl

/-- The stamped sub-query's question is the original question with the case
of every qname randomized by THE drawn case seed. -/
theorem withSecrets_question (sq : Format) (rid cid : UInt16) :
    (Server.withSecrets sq rid cid).question
      = sq.question.map fun qu =>
          { qu with qname := DomainName.randomizeCase cid qu.qname } := rfl

end VeriDNS.Proof.SentFresh
