import VeriDNS.Proof.FreeIO
import VeriDNS.Proof.IoResumeSound
import VeriDNS.Proof.NameTreeComplete
import VeriDNS.Proof.Primitives




namespace VeriDNS.Proof.SentMinimised

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO
open VeriDNS.Proof.DeliveredWire (CanonicalName)


inductive AllSent (P : ByteArray → ByteArray → Prop) : {α : Type} → Prog α → Prop where
  | pure {α : Type} (a : α) : AllSent P (Prog.pure a)
  | step {α : Type} {c : DnsCmd} {k : DnsCmd.Res c → Prog α}
      (hc : ∀ q addr, c = .exchange q addr → P q addr)
      (htc : ∀ q addr, c = .tcpExchange q addr → P q addr)
      (hns : ∀ d addr, c ≠ .sendTo d addr)
      (hnts : ∀ d, c ≠ .tcpSend d)
      (hk : ∀ r, AllSent P (k r)) : AllSent P (Prog.step c k)

theorem AllSent.bind_prog {P : ByteArray → ByteArray → Prop} {α β : Type}
    {p : Prog α} {f : α → Prog β}
    (hp : AllSent P p) (hf : ∀ a, AllSent P (f a)) : AllSent P (p.bind f) := by
  induction hp with
  | pure a => exact hf a
  | step hc htc hns hnts _ ih => exact .step hc htc hns hnts (fun r => ih r)

theorem AllSent.mono {P Q : ByteArray → ByteArray → Prop} {α : Type} {p : Prog α}
    (h : AllSent P p) (hpq : ∀ q a, P q a → Q q a) : AllSent Q p := by
  induction h with
  | pure a => exact .pure a
  | step hc htc hns hnts _ ih =>
    exact .step (fun q a hqa => hpq _ _ (hc q a hqa)) (fun q a hqa => hpq _ _ (htc q a hqa))
      hns hnts ih

/-- With client-reply sends now visible `DnsCmd` steps (finding 054), an
`AllSent`-covered program tree contains no `sendTo`/`tcpSend` node at all, so
running it frames the `World.sent`/`World.tcpSent` delivery logs exactly. -/
theorem AllSent.run_sends_frame {P : ByteArray → ByteArray → Prop} {α : Type} :
    ∀ {n : Nat} {p : Prog α} {w : World} {x : α} {w' : World},
      AllSent P p → Prog.run n p w = some (x, w') →
      w'.sent = w.sent ∧ w'.tcpSent = w.tcpSent := by
  intro n
  induction n with
  | zero =>
    intro p w x w' hp h
    cases hp with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact ⟨rfl, rfl⟩
    | step hc htc hns hnts hk => exact nomatch h
  | succ n ih =>
    intro p w x w' hp h
    cases hp with
    | pure a =>
      simp only [run_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact ⟨rfl, rfl⟩
    | @step c k hc htc hns hnts hk =>
      rw [run_step] at h
      obtain ⟨h1, h2⟩ := ih (hk _) h
      cases c with
      | sendTo d a => exact absurd rfl (hns d a)
      | tcpSend d => exact absurd rfl (hnts d)
      | now => exact ⟨h1, h2⟩
      | randomId => exact ⟨h1, h2⟩
      | exchange q a => exact ⟨h1, h2⟩
      | tcpExchange q a => exact ⟨h1, h2⟩
      | log s => exact ⟨h1, h2⟩

private theorem allSent_pure {P : ByteArray → ByteArray → Prop} {α : Type} (a : α) :
    AllSent P (pure a : Prog α) := .pure a

private theorem allSent_bind {P : ByteArray → ByteArray → Prop} {α β : Type}
    {p : Prog α} {f : α → Prog β}
    (hp : AllSent P p) (hf : ∀ a, AllSent P (f a)) : AllSent P (p >>= f) :=
  hp.bind_prog hf

private theorem allSent_now {P : ByteArray → ByteArray → Prop} {β : Type}
    {k : UInt32 → Prog β} (hk : ∀ t, AllSent P (k t)) :
    AllSent P ((UdpSocket.now (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) := by
  show AllSent P (Prog.step .now _)
  exact .step (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h) (fun r => hk r)

private theorem allSent_log {P : ByteArray → ByteArray → Prop} {β : Type} {s : String}
    {k : Unit → Prog β} (hk : ∀ u, AllSent P (k u)) :
    AllSent P ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) := by
  show AllSent P (Prog.step (.log s) _)
  exact .step (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h) (fun r => hk r)

private theorem allSent_randomId {P : ByteArray → ByteArray → Prop} {β : Type}
    {k : UInt16 → Prog β} (hk : ∀ i, AllSent P (k i)) :
    AllSent P ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) := by
  show AllSent P (Prog.step .randomId _)
  exact .step (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h) (fun r => hk r)

private theorem allSent_forwardQuery {P : ByteArray → ByteArray → Prop} {β : Type}
    {query : Format} {addr : ByteArray} {k : Option Format → Prog β}
    (hq : P (Message.encode query) addr)
    (hk : ∀ o, AllSent P (k o)) :
    AllSent P ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) := by
  show AllSent P (Prog.step (.exchange (Message.encode query) addr) _)
  refine .step (fun q' a' h => by cases h; exact hq) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h) (fun r => ?_)
  cases r with
  | none => exact hk none
  | some d =>
    show AllSent P ((match Server.acceptExchanged addr d with
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

private theorem allSent_tcpForward {P : ByteArray → ByteArray → Prop} {β : Type}
    {query : Format} {addr : ByteArray} {k : Option Format → Prog β}
    (hq : P (Message.encode query) addr)
    (hk : ∀ o, AllSent P (k o)) :
    AllSent P ((Server.tcpForward (M := Prog) (Sock := Unit) query addr) >>= k) := by
  show AllSent P (Prog.step (.tcpExchange (Message.encode query) addr) _)
  refine .step (fun _ _ h => nomatch h) (fun q' a' h => by cases h; exact hq) (fun _ _ h => nomatch h) (fun _ h => nomatch h) (fun r => ?_)
  cases r with
  | none => exact hk none
  | some d =>
    show AllSent P ((match Message.decode d with
      | .ok resp => Prog.pure (Server.sanitizeTtlsCap resp)
      | .error _ => Prog.pure none).bind k)
    split
    · exact hk _
    · exact hk none

private theorem allSent_gluelessUpdatedSlist {P : ByteArray → ByteArray → Prop}
    (slist : DnsSList) (nsName : ByteArray) (res : Except String Format) :
    AllSent P (Server.gluelessUpdatedSlist (M := Prog) (Sock := Unit) slist nsName res) := by
  unfold Server.gluelessUpdatedSlist
  split
  · split
    · exact allSent_log fun _ => allSent_pure _
    · exact allSent_log fun _ => allSent_pure _
  · split
    · exact allSent_log fun _ => allSent_pure _
    · exact allSent_pure _


def SentShape (bytes : ByteArray) (_addr : ByteArray) : Prop :=
  ∃ (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) (revealed : Nat)
    (sq : Format) (rid cid : UInt16),
    Resolver.buildSubQuery st revealed = some sq ∧
    bytes = Message.encode (Server.withSecrets sq rid cid)


/-! ### Egress restriction spec (findings 060b / 062)

`AclEntry.matches` is exactly prefix equality of the top `plen` bits
(equivalently: division by `2^(32-plen)` agrees; equivalently, for an
aligned net, membership in the CIDR interval).  This pins the mask
arithmetic (060b — verified correct, the upper half of every blocked
range DOES match), and `EgressOk`/`ioResumeLoop_sent_egress` below pin
that every wire that leaves the resolver was gated by `blockedEgress`
(062). -/

theorem aclEntry_matches_iff (e : Server.AclEntry) (ip : BitVec 32) (h : e.plen ≤ 32) :
    e.matches ip = true ↔
      ip.toNat / 2 ^ (32 - e.plen) = e.net.toNat / 2 ^ (32 - e.plen) := by
  unfold Server.AclEntry.matches
  simp only [Nat.min_eq_left h, beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-- Interval characterization: for an aligned net (all the entries of
`doNotQueryNets` are aligned), `matches` is exactly membership in
`[net, net + 2^(32-plen))` — so in particular the UPPER half of every
blocked range is blocked (060b). -/
theorem aclEntry_matches_interval (e : Server.AclEntry) (ip : BitVec 32) (h : e.plen ≤ 32)
    (halign : e.net.toNat % 2 ^ (32 - e.plen) = 0) :
    e.matches ip = true ↔
      e.net.toNat ≤ ip.toNat ∧ ip.toNat < e.net.toNat + 2 ^ (32 - e.plen) := by
  rw [aclEntry_matches_iff e ip h]
  have hk : 0 < 2 ^ (32 - e.plen) := Nat.two_pow_pos _
  have h1 := Nat.div_add_mod ip.toNat (2 ^ (32 - e.plen))
  have h2 := Nat.div_add_mod e.net.toNat (2 ^ (32 - e.plen))
  have h3 := Nat.mod_lt ip.toNat hk
  constructor
  · intro heq; rw [heq] at h1; omega
  · rintro ⟨hlo, hhi⟩
    have hle : e.net.toNat / 2 ^ (32 - e.plen) ≤ ip.toNat / 2 ^ (32 - e.plen) :=
      Nat.div_le_div_right hlo
    have hlt : ip.toNat / 2 ^ (32 - e.plen) < e.net.toNat / 2 ^ (32 - e.plen) + 1 :=
      (Nat.div_lt_iff_lt_mul hk).mpr (by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (e.net.toNat / 2 ^ (32 - e.plen))]
        omega)
    omega

private theorem getLsbD_255 (i : Nat) : (255#32).getLsbD i = decide (i < 8) := by
  show Nat.testBit 255 i = decide (i < 8)
  have h : (255 : Nat) = 2 ^ 8 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

private theorem and255_setWidth (b : BitVec 8) :
    BitVec.setWidth 32 b &&& 255#32 = BitVec.setWidth 32 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, getLsbD_255]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, hi, BitVec.getLsbD_of_ge b i (by omega)]

private theorem ofNat_shift_toBitVec (x : BitVec 32) (k : Nat) :
    (UInt8.ofNat (x.toNat >>> k)).toBitVec = (x >>> k).setWidth 8 := by
  simp [UInt8.ofNat, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]

/-- The egress guard's `BitVec 32` and the wire sockaddr agree: reading the
four address bytes of `ipv4ToAddr ip` back (the same conversion the ingress
ACL uses) recovers `ip`. -/
theorem clientIp_ipv4ToAddr (ip : BitVec 32) (port : UInt16) :
    Server.clientIp (Server.ipv4ToAddr ip port) = ip := by
  unfold Server.clientIp Server.ipv4ToAddr
  simp [Array.getD]
  rw [show (UInt8.ofNat ip.toNat).toBitVec = ip.setWidth 8 by
        simpa using ofNat_shift_toBitVec ip 0,
      ofNat_shift_toBitVec, ofNat_shift_toBitVec, ofNat_shift_toBitVec,
      and255_setWidth, and255_setWidth, and255_setWidth]
  have h := VeriDNS.Proof.Primitives.reassemble32 ip
  simpa [UInt8.toBitVec_ofBitVec] using h

/-- Every datagram the resolver sends upstream leaves for an address that
passed the `blockedEgress` do-not-query gate (finding 062).  Stated on the
wire address: the destination is the sockaddr encoding of an unblocked IP. -/
def EgressOk (_bytes : ByteArray) (addr : ByteArray) : Prop :=
  ∃ ip : BitVec 32, addr = Server.ipv4ToAddr ip ∧ Server.blockedEgress ip = false

/-- Consumer form of `EgressOk`: the IP read back from the wire destination
bytes is not in a blocked range. -/
theorem EgressOk.clientIp_unblocked {bytes addr : ByteArray} (h : EgressOk bytes addr) :
    Server.blockedEgress (Server.clientIp addr) = false := by
  obtain ⟨ip, rfl, hb⟩ := h
  rwa [clientIp_ipv4ToAddr]

def SentShapeEgress (bytes : ByteArray) (addr : ByteArray) : Prop :=
  SentShape bytes addr ∧ EgressOk bytes addr


private theorem ioResumeLoop_sent_shape_aux :
    ∀ (n depth fuel : Nat), depth + fuel ≤ n →
    ∀ (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
      (deadline : UInt32) (revealed : Nat),
      AllSent SentShapeEgress (Server.ioResumeLoop (M := Prog) (Sock := Unit)
        sbelt state deadline depth fuel revealed) := by
  intro n
  induction n with
  | zero =>
    intro depth fuel hle sbelt state deadline revealed
    have hf : fuel = 0 := by omega
    subst hf
    rw [Server.ioResumeLoop]
    exact allSent_pure _
  | succ n ih =>
    intro depth fuel hle sbelt state deadline revealed
    match fuel with
    | 0 =>
      rw [Server.ioResumeLoop]
      exact allSent_pure _
    | fuel' + 1 =>
      rw [Server.ioResumeLoop.eq_def]
      dsimp only [letFun]
      refine allSent_now fun t => ?_
      split
      · exact allSent_pure _
      · refine allSent_bind (allSent_pure PUnit.unit) fun _ => ?_
        split
        ·
          split
          ·
            split
            ·
              rename_i nsName hns depth'
              refine allSent_log fun _ => ?_
              split
              ·
                refine allSent_bind (allSent_gluelessUpdatedSlist _ _ _) fun slist' => ?_
                exact ih depth' fuel' (by omega) _ _ _ _
              ·
                refine allSent_bind (allSent_gluelessUpdatedSlist _ _ _) fun slist' => ?_
                exact ih depth' fuel' (by omega) _ _ _ _
              ·
                refine allSent_bind (ih depth' fuel' (by omega) _ _ _ _) fun sub => ?_
                obtain ⟨subResult, subCache⟩ := sub
                refine allSent_bind (allSent_gluelessUpdatedSlist _ _ _) fun slist' => ?_
                split
                ·
                  split
                  ·
                    split
                    · exact allSent_pure _
                    · exact ih depth' fuel' (by omega) _ _ _ _
                  · exact ih depth' fuel' (by omega) _ _ _ _
                · exact ih depth' fuel' (by omega) _ _ _ _
            ·
              exact allSent_pure _
          ·
            exact allSent_pure _
        ·
          rename_i entry ipAddr
          split
          ·
            rename_i subQuery₀ hbuild
            refine allSent_log fun _ => ?_
            refine allSent_randomId fun rid => ?_
            refine allSent_randomId fun cid => ?_
            split
            ·
              refine allSent_log fun _ => ?_
              exact ih depth fuel' (by omega) _ _ _ _
            ·
              rename_i hegress
              refine allSent_forwardQuery
                ⟨⟨state, revealed, subQuery₀, rid, cid, hbuild, rfl⟩,
                  _, rfl, Bool.eq_false_iff.mpr fun hcontra => hegress hcontra⟩ fun o => ?_
              split
              ·
                split
                ·
                  refine allSent_log fun _ => ?_
                  refine allSent_bind ?_ fun o => ?_
                  ·
                    split
                    ·
                      refine allSent_log fun _ => ?_
                      refine allSent_tcpForward
                        ⟨⟨state, revealed, subQuery₀, rid, cid, hbuild, rfl⟩,
                          _, rfl, Bool.eq_false_iff.mpr fun hcontra => hegress hcontra⟩
                        fun to => ?_
                      split
                      · exact allSent_pure _
                      · split
                        · exact allSent_pure _
                        · exact allSent_pure _
                    ·
                      exact allSent_pure _
                  ·
                    split
                    ·
                      split
                      ·
                        refine allSent_log fun _ => ?_
                        exact ih depth fuel' (by omega) _ _ _ _
                      · split
                        · -- 055 (RFC 6891 §6.2.2): FORMERR arm — EDNS-free retry recursion
                          refine allSent_log fun _ => ?_
                          exact ih depth fuel' (by omega) _ _ _ _
                        · split
                          · -- 051/064: the probe-NXDOMAIN arm now recurses (full-qname fallback)
                            refine allSent_log fun _ => ?_
                            exact ih depth fuel' (by omega) _ _ _ _
                          · split
                            ·
                              refine allSent_log fun _ => ?_
                              exact ih depth fuel' (by omega) _ _ _ _
                            ·
                              split
                              · exact allSent_pure _
                              · exact ih depth fuel' (by omega) _ _ _ _
                    ·
                      refine allSent_log fun _ => ?_
                      exact ih depth fuel' (by omega) _ _ _ _
                ·
                  refine allSent_log fun _ => ?_
                  exact ih depth fuel' (by omega) _ _ _ _
              ·
                exact ih depth fuel' (by omega) _ _ _ _
          ·
            exact allSent_pure _

/-- Flagship (finding 062): every `exchange`/`tcpExchange` node reachable in
the resolve loop's program tree carries BOTH the `buildSubQuery` payload shape
AND an egress-gated destination — deleting or bypassing the `blockedEgress`
guard in `ioResumeLoop` makes this theorem fail to compile. -/
theorem ioResumeLoop_sent_egress (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel revealed : Nat) :
    AllSent SentShapeEgress (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state deadline depth fuel revealed) :=
  ioResumeLoop_sent_shape_aux (depth + fuel) depth fuel (Nat.le_refl _)
    sbelt state deadline revealed

theorem ioResumeLoop_sent_shape (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel revealed : Nat) :
    AllSent SentShape (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state deadline depth fuel revealed) :=
  (ioResumeLoop_sent_egress sbelt state deadline depth fuel revealed).mono
    fun _ _ h => h.1


private theorem valid_le63 {ls : Array ByteArray}
    (hv : VeriDNS.Proof.DomainName.ValidLabels ls) : ∀ x ∈ ls, x.size ≤ 63 := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  exact (hv i hi).2

private theorem canonicalName_fold {m : ByteArray} (h : CanonicalName m) :
    CanonicalName (DomainName.foldNameCase m) := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  have hvf : VeriDNS.Proof.DomainName.ValidLabels (ls.map DomainName.foldNameCase) := by
    intro i hi
    have hi' : i < ls.size := by simpa using hi
    simp only [Array.getElem_map]
    rw [VeriDNS.Proof.NameTree.foldNameCase_size]
    exact hv i hi'
  refine ⟨ls.map DomainName.foldNameCase, hvf, ?_, ?_⟩
  · rw [← VeriDNS.Proof.Refinement.foldNameCase_labelsToWireFormat ls (valid_le63 hv),
      VeriDNS.Proof.NameTree.foldNameCase_size]
    exact hle
  · exact VeriDNS.Proof.Refinement.foldNameCase_labelsToWireFormat ls (valid_le63 hv)

private theorem labelCount_fold {m : ByteArray} (h : CanonicalName m) :
    DomainName.labelCount (DomainName.foldNameCase m) = DomainName.labelCount m := by
  obtain ⟨ls, hv, hle, rfl⟩ := h
  have hvf : VeriDNS.Proof.DomainName.ValidLabels (ls.map DomainName.foldNameCase) := by
    intro i hi
    have hi' : i < ls.size := by simpa using hi
    simp only [Array.getElem_map]
    rw [VeriDNS.Proof.NameTree.foldNameCase_size]
    exact hv i hi'
  rw [VeriDNS.Proof.Refinement.foldNameCase_labelsToWireFormat ls (valid_le63 hv),
    VeriDNS.Proof.QnameMin.labelCount_wire _ hvf,
    VeriDNS.Proof.QnameMin.labelCount_wire ls hv, Array.size_map]

theorem isAncestorB_congr_left (b1 b2 owner : ByteArray)
    (h : DomainName.nameEqCI b1 b2 = true) :
    Resolver.isAncestorB b1 owner = Resolver.isAncestorB b2 owner := by
  have hfold : DomainName.foldNameCase b1 = DomainName.foldNameCase b2 :=
    VeriDNS.Proof.NameTree.nameEqCI_iff.mp h
  unfold Resolver.isAncestorB
  cases ho : DomainName.wireFormatToLabels owner with
  | error _ =>
    cases h1 : DomainName.wireFormatToLabels b1 <;>
      cases h2 : DomainName.wireFormatToLabels b2 <;> simp
  | ok oL =>
    cases h1 : DomainName.wireFormatToLabels b1 with
    | error e1 =>
      obtain ⟨e1', he1'⟩ := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_error b1 e1 h1
      cases h2 : DomainName.wireFormatToLabels b2 with
      | error _ => simp
      | ok L2 =>
        have e2' := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok b2 L2 h2
        rw [← hfold, he1'] at e2'; exact absurd e2' (by simp)
    | ok L1 =>
      cases h2 : DomainName.wireFormatToLabels b2 with
      | error e2 =>
        obtain ⟨e2', he2'⟩ := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_error b2 e2 h2
        have e1' := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok b1 L1 h1
        rw [hfold, he2'] at e1'; exact absurd e1' (by simp)
      | ok L2 =>
        have hLL : L1.map DomainName.foldNameCase = L2.map DomainName.foldNameCase := by
          have e1' := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok b1 L1 h1
          have e2' := VeriDNS.Proof.NameTree.wireFormatToLabels_fold_ok b2 L2 h2
          rw [hfold, e2'] at e1'; injection e1' with e1'; exact e1'.symm
        have hLLt : L1.toList.map DomainName.foldNameCase
            = L2.toList.map DomainName.foldNameCase := by
          have := congrArg Array.toList hLL; simpa using this
        simp only [hLLt, List.length_map, Array.length_toList]


theorem sent_question_minimised
    {st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord}
    {revealed : Nat} {sq : Format}
    (hbuild : Resolver.buildSubQuery st revealed = some sq)
    (rid cid : UInt16)
    (hcanon : CanonicalName st.resources.sname) :
    ∃ (origQ : Format) (qu : Question) (q : Question),
      st.lastQuery = some origQ ∧ origQ.question[0]? = some qu ∧
      (Server.withSecrets sq rid cid).question = #[q] ∧
      Resolver.isAncestorB q.qname st.resources.sname = true ∧
      (Resolver.probeRoundB st.resources.sname revealed = true →
        q.qtype = 1 ∧ revealed < DomainName.labelCount st.resources.sname ∧
        DomainName.labelCount (DomainName.foldNameCase q.qname) = revealed) ∧
      (Resolver.probeRoundB st.resources.sname revealed = false →
        DomainName.nameEqCI q.qname st.resources.sname = true ∧ q.qtype = qu.qtype) := by
  obtain ⟨origQ, qu, hlq, hqu, hquestion⟩ :=
    buildSubQuery_inv st sq revealed hbuild
  have hsent : (Server.withSecrets sq rid cid).question
      = #[{ Resolver.subQuestion st.resources.sname revealed qu with
            qname := DomainName.randomizeCase cid
              (Resolver.subQuestion st.resources.sname revealed qu).qname }] := by
    unfold Server.withSecrets Server.withCaseSeed Server.withRandomId
    simp [hquestion]
  cases hp : Resolver.probeRoundB st.resources.sname revealed with
  | true =>
    rw [subQuestion_probe hp] at hsent
    obtain ⟨h0, hlt⟩ := probeRoundB_facts hp
    refine ⟨origQ, qu, _, hlq, hqu, hsent, ?_, fun _ => ⟨rfl, hlt, ?_⟩,
      fun hcontra => by simp at hcontra⟩
    ·
      rw [isAncestorB_congr_left _ _ _
        (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI cid _)]
      exact VeriDNS.Proof.QnameMin.isAncestorB_minimisedName hcanon revealed
    ·
      rw [VeriDNS.Proof.NameTree.randomizeCase_foldNameCase,
        VeriDNS.Proof.QnameMin.foldNameCase_minimisedName hcanon,
        VeriDNS.Proof.QnameMin.labelCount_minimisedName (canonicalName_fold hcanon),
        labelCount_fold hcanon]
      omega
  | false =>
    rw [subQuestion_full hp] at hsent
    obtain ⟨ls, hv, hle, hm⟩ := hcanon
    have hlabels : DomainName.wireFormatToLabels st.resources.sname = .ok ls := by
      rw [hm]; exact VeriDNS.Proof.DomainName.wireFormat_roundtrip ls hv
    refine ⟨origQ, qu, _, hlq, hqu, hsent, ?_,
      fun hcontra => by simp at hcontra, fun _ => ⟨?_, rfl⟩⟩
    · rw [isAncestorB_congr_left _ _ _
        (VeriDNS.Proof.NameTree.randomizeCase_nameEqCI cid _)]
      exact VeriDNS.Proof.Refinement.isAncestorB_self hlabels
    · exact VeriDNS.Proof.NameTree.randomizeCase_nameEqCI cid _


def SentMinimisedWire (bytes : ByteArray) (_addr : ByteArray) : Prop :=
  ∃ (st : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord) (revealed : Nat),
    CanonicalName st.resources.sname →
    ∃ (msg : Format) (q : Question),
      bytes = Message.encode msg ∧
      msg.question = #[q] ∧
      Resolver.isAncestorB q.qname st.resources.sname = true ∧
      (Resolver.probeRoundB st.resources.sname revealed = true →
        q.qtype = 1 ∧ revealed < DomainName.labelCount st.resources.sname ∧
        DomainName.labelCount (DomainName.foldNameCase q.qname) = revealed) ∧
      (Resolver.probeRoundB st.resources.sname revealed = false →
        DomainName.nameEqCI q.qname st.resources.sname = true)

theorem ioResumeLoop_sent_minimised (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel revealed : Nat) :
    AllSent SentMinimisedWire (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state deadline depth fuel revealed) := by
  refine (ioResumeLoop_sent_shape sbelt state deadline depth fuel revealed).mono ?_
  rintro bytes addr ⟨st, rev, sq, rid, cid, hbuild, rfl⟩
  refine ⟨st, rev, fun hcanon => ?_⟩
  obtain ⟨origQ, qu, q, _, _, hsent, hanc, hprobe, hfull⟩ :=
    sent_question_minimised hbuild rid cid hcanon
  exact ⟨Server.withSecrets sq rid cid, q, rfl, hsent, hanc, hprobe,
    fun hp => (hfull hp).1⟩

theorem resolveWithIO_sent_minimised (query : Format) (sbelt : DnsSList)
    (cache : DnsCache) (now : UInt32) (fuel depth : Nat) (budget : UInt32) :
    AllSent SentMinimisedWire (Server.resolveWithIO (M := Prog) (Sock := Unit)
      query sbelt cache now fuel depth budget) := by
  unfold Server.resolveWithIO
  split
  · exact allSent_pure _
  · exact ioResumeLoop_sent_minimised _ _ _ _ _ _
  · exact allSent_pure _

theorem resolveWithIO_sent_egress (query : Format) (sbelt : DnsSList)
    (cache : DnsCache) (now : UInt32) (fuel depth : Nat) (budget : UInt32) :
    AllSent SentShapeEgress (Server.resolveWithIO (M := Prog) (Sock := Unit)
      query sbelt cache now fuel depth budget) := by
  unfold Server.resolveWithIO
  split
  · exact allSent_pure _
  · exact ioResumeLoop_sent_egress _ _ _ _ _ _
  · exact allSent_pure _


/-! ### Delivery-log frames (finding 054)

`World.sent`/`World.tcpSent` record every client-reply send.  The resolver
phase (`resolveWithIO`) and the reply-assembly phase (`replyForResolution`)
contain no `sendTo`/`tcpSend` node — witnessed by their `AllSent` covers —
so running them leaves the delivery logs untouched.  These frames let the
serve capstones pin the delivery logs exactly: the single appended entry is
THE verified reply. -/

private theorem allSent_replyForResolution {P : ByteArray → ByteArray → Prop}
    (query : Format) (res : Except String Format) (cache' : DnsCache) (nowT : UInt32) :
    AllSent P (Server.replyForResolution (M := Prog) (Sock := Unit) query res cache' nowT) := by
  unfold Server.replyForResolution
  cases res with
  | error msg => exact allSent_log fun _ => allSent_pure _
  | ok resp =>
    refine allSent_bind ?_ (fun c => allSent_pure _)
    unfold Server.storeNegativeIfCacheable
    split
    · split
      · exact allSent_log fun _ => allSent_pure _
      · split
        · exact allSent_log fun _ => allSent_pure _
        · exact allSent_pure _
      · exact allSent_pure _
    · exact allSent_pure _

theorem resolveWithIO_sends_frame (query : Format) (sbelt : DnsSList)
    (cache : DnsCache) (now : UInt32) {fuel depth : Nat} {budget : UInt32}
    {n : Nat} {w : World} {x : Except String Format × DnsCache} {w' : World}
    (h : Prog.run n (Server.resolveWithIO (M := Prog) (Sock := Unit)
        query sbelt cache now fuel depth budget) w = some (x, w')) :
    w'.sent = w.sent ∧ w'.tcpSent = w.tcpSent :=
  (resolveWithIO_sent_minimised query sbelt cache now fuel depth budget).run_sends_frame h

theorem replyForResolution_sends_frame (query : Format) (res : Except String Format)
    (cache' : DnsCache) (nowT : UInt32) {n : Nat} {w : World}
    {x : Format × DnsCache} {w' : World}
    (h : Prog.run n (Server.replyForResolution (M := Prog) (Sock := Unit)
        query res cache' nowT) w = some (x, w')) :
    w'.sent = w.sent ∧ w'.tcpSent = w.tcpSent :=
  (allSent_replyForResolution (P := fun _ _ => True) query res cache' nowT).run_sends_frame h

end VeriDNS.Proof.SentMinimised
