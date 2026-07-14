import VeriDNS.Proof.FreeIO
import VeriDNS.Proof.IoResumeSound
import VeriDNS.Proof.NameTreeComplete




namespace VeriDNS.Proof.SentMinimised

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO
open VeriDNS.Proof.DeliveredWire (CanonicalName)


inductive AllSent (P : ByteArray → ByteArray → Prop) : {α : Type} → Prog α → Prop where
  | pure {α : Type} (a : α) : AllSent P (Prog.pure a)
  | step {α : Type} {c : DnsCmd} {k : DnsCmd.Res c → Prog α}
      (hc : ∀ q addr, c = .exchange q addr → P q addr)
      (htc : ∀ q addr, c = .tcpExchange q addr → P q addr)
      (hk : ∀ r, AllSent P (k r)) : AllSent P (Prog.step c k)

theorem AllSent.bind_prog {P : ByteArray → ByteArray → Prop} {α β : Type}
    {p : Prog α} {f : α → Prog β}
    (hp : AllSent P p) (hf : ∀ a, AllSent P (f a)) : AllSent P (p.bind f) := by
  induction hp with
  | pure a => exact hf a
  | step hc htc _ ih => exact .step hc htc (fun r => ih r)

theorem AllSent.mono {P Q : ByteArray → ByteArray → Prop} {α : Type} {p : Prog α}
    (h : AllSent P p) (hpq : ∀ q a, P q a → Q q a) : AllSent Q p := by
  induction h with
  | pure a => exact .pure a
  | step hc htc _ ih =>
    exact .step (fun q a hqa => hpq _ _ (hc q a hqa)) (fun q a hqa => hpq _ _ (htc q a hqa)) ih

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
  exact .step (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun r => hk r)

private theorem allSent_log {P : ByteArray → ByteArray → Prop} {β : Type} {s : String}
    {k : Unit → Prog β} (hk : ∀ u, AllSent P (k u)) :
    AllSent P ((UdpSocket.log (M := Prog) (Sock := Unit) (Addr := ByteArray) s) >>= k) := by
  show AllSent P (Prog.step (.log s) _)
  exact .step (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun r => hk r)

private theorem allSent_randomId {P : ByteArray → ByteArray → Prop} {β : Type}
    {k : UInt16 → Prog β} (hk : ∀ i, AllSent P (k i)) :
    AllSent P ((UdpSocket.randomId (M := Prog) (Sock := Unit) (Addr := ByteArray)) >>= k) := by
  show AllSent P (Prog.step .randomId _)
  exact .step (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun r => hk r)

private theorem allSent_forwardQuery {P : ByteArray → ByteArray → Prop} {β : Type}
    {query : Format} {addr : ByteArray} {k : Option Format → Prog β}
    (hq : P (Message.encode query) addr)
    (hk : ∀ o, AllSent P (k o)) :
    AllSent P ((Server.forwardQuery (M := Prog) (Sock := Unit) query addr) >>= k) := by
  show AllSent P (Prog.step (.exchange (Message.encode query) addr) _)
  refine .step (fun q' a' h => by cases h; exact hq) (fun _ _ h => nomatch h) (fun r => ?_)
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
  refine .step (fun _ _ h => nomatch h) (fun q' a' h => by cases h; exact hq) (fun r => ?_)
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


private theorem ioResumeLoop_sent_shape_aux :
    ∀ (n depth fuel : Nat), depth + fuel ≤ n →
    ∀ (sbelt : DnsSList) (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
      (deadline : UInt32) (revealed : Nat),
      AllSent SentShape (Server.ioResumeLoop (M := Prog) (Sock := Unit)
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
              refine allSent_forwardQuery
                ⟨state, revealed, subQuery₀, rid, cid, hbuild, rfl⟩ fun o => ?_
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
                        ⟨state, revealed, subQuery₀, rid, cid, hbuild, rfl⟩ fun to => ?_
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
                        ·
                          refine allSent_log fun _ => ?_
                          exact allSent_pure _
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

theorem ioResumeLoop_sent_shape (sbelt : DnsSList)
    (state : Resolver.State DnsSList DnsCache SlistEntry ResourceRecord)
    (deadline : UInt32) (depth fuel revealed : Nat) :
    AllSent SentShape (Server.ioResumeLoop (M := Prog) (Sock := Unit)
      sbelt state deadline depth fuel revealed) :=
  ioResumeLoop_sent_shape_aux (depth + fuel) depth fuel (Nat.le_refl _)
    sbelt state deadline revealed


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

end VeriDNS.Proof.SentMinimised
