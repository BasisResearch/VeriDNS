import VeriDNS.Proof.NameTree
import VeriDNS.Proof.Server
import VeriDNS.Proof.DeliveredWire




namespace VeriDNS.Proof.ServeSound

open VeriDNS.Spec
open VeriDNS.Proof.NameTree
open VeriDNS.Impl.NameTree
open VeriDNS.Impl.Server
open VeriDNS.Proof.Server
open VeriDNS.Impl.Cache (DnsCache)
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase)

variable {M : Type → Type} {Sock : Type} [Monad M] [LawfulMonad M]
  [UdpSocket M Sock ByteArray]

theorem sectionAgrees_of_subset {T : Node ResourceRecord} {a b : Array ByteArray}
    (hsub : ∀ x ∈ a.toList, x ∈ b.toList) (h : SectionAgrees T b) : SectionAgrees T a :=
  fun x hx => h x (hsub x hx)

private theorem nameEqCI_fold_eq {a b : ByteArray} (h : nameEqCI a b = true) :
    foldNameCase a = foldNameCase b := by
  have h'' : ByteArray.beq (foldNameCase a) (foldNameCase b) = true := h
  unfold ByteArray.beq at h''
  exact ByteArray.ext (eq_of_beq h'')

private theorem nameEqCI_of_fold_eq {a b : ByteArray}
    (h : foldNameCase a = foldNameCase b) : nameEqCI a b = true := by
  show ByteArray.beq (foldNameCase a) (foldNameCase b) = true
  unfold ByteArray.beq
  rw [h]
  exact beq_self_eq_true _

private theorem nameEqCI_symm' {a b : ByteArray} (h : nameEqCI a b = true) :
    nameEqCI b a = true :=
  nameEqCI_of_fold_eq (nameEqCI_fold_eq h).symm

private theorem nameEqCI_trans' {a b c : ByteArray} (h₁ : nameEqCI a b = true)
    (h₂ : nameEqCI b c = true) : nameEqCI a c = true :=
  nameEqCI_of_fold_eq ((nameEqCI_fold_eq h₁).trans (nameEqCI_fold_eq h₂))

theorem rrInTree_owner_congrCI {T : Node ResourceRecord} {rr : ResourceRecord} {m : ByteArray}
    (h : RRInTree T rr) (hci : nameEqCI m rr.name = true) :
    RRInTree T { rr with name := m } := by
  obtain ⟨n, hnode, rr', hmem, hsd⟩ := h
  refine ⟨n, ?_, rr', hmem, ?_⟩
  · show nodeAtName T m = some n
    rw [nodeAtName_congrCI T hci]
    exact hnode
  · unfold sameData at hsd ⊢
    simp only [Bool.and_eq_true] at hsd ⊢
    exact ⟨⟨⟨nameEqCI_trans' hsd.1.1.1 (nameEqCI_symm' hci), hsd.1.1.2⟩, hsd.1.2⟩, hsd.2⟩

theorem deliveredResponse_sectionAgrees {T : Node ResourceRecord} (query resp : Format)
    (hca : VeriDNS.Proof.DeliveredWire.CanonicalSection resp.answer)
    (hqn : VeriDNS.Proof.DeliveredWire.CanonicalName (clientQname query))
    (h : SectionAgrees T resp.answer) :
    SectionAgrees T (deliveredResponse query resp).answer := by
  intro b' hb'
  rw [deliveredResponse_answer] at hb'
  obtain ⟨b, hb, rr, hpr, m, hm, hci, rfl⟩ :=
    VeriDNS.Impl.Resolver.scrubAnswerB_mem (Array.mem_def.mpr hb')
  obtain ⟨ls, t, c, ttl, rdata, hv, hle, hrd, hbe, hpr'⟩ :=
    VeriDNS.Proof.DeliveredWire.canonicalRR_parse (hca b hb)
  obtain ⟨rrT, hprT, hinT⟩ := h b (Array.mem_def.mp hb)
  obtain rfl : _ = rr := Option.some.inj (hpr'.symm.trans hpr)
  obtain rfl : _ = rrT := Option.some.inj (hpr'.symm.trans hprT)
  obtain ⟨ms, hvms, hlems, rfl⟩ :=
    VeriDNS.Proof.DeliveredWire.reachableNamesB_canonical hca hqn m hm
  rw [show VeriDNS.Impl.Resolver.setOwnerB (RR := ResourceRecord) _ b
        (VeriDNS.Impl.DomainName.labelsToWireFormat ms)
      = VeriDNS.Proof.Message.rrWire ms t c ttl rdata from by
    rw [hbe]
    exact VeriDNS.Proof.DeliveredWire.setOwnerB_rrWire ls ms t c ttl rdata rfl]
  refine ⟨_, VeriDNS.Proof.DeliveredWire.parseRaw_rrWire ms hvms hlems t c ttl rdata
    (VeriDNS.Proof.Message.canonicalRdata_size_lt hrd), ?_⟩
  exact rrInTree_owner_congrCI hinT (nameEqCI_symm' hci)

theorem replyForResolution_answer_sound {T : Node ResourceRecord}
    (query : Format) (rr : Except String Format) (cache' : DnsCache) (nowT : UInt32)
    (hqn : VeriDNS.Proof.DeliveredWire.CanonicalName (clientQname query))
    (hca : ∀ resp, rr = .ok resp → VeriDNS.Proof.DeliveredWire.CanonicalSection resp.answer)
    (hsound : ShimSound T (rr, cache')) :
    SatisfiesM (fun p : Format × DnsCache => SectionAgrees T p.1.answer)
      (replyForResolution (M := M) (Sock := Sock) query rr cache' nowT) := by
  cases rr with
  | error msg =>
    unfold replyForResolution
    simp only []
    apply SatisfiesM.bind_pre
    apply SatisfiesM.of_true
    intro _
    refine SatisfiesM.pure ?_
    intro b hb
    exact absurd hb (by simp [finalizeForClient, buildErrorResponse, buildResponse])
  | ok resp =>
    have hans : SectionAgrees T resp.answer := hsound.1 resp rfl
    apply SatisfiesM.imp (replyForResolution_ok_fst (M := M) (Sock := Sock) query resp cache' nowT)
    rintro ⟨r, c⟩ (hfst : r = deliveredResponse query resp)
    show SectionAgrees T r.answer
    rw [hfst]
    exact deliveredResponse_sectionAgrees query resp (hca resp rfl) hqn hans

theorem resolveThenReply_sound {T : Node ResourceRecord}
    (query : Format) (sbelt : VeriDNS.Impl.SList.DnsSList)
    {cache : DnsCache} (now : UInt32) (fuel depth : Nat) (budget : UInt32)
    (hqn : VeriDNS.Proof.DeliveredWire.CanonicalName (clientQname query))
    (hrun : SatisfiesM (fun r : Except String Format × DnsCache =>
        ShimSound T r
        ∧ ∀ resp, r.1 = .ok resp → VeriDNS.Proof.DeliveredWire.CanonicalSection resp.answer)
      (resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget)) :
    SatisfiesM (fun p : Format × DnsCache => SectionAgrees T p.1.answer)
      (resolveWithIO (M := M) (Sock := Sock) query sbelt cache now fuel depth budget
        >>= fun r => replyForResolution (M := M) (Sock := Sock) query r.1 r.2 now) := by
  refine SatisfiesM.bind hrun ?_
  rintro ⟨result, cache'⟩ ⟨hshim, hcanon⟩
  exact replyForResolution_answer_sound query result cache' now hqn hcanon hshim
