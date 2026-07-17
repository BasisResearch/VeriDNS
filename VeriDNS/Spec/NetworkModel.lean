import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.NameTree
import VeriDNS.Spec.RRType
import VeriDNS.Spec.RRClass
import VeriDNS.RFC.Check

namespace VeriDNS.Spec.Net

open VeriDNS.Spec (RRType RRClass Node)

@[blueprint "Net.Name"]
abbrev Name := List ByteArray
rfc_proves VeriDNS.Spec.Net.Name [1034][366:372]

def L (s : String) : ByteArray := s.toUTF8
rfc_proves VeriDNS.Spec.Net.L [1034][362:365]

def N (ss : List String) : Name := ss.map L
rfc_proves VeriDNS.Spec.Net.N [1034][366:372]

def foldByte (x : UInt8) : UInt8 :=
  cond (Nat.ble 65 x.toNat && Nat.ble x.toNat 90) (x + 32) x
rfc_proves VeriDNS.Spec.Net.foldByte [1034][378:396]

def bytesEqCI : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | x :: xs, y :: ys => (foldByte x == foldByte y) && bytesEqCI xs ys
  | _, _ => false
rfc_proves VeriDNS.Spec.Net.bytesEqCI [1034][378:396]

def labelEq (a b : ByteArray) : Bool := bytesEqCI a.data.toList b.data.toList
rfc_proves VeriDNS.Spec.Net.labelEq [1034][378:396]

def nameEq : Name → Name → Bool
  | [], [] => true
  | x :: xs, y :: ys => labelEq x y && nameEq xs ys
  | _, _ => false
rfc_proves VeriDNS.Spec.Net.nameEq [1034][378:396]

def nameEqCS : Name → Name → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x == y) && nameEqCS xs ys
  | _, _ => false
rfc_proves VeriDNS.Spec.Net.nameEqCS [5452][258:278]

def isAncestor (anc n : Name) : Bool :=
  cond (Nat.ble anc.length n.length) (nameEq anc (n.drop (n.length - anc.length))) false
rfc_proves VeriDNS.Spec.Net.isAncestor [1034][423:430]

def ProbeFor (probe qname cut : Name) : Bool :=
  isAncestor cut probe && isAncestor probe qname
    && Nat.blt cut.length probe.length && Nat.blt probe.length qname.length
rfc_proves VeriDNS.Spec.Net.ProbeFor [9156][158:168]

def Node.descend {R : Type} (t : Node R) : List ByteArray → Option (Node R)
  | [] => some t
  | l :: rest =>
    match t.children.find? (fun c => labelEq c.label l) with
    | some c => Node.descend c rest
    | none => none
rfc_proves VeriDNS.Spec.Net.Node.descend [1034][1306:1310]

def Node.lookupPath {R : Type} (t : Node R) (n : Name) : Option (Node R) :=
  Node.descend t n.reverse
rfc_proves VeriDNS.Spec.Net.Node.lookupPath [1034][366:372]

@[blueprint "Net.IPv4"]
structure IPv4 where
  o0 : UInt8
  o1 : UInt8
  o2 : UInt8
  o3 : UInt8
  deriving DecidableEq, BEq, Inhabited
rfc_proves VeriDNS.Spec.Net.IPv4 [1035][1099:1110]

def IPv4.wireOctets : IPv4 → List UInt8
  | ⟨a, b, c, d⟩ => [a, b, c, d]
rfc_proves VeriDNS.Spec.Net.IPv4.wireOctets [1035][1099:1110]

def IPv4.toDotted (ip : IPv4) : String :=
  s!"{ip.o0.toNat}.{ip.o1.toNat}.{ip.o2.toNat}.{ip.o3.toNat}"
rfc_proves VeriDNS.Spec.Net.IPv4.toDotted [1035][1099:1110]

@[blueprint "Net.RData"]
inductive RData where
  | a (addr : IPv4)
  | ns (host : Name)
  | cname (target : Name)
  | soa (mname rname : Name) (serial refresh retry expire minimum : Nat)
  | mx (pref : Nat) (exch : Name)
  | hinfo (cpu os : String)
  | ptr (target : Name)
  | generic (t : RRType) (data : ByteArray)
  deriving BEq, Inhabited, DecidableEq
rfc_proves VeriDNS.Spec.Net.RData [1034][622:693]
rfc_proves VeriDNS.Spec.Net.RData [3597][77:83]

def RData.rtype : RData → RRType
  | .a _ => .a
  | .ns _ => .ns
  | .cname _ => .cname
  | .soa .. => .soa
  | .mx .. => .mx
  | .hinfo .. => .hinfo
  | .ptr _ => .ptr
  | .generic t _ => t
rfc_proves VeriDNS.Spec.Net.RData.rtype [1034][622:693]

@[blueprint "Net.RR"]
structure RR where
  owner : Name
  ttl : Nat
  rdata : RData
  cls : RRClass := RRClass.in
  deriving BEq, Inhabited, DecidableEq
rfc_proves VeriDNS.Spec.Net.RR [1034][622:693]

def RR.rtype (r : RR) : RRType := r.rdata.rtype
rfc_proves VeriDNS.Spec.Net.RR.rtype [1034][622:693]

@[blueprint "Net.QType"]
inductive QType where
  | rr (t : RRType)
  | star
  deriving BEq, Inhabited
rfc_proves VeriDNS.Spec.Net.QType [1035][660:680]

def QType.covers : QType → RRType → Bool
  | .star, _ => true
  | .rr t, t' => t == t'
rfc_proves VeriDNS.Spec.Net.QType.covers [1035][677:680]

structure Query where
  qname : Name
  qtype : QType
  qclass : RRClass := RRClass.in

  rd : Bool := false
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Query [1034][1177:1184]

inductive RCode where
  | noError
  | nameError
  | servFail
  deriving BEq, Inhabited
rfc_proves VeriDNS.Spec.Net.RCode [1035][1476:1481]

structure Response where
  aa : Bool
  rcode : RCode
  answer : List RR
  authority : List RR
  additional : List RR

  ra : Bool := false

  tc : Bool := false
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Response [1035][1404:1412]

@[blueprint "Net.Delegation"]
structure Delegation where
  subapex : Name
  nsSet : List RR
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Delegation [1034][1106:1110]

@[blueprint "Net.Zone"]
structure Zone where
  apex : Name
  records : List RR
  delegations : List Delegation

  cls : RRClass := RRClass.in

  negCacheNS : Bool := false
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Zone [1034][1043:1046]

@[blueprint "Net.Time"]
abbrev Time := Nat
rfc_proves VeriDNS.Spec.Net.Time [1034][701:708]

@[blueprint "Net.CacheEntry"]
structure CacheEntry where
  rr : RR
  insertedAt : Time
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.CacheEntry [1034][701:708]

def CacheEntry.expiresAt (e : CacheEntry) : Time := e.insertedAt + e.rr.ttl
rfc_proves VeriDNS.Spec.Net.CacheEntry.expiresAt [1034][704:708]

def CacheEntry.fresh (e : CacheEntry) (now : Time) : Bool := Nat.blt now e.expiresAt
rfc_proves VeriDNS.Spec.Net.CacheEntry.fresh [1034][704:708]

def CacheEntry.agedTTL (e : CacheEntry) (now : Time) : Nat :=
  e.rr.ttl - (now - e.insertedAt)
rfc_proves VeriDNS.Spec.Net.CacheEntry.agedTTL [1034][2247:2253]

def CacheEntry.aged (e : CacheEntry) (now : Time) : RR := { e.rr with ttl := e.agedTTL now }
rfc_proves VeriDNS.Spec.Net.CacheEntry.aged [1034][2247:2253]

@[blueprint "Net.Server"]
structure Server where
  name : Name
  zones : List Zone
  cache : List CacheEntry
  addr : String := ""

  recursionAvailable : Bool := false

  rtt : Nat := 0
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Server [1034][992:1000]

@[blueprint "Net.Network"]
structure Network where
  servers : List Server
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.Network [1034][994:1000]

def Network.hostsZone (net : Network) (sname : Name) (z : Zone) : Prop :=
  ∃ s, s ∈ net.servers ∧ nameEq s.name sname = true ∧ z ∈ s.zones
rfc_proves VeriDNS.Spec.Net.Network.hostsZone [1034][994:1000]
include_rfc [1034][1289:1366] {
4.3.2. Algorithm

The actual algorithm used by the name server will depend on the local OS
and data structures used to store RRs.  The following algorithm assumes
that the RRs are organized in several tree structures, one for each
zone, and another for the cache:

   1. Set or clear the value of recursion available in the response
      depending on whether the name server is willing to provide
      recursive service.  If recursive service is available and
      requested via the RD bit in the query, go to step 5,
      otherwise step 2.

   2. Search the available zones for the zone which is the nearest
      ancestor to QNAME.  If such a zone is found, go to step 3,
      otherwise step 4.

   3. Start matching down, label by label, in the zone.  The
      matching process can terminate several ways:

         a. If the whole of QNAME is matched, we have found the
            node.

            If the data at the node is a CNAME, and QTYPE doesn't
            match CNAME, copy the CNAME RR into the answer section
            of the response, change QNAME to the canonical name in
            the CNAME RR, and go back to step 1.

            Otherwise, copy all RRs which match QTYPE into the
            answer section and go to step 6.

         b. If a match would take us out of the authoritative data,
            we have a referral.  This happens when we encounter a
            node with NS RRs marking cuts along the bottom of a
            zone.

            Copy the NS RRs for the subzone into the authority
            section of the reply.  Put whatever addresses are
            available into the additional section, using glue RRs
            if the addresses are not available from authoritative
            data or the cache.  Go to step 4.

         c. If at some label, a match is impossible (i.e., the
            corresponding label does not exist), look to see if a
            the "*" label exists.

            If the "*" label does not exist, check whether the name
            we are looking for is the original QNAME in the query
            or a name we have followed due to a CNAME.  If the name
            is original, set an authoritative name error in the
            response and exit.  Otherwise just exit.

            If the "*" label does exist, match RRs at that node
            against QTYPE.  If any match, copy them into the answer
            section, but set the owner of the RR to be QNAME, and
            not the node with the "*" label.  Go to step 6.

   4. Start matching down in the cache.  If QNAME is found in the
      cache, copy all RRs attached to it that match QTYPE into the
      answer section.  If there was no delegation from
      authoritative data, look for the best one from the cache, and
      put it in the authority section.  Go to step 6.

   5. Using the local resolver or a copy of its algorithm (see
      resolver section of this memo) to answer the query.  Store
      the results, including any intermediate CNAMEs, in the answer
      section of the response.

   6. Using local data only, attempt to add other RRs which may be
      useful to the additional section of the query.  Exit.
}
def bestZone (s : Server) (qname : Name) (qcls : RRClass) : Option Zone :=
  (s.zones.filter (fun z => z.cls == qcls && isAncestor z.apex qname)).foldl
    (fun acc z => match acc with
      | none => some z
      | some z' => if z'.apex.length < z.apex.length then some z else some z')
    none
rfc_proves VeriDNS.Spec.Net.bestZone [1034][1300:1304]

def bestDeleg (z : Zone) (qname : Name) : Option Delegation :=
  (z.delegations.filter (fun d => isAncestor d.subapex qname)).foldl
    (fun acc d => match acc with
      | none => some d
      | some d' => if d'.subapex.length < d.subapex.length then some d else some d')
    none
rfc_proves VeriDNS.Spec.Net.bestDeleg [1034][1319:1330]

theorem foldl_pickDeleg_mem (l : List Delegation) (init : Option Delegation) (d : Delegation)
    (h : (l.foldl (fun acc x => match acc with
            | none => some x
            | some d' => if d'.subapex.length < x.subapex.length then some x else some d') init)
          = some d) :
    d ∈ l ∨ init = some d := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil] at h; exact Or.inr h
  | cons x t ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with hmem | hinit
    · exact Or.inl (List.mem_cons_of_mem _ hmem)
    · cases init with
      | none => simp only [Option.some.injEq] at hinit; subst hinit; exact Or.inl (List.mem_cons_self ..)
      | some d' =>
        simp only at hinit
        split at hinit
        · rw [Option.some.injEq] at hinit; subst hinit; exact Or.inl (List.mem_cons_self ..)
        · exact Or.inr hinit

theorem bestDeleg_isAncestor (z : Zone) (qname : Name) (d : Delegation)
    (h : bestDeleg z qname = some d) : isAncestor d.subapex qname = true := by
  unfold bestDeleg at h
  rcases foldl_pickDeleg_mem _ none d h with hmem | hinit
  · exact (List.mem_filter.mp hmem).2
  · exact absurd hinit (by simp)

inductive AuthoritativeFor (net : Network) (qcls : RRClass) : Name → Name → Prop where
  | mk (sname qname : Name) (s : Server) (z : Zone) :
      s ∈ net.servers →
      nameEq s.name sname = true →
      bestZone s qname qcls = some z →
      bestDeleg z qname = none →
      AuthoritativeFor net qcls sname qname
rfc_proves VeriDNS.Spec.Net.AuthoritativeFor [1034][1040:1046]

inductive DelegatesTo (net : Network) (qcls : RRClass) : Name → Name → Name → Prop where
  | mk (sname qname : Name) (s : Server) (z : Zone) (d : Delegation) :
      s ∈ net.servers →
      nameEq s.name sname = true →
      bestZone s qname qcls = some z →
      d ∈ z.delegations →
      isAncestor d.subapex qname = true →
      DelegatesTo net qcls sname qname d.subapex
rfc_proves VeriDNS.Spec.Net.DelegatesTo [1034][1319:1330]

def recordsAt (z : Zone) (qname : Name) : List RR :=
  z.records.filter (fun r => nameEq r.owner qname)
rfc_proves VeriDNS.Spec.Net.recordsAt [1034][1306:1310]

def isEmptyNonTerminal (z : Zone) (qname : Name) : Bool :=
  z.records.any (fun r => isAncestor qname r.owner && !nameEq qname r.owner)
    || z.delegations.any (fun d => isAncestor qname d.subapex && !nameEq qname d.subapex)
rfc_proves VeriDNS.Spec.Net.isEmptyNonTerminal [2308][274:376]

def nameKnown (z : Zone) (m : Name) : Bool :=
  z.records.any (fun r => isAncestor m r.owner) || z.delegations.any (fun d => isAncestor m d.subapex)
rfc_proves VeriDNS.Spec.Net.nameKnown [1034][1407:1414]

def soaOf (z : Zone) : Option RR :=
  z.records.find? (fun r => r.rdata.rtype == RRType.soa && nameEq r.owner z.apex)
rfc_proves VeriDNS.Spec.Net.soaOf [2308][404:412]

def apexNS (z : Zone) : List RR :=
  z.records.filter (fun r => r.rdata.rtype == RRType.ns && nameEq r.owner z.apex)
rfc_proves VeriDNS.Spec.Net.apexNS [2308][274:376]

def noDataAuthority (z : Zone) : List RR :=
  (soaOf z).toList ++ (if z.negCacheNS then apexNS z else [])
rfc_proves VeriDNS.Spec.Net.noDataAuthority [2308][274:376]

def nxdomainAuthority (z : Zone) : List RR :=
  (soaOf z).toList ++ (if z.negCacheNS then apexNS z else [])
rfc_proves VeriDNS.Spec.Net.nxdomainAuthority [2308][129:204]

def RData.soaMinimum : RData → Option Nat
  | .soa _ _ _ _ _ _ minimum => some minimum
  | _ => none
rfc_proves VeriDNS.Spec.Net.RData.soaMinimum [2308][404:412]

def negTTLof (soa : RR) : Option Nat := soa.rdata.soaMinimum.map (fun m => min m soa.ttl)
rfc_proves VeriDNS.Spec.Net.negTTLof [2308][404:412]

def negTTL (z : Zone) : Option Nat := (soaOf z).bind negTTLof
rfc_proves VeriDNS.Spec.Net.negTTL [2308][404:412]

def Response.negSOA (r : Response) : Option RR := r.authority.find? (fun rr => rr.rdata.rtype == RRType.soa)
rfc_proves VeriDNS.Spec.Net.Response.negSOA [2308][404:412]

def Response.negTTL (r : Response) : Option Nat := r.negSOA.bind negTTLof
rfc_proves VeriDNS.Spec.Net.Response.negTTL [2308][404:412]

structure NegCacheEntry where
  qname : Name
  soa : RR
  insertedAt : Time
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.NegCacheEntry [2308][404:412]

def NegCacheEntry.ttl (e : NegCacheEntry) : Option Nat := negTTLof e.soa
rfc_proves VeriDNS.Spec.Net.NegCacheEntry.ttl [2308][404:412]

def NegCacheEntry.expiresAt (e : NegCacheEntry) : Time := e.insertedAt + (e.ttl.getD 0)
rfc_proves VeriDNS.Spec.Net.NegCacheEntry.expiresAt [2308][404:412]

def NegCacheEntry.fresh (e : NegCacheEntry) (now : Time) : Bool := Nat.blt now e.expiresAt
rfc_proves VeriDNS.Spec.Net.NegCacheEntry.fresh [2308][404:412]

def freshServerCache (s : Server) (now : Time) : List RR :=
  (s.cache.filter (·.fresh now)).map (·.aged now)
rfc_proves VeriDNS.Spec.Net.freshServerCache [1034][1354:1364]

def cachedAnswer (s : Server) (now : Time) (q : Query) : List RR :=
  (freshServerCache s now).filter
    (fun r => nameEq r.owner q.qname && q.qtype.covers r.rdata.rtype && r.cls == q.qclass)
rfc_proves VeriDNS.Spec.Net.cachedAnswer [1034][1354:1364]

def cachedDelegation (s : Server) (now : Time) (qname : Name) (qcls : RRClass) : List RR :=
  let nsRecs := (freshServerCache s now).filter
    (fun r => r.rdata.rtype == RRType.ns && r.cls == qcls && isAncestor r.owner qname)
  let maxLen := nsRecs.foldl (fun m r => max m r.owner.length) 0
  nsRecs.filter (fun r => r.owner.length == maxLen)
rfc_proves VeriDNS.Spec.Net.cachedDelegation [1034][1354:1364]

def cnameRR (qname : Name) (recs : List RR) : Option RR :=
  recs.find? (fun r => r.rdata.rtype == RRType.cname && nameEq r.owner qname)
rfc_proves VeriDNS.Spec.Net.cnameRR [1034][1311:1318]

@[simp] theorem cnameRR_nil (qname : Name) : cnameRR qname ([] : List RR) = none := rfl

theorem cnameRR_filter_none (qname : Name) (here : List RR) (f : RR → Bool)
    (h : cnameRR qname here = none) :
    cnameRR qname (here.filter f) = none := by
  unfold cnameRR at h ⊢
  rw [List.find?_eq_none] at h ⊢
  intro x hx
  exact h x (List.mem_filter.mp hx).1

def cnameAlone (recs : List RR) : Bool :=
  !recs.any (fun r => r.rdata.rtype == RRType.cname)
    || recs.all (fun r => r.rdata.rtype == RRType.cname)
rfc_proves VeriDNS.Spec.Net.cnameAlone [1034][1311:1318]

theorem cnameAlone_forces_cname {qname : Name} {recs : List RR} {c : RR} {qt : QType} {qcls : RRClass}
    (hca : cnameAlone recs = true) (hcn : cnameRR qname recs = some c)
    (hqt : qt.covers RRType.cname = false) :
    recs.filter (fun r => qt.covers r.rdata.rtype && r.cls == qcls) = [] := by
  simp only [cnameRR] at hcn
  have hpc0 := List.find?_some hcn
  rw [Bool.and_eq_true] at hpc0
  have hpc := hpc0.1
  have hmem : c ∈ recs := List.mem_of_find?_eq_some hcn
  have hany : recs.any (fun r => r.rdata.rtype == RRType.cname) = true :=
    List.any_eq_true.mpr ⟨c, hmem, hpc⟩
  have hall : recs.all (fun r => r.rdata.rtype == RRType.cname) = true := by
    simp only [cnameAlone, hany, Bool.not_true, Bool.false_or] at hca; exact hca
  rw [List.filter_eq_nil_iff]
  intro r hr
  have hb : (r.rdata.rtype == RRType.cname) = true := List.all_eq_true.mp hall r hr
  cases qt with
  | star => exact absurd hqt (by decide)
  | rr t =>
    simp only [QType.covers] at hqt ⊢
    revert hb
    cases r.rdata.rtype <;> intro hb <;>
      first
        | exact absurd hb (by decide)
        | exact Bool.noConfusion hb
        | simp [hqt]
rfc_proves VeriDNS.Spec.Net.cnameAlone_forces_cname [1034][1311:1318]

def isA (r : RR) : Bool := match r.rdata with | .a _ => true | _ => false
rfc_proves VeriDNS.Spec.Net.isA [1034][1326:1330]

def addressesFor (recs : List RR) (target : Name) : List RR :=
  recs.filter (fun r => nameEq r.owner target && isA r)
rfc_proves VeriDNS.Spec.Net.addressesFor [1034][1326:1330]

def targetOf : RData → Option Name
  | .mx _ e => some e
  | .ns h => some h
  | _ => none
rfc_proves VeriDNS.Spec.Net.targetOf [1034][1365:1366]

def RR.eqCI (a b : RR) : Bool :=
  nameEq a.owner b.owner && a.ttl == b.ttl && a.rdata == b.rdata && a.cls == b.cls
rfc_proves VeriDNS.Spec.Net.RR.eqCI [1034][378:396]

def additionalFrom (pool : List RR) (recs : List RR) : List RR :=
  (recs.flatMap (fun r =>
    match targetOf r.rdata with
    | some t => addressesFor pool t
    | none => [])).filter (fun a => ! recs.any (fun r => RR.eqCI r a))
rfc_proves VeriDNS.Spec.Net.additionalFrom [1034][1365:1366]

def inBailiwick (subapex host : Name) : Bool := isAncestor subapex host
rfc_proves VeriDNS.Spec.Net.inBailiwick [1034][1326:1330]

def inBailiwickNS (d : Delegation) : List RR :=
  d.nsSet.filter (fun r => match targetOf r.rdata with
    | some h => inBailiwick d.subapex h
    | none => false)
rfc_proves VeriDNS.Spec.Net.inBailiwickNS [1034][1326:1330]

def outOfBailiwickNS (d : Delegation) : List RR :=
  d.nsSet.filter (fun r => match targetOf r.rdata with
    | some h => ! inBailiwick d.subapex h
    | none => true)
rfc_proves VeriDNS.Spec.Net.outOfBailiwickNS [1034][1326:1330]

def referralAdditional (pool : List RR) (d : Delegation) : List RR :=
  let glue := additionalFrom pool (inBailiwickNS d)
  glue ++ (additionalFrom pool (outOfBailiwickNS d)).filter
    (fun a => ! glue.any (fun g => RR.eqCI g a))
rfc_proves VeriDNS.Spec.Net.referralAdditional [1034][1340:1366]

def wildcardSynth (z : Zone) (qname : Name) (qt : QType) (qcls : RRClass) : Option (List RR) :=
  if nameKnown z qname then none else
  let applies := fun (k : Nat) =>
    let wrecs := (recordsAt z (L "*" :: qname.drop (k + 1))).filter
      (fun r => qt.covers r.rdata.rtype && r.cls == qcls)
    let noIntervening := (List.range k).all (fun m => ! nameKnown z (qname.drop (m + 1)))
    if !wrecs.isEmpty && noIntervening then some wrecs else none
  ((List.range qname.length).findSome? applies).map (fun wrecs =>
    wrecs.map (fun r => { r with owner := qname }))
rfc_proves VeriDNS.Spec.Net.wildcardSynth [1034][1349:1364]

inductive Step where
  | findZone (apex : Name)
  | matchNode (qname : Name)
  | copyAnswer
  | followCNAME (target : Name)
  | referral (subzone : Name)
  | wildcard
  | nameError
  | noData
  | exitFollowed
  | fromCache
  | addAdditional
  deriving BEq, Inhabited
rfc_proves VeriDNS.Spec.Net.Step [1034][1289:1366]

inductive ServerAnswers (s : Server) (now : Time) : List Name → Bool → Query → List Step → Response → Prop where

  | answer {seen : List Name} {o : Bool} (q : Query) (z : Zone) (here : List RR)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = none)
      (hh : recordsAt z q.qname = here)
      (hnc : cnameRR q.qname here = none ∨ q.qtype.covers RRType.cname = true)
      (hmatch : here.filter (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass) ≠ []) :
      ServerAnswers s now seen o q
        [Step.findZone z.apex, Step.matchNode q.qname, Step.copyAnswer, Step.addAdditional]
        { aa := true, rcode := RCode.noError, ra := s.recursionAvailable,
          answer := here.filter (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass),
          authority := [],
          additional := additionalFrom (z.records ++ freshServerCache s now)
            (here.filter (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass)) }

  | cname {seen : List Name} {o : Bool} (q : Query) (z : Zone) (c : RR) (target : Name)
      (tr : List Step) (rest : Response)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = none)
      (hc : cnameRR q.qname (recordsAt z q.qname) = some c)
      (hcov : q.qtype.covers RRType.cname = false)
      (ht : c.rdata = RData.cname target)
      (hfresh : target ∉ q.qname :: seen)
      (hrec : ServerAnswers s now (q.qname :: seen) false { q with qname := target } tr rest) :
      ServerAnswers s now seen o q
        (Step.findZone z.apex :: Step.matchNode q.qname :: Step.followCNAME target :: tr)
        { rest with answer := c :: rest.answer, aa := true }

  | referral {seen : List Name} {o : Bool} (q : Query) (z : Zone) (d : Delegation)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = some d)
      (hca : cachedAnswer s now q = []) :
      ServerAnswers s now seen o q
        [Step.findZone z.apex, Step.referral d.subapex, Step.addAdditional]
        { aa := false, rcode := RCode.noError, ra := s.recursionAvailable, answer := [],
          authority := d.nsSet,
          additional := referralAdditional (z.records ++ freshServerCache s now) d }

  | referralCacheAnswer {seen : List Name} {o : Bool} (q : Query) (z : Zone) (d : Delegation)
      (here : List RR)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = some d)
      (hca : cachedAnswer s now q = here)
      (hne : here ≠ []) :
      ServerAnswers s now seen o q
        [Step.findZone z.apex, Step.referral d.subapex, Step.copyAnswer, Step.addAdditional]
        { aa := false, rcode := RCode.noError, ra := s.recursionAvailable, answer := here,
          authority := d.nsSet,
          additional := referralAdditional (z.records ++ freshServerCache s now) d }

  | wildcard {seen : List Name} {o : Bool} (q : Query) (z : Zone) (syn : List RR)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = none)
      (hh : recordsAt z q.qname = [])
      (hent : isEmptyNonTerminal z q.qname = false)
      (hw : wildcardSynth z q.qname q.qtype q.qclass = some syn) :
      ServerAnswers s now seen o q
        [Step.findZone z.apex, Step.wildcard, Step.addAdditional]
        { aa := true, rcode := RCode.noError, ra := s.recursionAvailable, answer := syn, authority := [],
          additional := additionalFrom (z.records ++ freshServerCache s now) syn }

  | nameError {seen : List Name} (q : Query) (z : Zone)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = none)
      (hh : recordsAt z q.qname = [])
      (hw : wildcardSynth z q.qname q.qtype q.qclass = none)
      (hent : isEmptyNonTerminal z q.qname = false) :
      ServerAnswers s now seen true q
        [Step.findZone z.apex, Step.nameError]
        { aa := true, rcode := RCode.nameError, ra := s.recursionAvailable, answer := [],
          authority := nxdomainAuthority z, additional := [] }

  | noData {seen : List Name} {o : Bool} (q : Query) (z : Zone) (here : List RR)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = none)
      (hh : recordsAt z q.qname = here)
      (hnc : cnameRR q.qname here = none ∨ q.qtype.covers RRType.cname = true)
      (hempty : here.filter (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass) = [])
      (hw : wildcardSynth z q.qname q.qtype q.qclass = none)
      (hexists : here ≠ [] ∨ isEmptyNonTerminal z q.qname = true) :
      ServerAnswers s now seen o q
        [Step.findZone z.apex, Step.noData]
        { aa := true, rcode := RCode.noError, ra := s.recursionAvailable, answer := [],
          authority := noDataAuthority z, additional := [] }

  | exitFollowed {seen : List Name} (q : Query) (z : Zone)
      (hz : bestZone s q.qname q.qclass = some z)
      (hd : bestDeleg z q.qname = none)
      (hh : recordsAt z q.qname = [])
      (hw : wildcardSynth z q.qname q.qtype q.qclass = none)
      (hent : isEmptyNonTerminal z q.qname = false) :
      ServerAnswers s now seen false q
        [Step.findZone z.apex, Step.exitFollowed]
        { aa := true, rcode := RCode.noError, ra := s.recursionAvailable, answer := [], authority := [], additional := [] }

  | fromCache {seen : List Name} {o : Bool} (q : Query) (here : List RR)
      (hz : bestZone s q.qname q.qclass = none)
      (hh : (s.cache.filter (fun e => e.fresh now && nameEq e.rr.owner q.qname
                && q.qtype.covers e.rr.rdata.rtype && e.rr.cls == q.qclass)).map
              (·.aged now) = here)

      (hne : here ≠ [] ∨ cachedDelegation s now q.qname q.qclass ≠ []) :
      ServerAnswers s now seen o q
        [Step.fromCache, Step.addAdditional]
        { aa := false, rcode := RCode.noError, ra := s.recursionAvailable, answer := here,
          authority := cachedDelegation s now q.qname q.qclass,
          additional := additionalFrom (freshServerCache s now) (cachedDelegation s now q.qname q.qclass) }

  | cacheMiss {seen : List Name} {o : Bool} (q : Query)
      (hz : bestZone s q.qname q.qclass = none)
      (hmiss : (s.cache.filter (fun e => e.fresh now && nameEq e.rr.owner q.qname
                && q.qtype.covers e.rr.rdata.rtype && e.rr.cls == q.qclass)).map
                (·.aged now) = [])
      (hnodeleg : cachedDelegation s now q.qname q.qclass = []) :
      ServerAnswers s now seen o q
        [Step.fromCache, Step.addAdditional]
        { aa := false, rcode := RCode.noError, ra := s.recursionAvailable, answer := [],
          authority := [], additional := [] }
rfc_proves VeriDNS.Spec.Net.ServerAnswers [1034][1289:1366]

abbrev ServerReplies (s : Server) (now : Time) (q : Query) (tr : List Step) (resp : Response) : Prop :=
  ServerAnswers s now [] true q tr resp
rfc_proves VeriDNS.Spec.Net.ServerReplies [1034][1185:1192]

def Step.cnameTarget : Step → Option Name
  | .followCNAME t => some t
  | _ => none

def chainNames (tr : List Step) : List Name := tr.filterMap Step.cnameTarget
rfc_proves VeriDNS.Spec.Net.chainNames [1034][1311:1318]

theorem cname_acyclic {s : Server} {now : Time} {seen : List Name} {o : Bool} {q : Query}
    {tr : List Step} {resp : Response} (h : ServerAnswers s now seen o q tr resp) :
    (chainNames tr).Nodup ∧ ∀ n ∈ chainNames tr, n ∉ q.qname :: seen := by
  induction h with
  | cname q z c target tr' rest hz hd hc hcov ht hfresh hrec ih =>
      obtain ⟨ihnd, ihmem⟩ := ih
      have htgt : target ∉ chainNames tr' := fun hm => (ihmem target hm) (List.mem_cons_self ..)
      refine ⟨List.nodup_cons.mpr ⟨htgt, ihnd⟩, ?_⟩
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn'
      · exact hfresh
      · exact fun hc2 => (ihmem n hn') (List.mem_cons_of_mem _ hc2)
  | _ => exact ⟨by simp [chainNames, Step.cnameTarget], by simp [chainNames, Step.cnameTarget]⟩
rfc_proves VeriDNS.Spec.Net.cname_acyclic [1034][1705:1712]

theorem ent_imp_nameKnown {z : Zone} {m : Name}
    (h : isEmptyNonTerminal z m = true) : nameKnown z m = true := by
  simp only [isEmptyNonTerminal, nameKnown, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true] at h ⊢
  rcases h with ⟨r, hr, ha, _⟩ | ⟨d, hd, ha, _⟩
  · exact Or.inl ⟨r, hr, ha⟩
  · exact Or.inr ⟨d, hd, ha⟩

theorem wildcardSynth_some_not_known {z : Zone} {qname : Name} {qt : QType} {qcls : RRClass}
    {syn : List RR} (h : wildcardSynth z qname qt qcls = some syn) :
    nameKnown z qname = false := by
  unfold wildcardSynth at h
  split at h
  · exact absurd h (by simp)
  · simp_all
rfc_proves VeriDNS.Spec.Net.wildcardSynth_some_not_known [1034][1404:1414]

theorem wildcardSynth_some_not_ent {z : Zone} {qname : Name} {qt : QType} {qcls : RRClass}
    {syn : List RR} (h : wildcardSynth z qname qt qcls = some syn) :
    isEmptyNonTerminal z qname = false := by
  cases he : isEmptyNonTerminal z qname with
  | false => rfl
  | true => exact absurd ((ent_imp_nameKnown he).symm.trans (wildcardSynth_some_not_known h))
              (by decide)
rfc_proves VeriDNS.Spec.Net.wildcardSynth_some_not_ent [1034][1404:1414]

theorem noData_branch_total {s : Server} (now : Time) (seen : List Name) (o : Bool) (q : Query) (z : Zone)
    (hz : bestZone s q.qname q.qclass = some z) (hd : bestDeleg z q.qname = none)
    (hh : recordsAt z q.qname = []) : ∃ tr r, ServerAnswers s now seen o q tr r := by
  cases hw : wildcardSynth z q.qname q.qtype q.qclass with
  | some syn =>
      exact ⟨_, _, ServerAnswers.wildcard q z syn hz hd hh (wildcardSynth_some_not_ent hw) hw⟩
  | none =>
      cases hent : isEmptyNonTerminal z q.qname with
      | true => exact ⟨_, _, ServerAnswers.noData q z _ hz hd hh (Or.inl rfl) rfl hw (Or.inr hent)⟩
      | false => cases o with
        | true => exact ⟨_, _, ServerAnswers.nameError q z hz hd hh hw hent⟩
        | false => exact ⟨_, _, ServerAnswers.exitFollowed q z hz hd hh hw hent⟩
rfc_proves VeriDNS.Spec.Net.noData_branch_total [1034][1336:1351]

theorem step4_total {s : Server} (now : Time) (seen : List Name) (o : Bool) (q : Query)
    (hz : bestZone s q.qname q.qclass = none) : ∃ tr r, ServerAnswers s now seen o q tr r := by
  by_cases hmiss : (s.cache.filter (fun e => e.fresh now && nameEq e.rr.owner q.qname
        && q.qtype.covers e.rr.rdata.rtype && e.rr.cls == q.qclass)).map (·.aged now) = []
  · by_cases hdeleg : cachedDelegation s now q.qname q.qclass = []
    · exact ⟨_, _, ServerAnswers.cacheMiss q hz hmiss hdeleg⟩
    · exact ⟨_, _, ServerAnswers.fromCache q _ hz rfl (Or.inr hdeleg)⟩
  · exact ⟨_, _, ServerAnswers.fromCache q _ hz rfl (Or.inl hmiss)⟩
rfc_proves VeriDNS.Spec.Net.step4_total [1034][1354:1364]

theorem ServerAnswers_det {s : Server} {now : Time} {seen : List Name} {o : Bool} {q : Query} :
    ∀ {tr1 r1 tr2 r2}, ServerAnswers s now seen o q tr1 r1 → ServerAnswers s now seen o q tr2 r2 →
      tr1 = tr2 ∧ r1 = r2 := by
  intro tr1 r1 tr2 r2 h1
  induction h1 generalizing tr2 r2 with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih =>
      intro h2
      cases h2 with
      | cname _ z2 c2 target2 tr2' rest2 hz2 hd2 hc2 hcov2 ht2 hfresh2 hrec2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          obtain rfl : c = c2 := by simpa using hc.symm.trans hc2
          obtain rfl : target = target2 := by simpa using ht.symm.trans ht2
          obtain ⟨rfl, rfl⟩ := ih hrec2
          exact ⟨rfl, rfl⟩
      | answer _ z2 here2 hz2 hd2 hh2 hnc2 hmatch2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          rcases hnc2 with hnc2 | hnc2 <;> simp_all [cnameRR]
      | noData _ z2 here2 hz2 hd2 hh2 hnc2 hempty2 hw2 hexists2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          rcases hnc2 with hnc2 | hnc2 <;> simp_all [cnameRR]
      | _ => simp_all [cnameRR]
  | answer q z here hz hd hh hnc hmatch =>
      intro h2
      cases h2 with
      | cname _ z2 c2 target2 tr2' rest2 hz2 hd2 hc2 hcov2 ht2 hfresh2 hrec2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          rcases hnc with hnc | hnc <;> simp_all [cnameRR]
      | noData _ z2 here2 hz2 hd2 hh2 hnc2 hempty2 hw2 hexists2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          obtain rfl : here = here2 := hh.symm.trans hh2
          exact absurd hempty2 hmatch
      | _ => simp_all [cnameRR]
  | noData q z here hz hd hh hnc hempty hw hexists =>
      intro h2
      cases h2 with
      | cname _ z2 c2 target2 tr2' rest2 hz2 hd2 hc2 hcov2 ht2 hfresh2 hrec2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          rcases hnc with hnc | hnc <;> simp_all [cnameRR]
      | answer _ z2 here2 hz2 hd2 hh2 hnc2 hmatch2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          obtain rfl : here = here2 := hh.symm.trans hh2
          exact absurd hempty hmatch2
      | _ => rcases hexists with hex | hex <;> simp_all [cnameRR]
  | nameError q z hz hd hh hw hent =>
      intro h2
      cases h2 with
      | noData _ z2 here2 hz2 hd2 hh2 hnc2 hempty2 hw2 hexists2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          rcases hexists2 with hex | hex <;> simp_all [cnameRR]
      | _ => simp_all [cnameRR]
  | exitFollowed q z hz hd hh hw hent =>
      intro h2
      cases h2 with
      | noData _ z2 here2 hz2 hd2 hh2 hnc2 hempty2 hw2 hexists2 =>
          obtain rfl : z = z2 := by simpa using hz.symm.trans hz2
          rcases hexists2 with hex | hex <;> simp_all [cnameRR]
      | _ => simp_all [cnameRR]
  | _ => intro h2; cases h2 <;> simp_all [cnameRR]
rfc_proves VeriDNS.Spec.Net.ServerAnswers_det [1034][1289:1366]

theorem serverAnswers_rd_irrelevant {s : Server} {now : Time} (b : Bool)
    {seen : List Name} {o : Bool} {q : Query} {tr : List Step} {resp : Response}
    (h : ServerAnswers s now seen o q tr resp) :
    ServerAnswers s now seen o {q with rd := b} tr resp := by
  induction h with
  | answer q z here hz hd hh hnc hmatch => exact ServerAnswers.answer _ z here hz hd hh hnc hmatch
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih =>
      exact ServerAnswers.cname _ z c target tr rest hz hd hc hcov ht hfresh ih
  | referral q z d hz hd hca => exact ServerAnswers.referral _ z d hz hd hca
  | referralCacheAnswer q z d here hz hd hca hne =>
      exact ServerAnswers.referralCacheAnswer _ z d here hz hd hca hne
  | wildcard q z syn hz hd hh hent hw => exact ServerAnswers.wildcard _ z syn hz hd hh hent hw
  | nameError q z hz hd hh hw hent => exact ServerAnswers.nameError _ z hz hd hh hw hent
  | noData q z here hz hd hh hnc hempty hw hexists =>
      exact ServerAnswers.noData _ z here hz hd hh hnc hempty hw hexists
  | exitFollowed q z hz hd hh hw hent => exact ServerAnswers.exitFollowed _ z hz hd hh hw hent
  | fromCache q here hz hh hne => exact ServerAnswers.fromCache _ here hz hh hne
  | cacheMiss q hz hmiss hnodeleg => exact ServerAnswers.cacheMiss _ hz hmiss hnodeleg
rfc_proves VeriDNS.Spec.Net.serverAnswers_rd_irrelevant [1034][1289:1366]

theorem serverAnswers_ra_eq_capability {s : Server} {now : Time} {seen : List Name} {o : Bool}
    {q : Query} {tr : List Step} {resp : Response} (h : ServerAnswers s now seen o q tr resp) :
    resp.ra = s.recursionAvailable := by
  induction h with
  | cname q z c target tr rest hz hd hc hcov ht hfresh hrec ih => exact ih
  | _ => rfl
rfc_proves VeriDNS.Spec.Net.serverAnswers_ra_eq_capability [1034][1185:1192]

theorem serverAnswers_plain_clears_ra {s : Server} {now : Time} {seen : List Name} {o : Bool}
    {q : Query} {tr : List Step} {resp : Response}
    (hcap : s.recursionAvailable = false) (h : ServerAnswers s now seen o q tr resp) :
    resp.ra = false := (serverAnswers_ra_eq_capability h).trans hcap
rfc_proves VeriDNS.Spec.Net.serverAnswers_plain_clears_ra [1034][1185:1192]

theorem soaOf_find_head {z : Zone} {soa : RR} (h : soaOf z = some soa) (rest : List RR) :
    ((soaOf z).toList ++ rest).find? (fun rr => rr.rdata.rtype == RRType.soa) = some soa := by
  have hpred := List.find?_some h
  simp only [Bool.and_eq_true] at hpred
  simp only [h, Option.toList, List.cons_append, List.find?_cons, hpred.1]

theorem noDataAuthority_negTTL {z : Zone} {soa : RR} (h : soaOf z = some soa) :
    (Response.mk true RCode.noError [] (noDataAuthority z) [] false false).negTTL = negTTL z := by
  unfold Response.negTTL Response.negSOA noDataAuthority negTTL
  rw [soaOf_find_head h (if z.negCacheNS then apexNS z else []), h]

theorem nameError_negTTL {z : Zone} {soa : RR} (h : soaOf z = some soa) :
    (Response.mk true RCode.nameError [] (nxdomainAuthority z) [] false false).negTTL = negTTL z := by
  unfold Response.negTTL Response.negSOA nxdomainAuthority negTTL
  rw [soaOf_find_head h (if z.negCacheNS then apexNS z else []), h]

theorem noDataAuthority_contains_soa {z : Zone} {soa : RR} (h : soaOf z = some soa) :
    soa ∈ noDataAuthority z := by
  unfold noDataAuthority; rw [h]; simp [Option.toList]

theorem nxdomainAuthority_contains_soa {z : Zone} {soa : RR} (h : soaOf z = some soa) :
    soa ∈ nxdomainAuthority z := by
  unfold nxdomainAuthority; rw [h]; simp [Option.toList]

theorem serverAnswers_nameError_authority {s : Server} {now : Time} {seen : List Name}
    {o : Bool} {q : Query} {tr : List Step} {resp : Response}
    (hd : ServerAnswers s now seen o q tr resp) (hrc : resp.rcode = RCode.nameError) :
    ∃ z, resp.authority = nxdomainAuthority z := by
  revert hrc
  induction hd with
  | cname _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact fun hrc => ih hrc
  | nameError _ z _ _ _ _ _ => exact fun _ => ⟨z, rfl⟩
  | _ => exact fun hrc => by simp at hrc

theorem serverAnswers_nameError_carries_soa {s : Server} {now : Time} {seen : List Name}
    {o : Bool} {q : Query} {tr : List Step} {resp : Response}
    (hd : ServerAnswers s now seen o q tr resp) (hrc : resp.rcode = RCode.nameError)
    (hsoa : ∀ z, resp.authority = nxdomainAuthority z → (soaOf z).isSome) :
    ∃ soa, soa ∈ resp.authority := by
  obtain ⟨z, hz⟩ := serverAnswers_nameError_authority hd hrc
  obtain ⟨soa, hsome⟩ := Option.isSome_iff_exists.mp (hsoa z hz)
  exact ⟨soa, hz ▸ nxdomainAuthority_contains_soa hsome⟩

rfc_proves VeriDNS.Spec.Net.noDataAuthority_contains_soa [2308][404:412]
rfc_proves VeriDNS.Spec.Net.nxdomainAuthority_contains_soa [2308][404:412]
rfc_proves VeriDNS.Spec.Net.serverAnswers_nameError_authority [2308][404:412]
rfc_proves VeriDNS.Spec.Net.serverAnswers_nameError_carries_soa [2308][404:412]

theorem negTTLof_eq_soaMinimum {soa : RR} {m : Nat}
    (h : soa.rdata.soaMinimum = some m) : negTTLof soa = some (min m soa.ttl) := by
  unfold negTTLof; rw [h]; rfl
rfc_proves VeriDNS.Spec.Net.negTTLof_eq_soaMinimum [2308][420:462]

def cacheable (r : RR) : Bool := Nat.blt 0 r.ttl
rfc_proves VeriDNS.Spec.Net.cacheable [1034][704:708]

def ageCache (now : Time) (es : List CacheEntry) : List RR :=
  (es.filter (·.fresh now)).map (fun e => { e.rr with ttl := e.agedTTL now })
rfc_proves VeriDNS.Spec.Net.ageCache [1034][2247:2253]

inductive Status where
  | up
  | down
  deriving BEq, Inhabited
rfc_proves VeriDNS.Spec.Net.Status [1034][1012:1018]

structure NetState where
  status : Name → Status
rfc_proves VeriDNS.Spec.Net.NetState [1034][1012:1018]

def NetState.isUp (ns : NetState) (sname : Name) : Bool := ns.status sname == Status.up
rfc_proves VeriDNS.Spec.Net.NetState.isUp [1034][1012:1018]

def serversForApex (net : Network) (apex : Name) : List Name :=
  (net.servers.filter (fun s => s.zones.any (fun z => nameEq z.apex apex))).map (·.name)
rfc_proves VeriDNS.Spec.Net.serversForApex [1034][1012:1018]

def zoneAvailable (net : Network) (ns : NetState) (apex : Name) : Bool :=
  (serversForApex net apex).any (fun n => ns.isUp n)
rfc_proves VeriDNS.Spec.Net.zoneAvailable [1034][1012:1018]

inductive ServerFailover (net : Network) (ns : NetState) (now : Time) : List Name → Query → Response → Prop where

  | here (sname : Name) (rest : List Name) (q : Query) (srv : Server)
      (tr : List Step) (resp : Response)
      (hfind : net.servers.find? (fun s => nameEq s.name sname) = some srv)
      (hup : ns.isUp sname = true)
      (hans : ServerAnswers srv now [] true q tr resp) :
      ServerFailover net ns now (sname :: rest) q resp

  | skipDown (sname : Name) (rest : List Name) (q : Query) (resp : Response)
      (hup : ns.isUp sname = false)
      (hrec : ServerFailover net ns now rest q resp) :
      ServerFailover net ns now (sname :: rest) q resp

  | skipMissing (sname : Name) (rest : List Name) (q : Query) (resp : Response)
      (hfind : net.servers.find? (fun s => nameEq s.name sname) = none)
      (hrec : ServerFailover net ns now rest q resp) :
      ServerFailover net ns now (sname :: rest) q resp
rfc_proves VeriDNS.Spec.Net.ServerFailover [1034][1940:1948]

inductive TreeEvolution {R : Type} : Node R → Node R → Prop where
  | changeData (l : ByteArray) (rs rs' : Array R) (cs : Array (Node R)) :
      TreeEvolution (Node.mk l rs cs) (Node.mk l rs' cs)
  | growSection (l : ByteArray) (rs : Array R) (cs : Array (Node R)) (new : Node R) :
      TreeEvolution (Node.mk l rs cs) (Node.mk l rs (cs.push new))
  | deleteNodes (l : ByteArray) (rs : Array R) (cs cs' : Array (Node R)) :
      (∀ x, x ∈ cs' → x ∈ cs) → TreeEvolution (Node.mk l rs cs) (Node.mk l rs cs')
rfc_proves VeriDNS.Spec.Net.TreeEvolution [1034][1065:1073]

theorem TreeEvolution.preserves_label {R : Type} {t t' : Node R}
    (h : TreeEvolution t t') : t.label = t'.label := by
  cases h <;> rfl
rfc_proves VeriDNS.Spec.Net.TreeEvolution.preserves_label [1034][1065:1073]

def Network.addServer (net : Network) (s : Server) : Network := ⟨s :: net.servers⟩
rfc_proves VeriDNS.Spec.Net.Network.addServer [1034][1140:1166]

def Network.modifyServer (net : Network) (i : Nat) (f : Server → Server) : Network :=
  { net with servers := net.servers.set i (f (net.servers.getD i default)) }
rfc_proves VeriDNS.Spec.Net.Network.modifyServer [1034][1140:1166]

def Server.growZoneAt (s : Server) (j : Nat) (r : RR) : Server :=
  let z := s.zones.getD j default
  { s with zones := s.zones.set j { z with records := r :: z.records } }
rfc_proves VeriDNS.Spec.Net.Server.growZoneAt [1034][1065:1073]

def Server.delegateAt (s : Server) (j : Nat) (d : Delegation) : Server :=
  let z := s.zones.getD j default
  { s with zones := s.zones.set j { z with delegations := d :: z.delegations } }
rfc_proves VeriDNS.Spec.Net.Server.delegateAt [1034][1140:1166]

inductive NetworkEvolution : Network → Network → Prop where
  | addServer (net : Network) (s : Server) :
      NetworkEvolution net (net.addServer s)
  | growZone (net : Network) (i j : Nat) (r : RR) :
      NetworkEvolution net (net.modifyServer i (·.growZoneAt j r))

  | delegate (net : Network) (i j : Nat) (d : Delegation) (s : Server) :
      NetworkEvolution net ((net.modifyServer i (·.delegateAt j d)).addServer s)
rfc_proves VeriDNS.Spec.Net.NetworkEvolution [1034][1140:1166]

theorem NetworkEvolution.servers_monotone {net net' : Network}
    (h : NetworkEvolution net net') : net.servers.length ≤ net'.servers.length := by
  cases h with
  | addServer => simp [Network.addServer]
  | growZone => simp [Network.modifyServer]
  | delegate => simp [Network.addServer, Network.modifyServer]
rfc_proves VeriDNS.Spec.Net.NetworkEvolution.servers_monotone [1034][1140:1166]

theorem AuthoritativeFor.mono_addServer {net : Network} {qcls : RRClass} {a b : Name} {s : Server}
    (h : AuthoritativeFor net qcls a b) : AuthoritativeFor (net.addServer s) qcls a b := by
  cases h with
  | mk srv z hmem hnm hbz hbd =>
    exact AuthoritativeFor.mk a b srv z (List.mem_cons_of_mem _ hmem) hnm hbz hbd
rfc_proves VeriDNS.Spec.Net.AuthoritativeFor.mono_addServer [1034][1140:1166]

theorem DelegatesTo.mono_addServer {net : Network} {qcls : RRClass} {a b c : Name} {s : Server}
    (h : DelegatesTo net qcls a b c) : DelegatesTo (net.addServer s) qcls a b c := by
  cases h with
  | mk srv z d hmem hnm hbz hmemd hsub =>
    exact DelegatesTo.mk a b srv z d (List.mem_cons_of_mem _ hmem) hnm hbz hmemd hsub
rfc_proves VeriDNS.Spec.Net.DelegatesTo.mono_addServer [1034][1140:1166]

structure ZoneVersion where
  apex : Name
  serial : Nat
  records : List RR
  deriving Inhabited
rfc_proves VeriDNS.Spec.Net.ZoneVersion [1034][1530:1543]

def serialMod : Nat := 4294967296
rfc_proves VeriDNS.Spec.Net.serialMod [1034][1534:1539]

def serialHalf : Nat := 2147483648
rfc_proves VeriDNS.Spec.Net.serialHalf [1034][1534:1539]

def serialLt (s1 s2 : Nat) : Bool :=
  let a := s1 % serialMod
  let b := s2 % serialMod
  (Nat.blt a b && Nat.blt (b - a) serialHalf) || (Nat.blt b a && Nat.blt serialHalf (a - b))
rfc_proves VeriDNS.Spec.Net.serialLt [1034][1534:1539]

def ZoneVersion.moreRecent (a b : ZoneVersion) : Bool := serialLt b.serial a.serial
rfc_proves VeriDNS.Spec.Net.ZoneVersion.moreRecent [1034][1534:1539]

def changeAdvancesSerial (before after : ZoneVersion) : Prop :=
  before.records ≠ after.records → serialLt before.serial after.serial = true
rfc_proves VeriDNS.Spec.Net.changeAdvancesSerial [1034][1530:1534]

theorem change_detected {before after : ZoneVersion}
    (hadv : changeAdvancesSerial before after)
    (hchg : before.records ≠ after.records) :
    after.moreRecent before = true := by
  simpa [ZoneVersion.moreRecent] using hadv hchg
rfc_proves VeriDNS.Spec.Net.change_detected [1034][1530:1543]

theorem unchanged_serial_no_change {before after : ZoneVersion}
    (hadv : changeAdvancesSerial before after)
    (hstale : serialLt before.serial after.serial = false) :
    before.records = after.records := by
  by_contra hne
  have h := hadv hne
  rw [h] at hstale
  exact absurd hstale (by decide)
rfc_proves VeriDNS.Spec.Net.unchanged_serial_no_change [1034][1530:1543]

theorem serial_wraps_around :
    serialLt (serialMod - 1) 0 = true ∧ serialLt 0 (serialMod - 1) = false := by
  refine ⟨by decide, by decide⟩
rfc_proves VeriDNS.Spec.Net.serial_wraps_around [1034][1530:1543]

theorem bytesEqCI_refl (l : List UInt8) : bytesEqCI l l = true := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [bytesEqCI, ih]

theorem labelEq_refl (a : ByteArray) : labelEq a a = true := bytesEqCI_refl _

theorem bytesEqCI_symm : ∀ (a b : List UInt8), bytesEqCI a b = bytesEqCI b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [bytesEqCI]
      rw [bytesEqCI_symm xs ys, Bool.beq_comm (a := foldByte x) (b := foldByte y)]

theorem bytesEqCI_trans : ∀ {a b c : List UInt8},
    bytesEqCI a b = true → bytesEqCI b c = true → bytesEqCI a c = true
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, hbc => by simp [bytesEqCI] at hbc
  | [], _ :: _, _, hab, _ => by simp [bytesEqCI] at hab
  | _ :: _, [], _, hab, _ => by simp [bytesEqCI] at hab
  | _ :: _, _ :: _, [], _, hbc => by simp [bytesEqCI] at hbc
  | x :: xs, y :: ys, z :: zs, hab, hbc => by
      simp only [bytesEqCI, Bool.and_eq_true] at hab hbc ⊢
      refine ⟨?_, bytesEqCI_trans hab.2 hbc.2⟩
      rw [eq_of_beq hab.1, eq_of_beq hbc.1]
      exact beq_self_eq_true _

theorem labelEq_symm (a b : ByteArray) : labelEq a b = labelEq b a := bytesEqCI_symm _ _
theorem labelEq_trans {a b c : ByteArray} (h1 : labelEq a b = true) (h2 : labelEq b c = true) :
    labelEq a c = true := bytesEqCI_trans h1 h2

theorem nameEq_refl (n : Name) : nameEq n n = true := by
  induction n with
  | nil => rfl
  | cons x xs ih => simp [nameEq, labelEq_refl, ih]

theorem nameEqCS_refl (n : Name) : nameEqCS n n = true := by
  induction n with
  | nil => rfl
  | cons x xs ih =>
    have hx : (x == x) = true := by
      show ByteArray.beq x x = true
      unfold ByteArray.beq
      simp
    simp [nameEqCS, hx, ih]

theorem labelEq_of_beq {a b : ByteArray} (h : (a == b) = true) :
    labelEq a b = true := by
  have hab : a = b := by
    apply ByteArray.ext
    show a.data = b.data
    have h' : ByteArray.beq a b = true := h
    unfold ByteArray.beq at h'
    simpa using h'
  subst hab
  exact labelEq_refl a

theorem nameEq_of_nameEqCS : ∀ {a b : Name}, nameEqCS a b = true → nameEq a b = true
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [nameEqCS, Bool.and_eq_true] at h
      simp only [nameEq, Bool.and_eq_true]
      exact ⟨labelEq_of_beq h.1, nameEq_of_nameEqCS h.2⟩

theorem nameEq_symm : ∀ (a b : Name), nameEq a b = nameEq b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [nameEq, labelEq_symm x y, nameEq_symm xs ys]

theorem nameEq_trans : ∀ {a b c : Name}, nameEq a b = true → nameEq b c = true → nameEq a c = true
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h => by simp [nameEq] at h
  | [], _ :: _, _, h, _ => by simp [nameEq] at h
  | _ :: _, [], _, h, _ => by simp [nameEq] at h
  | _ :: _, _ :: _, [], _, h => by simp [nameEq] at h
  | x :: xs, y :: ys, z :: zs, hab, hbc => by
      simp only [nameEq, Bool.and_eq_true] at hab hbc ⊢
      exact ⟨labelEq_trans hab.1 hbc.1, nameEq_trans hab.2 hbc.2⟩

theorem isAncestor_refl (n : Name) : isAncestor n n = true := by
  simp [isAncestor, Nat.sub_self, nameEq_refl]

theorem cnameRR_congr {qn qn' : Name} (h : nameEq qn qn' = true) (recs : List RR) :
    cnameRR qn recs = cnameRR qn' recs := by
  unfold cnameRR
  have hpt : ∀ o, nameEq o qn = nameEq o qn' := by
    intro o
    cases ho : nameEq o qn with
    | true => exact (nameEq_trans ho h).symm
    | false =>
      cases ho' : nameEq o qn' with
      | false => rfl
      | true =>
        have : nameEq o qn = true := nameEq_trans ho' (by rw [nameEq_symm]; exact h)
        rw [this] at ho; exact ho.symm
  have : (fun r : RR => r.rdata.rtype == RRType.cname && nameEq r.owner qn)
      = (fun r : RR => r.rdata.rtype == RRType.cname && nameEq r.owner qn') := by
    funext r; rw [hpt r.owner]
  rw [this]

theorem nameEq_length : ∀ {a b : Name}, nameEq a b = true → a.length = b.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [nameEq] at h
  | _ :: _, [], h => by simp [nameEq] at h
  | _ :: xs, _ :: ys, h => by
      simp only [nameEq, Bool.and_eq_true] at h
      simp [List.length_cons, nameEq_length h.2]

theorem nameEq_drop : ∀ (k : Nat) {a b : Name}, nameEq a b = true →
    nameEq (a.drop k) (b.drop k) = true
  | 0, _, _, h => h
  | _ + 1, [], [], h => h
  | _ + 1, [], _ :: _, h => by simp [nameEq] at h
  | _ + 1, _ :: _, [], h => by simp [nameEq] at h
  | k + 1, _ :: xs, _ :: ys, h => by
      simp only [nameEq, Bool.and_eq_true] at h
      simpa only [List.drop_succ_cons] using nameEq_drop k h.2

theorem isAncestor_of_nameEq {a b : Name} (h : nameEq a b = true) : isAncestor b a = true := by
  have hl : a.length = b.length := nameEq_length h
  unfold isAncestor
  rw [← hl, Nat.sub_self, List.drop_zero, Nat.ble_self_eq_true, cond_true, nameEq_symm]
  exact h

theorem isAncestor_trans {a b c : Name}
    (hab : isAncestor a b = true) (hbc : isAncestor b c = true) : isAncestor a c = true := by
  unfold isAncestor at hab hbc ⊢
  cases hg1 : Nat.ble a.length b.length with
  | false => rw [hg1] at hab; simp at hab
  | true =>
    cases hg2 : Nat.ble b.length c.length with
    | false => rw [hg2] at hbc; simp at hbc
    | true =>
      rw [hg1, cond_true] at hab
      rw [hg2, cond_true] at hbc
      have hab_len := Nat.le_of_ble_eq_true hg1
      have hbc_len := Nat.le_of_ble_eq_true hg2
      rw [Nat.ble_eq_true_of_le (Nat.le_trans hab_len hbc_len), cond_true]
      have hdrop := nameEq_drop (b.length - a.length) hbc
      rw [List.drop_drop] at hdrop
      have harith : c.length - b.length + (b.length - a.length) = c.length - a.length := by omega
      rw [harith] at hdrop
      exact nameEq_trans hab hdrop

theorem isAncestor_congr_left {a b n : Name} (h : isAncestor a n = true) (hba : nameEq b a = true) :
    isAncestor b n = true := by
  unfold isAncestor at h ⊢
  rw [nameEq_length hba]
  by_cases hb : Nat.ble a.length n.length = true
  · rw [hb, cond_true] at h ⊢
    exact nameEq_trans hba h
  · rw [Bool.not_eq_true] at hb; rw [hb, cond_false] at h; exact absurd h (by simp)

theorem isAncestor_congr_right {a b c : Name} (h : isAncestor a b = true) (hbc : nameEq b c = true) :
    isAncestor a c = true := by
  unfold isAncestor at h ⊢
  rw [← nameEq_length hbc]
  by_cases ha : Nat.ble a.length b.length = true
  · rw [ha, cond_true] at h ⊢
    exact nameEq_trans h (nameEq_drop (b.length - a.length) hbc)
  · rw [Bool.not_eq_true] at ha; rw [ha, cond_false] at h; exact absurd h (by simp)

theorem isAncestor_length_le {a b : Name} (h : isAncestor a b = true) : a.length ≤ b.length := by
  unfold isAncestor at h
  by_cases hb : Nat.ble a.length b.length = true
  · exact Nat.le_of_ble_eq_true hb
  · rw [Bool.not_eq_true] at hb; rw [hb, cond_false] at h; exact absurd h (by simp)

theorem isAncestor_drop_ancestor {n : Name} {k : Nat} (hk : k ≤ n.length) :
    isAncestor (n.drop (n.length - k)) n = true ∧ (n.drop (n.length - k)).length = k := by
  have hlen : (n.drop (n.length - k)).length = k := by
    rw [List.length_drop]; omega
  refine ⟨?_, hlen⟩
  unfold isAncestor
  rw [hlen, Nat.ble_eq_true_of_le hk, cond_true]
  exact nameEq_refl _

theorem isAncestor_eq_length_nameEq {a b : Name} (h : isAncestor a b = true)
    (hlen : a.length = b.length) : nameEq a b = true := by
  unfold isAncestor at h
  rw [Nat.ble_eq_true_of_le (Nat.le_of_eq hlen), cond_true] at h
  rwa [hlen, Nat.sub_self, List.drop_zero] at h

structure System where
  tree : Node Unit
  net : Network

inductive CoEvolves : System → System → Prop where
  | grow (l : ByteArray) (rs : Array Unit) (cs : Array (Node Unit)) (new : Node Unit)
      (net : Network) (i j : Nat) (r : RR) :
      CoEvolves ⟨Node.mk l rs cs, net⟩
                ⟨Node.mk l rs (cs.push new), net.modifyServer i (·.growZoneAt j r)⟩
  | change (l : ByteArray) (rs rs' : Array Unit) (cs : Array (Node Unit))
      (net : Network) (i j : Nat) (r : RR) :
      CoEvolves ⟨Node.mk l rs cs, net⟩
                ⟨Node.mk l rs' cs, net.modifyServer i (·.growZoneAt j r)⟩
  | delegate (l : ByteArray) (rs : Array Unit) (cs : Array (Node Unit)) (sub : Node Unit)
      (net : Network) (i j : Nat) (d : Delegation) (s : Server) :
      CoEvolves ⟨Node.mk l rs cs, net⟩
                ⟨Node.mk l rs (cs.push sub), (net.modifyServer i (·.delegateAt j d)).addServer s⟩
rfc_proves VeriDNS.Spec.Net.CoEvolves [1034][1140:1166]

theorem CoEvolves.tree_step {sys sys' : System} (h : CoEvolves sys sys') :
    TreeEvolution sys.tree sys'.tree := by
  cases h with
  | grow => exact TreeEvolution.growSection _ _ _ _
  | change => exact TreeEvolution.changeData _ _ _ _
  | delegate => exact TreeEvolution.growSection _ _ _ _
rfc_proves VeriDNS.Spec.Net.CoEvolves.tree_step [1034][1065:1073]

theorem CoEvolves.net_step {sys sys' : System} (h : CoEvolves sys sys') :
    NetworkEvolution sys.net sys'.net := by
  cases h with
  | grow => exact NetworkEvolution.growZone _ _ _ _
  | change => exact NetworkEvolution.growZone _ _ _ _
  | delegate => exact NetworkEvolution.delegate _ _ _ _ _
rfc_proves VeriDNS.Spec.Net.CoEvolves.net_step [1034][1140:1166]

theorem CoEvolves.preserves {sys sys' : System} (h : CoEvolves sys sys') :
    sys.tree.label = sys'.tree.label ∧ sys.net.servers.length ≤ sys'.net.servers.length :=
  ⟨TreeEvolution.preserves_label h.tree_step, NetworkEvolution.servers_monotone h.net_step⟩
rfc_proves VeriDNS.Spec.Net.CoEvolves.preserves [1034][1065:1073]

theorem CoEvolves.delegate_creates_authority
    (net : Network) (i j : Nat) (d : Delegation) (s : Server) (zsub : Zone)
    (hbz : bestZone s zsub.apex zsub.cls = some zsub) (hdel : zsub.delegations = []) :
    AuthoritativeFor ((net.modifyServer i (·.delegateAt j d)).addServer s) zsub.cls s.name zsub.apex :=
  AuthoritativeFor.mk s.name zsub.apex s zsub
    List.mem_cons_self (nameEq_refl _) hbz (by simp [bestDeleg, hdel])
rfc_proves VeriDNS.Spec.Net.CoEvolves.delegate_creates_authority [1034][1140:1166]

mutual

def childInsert : List (Node RR) → ByteArray → List ByteArray → RR → List (Node RR)
  | [], l, rest, r => [Node.insertRR (Node.mk l #[] #[]) rest r]
  | c :: cs, l, rest, r =>
      match labelEq c.label l with
      | true => Node.insertRR c rest r :: cs
      | false => c :: childInsert cs l rest r

def Node.insertRR : Node RR → List ByteArray → RR → Node RR
  | Node.mk lab rs cs, [], r => Node.mk lab (rs.push r) cs
  | Node.mk lab rs cs, l :: rest, r => Node.mk lab rs (childInsert cs.toList l rest r).toArray
end

def treeOf (z : Zone) : Node RR :=
  z.records.foldl (fun t r => Node.insertRR t r.owner.reverse r) (Node.mk (L "") #[] #[])

def dRecs (t : Node RR) (path : List ByteArray) : List RR :=
  (Node.descend t path).elim [] (fun n => n.resourceSet.toList)

def treeRecordsAt (t : Node RR) (qname : Name) : List RR := dRecs t qname.reverse

theorem Node.label_mk (l : ByteArray) (rs : Array RR) (cs : Array (Node RR)) :
    (Node.mk l rs cs).label = l := rfl
theorem Node.resourceSet_mk (l : ByteArray) (rs : Array RR) (cs : Array (Node RR)) :
    (Node.mk l rs cs).resourceSet = rs := rfl
theorem Node.children_mk (l : ByteArray) (rs : Array RR) (cs : Array (Node RR)) :
    (Node.mk l rs cs).children = cs := rfl

theorem insertRR_label (t : Node RR) (path : List ByteArray) (r : RR) :
    (Node.insertRR t path r).label = t.label := by
  cases t with | mk lab rs cs => cases path <;> simp [Node.insertRR, Node.label_mk]

theorem dRecs_nil (lab : ByteArray) (rs : Array RR) (cs : Array (Node RR)) :
    dRecs (Node.mk lab rs cs) [] = rs.toList := rfl

theorem dRecs_cons (lab : ByteArray) (rs : Array RR) (cs : Array (Node RR))
    (q : ByteArray) (qrest : List ByteArray) :
    dRecs (Node.mk lab rs cs) (q :: qrest)
      = (cs.toList.find? (fun c => labelEq c.label q)).elim [] (fun c => dRecs c qrest) := by
  simp only [dRecs, Node.descend, Node.children_mk, ← Array.find?_toList]
  cases cs.toList.find? (fun c => labelEq c.label q) <;> rfl

theorem dRecs_empty (lab : ByteArray) : ∀ (path : List ByteArray),
    dRecs (Node.mk lab #[] #[]) path = []
  | [] => rfl
  | _ :: _ => rfl

theorem dRecs_insertRR : ∀ (ipath : List ByteArray) (t : Node RR) (qpath : List ByteArray) (r : RR),
    dRecs (Node.insertRR t ipath r) qpath
      = dRecs t qpath ++ (if nameEq ipath qpath then [r] else [])
  | [], t, qpath, r => by
      cases t with
      | mk lab rs cs =>
        cases qpath with
        | nil => simp [Node.insertRR, dRecs_nil, Array.toList_push, nameEq]
        | cons q qrest =>
            have hins : Node.insertRR (Node.mk lab rs cs) [] r
                = Node.mk lab (rs.push r) cs := by simp [Node.insertRR]
            simp only [hins, dRecs_cons, nameEq]
            cases cs.toList.find? (fun c => labelEq c.label q) <;> simp
  | il :: irest, t, qpath, r => by
      cases t with
      | mk lab rs cs =>
        have hins : Node.insertRR (Node.mk lab rs cs) (il :: irest) r
            = Node.mk lab rs (childInsert cs.toList il irest r).toArray := by simp [Node.insertRR]
        cases qpath with
        | nil => simp [hins, dRecs_nil, nameEq]
        | cons ql qrest =>
            simp only [hins, dRecs_cons, List.toList_toArray, nameEq]

            have key : ∀ (csL : List (Node RR)),
                ((childInsert csL il irest r).find? (fun c => labelEq c.label ql)).elim []
                    (fun c => dRecs c qrest)
                  = (csL.find? (fun c => labelEq c.label ql)).elim [] (fun c => dRecs c qrest)
                      ++ (if labelEq il ql && nameEq irest qrest then [r] else []) := by
              intro csL
              induction csL with
              | nil =>
                  simp only [childInsert, List.find?_cons, List.find?_nil, insertRR_label,
                    Node.label_mk]
                  cases h : labelEq il ql with
                  | true =>
                      simp only [h, Option.elim, Bool.true_and]
                      rw [dRecs_insertRR irest (Node.mk il #[] #[]) qrest r, dRecs_empty]
                  | false => simp [h]
              | cons c cs' ih =>
                  simp only [childInsert]
                  cases hcil : labelEq c.label il with
                  | true =>
                      simp only [List.find?_cons, insertRR_label]
                      cases hcql : labelEq c.label ql with
                      | true =>
                          have hilql : labelEq il ql = true :=
                            labelEq_trans (by rw [labelEq_symm]; exact hcil) hcql
                          simp only [hcql, Option.elim, hilql, Bool.true_and]
                          exact dRecs_insertRR irest c qrest r
                      | false =>
                          have hilql : labelEq il ql = false := by
                            cases hq : labelEq il ql with
                            | false => rfl
                            | true => simp [labelEq_trans hcil hq] at hcql
                          simp [hilql]
                  | false =>
                      simp only [List.find?_cons]
                      cases hcql : labelEq c.label ql with
                      | true =>
                          have hilql : labelEq il ql = false := by
                            cases hq : labelEq il ql with
                            | false => rfl
                            | true =>
                                have hci : labelEq c.label il = true :=
                                  labelEq_trans hcql (by rw [labelEq_symm]; exact hq)
                                simp [hci] at hcil
                          simp [hilql]
                      | false =>
                          simp only [hcql, Option.elim]
                          exact ih
            exact key cs.toList

theorem dRecs_foldl (recs : List RR) (t0 : Node RR) (qpath : List ByteArray) :
    dRecs (recs.foldl (fun t r => Node.insertRR t r.owner.reverse r) t0) qpath
      = dRecs t0 qpath ++ recs.filter (fun r => nameEq r.owner.reverse qpath) := by
  induction recs generalizing t0 with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl_cons, ih, dRecs_insertRR, List.filter_cons]
      by_cases h : nameEq r.owner.reverse qpath = true
      · simp [h, List.append_assoc]
      · simp [h]

theorem nameEq_concat : ∀ (a b : Name) (x y : ByteArray),
    nameEq (a ++ [x]) (b ++ [y]) = (nameEq a b && labelEq x y)
  | [], [], x, y => by simp [nameEq, Bool.and_comm]
  | [], _ :: _, x, y => by simp [nameEq]
  | _ :: _, [], x, y => by simp [nameEq]
  | a :: as, b :: bs, x, y => by
      simp only [List.cons_append, nameEq, nameEq_concat as bs x y, Bool.and_assoc]

theorem nameEq_reverse : ∀ (a b : Name), nameEq a.reverse b.reverse = nameEq a b
  | [], [] => rfl
  | [], _ :: _ => by simp [nameEq]
  | _ :: _, [] => by simp [nameEq]
  | a :: as, b :: bs => by
      simp only [List.reverse_cons, nameEq_concat, nameEq_reverse as bs, nameEq, Bool.and_comm]

theorem treeRecordsAt_treeOf (z : Zone) (qname : Name) :
    treeRecordsAt (treeOf z) qname = recordsAt z qname := by
  simp only [treeRecordsAt, treeOf, dRecs_foldl, dRecs_empty, List.nil_append, recordsAt]
  apply List.filter_congr
  intro r _
  rw [nameEq_reverse]

rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][431:448]
rfc_proves VeriDNS.Spec.Net.treeRecordsAt_treeOf [1034][449:454]

theorem answer_step_on_tree (s : Server) (now : Time) (seen : List Name) (o : Bool)
    (q : Query) (z : Zone)
    (hz : bestZone s q.qname q.qclass = some z) (hd : bestDeleg z q.qname = none)
    (hnc : cnameRR q.qname (treeRecordsAt (treeOf z) q.qname) = none ∨ q.qtype.covers RRType.cname = true)
    (hmatch : (treeRecordsAt (treeOf z) q.qname).filter
        (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass) ≠ []) :
    ServerAnswers s now seen o q
      [Step.findZone z.apex, Step.matchNode q.qname, Step.copyAnswer, Step.addAdditional]
      { aa := true, rcode := RCode.noError, ra := s.recursionAvailable,
        answer := (treeRecordsAt (treeOf z) q.qname).filter
          (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass),
        authority := [],
        additional := additionalFrom (z.records ++ freshServerCache s now)
          ((treeRecordsAt (treeOf z) q.qname).filter
          (fun r => q.qtype.covers r.rdata.rtype && r.cls == q.qclass)) } :=
  ServerAnswers.answer q z (treeRecordsAt (treeOf z) q.qname)
    hz hd (treeRecordsAt_treeOf z q.qname).symm hnc hmatch
rfc_proves VeriDNS.Spec.Net.answer_step_on_tree [1034][1300:1310]

theorem foldl_pick_mem {α : Type} {g : Option α → α → Option α} {l : List α} {r : α}
    (hnone : ∀ x, g none x = some x)
    (hsome : ∀ y x, g (some y) x = some y ∨ g (some y) x = some x)
    (h : l.foldl g none = some r) : r ∈ l := by
  have gen : ∀ (l : List α) (acc : Option α), l.foldl g acc = some r → r ∈ l ∨ acc = some r := by
    intro l
    induction l with
    | nil => intro acc h; exact Or.inr h
    | cons x xs ih =>
        intro acc h
        simp only [List.foldl_cons] at h
        rcases ih _ h with hm | hacc
        · exact Or.inl (List.mem_cons_of_mem _ hm)
        · cases acc with
          | none =>
              rw [hnone, Option.some.injEq] at hacc
              exact Or.inl (by rw [← hacc]; exact List.mem_cons_self)
          | some y =>
              rcases hsome y x with he | he
              · rw [he] at hacc; exact Or.inr hacc
              · rw [he, Option.some.injEq] at hacc
                exact Or.inl (by rw [← hacc]; exact List.mem_cons_self)
  rcases gen l none h with hm | hc
  · exact hm
  · exact absurd hc (by simp)

theorem foldl_pick_none {α : Type} {g : Option α → α → Option α} {l : List α}
    (hnone : ∀ x, g none x = some x)
    (hkeep : ∀ w x, ∃ v, g (some w) x = some v)
    (h : l.foldl g none = none) : l = [] := by
  have keep : ∀ (l : List α) (w : α), ∃ v, l.foldl g (some w) = some v := by
    intro l
    induction l with
    | nil => intro w; exact ⟨w, rfl⟩
    | cons x xs ih =>
        intro w; obtain ⟨v, hv⟩ := hkeep w x; rw [List.foldl_cons, hv]; exact ih v
  cases l with
  | nil => rfl
  | cons x xs =>
      rw [List.foldl_cons, hnone x] at h
      obtain ⟨v, hv⟩ := keep xs x
      rw [hv] at h; exact absurd h (by simp)

theorem bestZone_spec {s : Server} {qname : Name} {qcls : RRClass} {z : Zone}
    (h : bestZone s qname qcls = some z) :
    z ∈ s.zones ∧ isAncestor z.apex qname = true := by
  unfold bestZone at h
  have hmem := foldl_pick_mem
    (g := fun acc z => match acc with
      | none => some z | some z' => if z'.apex.length < z.apex.length then some z else some z')
    (l := s.zones.filter (fun z => z.cls == qcls && isAncestor z.apex qname))
    (fun _ => rfl)
    (fun y x => by dsimp only; by_cases hk : y.apex.length < x.apex.length <;> simp [hk]) h
  rw [List.mem_filter] at hmem
  obtain ⟨hz, hp⟩ := hmem
  rw [Bool.and_eq_true] at hp
  exact ⟨hz, hp.2⟩

theorem bestDeleg_none_all {z : Zone} {qname : Name} (h : bestDeleg z qname = none) :
    (z.delegations.all (fun d => ! isAncestor d.subapex qname)) = true := by
  unfold bestDeleg at h
  have hnil := foldl_pick_none
    (g := fun acc d => match acc with
      | none => some d | some d' => if d'.subapex.length < d.subapex.length then some d else some d')
    (l := z.delegations.filter (fun d => isAncestor d.subapex qname))
    (fun _ => rfl)
    (fun w x => by dsimp only; by_cases hk : w.subapex.length < x.subapex.length <;> simp [hk]) h
  rw [List.filter_eq_nil_iff] at hnil
  rw [List.all_eq_true]
  intro d hd
  have := hnil d hd
  simp only [Bool.not_eq_true] at this
  simp [this]

theorem serverAnswers_answer_authoritative {s : Server} {qname : Name} {qcls : RRClass} {z : Zone}
    (hz : bestZone s qname qcls = some z) (hd : bestDeleg z qname = none)
    {net : Network} (hmem : s ∈ net.servers) :
    AuthoritativeFor net qcls s.name qname :=
  AuthoritativeFor.mk s.name qname s z hmem (nameEq_refl _) hz hd
rfc_proves VeriDNS.Spec.Net.serverAnswers_answer_authoritative [1034][1300:1310]

end VeriDNS.Spec.Net
