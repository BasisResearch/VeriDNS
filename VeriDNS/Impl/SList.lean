import VeriDNS.Spec.Resolver
import VeriDNS.Impl.DomainName

namespace VeriDNS.Impl.SList

open VeriDNS.Spec
open VeriDNS.Impl.DomainName (nameEqCI foldNameCase)

structure DnsSList where
  servers : Array SlistEntry
  zone : ByteArray
  matchCount : Nat
  deriving Inhabited

def DnsSList.empty : DnsSList := ⟨#[], ByteArray.empty, 0⟩

def DnsSList.addServer (s : DnsSList) (entry : SlistEntry) : DnsSList :=
  { s with servers := s.servers.push entry }

def DnsSList.bestServer (s : DnsSList) : Option SlistEntry :=
  s.servers.foldl (init := none) fun best e =>
    match best with
    | none => some e
    | some b => if e.transmissionCount < b.transmissionCount then some e else some b

def DnsSList.removeServer (s : DnsSList) (name : ByteArray) : DnsSList :=
  { s with servers := s.servers.filter fun e => e.name != name }

instance : SlistSpec DnsSList SlistEntry where
  describeServers s _ns := s.servers
  describeZone s _ba := s.zone
  keepTrack s _ba := s.zone
  zoneName s _ba := s.zone

def DnsSList.mkSbelt (entries : Array (ByteArray × BitVec 32)) : DnsSList :=
  { servers := entries.map fun (name, addr) => ⟨name, some addr, 0⟩
    zone := ByteArray.empty
    matchCount := 0 }

def DnsSList.fromNsWithGlue (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) : DnsSList :=
  let servers := names.map fun n =>

    let addr := glue.findSome? fun (gn, ga) => if nameEqCI gn n then some ga else none
    ⟨n, addr, 0⟩
  { servers := servers, zone := ByteArray.empty, matchCount := mc }

/-- **All-addresses SLIST construction** (the credibility-aware, RFC-faithful form of `fromNsWithGlue`). A real
    resolver keeps and tries EVERY known address of a nameserver (RFC 1034 §5.3.3 SLIST holds all addresses per
    server), so each NS host contributes one server entry per in-bailiwick glue address — not just the first. A
    glueless host (no cached glue) still yields a single address-less entry, preserving the glueless re-resolution
    path. This matches the model `Cache.referralSlist` (`flatMap glueAddrsAt`, all-addresses) so `modelSlistOf`
    is a genuine permutation; `findSome?`-first (`fromNsWithGlue`) under-tries multi-homed nameservers and is
    not `MatchMaxEquiv`-stable. Glue is keyed by the EXACT NS host name (the case-insensitive glue-owner match
    already happened in the `lookupTopCred` cache read), so association is by `==`, NOT `nameEqCI` — a `nameEqCI`
    re-match here would re-scan the full glue per name and *quadratically over-count* case-variant NS names
    (each variant collecting every variant's addresses), diverging from the model's linear per-host count. -/
def DnsSList.fromNsWithGlueAll (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) : DnsSList :=
  let servers := names.flatMap fun n =>

    let addrs := glue.filterMap fun (gn, ga) => if foldNameCase gn == foldNameCase n then some ga else none
    if addrs.isEmpty then #[(⟨n, none, 0⟩ : SlistEntry)]
    else addrs.map fun ga => (⟨n, some ga, 0⟩ : SlistEntry)
  { servers := servers, zone := ByteArray.empty, matchCount := mc }

instance : SlistFromNameSpec DnsSList SlistEntry where
  copyNames names mc :=
    { servers := names.map fun n => ⟨n, none, 0⟩
      zone := ByteArray.empty
      matchCount := mc }
  setUpAddresses names glue mc := DnsSList.fromNsWithGlueAll names glue mc
  matchCount s := s.matchCount
  searchFails s := s.servers.isEmpty

def DnsSList.pickBest (best : Option (SlistEntry × BitVec 32)) (e : SlistEntry)
    : Option (SlistEntry × BitVec 32) :=
  match e.address with
  | none => best
  | some addr =>
    match best with
    | none => some (e, addr)
    | some (b, baddr) =>
      if e.transmissionCount < b.transmissionCount then some (e, addr) else some (b, baddr)

def DnsSList.bestWithAddress (s : DnsSList) : Option (SlistEntry × BitVec 32) :=
  s.servers.foldl DnsSList.pickBest none

def DnsSList.markQueried (s : DnsSList) (name : ByteArray) : DnsSList :=
  { s with servers := s.servers.map fun e =>
    if e.name == name then { e with transmissionCount := e.transmissionCount + 1 } else e }

def DnsSList.addressTargets (s : DnsSList) : Array ByteArray :=
  s.servers.filterMap fun e =>
    match e.address with
    | none => some e.name
    | some _ => none

def DnsSList.addAddress (s : DnsSList) (name : ByteArray) (addr : BitVec 32) : DnsSList :=
  { s with servers := s.servers.map fun e =>
    if e.name == name then { e with address := some addr } else e }

end VeriDNS.Impl.SList
