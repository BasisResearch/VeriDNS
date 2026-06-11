import VeriDNS.Spec.Resolver

namespace VeriDNS.Impl.SList

open VeriDNS.Spec

structure DnsSList where
  servers : Array SlistEntry
  zone : ByteArray
  matchCount : Nat
  deriving Inhabited

def DnsSList.empty : DnsSList := ⟨#[], ByteArray.empty, 0⟩

def DnsSList.addServer (s : DnsSList) (entry : SlistEntry) : DnsSList :=
  { s with servers := s.servers.push entry }

/-- Best server = least queries sent so far. -/
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

/-- Create SBELT from root server entries (name wire bytes, IPv4 address).
    Match count 0 = "no labels match" (RFC says -1, Nat can't represent). -/
def DnsSList.mkSbelt (entries : Array (ByteArray × BitVec 32)) : DnsSList :=
  { servers := entries.map fun (name, addr) => ⟨name, some addr, 0⟩
    zone := ByteArray.empty
    matchCount := 0 }

/-- Create SLIST from NS names with optional glue addresses.
    Used after delegation (4b) when additional section has A records. -/
def DnsSList.fromNsWithGlue (names : Array ByteArray)
    (glue : Array (ByteArray × BitVec 32)) (mc : Nat) : DnsSList :=
  let servers := names.map fun n =>
    let addr := glue.findSome? fun (gn, ga) => if gn == n then some ga else none
    ⟨n, addr, 0⟩
  { servers := servers, zone := ByteArray.empty, matchCount := mc }

instance : SlistFromNameSpec DnsSList SlistEntry where
  copyNames names mc :=
    { servers := names.map fun n => ⟨n, none, 0⟩
      zone := ByteArray.empty
      matchCount := mc }
  setUpAddresses names glue mc := DnsSList.fromNsWithGlue names glue mc
  matchCount s := s.matchCount
  searchFails s := s.servers.isEmpty

/-- Fold step for `bestWithAddress`: keep the less-queried addressed entry
    (ties keep the earlier one), pairing each entry with its OWN address. -/
def DnsSList.pickBest (best : Option (SlistEntry × BitVec 32)) (e : SlistEntry)
    : Option (SlistEntry × BitVec 32) :=
  match e.address with
  | none => best
  | some addr =>
    match best with
    | none => some (e, addr)
    | some (b, baddr) =>
      if e.transmissionCount < b.transmissionCount then some (e, addr) else some (b, baddr)

/-- Pick the best server that has an address: the least-queried one.
    RFC 1035 §7.2 "Each time an address is chosen and the state should be
    altered to prevent its selection again until all other addresses have
    been tried" — `markQueried` is the alteration, and least-queried-first
    selection is the prevention (proved as `slist_prevent_selection`
    instantiating the generated `sendingthequeries_prevent_selection`). -/
def DnsSList.bestWithAddress (s : DnsSList) : Option (SlistEntry × BitVec 32) :=
  s.servers.foldl DnsSList.pickBest none

/-- Mark a server as queried (increment transmissionCount). -/
def DnsSList.markQueried (s : DnsSList) (name : ByteArray) : DnsSList :=
  { s with servers := s.servers.map fun e =>
    if e.name == name then { e with transmissionCount := e.transmissionCount + 1 } else e }

/-- Names of servers whose addresses are not available. RFC 1034 §5.3.3
    step 2: "It may be the case that the addresses are not available" —
    address knowledge is partial (`SlistEntry.address : Option`). These names
    are the targets for glueless sub-resolution (the RFC's "looking for the
    addresses"); instantiates `lookAddresses` in the generated
    `recommendation_addressesAvailable`. -/
def DnsSList.addressTargets (s : DnsSList) : Array ByteArray :=
  s.servers.filterMap fun e =>
    match e.address with
    | none => some e.name
    | some _ => none

/-- Record a resolved address for a named server. -/
def DnsSList.addAddress (s : DnsSList) (name : ByteArray) (addr : BitVec 32) : DnsSList :=
  { s with servers := s.servers.map fun e =>
    if e.name == name then { e with address := some addr } else e }

end VeriDNS.Impl.SList
