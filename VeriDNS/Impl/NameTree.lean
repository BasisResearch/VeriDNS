import VeriDNS.Spec.NameTree
import VeriDNS.Spec.Resolver
import VeriDNS.Spec.Message
import VeriDNS.Impl.DomainName

namespace VeriDNS.Impl.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.DomainName (foldNameCase wireFormatToLabels)

def labelEqCI (a b : ByteArray) : Bool :=
  foldNameCase a == foldNameCase b

variable {RR : Type}

def findChild (n : Node RR) (lab : ByteArray) : Option (Node RR) :=
  n.children.find? (fun c => labelEqCI c.label lab)

def nodeAt (root : Node RR) : List ByteArray → Option (Node RR)
  | [] => some root
  | l :: rest =>
    match findChild root l with
    | some c => nodeAt c rest
    | none => none

def nodeAtName (root : Node RR) (qnameWire : ByteArray) : Option (Node RR) :=
  match wireFormatToLabels qnameWire with
  | .ok labels => nodeAt root labels.toList.reverse
  | .error _ => none

inductive Outcome (RR : Type) where

  | answer (rrs : Array RR)

  | nodata

  | redirect (rr : RR) (canonical : ByteArray)

  | nameError

def cnameType : BitVec 16 := 5

def lookupAt [RRParse RR] (n : Node RR) (qtype : BitVec 16) : Outcome RR :=
  let matching := n.resourceSet.filter (fun rr => RRParse.rrType rr == qtype)
  if matching.size > 0 then .answer matching
  else
    match n.resourceSet.find? (fun rr => RRParse.rrType rr == cnameType) with
    | some rr =>
      if qtype == cnameType then .nodata
      else .redirect rr (RRParse.rrRdata rr)
    | none => .nodata

def treeLookup [RRParse RR] (root : Node RR) (qnameWire : ByteArray)
    (qtype : BitVec 16) : Outcome RR :=
  match nodeAtName root qnameWire with
  | none => .nameError
  | some n => lookupAt n qtype

def treeResolve [RRParse RR] (root : Node RR) (qtype : BitVec 16) :
    Nat → ByteArray → Array RR → Option (Array RR × Outcome RR)
  | 0, _, _ => none
  | fuel + 1, qname, chain =>
    match treeLookup root qname qtype with
    | .redirect rr canonical => treeResolve root qtype fuel canonical (chain.push rr)
    | o => some (chain, o)

inductive WellFormed [RRParse RR] : Node RR → Prop where
  | mk {n : Node RR} :
      node_label_size RR n →
      node_brothers_distinct_label RR n →
      (∀ c ∈ n.children.toList, WellFormed c) →
      WellFormed n

structure WellFormedTree [RRParse RR] (root : Node RR) : Prop where
  wf : WellFormed root
  rootNull : node_root_label_null RR root

theorem domainname_conform (R : Type) (path : Node R → List (Node R)) :
    domainname_labels_on_path R (fun n => (path n).map Node.label) path :=
  fun _ => rfl

end VeriDNS.Impl.NameTree
