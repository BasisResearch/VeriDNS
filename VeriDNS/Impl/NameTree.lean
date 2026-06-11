import VeriDNS.Spec.NameTree
import VeriDNS.Spec.Resolver
import VeriDNS.Spec.Message
import VeriDNS.Impl.DomainName

/-!
# Denotational lookup over the RFC 1034 §3.1 name tree

`Spec.Node` (generated from the §3.1 prose) is the semantic model: one
global tree of labeled nodes, each carrying a resource set. This module
gives queries their *meaning* against that tree:

- `nodeAt`/`nodeAtName` — descend from the root by labels (case-insensitive
  per RFC 1035 §3.1, routed through `foldNameCase`);
- `treeLookup` — the verdict for one ⟨QNAME, QTYPE⟩: the matching RRs at
  the node, NODATA when the node exists but holds none, a CNAME redirect,
  or NXDOMAIN exactly when the node is missing;
- `treeResolve` — `treeLookup` with the RFC 1034 §3.6.2 CNAME chase,
  accumulating the chain;
- `WellFormed` — the recursive closure of the generated node-local props
  (`node_label_size`, `node_brothers_distinct_label`) over every node
  actually in a tree, plus `node_root_label_null` at the root.

The resolver is then proven (Proof/NameTree.lean) to return `treeResolve`'s
verdict whenever the network's accepted responses are consistent with the
tree — the answer the client gets is the data at the node QNAME names,
and NXDOMAIN means the node does not exist.
-/

namespace VeriDNS.Impl.NameTree

open VeriDNS.Spec
open VeriDNS.Impl.DomainName (foldNameCase wireFormatToLabels)

/-- Case-insensitive equality of raw labels (no length prefix), RFC 1035
    §3.1: the byte-level fold identifies `A`/`a`; non-alphabetic bytes
    compare exactly. -/
def labelEqCI (a b : ByteArray) : Bool :=
  foldNameCase a == foldNameCase b

variable {RR : Type}

/-- The child of `n` carrying the given label, if any (first match;
    well-formed trees have at most one — `node_brothers_distinct_label`). -/
def findChild (n : Node RR) (lab : ByteArray) : Option (Node RR) :=
  n.children.find? (fun c => labelEqCI c.label lab)

/-- Descend from `root` along `labels`, given ROOT-FIRST (the reverse of
    the printed/wire order, which is most-specific-first). `none` exactly
    when some label has no matching child — RFC 1034 §4.3.2's "the
    corresponding label does not exist". -/
def nodeAt (root : Node RR) : List ByteArray → Option (Node RR)
  | [] => some root
  | l :: rest =>
    match findChild root l with
    | some c => nodeAt c rest
    | none => none

/-- The node a wire-format domain name refers to, if it exists in the
    tree. An undecodable name names no node. -/
def nodeAtName (root : Node RR) (qnameWire : ByteArray) : Option (Node RR) :=
  match wireFormatToLabels qnameWire with
  | .ok labels => nodeAt root labels.toList.reverse
  | .error _ => none

/-- The semantic verdict for one ⟨QNAME, QTYPE⟩ query against the tree. -/
inductive Outcome (RR : Type) where
  /-- The node exists and holds records of the queried type. -/
  | answer (rrs : Array RR)
  /-- The node exists but holds no record of the queried type
      (RFC 2308 §2.2 NODATA). -/
  | nodata
  /-- The node exists, holds no record of the queried type, but has a
      CNAME: resolution restarts at the canonical name (RFC 1034 §3.6.2). -/
  | redirect (rr : RR) (canonical : ByteArray)
  /-- The node does not exist (RFC 2308 §2.1 NXDOMAIN / RFC 1035 §4.1.1
      name error). -/
  | nameError

/-- The CNAME RR type code (RFC 1035 §3.2.2). -/
def cnameType : BitVec 16 := 5

/-- Verdict at a node that exists: matching RRs, else a CNAME redirect
    (a CNAME query is answered by the CNAME itself, never redirected),
    else NODATA. -/
def lookupAt [RRParse RR] (n : Node RR) (qtype : BitVec 16) : Outcome RR :=
  let matching := n.resourceSet.filter (fun rr => RRParse.rrType rr == qtype)
  if matching.size > 0 then .answer matching
  else
    match n.resourceSet.find? (fun rr => RRParse.rrType rr == cnameType) with
    | some rr =>
      if qtype == cnameType then .nodata
      else .redirect rr (RRParse.rrRdata rr)
    | none => .nodata

/-- The denotation of one query: NXDOMAIN exactly when the name's node is
    missing from the tree; otherwise the verdict at the node. -/
def treeLookup [RRParse RR] (root : Node RR) (qnameWire : ByteArray)
    (qtype : BitVec 16) : Outcome RR :=
  match nodeAtName root qnameWire with
  | none => .nameError
  | some n => lookupAt n qtype

/-- `treeLookup` with the CNAME chase: follow redirects, accumulating the
    chain (served back in the answer section, RFC 1034 §3.6.2). `none` on
    fuel exhaustion — a CNAME cycle in the tree, which well-formed
    deployments do not have. -/
def treeResolve [RRParse RR] (root : Node RR) (qtype : BitVec 16) :
    Nat → ByteArray → Array RR → Option (Array RR × Outcome RR)
  | 0, _, _ => none
  | fuel + 1, qname, chain =>
    match treeLookup root qname qtype with
    | .redirect rr canonical => treeResolve root qtype fuel canonical (chain.push rr)
    | o => some (chain, o)

/-- Well-formedness: the generated node-local §3.1 props hold at every
    node of the tree. (`node_label_size`: labels ≤ 63 octets;
    `node_brothers_distinct_label`: no two children share a label.) -/
inductive WellFormed [RRParse RR] : Node RR → Prop where
  | mk {n : Node RR} :
      node_label_size RR n →
      node_brothers_distinct_label RR n →
      (∀ c ∈ n.children.toList, WellFormed c) →
      WellFormed n

/-- A well-formed TREE additionally has the reserved null label at its
    root (`node_root_label_null`, §3.1). -/
structure WellFormedTree [RRParse RR] (root : Node RR) : Prop where
  wf : WellFormed root
  rootNull : node_root_label_null RR root

/-- Conformance to the generated `domainname_labels_on_path`: the domain
    name of a node IS the label projection mapped over its path to the
    root — the RFC sentence is definitional, so any path assignment
    satisfies it with the name function it induces. The substantive
    connection between names and descent is `nodeAt`/`nodeAtName`, used by
    the lookup theorems. -/
theorem domainname_conform (R : Type) (path : Node R → List (Node R)) :
    domainname_labels_on_path R (fun n => (path n).map Node.label) path :=
  fun _ => rfl

end VeriDNS.Impl.NameTree
