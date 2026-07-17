import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Message
import VeriDNS.RFC.Check
include_rfc [1034][355:371] {
3.1. Name space specifications and terminology

The domain name space is a tree structure.  Each node and leaf on the
tree corresponds to a resource set (which may be empty).  The domain
system makes no distinctions between the uses of the interior nodes and
leaves, and this memo uses the term "node" to refer to both.

Each node has a label, which is zero to 63 octets in length.  Brother
nodes may not have the same label, although the same label can be used
for nodes which are not brothers.  One label is reserved, and that is
the null (i.e., zero length) label used for the root.

The domain name of a node is the list of the labels on the path from the
node to the root of the tree.  By convention, the labels that compose a
domain name are printed or read left to right, from the most specific
(lowest, farthest from the root) to the least specific (highest, closest
to the root).
}




/--

3. DOMAIN NAME SPACE and RESOURCE RECORDS

3.1. Name space specifications and terminology

The domain name space is a tree structure.  Each node and leaf on the
tree corresponds to a resource set (which may be empty).  The domain
system makes no distinctions between the uses of the interior nodes and
leaves, and this memo uses the term "node" to refer to both.

-/
@[blueprint "Node"]
inductive VeriDNS.Spec.Node (R : Type) where
  | mk : ByteArray → Array R → Array (VeriDNS.Spec.Node R) → VeriDNS.Spec.Node R

def VeriDNS.Spec.Node.label : {R : Type} → VeriDNS.Spec.Node R → ByteArray :=
  fun {R} n =>
  match n with
  | VeriDNS.Spec.Node.mk l a a_1 => l



/--

The domain name of a node is the list of the labels on the path from the
node to the root of the tree.  By convention, the labels that compose a
domain name are printed or read left to right, from the most specific
(lowest, farthest from the root) to the least specific (highest, closest
to the root).

-/
def VeriDNS.Spec.domainname_labels_on_path : (R : Type) →
  (VeriDNS.Spec.Node R → List ByteArray) → (VeriDNS.Spec.Node R → List (VeriDNS.Spec.Node R)) → Prop :=
  fun R domainName pathFromNodeToRoot =>
  ∀ (n : VeriDNS.Spec.Node R),
    domainName n = List.map VeriDNS.Spec.Node.label (pathFromNodeToRoot n)

def VeriDNS.Spec.Node.resourceSet : {R : Type} → VeriDNS.Spec.Node R → Array R :=
  fun {R} n =>
  match n with
  | VeriDNS.Spec.Node.mk a rs a_1 => rs

/--
Each node has a label, which is zero to 63 octets in length.  Brother
nodes may not have the same label, although the same label can be used
for nodes which are not brothers.  One label is reserved, and that is
the null (i.e., zero length) label used for the root.
-/
def VeriDNS.Spec.node_root_label_null : (R : Type) → VeriDNS.Spec.Node R → Prop :=
  fun R root => root.label.size = 0

def VeriDNS.Spec.Node.children : {R : Type} → VeriDNS.Spec.Node R → Array (VeriDNS.Spec.Node R) :=
  fun {R} n =>
  match n with
  | VeriDNS.Spec.Node.mk a a_1 cs => cs

/--
Each node has a label, which is zero to 63 octets in length.  Brother
nodes may not have the same label, although the same label can be used
for nodes which are not brothers.  One label is reserved, and that is
the null (i.e., zero length) label used for the root.
-/
def VeriDNS.Spec.node_label_size : (R : Type) → VeriDNS.Spec.Node R → Prop :=
  fun R n => n.label.size ≤ 63

/--
Each node has a label, which is zero to 63 octets in length.  Brother
nodes may not have the same label, although the same label can be used
for nodes which are not brothers.  One label is reserved, and that is
the null (i.e., zero length) label used for the root.
-/
def VeriDNS.Spec.node_brothers_distinct_label : (R : Type) → VeriDNS.Spec.Node R → Prop :=
  fun R n => ∀ (i j : Fin n.children.size), i ≠ j → n.children[i].label ≠ n.children[j].label



/--

The domain name of a node is the list of the labels on the path from the
node to the root of the tree.  By convention, the labels that compose a
domain name are printed or read left to right, from the most specific
(lowest, farthest from the root) to the least specific (highest, closest
to the root).

-/
def VeriDNS.Spec.DomainName : Type := List ByteArray



/--

A domain is identified by a domain name, and consists of that part of
the domain name space that is at or below the domain name which
specifies the domain.  A domain is a subdomain of another domain if it
is contained within that domain.  This relationship can be tested by
seeing if the subdomain's name ends with the containing domain's name.
For example, A.B.C.D is a subdomain of B.C.D, C.D, D, and " ".

-/
def VeriDNS.Spec.isSubdomain (sub dom : List ByteArray) : Prop := dom <:+ sub

theorem VeriDNS.Spec.isSubdomain_example
    (a b c d : ByteArray) :
    VeriDNS.Spec.isSubdomain [a, b, c, d] [b, c, d]
  ∧ VeriDNS.Spec.isSubdomain [a, b, c, d] [c, d]
  ∧ VeriDNS.Spec.isSubdomain [a, b, c, d] [d]
  ∧ VeriDNS.Spec.isSubdomain [a, b, c, d] [] := by
  refine ⟨⟨[a], rfl⟩, ⟨[a, b], rfl⟩, ⟨[a, b, c], rfl⟩, ⟨[a, b, c, d], rfl⟩⟩

theorem VeriDNS.Spec.isSubdomain_refl (n : List ByteArray) :
    VeriDNS.Spec.isSubdomain n n := List.suffix_refl n

theorem VeriDNS.Spec.isSubdomain_trans {a b c : List ByteArray}
    (h₁ : VeriDNS.Spec.isSubdomain a b) (h₂ : VeriDNS.Spec.isSubdomain b c) :
    VeriDNS.Spec.isSubdomain a c := List.IsSuffix.trans h₂ h₁


/--
Relative names are either taken relative to a well known origin, or to a
list of domains used as a search list.  Relative names appear mostly at
the user interface, where their interpretation varies from
implementation to implementation, and in master files, where they are
relative to a single origin domain name.  The most common interpretation
uses the root "." as either the single origin or as one of the members
of the search list, so a multi-label relative name is often one where
the trailing dot has been omitted to save typing.

To simplify implementations, the total number of octets that represent a
domain name (i.e., the sum of all label octets and label lengths) is
limited to 255.
-/
def VeriDNS.Spec.domainName_octet_limit : Nat := 255

def VeriDNS.Spec.nameOctetCount (n : List ByteArray) : Nat :=
  (n.map (fun l => 1 + l.size)).sum + 1

def VeriDNS.Spec.nameWithinLimit (n : List ByteArray) : Prop :=
  VeriDNS.Spec.nameOctetCount n ≤ VeriDNS.Spec.domainName_octet_limit



/--

By convention, domain names can be stored with arbitrary case, but
domain name comparisons for all present domain functions are done in a
case-insensitive manner, assuming an ASCII character set, and a high
order zero bit.  This means that you are free to create a node with
label "A" or a node with label "a", but not both as brothers; you could
refer to either using "a" or "A".  When you receive a domain name or
label, you should preserve its case.  The rationale for this choice is
that we may someday need to add full binary domain names for new
services; existing services would not be changed.

-/
def VeriDNS.Spec.name_comparison_case_insensitive
    (foldCase : ByteArray → ByteArray) (R : Type) (n : VeriDNS.Spec.Node R) : Prop :=
  ∀ (i j : Fin n.children.size), i ≠ j →
    foldCase n.children[i].label ≠ foldCase n.children[j].label

def VeriDNS.Spec.case_preserved {α : Type}
    (receive store : α → ByteArray) : Prop :=
  ∀ (x : α), store x = receive x





/--

3.3. Technical guidelines on use

Before the DNS can be used to hold naming information for some kind of
object, two needs must be met:

   - A convention for mapping between object names and domain
     names.  This describes how information about an object is
     accessed.

   - RR types and data formats for describing the object.
-/
@[blueprint "ObjectMapping"]
structure VeriDNS.Spec.ObjectMapping (Object : Type) (RR : Type) where

  toDomainName : Object → List ByteArray

  describe : Object → Array RR

private def lbl (s : String) : ByteArray := s.toUTF8

private def leaf (s : String) : VeriDNS.Spec.Node Unit :=
  VeriDNS.Spec.Node.mk (lbl s) #[] #[]

private def branch (s : String) (cs : Array (VeriDNS.Spec.Node Unit)) : VeriDNS.Spec.Node Unit :=
  VeriDNS.Spec.Node.mk (lbl s) #[] cs





/--
3.4. Example name space

The following figure shows a part of the current domain name space, and
is used in many examples in this RFC.  Note that the tree is a very
small subset of the actual name space.

                                   |
                                   |
             +---------------------+------------------+
             |                     |                  |
            MIL                   EDU                ARPA
             |                     |                  |
             |                     |                  |
       +-----+-----+               |     +------+-----+-----+
       |     |     |               |     |      |           |
      BRL  NOSC  DARPA             |  IN-ADDR  SRI-NIC     ACC
                                   |
       +--------+------------------+---------------+--------+
       |        |                  |               |        |
      UCI      MIT                 |              UDEL     YALE
                |                 ISI
                |                  |
            +---+---+              |
            |       |              |
           LCS  ACHILLES  +--+-----+-----+--------+
            |             |  |     |     |        |
            XX            A  C   VAXA  VENERA Mockapetris

In this example, the root domain has three immediate subdomains: MIL,
EDU, and ARPA.  The LCS.MIT.EDU domain has one immediate subdomain named
XX.LCS.MIT.EDU.  All of the leaves are also domains.

-/
def VeriDNS.Spec.exampleNameSpace : VeriDNS.Spec.Node Unit :=
  branch "" #[
    branch "MIL" #[leaf "BRL", leaf "NOSC", leaf "DARPA"],
    branch "EDU" #[
      branch "MIT" #[branch "LCS" #[leaf "XX"], leaf "ACHILLES"],
      branch "ISI" #[leaf "A", leaf "C", leaf "VAXA", leaf "VENERA", leaf "Mockapetris"],
      leaf "UDEL", leaf "YALE", leaf "UCI"],
    branch "ARPA" #[leaf "IN-ADDR", leaf "SRI-NIC", leaf "ACC"]]

theorem VeriDNS.Spec.exampleNameSpace_root_subdomains :
    VeriDNS.Spec.exampleNameSpace.children.size = 3
  ∧ VeriDNS.Spec.exampleNameSpace.children[0].label = lbl "MIL"
  ∧ VeriDNS.Spec.exampleNameSpace.children[1].label = lbl "EDU"
  ∧ VeriDNS.Spec.exampleNameSpace.children[2].label = lbl "ARPA" :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem VeriDNS.Spec.exampleNameSpace_lcs_child :
    (VeriDNS.Spec.exampleNameSpace.children[1].children[0].children[0]).children.size = 1
  ∧ (VeriDNS.Spec.exampleNameSpace.children[1].children[0].children[0]).children[0].label
      = lbl "XX" :=
  ⟨rfl, rfl⟩

theorem VeriDNS.Spec.exampleNameSpace_root_label_null :
    VeriDNS.Spec.node_root_label_null Unit VeriDNS.Spec.exampleNameSpace := by
  unfold VeriDNS.Spec.node_root_label_null; decide

theorem VeriDNS.Spec.exampleNameSpace_root_label_size :
    VeriDNS.Spec.node_label_size Unit VeriDNS.Spec.exampleNameSpace := by
  unfold VeriDNS.Spec.node_label_size; decide

theorem VeriDNS.Spec.exampleNameSpace_root_brothers_distinct :
    VeriDNS.Spec.node_brothers_distinct_label Unit VeriDNS.Spec.exampleNameSpace := by
  unfold VeriDNS.Spec.node_brothers_distinct_label; decide

theorem VeriDNS.Spec.exampleNameSpace_deep_label_size :
    VeriDNS.Spec.node_label_size Unit
      VeriDNS.Spec.exampleNameSpace.children[1].children[1].children[4] := by
  unfold VeriDNS.Spec.node_label_size; decide

theorem VeriDNS.Spec.exampleName_xx_within_limit :
    VeriDNS.Spec.nameWithinLimit [lbl "XX", lbl "LCS", lbl "MIT", lbl "EDU"] := by
  unfold VeriDNS.Spec.nameWithinLimit VeriDNS.Spec.nameOctetCount
    VeriDNS.Spec.domainName_octet_limit
  decide

check_rfc_doc VeriDNS.Spec.Node [1034][352:361]

check_rfc_doc VeriDNS.Spec.node_label_size [1034][362:365] via VeriDNS.Spec.exampleNameSpace_root_label_size
check_rfc_doc VeriDNS.Spec.node_brothers_distinct_label [1034][362:365] via VeriDNS.Spec.exampleNameSpace_root_brothers_distinct
check_rfc_doc VeriDNS.Spec.node_root_label_null [1034][362:365] via VeriDNS.Spec.exampleNameSpace_root_label_null
rfc_proves VeriDNS.Spec.exampleNameSpace_deep_label_size [1034][362:365]
check_rfc_doc VeriDNS.Spec.domainname_labels_on_path [1034][366:372]
check_rfc_doc VeriDNS.Spec.DomainName [1034][366:372]
check_rfc_doc VeriDNS.Spec.name_comparison_case_insensitive [1034][378:396]
check_rfc_doc VeriDNS.Spec.domainName_octet_limit [1034][411:422]
rfc_proves VeriDNS.Spec.exampleName_xx_within_limit [1034][411:422]
check_rfc_doc VeriDNS.Spec.isSubdomain [1034][423:430] via VeriDNS.Spec.isSubdomain_example
rfc_out_of_scope [1034][431:454]
check_rfc_doc VeriDNS.Spec.ObjectMapping [1034][468:478]
check_rfc_doc VeriDNS.Spec.exampleNameSpace [1034][518:549]
rfc_proves VeriDNS.Spec.exampleNameSpace_root_subdomains [1034][518:549]
rfc_proves VeriDNS.Spec.exampleNameSpace_lcs_child [1034][518:549]
