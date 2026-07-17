import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.NameTree
import VeriDNS.Spec.Header
import VeriDNS.Spec.RRType
import VeriDNS.Spec.ResourceRecord
import VeriDNS.RFC.Check
include_rfc [1034][996:1024] {
Name servers are the repositories of information that make up the domain
database.  The database is divided up into sections called zones, which
are distributed among the name servers.  While name servers can have
several optional functions and sources of data, the essential task of a
name server is to answer queries using data in its zones.  By design,
name servers can answer queries in a simple manner; the response can
always be generated using only local data, and either contains the
answer to the question or a referral to other name servers "closer" to
the desired information.

A given zone will be available from several name servers to insure its
availability in spite of host or communication link failure.  By
administrative fiat, we require every zone to be available on at least
two servers, and many zones have more redundancy than that.

A given name server will typically support one or more zones, but this
gives it authoritative information about only a small section of the
domain tree.  It may also have some cached non-authoritative data about
other parts of the tree.  The name server marks its responses to queries
so that the requester can tell whether the response comes from
authoritative data or not.
}
namespace VeriDNS.Spec

/--
name servers can answer queries in a simple manner; the response can
always be generated using only local data, and either contains the
answer to the question or a referral to other name servers "closer" to
the desired information.
-/
inductive Response (R : Type) where
  | answer : Array R → Response R
  | referral : Array R → Response R
  | error : Rcode → Response R



/--
4. NAME SERVERS

4.1. Introduction

Name servers are the repositories of information that make up the domain
database.  The database is divided up into sections called zones, which
are distributed among the name servers.  While name servers can have
several optional functions and sources of data, the essential task of a
name server is to answer queries using data in its zones.  By design,
-/
@[blueprint "NameServer"]
structure NameServer (R : Type) where
  zones : List (ByteArray × Array R)
  cache : Array R


/--
A given zone will be available from several name servers to insure its
availability in spite of host or communication link failure.  By
administrative fiat, we require every zone to be available on at least
two servers, and many zones have more redundancy than that.

-/
def zone_redundancy (zoneServerCount : Nat) : Prop := 2 ≤ zoneServerCount

/--
A given name server will typically support one or more zones, but this
gives it authoritative information about only a small section of the
domain tree.  It may also have some cached non-authoritative data about
other parts of the tree.  The name server marks its responses to queries
so that the requester can tell whether the response comes from
authoritative data or not.
-/
def responses_marked_authoritative {R : Type}
    (markAuthoritative fromAuthoritativeData : Response R → Bool) : Prop :=
  ∀ (r : Response R), markAuthoritative r = fromAuthoritativeData r
include_rfc [1034][1028:1051] {
The domain database is partitioned in two ways: by class, and by "cuts"
made in the name space between nodes.

The class partition is simple.  The database for any class is organized,
delegated, and maintained separately from all other classes.  Since, by
convention, the name spaces are the same for all classes, the separate
classes can be thought of as an array of parallel namespace trees.  Note
that the data attached to nodes will be different for these different
parallel classes.  The most common reasons for creating a new class are
the necessity for a new data format for existing types or a desire for a
separately managed version of the existing name space.

Within a class, "cuts" in the name space can be made between any two
adjacent nodes.  After all cuts are made, each group of connected name
space is a separate zone.  The zone is said to be authoritative for all
names in the connected region.  Note that the "cuts" in the name space
may be in different places for different classes, the name servers may
be different, etc.

These rules mean that every zone has at least one node, and hence domain
name, for which it is authoritative, and all of the nodes in a
particular zone are connected.  Given, the tree structure, every zone
has a highest node which is closer to the root than any other node in
the zone.  The name of this node is often used to identify the zone.
}

/--
4.2. How the database is divided into zones

The domain database is partitioned in two ways: by class, and by "cuts"
made in the name space between nodes.
-/
inductive PartitionAxis where
  | byClass : PartitionAxis
  | byCut : PartitionAxis

/--
The class partition is simple.  The database for any class is organized,
delegated, and maintained separately from all other classes.  Since, by
convention, the name spaces are the same for all classes, the separate
classes can be thought of as an array of parallel namespace trees.  Note
that the data attached to nodes will be different for these different
parallel classes.  The most common reasons for creating a new class are
the necessity for a new data format for existing types or a desire for a
separately managed version of the existing name space.
-/
@[blueprint "ClassPartition"]
structure ClassPartition (R : Type) where
  treeForClass : BitVec 16 → Node R


/--
Within a class, "cuts" in the name space can be made between any two
adjacent nodes.  After all cuts are made, each group of connected name
space is a separate zone.  The zone is said to be authoritative for all
names in the connected region.  Note that the "cuts" in the name space
may be in different places for different classes, the name servers may
be different, etc.

-/
@[blueprint "Zone"]
structure Zone (R : Type) where

  apex : Node R

  isCut : List ByteArray → Bool


/--
These rules mean that every zone has at least one node, and hence domain
name, for which it is authoritative, and all of the nodes in a
particular zone are connected.  Given, the tree structure, every zone
has a highest node which is closer to the root than any other node in
the zone.  The name of this node is often used to identify the zone.

-/
def Zone.name {R : Type} (z : Zone R) : ByteArray := z.apex.label


/--
a subtree.  Once an organization controls its own zone it can
unilaterally change the data in the zone, grow new tree sections
connected to the zone, delete existing nodes, or delegate new subzones
under its zone.

If the organization has substructure, it may want to make further
internal partitions to achieve nested delegations of name space control.
In some cases, such divisions are made purely to make database
maintenance more convenient.
-/
inductive ZoneEvolution (R : Type) : Node R → Node R → Prop where
  | changeData (l : ByteArray) (rs rs' : Array R) (cs : Array (Node R)) :
      ZoneEvolution R (Node.mk l rs cs) (Node.mk l rs' cs)
  | growSection (l : ByteArray) (rs : Array R) (cs : Array (Node R)) (new : Node R) :
      ZoneEvolution R (Node.mk l rs cs) (Node.mk l rs (cs.push new))
  | deleteNode (l : ByteArray) (rs : Array R) (cs cs' : Array (Node R)) :
      (∀ x, x ∈ cs' → x ∈ cs) →
      ZoneEvolution R (Node.mk l rs cs) (Node.mk l rs cs')
  | delegateSubzone (l : ByteArray) (rs : Array R) (cs : Array (Node R)) (sub : Node R) :
      ZoneEvolution R (Node.mk l rs cs) (Node.mk l rs (cs.push sub))

theorem ZoneEvolution.preserves_label {R : Type} {t t' : Node R}
    (h : ZoneEvolution R t t') : t.label = t'.label := by
  cases h <;> rfl
include_rfc [1034][1077:1136] {
The data that describes a zone has four major parts:

   - Authoritative data for all nodes within the zone.

   - Data that defines the top node of the zone (can be thought of
     as part of the authoritative data).

   - Data that describes delegated subzones, i.e., cuts around the
     bottom of the zone.

   - Data that allows access to name servers for subzones
     (sometimes called "glue" data).

All of this data is expressed in the form of RRs, so a zone can be
completely described in terms of a set of RRs.  Whole zones can be
transferred between name servers by transferring the RRs, either carried
in a series of messages or by FTPing a master file which is a textual
representation.

The authoritative data for a zone is simply all of the RRs attached to
all of the nodes from the top node of the zone down to leaf nodes or
nodes above cuts around the bottom edge of the zone.

Though logically part of the authoritative data, the RRs that describe
the top node of the zone are especially important to the zone's
management.  These RRs are of two types: name server RRs that list, one
per RR, all of the servers for the zone, and a single SOA RR that
describes zone management parameters.

The RRs that describe cuts around the bottom of the zone are NS RRs that
name the servers for the subzones.  Since the cuts are between nodes,
these RRs are NOT part of the authoritative data of the zone, and should
be exactly the same as the corresponding RRs in the top node of the
subzone.  Since name servers are always associated with zone boundaries,
NS RRs are only found at nodes which are the top node of some zone.  In
the data that makes up a zone, NS RRs are found at the top node of the
zone (and are authoritative) and at cuts around the bottom of the zone
(where they are not authoritative), but never in between.

One of the goals of the zone structure is that any zone have all the
data required to set up communications with the name servers for any
subzones.  That is, parent zones have all the information needed to
access servers for their children zones.  The NS RRs that name the
servers for subzones are often not enough for this task since they name
the servers, but do not give their addresses.  In particular, if the
name of the name server is itself in the subzone, we could be faced with
the situation where the NS RRs tell us that in order to learn a name
server's address, we should contact the server using the address we wish
to learn.  To fix this problem, a zone contains "glue" RRs which are not
part of the authoritative data, and are address RRs for the servers.
These RRs are only necessary if the name server's name is "below" the
cut, and are only used as part of a referral response.
}





/--
4.2.1. Technical considerations

The data that describes a zone has four major parts:

   - Authoritative data for all nodes within the zone.

   - Data that defines the top node of the zone (can be thought of
     as part of the authoritative data).

   - Data that describes delegated subzones, i.e., cuts around the
     bottom of the zone.

   - Data that allows access to name servers for subzones
     (sometimes called "glue" data).
-/
@[blueprint "ZoneData"]
structure ZoneData (R : Type) where

  authoritativeData : Array R

  topNodeData : Array R

  delegations : Array R

  glue : Array R


/--
All of this data is expressed in the form of RRs, so a zone can be
completely described in terms of a set of RRs.  Whole zones can be
transferred between name servers by transferring the RRs, either carried
in a series of messages or by FTPing a master file which is a textual
representation.

-/
def zone_described_by_RRs {R : Type} (z : ZoneData R) : Array R :=
  z.authoritativeData ++ z.topNodeData ++ z.delegations ++ z.glue


/--
The authoritative data for a zone is simply all of the RRs attached to
all of the nodes from the top node of the zone down to leaf nodes or
nodes above cuts around the bottom edge of the zone.

-/
def zone_authoritative_data {R : Type} (z : Zone R) (name : List ByteArray) : Prop :=
  z.isCut name = false


/--
Though logically part of the authoritative data, the RRs that describe
the top node of the zone are especially important to the zone's
management.  These RRs are of two types: name server RRs that list, one
per RR, all of the servers for the zone, and a single SOA RR that
describes zone management parameters.

-/
def topNode_RR_types : List Nat := [RRType.ns.toCode, RRType.soa.toCode]


/--
The RRs that describe cuts around the bottom of the zone are NS RRs that
name the servers for the subzones.  Since the cuts are between nodes,
these RRs are NOT part of the authoritative data of the zone, and should
be exactly the same as the corresponding RRs in the top node of the
subzone.  Since name servers are always associated with zone boundaries,
NS RRs are only found at nodes which are the top node of some zone.  In
the data that makes up a zone, NS RRs are found at the top node of the
zone (and are authoritative) and at cuts around the bottom of the zone
(where they are not authoritative), but never in between.

-/
def ns_only_at_zone_top {R : Type} (z : Zone R) (hasNS : List ByteArray → Bool) : Prop :=
  ∀ name, hasNS name = true → name = [] ∨ z.isCut name = true

/--
One of the goals of the zone structure is that any zone have all the
data required to set up communications with the name servers for any
subzones.  That is, parent zones have all the information needed to
access servers for their children zones.  The NS RRs that name the
servers for subzones are often not enough for this task since they name
the servers, but do not give their addresses.  In particular, if the
name of the name server is itself in the subzone, we could be faced with
the situation where the NS RRs tell us that in order to learn a name
server's address, we should contact the server using the address we wish
to learn.  To fix this problem, a zone contains "glue" RRs which are not
part of the authoritative data, and are address RRs for the servers.
These RRs are only necessary if the name server's name is "below" the
cut, and are only used as part of a referral response.
-/
@[blueprint "Glue"]
structure Glue (R : Type) where
  addressRRs : Array R
include_rfc [1034][1140:1166] {
When some organization wants to control its own domain, the first step
is to identify the proper parent zone, and get the parent zone's owners
to agree to the delegation of control.  While there are no particular
technical constraints dealing with where in the tree this can be done,
there are some administrative groupings discussed in [RFC-1032] which
deal with top level organization, and middle level zones are free to
create their own rules.  For example, one university might choose to use
a single zone, while another might choose to organize by subzones
dedicated to individual departments or schools.  [RFC-1033] catalogs
available DNS software an discusses administration procedures.

Once the proper name for the new subzone is selected, the new owners
should be required to demonstrate redundant name server support.  Note
that there is no requirement that the servers for a zone reside in a
host which has a name in that domain.  In many cases, a zone will be
more accessible to the internet at large if its servers are widely
distributed rather than being within the physical facilities controlled
by the same organization that manages the zone.  For example, in the
current DNS, one of the name servers for the United Kingdom, or UK
domain, is found in the US.  This allows US hosts to get UK data without
using limited transatlantic bandwidth.

As the last installation step, the delegation NS RRs and glue RRs
necessary to make the delegation effective should be added to the parent
zone.  The administrators of both zones should insure that the NS and
glue RRs which mark both sides of the cut are consistent and remain so.
}


/--

Once the proper name for the new subzone is selected, the new owners
should be required to demonstrate redundant name server support.  Note
that there is no requirement that the servers for a zone reside in a
host which has a name in that domain.  In many cases, a zone will be
more accessible to the internet at large if its servers are widely
distributed rather than being within the physical facilities controlled
by the same organization that manages the zone.  For example, in the
current DNS, one of the name servers for the United Kingdom, or UK
domain, is found in the US.  This allows US hosts to get UK data without
using limited transatlantic bandwidth.

-/
def redundant_name_server_support (zoneServerCount : Nat) : Prop :=
  zone_redundancy zoneServerCount


/--
As the last installation step, the delegation NS RRs and glue RRs
necessary to make the delegation effective should be added to the parent
zone.  The administrators of both zones should insure that the NS and
glue RRs which mark both sides of the cut are consistent and remain so.

-/
def delegation_glue_added_to_parent {R : Type} (parent : ZoneData R)
    (delegationNS glueRRs : Array R) : ZoneData R :=
  { parent with delegations := parent.delegations ++ delegationNS,
                glue := parent.glue ++ glueRRs }
include_rfc [1034][1179:1199] {
The principal activity of name servers is to answer standard queries.
Both the query and its response are carried in a standard message format
which is described in [RFC-1035].  The query contains a QTYPE, QCLASS,
and QNAME, which describe the types and classes of desired information
and the name of interest.

The way that the name server answers the query depends upon whether it
is operating in recursive mode or not:

   - The simplest mode for the server is non-recursive, since it
     can answer queries using only local information: the response
     contains an error, the answer, or a referral to some other
     server "closer" to the answer.  All name servers must
     implement non-recursive queries.

   - The simplest mode for the client is recursive, since in this
     mode the name server acts in the role of a resolver and
     returns either an error or the answer, but never referrals.
     This service is optional in a name server, and the name server
     may also choose to restrict the clients which can use
     recursive mode.
}


/--
4.3.1. Queries and responses

The principal activity of name servers is to answer standard queries.
Both the query and its response are carried in a standard message format
which is described in [RFC-1035].  The query contains a QTYPE, QCLASS,
and QNAME, which describe the types and classes of desired information
and the name of interest.

-/
@[blueprint "StandardQuery"]
structure StandardQuery where
  qname : List ByteArray
  qtype : BitVec 16
  qclass : BitVec 16


/--
The way that the name server answers the query depends upon whether it
is operating in recursive mode or not:

   - The simplest mode for the server is non-recursive, since it
     can answer queries using only local information: the response
     contains an error, the answer, or a referral to some other
     server "closer" to the answer.  All name servers must
     implement non-recursive queries.
-/
def nonRecursive_response_kinds {R : Type} (r : Response R) : Prop :=
  (∃ a, r = Response.answer a) ∨ (∃ n, r = Response.referral n) ∨ (∃ e, r = Response.error e)

theorem nonRecursive_response_kinds_total {R : Type} (r : Response R) :
    nonRecursive_response_kinds r := by
  cases r with
  | answer a => exact Or.inl ⟨a, rfl⟩
  | referral n => exact Or.inr (Or.inl ⟨n, rfl⟩)
  | error e => exact Or.inr (Or.inr ⟨e, rfl⟩)


/--
   - The simplest mode for the client is recursive, since in this
     mode the name server acts in the role of a resolver and
     returns either an error or the answer, but never referrals.
     This service is optional in a name server, and the name server
     may also choose to restrict the clients which can use
     recursive mode.

-/
inductive RecursiveResult (R : Type) where
  | answer : Array R → RecursiveResult R
  | error : Rcode → RecursiveResult R

def RecursiveResult.toResponse {R : Type} : RecursiveResult R → Response R
  | .answer a => Response.answer a
  | .error e => Response.error e

theorem recursive_never_referral {R : Type} (r : RecursiveResult R) :
    ∀ ns, r.toResponse ≠ Response.referral ns := by
  intro ns; cases r <;> simp [RecursiveResult.toResponse]

end VeriDNS.Spec

check_rfc_doc VeriDNS.Spec.NameServer [1034][992:1000]
check_rfc_doc VeriDNS.Spec.Response [1034][1009:1012]
check_rfc_doc VeriDNS.Spec.zone_redundancy [1034][1014:1018]
check_rfc_doc VeriDNS.Spec.responses_marked_authoritative [1034][1019:1024]
check_rfc_doc VeriDNS.Spec.PartitionAxis [1034][1026:1029]
check_rfc_doc VeriDNS.Spec.ClassPartition [1034][1031:1038]
check_rfc_doc VeriDNS.Spec.Zone [1034][1040:1046]
check_rfc_doc VeriDNS.Spec.Zone.name [1034][1047:1052]
rfc_out_of_scope [1034][1053:1065]
check_rfc_doc VeriDNS.Spec.ZoneEvolution [1034][1065:1073]
rfc_proves VeriDNS.Spec.ZoneEvolution.preserves_label [1034][1065:1073]
check_rfc_doc VeriDNS.Spec.ZoneData [1034][1075:1088]
check_rfc_doc VeriDNS.Spec.zone_described_by_RRs [1034][1090:1095]
check_rfc_doc VeriDNS.Spec.zone_authoritative_data [1034][1096:1099]
check_rfc_doc VeriDNS.Spec.topNode_RR_types [1034][1100:1105]
check_rfc_doc VeriDNS.Spec.ns_only_at_zone_top [1034][1106:1123]
check_rfc_doc VeriDNS.Spec.Glue [1034][1124:1136]
rfc_out_of_scope [1034][1138:1149]
check_rfc_doc VeriDNS.Spec.redundant_name_server_support [1034][1150:1161]
check_rfc_doc VeriDNS.Spec.delegation_glue_added_to_parent [1034][1162:1166]
check_rfc_doc VeriDNS.Spec.StandardQuery [1034][1177:1184]
check_rfc_doc VeriDNS.Spec.nonRecursive_response_kinds [1034][1185:1192]
rfc_proves VeriDNS.Spec.nonRecursive_response_kinds_total [1034][1185:1192]
check_rfc_doc VeriDNS.Spec.RecursiveResult [1034][1194:1200]
rfc_proves VeriDNS.Spec.recursive_never_referral [1034][1194:1200]
