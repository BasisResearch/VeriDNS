import VeriDNS.RFC.Macro
import VeriDNS.Spec.Message

namespace VeriDNS.Spec

-- Verify and parse RFC 1034 section 3.1: the semantic model of the domain
-- name space. The tree-structure frame generates the recursive node type
--   inductive Node (R : Type) | mk : ByteArray → Array R → Array (Node R)
-- with projections `label`/`resourceSet`/`children`, plus:
--   node_label_size            — every label is ≤ 63 octets
--   node_brothers_distinct_label — children of one node have distinct labels
--   node_root_label_null       — the root's reserved null label has size 0
--   domainname_labels_on_path  — a node's domain name is the label
--                                projection mapped over its path to the root
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

end VeriDNS.Spec
