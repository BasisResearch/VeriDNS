import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Header
import VeriDNS.Spec.Question
import VeriDNS.RFC.Check
include_rfc [1035][1351:1400] {
4.1. Format

All communications inside of the domain protocol are carried in a single
format called a message.  The top level format of message is divided
into 5 sections (some of which are empty in certain cases) shown below:

    +---------------------+
    |        Header       |
    +---------------------+
    |       Question      | the question for the name server
    +---------------------+
    |        Answer       | RRs answering the question
    +---------------------+
    |      Authority      | RRs pointing toward an authority
    +---------------------+
    |      Additional     | RRs holding additional information
    +---------------------+

The header section is always present.  The header includes fields that
specify which of the remaining sections are present, and also specify
whether the message is a query or a response, a standard query or some
other opcode, etc.

The names of the sections after the header are derived from their use in
standard queries.  The question section contains fields that describe a
question to a name server.  These fields are a query type (QTYPE), a
query class (QCLASS), and a query domain name (QNAME).  The last three
sections have the same format: a possibly empty list of concatenated
resource records (RRs).  The answer section contains RRs that answer the
question; the authority section contains RRs that point toward an
authoritative name server; the additional records section contains RRs
which relate to the query, but are not strictly answers for the
question.
}
@[blueprint "Format", uses := ["header", "Question", "ResourceRecord"]]
structure VeriDNS.Spec.Format  where
  header : VeriDNS.Spec.Header
  question : Array VeriDNS.Spec.Question
  answer : Array ByteArray
  authority : Array ByteArray
  additional : Array ByteArray
  deriving BEq, Inhabited

def VeriDNS.Spec.format_question_qname_valid : (ByteArray → Array ByteArray) → VeriDNS.Spec.Format → Prop :=
  fun labels msg =>
  ∀ (i : Nat) (hi : i < msg.question.size) (l : ByteArray),
    l ∈ labels msg.question[i].qname → 0 < l.size ∧ l.size ≤ 63

def VeriDNS.Spec.format_qdcount_counts_question : VeriDNS.Spec.Format → Prop :=
  fun msg => msg.header.qdcount.toNat = msg.question.size

def VeriDNS.Spec.format_arcount_counts_additional : VeriDNS.Spec.Format → Prop :=
  fun msg => msg.header.arcount.toNat = msg.additional.size

def VeriDNS.Spec.format_nscount_counts_authority : VeriDNS.Spec.Format → Prop :=
  fun msg => msg.header.nscount.toNat = msg.authority.size

def VeriDNS.Spec.format_ancount_counts_answer : VeriDNS.Spec.Format → Prop :=
  fun msg => msg.header.ancount.toNat = msg.answer.size
