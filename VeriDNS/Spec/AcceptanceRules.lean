import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.NameTree
import VeriDNS.Spec.RRType
import VeriDNS.Spec.NetworkSemantics
import VeriDNS.RFC.Check

namespace VeriDNS.Spec

/--
   When certain steps are taken, it is feasible to "spoof" the current
   deployed majority of resolvers with carefully crafted and timed DNS
   packets.  Once spoofed, a caching server will repeat the data it
   wrongfully accepted, and make its clients contact the wrong, and
   possibly malicious, servers.

-/
def spoofing_feasible (craftedTimedPackets resolverSpoofed : Prop) : Prop :=
  craftedTimedPackets → resolverSpoofed

/--

   DNS data is to be accepted by a resolver if and only if:

   1.  The question section of the reply packet is equivalent to that of
       a question packet currently waiting for a response.

   2.  The ID field of the reply packet matches that of the question
       packet.

   3.  The response comes from the same network address to which the
       question was sent.

   4.  The response comes in on the same network address, including port
       number, from which the question was sent.

-/
@[blueprint "AcceptanceConditions"]
structure AcceptanceConditions where
  questionMatches : Prop
  idMatches : Prop
  sourceAddressMatches : Prop
  destAddressPortMatches : Prop

def acceptResponse (c : AcceptanceConditions) : Prop :=
  c.questionMatches ∧ c.idMatches ∧ c.sourceAddressMatches ∧ c.destAddressPortMatches

theorem accept_requires_id_match (c : AcceptanceConditions)
    (h : acceptResponse c) : c.idMatches := h.2.1

theorem accept_requires_question_match (c : AcceptanceConditions)
    (h : acceptResponse c) : c.questionMatches := h.1

theorem accept_requires_source_match (c : AcceptanceConditions)
    (h : acceptResponse c) : c.sourceAddressMatches := h.2.2.1

/--

   DNS packets, both queries and responses, contain a question section.
   Incoming responses should be verified to have a question section that
   is equivalent to that of the outgoing query.

-/
def question_section_must_match (replyQuestion outgoingQuestion : ByteArray) : Prop :=
  replyQuestion = outgoingQuestion

/--
4.3.  Matching the ID Field

   The DNS ID field is 16 bits wide, meaning that if full use is made of
   all these bits, and if their contents are truly random, it will
   require on average 32768 attempts to guess.  Anecdotal evidence
   suggests there are implementations utilizing only 14 bits, meaning on
   average 8192 attempts will suffice.

   Additionally, if the target nameserver can be forced into having
   multiple identical queries outstanding, the "Birthday Attack"
   phenomenon means that any fake data sent by the attacker is matched
   against multiple outstanding queries, significantly raising the
   chance of success.  Further details in Section 5.

-/
def id_field_width : Nat := 16

/--
4.4.  Matching the Source Address of the Authentic Response

   It should be noted that meeting this condition entails being able to
   transmit packets on behalf of the address of the authoritative
   nameserver.  While two Best Current Practice documents ([RFC2827] and
   [RFC3013] specifically) direct Internet access providers to prevent
   their customers from assuming IP addresses that are not assigned to
   them, these recommendations are not universally (nor even widely)
   implemented.

   Many zones have two or three authoritative nameservers, which make
   matching the source address of the authentic response very likely
   with even a naive choice having a double digit success rate.

   Most recursing nameservers store relative performance indications of
   authoritative nameservers, which may make it easier to predict which
   nameserver would originally be queried -- the one most likely to
   respond the quickest.

   Generally, this condition requires at most two or three attempts
   before it is matched.
-/
def source_address_match_likely (authoritativeServerCount : Nat) : Prop :=
  authoritativeServerCount ≤ 3

/--
4.5.  Matching the Destination Address and Port of the Authentic
      Response

   Note that the destination address of the authentic response is the
   source address of the original query.

   The actual address of a recursing nameserver is generally known; the
   port used for asking questions is harder to determine.  Most current
   resolvers pick an arbitrary port at startup (possibly at random) and
   use this for all outgoing queries.  In quite a number of cases, the
   source port of outgoing questions is fixed at the traditional DNS
   assigned server port number of 53.

   If the source port of the original query is random, but static, any
   authoritative nameserver under observation by the attacker can be
   used to determine this port.  This means that matching this
   conditions often requires no guess work.

   If multiple ports are used for sending queries, this enlarges the
   effective ID space by a factor equal to the number of ports used.

   Less common resolving servers choose a random port per outgoing
   query.  If this strategy is followed, this port number can be
   regarded as an additional ID field, again containing up to 16 bits.

   If the maximum ports range is utilized, on average, around 32256
   source ports would have to be tried before matching the source port
   of the original query, as ports below 1024 may be unavailable for
   use, leaving 64512 options.

   It is in general safe for DNS to use ports in the range 1024-49152
   even though some of these ports are allocated to other protocols.
   DNS resolvers will not be able to use any ports that are already in
   use.  If a DNS resolver uses a port, it will release that port after
   a short time and migrate to a different port.  Only in the case of a
   high-volume resolver is it possible that an application wanting a
   particular UDP port suffers a long term block-out.

   It should be noted that a firewall will not prevent the matching of
   this address, as it will accept answers that (appear to) come from
   the correct address, offering no additional security.

-/
def ports_enlarge_id_space (idSpace portsUsed : Nat) : Nat := idSpace * portsUsed

/--
4.6.  Have the Response Arrive before the Authentic Response

   Once any packet has matched the previous four conditions (plus
   possible additional conditions), no further responses are generally
   accepted.
-/
def first_match_accepted (alreadyMatched acceptFurther : Prop) : Prop :=
  alreadyMatched → ¬ acceptFurther

/--

5.  Birthday Attacks

   The so-called "birthday paradox" implies that a group of 23 people
   suffices to have a more than even chance of having two or more
   members of the group share a birthday.

   An attacker can benefit from this exact phenomenon if it can force
   the target resolver to have multiple equivalent (identical QNAME,
   QTYPE, and QCLASS) outstanding queries at any one time to the same
   authoritative server.

   Any packet the attacker sends then has a much higher chance of being
   accepted because it only has to match any of the outstanding queries
   for that single domain.  Compared to the birthday analogy above, of
   the group composed of queries and responses, the chance of having any
   of these share an ID rises quickly.

   As long as small numbers of queries are sent out, the chance of
   successfully spoofing a response rises linearly with the number of
   outstanding queries for the exact domain and nameserver.

   For larger numbers, this effect is less pronounced.

   More details are available in US-CERT [vu-457875].

-/
def birthday_paradox_group : Nat := 23

/--
6.  Accepting Only In-Domain Records

   Responses from authoritative nameservers often contain information
   that is not part of the zone for which we deem it authoritative.  As
   an example, a query for the MX record of a domain might get as its
   responses a mail exchanger in another domain, and additionally the IP
   address of this mail exchanger.

   If accepted uncritically, the resolver stands the chance of accepting
   data from an untrusted source.  Care must be taken to only accept
   data if it is known that the originator is authoritative for the
   QNAME or a parent of the QNAME.
   One very simple way to achieve this is to only accept data if it is
   part of the domain for which the query was intended.

-/
def accept_only_in_domain (recordName qname : List ByteArray) (accepted : Prop) : Prop :=
  accepted → VeriDNS.Spec.isSubdomain recordName qname

/--
7.  Combined Difficulty

   Given a known or static destination port, matching ID field, the
   source and destination address requires on average in the order of 2
   * 2^15 = 65000 packets, assuming a zone has 2 authoritative
   nameservers.

   If the window of opportunity available is around 100 ms, as assumed
   above, an attacker would need to be able to briefly transmit 650000
   packets/s to have a 50% chance to get spoofed data accepted on the
   first attempt.

   A realistic minimal DNS response consists of around 80 bytes,
   including IP headers, making the packet rate above correspond to a
   respectable burst of 416 Mbit/s.

   As of mid-2006, this kind of bandwidth was not common but not scarce
   either, especially among those in a position to control many servers.

   These numbers change when a window of a full second is assumed,
   possibly because the arrival of the authentic response can be
   prevented by overloading the bona fide authoritative hosts with decoy
   queries.  This reduces the needed bandwidth to 42 Mbit/s.

   If, in addition, the attacker is granted more than a single chance
   and allowed up to 60 minutes of work on a domain with a time to live
   of 300 seconds, a meager 4 Mbit/s suffices for a 50% chance at
   getting fake data accepted.  Once equipped with a longer time,
   matching condition 1 mentioned above is straightforward -- any
   popular domain will have been queried a number of times within this
   hour, and given the short TTL, this would lead to queries to
   authoritative nameservers, opening windows of opportunity.

-/
def combined_difficulty_packets : Nat := 2 * 2 ^ 15

theorem combined_difficulty_packets_value : combined_difficulty_packets = 65536 := by decide

end VeriDNS.Spec

check_rfc_doc VeriDNS.Spec.spoofing_feasible [5452][247:252]
check_rfc_doc VeriDNS.Spec.AcceptanceConditions [5452][262:276]
rfc_proves VeriDNS.Spec.accept_requires_id_match [5452][263:278]
rfc_proves VeriDNS.Spec.accept_requires_id_match [5452][349:353]
rfc_proves VeriDNS.Spec.accept_requires_question_match [5452][277:286]
check_rfc_doc VeriDNS.Spec.question_section_must_match [5452][349:353]
check_rfc_doc VeriDNS.Spec.id_field_width [5452][354:367]
check_rfc_doc VeriDNS.Spec.source_address_match_likely [5452][368:388]
check_rfc_doc VeriDNS.Spec.ports_enlarge_id_space [5452][399:440]
check_rfc_doc VeriDNS.Spec.first_match_accepted [5452][441:445]
check_rfc_doc VeriDNS.Spec.birthday_paradox_group [5452][463:488]
check_rfc_doc VeriDNS.Spec.accept_only_in_domain [5452][489:513]
rfc_proves VeriDNS.Spec.Net.out_of_bailiwick_glue_rejected [5452][489:513]
check_rfc_doc VeriDNS.Spec.combined_difficulty_packets [5452][514:546]
