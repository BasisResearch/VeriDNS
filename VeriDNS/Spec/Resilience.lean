import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check
include_rfc [5452][704:765] {
9.1.  Query Matching Rules

   A resolver implementation MUST match responses to all of the
   following attributes of the query:

   o  Source address against query destination address

   o  Destination address against query source address

   o  Destination port against query source port

   o  Query ID

   o  Query name

   o  Query class and type

   before applying DNS trustworthiness rules (see Section 5.4.1 of
   [RFC2181]).

   A mismatch and the response MUST be considered invalid.
9.2.  Extending the Q-ID Space by Using Ports and Addresses

   Resolver implementations MUST:

   o  Use an unpredictable source port for outgoing queries from the
      range of available ports (53, or 1024 and above) that is as large
      as possible and practicable;

   o  Use multiple different source ports simultaneously in case of
      multiple outstanding queries;

   o  Use an unpredictable query ID for outgoing queries, utilizing the
      full range available (0-65535).

   Resolvers that have multiple IP addresses SHOULD use them in an
   unpredictable manner for outgoing queries.

   Resolver implementations SHOULD provide means to avoid usage of
   certain ports.

   Resolvers SHOULD favor authoritative nameservers with which a trust
   relation has been established; stub-resolvers SHOULD be able to use
   Transaction Signature (TSIG) ([RFC2845]) or IPsec ([RFC4301]) when
   communicating with their recursive resolver.

   In case a cryptographic verification of response validity is
   available (TSIG, SIG(0)), resolver implementations MAY waive above
   rules, and rely on this guarantee instead.

   Proper unpredictability can be achieved by employing a high quality
   (pseudo-)random generator, as described in [RFC4086].
}
/--
9.1.  Query Matching Rules

   A resolver implementation MUST match responses to all of the
   following attributes of the query:

   o  Source address against query destination address

   o  Destination address against query source address

   o  Destination port against query source port

   o  Query ID

   o  Query name

   o  Query class and type

   before applying DNS trustworthiness rules (see Section 5.4.1 of
   [RFC2181]).

   A mismatch and the response MUST be considered invalid.

-/
def VeriDNS.Spec.querymatchingrules_match_obligation : (ρ : Type) →
  (ρ → Bool) → (ρ → Bool) → (ρ → Bool) → (ρ → Bool) → (ρ → Bool) → (ρ → Bool) → (ρ → Bool) → Prop :=
  fun ρ accepted sourceAddress destinationAddress destinationPort queryId queryName
    queryClassAndType =>
  ∀ (r : ρ),
    accepted r = Bool.true →
      ((((sourceAddress r = Bool.true ∧ destinationAddress r = Bool.true) ∧
              destinationPort r = Bool.true) ∧
            queryId r = Bool.true) ∧
          queryName r = Bool.true) ∧
        queryClassAndType r = Bool.true

/--
9.2.  Extending the Q-ID Space by Using Ports and Addresses

   Resolver implementations MUST:

   o  Use an unpredictable source port for outgoing queries from the
      range of available ports (53, or 1024 and above) that is as large
      as possible and practicable;

   o  Use multiple different source ports simultaneously in case of
      multiple outstanding queries;

   o  Use an unpredictable query ID for outgoing queries, utilizing the
      full range available (0-65535).

   Resolvers that have multiple IP addresses SHOULD use them in an
   unpredictable manner for outgoing queries.

   Resolver implementations SHOULD provide means to avoid usage of
   certain ports.

   Resolvers SHOULD favor authoritative nameservers with which a trust
   relation has been established; stub-resolvers SHOULD be able to use
   Transaction Signature (TSIG) ([RFC2845]) or IPsec ([RFC4301]) when
   communicating with their recursive resolver.

   In case a cryptographic verification of response validity is
   available (TSIG, SIG(0)), resolver implementations MAY waive above
   rules, and rely on this guarantee instead.

   Proper unpredictability can be achieved by employing a high quality
   (pseudo-)random generator, as described in [RFC4086].
-/
def VeriDNS.Spec.resolver_qid_space_must
    (unpredictableSourcePort multipleSourcePorts unpredictableQueryId : Prop) : Prop :=
  unpredictableSourcePort ∧ multipleSourcePorts ∧ unpredictableQueryId

check_rfc_doc VeriDNS.Spec.querymatchingrules_match_obligation [5452][704:727]
check_rfc_doc VeriDNS.Spec.resolver_qid_space_must [5452][728:765]
