import VeriDNS.RFC.Macro
import VeriDNS.Spec.Message
import VeriDNS.Spec.RData

namespace VeriDNS.Spec

-- RFC 2308: negative caching of DNS queries (NXDOMAIN / NODATA).
-- §2.2 derives `nodata_indicated` (rcode = noError ∧ answer empty) via the
-- "is indicated by" rule; the implementation detects NODATA with it
-- (Impl/Resolver.lean) and the conformance proof connects them
-- (Proof/Cache.lean).
include_rfc [2308][274:279] {
2.2 - No Data

   NODATA is indicated by an answer with the RCODE set to NOERROR and no
   relevant answers in the answer section.  The authority section will
   contain an SOA record, or there will be no NS records there.
}

-- §3 derives `negativeanswers_negative_ttl`: the TTL a resolver may cache a
-- negative answer for is min(SOA.MINIMUM, the SOA record's own TTL), via the
-- minimum-of-two-fields rule. Instantiated by `computeNegativeTtl`
-- (Impl/Server.lean, proven in Proof/Cache.lean).
include_rfc [2308][404:416] {
3 - Negative Answers from Authoritative Servers

   Name servers authoritative for a zone MUST include the SOA record of
   the zone in the authority section of the response when reporting an
   NXDOMAIN or indicating that no data of the requested type exists.
   This is required so that the response may be cached.  The TTL of this
   record is set from the minimum of the MINIMUM field of the SOA record
   and the TTL of the SOA itself, and indicates how long a resolver may
   cache the negative answer.  The TTL SIG record associated with the
   SOA record should also be trimmed in line with the SOA's TTL.

   If the containing zone is signed [RFC2065] the SOA and appropriate
   NXT and SIG records MUST be added.
}

-- §5 derives `cachingnegativeanswers_nameError_retrieval` via the
-- tuple-key rule: the tuple "<QNAME, QCLASS>" is one lexical token; the
-- keyed PP ("for the same ⟨tuple⟩") is found grammatically; the answer
-- class resolves through the enum machinery ("resulted from a name error"
-- → Rcode.nameError). The omitted QTYPE renders as qtype-invariance of the
-- abstract retrieve function (an NXDOMAIN answers EVERY type at that
-- name). The NODATA sentence names all three fields, so no invariance is
-- generated for it (per-type keying is the existing lookup behavior).
-- Instantiated by `DnsCache.lookupNxdomain` (Proof/Cache.lean).
--
-- The closing paragraph derives `cachingnegativeanswers_limit_negativeresponse_ttl`
-- via the duration-cap rule: the capped entity is the object NP of "cache"
-- in the limit sentence ("… limit for how long it will cache a negative
-- response …"), and the bound is the upper end of the parsed
-- ⟨numeral to numeral time-unit⟩ range in "Values of one to three hours …
-- would make sensible a default" (10800 seconds). Instantiated by
-- `capNegativeTtl` (Impl/Server.lean, proven in Proof/Cache.lean).
include_rfc [2308][464:521] {
5 - Caching Negative Answers

   Like normal answers negative answers have a time to live (TTL).  As
   there is no record in the answer section to which this TTL can be
   applied, the TTL must be carried by another method.  This is done by
   including the SOA record from the zone in the authority section of
   the reply.  When the authoritative server creates this record its TTL
   is taken from the minimum of the SOA.MINIMUM field and SOA's TTL.
   This TTL decrements in a similar manner to a normal cached answer and
   upon reaching zero (0) indicates the cached negative answer MUST NOT
   be used again.

   A negative answer that resulted from a name error (NXDOMAIN) should
   be cached such that it can be retrieved and returned in response to
   another query for the same <QNAME, QCLASS> that resulted in the
   cached negative response.

   A negative answer that resulted from a no data error (NODATA) should
   be cached such that it can be retrieved and returned in response to
   another query for the same <QNAME, QTYPE, QCLASS> that resulted in
   the cached negative response.

   The NXT record, if it exists in the authority section of a negative
   answer received, MUST be stored such that it can be be located and
   returned with SOA record in the authority section, as should any SIG
   records in the authority section.  For NXDOMAIN answers there is no
   "necessary" obvious relationship between the NXT records and the
   QNAME.  The NXT record MUST have the same owner name as the query
   name for NODATA responses.

   Negative responses without SOA records SHOULD NOT be cached as there
   is no way to prevent the negative responses looping forever between a
   pair of servers even with a short TTL.

   Despite the DNS forming a tree of servers, with various mis-
   configurations it is possible to form a loop in the query graph, e.g.
   two servers listing each other as forwarders, various lame server
   configurations.  Without a TTL count down a cache negative response
   when received by the next server would have its TTL reset.  This
   negative indication could then live forever circulating between the
   servers involved.

   As with caching positive responses it is sensible for a resolver to
   limit for how long it will cache a negative response as the protocol
   supports caching for up to 68 years.  Such a limit should not be
   greater than that applied to positive answers and preferably be
   tunable.  Values of one to three hours have been found to work well
   and would make sensible a default.  Values exceeding one day have
   been found to be problematic.
}

-- §6 derives `obligation_addCachedSoaRecordToAuthoritySection` via the
-- MUST-add-to rule: the when-clause guard ("encounters a cached negative
-- response"), the imperative's object NP ("the cached SOA record"), the
-- "to" PP target ("the authority section"), and the "with" PP's
-- head-noun + participle transform ("the TTL decremented …") are all read
-- from the parse. Instantiated by the negative-answer path in
-- Impl/Server.lean (proven in Proof/Cache.lean).
include_rfc [2308][523:529] {
6 - Negative answers from the cache

   When a server, in answering a query, encounters a cached negative
   response it MUST add the cached SOA record to the authority section
   of the response with the TTL decremented by the amount of time it was
   stored in the cache.  This allows the NXDOMAIN / NODATA response to
   time out correctly.
}

end VeriDNS.Spec
