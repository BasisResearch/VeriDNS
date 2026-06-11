import VeriDNS.RFC.Macro
import VeriDNS.Spec.Message

namespace VeriDNS.Spec

-- RFC 2181 §5.4.1: data ranking. The ranked-list rule ("in order from most
-- to least:" + "+"-bullets) generates the ordered `Credibility` enum (ctor
-- order = rank; `toCode` is the rank, 0 most trustworthy), the
-- `Credibility.atLeastAsTrustworthy` order relation, and — from "should not
-- be cached in such a way that they would ever be returned as answers" —
-- `obligation_untrustworthyNotAnswerable`: max-rank data is never served as
-- an answer. Instantiated by the cache's credibility tagging
-- (Impl/Cache.lean, proven in Proof/Cache.lean).
include_rfc [2181][343:384] {
5.4.1. Ranking data

   When considering whether to accept an RRSet in a reply, or retain an
   RRSet already in its cache instead, a server should consider the
   relative likely trustworthiness of the various data.  An
   authoritative answer from a reply should replace cached data that had
   been obtained from additional information in an earlier reply.
   However additional information from a reply will be ignored if the
   cache contains data from an authoritative answer or a zone file.

   The accuracy of data available is assumed from its source.
   Trustworthiness shall be, in order from most to least:

     + Data from a primary zone file, other than glue data,
     + Data from a zone transfer, other than glue,
     + The authoritative data included in the answer section of an
       authoritative reply.
     + Data from the authority section of an authoritative answer,
     + Glue from a primary zone, or glue from a zone transfer,
     + Data from the answer section of a non-authoritative answer, and
       non-authoritative data from the answer section of authoritative
       answers,
     + Additional information from an authoritative answer,
       Data from the authority section of a non-authoritative answer,
       Additional information from non-authoritative answers.

   Note that the answer section of an authoritative answer normally
   contains only authoritative data.  However when the name sought is an
   alias (see section 10.1.1) only the record describing that alias is
   necessarily authoritative.  Clients should assume that other records
   may have come from the server's cache.  Where authoritative answers
   are required, the client should query again, using the canonical name
   associated with the alias.

   Unauthenticated RRs received and cached from the least trustworthy of
   those groupings, that is data from the additional data section, and
   data from the authority section of a non-authoritative answer, should
   not be cached in such a way that they would ever be returned as
   answers to a received query.  They may be returned as additional
   information where appropriate.  Ignoring this would allow the
   trustworthiness of relatively untrustworthy data to be increased
   without cause or excuse.
}

end VeriDNS.Spec
