import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Message
import VeriDNS.Spec.RData
import VeriDNS.RFC.Check
include_rfc [2308][274:279] {
2.2 - No Data

   NODATA is indicated by an answer with the RCODE set to NOERROR and no
   relevant answers in the answer section.  The authority section will
   contain an SOA record, or there will be no NS records there.
}include_rfc [2308][404:416] {
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
}include_rfc [2308][464:521] {
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
}include_rfc [2308][523:529] {
6 - Negative answers from the cache

   When a server, in answering a query, encounters a cached negative
   response it MUST add the cached SOA record to the authority section
   of the response with the TTL decremented by the amount of time it was
   stored in the cache.  This allows the NXDOMAIN / NODATA response to
   time out correctly.
}
def VeriDNS.Spec.obligation_addCachedSoaRecordToAuthoritySection : (σ RR : Type) → (σ → Bool) → (σ → Option RR) → (σ → RR → RR) → (σ → Array RR) → Prop :=
  fun σ RR encountersCachedNegativeResponse cachedSoaRecord withTtlDecremented authoritySection =>
  ∀ (s : σ),
    encountersCachedNegativeResponse s = Bool.true →
      ∀ (rr : RR), cachedSoaRecord s = Option.some rr → withTtlDecremented s rr ∈ authoritySection s

@[blueprint "NegativeCacheSpec"]
class VeriDNS.Spec.NegativeCacheSpec (C : Type) where
  cacheNegative : C → ByteArray → BitVec 16 → BitVec 16 → VeriDNS.Spec.Rcode → UInt32 → C
  retrieveNegative : C → ByteArray → BitVec 16 → BitVec 16 → UInt32 → Option VeriDNS.Spec.Rcode

@[blueprint "NegativeAuthoritySpec"]
class VeriDNS.Spec.NegativeAuthoritySpec (C : Type) (RR : Type) extends VeriDNS.Spec.NegativeCacheSpec C where
  storeSoaRecord : C → ByteArray → BitVec 16 → BitVec 16 → RR → UInt32 → C
  authoritySection : C → ByteArray → BitVec 16 → BitVec 16 → UInt32 → Array RR

def VeriDNS.Spec.cachingnegativeanswers_limit_negativeresponse_ttl : (σ : Type) → (σ → Nat) → Prop :=
  fun σ cachedTtl => ∀ (s : σ), cachedTtl s ≤ 10800

def VeriDNS.Spec.cachingnegativeanswers_nameError_retrieval : (σ ρ : Type) → (σ → ByteArray → BitVec 16 → BitVec 16 → ρ) → Prop :=
  fun σ ρ retrieve =>
  ∀ (s : σ) (qname : ByteArray) (qtype qtype' qclass : BitVec 16),
    retrieve s qname qtype qclass = retrieve s qname qtype' qclass

def VeriDNS.Spec.negativeanswersfromauthoritativeservers_negative_ttl : (VeriDNS.Spec.RData.Soa.SoaRdata → BitVec 32 → BitVec 32) → Prop :=
  fun negTtl =>
  ∀ (r : VeriDNS.Spec.RData.Soa.SoaRdata) (t : BitVec 32),
    negTtl r t = if r.minimum ≤ t then r.minimum else t

def VeriDNS.Spec.nodata_indicated : VeriDNS.Spec.Format → Prop :=
  fun resp => resp.header.rcode = VeriDNS.Spec.Rcode.noError ∧ resp.answer.size = 0
