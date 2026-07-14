import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Header
import VeriDNS.Spec.Message
import VeriDNS.Spec.RData
import VeriDNS.RFC.Check

namespace VeriDNS.Spec

def ct_mkResponse (rc : VeriDNS.Spec.Rcode)
    (answers authority additional : Array ByteArray) : VeriDNS.Spec.Format :=
  { header := { (default : VeriDNS.Spec.Header) with
      rcode := rc
      ancount := BitVec.ofNat 16 answers.size
      nscount := BitVec.ofNat 16 authority.size
      arcount := BitVec.ofNat 16 additional.size }
    question := #[]
    answer := answers
    authority := authority
    additional := additional }

theorem ct_nxdomain_type1 :
    let r := ct_mkResponse VeriDNS.Spec.Rcode.nameError
      #[ByteArray.empty]
      #[ByteArray.empty, ByteArray.empty, ByteArray.empty]
      #[ByteArray.empty, ByteArray.empty]
    r.header.rcode = VeriDNS.Spec.Rcode.nameError ∧ r.answer.size = 1
      ∧ r.authority.size = 3 := by
  refine ⟨rfl, rfl, rfl⟩

theorem ct_nxdomain_type2 :
    let r := ct_mkResponse VeriDNS.Spec.Rcode.nameError
      #[ByteArray.empty] #[ByteArray.empty] #[]
    r.header.rcode = VeriDNS.Spec.Rcode.nameError ∧ r.answer.size = 1
      ∧ r.authority.size = 1 ∧ r.additional.size = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem ct_nxdomain_type3 :
    let r := ct_mkResponse VeriDNS.Spec.Rcode.nameError #[ByteArray.empty] #[] #[]
    r.header.rcode = VeriDNS.Spec.Rcode.nameError ∧ r.answer.size = 1
      ∧ r.authority.size = 0 ∧ r.additional.size = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem ct_nxdomain_distinct_from_referral :
    (ct_mkResponse VeriDNS.Spec.Rcode.nameError #[ByteArray.empty] #[] #[]).header.rcode
      ≠ (ct_mkResponse VeriDNS.Spec.Rcode.noError #[] #[] #[]).header.rcode := by
  intro h
  exact VeriDNS.Spec.Rcode.noConfusion h

theorem ct_nodata_type1 :
    let r := ct_mkResponse VeriDNS.Spec.Rcode.noError
      #[]
      #[ByteArray.empty, ByteArray.empty, ByteArray.empty]
      #[ByteArray.empty, ByteArray.empty]
    r.header.rcode = VeriDNS.Spec.Rcode.noError ∧ r.answer.size = 0
      ∧ r.authority.size = 3 := by
  refine ⟨rfl, rfl, rfl⟩

theorem ct_nodata_type2 :
    let r := ct_mkResponse VeriDNS.Spec.Rcode.noError #[] #[ByteArray.empty] #[]
    r.header.rcode = VeriDNS.Spec.Rcode.noError ∧ r.answer.size = 0
      ∧ r.authority.size = 1 ∧ r.additional.size = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem ct_nodata_type3 :
    let r := ct_mkResponse VeriDNS.Spec.Rcode.noError #[] #[] #[]
    r.header.rcode = VeriDNS.Spec.Rcode.noError ∧ r.answer.size = 0
      ∧ r.authority.size = 0 ∧ r.additional.size = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem ct_nodata_shares_rcode_with_referral :
    (ct_mkResponse VeriDNS.Spec.Rcode.noError #[] #[ByteArray.empty] #[]).header.rcode
      = (ct_mkResponse VeriDNS.Spec.Rcode.noError #[]
          #[ByteArray.empty, ByteArray.empty] #[ByteArray.empty, ByteArray.empty]).header.rcode :=
  rfl

/--
   Like normal answers negative answers have a time to live (TTL).  As
   there is no record in the answer section to which this TTL can be
   applied, the TTL must be carried by another method.  This is done by
   including the SOA record from the zone in the authority section of
   the reply.  When the authoritative server creates this record its TTL
   is taken from the minimum of the SOA.MINIMUM field and SOA's TTL.
   This TTL decrements in a similar manner to a normal cached answer and
   upon reaching zero (0) indicates the cached negative answer MUST NOT
   be used again.
-/
def ct_negative_answer_ttl_carried_by_soa
    (soaMinimum soaTtl : BitVec 32) : BitVec 32 :=
  if soaMinimum ≤ soaTtl then soaMinimum else soaTtl

/--
   Negative responses without SOA records SHOULD NOT be cached as there
   is no way to prevent the negative responses looping forever between a
   pair of servers even with a short TTL.
-/
def ct_no_soa_not_cached (soaPresent cached : Bool) : Prop :=
  cached = true → soaPresent = true

/--
   As with caching positive responses it is sensible for a resolver to
   limit for how long it will cache a negative response as the protocol
   supports caching for up to 68 years.  Such a limit should not be
   greater than that applied to positive answers and preferably be
   tunable.  Values of one to three hours have been found to work well
   and would make sensible a default.  Values exceeding one day have
   been found to be problematic.
-/
def ct_negative_cache_limit (negativeLimit positiveLimit : Nat) : Prop :=
  negativeLimit ≤ positiveLimit

/--
   When a server, in answering a query, encounters a cached negative
   response it MUST add the cached SOA record to the authority section
   of the response with the TTL decremented by the amount of time it was
   stored in the cache.  This allows the NXDOMAIN / NODATA response to
   time out correctly.
-/
def ct_served_soa_ttl (cachedTtl storedFor : Nat) : Nat := cachedTtl - storedFor

theorem ct_served_soa_ttl_le (cachedTtl storedFor : Nat) :
    ct_served_soa_ttl cachedTtl storedFor ≤ cachedTtl :=
  Nat.sub_le cachedTtl storedFor

/--
   A cached SOA record must be added to the response.  This was
   explicitly not allowed because previously the distinction between a
   normal cached SOA record, and the SOA cached as a result of a
   negative response was not made, and simply extracting a normal cached
   SOA and adding that to a cached negative response causes problems.
-/
def ct_cached_soa_added_to_response (soaCachedFromNegative soaAdded : Bool) : Prop :=
  soaCachedFromNegative = true → soaAdded = true

/--
its operating system.  User queries will typically be operating system
calls, and the resolver and its cache will be part of the host operating
system.  Less capable hosts may choose to implement the resolver as a
subroutine to be linked in with every program that needs its services.
Resolvers answer user queries with information they acquire via queries
to foreign name servers and the local cache.
-/
def ct_resolver_answers_from_servers_and_cache
    (fromForeignServers fromLocalCache answered : Bool) : Prop :=
  (fromForeignServers = true ∨ fromLocalCache = true) → answered = true

inductive ct_RrField where
  | name
  | type
  | «class»
  | ttl
  | rdlength
  | rdata
  deriving Repr, BEq, Inhabited

def ct_rrFieldOrder : List ct_RrField :=
  [ct_RrField.name, ct_RrField.type, ct_RrField.«class»,
   ct_RrField.ttl, ct_RrField.rdlength, ct_RrField.rdata]

theorem ct_rrFieldOrder_name_first_rdata_last :
    ct_rrFieldOrder.head? = some ct_RrField.name ∧
    ct_rrFieldOrder.getLast? = some ct_RrField.rdata := by
  refine ⟨rfl, rfl⟩

/--
TTL             a 32 bit signed integer that specifies the time interval
                that the resource record may be cached before the source
                of the information should again be consulted.  Zero
                values are interpreted to mean that the RR can only be
                used for the transaction in progress, and should not be
                cached.  For example, SOA records are always distributed
-/
def ct_ttl_zero_not_cached (ttl : BitVec 32) (cacheable : Bool) : Prop :=
  ttl = 0#32 → cacheable = false

/--
The first step a resolver takes is to transform the client's request,
stated in a format suitable to the local OS, into a search specification
for RRs at a specific name which match a specific QTYPE and QCLASS.
-/
structure ct_SearchSpec where
  name : List ByteArray
  qtype : BitVec 16
  qclass : BitVec 16

/--
   - A timestamp indicating the time the request began.
     The timestamp is used to decide whether RRs in the database
     can be used or are out of date.  This timestamp uses the
     absolute time format previously discussed for RR storage in
     zones and caches.  Note that when an RRs TTL indicates a
-/
def ct_request_timestamp (started : Nat) : Nat := started

/--
     The amount of work which a resolver will do in response to a
     client request must be limited to guard against errors in the
     database, such as circular CNAME references, and operational
     problems, such as network partition which prevents the
     resolver from accessing the name servers it needs.  While
-/
def ct_work_must_be_limited (workDone workLimit : Nat) : Prop :=
  workDone ≤ workLimit

/--
     Note that if the resolver structure allows one request to
     start others in parallel, such as when the need to access a
     name server for one request causes a parallel resolve for the
     name server's addresses, the spawned request should be started
     with a lower counter.  This prevents circular references in
-/
def ct_spawned_lower_counter (parentCounter spawnedCounter : Nat) : Prop :=
  spawnedCounter < parentCounter

/--
The information establishes a partial ranking of the available name
server addresses.  Each time an address is chosen and the state should
be altered to prevent its selection again until all other addresses have
been tried.  The timeout for each transmission should be 50-100% greater
-/
def ct_address_not_reselected (chosen : ByteArray) (remaining : List ByteArray) : Prop :=
  chosen ∉ remaining

/--
   - The resolver may encounter a situation where no addresses are
     available for any of the name servers named in SLIST, and
     where the servers in the list are precisely those which would
     normally be used to look up their own addresses.  This
     situation typically occurs when the glue address RRs have a
     smaller TTL than the NS RRs marking delegation, or when the
     resolver caches the result of a NS search.  The resolver
-/
def ct_restart_at_ancestor (noAddresses restartAtAncestor : Bool) : Prop :=
  noAddresses = true → restartAtAncestor = true

/--
   - If a resolver gets a server error or other bizarre response
     from a name server, it should remove it from SLIST, and may
     wish to schedule an immediate transmission to the next
     candidate server address.
-/
def ct_remove_on_error (server : Nat) (slist : List Nat) : List Nat :=
  slist.filter (· != server)

theorem ct_remove_on_error_absent (server : Nat) (slist : List Nat) :
    server ∉ ct_remove_on_error server slist := by
  intro h
  rw [ct_remove_on_error, List.mem_filter] at h
  rw [bne_self_eq_false] at h
  exact absurd h.2 (by decide)

/--
   - The results of an inverse query should not be cached.
-/
def ct_inverse_query_not_cached (fromInverseQuery cached : Bool) : Prop :=
  fromInverseQuery = true → cached = false

/--
   - RR data in responses of dubious reliability.  When a resolver
     receives unsolicited responses or RR data other than that
     requested, it should discard it without caching it.  The basic
     implication is that all sanity checks on a packet should be
     performed before any of it is cached.
-/
def ct_discard_unsolicited (unsolicited cached : Bool) : Prop :=
  unsolicited = true → cached = false

/--
In a similar vein, when a resolver has a set of RRs for some name in a
response, and wants to cache the RRs, it should check its cache for
already existing RRs.  Depending on the circumstances, either the data
in the response or the cache is preferred, but the two should never be
combined.  If the data in the response is from authoritative data in the
-/
def ct_response_and_cache_not_combined (combined : Bool) : Prop := combined = false

end VeriDNS.Spec

rfc_proves VeriDNS.Spec.ct_nxdomain_type1 [2308][145:160]
rfc_proves VeriDNS.Spec.ct_nxdomain_type2 [2308][161:180]
rfc_proves VeriDNS.Spec.ct_nxdomain_type3 [2308][182:193]
rfc_proves VeriDNS.Spec.ct_nxdomain_distinct_from_referral [2308][195:243]
rfc_proves VeriDNS.Spec.ct_nodata_type1 [2308][305:320]
rfc_proves VeriDNS.Spec.ct_nodata_type2 [2308][321:333]
rfc_proves VeriDNS.Spec.ct_nodata_type3 [2308][343:355]
rfc_proves VeriDNS.Spec.ct_nodata_shares_rcode_with_referral [2308][356:376]
check_rfc_doc VeriDNS.Spec.ct_negative_answer_ttl_carried_by_soa [2308][466:474]
check_rfc_doc VeriDNS.Spec.ct_no_soa_not_cached [2308][494:496]
check_rfc_doc VeriDNS.Spec.ct_negative_cache_limit [2308][515:521]
check_rfc_doc VeriDNS.Spec.ct_served_soa_ttl [2308][525:529]
rfc_proves VeriDNS.Spec.ct_served_soa_ttl_le [2308][525:529]
rfc_out_of_scope [2308][603:603]
check_rfc_doc VeriDNS.Spec.ct_cached_soa_added_to_response [2308][610:614]
rfc_out_of_scope [2308][623:623]
check_rfc_doc VeriDNS.Spec.ct_resolver_answers_from_servers_and_cache [1035][205:210]
rfc_proves VeriDNS.Spec.ct_rrFieldOrder_name_first_rdata_last [1035][565:587]
check_rfc_doc VeriDNS.Spec.ct_ttl_zero_not_cached [1035][598:603]
check_rfc_doc VeriDNS.Spec.ct_SearchSpec [1035][2362:2364]
check_rfc_doc VeriDNS.Spec.ct_request_timestamp [1035][2378:2382]
check_rfc_doc VeriDNS.Spec.ct_work_must_be_limited [1035][2397:2409]
check_rfc_doc VeriDNS.Spec.ct_spawned_lower_counter [1035][2419:2423]
check_rfc_doc VeriDNS.Spec.ct_address_not_reselected [1035][2494:2497]
check_rfc_doc VeriDNS.Spec.ct_restart_at_ancestor [1035][2502:2508]
check_rfc_doc VeriDNS.Spec.ct_remove_on_error [1035][2521:2524]
rfc_proves VeriDNS.Spec.ct_remove_on_error_absent [1035][2521:2524]
rfc_out_of_scope [1035][2579:2580]
check_rfc_doc VeriDNS.Spec.ct_inverse_query_not_cached [1035][2593:2593]
check_rfc_doc VeriDNS.Spec.ct_discard_unsolicited [1035][2601:2605]
check_rfc_doc VeriDNS.Spec.ct_response_and_cache_not_combined [1035][2607:2611]
