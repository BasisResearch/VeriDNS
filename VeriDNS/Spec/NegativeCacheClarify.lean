import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Header
import VeriDNS.Spec.Message
import VeriDNS.Spec.RData
import VeriDNS.RFC.Check

namespace VeriDNS.Spec

/--
   Name errors (NXDOMAIN) are indicated by the presence of "Name Error"
   in the RCODE field.  In this case the domain referred to by the QNAME
   does not exist.  Note: the answer section may have SIG and CNAME RRs
-/
def nxdomain_indicated (resp : VeriDNS.Spec.Format) : Prop :=
  resp.header.rcode = VeriDNS.Spec.Rcode.nameError

/--
   It is possible to distinguish between a referral and a NXDOMAIN
   response by the presense of NXDOMAIN in the RCODE regardless of the
   presence of NS or SOA records in the authority section.
-/
def nxdomain_vs_referral (resp : VeriDNS.Spec.Format) : Prop :=
  resp.header.rcode = VeriDNS.Spec.Rcode.nameError

theorem nxdomain_distinct_from_referral (resp : VeriDNS.Spec.Format)
    (h : nxdomain_indicated resp) :
    resp.header.rcode ≠ VeriDNS.Spec.Rcode.noError := by
  simp only [nxdomain_indicated] at h
  rw [h]
  exact fun hc => Rcode.noConfusion hc

/--
   Where no CNAME records appear, the NXDOMAIN response refers to the
   name in the label of the RR in the question section.
-/
def nxdomain_refers_to_qname (cnamesPresent : Bool) (referent qnameLabel : ByteArray) :
    Prop :=
  cnamesPresent = false → referent = qnameLabel

/--
   NODATA is indicated by an answer with the RCODE set to NOERROR and no
   relevant answers in the answer section.  The authority section will
-/
def nodata_response_indicated (resp : VeriDNS.Spec.Format) : Prop :=
  resp.header.rcode = VeriDNS.Spec.Rcode.noError ∧ resp.answer.size = 0

/--
   It is possible to distinguish between a NODATA and a referral
   response by the presence of a SOA record in the authority section or
   the absence of NS records in the authority section.
-/
def nodata_vs_referral (soaInAuthority nsInAuthority : Bool) : Prop :=
  soaInAuthority = true ∨ nsInAuthority = false

/--
   Some name servers fail to set the RCODE to NXDOMAIN in the presence
   of CNAMEs in the answer section.  If a definitive NXDOMAIN / NODATA
   answer is required in this case the resolver must query again using
   the QNAME as the query label.
-/
def requery_with_qname_on_cname (cnamesPresent definitiveRequired requery : Bool) :
    Prop :=
  (cnamesPresent = true ∧ definitiveRequired = true) → requery = true

/--
   If a NXT record was cached along with SOA record it MUST be added to
   the authority section.  If a SIG record was cached along with a NXT
-/
def cached_nxt_added_to_authority (nxtCached nxtInAuthority : Bool) : Prop :=
  nxtCached = true → nxtInAuthority = true

/--
   resolver to locate an authoritative source.  An implicit referral is
   characterised by NS records in the authority section referring the
   resolver towards a authoritative source.  NXDOMAIN types 1 and 4
-/
def implicit_referral (nsInAuthority : Bool) : Prop :=
  nsInAuthority = true

/--
   In either case a resolver MAY cache a server failure response.  If it
   does so it MUST NOT cache it for longer than five (5) minutes, and it
   MUST be cached against the specific query tuple <query name, type,
   class, server IP address>.
-/
def server_failure_cache_ttl (cachedSeconds : Nat) : Prop := cachedSeconds ≤ 300

theorem server_failure_cap_300 :
    server_failure_cache_ttl 300 ∧ ¬ server_failure_cache_ttl 301 := by
  unfold server_failure_cache_ttl
  constructor <;> decide

/--
   indication that the server does not exist or is unreachable.  A
   server may be deemed to be dead or unreachable if it has not
   responded to an outstanding query within 120 seconds.
-/
def dead_server_threshold (unansweredSeconds : Nat) (deemedDead : Bool) : Prop :=
  deemedDead = true → unansweredSeconds ≥ 120

/--
   A server MAY cache a dead server indication.  If it does so it MUST
   NOT be deemed dead for longer than five (5) minutes.  The indication
-/
def dead_server_cache_ttl (deemedDeadSeconds : Nat) : Prop := deemedDeadSeconds ≤ 300

/--
   Negative caching in resolvers is no-longer optional, if a resolver
   caches anything it must also cache negative answers.
-/
def negative_caching_not_optional (cachesAnything cachesNegative : Bool) : Prop :=
  cachesAnything = true → cachesNegative = true

/--
   The SOA record from the authority section MUST be cached.  Name error
-/
def soa_must_be_cached (soaInAuthority soaCached : Bool) : Prop :=
  soaInAuthority = true → soaCached = true

def example_negative_ttl (soa : VeriDNS.Spec.RData.Soa.SoaRdata) (soaTtl : BitVec 32) :
    BitVec 32 :=
  if soa.minimum ≤ soaTtl then soa.minimum else soaTtl

theorem example_initial_soa_ttl :
    example_negative_ttl
      { mname := ByteArray.empty, rname := ByteArray.empty,
        serial := 1997102000#32, refresh := 1800#32, retry := 900#32,
        expire := 604800#32, minimum := 1200#32 } 86400#32 = 1200#32 := by
  decide

end VeriDNS.Spec

check_rfc_doc VeriDNS.Spec.nxdomain_indicated [2308][131:133]
check_rfc_doc VeriDNS.Spec.nxdomain_vs_referral [2308][136:138]
rfc_proves VeriDNS.Spec.nxdomain_distinct_from_referral [2308][129:144]
check_rfc_doc VeriDNS.Spec.nxdomain_refers_to_qname [2308][242:243]
check_rfc_doc VeriDNS.Spec.nodata_response_indicated [2308][276:277]
check_rfc_doc VeriDNS.Spec.nodata_vs_referral [2308][296:298]
check_rfc_doc VeriDNS.Spec.requery_with_qname_on_cname [2308][399:402]
check_rfc_doc VeriDNS.Spec.cached_nxt_added_to_authority [2308][531:532]
check_rfc_doc VeriDNS.Spec.implicit_referral [2308][537:539]
rfc_out_of_scope [2308][544:546]
check_rfc_doc VeriDNS.Spec.server_failure_cache_ttl [2308][572:575]
rfc_proves VeriDNS.Spec.server_failure_cap_300 [2308][548:576]
check_rfc_doc VeriDNS.Spec.dead_server_threshold [2308][581:583]
check_rfc_doc VeriDNS.Spec.dead_server_cache_ttl [2308][591:592]
check_rfc_doc VeriDNS.Spec.negative_caching_not_optional [2308][600:601]
check_rfc_doc VeriDNS.Spec.soa_must_be_cached [2308][605:605]
rfc_proves VeriDNS.Spec.example_initial_soa_ttl [2308][791:858]
rfc_out_of_scope [2308][859:886]
