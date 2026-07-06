import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Header
import VeriDNS.Spec.Transport
import VeriDNS.Spec.Message
import VeriDNS.RFC.Check
include_rfc [1035][2148:2170] {
6.2. Standard query processing

The major algorithm for standard query processing is presented in
[RFC-1034].

When processing queries with QCLASS=*, or some other QCLASS which
matches multiple classes, the response should never be authoritative
unless the server can guarantee that the response covers all classes.

When composing a response, RRs which are to be inserted in the
additional section, but duplicate RRs in the answer or authority
sections, may be omitted from the additional section.

When a response is so long that truncation is required, the truncation
should start at the end of the response and work forward in the
datagram.  Thus if there is any data for the authority section, the
answer section is guaranteed to be unique.

The MINIMUM value in the SOA should be used to set a floor on the TTL of
data distributed from a zone.  This floor function should be done when
the data is copied into a response.  This will allow future dynamic
update protocols to change the SOA MINIMUM field without ambiguous
semantics.
}include_rfc [1035][2526:2574] {
7.3. Processing responses

The first step in processing arriving response datagrams is to parse the
response.  This procedure should include:

   - Check the header for reasonableness.  Discard datagrams which
     are queries when responses are expected.

   - Parse the sections of the message, and insure that all RRs are
     correctly formatted.

   - As an optional step, check the TTLs of arriving data looking
     for RRs with excessively long TTLs.  If a RR has an
     excessively long TTL, say greater than 1 week, either discard
     the whole response, or limit all TTLs in the response to 1
     week.

The next step is to match the response to a current resolver request.
The recommended strategy is to do a preliminary matching using the ID
field in the domain header, and then to verify that the question section
corresponds to the information currently desired.  This requires that
the transmission algorithm devote several bits of the domain ID field to
a request identifier of some sort.  This step has several fine points:

   - Some name servers send their responses from different
     addresses than the one used to receive the query.  That is, a
     resolver cannot rely that a response will come from the same
     address which it sent the corresponding query to.  This name
     server bug is typically encountered in UNIX systems.

   - If the resolver retransmits a particular request to a name
     server it should be able to use a response from any of the
     transmissions.  However, if it is using the response to sample
     the round trip time to access the name server, it must be able
     to determine which transmission matches the response (and keep
     transmission times for each outgoing message), or only
     calculate round trip times based on initial transmissions.

   - A name server will occasionally not have a current copy of a
     zone which it should have according to some NS RRs.  The
     resolver should simply remove the name server from the current
     SLIST, and continue.
}
@[blueprint "Exchanged"]
structure VeriDNS.Spec.Exchanged (Addr : Type) where
  payload : ByteArray
  source : Addr
  destination : Addr
  localAddr : Addr

def VeriDNS.Spec.processingresponses_limit_ttls : (RR : Type) →
  (ByteArray → Option RR) → (RR → Nat) → (VeriDNS.Spec.Format → Option VeriDNS.Spec.Format) → Prop :=
  fun RR parse ttlOf process =>
  ∀ (resp resp' : VeriDNS.Spec.Format),
    process resp = Option.some resp' →
      ∀ (bytes : ByteArray),
        (bytes ∈ resp'.answer ∨ bytes ∈ resp'.authority) ∨ bytes ∈ resp'.additional →
          ∀ (rr : RR), parse bytes = Option.some rr → ttlOf rr ≤ 604800

@[blueprint "UdpSocket"]
class VeriDNS.Spec.UdpSocket (M : Type → Type) (Sock : Type) (Addr : Type) [Monad M] where
  recvFrom : Sock → Nat → M (ByteArray × Addr)
  sendTo : Sock → ByteArray → Addr → M Unit
  now : M UInt32
  randomId : M UInt16
  exchange : ByteArray → Addr → M (Option (VeriDNS.Spec.Exchanged Addr))
  log : String → M Unit := fun _ => pure ()
