import VeriDNS.RFC.Macro
import VeriDNS.Spec.Header
import VeriDNS.Spec.Transport
import VeriDNS.Spec.Message

namespace VeriDNS.Spec

-- RFC 1035 §6.2: Standard query processing — response composition rules
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
}

-- RFC 1035 §7.3: Processing responses — response validation rules
include_rfc [1035][2526:2574] {
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

/-- Abstract UDP socket operations. Parametric over monad M, socket type Sock,
    and address type Addr. Follows the CacheLookup pattern: manual typeclass
    extending NLP-generated transport specs. -/
class UdpSocket (M : Type → Type) (Sock Addr : Type) [Monad M] where
  recvFrom : Sock → Nat → M (ByteArray × Addr)
  sendTo : Sock → ByteArray → Addr → M Unit
  /-- Absolute time in seconds, for cache expiry (RFC 1035 §6.1.3). -/
  now : M UInt32
  /-- Unpredictable query ID for outgoing queries (RFC 5452 resilience). -/
  randomId : M UInt16
  /-- One connected query exchange (RFC 5452 §9.1/§9.2): a fresh socket per
      exchange gives an unpredictable ephemeral local port, and connecting it
      makes the kernel discard datagrams whose source address/port do not
      match the queried server. Returns `none` on timeout. -/
  exchange : ByteArray → Addr → M (Option ByteArray)
  /-- Diagnostic log hook (default: silent). -/
  log : String → M Unit := fun _ => pure ()

end VeriDNS.Spec
