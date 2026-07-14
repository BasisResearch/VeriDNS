import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Header
import VeriDNS.RFC.Check
include_rfc [1035][1752:1779] {
4.2.1. UDP usage

Messages sent using UDP user server port 53 (decimal).

Messages carried by UDP are restricted to 512 bytes (not counting the IP
or UDP headers).  Longer messages are truncated and the TC bit is set in
the header.

UDP is not acceptable for zone transfers, but is the recommended method
for standard queries in the Internet.  Queries sent using UDP may be
lost, and hence a retransmission strategy is required.  Queries or their
responses may be reordered by the network, or by processing in name
servers, so resolvers should not depend on them being returned in order.

The optimal UDP retransmission policy will vary with performance of the
Internet and the needs of the client, but the following are recommended:

   - The client should try other servers and server addresses
     before repeating a query to a specific address of a server.

   - The retransmission interval should be based on prior
     statistics if possible.  Too aggressive retransmission can
     easily slow responses for the community at large.  Depending
     on how well connected the client is to its expected servers,
     the minimum retransmission interval should be 2-5 seconds.

More suggestions on server selection and retransmission policy can be
found in the resolver section of this memo.
}include_rfc [1035][1781:1816] {
4.2.2. TCP usage

Messages sent over TCP connections use server port 53 (decimal).  The
message is prefixed with a two byte length field which gives the message
length, excluding the two byte length field.  This length field allows
the low-level processing to assemble a complete message before beginning
to parse it.

Several connection management policies are recommended:

   - The server should not block other activities waiting for TCP
     data.

   - The server should support multiple connections.

   - The server should assume that the client will initiate
     connection closing, and should delay closing its end of the
     connection until all outstanding client requests have been
     satisfied.

   - If the server needs to close a dormant connection to reclaim
     resources, it should wait until the connection has been idle
     for a period on the order of two minutes.  In particular, the
     server should allow the SOA and AXFR request sequence (which
     begins a refresh operation) to be made on a single connection.
     Since the server would be unable to answer queries anyway, a
     unilateral close or reset may be used instead of a graceful
     close.
}
def VeriDNS.Spec.tcpusage_limit_0 : Nat :=
  53

@[blueprint "UdpUsage"]
structure VeriDNS.Spec.UdpUsage  where
  data : ByteArray
  deriving BEq, Inhabited

def VeriDNS.Spec.udpusage_prop_1 : VeriDNS.Spec.UdpUsage → VeriDNS.Spec.Header → Prop :=
  fun msg ext => msg.data.size > 512 → ext.tc = 1

def VeriDNS.Spec.udpusage_limit_0 : Nat :=
  53

def VeriDNS.Spec.udpusage_limit_1 : Nat :=
  512

def VeriDNS.Spec.udpusage_prop_0 : VeriDNS.Spec.UdpUsage → Prop :=
  fun msg => msg.data.size ≤ 512

@[blueprint "TcpUsage"]
structure VeriDNS.Spec.TcpUsage  where
  lengthfield : BitVec 16
  data : ByteArray
  deriving BEq, Inhabited

def VeriDNS.Spec.tcpusage_prop_0 : VeriDNS.Spec.TcpUsage → Prop :=
  fun msg => msg.lengthfield.toNat = msg.data.size
