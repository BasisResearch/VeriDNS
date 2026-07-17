import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.RFC.Check
include_rfc [1035][1572:1632] {
4.1.3. Resource record format

The answer, authority, and additional sections all share the same
format: a variable number of resource records, where the number of
records is specified in the corresponding count field in the header.
Each resource record has the following format:
                                    1  1  1  1  1  1
      0  1  2  3  4  5  6  7  8  9  0  1  2  3  4  5
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    |                                               |
    /                                               /
    /                      NAME                     /
    |                                               |
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    |                      TYPE                     |
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    |                     CLASS                     |
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    |                      TTL                      |
    |                                               |
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    |                   RDLENGTH                    |
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--|
    /                     RDATA                     /
    /                                               /
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

where:

NAME            a domain name to which this resource record pertains.

TYPE            two octets containing one of the RR type codes.  This
                field specifies the meaning of the data in the RDATA
                field.

CLASS           two octets which specify the class of the data in the
                RDATA field.

TTL             a 32 bit unsigned integer that specifies the time
                interval (in seconds) that the resource record may be
                cached before it should be discarded.  Zero values are
                interpreted to mean that the RR can only be used for the
                transaction in progress, and should not be cached.
RDLENGTH        an unsigned 16 bit integer that specifies the length in
                octets of the RDATA field.

RDATA           a variable length string of octets that describes the
                resource.  The format of this information varies
                according to the TYPE and CLASS of the resource record.
                For example, the if the TYPE is A and the CLASS is IN,
                the RDATA field is a 4 octet ARPA Internet address.
}
@[blueprint "ResourceRecord", uses := ["RData.A.ARdata", "RData.Ns.NsRdata",
  "RData.Md.MdRdata", "RData.Mf.MfRdata", "RData.Cname.CnameRdata", "RData.Soa.SoaRdata",
  "RData.Mb.MbRdata", "RData.Mg.MgRdata", "RData.Mr.MrRdata", "RData.Null.NullRdata",
  "RData.Wks.WksRdata", "RData.Ptr.PtrRdata", "RData.Hinfo.HinfoRdata",
  "RData.Minfo.MinfoRdata", "RData.Mx.MxRdata", "RData.Txt.TxtRdata"]]
structure VeriDNS.Spec.ResourceRecord  where
  name : ByteArray
  type : BitVec 16
  «class» : BitVec 16
  ttl : BitVec 32
  rdlength : BitVec 16
  rdata : ByteArray
  deriving BEq, Inhabited

def VeriDNS.Spec.rdlength_prop_0 : VeriDNS.Spec.ResourceRecord → Prop :=
  fun h => h.rdlength.toNat = h.rdata.size
