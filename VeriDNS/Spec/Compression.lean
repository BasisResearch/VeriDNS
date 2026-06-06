import VeriDNS.RFC.Macro

namespace VeriDNS.Spec

-- Verify and parse RFC 1035 section 4.1.4.
-- Custom syntax generates: structure MessageCompression (offset : BitVec 14)
-- Literal "1  1" marker bits are filtered; example diagrams are skipped.
include_rfc [1035][1634:1738] {
4.1.4. Message compression

In order to reduce the size of messages, the domain system utilizes a
compression scheme which eliminates the repetition of domain names in a
message.  In this scheme, an entire domain name or a list of labels at
the end of a domain name is replaced with a pointer to a prior occurance
of the same name.

The pointer takes the form of a two octet sequence:

    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    | 1  1|                OFFSET                   |
    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

The first two bits are ones.  This allows a pointer to be distinguished
from a label, since the label must begin with two zero bits because
labels are restricted to 63 octets or less.  (The 10 and 01 combinations
are reserved for future use.)  The OFFSET field specifies an offset from
the start of the message (i.e., the first octet of the ID field in the
domain header).  A zero offset specifies the first byte of the ID field,
etc.

The compression scheme allows a domain name in a message to be
represented as either:

   - a sequence of labels ending in a zero octet

   - a pointer

   - a sequence of labels ending with a pointer

Pointers can only be used for occurances of a domain name where the
format is not class specific.  If this were not the case, a name server
or resolver would be required to know the format of all RRs it handled.
As yet, there are no such cases, but they may occur in future RDATA
formats.

If a domain name is contained in a part of the message subject to a
length field (such as the RDATA section of an RR), and compression is
used, the length of the compressed name is used in the length
calculation, rather than the length of the expanded name.

Programs are free to avoid using pointers in messages they generate,
although this will reduce datagram capacity, and may cause truncation.
However all programs are required to understand arriving messages that
contain pointers.

For example, a datagram might need to use the domain names F.ISI.ARPA,
FOO.F.ISI.ARPA, ARPA, and the root.  Ignoring the other fields of the
message, these domain names might be represented as:

       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    20 |           1           |           F           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    22 |           3           |           I           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    24 |           S           |           I           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    26 |           4           |           A           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    28 |           R           |           P           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    30 |           A           |           0           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    40 |           3           |           F           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    42 |           O           |           O           |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    44 | 1  1|                20                       |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    64 | 1  1|                26                       |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
    92 |           0           |                       |
       +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

The domain name for F.ISI.ARPA is shown at offset 20.  The domain name
FOO.F.ISI.ARPA is shown at offset 40; this definition uses a pointer to
concatenate a label for FOO to the previously defined F.ISI.ARPA.  The
domain name ARPA is defined at offset 64 using a pointer to the ARPA
component of the name F.ISI.ARPA at 20; note that this pointer relies on
ARPA being the last label in the string at 20.  The root domain name is
defined by a single octet of zeros at 92; the root domain name has no
labels.
}

end VeriDNS.Spec
