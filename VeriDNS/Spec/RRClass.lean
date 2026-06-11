import VeriDNS.RFC.Macro

namespace VeriDNS.Spec

-- Verify and parse RFC 1035 section 3.2.4.
-- Custom syntax generates: inductive RRClass
include_rfc [1035][681:693] {
3.2.4. CLASS values

CLASS fields appear in resource records.  The following CLASS mnemonics
and values are defined:

IN              1 the Internet

CS              2 the CSNET class (Obsolete - used only for examples in
                some obsolete RFCs)

CH              3 the CHAOS class

HS              4 Hesiod [Dyer 87]
}

-- Verify and parse RFC 1035 section 3.2.5.
-- Custom syntax generates: inductive Qclass
include_rfc [1035][695:701] {
3.2.5. QCLASS values

QCLASS fields appear in the question section of a query.  QCLASS values
are a superset of CLASS values; every CLASS is a valid QCLASS.  In
addition to CLASS values, the following QCLASSes are defined:

*               255 any class
}

end VeriDNS.Spec
