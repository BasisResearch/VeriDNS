import VeriDNS.RFC.Macro

namespace VeriDNS.Spec

-- Verify and parse RFC 1035 section 3.1.
-- Prose-only section: generates structure NameSpace { labels : Array ByteArray }
-- and formal ∀ constraints from NLP analysis of prose.
include_rfc [1035][533:552] {
3.1. Name space definitions

Domain names in messages are expressed in terms of a sequence of labels.
Each label is represented as a one octet length field followed by that
number of octets.  Since every domain name ends with the null label of
the root, a domain name is terminated by a length byte of zero.  The
high order two bits of every length octet must be zero, and the
remaining six bits of the length field limit the label to 63 octets or
less.

To simplify implementations, the total length of a domain name (i.e.,
label octets and label length octets) is restricted to 255 octets or
less.

Although labels can contain any 8 bit values in octets that make up a
label, it is strongly recommended that labels follow the preferred
syntax described elsewhere in this memo, which is compatible with
existing host naming conventions.  Name servers and resolvers must
compare labels in a case-insensitive manner (i.e., A=a), assuming ASCII
with zero parity.  Non-alphabetic codes must match exactly.
}

end VeriDNS.Spec
