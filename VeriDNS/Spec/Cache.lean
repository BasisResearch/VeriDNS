import VeriDNS.RFC.Macro

namespace VeriDNS.Spec

-- RFC 1034 §5.3.2 CACHE glossary entry is now codegen'd as part of
-- Spec/Resolver.lean's full §5.3.2 block (Resources.cache field).

-- RFC 1035 section 7.4: Using the cache
-- Prose-only section: generates cache usage constraint props
include_rfc [1035][2577:2613] {
7.4. Using the cache

In general, we expect a resolver to cache all data which it receives in
responses since it may be useful in answering future client requests.
However, there are several types of data which should not be cached:

   - When several RRs of the same type are available for a
     particular owner name, the resolver should either cache them
     all or none at all.  When a response is truncated, and a
     resolver doesn't know whether it has a complete set, it should
     not cache a possibly partial set of RRs.

   - Cached data should never be used in preference to
     authoritative data, so if caching would cause this to happen
     the data should not be cached.

   - The results of an inverse query should not be cached.

   - The results of standard queries where the QNAME contains "*"
     labels if the data might be used to construct wildcards.  The
     reason is that the cache does not necessarily contain existing
     RRs or zone boundary information which is necessary to
     restrict the application of the wildcard RRs.

   - RR data in responses of dubious reliability.  When a resolver
     receives unsolicited responses or RR data other than that
     requested, it should discard it without caching it.  The basic
     implication is that all sanity checks on a packet should be
     performed before any of it is cached.

In a similar vein, when a resolver has a set of RRs for some name in a
response, and wants to cache the RRs, it should check its cache for
already existing RRs.  Depending on the circumstances, either the data
in the response or the cache is preferred, but the two should never be
combined.  If the data in the response is from authoritative data in the
answer section, it is always preferred.
}

-- RFC 1035 section 6.1.3: Time
-- Prose-only section: generates timer struct + expiry props
include_rfc [1035][2132:2147] {
6.1.3. Time

Both the TTL data for RRs and the timing data for refreshing activities
depends on 32 bit timers in units of seconds.  Inside the database,
refresh timers and TTLs for cached data conceptually "count down", while
data in the zone stays with constant TTLs.

A recommended implementation strategy is to store time in two ways:  as
a relative increment and as an absolute time.  One way to do this is to
use positive 32 bit numbers for one type and negative numbers for the
other.  The RRs in zones use relative times; the refresh timers and
cache data use absolute times.  Absolute numbers are taken with respect
to some known origin and converted to relative values when placed in the
response to a query.  When an absolute TTL is negative after conversion
to relative, then the data is expired and should be ignored.
}

end VeriDNS.Spec
