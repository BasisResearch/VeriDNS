import VeriDNS.RFC.Macro
import VeriDNS.Spec.Header
import VeriDNS.Spec.Message
import VeriDNS.Spec.RRType
import VeriDNS.Spec.RRClass
import VeriDNS.Spec.ResourceRecord
import VeriDNS.Spec.Credibility

namespace VeriDNS.Spec

-- RFC 1034 §5.3.2: Resolver state definitions (glossary format)
-- NLP generates: structure Resources { sname, stype, sclass, slist, sbelt, cache }
include_rfc [1034][1777:1838] {
5.3.2. Resources

In addition to its own resources, the resolver may also have shared
access to zones maintained by a local name server.  This gives the
resolver the advantage of more rapid access, but the resolver must be
careful to never let cached information override zone data.  In this
discussion the term "local information" is meant to mean the union of
the cache and such shared zones, with the understanding that
authoritative data is always used in preference to cached data when both
are present.

The following resolver algorithm assumes that all functions have been
converted to a general lookup function, and uses the following data
structures to represent the state of a request in progress in the
resolver:

SNAME           the domain name we are searching for.

STYPE           the QTYPE of the search request.

SCLASS          the QCLASS of the search request.

SLIST           a structure which describes the name servers and the
                zone which the resolver is currently trying to query.
                This structure keeps track of the resolver's current
                best guess about which name servers hold the desired
                information; it is updated when arriving information
                changes the guess.  This structure includes the
                equivalent of a zone name, the known name servers for
                the zone, the known addresses for the name servers, and
                history information which can be used to suggest which
                server is likely to be the best one to try next.  The
                zone name equivalent is a match count of the number of
                labels from the root down which SNAME has in common with
                the zone being queried; this is used as a measure of how
                "close" the resolver is to SNAME.

SBELT           a "safety belt" structure of the same form as SLIST,
                which is initialized from a configuration file, and
                lists servers which should be used when the resolver
                doesn't have any local information to guide name server
                selection.  The match count will be -1 to indicate that
                no labels are known to match.

CACHE           A structure which stores the results from previous
                responses.  Since resolvers are responsible for
                discarding old RRs whose TTL has expired, most
                implementations convert the interval specified in
                arriving RRs to some sort of absolute time when the RR
                is stored in the cache.  Instead of counting the TTLs
                down individually, the resolver just ignores or discards
                old RRs when it runs across them in the course of a
                search, or discards them during periodic sweeps to
                reclaim the memory consumed by old RRs.
}

-- RFC 1034 §5.3.3: Resolution algorithm
-- NLP generates: inductive AlgorithmStep, inductive ResponseAction, Transition table
include_rfc [1034][1849:1976] {
5.3.3. Algorithm

The top level algorithm has four steps:

   1. See if the answer is in local information, and if so return
      it to the client.

   2. Find the best servers to ask.

   3. Send them queries until one returns a response.

   4. Analyze the response, either:

         a. if the response answers the question or contains a name
            error, cache the data as well as returning it back to
            the client.

         b. if the response contains a better delegation to other
            servers, cache the delegation information, and go to
            step 2.

         c. if the response shows a CNAME and that is not the
            answer itself, cache the CNAME, change the SNAME to the
            canonical name in the CNAME RR and go to step 1.

         d. if the response shows a servers failure or other
            bizarre contents, delete the server from the SLIST and
            go back to step 3.

Step 1 searches the cache for the desired data. If the data is in the
cache, it is assumed to be good enough for normal use.  Some resolvers
have an option at the user interface which will force the resolver to
ignore the cached data and consult with an authoritative server.  This
is not recommended as the default.  If the resolver has direct access to
a name server's zones, it should check to see if the desired data is
present in authoritative form, and if so, use the authoritative data in
preference to cached data.

Step 2 looks for a name server to ask for the required data.  The
general strategy is to look for locally-available name server RRs,
starting at SNAME, then the parent domain name of SNAME, the
grandparent, and so on toward the root.  Thus if SNAME were
Mockapetris.ISI.EDU, this step would look for NS RRs for
Mockapetris.ISI.EDU, then ISI.EDU, then EDU, and then . (the root).
These NS RRs list the names of hosts for a zone at or above SNAME.  Copy
the names into SLIST.  Set up their addresses using local data.  It may
be the case that the addresses are not available.  The resolver has many
choices here; the best is to start parallel resolver processes looking
for the addresses while continuing onward with the addresses which are
available.  Obviously, the design choices and options are complicated
and a function of the local host's capabilities.  The recommended
priorities for the resolver designer are:

   1. Bound the amount of work (packets sent, parallel processes
      started) so that a request can't get into an infinite loop or
      start off a chain reaction of requests or queries with other
      implementations EVEN IF SOMEONE HAS INCORRECTLY CONFIGURED
      SOME DATA.

   2. Get back an answer if at all possible.

   3. Avoid unnecessary transmissions.

   4. Get the answer as quickly as possible.

If the search for NS RRs fails, then the resolver initializes SLIST from
the safety belt SBELT.  The basic idea is that when the resolver has no
idea what servers to ask, it should use information from a configuration
file that lists several servers which are expected to be helpful.
Although there are special situations, the usual choice is two of the
root servers and two of the servers for the host's domain.  The reason
for two of each is for redundancy.  The root servers will provide
eventual access to all of the domain space.  The two local servers will
allow the resolver to continue to resolve local names if the local
network becomes isolated from the internet due to gateway or link
failure.

In addition to the names and addresses of the servers, the SLIST data
structure can be sorted to use the best servers first, and to insure
that all addresses of all servers are used in a round-robin manner.  The
sorting can be a simple function of preferring addresses on the local
network over others, or may involve statistics from past events, such as
previous response times and batting averages.

Step 3 sends out queries until a response is received.  The strategy is
to cycle around all of the addresses for all of the servers with a
timeout between each transmission.  In practice it is important to use
all addresses of a multihomed host, and too aggressive a retransmission
policy actually slows response when used by multiple resolvers
contending for the same name server and even occasionally for a single
resolver.  SLIST typically contains data values to control the timeouts
and keep track of previous transmissions.

Step 4 involves analyzing responses.  The resolver should be highly
paranoid in its parsing of responses.  It should also check that the
response matches the query it sent using the ID field in the response.
The ideal answer is one from a server authoritative for the query which
either gives the required data or a name error.  The data is passed back
to the user and entered in the cache for future use if its TTL is
greater than zero.

If the response shows a delegation, the resolver should check to see
that the delegation is "closer" to the answer than the servers in SLIST
are.  This can be done by comparing the match count in SLIST with that
computed from SNAME and the NS RRs in the delegation.  If not, the reply
is bogus and should be ignored.  If the delegation is valid the NS
delegation RRs and any address RRs for the servers should be cached.
The name servers are entered in the SLIST, and the search is restarted.

If the response contains a CNAME, the search is restarted at the CNAME
unless the response has the data for the canonical name or if the CNAME
is the answer itself.
}

-- RFC 1035 §7.2: query transmission — server selection and retransmission.
-- NLP generates sendingthequeries_prevent_selection (a chosen address is not
-- selectable again until the others have been tried).
include_rfc [1035][2432:2499] {
7.2. Sending the queries

As described in [RFC-1034], the basic task of the resolver is to
formulate a query which will answer the client's request and direct that
query to name servers which can provide the information.  The resolver
will usually only have very strong hints about which servers to ask, in
the form of NS RRs, and may have to revise the query, in response to
CNAMEs, or revise the set of name servers the resolver is asking, in
response to delegation responses which point the resolver to name
servers closer to the desired information.  In addition to the
information requested by the client, the resolver may have to call upon
its own services to determine the address of name servers it wishes to
contact.

In any case, the model used in this memo assumes that the resolver is
multiplexing attention between multiple requests, some from the client,
and some internally generated.  Each request is represented by some
state information, and the desired behavior is that the resolver
transmit queries to name servers in a way that maximizes the probability
that the request is answered, minimizes the time that the request takes,
and avoids excessive transmissions.  The key algorithm uses the state
information of the request to select the next name server address to
query, and also computes a timeout which will cause the next action
should a response not arrive.  The next action will usually be a
transmission to some other server, but may be a temporary error to the
client.

The resolver always starts with a list of server names to query (SLIST).
This list will be all NS RRs which correspond to the nearest ancestor
zone that the resolver knows about.  To avoid startup problems, the
resolver should have a set of default servers which it will ask should
it have no current NS RRs which are appropriate.  The resolver then adds
to SLIST all of the known addresses for the name servers, and may start
parallel requests to acquire the addresses of the servers when the
resolver has the name, but no addresses, for the name servers.

To complete initialization of SLIST, the resolver attaches whatever
history information it has to the each address in SLIST.  This will
usually consist of some sort of weighted averages for the response time
of the address, and the batting average of the address (i.e., how often
the address responded at all to the request).  Note that this
information should be kept on a per address basis, rather than on a per
name server basis, because the response time and batting average of a
particular server may vary considerably from address to address.  Note
also that this information is actually specific to a resolver address /
server address pair, so a resolver with multiple addresses may wish to
keep separate histories for each of its addresses.  Part of this step
must deal with addresses which have no such history; in this case an
expected round trip time of 5-10 seconds should be the worst case, with
lower estimates for the same local network, etc.

Note that whenever a delegation is followed, the resolver algorithm
reinitializes SLIST.

The information establishes a partial ranking of the available name
server addresses.  Each time an address is chosen and the state should
be altered to prevent its selection again until all other addresses have
been tried.  The timeout for each transmission should be 50-100% greater
than the average predicted value to allow for variance in response.
}

-- SlistEntry is generated from the §5.3.3 algorithm prose above ("Copy the
-- names into SLIST" / "Set up their addresses ..." / "It may be the case
-- that the addresses are not available" / "keep track of previous
-- transmissions") — see `deriveEntryStructure` in VeriDNS.RFC.Syntax.

-- Manual remainder of the cache interface. The time-aware operations
-- (storeAt, sweep) and their laws are NLP-generated on CacheSpec from the
-- §5.3.2 prose; the RFC 2308 negative-cache operations are generated as
-- NegativeCacheSpec / NegativeAuthoritySpec in Spec/NegativeCache.lean.
-- Still manual, and why:
--  * `lookup` — the keyed signature joins the §5.3.2 search-state glossary
--    (SNAME/STYPE/SCLASS) with the CACHE entry's "in the course of a
--    search"; the generator does not yet assemble one method from two
--    glossary entries.
--  * `storeRanked`/`lookupAnswerable` — the §5.4.1 sentences (in
--    Spec/Credibility.lean) license trust-tagged store and an answer-path
--    lookup, but the absolute-time argument comes from the §5.3.2 storeAt
--    convention, which is not in scope in that file. Generating these needs
--    cross-file assembly (an env extension, like `rfcEnumDescriptions`).
class CacheLookup (C RR : Type) extends CacheSpec C RR where
  lookup : C → ByteArray → BitVec 16 → BitVec 16 → UInt32 → Array RR
  /-- RFC 2181 §5.4.1 credibility-aware store: cache an RR tagged with its
      trust tier (the generated `Trustworthiness`), retaining
      strictly-more-trustworthy same-key data in preference. -/
  storeRanked : C → RR → Trustworthiness → UInt32 → C
  /-- RFC 2181 §5.4.1 answer-path lookup: like `lookup` but excludes data at
      the least-trustworthy rank, which must never be returned as an answer. -/
  lookupAnswerable : C → ByteArray → BitVec 16 → BitVec 16 → UInt32 → Array RR

-- Manual: batch SLIST creation from NS names. The licensing prose exists —
-- "Copy the names into SLIST" / "Set up their addresses using local data"
-- read as OPERATIONS (the same sentences the generator reads as per-entry
-- FIELDS for SlistEntry), and the §5.3.2 match-count copula for
-- matchCount/hasServers — but the imperative→constructor derivation is not
-- implemented yet; see the entry-structure rule in VeriDNS.RFC.Syntax for
-- where it would attach.
class SlistFromNS (S NS : Type) extends SlistSpec S NS where
  fromNsNames : Array ByteArray → Nat → S
  fromNsWithGlue : Array ByteArray → Array (ByteArray × BitVec 32) → Nat → S
  matchCount : S → Nat
  hasServers : S → Bool

-- Manual: wire-format plumbing, not RFC semantics. RRs cross the Spec/Impl
-- boundary as canonical wire bytes; these accessors expose decode/encode
-- and field projections of the Impl's RR representation to the abstract
-- resolver. The RFC describes the wire FORMAT (generated in
-- Spec/ResourceRecord.lean), not this API.
class RRParse (RR : Type) where
  parseRaw : ByteArray → Option RR
  rrType : RR → BitVec 16
  rrRdata : RR → ByteArray
  /-- Canonical wire encoding, for returning cached RRs to the client
      (RFC 1034 §5.3.3 step 1). -/
  rrBytes : RR → ByteArray
  /-- Owner name (canonical wire bytes), for identifying the delegation
      zone when validating closeness (§5.3.3 "computed from SNAME and the
      NS RRs in the delegation"). -/
  rrName : RR → ByteArray

end VeriDNS.Spec
