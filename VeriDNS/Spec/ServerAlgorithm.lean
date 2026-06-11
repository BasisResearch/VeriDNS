import VeriDNS.RFC.Macro
import VeriDNS.Spec.Message
import VeriDNS.Spec.NameTree

/-!
RFC 1034 §4.3.2: the name server lookup algorithm — the operational
reading of the §3.1 name tree. The match-down sub-steps (3a/3b/3c) are
where queries get their meaning: whole-QNAME match → answer (or CNAME
restart), zone cut → referral, missing label → authoritative name error.

The sub-step discourse rule generates the obligations as parameterized
props over an abstract state σ; `Proof/NameTree.lean` instantiates them
with the `treeLookup` denotation, pinning the denotation to this text:

- `obligation_copyRRsMatchQTYPE` — whole-QNAME match, not the CNAME case
  → the answer is the RRs matching QTYPE (3a);
- `obligation_copyCNAMERRIntoAnswerSection` /
  `obligation_changeQNAMEToCanonicalName` — CNAME at the node and QTYPE ≠
  CNAME → the CNAME RR is served and resolution restarts at the canonical
  name (3a);
- `obligation_setAuthoritativeNameErrorInResponse` — a label match is
  impossible and the name is the original QNAME → authoritative name
  error (3c). The wildcard qualifier ("if the '*' label does not exist")
  drops out grammatically — its sentence's guard does not parse to a
  name, so its body is skipped — consistent with wildcards being out of
  scope (§4.3.3 is not implemented; the model tree carries no `*` nodes).

This file uses its own namespace: the algorithm-path generator also
emits step/transition types whose names (`AlgorithmStep`,
`ResponseAction`, `Transition`, `StepSpec`) would otherwise collide with
the §5.3.3 resolver algorithm in `Spec/Resolver.lean`.
-/

namespace VeriDNS.Spec.ServerLookup

include_rfc [1034][1289:1366] {
4.3.2. Algorithm

The actual algorithm used by the name server will depend on the local OS
and data structures used to store RRs.  The following algorithm assumes
that the RRs are organized in several tree structures, one for each
zone, and another for the cache:

   1. Set or clear the value of recursion available in the response
      depending on whether the name server is willing to provide
      recursive service.  If recursive service is available and
      requested via the RD bit in the query, go to step 5,
      otherwise step 2.

   2. Search the available zones for the zone which is the nearest
      ancestor to QNAME.  If such a zone is found, go to step 3,
      otherwise step 4.

   3. Start matching down, label by label, in the zone.  The
      matching process can terminate several ways:

         a. If the whole of QNAME is matched, we have found the
            node.

            If the data at the node is a CNAME, and QTYPE doesn't
            match CNAME, copy the CNAME RR into the answer section
            of the response, change QNAME to the canonical name in
            the CNAME RR, and go back to step 1.

            Otherwise, copy all RRs which match QTYPE into the
            answer section and go to step 6.

         b. If a match would take us out of the authoritative data,
            we have a referral.  This happens when we encounter a
            node with NS RRs marking cuts along the bottom of a
            zone.

            Copy the NS RRs for the subzone into the authority
            section of the reply.  Put whatever addresses are
            available into the additional section, using glue RRs
            if the addresses are not available from authoritative
            data or the cache.  Go to step 4.

         c. If at some label, a match is impossible (i.e., the
            corresponding label does not exist), look to see if a
            the "*" label exists.

            If the "*" label does not exist, check whether the name
            we are looking for is the original QNAME in the query
            or a name we have followed due to a CNAME.  If the name
            is original, set an authoritative name error in the
            response and exit.  Otherwise just exit.

            If the "*" label does exist, match RRs at that node
            against QTYPE.  If any match, copy them into the answer
            section, but set the owner of the RR to be QNAME, and
            not the node with the "*" label.  Go to step 6.

   4. Start matching down in the cache.  If QNAME is found in the
      cache, copy all RRs attached to it that match QTYPE into the
      answer section.  If there was no delegation from
      authoritative data, look for the best one from the cache, and
      put it in the authority section.  Go to step 6.

   5. Using the local resolver or a copy of its algorithm (see
      resolver section of this memo) to answer the query.  Store
      the results, including any intermediate CNAMEs, in the answer
      section of the response.

   6. Using local data only, attempt to add other RRs which may be
      useful to the additional section of the query.  Exit.
}

end VeriDNS.Spec.ServerLookup
