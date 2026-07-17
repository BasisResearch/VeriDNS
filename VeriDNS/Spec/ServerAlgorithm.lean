import Std.Tactic.BVDecide
import Batteries
import Pseudoprint
import VeriDNS.Spec.Message
import VeriDNS.Spec.NameTree
import VeriDNS.RFC.Check
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
def VeriDNS.Spec.ServerLookup.obligation_setAuthoritativeNameErrorInResponse : (σ : Type) → (σ → Bool) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ matchImpossible nameOriginal setAuthoritativeNameErrorInResponse =>
  ∀ (s : σ),
    matchImpossible s = Bool.true →
      nameOriginal s = Bool.true → setAuthoritativeNameErrorInResponse s

def VeriDNS.Spec.ServerLookup.obligation_copyRRsMatchQTYPE : (σ : Type) → (σ → Bool) → (σ → Bool) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ wholeOfQNAMEMatched dataAtNodeCNAME qtypeNotMatchCNAME copyRRsMatchQTYPE =>
  ∀ (s : σ),
    wholeOfQNAMEMatched s = Bool.true →
      ¬(dataAtNodeCNAME s = Bool.true ∧ qtypeNotMatchCNAME s = Bool.true) → copyRRsMatchQTYPE s

def VeriDNS.Spec.ServerLookup.obligation_changeQNAMEToCanonicalName : (σ : Type) → (σ → Bool) → (σ → Bool) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ wholeOfQNAMEMatched dataAtNodeCNAME qtypeNotMatchCNAME changeQNAMEToCanonicalName =>
  ∀ (s : σ),
    wholeOfQNAMEMatched s = Bool.true →
      dataAtNodeCNAME s = Bool.true →
        qtypeNotMatchCNAME s = Bool.true → changeQNAMEToCanonicalName s

@[blueprint "ServerLookup.AlgorithmStep"]
inductive VeriDNS.Spec.ServerLookup.AlgorithmStep  where
  | setClear : VeriDNS.Spec.ServerLookup.AlgorithmStep
  | searchAvailable : VeriDNS.Spec.ServerLookup.AlgorithmStep
  | startMatching : VeriDNS.Spec.ServerLookup.AlgorithmStep
  | startMatchingCache : VeriDNS.Spec.ServerLookup.AlgorithmStep
  | usingLocal : VeriDNS.Spec.ServerLookup.AlgorithmStep
  | usingLocalQuery : VeriDNS.Spec.ServerLookup.AlgorithmStep
  deriving Repr, BEq, Inhabited

@[blueprint "ServerLookup.ResponseAction"]
inductive VeriDNS.Spec.ServerLookup.ResponseAction  where
  | whole : VeriDNS.Spec.ServerLookup.ResponseAction
  | «match» : VeriDNS.Spec.ServerLookup.ResponseAction
  | some : VeriDNS.Spec.ServerLookup.ResponseAction
  deriving Repr, BEq, Inhabited

@[blueprint "ServerLookup.Transition"]
structure VeriDNS.Spec.ServerLookup.Transition  where
  «from» : VeriDNS.Spec.ServerLookup.AlgorithmStep
  action : VeriDNS.Spec.ServerLookup.ResponseAction
  to : VeriDNS.Spec.ServerLookup.AlgorithmStep
  deriving Repr, BEq, Inhabited

def VeriDNS.Spec.ServerLookup.algorithm_transition_0 : VeriDNS.Spec.ServerLookup.Transition :=
  VeriDNS.Spec.ServerLookup.Transition.mk VeriDNS.Spec.ServerLookup.AlgorithmStep.usingLocalQuery
  VeriDNS.Spec.ServerLookup.ResponseAction.whole
  VeriDNS.Spec.ServerLookup.AlgorithmStep.usingLocalQuery

def VeriDNS.Spec.ServerLookup.algorithm_transition_1 : VeriDNS.Spec.ServerLookup.Transition :=
  VeriDNS.Spec.ServerLookup.Transition.mk VeriDNS.Spec.ServerLookup.AlgorithmStep.usingLocalQuery
  VeriDNS.Spec.ServerLookup.ResponseAction.match
  VeriDNS.Spec.ServerLookup.AlgorithmStep.startMatchingCache

def VeriDNS.Spec.ServerLookup.algorithm_transition_2 : VeriDNS.Spec.ServerLookup.Transition :=
  VeriDNS.Spec.ServerLookup.Transition.mk VeriDNS.Spec.ServerLookup.AlgorithmStep.usingLocalQuery
  VeriDNS.Spec.ServerLookup.ResponseAction.some
  VeriDNS.Spec.ServerLookup.AlgorithmStep.usingLocalQuery

def VeriDNS.Spec.ServerLookup.obligation_copyCNAMERRIntoAnswerSection : (σ : Type) → (σ → Bool) → (σ → Bool) → (σ → Bool) → (σ → Prop) → Prop :=
  fun σ wholeOfQNAMEMatched dataAtNodeCNAME qtypeNotMatchCNAME copyCNAMERRIntoAnswerSection =>
  ∀ (s : σ),
    wholeOfQNAMEMatched s = Bool.true →
      dataAtNodeCNAME s = Bool.true →
        qtypeNotMatchCNAME s = Bool.true → copyCNAMERRIntoAnswerSection s
