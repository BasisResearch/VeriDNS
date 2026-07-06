import VeriDNS.Impl.DomainName
import VeriDNS.Spec.Resolver

/-!
# Executable client-answer scrub

The wire-level counterpart of `VeriDNS.Spec.Net.scrubAnswer`. Applied at the client-delivery
boundary (`Server.replyForResolution`) so the resolver hands the stub only records whose owner is
CNAME-reachable (case-insensitively, RFC 1035 §2.3.3) from the queried name — closing the
answer-injection / poison-conduit vector. The authenticity guarantee is
`Proof/AnswerScrub.lean` (`scrubAnswerB_no_foreign`).
-/

namespace VeriDNS.Impl.Resolver

open VeriDNS.Spec VeriDNS.Impl

variable {RR : Type} [RRParse RR]

/-- Case-insensitive membership of a wire name in a reach set. -/
def nameMemB (n : ByteArray) (reach : Array ByteArray) : Bool :=
  reach.any (fun m => DomainName.nameEqCI n m)

/-- The CNAME target (rdata name) of a record, if it is a CNAME (type 5) whose owner is already in
    `reach`; `none` otherwise. -/
def reachTarget? [RRParse RR] (reach : Array ByteArray) (bytes : ByteArray) : Option ByteArray :=
  match RRParse.parseRaw (RR := RR) bytes with
  | some rr =>
    if RRParse.rrType rr == (5 : BitVec 16) && nameMemB (RRParse.rrName rr) reach
    then some (RRParse.rrRdata rr) else none
  | none => none

/-- One CNAME-expansion round (`reachStep`, wire level). -/
def reachStepB [RRParse RR] (answer reach : Array ByteArray) : Array ByteArray :=
  reach ++ answer.filterMap (reachTarget? (RR := RR) reach)

/-- Iterate `reachStepB` `k` times. -/
def reachIterB [RRParse RR] (answer : Array ByteArray) : Nat → Array ByteArray → Array ByteArray
  | 0, reach => reach
  | k + 1, reach => reachIterB answer k (reachStepB (RR := RR) answer reach)

/-- Owner names entitled to appear in a client answer to `qname`: the CNAME-closure of `{qname}`. -/
def reachableNamesB [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  reachIterB (RR := RR) answer answer.size #[qname]

/-- Keep only records whose owner is entitled — the client-delivery scrub. -/
def scrubAnswerB [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  answer.filter (fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr => nameMemB (RRParse.rrName rr) (reachableNamesB (RR := RR) qname answer)
    | none => false)

end VeriDNS.Impl.Resolver
