import VeriDNS.Impl.DomainName
import VeriDNS.Spec.Resolver



namespace VeriDNS.Impl.Resolver

open VeriDNS.Spec VeriDNS.Impl

variable {RR : Type} [RRParse RR]

def nameMemB (n : ByteArray) (reach : Array ByteArray) : Bool :=
  reach.any (fun m => DomainName.nameEqCI n m)

def reachTarget? [RRParse RR] (reach : Array ByteArray) (bytes : ByteArray) : Option ByteArray :=
  match RRParse.parseRaw (RR := RR) bytes with
  | some rr =>
    if RRParse.rrType rr == (5 : BitVec 16) && nameMemB (RRParse.rrName rr) reach
    then some (RRParse.rrRdata rr) else none
  | none => none

def reachStepB [RRParse RR] (answer reach : Array ByteArray) : Array ByteArray :=
  reach ++ answer.filterMap (reachTarget? (RR := RR) reach)

def reachIterB [RRParse RR] (answer : Array ByteArray) : Nat → Array ByteArray → Array ByteArray
  | 0, reach => reach
  | k + 1, reach => reachIterB answer k (reachStepB (RR := RR) answer reach)

def reachableNamesB [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  reachIterB (RR := RR) answer answer.size #[qname]

def setOwnerB [RRParse RR] (rr : RR) (bytes m : ByteArray) : ByteArray :=
  m ++ bytes.extract (RRParse.rrName (RR := RR) rr).size bytes.size

def scrubAnswerB [RRParse RR] (qname : ByteArray) (answer : Array ByteArray) : Array ByteArray :=
  answer.filterMap (fun bytes =>
    match RRParse.parseRaw (RR := RR) bytes with
    | some rr =>
      ((reachableNamesB (RR := RR) qname answer).find?
          (fun m => DomainName.nameEqCI (RRParse.rrName rr) m)).map
        (setOwnerB (RR := RR) rr bytes)
    | none => none)

end VeriDNS.Impl.Resolver
