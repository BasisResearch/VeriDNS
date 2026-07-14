import VeriDNS.Proof.Depth1Adequacy
import VeriDNS.Proof.SpineAdequacy
import VeriDNS.Proof.ServeAdequacy
import VeriDNS.Test.Loop





namespace VeriDNS.Test.AdequacyPins

open VeriDNS.Spec VeriDNS.Impl VeriDNS.Impl.SList VeriDNS.Impl.Cache
open VeriDNS.Proof.FreeIO VeriDNS.Proof.Adequacy
open VeriDNS.Test.Loop


def comWire : ByteArray := wireName ["com"]
def comNsName : ByteArray := wireName ["ns", "nic", "com"]
def pinRootIp : BitVec 32 := BitVec.ofNat 32 0xC6290004
def childIpBytes : ByteArray := ⟨#[93, 184, 216, 53]⟩

def comARR : ResourceRecord :=
  { name := comWire, type := 1, «class» := 1, ttl := 300, rdlength := 4,
    rdata := ⟨#[93, 184, 216, 34]⟩ }

def nsAuthPin : Array ByteArray := #[mkRR comWire 2 comNsName]
def gluePin : Array ByteArray := #[mkRR comNsName 1 childIpBytes]
def childT : Node ResourceRecord := .mk ByteArray.empty #[] #[.mk (lab "com") #[comARR] #[]]
def childNeg : Array ByteArray := #[mkRR comWire 6 soaRdata (ttl := 60)]

def respondPin : ByteArray → Format → Format :=
  twoServerRespond pinRootIp nsAuthPin gluePin childT childNeg

def w0 : World :=
  { clock := 100000, ids := fun n => (0x4321 + 17 * n).toUInt16,
    oracle := mkHonestOracleAddr respondPin,
    tcpOracle := fun _ _ => none, trace := [], idCtr := 0 }

def pinSbelt : DnsSList := DnsSList.mkSbelt #[(rootName, pinRootIp)]
def pinQuery : Format := mkQuery comWire

def depth1AnswerDelivered : Bool :=
  match Prog.run 400 (Server.resolveWithIO (M := Prog) (Sock := Unit)
      pinQuery pinSbelt DnsCache.empty 100000 40 6 5) w0 with
  | some ((.ok resp, _), w') =>
    resp.header.rcode == Rcode.noError
      && resp.answer == #[RRParse.rrBytes comARR]
      && resp.question.size == 1
      && resp.question[0]?.any (fun (qu : Question) => qu.qname == comWire && qu.qtype == 1)
      && w'.idCtr == 4
  | _ => false

#guard depth1AnswerDelivered

def depth1NxdomainDelivered : Bool :=
  let respondNx := twoServerRespond pinRootIp nsAuthPin gluePin
    (.mk ByteArray.empty #[] #[]) childNeg
  match Prog.run 400 (Server.resolveWithIO (M := Prog) (Sock := Unit)
      pinQuery pinSbelt DnsCache.empty 100000 40 6 5)
      { w0 with oracle := mkHonestOracleAddr respondNx } with
  | some ((.ok resp, _), w') =>
    resp.header.rcode == Rcode.nameError && resp.answer.isEmpty && w'.idCtr == 4
  | _ => false

#guard depth1NxdomainDelivered

def flatAnswerDelivered : Bool :=
  let respondFlat : ByteArray → Format → Format := fun _ q => treeRespond childT childNeg q
  match Prog.run 400 (Server.resolveWithIO (M := Prog) (Sock := Unit)
      pinQuery pinSbelt DnsCache.empty 100000 40 6 5)
      { w0 with oracle := mkHonestOracleAddr respondFlat } with
  | some ((.ok resp, _), w') =>
    resp.header.rcode == Rcode.noError
      && resp.answer == #[RRParse.rrBytes comARR]
      && w'.idCtr == 2
  | _ => false

#guard flatAnswerDelivered


def wwwWire : ByteArray := wireName ["www", "example", "com"]

def wwwARR : ResourceRecord :=
  { name := wwwWire, type := 1, «class» := 1, ttl := 300, rdlength := 4,
    rdata := ⟨#[93, 184, 216, 34]⟩ }

def ladderT : Node ResourceRecord :=
  .mk ByteArray.empty #[]
    #[.mk (lab "com") #[]
      #[.mk (lab "example") #[]
        #[.mk (lab "www") #[wwwARR] #[]]]]

def ladderNeg : Array ByteArray := #[mkRR wwwWire 6 soaRdata (ttl := 60)]

def flatMultiLabelDelivered : Bool :=
  let respondFlat : ByteArray → Format → Format := fun _ q => treeRespond ladderT ladderNeg q
  match Prog.run 400 (Server.resolveWithIO (M := Prog) (Sock := Unit)
      (mkQuery wwwWire) pinSbelt DnsCache.empty 100000 40 6 5)
      { w0 with oracle := mkHonestOracleAddr respondFlat } with
  | some ((.ok resp, _), w') =>
    resp.header.rcode == Rcode.noError
      && resp.answer == #[RRParse.rrBytes wwwARR]
      && resp.question.size == 1
      && resp.question[0]?.any (fun (qu : Question) => qu.qname == wwwWire && qu.qtype == 1)
      && w'.idCtr == 6
  | _ => false

#guard flatMultiLabelDelivered


def spineRespond : ByteArray → Format → Format := fun addr q =>
  if addr == Server.ipv4ToAddr pinRootIp
  then hopRespond comWire.size nsAuthPin gluePin (.mk ByteArray.empty #[] #[]) ladderNeg q
  else treeRespond ladderT ladderNeg q

def spineDelivered : Bool :=
  match Prog.run 400 (Server.resolveWithIO (M := Prog) (Sock := Unit)
      (mkQuery wwwWire) pinSbelt DnsCache.empty 100000 40 6 5)
      { w0 with oracle := mkHonestOracleAddr spineRespond } with
  | some ((.ok resp, _), w') =>
    resp.header.rcode == Rcode.noError
      && resp.answer == #[RRParse.rrBytes wwwARR]
      && resp.question.size == 1
      && resp.question[0]?.any (fun (qu : Question) => qu.qname == wwwWire && qu.qtype == 1)
      && w'.idCtr == 6
  | _ => false

#guard spineDelivered



def rootHandler (qb : ByteArray) : Option ByteArray :=
  match Message.decode qb with
  | .error _ => none
  | .ok q => some (Message.encode (referralReply q nsAuthPin gluePin))

def childHandler (qb : ByteArray) : Option ByteArray :=
  match Message.decode qb with
  | .error _ => none
  | .ok q => some (Message.encode (treeRespond childT childNeg q))

def serveDepth1Delivered : Bool := Id.run do
  let (_, st) := runServe (mkQuery comWire) [rootHandler, childHandler]
  let some resp := sentResponse st | return false
  return st.exchanged.size == 2
    && resp.header.id == 0x1234
    && resp.header.qr == 1
    && resp.header.rcode == Rcode.noError
    && resp.answer == #[RRParse.rrBytes comARR]
    && resp.question[0]?.any (fun (qu : Question) => qu.qname == comWire && qu.qtype == 1)

#guard serveDepth1Delivered

end VeriDNS.Test.AdequacyPins
