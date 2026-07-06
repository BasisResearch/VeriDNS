import VeriDNS.Impl.Parsec

namespace VeriDNS.Impl.DomainName

open VeriDNS.Impl

def decodeNameAux (buf : ByteArray) (pos : Nat) (fuel : Nat)
    (firstEndPos : Option Nat)
    : Except String (Array ByteArray × Nat) :=
  match fuel with
  | 0 => .error "domain name: circular pointer or too many labels"
  | fuel + 1 =>
    if h : pos < buf.data.size then
      let b := buf.data[pos]
      if b == 0 then

        let endPos := firstEndPos.getD (pos + 1)
        .ok (#[], endPos)
      else if b.toNat &&& 0xC0 == 0xC0 then

        if h2 : pos + 1 < buf.data.size then
          let lo := buf.data[pos + 1]
          let offset := (b.toNat &&& 0x3F) * 256 + lo.toNat

          if offset < pos then
            let endPos := firstEndPos.getD (pos + 2)
            match decodeNameAux buf offset fuel (some endPos) with
            | .ok (labels, _) => .ok (labels, endPos)
            | .error e => .error e
          else .error "domain name: forward or self compression pointer (RFC 1035 §4.1.4)"
        else .error "domain name: truncated pointer"
      else

        let len := b.toNat
        if len > 63 then .error s!"domain name: label length {len} > 63"
        else if pos + 1 + len ≤ buf.data.size then
          let label := buf.extract (pos + 1) (pos + 1 + len)
          match decodeNameAux buf (pos + 1 + len) fuel firstEndPos with
          | .ok (rest, endPos) => .ok (#[label] ++ rest, endPos)
          | .error e => .error e
        else .error "domain name: label truncated"
    else .error "domain name: unexpected end of input"

/-- The wire-encoded length of a domain name: one length-octet per label plus the label bytes, plus the
    terminating zero octet. Equals `(labelsToWireFormat labels).size` (see `Proof/DomainName.lean`). -/
def encodedNameLen (labels : Array ByteArray) : Nat :=
  labels.foldl (fun acc l => acc + 1 + l.size) 1

def decodeName : DnsParser (Array ByteArray) := do
  let buf ← DnsParser.getBuffer
  let pos ← DnsParser.getPos
  match decodeNameAux buf pos buf.size none with
  | .ok (labels, endPos) =>

    if encodedNameLen labels ≤ 255 then
      DnsParser.setPos endPos
      return labels
    else DnsParser.fail "domain name: encoded length exceeds 255 octets (RFC 1035 §2.3.4)"
  | .error e => DnsParser.fail e

def encodeName (labels : Array ByteArray) : DnsSerializer Unit := do
  for label in labels do
    if label.size > 63 then

      DnsSerializer.writeUInt8 63
      DnsSerializer.writeBytes (label.extract 0 63)
    else
      DnsSerializer.writeUInt8 label.size.toUInt8
      DnsSerializer.writeBytes label

  DnsSerializer.writeUInt8 0

def labelsToWireFormatGo : List ByteArray → ByteArray
  | [] => ⟨#[0]⟩
  | l :: rest => (ByteArray.empty.push l.size.toUInt8 ++ l) ++ labelsToWireFormatGo rest

def labelsToWireFormat (labels : Array ByteArray) : ByteArray :=
  labelsToWireFormatGo labels.toList

def wireFormatToLabelsGo (wire : ByteArray) (pos : Nat)
    : Except String (List ByteArray) :=

  if h : pos < wire.data.size then
    let len := wire.data[pos]'h |>.toNat
    if hlen : len = 0 then .ok []
    else if _ : len > 63 then .error s!"wireFormatToLabels: label length {len} > 63"
    else if h2 : pos + 1 + len ≤ wire.size then
      match wireFormatToLabelsGo wire (pos + 1 + len) with
      | .ok rest => .ok (wire.extract (pos + 1) (pos + 1 + len) :: rest)
      | .error e => .error e
    else .error "wireFormatToLabels: truncated"
  else .ok []
termination_by wire.size - pos
decreasing_by omega

def wireFormatToLabels (wire : ByteArray) : Except String (Array ByteArray) :=
  match wireFormatToLabelsGo wire 0 with
  | .ok ls => .ok ls.toArray
  | .error e => .error e

def parentDomainWire (wire : ByteArray) : Option ByteArray :=
  match wireFormatToLabels wire with
  | .error _ => none
  | .ok labels =>
    if labels.size == 0 then none
    else some (labelsToWireFormat (labels.extract 1 labels.size))

def foldCaseByte (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

def alphabeticByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

def foldNameCase (n : ByteArray) : ByteArray :=
  ⟨n.data.map foldCaseByte⟩

def nameEqCI (a b : ByteArray) : Bool :=
  foldNameCase a == foldNameCase b

def matchCountLabels (a b : Array ByteArray) : Nat :=
  go a.reverse b.reverse 0 (Nat.min a.size b.size)
where
  go (ra rb : Array ByteArray) (i bound : Nat) : Nat :=
    if i >= bound then i
    else if nameEqCI ra[i]! rb[i]! then go ra rb (i + 1) bound
    else i
  termination_by bound - i

end VeriDNS.Impl.DomainName
