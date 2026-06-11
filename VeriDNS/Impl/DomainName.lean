import VeriDNS.Impl.Parsec

namespace VeriDNS.Impl.DomainName

open VeriDNS.Impl

-- ============================================================
-- Domain name decoding with compression pointer support (§4.1.4)
--
-- Top 2 bits of length byte:
--   00 = label (length 0–63)
--   11 = compression pointer (14-bit offset)
--
-- We use a fuel-based approach for termination in the pure decoder.
-- The fuel is bounded by buffer size (worst case: every byte is visited).
-- ============================================================

/-- Pure domain name decoder with fuel for termination.
    Returns (labels, position after the name in the current stream). -/
def decodeNameAux (buf : ByteArray) (pos : Nat) (fuel : Nat)
    (firstEndPos : Option Nat)
    : Except String (Array ByteArray × Nat) :=
  match fuel with
  | 0 => .error "domain name: circular pointer or too many labels"
  | fuel + 1 =>
    if h : pos < buf.data.size then
      let b := buf.data[pos]
      if b == 0 then
        -- Null terminator: end of name
        let endPos := firstEndPos.getD (pos + 1)
        .ok (#[], endPos)
      else if b.toNat &&& 0xC0 == 0xC0 then
        -- Compression pointer
        if h2 : pos + 1 < buf.data.size then
          let lo := buf.data[pos + 1]
          let offset := (b.toNat &&& 0x3F) * 256 + lo.toNat
          -- Record the end position (pointer consumes 2 bytes at the current level)
          let endPos := firstEndPos.getD (pos + 2)
          match decodeNameAux buf offset fuel (some endPos) with
          | .ok (labels, _) => .ok (labels, endPos)
          | .error e => .error e
        else .error "domain name: truncated pointer"
      else
        -- Label
        let len := b.toNat
        if len > 63 then .error s!"domain name: label length {len} > 63"
        else if pos + 1 + len ≤ buf.data.size then
          let label := buf.extract (pos + 1) (pos + 1 + len)
          match decodeNameAux buf (pos + 1 + len) fuel firstEndPos with
          | .ok (rest, endPos) => .ok (#[label] ++ rest, endPos)
          | .error e => .error e
        else .error "domain name: label truncated"
    else .error "domain name: unexpected end of input"

/-- Decode a domain name from the parser, following compression pointers. -/
def decodeName : DnsParser (Array ByteArray) := do
  let buf ← DnsParser.getBuffer
  let pos ← DnsParser.getPos
  match decodeNameAux buf pos buf.size none with
  | .ok (labels, endPos) =>
    DnsParser.setPos endPos
    return labels
  | .error e => DnsParser.fail e

-- ============================================================
-- Domain name encoding (uncompressed)
-- ============================================================

/-- Encode a domain name as wire-format labels + null terminator. -/
def encodeName (labels : Array ByteArray) : DnsSerializer Unit := do
  for label in labels do
    if label.size > 63 then
      -- Silently truncate (shouldn't happen with valid names)
      DnsSerializer.writeUInt8 63
      DnsSerializer.writeBytes (label.extract 0 63)
    else
      DnsSerializer.writeUInt8 label.size.toUInt8
      DnsSerializer.writeBytes label
  -- Null terminator
  DnsSerializer.writeUInt8 0

-- ============================================================
-- Wire format ↔ labels conversion
--
-- The Spec types store domain names as a flat ByteArray (wire format).
-- These helpers convert between Array ByteArray (labels) and the flat form.
-- ============================================================

/-- Recursive helper: encode labels as length-prefixed bytes + null terminator. -/
def labelsToWireFormatGo : List ByteArray → ByteArray
  | [] => ⟨#[0]⟩
  | l :: rest => (ByteArray.empty.push l.size.toUInt8 ++ l) ++ labelsToWireFormatGo rest

/-- Convert labels to flat wire-format ByteArray (length-prefixed labels + null). -/
def labelsToWireFormat (labels : Array ByteArray) : ByteArray :=
  labelsToWireFormatGo labels.toList

/-- Recursive helper: parse wire-format bytes into labels starting at `pos`. -/
def wireFormatToLabelsGo (wire : ByteArray) (pos : Nat)
    : Except String (List ByteArray) :=
  if h : pos < wire.size then
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

/-- Parse a flat wire-format ByteArray back into labels.
    This only handles uncompressed names (no pointers). -/
def wireFormatToLabels (wire : ByteArray) : Except String (Array ByteArray) :=
  match wireFormatToLabelsGo wire 0 with
  | .ok ls => .ok ls.toArray
  | .error e => .error e

/-- Drop first label from uncompressed wire-format name. None for root/malformed. -/
def parentDomainWire (wire : ByteArray) : Option ByteArray :=
  match wireFormatToLabels wire with
  | .error _ => none
  | .ok labels =>
    if labels.size == 0 then none
    else some (labelsToWireFormat (labels.extract 1 labels.size))

-- ============================================================
-- RFC 1035 §3.1 / §2.3.3: case-insensitive name comparison
-- (generated specs: namespace_compare_caseinsensitive,
--  namespace_compare_example, namespace_nonalphabetic_match_exactly)
-- ============================================================

/-- ASCII case folding: uppercase letters (65–90) fold to lowercase
    (+32); every other code is fixed — "Non-alphabetic codes must match
    exactly". -/
def foldCaseByte (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- Alphabetic ASCII codes (A–Z, a–z) — the range the case fold may touch. -/
def alphabeticByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

/-- Case-fold every byte of a name (or label). Safe on whole wire-format
    names: length bytes are ≤ 63 < 'A', so only label content can fold. -/
def foldNameCase (n : ByteArray) : ByteArray :=
  ⟨n.data.map foldCaseByte⟩

/-- Case-insensitive name/label equality (RFC 1035 §3.1: "Name servers and
    resolvers must compare labels in a case-insensitive manner"). Every
    protocol-level name comparison goes through this. -/
def nameEqCI (a b : ByteArray) : Bool :=
  foldNameCase a == foldNameCase b

/-- Count matching labels from the right (suffix match), comparing labels
    case-insensitively (§3.1). -/
def matchCountLabels (a b : Array ByteArray) : Nat :=
  go a.reverse b.reverse 0 (Nat.min a.size b.size)
where
  go (ra rb : Array ByteArray) (i bound : Nat) : Nat :=
    if i >= bound then i
    else if nameEqCI ra[i]! rb[i]! then go ra rb (i + 1) bound
    else i
  termination_by bound - i

end VeriDNS.Impl.DomainName
