/-
  AST and parser for semi-formal RFC field description properties.

  Parses sentences from where-block field descriptions into
  structured property nodes. These will be retrofitted into
  logical formulas once the rest of the system is in place.
-/

set_option autoImplicit false

namespace VeriDNS.RFC.Property

/-- AST node for a semi-formal field description property.
    Parsed from RFC where-block descriptions. -/
inductive DescProp where
  | mustBeZero
  | reserved
  | copiedTo (target : String)
  | countsEntriesIn (sect : String)
  | validIn (context : String)
  | setIn (context : String)
  | raw (text : String)
  deriving Repr, BEq, Inhabited

/-- Human-readable label for hover display -/
def DescProp.toLabel : DescProp → String
  | .mustBeZero => "must be zero"
  | .reserved => "reserved"
  | .copiedTo t => s!"copied to {t}"
  | .countsEntriesIn s => s!"counts entries in {s} section"
  | .validIn c => s!"valid in {c}"
  | .setIn c => s!"set in {c}"
  | .raw _ => "unclassified"

-- ============================================================
-- Helpers
-- ============================================================

private def containsCI (s sub : String) : Bool :=
  (s.toLower.splitOn sub.toLower).length > 1

private def trim (s : String) : String := s.trimAscii.toString

/-- Drop a suffix from a string if present -/
private def dropSuffix (s : String) (suffix : String) : String :=
  if s.endsWith suffix then
    s.toList.take (s.length - suffix.length) |>.foldl String.push ""
  else s

-- ============================================================
-- Parsing
-- ============================================================

/-- Split description text into sentences on ". " boundaries -/
def splitSentences (desc : String) : Array String := Id.run do
  let parts := desc.splitOn ". "
  let mut result : Array String := #[]
  for p in parts do
    let t := trim p
    let cleaned := dropSuffix t "."
    if !cleaned.isEmpty then
      result := result.push cleaned
  return result

/-- Extract section name from "...in the X section" -/
private def extractSection (s : String) : Option String := Id.run do
  let parts := s.toLower.splitOn "in the "
  if parts.length < 2 then return none
  let tail := parts[parts.length - 1]!
  let cleaned := dropSuffix (dropSuffix tail " section.") " section"
  let t := trim cleaned
  if t.isEmpty then none else some t

/-- Extract context after a marker phrase, up to comma/period -/
private def extractAfter (s : String) (marker : String) : Option String := Id.run do
  let parts := s.toLower.splitOn marker
  if parts.length < 2 then return none
  let rest := trim parts[parts.length - 1]!
  let t := trim (rest.splitOn ",")[0]!
  let t := trim (t.splitOn ".")[0]!
  if t.isEmpty then none else some t

/-- Classify a single sentence into a DescProp -/
def classifySentence (sentence : String) : DescProp :=
  let s := trim sentence
  if containsCI s "must be zero" then .mustBeZero
  else if s.toLower.startsWith "reserved" then .reserved
  else if containsCI s "copied" && (containsCI s "response" || containsCI s "reply") then
    .copiedTo "response"
  else if containsCI s "number of" && containsCI s "in the" then
    match extractSection s with
    | some sec => .countsEntriesIn sec
    | none => .raw s
  else if containsCI s "valid in" then
    match extractAfter s "valid in " with
    | some ctx => .validIn ctx
    | none => .raw s
  else if containsCI s "set as part of" then
    match extractAfter s "set as part of " with
    | some ctx => .setIn ctx
    | none => .raw s
  else if containsCI s "set in" then
    match extractAfter s "set in " with
    | some ctx => .setIn ctx
    | none => .raw s
  else .raw s

/-- Parse a field description into property AST nodes -/
def parseDescription (desc : String) : Array DescProp :=
  (splitSentences desc).map classifySentence

-- ============================================================
-- Sentence byte position tracking
-- ============================================================

/-- Find byte offsets of sentence boundaries (". " or ".\n") within text.
    Returns byte offsets just after each sentence-ending period. -/
def findSentenceSplitBytes (text : String) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  let mut byteOff : Nat := 0
  let chars := text.toList
  for j in [:chars.length] do
    let c := chars[j]!
    if c == '.' && j + 1 < chars.length then
      let next := chars[j + 1]!
      if next == ' ' || next == '\n' then
        result := result.push (byteOff + c.utf8Size)
    byteOff := byteOff + c.utf8Size
  return result

end VeriDNS.RFC.Property
