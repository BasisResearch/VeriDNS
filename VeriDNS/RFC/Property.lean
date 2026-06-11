/-
  Utilities for RFC field description processing.

  Provides sentence splitting and byte-position tracking for
  where-block field descriptions. Sentence classification is
  handled by the NLP pipeline (NLP.lean).
-/

set_option autoImplicit false

namespace VeriDNS.RFC.Property

-- ============================================================
-- Helpers
-- ============================================================

private def trim (s : String) : String := s.trimAscii.toString

/-- Drop a suffix from a string if present -/
private def dropSuffix (s : String) (suffix : String) : String :=
  if s.endsWith suffix then
    s.toList.take (s.length - suffix.length) |>.foldl String.push ""
  else s

-- ============================================================
-- Sentence splitting
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
