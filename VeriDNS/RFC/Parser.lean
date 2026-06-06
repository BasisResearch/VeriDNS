/-
  RFC text file utilities.

  Handles extracting line ranges from RFC files and stripping
  page break artifacts (the [Page N] / form-feed / header blocks)
  so that `include_rfc` can compare clean text.
-/
import Batteries

namespace RFC.Parser

/-- Check if `sub` is a substring of `s` -/
private def containsSub (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Check if a line is a page break footer like "Mockapetris  [Page 26]" -/
def isPageFooter (line : String) : Bool :=
  containsSub line "[Page " && containsSub line "]"

/-- Check if a line contains a form feed character -/
def isFormFeed (line : String) : Bool :=
  line.any (· == '\x0c')

/-- Check if a line is an RFC header like "RFC 1035  Domain..." -/
def isRfcHeader (line : String) : Bool :=
  (line.trimAsciiStart).toString.startsWith "RFC "

/-- Strip page break artifacts from a list of lines.
    Pattern in old RFCs:
      blank line(s), "Author [Page N]", form-feed, "RFC NNNN ...", blank line(s)
    These interrupt the text mid-section and must be removed. -/
def stripPageBreaks (lines : Array String) : Array String := Id.run do
  let mut toRemove : Array Bool := Array.replicate lines.size false
  for i in [:lines.size] do
    if isFormFeed lines[i]! then
      toRemove := toRemove.set! i true
      -- Scan upward: remove blank lines, the page footer, and blank lines above it
      let mut j := i
      while j > 0 do
        j := j - 1
        let line := lines[j]!
        if line.trimAscii.toString.isEmpty then
          toRemove := toRemove.set! j true
        else if isPageFooter line then
          toRemove := toRemove.set! j true
          -- Continue scanning up to remove blank lines above the footer
          while j > 0 do
            j := j - 1
            if lines[j]!.trimAscii.toString.isEmpty then
              toRemove := toRemove.set! j true
            else
              break
          break
        else
          break
      -- Scan downward: remove RFC header and surrounding blank lines
      let mut k := i + 1
      while k < lines.size do
        let line := lines[k]!
        if line.trimAscii.toString.isEmpty then
          toRemove := toRemove.set! k true
          k := k + 1
        else if isRfcHeader line then
          toRemove := toRemove.set! k true
          k := k + 1
          while k < lines.size && lines[k]!.trimAscii.toString.isEmpty do
            toRemove := toRemove.set! k true
            k := k + 1
          break
        else
          break
  let mut result : Array String := #[]
  for i in [:lines.size] do
    if !toRemove[i]! then
      result := result.push lines[i]!
  return result

/-- Extract lines [from, to] (1-indexed, inclusive) from RFC text,
    with page break artifacts stripped. -/
def extractLines (rfcText : String) (from_ to_ : Nat) : Except String String := do
  if from_ == 0 then
    .error "Line numbers are 1-indexed"
  if from_ > to_ then
    .error s!"Invalid range: {from_} > {to_}"
  let allLines := rfcText.splitOn "\n" |>.toArray
  if to_ > allLines.size then
    .error s!"Line {to_} exceeds file length ({allLines.size} lines)"
  -- Extract the raw range (convert to 0-indexed)
  let rawSlice := allLines.extract (from_ - 1) to_
  -- Strip page breaks within the range
  let cleaned := stripPageBreaks rawSlice
  -- Strip trailing whitespace from each line
  let cleaned := cleaned.map (·.trimAsciiEnd.toString)
  .ok ("\n".intercalate cleaned.toList)

end RFC.Parser
