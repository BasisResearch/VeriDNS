/-
  Custom syntax infrastructure for RFC semi-formal constructs.

  Text Processing (pure, reusable):
  - parseBitDiagram: extracts field layout from ASCII bit diagrams
  - parseWhereBlock: extracts field descriptions and value enumerations
  - extractBitWidth: parses English bit-width descriptions

  Elaboration:
  - processRfcText: main pipeline generating Lean definitions from RFC text
  - Generates structures with BitVec fields from bit diagrams
  - Generates inductive types from value enumerations

  De-elaboration:
  - Enum constructors display RFC value descriptions
  - Structure types display ASCII bit diagrams
-/
import Lean
import VeriDNS.RFC.Property
import VeriDNS.RFC.NLP
import VeriDNS.RFC.PropRules

open Lean Elab Command Meta Parser PrettyPrinter

set_option autoImplicit false

namespace VeriDNS.RFC.Syntax

-- ============================================================
-- Data types for intermediate representation
-- ============================================================

/-- A field extracted from an ASCII bit diagram -/
structure DiagramField where
  name : String
  bits : Option Nat   -- None for variable-length (/ delimiters)
  isVariable : Bool
  deriving Repr, Inhabited

/-- A named value in an enumeration table -/
structure EnumValue where
  code : Nat
  name : String
  description : String
  deriving Repr, Inhabited

/-- A field definition from a where block -/
structure WhereField where
  name : String
  description : String
  bits : Option Nat
  values : Array EnumValue
  deriving Repr, Inhabited

/-- Merged field combining diagram layout and where-block semantics -/
structure MergedField where
  name : String
  bits : Option Nat
  isVariable : Bool
  description : String
  values : Array EnumValue
  enumTypeName : Option String
  resolvedType : Option Name
  isArray : Bool
  deriving Repr, Inhabited

/-- A group of fields from a single bit diagram occurrence.
    The first group in a section is the definition; subsequent groups are examples. -/
structure DiagramGroup where
  fields : Array DiagramField
  isExample : Bool
  precedingText : String
  deriving Repr, Inhabited

-- ============================================================
-- String helpers
-- ============================================================

/-- Check if a string contains a substring -/
private def hasSub (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Find all character positions in a string (0-indexed) -/
private def charPositions (s : String) (c : Char) : Array Nat := Id.run do
  let chars := s.toList
  let mut result : Array Nat := #[]
  for i in [:chars.length] do
    if chars[i]! == c then
      result := result.push i
  return result

/-- Extract substring by character index range [i, j) -/
private def sliceStr (s : String) (i j : Nat) : String :=
  String.ofList (s.toList.toArray.extract i j).toList

/-- Trim whitespace from a string, returning a String -/
private def trimStr (s : String) : String :=
  s.trimAscii.toString

/-- Convert word to number -/
private def wordToNum : String → Option Nat
  | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | "five" => some 5
  | "six" => some 6
  | "seven" => some 7
  | "eight" => some 8
  | "sixteen" => some 16
  | _ => none

/-- Capitalize first character -/
private def capitalize (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- Convert word list to camelCase -/
private def toCamelCase (words : List String) : String :=
  match words with
  | [] => ""
  | first :: rest => first.toLower ++ String.join (rest.map capitalize)

/-- Check if a field name is a literal bit value (e.g., "1  1"), not a named field -/
private def isLiteralBitValue (name : String) : Bool :=
  let trimmed := trimStr name
  !trimmed.isEmpty && trimmed.toList.all (fun c => c.isDigit || c == ' ')


-- ============================================================
-- Bit width extraction from English descriptions
-- ============================================================

/-- Extract bit width from RFC description text.
    "A 16 bit identifier" → 16, "A one bit field" → 1,
    "two octets" → 16, "a 32 bit unsigned integer" → 32. -/
def extractBitWidth (desc : String) : Option Nat := Id.run do
  let words := desc.toLower.splitOn " "
    |>.map trimStr |>.filter (!·.isEmpty)
  -- Pattern: "N bit" or "word bit"
  for i in [:words.length] do
    if i + 1 < words.length then
      let next := words[i + 1]!
      if next == "bit" || next.startsWith "bit" then
        if let some n := words[i]!.toNat? then return some n
        if let some n := wordToNum words[i]! then return some n
  -- Pattern: "N octet(s)" or "word octet(s)"
  for i in [:words.length] do
    if i + 1 < words.length then
      if words[i + 1]!.startsWith "octet" then
        if let some n := words[i]!.toNat? then return some (n * 8)
        if let some n := wordToNum words[i]! then return some (n * 8)
  return none

-- ============================================================
-- Bit diagram parser
-- ============================================================

/-- Merge raw diagram fields: handle multi-row fields (empty name = continuation, same name = merge) -/
private def mergeDiagramFields (fields : Array DiagramField) : Array DiagramField := Id.run do
  let mut merged : Array DiagramField := #[]
  for f in fields do
    if f.name.isEmpty then
      if merged.size > 0 then
        let idx := merged.size - 1
        let last := merged[idx]!
        let newBits := match last.bits, f.bits with
          | some a, some b => some (a + b)
          | _, _ => none
        merged := merged.set! idx { last with bits := newBits, isVariable := last.isVariable || f.isVariable }
    else if merged.size > 0 && merged[merged.size - 1]!.name.toUpper == f.name.toUpper then
      let idx := merged.size - 1
      let last := merged[idx]!
      let newBits := match last.bits, f.bits with
        | some a, some b => some (a + b)
        | _, _ => none
      merged := merged.set! idx { last with bits := newBits, isVariable := last.isVariable || f.isVariable }
    else
      merged := merged.push f
  return merged

/-- Parse an ASCII bit diagram into field specifications, returning all diagram groups.

    Each bit cell spans 3 characters in the separator line (+--+).
    Field width = column span between delimiters / 3.
    Fields delimited by / are variable-length.
    Multiple diagrams in the same text produce separate groups;
    the first is the definition and subsequent ones are examples. -/
def parseBitDiagrams (text : String) : Array DiagramGroup := Id.run do
  let lines := text.splitOn "\n"
  let mut groups : Array DiagramGroup := #[]
  let mut currentFields : Array DiagramField := #[]
  let mut inDiagram := false
  let mut precedingText : Array String := #[]

  for line in lines do
    if hasSub line "+--+" then
      if !inDiagram then
        -- Starting a new diagram group
        inDiagram := true
      continue
    if (trimStr line).isEmpty then
      if !inDiagram then
        continue
      else
        -- Blank line inside diagram region — continue
        continue

    let hasBar := line.any (· == '|')
    let hasSlash := line.any (· == '/')
    if !hasBar && !hasSlash then
      if inDiagram then
        -- Non-field content after diagram: finalize current group
        let isExample := groups.size > 0
        -- Definition groups get merged fields; example groups keep raw cells
        let groupFields := if isExample then currentFields else mergeDiagramFields currentFields
        if !groupFields.isEmpty then
          groups := groups.push ⟨groupFields, isExample, "\n".intercalate precedingText.toList⟩
        currentFields := #[]
        precedingText := #[]
        inDiagram := false
      -- Collect preceding text for context
      precedingText := precedingText.push (trimStr line)
      continue

    if !inDiagram then continue

    -- Collect delimiter positions and types
    let chars := line.toList
    let mut delimsArr : Array (Nat × Bool) := #[]
    for i in [:chars.length] do
      if chars[i]! == '|' then delimsArr := delimsArr.push (i, false)
      else if chars[i]! == '/' then delimsArr := delimsArr.push (i, true)
    let sortedDelims := delimsArr.qsort (fun a b => a.1 < b.1)

    for j in [:sortedDelims.size - 1] do
      let (leftPos, leftSlash) := sortedDelims[j]!
      let (rightPos, rightSlash) := sortedDelims[j + 1]!
      let fieldText := trimStr (sliceStr line (leftPos + 1) rightPos)
      let isVar := leftSlash || rightSlash
      let bits := if isVar then none else some ((rightPos - leftPos) / 3)
      currentFields := currentFields.push ⟨fieldText, bits, isVar⟩

  -- Finalize last group if still inside a diagram
  if inDiagram then
    let isExample := groups.size > 0
    let groupFields := if isExample then currentFields else mergeDiagramFields currentFields
    if !groupFields.isEmpty then
      groups := groups.push ⟨groupFields, isExample, "\n".intercalate precedingText.toList⟩

  return groups

/-- Parse an ASCII bit diagram, returning only the first (definition) group's fields.
    Backward-compatible wrapper around parseBitDiagrams. -/
def parseBitDiagram (text : String) : Array DiagramField :=
  match (parseBitDiagrams text)[0]? with
  | some group => group.fields
  | none => #[]

-- ============================================================
-- Section diagram parser
-- ============================================================

/-- Check if a line is a section diagram separator (+----...----+).
    Distinguished from bit diagram separators (+--+--+) by having
    no intermediate + chars (only dashes between the two outer +'s). -/
private def isSectionSeparator (line : String) : Bool :=
  let chars := (trimStr line).toList
  chars.length >= 5 &&
  chars[0]! == '+' &&
  chars[chars.length - 1]! == '+' &&
  (chars.drop 1 |>.dropLast).all (· == '-')

/-- Parse a section diagram into field specifications and inline descriptions.
    Section diagrams use +-----+ separators (no intermediate +) and contain
    field names with optional inline descriptions after the closing |. -/
def parseSectionDiagram (text : String) : Array DiagramField × Array WhereField := Id.run do
  let lines := text.splitOn "\n"
  let mut fields : Array DiagramField := #[]
  let mut whereFields : Array WhereField := #[]
  let mut inDiagram := false
  for line in lines do
    if isSectionSeparator line then
      inDiagram := true
      continue
    if !inDiagram then continue
    let trimmed := trimStr line
    if trimmed.isEmpty then continue
    if !(line.any (· == '|')) then
      break
    let bars := charPositions line '|'
    if bars.size < 2 then continue
    let fieldName := trimStr (sliceStr line (bars[0]! + 1) bars[1]!)
    if fieldName.isEmpty then continue
    fields := fields.push ⟨fieldName, none, true⟩
    -- Inline description: text after the second |
    let inlineDesc := if bars[1]! + 1 < line.toList.length then
      trimStr (sliceStr line (bars[1]! + 1) line.toList.length)
    else ""
    if !inlineDesc.isEmpty then
      whereFields := whereFields.push ⟨fieldName, inlineDesc, none, #[]⟩
  return (fields, whereFields)

-- ============================================================
-- Where block parser
-- ============================================================

/-- Extract enum constructor name from a value description.
    "a standard query (QUERY)" → "query"
    "No error condition" → "noError" -/
private def extractEnumName (desc : String) : String := Id.run do
  -- Try parenthesized name: "... (NAME)"
  let chars := desc.toList
  let mut parenStart : Option Nat := none
  let mut parenEnd : Option Nat := none
  for i in [:chars.length] do
    if chars[i]! == '(' then parenStart := some i
    if chars[i]! == ')' then parenEnd := some i
  if let (some s, some e) := (parenStart, parenEnd) then
    if e > s + 1 then
      return (sliceStr desc (s + 1) e).toLower

  -- Try "Phrase - detailed description"
  let parts := desc.splitOn " - "
  let phrase := if parts.length > 1 then (parts[0]!).trimAscii.toString else desc
  let words := phrase.splitOn " " |>.filter (!·.isEmpty) |>.take 2
  return toCamelCase words

/-- Parse the where block to extract field definitions with descriptions
    and value enumerations. -/
def parseWhereBlock (text : String) : Array WhereField := Id.run do
  let lines := text.splitOn "\n"
  let mut fields : Array WhereField := #[]
  let mut currentName := ""
  let mut currentDesc := ""
  let mut currentValues : Array EnumValue := #[]
  let mut inWhere := false

  for line in lines do
    let trimmed := trimStr line
    if trimmed == "where:" then
      inWhere := true
      continue
    if !inWhere then continue
    if trimmed.isEmpty then continue

    -- Leading whitespace count
    let leadingSpaces := line.toList.takeWhile (· == ' ') |>.length

    -- New field definition: low indent, starts with uppercase
    if leadingSpaces < 8 && !trimmed.isEmpty && trimmed.toList[0]!.isUpper then
      -- Save previous field
      if !currentName.isEmpty then
        fields := fields.push ⟨currentName, trimStr currentDesc,
          extractBitWidth currentDesc, currentValues⟩
      currentValues := #[]
      -- Split "NAME            description text"
      let chars := line.toList
      let mut nameEnd := 0
      for i in [:chars.length] do
        if chars[i]! == ' ' then
          nameEnd := i
          break
      currentName := trimStr (sliceStr line 0 nameEnd)
      let mut descStart := nameEnd
      while descStart < chars.length && chars[descStart]! == ' ' do
        descStart := descStart + 1
      currentDesc := sliceStr line descStart chars.length

    -- Value enumeration: indented, starts with digit
    else if leadingSpaces >= 12 && !trimmed.isEmpty && trimmed.toList[0]!.isDigit then
      -- Skip "3-15  reserved for future use" ranges
      if hasSub trimmed "-" && hasSub trimmed.toLower "reserved" then
        continue
      -- Parse "0               description (NAME)"
      let parts := trimmed.splitOn " " |>.filter (!·.isEmpty)
      if parts.length >= 2 then
        if let some code := parts[0]!.toNat? then
          let desc := " ".intercalate (parts.drop 1)
          let enumName := extractEnumName desc
          currentValues := currentValues.push ⟨code, enumName, desc⟩

    -- Description continuation: after a value entry it belongs to that
    -- value (wrapped lines like "unable to interpret the query."); before
    -- any value it extends the field description. The value's enum NAME
    -- was already derived from its first line and is not recomputed.
    else if leadingSpaces >= 8 && !trimmed.isEmpty then
      if currentValues.isEmpty then
        currentDesc := currentDesc ++ " " ++ trimmed
      else
        let last := currentValues.back!
        currentValues := currentValues.set! (currentValues.size - 1)
          { last with description := last.description ++ " " ++ trimmed }

  -- Save last field
  if !currentName.isEmpty then
    fields := fields.push ⟨currentName, trimStr currentDesc,
      extractBitWidth currentDesc, currentValues⟩

  return fields

-- ============================================================
-- Section title extraction
-- ============================================================

/-- Extract section title from "N.N.N. Title" pattern -/
def extractSectionTitle (text : String) : Option String := Id.run do
  for line in text.splitOn "\n" do
    let trimmed := trimStr line
    if trimmed.isEmpty then continue
    let chars := trimmed.toList
    if !chars[0]!.isDigit then continue
    -- Newer RFC style: "N - Title" / "N.N - Title" (e.g. RFC 2308)
    if hasSub trimmed " - " then
      let numPart := (trimmed.splitOn " - ").headD ""
      if !numPart.isEmpty && numPart.toList.all (fun c => c.isDigit || c == '.') then
        return some (trimStr ((trimmed.splitOn " - ").getD 1 ""))
    let mut i := 0
    let mut dotCount := 0
    while i < chars.length do
      if chars[i]! == '.' then
        dotCount := dotCount + 1
        if i + 1 < chars.length && chars[i + 1]! == ' ' && dotCount >= 2 then
          return some (sliceStr trimmed (i + 2) chars.length)
      else if !chars[i]!.isDigit then
        break
      i := i + 1
  return none

/-- Extract the full section header line ("4.1.1. Header section format") -/
def extractSectionHeader (text : String) : Option String := Id.run do
  for line in text.splitOn "\n" do
    let trimmed := trimStr line
    if trimmed.isEmpty then continue
    let chars := trimmed.toList
    if chars[0]!.isDigit && hasSub trimmed ". " then
      return some trimmed
  return none

/-- Find byte offset and length of the section title line within RFC text.
    Returns (byteOffset, byteLength) relative to text start. -/
def findSectionTitleOffset (text : String) : Option (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut offset : Nat := 0
  for line in lines do
    let trimmed := trimStr line
    if !trimmed.isEmpty then
      let chars := trimmed.toList
      if chars[0]!.isDigit && hasSub trimmed ". " then
        let spaces := line.toList.takeWhile (· == ' ') |>.length
        return some (offset + spaces, trimmed.utf8ByteSize)
    offset := offset + line.utf8ByteSize + 1
  return none

/-- Find byte offset and length of the entire bit diagram (including number scales)
    within RFC text. Returns (byteOffset, byteLength) relative to text start. -/
def findDiagramOffset (text : String) : Option (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut offset : Nat := 0
  let mut startOffset : Option Nat := none
  let mut endOffset : Nat := 0
  let mut inDiagram := false
  let mut preScaleStart : Option Nat := none
  for line in lines do
    let lineByteLen := line.utf8ByteSize
    let trimmed := trimStr line
    if hasSub line "+--+" then
      if !inDiagram then
        startOffset := preScaleStart.orElse (fun _ => some offset)
      inDiagram := true
      endOffset := offset + lineByteLen
    else if inDiagram then
      if line.any (· == '|') || line.any (· == '/') then
        endOffset := offset + lineByteLen
      else if !trimmed.isEmpty then
        break
    else
      if !trimmed.isEmpty then
        if trimmed.toList[0]!.isDigit then
          if preScaleStart.isNone then
            preScaleStart := some offset
        else
          preScaleStart := none
    offset := offset + lineByteLen + 1
  match startOffset with
  | some s => some (s, endOffset - s)
  | none => none

/-- Extract prose text between the section header and the bit diagram -/
def extractProse (text : String) : String := Id.run do
  let lines := text.splitOn "\n"
  let mut proseLines : Array String := #[]
  let mut pastHeader := false
  for line in lines do
    let trimmed := trimStr line
    -- Skip until past section header
    if !pastHeader then
      if !trimmed.isEmpty && trimmed.toList[0]!.isDigit && hasSub trimmed ". " then
        pastHeader := true
      continue
    -- Stop at bit diagram or section diagram
    if hasSub line "+--+" || (line.any (· == '|')) || isSectionSeparator line then break
    -- Stop at "where:"
    if trimmed == "where:" then break
    -- Collect non-empty prose lines
    if !trimmed.isEmpty then
      proseLines := proseLines.push trimmed
  return "\n".intercalate proseLines.toList

/-- Derive structure name: "Header section format" → "Header",
    "Resource record format" → "ResourceRecord",
    "Name space definitions" → "NameSpace" -/
def deriveStructName (title : String) : String :=
  let allWords := title.toLower.splitOn " " |>.filter (!·.isEmpty) |>.map capitalize
  let words := allWords.filter (fun w =>
    w.toLower != "section" && w.toLower != "format" &&
    w.toLower != "definitions" && !w.startsWith "(")
  String.join (if words.isEmpty then allWords else words)

/-- Extract all prose text after the section header (for prose-only sections) -/
def extractAllProse (text : String) : String := Id.run do
  let lines := text.splitOn "\n"
  let mut proseLines : Array String := #[]
  let mut pastHeader := false
  for line in lines do
    let trimmed := trimStr line
    if !pastHeader then
      -- Section headers: "N.N. Title" (RFC 1034/1035) or "N - Title" (RFC 2308+)
      if !trimmed.isEmpty && trimmed.toList[0]!.isDigit
          && (hasSub trimmed ". " || hasSub trimmed " - ") then
        pastHeader := true
      continue
    if !trimmed.isEmpty then
      proseLines := proseLines.push trimmed
  return " ".intercalate proseLines.toList

/-- Extract numeric constraints from prose: "to N octets/bits" and "port N" patterns.
    Returns (value, unit) pairs. -/
def extractConstraintValues (prose : String) : Array (Nat × String × String) := Id.run do
  let words := prose.toLower.splitOn " " |>.toArray |>.filter (!·.isEmpty)
  let mut result : Array (Nat × String × String) := #[]
  for i in [:words.size] do
    if words[i]! == "to" && i + 2 < words.size then
      let unitWord := words[i + 2]!
      if unitWord.startsWith "octet" || unitWord.startsWith "bit" ||
         unitWord.startsWith "byte" then
        let unit := if unitWord.startsWith "bit" then "bits"
          else if unitWord.startsWith "byte" then "bytes" else "octets"
        -- The literal matched phrase, for hover source matching
        let srcPhrase := s!"to {words[i + 1]!} {unitWord}"
        if let some n := words[i + 1]!.toNat? then
          result := result.push (n, unit, srcPhrase)
        else if let some n := wordToNum words[i + 1]! then
          result := result.push (n, unit, srcPhrase)
    -- "port N" pattern
    if words[i]! == "port" && i + 1 < words.size then
      if let some n := words[i + 1]!.toNat? then
        -- Avoid duplicates (port may appear multiple times)
        if !result.any (fun (v, u, _) => v == n && u == "port") then
          result := result.push (n, "port", s!"port {n}")
  return result

-- ============================================================
-- Value-list parser (TYPE/CLASS enumerations)
-- ============================================================

/-- Parse a value enumeration list from RFC text (e.g., section 3.2.2 TYPE values).
    Detects entries with format: NAME  number description (possibly multi-line).
    Maps `*` to constructor name `any`. -/
def parseValueList (text : String) : Array EnumValue := Id.run do
  let lines := text.splitOn "\n"
  let mut result : Array EnumValue := #[]
  let mut i := 0
  while i < lines.length do
    let line := lines[i]!
    let trimmed := trimStr line
    if trimmed.isEmpty then
      i := i + 1
      continue
    -- Skip high-indent continuation lines (handled when parsing entries)
    let leadingSpaces := line.toList.takeWhile (· == ' ') |>.length
    if leadingSpaces >= 8 then
      i := i + 1
      continue
    let parts := trimmed.splitOn " " |>.filter (!·.isEmpty)
    if parts.length < 2 then
      i := i + 1
      continue
    let name := parts[0]!
    -- Name must be uppercase letters, digits, *, or -
    let isValidName := (name == "*") ||
      (!name.isEmpty && name.toList.all (fun c => c.isUpper || c.isDigit || c == '-'))
    if !isValidName then
      i := i + 1
      continue
    match parts[1]!.toNat? with
    | some code =>
      -- Collect description from rest of line + continuation lines
      let desc := " ".intercalate (parts.drop 2)
      let mut fullDesc := desc
      let mut j := i + 1
      while j < lines.length do
        let nextLine := lines[j]!
        let nextTrimmed := trimStr nextLine
        if nextTrimmed.isEmpty then
          j := j + 1
          continue
        let nextLeading := nextLine.toList.takeWhile (· == ' ') |>.length
        if nextLeading >= 16 then
          fullDesc := fullDesc ++ " " ++ nextTrimmed
          j := j + 1
        else
          break
      let ctorName := if name == "*" then "any" else name.toLower
      result := result.push ⟨code, ctorName, fullDesc⟩
      i := j
    | none =>
      i := i + 1
  return result

-- ============================================================
-- Glossary parser (NAME  description format, e.g., §5.3.2)
-- ============================================================

/-- A glossary entry: NAME followed by multi-line description. -/
structure GlossaryEntry where
  name : String        -- "SNAME", "STYPE", etc.
  description : String -- full multi-line description
  deriving Repr, Inhabited

/-- Parse a glossary list from RFC text (e.g., section 5.3.2 resolver state).
    Detects entries where first word is ALL-CAPS, followed by 2+ spaces,
    and second token is NOT a number. Continuation lines at indent ≥ 16. -/
def parseGlossaryList (text : String) : Array GlossaryEntry := Id.run do
  let lines := text.splitOn "\n"
  let mut result : Array GlossaryEntry := #[]
  let mut i := 0
  while i < lines.length do
    let line := lines[i]!
    let trimmed := trimStr line
    if trimmed.isEmpty then
      i := i + 1
      continue
    let parts := trimmed.splitOn " " |>.filter (!·.isEmpty)
    if parts.length < 2 then
      i := i + 1
      continue
    let name := parts[0]!
    -- Name must be ALL-CAPS letters (no digits, no *)
    let isAllCaps := !name.isEmpty && name.toList.all (fun c => c.isUpper)
    if !isAllCaps then
      i := i + 1
      continue
    -- Must NOT have a number as second token (that's a value list)
    if parts[1]!.toNat?.isSome then
      i := i + 1
      continue
    -- Check there are 2+ spaces between name and description in the original line
    let leadingSpaces := line.toList.takeWhile (· == ' ') |>.length
    let nameChars := line.toList.dropWhile (· == ' ') |>.takeWhile (· != ' ')
    let nameEnd := nameChars.length
    let dropCount := leadingSpaces + nameEnd
    let afterName := line.toList.drop dropCount
    let spacesAfterName := afterName.takeWhile (· == ' ') |>.length
    if spacesAfterName < 2 then
      i := i + 1
      continue
    -- Collect description from rest of line + continuation lines
    let desc := " ".intercalate (parts.drop 1)
    let mut fullDesc := desc
    let mut j := i + 1
    while j < lines.length do
      let nextLine := lines[j]!
      let nextTrimmed := trimStr nextLine
      if nextTrimmed.isEmpty then
        j := j + 1
        continue
      let nextLeading := nextLine.toList.takeWhile (· == ' ') |>.length
      if nextLeading >= 16 then
        fullDesc := fullDesc ++ " " ++ nextTrimmed
        j := j + 1
      else
        break
    result := result.push ⟨name, fullDesc⟩
    i := j
  return result

/-- Detect a structural-identity cross-reference — "… of the same
    ⟨form/format/structure⟩ as ⟨REF⟩ …" — and return REF (uppercased, as
    glossary entries are keyed). The frame is parsed from the tagged
    tokens: a "same" premodifier on a structural-identity noun, "as", then
    the referent NP (chunked, so trailing punctuation and relative clauses
    don't leak into the name). -/
def sameFormReference (desc : String) : Option String := Id.run do
  let toks := NLP.tagPOS (NLP.tokenize desc.toLower)
  for i in [:toks.size] do
    let h := toks[i]!.word
    if (h == "form" || h == "format" || h == "structure") &&
        i >= 1 && i + 1 < toks.size &&
        toks[i - 1]!.word == "same" && toks[i + 1]!.word == "as" then
      if let some (refNP, _) := NLP.parseNP toks (i + 2) then
        return some refNP.head.toUpper
  return none

/-- Resolve glossary entry descriptions to Lean types via NLP keyword table + env lookup. -/
def resolveGlossaryFieldTypes (entries : Array GlossaryEntry)
    (env : Environment) (ns : Name) : Array (String × Option Name) := Id.run do
  -- First pass: resolve each entry independently
  let mut resolved : Array (String × Option Name) := #[]
  let mut resolvedMap : Std.HashMap String (Option Name) := {}
  for entry in entries do
    let desc := entry.description.toLower
    let fieldType :=
      if hasSub desc "domain name" then none  -- ByteArray
      else if hasSub desc "qtype" then
        let n := ns ++ Name.mkSimple "Qtype"
        if (env.find? n).isSome then some n else none
      else if hasSub desc "qclass" then
        let n := ns ++ Name.mkSimple "Qclass"
        if (env.find? n).isSome then some n else none
      else if hasSub desc "structure" then none  -- opaque ByteArray
      else none  -- fallback ByteArray
    resolved := resolved.push (entry.name, fieldType)
    resolvedMap := resolvedMap.insert entry.name fieldType
  -- Second pass: resolve structural-identity cross-references
  for i in [:entries.size] do
    if let some refName := sameFormReference entries[i]!.description then
      if let some refType := resolvedMap.get? refName then
        resolved := resolved.set! i (entries[i]!.name, refType)
  return resolved

/-- Extract prose text before the first glossary entry. -/
def extractProseBeforeGlossary (text : String) (entries : Array GlossaryEntry) : String := Id.run do
  if entries.isEmpty then return ""
  let firstName := entries[0]!.name
  let lines := text.splitOn "\n"
  let mut proseLines : Array String := #[]
  let mut pastHeader := false
  for line in lines do
    let trimmed := trimStr line
    if !pastHeader then
      if !trimmed.isEmpty && trimmed.toList[0]!.isDigit && hasSub trimmed ". " then
        pastHeader := true
      continue
    -- Stop at first glossary entry
    if trimmed.startsWith firstName then break
    if !trimmed.isEmpty then
      proseLines := proseLines.push trimmed
  return "\n".intercalate proseLines.toList

-- ============================================================
-- Typeclass spec derivation from glossary descriptions
-- ============================================================

/-- A method derived from NLP clause analysis. -/
structure MethodSpec where
  name : String                     -- verb-derived name
  args : Array (String × Bool)      -- (typeName, isAbstract) — Bool true = needs type param
  returnsSelf : Bool                -- true if method modifies the structure
  returnType : Option (String × Bool) -- (typeName, isAbstract) for getters, none if returnsSelf
  sourceClause : String             -- original RFC text for docstring
  deriving Repr, Inhabited

/-- A predicate derived from relative clauses on object NPs. -/
structure PredicateSpec where
  name : String                     -- e.g., "ttl" (accessor)
  onType : String                   -- which abstract type it's on
  returnType : String               -- e.g., "Nat"
  sourceText : String
  deriving Repr, Inhabited

/-- An axiom linking a method to a predicate. -/
structure AxiomSpec where
  name : String                     -- e.g., "store_mem", "discard_spec"
  body : String                     -- description for docstring generation
  methodName : String               -- which method this constrains
  predicateName : Option String     -- which predicate (if any)
  deriving Repr, Inhabited

/-- Full NLP-derived class specification. -/
structure ClassSpec where
  className : String
  typeParams : Array (String × String) -- (paramLetter, conceptName) e.g., ("RR", "results")
  methods : Array MethodSpec
  predicates : Array PredicateSpec
  axioms : Array AxiomSpec
  deriving Repr, Inhabited

/-- Derive a method name from a verb and optional object.
    Multi-word idioms like "keeps" + "track" → "keepTrack". -/
private def deriveMethodName (verb : String) (objHead : String) : String :=
  let v := verb.toLower
  -- Strip trailing "s"/"es" for third-person singular, handling "includes" → "include"
  let stem := if v.endsWith "bes" || v.endsWith "ces" || v.endsWith "des" ||
    v.endsWith "ges" || v.endsWith "kes" || v.endsWith "les" || v.endsWith "mes" ||
    v.endsWith "nes" || v.endsWith "res" || v.endsWith "ses" || v.endsWith "tes" then
      -- "-es" where the base ends in a consonant + "e": includes→include, describes→describe
      v.dropRight 1
    else if v.endsWith "es" && v.length > 3 then v.dropRight 2  -- "stores"→"stor" → need fix
    else if v.endsWith "s" && !v.endsWith "ss" && v.length > 2 then v.dropRight 1
    else v
  -- Multi-word idiom detection: "keeps track" → "keepTrack"
  if (stem == "keep" || v == "keeps") && objHead.toLower == "track" then "keepTrack"
  else if (stem == "include" || v == "includes") && objHead.toLower == "equivalent" then "zoneName"
  else stem

/-- Resolve a noun phrase head to a type. Returns (typeName, isAbstract).
    Tries env lookup first; if not found, treats as abstract type param. -/
private def resolveNPType (head : String) (preAdjs : Array String)
    (_number : NLP.Number) (env : Environment) (ns : Name)
    : String × Bool := Id.run do
  let h := head.toLower
  -- Try to resolve to an existing Lean type
  let candidates := #[
    ns ++ Name.mkSimple (capitalize h),
    ns ++ Name.mkSimple (capitalize (if h.endsWith "s" then h.dropRight 1 else h))
  ]
  for c in candidates do
    if (env.find? c).isSome then return (toString c, false)
  -- Known DNS domain type mappings
  if hasSub h "name" && preAdjs.any (· == "domain") then return ("ByteArray", false)
  if h == "name" || h == "names" then return ("ByteArray", false)
  if h == "address" || h == "addresses" then return ("BitVec 32", false)
  if h == "count" || h == "number" then return ("Nat", false)
  if h == "zone" then return ("ByteArray", false)
  if h == "guess" || h == "information" || h == "history" then return ("ByteArray", false)
  if h == "track" || h == "equivalent" || h == "form" || h == "time" then return ("ByteArray", false)
  if h == "match" then return ("Nat", false)
  -- Abstract: introduce type parameter
  let singularHead := if h.endsWith "s" && !h.endsWith "ss" then h.dropRight 1 else h
  return (singularHead, true)

/-- Derive a short type parameter letter from a concept name.
    "results" → "RR", "servers" → "NS", "server" → "NS" -/
private def deriveParamLetter (conceptName : String)
    (known : Std.HashMap String String) : String :=
  if let some letter := known.get? conceptName then letter
  else
    let cn := conceptName.toLower
    if cn == "result" || cn == "results" || cn == "rr" || cn == "rrs" then "RR"
    else if cn == "server" || cn == "servers" || hasSub cn "name server" then "NS"
    else if cn == "record" || cn == "records" then "RR"
    else
      -- Use first two chars uppercased
      let chars := cn.toList.take 2 |>.map Char.toUpper
      String.ofList chars

/-- Check if subject head refers to the structure being defined. -/
private def isStructureSubject (head : String) : Bool :=
  let h := head.toLower
  h == "structure" || h == "it" || h == "this" || h == "slist" || h == "sbelt" || h == "cache"

/-- Parse a "whose X has Y" clause into (accessorName, predicateDescription). -/
private def parseWhoseClause (text : String) : String × String :=
  let words := text.splitOn " " |>.filter (!·.isEmpty)
  if words.length >= 1 then
    let accessor := words[0]!.toLower
    let rest := " ".intercalate (words.drop 1)
    (accessor, rest)
  else ("unknown", text)

/-- Infer a ClassSpec from parsed clauses of a glossary entry description.
    Full NLP: grammatical structure determines method signatures, type parameters,
    predicates, and axioms. No verb→method keyword tables. -/
private def inferClassFromClauses (entryName : String) (clauses : Array NLP.Clause)
    (env : Environment) (ns : Name) (rawText : String := "") : ClassSpec := Id.run do
  let mut methods : Array MethodSpec := #[]
  let mut predicates : Array PredicateSpec := #[]
  let mut axioms : Array AxiomSpec := #[]
  let mut typeParams : Array (String × String) := #[]
  let mut knownParams : Std.HashMap String String := {}

  for clause in clauses do
    match clause with
    | .npOnly np =>
      -- First sentence pattern: "a structure which [verb phrase]"
      for pm in np.postMods do
        match pm with
        | .relClause _ text =>
          let subClauses := NLP.reparseRelClause text
          for sc in subClauses do
            match sc with
            | .svo _subj vp obj pps =>
              -- Skip copula clauses (e.g., "are responsible") — they describe state, not methods
              if vp.isCopula then continue
              -- Skip empty object heads
              if obj.head.isEmpty then continue
              let methodName := deriveMethodName vp.verb obj.head
              let (objTypeName, isAbstract) := resolveNPType obj.head obj.preAdjs obj.number env ns
              -- Check if verb modifies Self: PP references the structure, OR verb is inherently state-modifying
              let verbIsStateful := let v := vp.verb.toLower
                v == "stores" || v == "store" || v == "discard" || v == "discards" ||
                v == "add" || v == "adds" || v == "update" || v == "updates" ||
                v == "set" || v == "sets" || v == "remove" || v == "removes"
              let returnsSelf := verbIsStateful || pps.any fun pp =>
                let h := pp.np.head.toLower
                h == "cache" || h == "structure" || h == "list" || h == "slist" ||
                hasSub h entryName.toLower
              -- Register abstract type param if needed
              if isAbstract then
                let paramLetter := deriveParamLetter objTypeName knownParams
                if !typeParams.any (·.1 == paramLetter) then
                  typeParams := typeParams.push (paramLetter, objTypeName)
                knownParams := knownParams.insert objTypeName paramLetter
              -- Extract predicates from relative clauses on object NP
              for pm' in obj.postMods do
                match pm' with
                | .relClause pron relText =>
                  if pron.toLower == "whose" then
                    let (accessorName, _predicateDesc) := parseWhoseClause relText
                    predicates := predicates.push ⟨accessorName, objTypeName, "Nat", relText⟩
                | _ => pure ()
              let isPlural := obj.number == .plural
              methods := methods.push ⟨methodName,
                #[(objTypeName, isAbstract)], returnsSelf,
                if returnsSelf then none
                else some (if isPlural then s!"Array {objTypeName}" else objTypeName, isAbstract),
                vp.verb ++ " " ++ obj.head⟩
            | .svPassive _subj participle pps _negated =>
              let stem := if participle.toLower.endsWith "ing" then
                participle.toLower.dropRight 3 else participle.toLower
              let methodName := stem
              -- Get type from first PP object
              let (argType, isAbstract) := match pps[0]? with
                | some pp => resolveNPType pp.np.head pp.np.preAdjs pp.np.number env ns
                | none => ("ByteArray", false)
              if isAbstract then
                let paramLetter := deriveParamLetter argType knownParams
                if !typeParams.any (·.1 == paramLetter) then
                  typeParams := typeParams.push (paramLetter, argType)
                knownParams := knownParams.insert argType paramLetter
              methods := methods.push ⟨methodName, #[(argType, isAbstract)], true, none, participle⟩
            | _ => pure ()
        | .participle verb objOpt pps =>
          let stem := if verb.toLower.endsWith "ing" then verb.toLower.dropRight 3
            else verb.toLower
          let (argType, isAbstract) := match objOpt with
            | some npd => resolveNPType npd.head npd.preAdjs npd.number env ns
            | none => match pps[0]? with
              | some pp => resolveNPType pp.np.head #[] .unknown env ns
              | none => ("ByteArray", false)
          if isAbstract then
            let paramLetter := deriveParamLetter argType knownParams
            if !typeParams.any (·.1 == paramLetter) then
              typeParams := typeParams.push (paramLetter, argType)
            knownParams := knownParams.insert argType paramLetter
          methods := methods.push ⟨stem, #[(argType, isAbstract)], true, none, verb⟩
        | _ => pure ()
    | .svo _subj vp obj pps =>
      if vp.isCopula then continue
      if obj.head.isEmpty then continue
      let methodName := deriveMethodName vp.verb obj.head
      let (objTypeName, isAbstract) := resolveNPType obj.head obj.preAdjs obj.number env ns
      let verbIsStateful' := let v := vp.verb.toLower
        v == "stores" || v == "store" || v == "discard" || v == "discards" ||
        v == "add" || v == "adds" || v == "update" || v == "updates"
      let returnsSelf := verbIsStateful' || pps.any fun pp =>
        let h := pp.np.head.toLower
        h == "cache" || h == "structure" || h == "list" ||
        hasSub h entryName.toLower
      if isAbstract then
        let paramLetter := deriveParamLetter objTypeName knownParams
        if !typeParams.any (·.1 == paramLetter) then
          typeParams := typeParams.push (paramLetter, objTypeName)
        knownParams := knownParams.insert objTypeName paramLetter
      methods := methods.push ⟨methodName,
        #[(objTypeName, isAbstract)], returnsSelf,
        if returnsSelf then none else some (objTypeName, isAbstract),
        vp.verb ++ " " ++ obj.head⟩
    | _ => pure ()

  -- Deduplicate method names: when same verb produces multiple clauses,
  -- suffix with object type to distinguish (e.g., "describ" → "describServer", "describZone")
  let mut deduped : Array MethodSpec := #[]
  let mut nameCounts : Std.HashMap String Nat := {}
  for m in methods do
    nameCounts := nameCounts.insert m.name ((nameCounts.get? m.name |>.getD 0) + 1)
  let mut seenNames : Std.HashMap String Nat := {}
  for m in methods do
    let count := nameCounts.get? m.name |>.getD 1
    if count > 1 then
      -- Differentiate: extract object noun from sourceClause for natural naming
      let srcWords := m.sourceClause.splitOn " " |>.filter (!·.isEmpty)
      let objWord := if srcWords.length >= 2 then srcWords[1]! else
        match m.args[0]? with | some (n, _) => n | none => toString (seenNames.get? m.name |>.getD 0)
      let uniqueName := m.name ++ capitalize objWord.toLower
      seenNames := seenNames.insert m.name ((seenNames.get? m.name |>.getD 0) + 1)
      deduped := deduped.push { m with name := uniqueName }
    else
      deduped := deduped.push m
  methods := deduped

  -- Temporal store derivation (e.g. §5.3.2 CACHE: "convert the interval
  -- specified in arriving RRs to some sort of absolute time when the RR is
  -- stored"): the store operation additionally takes an absolute time.
  let rawLower := rawText.toLower
  let sentenceContaining (marker : String) : String :=
    (Property.splitSentences rawText).find? (fun s => hasSub s.toLower marker)
      |>.getD marker
  if hasSub rawLower "absolute time" && hasSub rawLower "stored" then
    if let some storeM := methods.find? (·.name == "store") then
      unless methods.any (·.name == "storeAt") do
        methods := methods.push { storeM with
          name := "storeAt"
          args := storeM.args.push ("UInt32", false)
          sourceClause := sentenceContaining "absolute time" }
  -- Periodic sweep derivation ("discards them during periodic sweeps to
  -- reclaim the memory consumed by old RRs"): a time-indexed sweep that only
  -- removes entries (sweep_subset law).
  if hasSub rawLower "periodic sweep" then
    unless methods.any (·.name == "sweep") do
      methods := methods.push ⟨"sweep", #[("UInt32", false)], true, none,
        sentenceContaining "periodic sweep"⟩
      axioms := axioms.push ⟨"sweep_subset",
        "sweep only discards entries (no additions)", "sweep", some "entries"⟩

  -- Post-processing: generate implied getters + axioms for Self-returning methods
  let mut impliedMethods : Array MethodSpec := #[]
  for m in methods do
    if m.returnsSelf then
      for (argName, isAbstract) in m.args do
        if isAbstract then
          let getterName := "entries"
          if !methods.any (·.name == getterName) && !impliedMethods.any (·.name == getterName) then
            let paramLetter := knownParams.get? argName |>.getD argName.toUpper
            impliedMethods := impliedMethods.push ⟨getterName, #[], false,
              some (s!"Array {paramLetter}", true), s!"implied by {m.name}"⟩
          unless axioms.any (·.name == s!"{m.name}_mem") do
            axioms := axioms.push ⟨s!"{m.name}_mem",
              s!"{m.name} implies membership in {getterName}",
              m.name, some getterName⟩

  methods := methods ++ impliedMethods

  -- Generate discard axiom if both store and discard exist
  if methods.any (·.name == "store") && methods.any (·.name == "discard") then
    if !axioms.any (·.name == "discard_spec") then
      axioms := axioms.push ⟨"discard_spec",
        "discard removes only expired entries",
        "discard", some "entries"⟩

  let className := capitalize entryName.toLower ++ "Spec"
  return ⟨className, typeParams, methods, predicates, axioms⟩

-- ============================================================
-- Algorithm step parser (numbered lists, e.g., §5.3.3)
-- ============================================================

/-- A top-level or sub-level algorithm step. -/
structure AlgorithmStep where
  index : Nat          -- step number (1-based for top, 0-based for sub)
  label : Option Char  -- sub-step letter (a, b, c, d) or none for top-level
  description : String
  gotoTarget : Option Nat  -- "go to step N" target
  deriving Repr, Inhabited

/-- Parse a numbered algorithm from RFC text.
    Top-level: lines matching `   N. description`
    Sub-steps: lines matching `         a. description`
    Returns (topSteps, subSteps). -/
def parseNumberedAlgorithm (text : String) : Array AlgorithmStep × Array AlgorithmStep := Id.run do
  let lines := text.splitOn "\n"
  let mut topSteps : Array AlgorithmStep := #[]
  let mut subSteps : Array AlgorithmStep := #[]
  let mut i := 0
  let mut inAlgorithm := false
  -- Once we've seen sub-steps and hit a prose paragraph, stop parsing new top-level steps
  let mut seenSubSteps := false
  let mut doneWithSteps := false
  while i < lines.length do
    let line := lines[i]!
    let trimmed := trimStr line
    let leading := line.toList.takeWhile (· == ' ') |>.length
    -- Once we've parsed sub-steps and encounter left-margin prose, stop
    if seenSubSteps && leading == 0 && !trimmed.isEmpty && !trimmed.toList[0]!.isDigit then
      doneWithSteps := true
    -- Detect top-level step: 3-7 spaces, digit, period, space
    if !doneWithSteps && leading >= 3 && leading <= 7 && !trimmed.isEmpty then
      let parts := trimmed.splitOn "." |>.filter (!·.isEmpty)
      if !parts.isEmpty then
        if let some num := (trimStr parts[0]!).toNat? then
          inAlgorithm := true
          let desc := trimStr ((trimmed.drop ((trimStr parts[0]!).length + 2)).toString)
          -- Collect continuation lines
          let mut fullDesc := desc
          let mut j := i + 1
          while j < lines.length do
            let nextLine := lines[j]!
            let nextTrimmed := trimStr nextLine
            if nextTrimmed.isEmpty then
              j := j + 1
              continue
            let nextLeading := nextLine.toList.takeWhile (· == ' ') |>.length
            -- Sub-step or new top-level step breaks continuation
            if nextLeading >= 8 then
              -- Check if it's a sub-step (letter + period)
              let subParts := nextTrimmed.splitOn "." |>.filter (!·.isEmpty)
              if !subParts.isEmpty then
                let firstPart := trimStr subParts[0]!
                if firstPart.length == 1 && firstPart.toList[0]!.isAlpha then
                  break  -- sub-step
              fullDesc := fullDesc ++ " " ++ nextTrimmed
              j := j + 1
            else if nextLeading >= 3 && nextLeading <= 7 then
              -- Might be next top-level step
              let nextParts := nextTrimmed.splitOn "." |>.filter (!·.isEmpty)
              if !nextParts.isEmpty then
                if (trimStr nextParts[0]!).toNat?.isSome then break
              fullDesc := fullDesc ++ " " ++ nextTrimmed
              j := j + 1
            else
              break
          let gotoTarget := extractGotoTarget fullDesc
          topSteps := topSteps.push ⟨num, none, fullDesc, gotoTarget⟩
          i := j
          continue
    -- Detect sub-step: 8+ spaces, letter, period, space
    if !doneWithSteps && leading >= 8 && inAlgorithm && !trimmed.isEmpty then
      seenSubSteps := true
      let parts := trimmed.splitOn "." |>.filter (!·.isEmpty)
      if !parts.isEmpty then
        let firstPart := trimStr parts[0]!
        if firstPart.length == 1 && firstPart.toList[0]!.isAlpha then
          let letter := firstPart.toList[0]!
          let desc := trimStr ((trimmed.drop 3).toString)
          -- Collect continuation lines
          let mut fullDesc := desc
          let mut j := i + 1
          while j < lines.length do
            let nextLine := lines[j]!
            let nextTrimmed := trimStr nextLine
            if nextTrimmed.isEmpty then
              j := j + 1
              continue
            let nextLeading := nextLine.toList.takeWhile (· == ' ') |>.length
            if nextLeading >= 12 then
              fullDesc := fullDesc ++ " " ++ nextTrimmed
              j := j + 1
            else
              break
          let gotoTarget := extractGotoTarget fullDesc
          subSteps := subSteps.push ⟨0, some letter, fullDesc, gotoTarget⟩
          i := j
          continue
    i := i + 1
  return (topSteps, subSteps)
where
  extractGotoTarget (desc : String) : Option Nat := Id.run do
    let lower := desc.toLower
    -- Look for "go to step N" or "go back to step N"
    for pattern in #["go to step ", "go back to step "] do
      if hasSub lower pattern then
        let parts := lower.splitOn pattern
        if parts.length > 1 then
          let afterPattern := parts[1]!
          let numStr := afterPattern.toList.takeWhile (fun c => c.isDigit) |>.foldl String.push ""
          if let some n := numStr.toNat? then
            return some n
    return none

/-- Derive a constructor name from an algorithm step description via NLP.
    For top-level: verb + first significant noun → camelCase.
    For sub-steps: first distinctive noun after common prefix. -/
def deriveConstructorName (desc : String) (isSubStep : Bool) : String := Id.run do
  -- Strip trailing punctuation from each word
  let stripPunct (w : String) : String :=
    let chars := w.toList.reverse.dropWhile (fun c => c == ',' || c == ':' || c == '.' || c == ';')
    String.ofList chars.reverse
  let words := desc.toLower.splitOn " " |>.filter (!·.isEmpty) |>.map stripPunct
  if isSubStep then
    -- Sub-step naming: look for distinctive keyword
    let lower := desc.toLower
    if hasSub lower "answers the question" || hasSub lower "name error" then
      return "answerOrError"
    if hasSub lower "better delegation" then
      return "delegation"
    if hasSub lower "cname" then
      return "cnameRedirect"
    if hasSub lower "servers failure" || hasSub lower "server failure" || hasSub lower "bizarre" then
      return "serverFailure"
    -- Fallback: first noun-like word
    let skip := #["if", "the", "response", "contains", "shows", "a", "an"]
    for w in words do
      if !skip.contains w && w.length > 2 then return w
    return "unknown"
  else
    -- Top-level: verb + object
    if words.isEmpty then return "unknown"
    let verb := words[0]!
    -- Map common verbs to constructor prefixes
    let verbPrefix := match verb with
      | "see" => "check"
      | "find" => "find"
      | "send" => "send"
      | "analyze" => "analyze"
      | _ => verb
    -- Find first significant noun (skip articles, prepositions)
    let skipWords := #["if", "the", "a", "an", "is", "in", "to", "it", "them", "so",
                        "or", "and", "until", "one", "best", "either"]
    let mut noun := ""
    for w in words.drop 1 do
      if !skipWords.contains w && w.length > 2 then
        noun := w
        break
    if noun.isEmpty then return verbPrefix
    return verbPrefix ++ capitalize noun

-- ============================================================
-- Symbolic NLP and type resolution
-- ============================================================

/-- Determine if a section diagram field should be wrapped in Array,
    using grammatical parsing and semantic derivation from NLP pipeline.
    Parses inline descriptions and prose into SVO clauses, derives
    SectionProp values, then uses those to decide. -/
def shouldBeArray (fieldName : String) (inlineDesc : String) (prose : String) : Bool :=
  NLP.shouldBeArrayNLP fieldName inlineDesc prose

/-- Look up a type name in the environment by namespace + field name.
    Returns the full name if found, otherwise none (falls back to ByteArray). -/
def resolveFieldType (env : Environment) (ns : Name) (fieldName : String) : Option Name :=
  let name := ns ++ Name.mkSimple fieldName
  if (env.find? name).isSome then some name else none

-- ============================================================
-- Example Prop generation from prose
-- ============================================================

/-- Find the bit width of a field by name (case-insensitive) in merged fields. -/
private def findFieldBitWidth (fieldName : String) (fields : Array MergedField)
    : Option Nat :=
  match fields.find? (fun f => f.name.toLower == fieldName.toLower) with
  | some f => f.bits
  | none => none

/-- Check if a field is a variable-length (ByteArray) field. -/
private def isVariableField (fieldName : String) (fields : Array MergedField)
    : Bool :=
  match fields.find? (fun f => f.name.toLower == fieldName.toLower) with
  | some f => f.isVariable || f.bits.isNone
  | none => false

-- ============================================================
-- Cross-referencing
-- ============================================================

/-- Merge diagram layout with where-block semantics -/
def mergeFields (diagram : Array DiagramField) (whereBlock : Array WhereField)
    : Array MergedField := Id.run do
  let mut result : Array MergedField := #[]
  for df in diagram do
    let nameUpper := df.name.toUpper
    let wf := whereBlock.find? (fun wf => wf.name.toUpper == nameUpper)
    let description := wf.map (·.description) |>.getD ""
    let values := wf.map (·.values) |>.getD #[]
    -- Prefer where-block bit width when available, fall back to diagram.
    -- Where-block descriptions are authoritative (e.g., "32 bit" for A ADDRESS
    -- where the diagram only shows one 16-bit row, or "8 bit" for WKS PROTOCOL
    -- where mergeDiagramFields incorrectly merges adjacent unnamed cells).
    let bits := (wf.bind (·.bits)).orElse (fun _ => df.bits)
    -- If description says "variable length", force ByteArray regardless of
    -- extractBitWidth picking up example values (e.g., RDATA's "4 octet" example).
    let isVar := df.isVariable || hasSub description.toLower "variable length"
    let bits := if isVar then none else bits
    let enumTypeName := if values.size > 0 then some (capitalize df.name.toLower) else none
    result := result.push ⟨df.name, bits, isVar, description, values, enumTypeName, none, false⟩
  return result

-- ============================================================
-- Code generation via syntax quotations
-- ============================================================

-- ============================================================
-- Syntax node construction helpers
-- ============================================================

private def mkEmptyDeclModifiers : Syntax :=
  mkNode ``Lean.Parser.Command.declModifiers
    #[mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode]

private def mkDeclId (name : Ident) : Syntax :=
  mkNode ``Lean.Parser.Command.declId #[name, mkNullNode]

private def mkEmptyOptDeclSig : Syntax :=
  mkNode ``Lean.Parser.Command.optDeclSig #[mkNullNode, mkNullNode]

private def mkCtorNode (name : Ident) : Syntax :=
  mkNode ``Lean.Parser.Command.ctor
    #[mkNullNode, mkAtom "|", mkEmptyDeclModifiers, name, mkEmptyOptDeclSig]

private def mkDerivingNode (classes : Array Name) : Syntax :=
  if classes.isEmpty then
    mkNode ``Lean.Parser.Command.optDeriving #[mkNullNode]
  else
    let derivClasses : Array Syntax := classes.map fun c =>
      mkNode ``Lean.Parser.Command.derivingClass #[mkNullNode, mkIdent c]
    let items := derivClasses.toList.intersperse (mkAtom ",") |>.toArray
    mkNode ``Lean.Parser.Command.optDeriving #[mkNullNode #[mkAtom "deriving", mkNullNode items]]

/-- Build a complete `inductive` command syntax node -/
private def mkInductiveCmd (typeName : Ident) (ctorNames : Array Ident)
    (deriving_ : Array Name) : Syntax :=
  let ctorNodes := ctorNames.map mkCtorNode
  mkNode ``Lean.Parser.Command.declaration #[
    mkEmptyDeclModifiers,
    mkNode ``Lean.Parser.Command.inductive #[
      mkAtom "inductive", mkDeclId typeName, mkEmptyOptDeclSig,
      mkNullNode #[mkAtom "where"],
      mkNullNode ctorNodes,
      mkNullNode,
      mkDerivingNode deriving_
    ]
  ]

/-- Build a type syntax node for a structure field.
    Priority: resolvedType > enumTypeName > BitVec > ByteArray.
    Wraps in Array if isArray is set. -/
private def mkFieldTypeSyntax (f : MergedField) : CommandElabM (TSyntax `term) := do
  let baseType ← match f.resolvedType with
    | some name => `($(mkIdent name))
    | none => match f.enumTypeName with
      | some tn => `($(mkIdent (Name.mkSimple tn)))
      | none => match f.bits with
        | some n => `(BitVec $(Syntax.mkNumLit (toString n)))
        | none => `(ByteArray)
  if f.isArray then
    `(Array $baseType)
  else
    pure baseType

/-- Build a structSimpleBinder syntax node -/
private def mkFieldBinder (name : Ident) (type : TSyntax `term) : Syntax :=
  let typeSpec := mkNode ``Lean.Parser.Term.typeSpec #[mkAtom ":", type]
  let optSig := mkNode ``Lean.Parser.Command.optDeclSig #[mkNullNode, mkNullNode #[typeSpec]]
  mkNode ``Lean.Parser.Command.structSimpleBinder
    #[mkEmptyDeclModifiers, name, optSig, mkNullNode]

/-- Build a complete `structure` command syntax node -/
private def mkStructureCmd (structName : Ident) (fieldNames : Array Ident)
    (fieldTypes : Array (TSyntax `term)) (deriving_ : Array Name) : Syntax :=
  let binders := (fieldNames.zip fieldTypes).map fun (n, t) => mkFieldBinder n t
  let structFields := mkNode ``Lean.Parser.Command.structFields #[mkNullNode binders]
  mkNode ``Lean.Parser.Command.declaration #[
    mkEmptyDeclModifiers,
    mkNode ``Lean.Parser.Command.structure #[
      mkNode ``Lean.Parser.Command.structureTk #[mkAtom "structure"],
      mkDeclId structName, mkEmptyOptDeclSig,
      mkNullNode,
      mkNullNode #[mkAtom "where", mkNullNode, structFields],
      mkDerivingNode deriving_
    ]
  ]

/-- Parse and elaborate a command from a string. -/
private def elabCommandStr (s : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← getEnv) `command s "<enum>" with
  | .ok stx => elabCommand stx
  | .error e => throwError "parse error in generated code: {e}"

/-- Generate a `class` command string for parsing via elabCommandStr.
    Classes are parameterized: `class Name (T₁ T₂ : Type) where field₁ : type₁; ...` -/
private def mkClassString (className : String)
    (typeParams : Array String)
    (fieldNames : Array String) (fieldTypeStrs : Array String)
    : String := Id.run do
  let paramStr := if typeParams.isEmpty then ""
    else " (" ++ " ".intercalate typeParams.toList ++ " : Type)"
  let mut fields := ""
  for i in [:fieldNames.size] do
    let fname := fieldNames[i]!
    let ftype := fieldTypeStrs[i]!
    fields := fields ++ s!"\n  {fname} : {ftype}"
  return s!"class {className}{paramStr} where{fields}"

/-- Generate a `structure` command string with type parameters and instance binders.
    `structure Name (S NS C RR : Type) [SlistSpec S NS] [CacheSpec C RR] where ...` -/
private def mkPolymorphicStructString (structName : String)
    (typeParams : Array String)
    (instanceSpecs : Array (String × Array String))  -- (className, paramNames)
    (fieldNames : Array String) (fieldTypeStrs : Array String)
    (derivClasses : Array String)
    : String := Id.run do
  let paramStr := if typeParams.isEmpty then ""
    else " (" ++ " ".intercalate typeParams.toList ++ " : Type)"
  let instStr := String.join (instanceSpecs.toList.map fun (cls, params) =>
    " [" ++ cls ++ " " ++ " ".intercalate params.toList ++ "]")
  let mut fields := ""
  for i in [:fieldNames.size] do
    fields := fields ++ s!"\n  {fieldNames[i]!} : {fieldTypeStrs[i]!}"
  let derivStr := if derivClasses.isEmpty then ""
    else "\n  deriving " ++ ", ".intercalate derivClasses.toList
  return s!"structure {structName}{paramStr}{instStr} where{fields}{derivStr}"

/-- Build a method type string from a MethodSpec. -/
private def mkMethodTypeStr (spec : MethodSpec) (selfParamName : String)
    (knownParams : Std.HashMap String String) : String := Id.run do
  -- Build argument types: Self → arg₁ → ... → returnType
  let mut argParts : Array String := #[selfParamName]
  for (argName, isAbstract) in spec.args do
    if isAbstract then
      let paramLetter := knownParams.get? argName |>.getD argName.toUpper
      argParts := argParts.push paramLetter
    else if argName == "Nat" || argName == "ByteArray" then
      argParts := argParts.push argName
    else
      argParts := argParts.push argName
  -- Return type
  let retPart :=
    if spec.returnsSelf then selfParamName
    else match spec.returnType with
      | some (typeName, isAbstract) =>
        if isAbstract then
          let paramLetter := knownParams.get? typeName |>.getD typeName.toUpper
          if typeName.startsWith "Array " then
            let innerName := (typeName.drop 6).toString
            let innerLetter := knownParams.get? innerName |>.getD innerName.toUpper
            s!"Array {innerLetter}"
          else paramLetter
        else typeName
      | none => selfParamName
  argParts := argParts.push retPart
  return " → ".intercalate argParts.toList

/-- Generate a class declaration from a ClassSpec. Returns the full name. -/
private def generateGlossaryClass (spec : ClassSpec) : CommandElabM Name := do
  let ns ← getCurrNamespace
  let selfParamName := (spec.className.take 1).toString

  -- Build param letter map
  let mut knownParams : Std.HashMap String String := {}
  for (letter, concept) in spec.typeParams do
    knownParams := knownParams.insert concept letter

  let allParamNames := #[selfParamName] ++ spec.typeParams.map (·.1)

  -- Build field names and types as strings
  let mut fieldNames : Array String := #[]
  let mut fieldTypeStrs : Array String := #[]

  for m in spec.methods do
    fieldNames := fieldNames.push m.name
    fieldTypeStrs := fieldTypeStrs.push (mkMethodTypeStr m selfParamName knownParams)

  -- Build predicate fields (accessors)
  for p in spec.predicates do
    fieldNames := fieldNames.push p.name
    let onParamLetter := knownParams.get? p.onType |>.getD p.onType.toUpper
    fieldTypeStrs := fieldTypeStrs.push s!"{onParamLetter} → {p.returnType}"

  -- Build axiom fields. Where the axiom links a Self-returning method to a
  -- getter (the "{m}_mem" implied pair from "stores X" clauses), emit the
  -- membership LAW itself rather than a bare Prop, so instances are forced
  -- to prove it: ∀ c x, x ∈ getter (method c x).
  for ax in spec.axioms do
    fieldNames := fieldNames.push ax.name
    let lawStr? : Option String := Id.run do
      let some getter := ax.predicateName | return none
      let some m := spec.methods.find? (·.name == ax.methodName) | return none
      unless m.returnsSelf do return none
      -- element letter of the getter's Array return type
      let elemLetter := Id.run do
        match spec.methods.find? (·.name == getter) with
        | some g =>
          match g.returnType with
          | some (tn, _) =>
            if tn.startsWith "Array " then return (tn.drop 6).toString
            return "RR"
          | none => return "RR"
        | none => return "RR"
      -- binders for the method's arguments, tracking the first abstract one
      let mut binders := s!"(c : {selfParamName})"
      let mut app := s!"{ax.methodName} c"
      let mut memVar : Option String := none
      let mut idx := 0
      for (argName, isAbstract) in m.args do
        let v := s!"x{idx}"
        let ty := if isAbstract then knownParams.get? argName |>.getD argName.toUpper
          else argName
        binders := binders ++ s!" ({v} : {ty})"
        app := app ++ s!" {v}"
        if isAbstract && memVar.isNone then memVar := some v
        idx := idx + 1
      if ax.name.endsWith "_mem" then
        let some xv := memVar | return none
        return some s!"∀ {binders}, {xv} ∈ {getter} ({app})"
      if ax.name.endsWith "_subset" then
        return some
          s!"∀ {binders} (y : {elemLetter}), y ∈ {getter} ({app}) → y ∈ {getter} c"
      return none
    fieldTypeStrs := fieldTypeStrs.push (lawStr?.getD "Prop")

  let classStr := mkClassString spec.className allParamNames fieldNames fieldTypeStrs
  elabCommandStr classStr

  let fullName := ns ++ Name.mkSimple spec.className
  addDocStringCore fullName s!"Abstract spec for {spec.className} derived from RFC glossary NLP"

  -- Add docstrings to fields
  for m in spec.methods do
    let fieldFullName := fullName ++ Name.mkSimple m.name
    addDocStringCore fieldFullName s!"\"{m.sourceClause}\""
  for p in spec.predicates do
    let fieldFullName := fullName ++ Name.mkSimple p.name
    addDocStringCore fieldFullName s!"\"{p.sourceText}\""
  for ax in spec.axioms do
    let fieldFullName := fullName ++ Name.mkSimple ax.name
    addDocStringCore fieldFullName s!"{ax.body}"

  return fullName

-- ============================================================
-- Code generation
-- ============================================================

/-- Generate toCode, ofCode, value lemmas, and roundtrip theorem for an enum type. -/
private def generateEnumFunctions (fullName : Name) (typeName : String)
    (values : Array EnumValue) : CommandElabM Unit := do
  -- Use short name since we're inside the same namespace
  let qualName := typeName
  -- Build toCode function
  let mut toCodeArms := ""
  for v in values do
    toCodeArms := toCodeArms ++ s!"  | .{v.name} => {v.code}\n"
  elabCommandStr s!"def {qualName}.toCode (x : {qualName}) : Nat :=\n  match x with\n{toCodeArms}"
  -- Build ofCode function
  let mut ofCodeArms := ""
  for v in values do
    ofCodeArms := ofCodeArms ++ s!"  | {v.code} => .ok .{v.name}\n"
  let errMsg := s!"invalid {typeName.toLower}: "
  ofCodeArms := ofCodeArms ++ s!"  | _ => .error (\"{errMsg}\" ++ toString n)\n"
  elabCommandStr s!"def {qualName}.ofCode (n : Nat) : Except String {qualName} :=\n  match n with\n{ofCodeArms}"
  -- Generate individual value lemmas
  for v in values do
    elabCommandStr s!"theorem {qualName}.{v.name}_code : {qualName}.toCode .{v.name} = {v.code} := by rfl"
  -- Generate roundtrip theorem
  elabCommandStr s!"theorem {qualName}.ofCode_toCode (x : {qualName}) : {qualName}.ofCode ({qualName}.toCode x) = .ok x := by cases x <;> rfl"

/-- Generate an inductive type for value enumerations.
    Also generates toCode/ofCode and roundtrip proofs. -/
private def generateEnum (fieldName : String) (values : Array EnumValue)
    : CommandElabM Name := do
  let ns ← getCurrNamespace
  let typeName := capitalize fieldName.toLower
  let typeIdent := mkIdent (Name.mkSimple typeName)
  let fullName := ns ++ Name.mkSimple typeName

  let ctorIdents := values.map fun v => mkIdent (Name.mkSimple v.name)

  elabCommand <| mkInductiveCmd typeIdent ctorIdents #[`Repr, `BEq, `Inhabited]

  -- Add docstrings to constructors
  for v in values do
    let ctorFullName := fullName ++ Name.mkSimple v.name
    (addDocStringCore ctorFullName s!"{v.code}: {v.description}" : CommandElabM Unit)

  generateEnumFunctions fullName typeName values
  return fullName

/-- Generate an inductive type from a value enumeration list section.
    Uses the type name directly (unlike generateEnum which lowercases).
    Also generates toCode/ofCode and roundtrip proofs. -/
private def generateValueListType (typeName : String) (values : Array EnumValue)
    : CommandElabM Name := do
  let ns ← getCurrNamespace
  let typeIdent := mkIdent (Name.mkSimple typeName)
  let fullName := ns ++ Name.mkSimple typeName
  let ctorIdents := values.map fun v => mkIdent (Name.mkSimple v.name)
  elabCommand <| mkInductiveCmd typeIdent ctorIdents #[`Repr, `BEq, `Inhabited]
  for v in values do
    let ctorFullName := fullName ++ Name.mkSimple v.name
    (addDocStringCore ctorFullName s!"{v.code}: {v.description}" : CommandElabM Unit)
  generateEnumFunctions fullName typeName values
  return fullName

/-- Generate a structure from merged field definitions. -/
private def generateStructure (name : String) (docstring : String)
    (fields : Array MergedField) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let structIdent := mkIdent (Name.mkSimple name)
  let fullName := ns ++ Name.mkSimple name

  let fieldIdents := fields.map fun f => mkIdent (Name.mkSimple f.name.toLower)
  let fieldTypes ← fields.mapM mkFieldTypeSyntax

  -- Only derive Repr if all fields have types that support it (ByteArray lacks Repr)
  let hasVariableField := fields.any fun f => f.resolvedType.isNone && f.enumTypeName.isNone && f.bits.isNone
  let derivClasses := if hasVariableField then #[`BEq, `Inhabited] else #[`Repr, `BEq, `Inhabited]
  elabCommand <| mkStructureCmd structIdent fieldIdents fieldTypes derivClasses

  -- Add struct-level docstring
  if !docstring.isEmpty then
    addDocStringCore fullName docstring

  -- Add field-level docstrings
  for i in [:fields.size] do
    let f := fields[i]!
    if !f.description.isEmpty then
      let fieldName := fullName ++ Name.mkSimple f.name.toLower
      addDocStringCore fieldName f.description

/-- Generate inductive types and transition table from parsed algorithm steps. -/
private def generateAlgorithmTypes (sectionName : String)
    (topSteps : Array AlgorithmStep) (subSteps : Array AlgorithmStep)
    : CommandElabM Unit := do
  let ns ← getCurrNamespace
  -- 1. Generate inductive AlgorithmStep
  let stepTypeName := sectionName ++ "Step"
  let stepTypeIdent := mkIdent (Name.mkSimple stepTypeName)
  let stepCtorNames := topSteps.map fun s =>
    mkIdent (Name.mkSimple (deriveConstructorName s.description false))
  elabCommand <| mkInductiveCmd stepTypeIdent stepCtorNames #[`Repr, `BEq, `Inhabited]
  -- Docstrings for step constructors
  let fullStepName := ns ++ Name.mkSimple stepTypeName
  for s in topSteps do
    let ctorName := deriveConstructorName s.description false
    let ctorFullName := fullStepName ++ Name.mkSimple ctorName
    addDocStringCore ctorFullName s!"Step {s.index}: {s.description}"

  -- 2. Generate inductive ResponseAction (from sub-steps)
  if !subSteps.isEmpty then
    let actionTypeName := "ResponseAction"
    let actionTypeIdent := mkIdent (Name.mkSimple actionTypeName)
    let actionCtorNames := subSteps.map fun s =>
      mkIdent (Name.mkSimple (deriveConstructorName s.description true))
    elabCommand <| mkInductiveCmd actionTypeIdent actionCtorNames #[`Repr, `BEq, `Inhabited]
    let fullActionName := ns ++ Name.mkSimple actionTypeName
    for s in subSteps do
      let ctorName := deriveConstructorName s.description true
      let ctorFullName := fullActionName ++ Name.mkSimple ctorName
      let label := match s.label with | some c => s!"{c}" | none => "?"
      addDocStringCore ctorFullName s!"Sub-step {label}: {s.description}"

  -- 3. Generate Transition structure
  let transIdent := mkIdent (Name.mkSimple "Transition")
  let fromIdent := mkIdent (Name.mkSimple "from")
  let actionIdent := mkIdent (Name.mkSimple "action")
  let toIdent := mkIdent (Name.mkSimple "to")
  let stepTypeRef ← `($(mkIdent (Name.mkSimple stepTypeName)))
  let actionTypeRef ← if subSteps.isEmpty
    then `($(mkIdent (Name.mkSimple stepTypeName)))
    else `($(mkIdent (Name.mkSimple "ResponseAction")))
  let fieldNames := #[fromIdent, actionIdent, toIdent]
  let fieldTypes := #[stepTypeRef, actionTypeRef, stepTypeRef]
  elabCommand <| mkStructureCmd transIdent fieldNames fieldTypes #[`Repr, `BEq, `Inhabited]

  -- 4. Generate transition constants from goto targets
  let mut transIdx : Nat := 0
  for s in subSteps do
    if let some target := s.gotoTarget then
      let constName := mkIdent (Name.mkSimple s!"{sectionName.toLower}_transition_{transIdx}")
      -- Find source step (step 4 = analyzeResponse for sub-steps)
      let sourceCtorName := if topSteps.size >= 4
        then deriveConstructorName topSteps[topSteps.size - 1]!.description false
        else "unknown"
      let targetCtorName := if target > 0 && target ≤ topSteps.size
        then deriveConstructorName topSteps[target - 1]!.description false
        else "unknown"
      let actionCtorName := deriveConstructorName s.description true
      let sourceIdent := mkIdent (Name.mkSimple stepTypeName ++ Name.mkSimple sourceCtorName)
      let targetIdent := mkIdent (Name.mkSimple stepTypeName ++ Name.mkSimple targetCtorName)
      let actionRef := mkIdent (Name.mkSimple "ResponseAction" ++ Name.mkSimple actionCtorName)
      let transType := mkIdent (Name.mkSimple "Transition")
      elabCommand (← `(def $constName : $transType := ⟨$sourceIdent, $actionRef, $targetIdent⟩))
      let fullName := ns ++ Name.mkSimple s!"{sectionName.toLower}_transition_{transIdx}"
      addDocStringCore fullName s!"Transition: {sourceCtorName} + {actionCtorName} → step {target} ({targetCtorName})"
      transIdx := transIdx + 1

-- ============================================================
-- Property generation
-- ============================================================

open PropRules

/-- Context for field-level PropSpec interpretation -/
structure FieldInterpContext where
  structName : String
  structIdent : TSyntax `ident
  fieldName : String
  ns : Name

/-- Interpret a FieldRef for field-level rules (simpler context). -/
private def interpretFieldRefForField (ref : FieldRef) (ctx : FieldInterpContext)
    (binders : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  match ref with
  | .currentField =>
    let projIdent := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple ctx.fieldName.toLower)
    let hIdent := binders[binders.size - 1]!
    `($projIdent $hIdent)
  | .namedField name =>
    let projIdent := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple name.toLower)
    let hIdent := binders[binders.size - 1]!
    `($projIdent $hIdent)
  | .pairLeft inner =>
    -- Use second-to-last binder (first of pair)
    let pairIdent := binders[binders.size - 2]!
    let innerTerm ← interpretFieldRefForField inner { ctx with } #[pairIdent]
    return innerTerm
  | .pairRight inner =>
    -- Use last binder (second of pair)
    let pairIdent := binders[binders.size - 1]!
    let innerTerm ← interpretFieldRefForField inner { ctx with } #[pairIdent]
    return innerTerm
  | .lit n =>
    let nLit := Syntax.mkNumLit (toString n)
    `($nLit)
  | .toNat inner =>
    let innerTerm ← interpretFieldRefForField inner ctx binders
    `(BitVec.toNat $innerTerm)
  | .size inner =>
    let innerTerm ← interpretFieldRefForField inner ctx binders
    `(ByteArray.size $innerTerm)
  | .bound idx =>
    if idx < binders.size then
      let binderIdent := binders[binders.size - 1 - idx]!
      `($binderIdent)
    else
      `(True)
  | _ => `(True)

/-- Interpret a PropSpec for field-level rules. -/
private partial def interpretPropSpecForField (spec : PropSpec) (ctx : FieldInterpContext)
    (binders : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  match spec with
  | .forallStruct body =>
    let hIdent : TSyntax `ident := mkIdent `h
    let binders' := binders.push hIdent
    let bodyTerm ← interpretPropSpecForField body ctx binders'
    `(∀ ($hIdent : $(ctx.structIdent)), $bodyTerm)
  | .forallPair body =>
    let aIdent : TSyntax `ident := mkIdent `a
    let bIdent : TSyntax `ident := mkIdent `b
    let binders' := binders.push aIdent |>.push bIdent
    let bodyTerm ← interpretPropSpecForField body ctx binders'
    `(∀ ($aIdent $bIdent : $(ctx.structIdent)), $bodyTerm)
  | .eq lhs rhs =>
    let lhsTerm ← interpretFieldRefForField lhs ctx binders
    let rhsTerm ← interpretFieldRefForField rhs ctx binders
    `($lhsTerm = $rhsTerm)
  | .lt lhs rhs =>
    let lhsTerm ← interpretFieldRefForField lhs ctx binders
    let rhsTerm ← interpretFieldRefForField rhs ctx binders
    `($lhsTerm < $rhsTerm)
  | .le lhs rhs =>
    let lhsTerm ← interpretFieldRefForField lhs ctx binders
    let rhsTerm ← interpretFieldRefForField rhs ctx binders
    `($lhsTerm ≤ $rhsTerm)
  | .gt lhs rhs =>
    let lhsTerm ← interpretFieldRefForField lhs ctx binders
    let rhsTerm ← interpretFieldRefForField rhs ctx binders
    `($lhsTerm > $rhsTerm)
  | .implies ante body =>
    let anteTerm ← interpretPropSpecForField ante ctx binders
    let bodyTerm ← interpretPropSpecForField body ctx binders
    `($anteTerm → $bodyTerm)
  | .conj a b =>
    let aTerm ← interpretPropSpecForField a ctx binders
    let bTerm ← interpretPropSpecForField b ctx binders
    `($aTerm ∧ $bTerm)
  | .trivial => `(True)
  | .neg body =>
    let bodyTerm ← interpretPropSpecForField body ctx binders
    `(¬ $bodyTerm)
  | .disj a b =>
    let aTerm ← interpretPropSpecForField a ctx binders
    let bTerm ← interpretPropSpecForField b ctx binders
    `($aTerm ∨ $bTerm)
  | _ => `(True)

/-- Check if a NLP Clause matches a ClausePattern -/
private def matchesClausePattern (clause : NLP.Clause) (pat : ClausePattern) : Bool :=
  match pat with
  | .adjEquals adj =>
    match clause with
    | .svAdj _ _ comp _ => comp.adj.toLower == adj.toLower
    | _ => false
  | .hasWord word =>
    match clause with
    | .npOnly np =>
      np.preAdjs.any (·.toLower == word.toLower) || np.head.toLower == word.toLower
    | _ => false
  | .textPrefix pfx =>
    match clause with
    | .unparsed text => text.toLower.trimAscii.toString.startsWith pfx.toLower
    | _ => false
  | .textContains word =>
    let w := word.toLower
    let checkPostMods (pms : Array NLP.PostMod) : Bool :=
      pms.any fun pm => match pm with
        | .participle verb _ _ => hasSub verb.toLower w
        | .relClause _ text => hasSub text.toLower w
        | .pp _ npd => hasSub npd.head.toLower w
        | .raw text => hasSub text.toLower w
    let checkFullPPs (pps : Array NLP.PrepPhrase) : Bool :=
      pps.any fun pp =>
        hasSub pp.prep.toLower w || hasSub pp.np.head.toLower w || checkPostMods pp.np.postMods
    match clause with
    | .unparsed text => hasSub text.toLower w
    | .svPassive subj part pps _ =>
      hasSub part.toLower w || checkFullPPs pps || checkPostMods subj.postMods
    | .svAdj _ _ comp _ => hasSub comp.adj.toLower w
    | .svo _ vp _ pps =>
      hasSub vp.verb.toLower w || checkFullPPs pps
    | .npOnly np => checkPostMods np.postMods

/-- Build a formal `Prop` term from a parsed `Clause` and the struct type name.
    Queries registered field-level rules and interprets the first matching
    PropSpec. Returns `none` if no rule matches. -/
private def mkFormalProp (clause : NLP.Clause) (structName : String)
    (fieldName : String) : CommandElabM (Option (TSyntax `term)) := do
  let env ← getEnv
  let rules := fieldPropRuleExt.getState env
  let structIdent := mkIdent (Name.mkSimple structName)
  let ns ← getCurrNamespace
  let ctx : FieldInterpContext := { structName, structIdent, fieldName, ns }
  -- Try each registered rule in order
  for rule in rules do
    if matchesClausePattern clause rule.pattern then
      let propTerm ← interpretPropSpecForField rule.prop ctx #[]
      return some propTerm
  -- No rule matched
  return none

/-- Derive a human-readable label from a Clause for hover display. -/
private def clauseLabel : NLP.Clause → String
  | .svo subj vp obj _ => s!"{subj.head} {vp.verb} {obj.head}"
  | .svAdj subj _ comp _ => s!"{subj.head} is {comp.adj}"
  | .svPassive subj part _ _ => s!"{subj.head} {part}"
  | .npOnly np => np.head
  | .unparsed text => if text.length > 40 then (text.toList.take 40 |>.foldl String.push "") ++ "…" else text

/-- Derive complement-clause semantics from a field description sentence:
    "specifies/denotes/indicates that/whether ⟨C⟩" where C is a copular clause.
    The complement's truth is abstracted as a Bool parameter (the Spec cannot
    know server capability), and quantification is over an abstract emission
    predicate (the claim concerns headers produced by the responding server).
    "that" yields an implication (bit set ⇒ statement); "whether" an iff (the
    bit reflects the statement).
    Returns (isIff, hasResponseGuard, paramName). -/
private def deriveComplementSemantics (sentence : String) : Option (Bool × Bool × String) :=
  Id.run do
  let toks := NLP.tagPOS (NLP.tokenize sentence.toLower)
  -- The frame is found in the tagged tokens: an assertive verb (lexicon)
  -- immediately followed by the complementizer. "that" yields an
  -- implication, "whether" an iff.
  let assertiveVerbs : Array String :=
    #["specify", "specifies", "denote", "denotes", "indicate", "indicates"]
  let mut ci? : Option (Nat × Bool) := none
  for i in [:toks.size] do
    if ci?.isNone && assertiveVerbs.contains toks[i]!.word && i + 1 < toks.size then
      let nxt := toks[i + 1]!.word
      if nxt == "that" then ci? := some (i + 1, false)
      else if nxt == "whether" then ci? := some (i + 1, true)
  let some (ci, isIff) := ci? | return none
  -- guard: a "response" mention in the matrix clause (before the verb)
  let hasRespGuard := (toks.extract 0 (ci - 1)).any
    (fun t => t.word == "response" || t.word == "responses")
  let compToks := toks.extract (ci + 1) toks.size
  -- Complement head: clause parse first, then a token fallback after the
  -- copula. Heads must be alphabetic words (parentheticals like "(0)"
  -- produce junk heads otherwise).
  let validHead (w : String) : Bool :=
    w.length ≥ 3 && w.toList.all Char.isAlpha
  let headWord? : Option String := Id.run do
    let clauseHead? : Option String :=
      match NLP.parseClause compToks with
      | .svAdj _ vp adj _ => if vp.isCopula then some adj.adj else none
      | .svo _ vp obj _ => if vp.isCopula then some obj.head else none
      | .svPassive _ part _ _ => some part
      | _ => none
    if let some hw := clauseHead? then
      if validHead hw then return some hw
    -- Fallback: first valid content word after a copula token
    for k in [:compToks.size] do
      if compToks[k]!.pos == .copula then
        for j in [k + 1:compToks.size] do
          let w := compToks[j]!.word
          if compToks[j]!.pos != .det && w != "not" && validHead w then
            return some w
        return none
    return none
  match headWord? with
  | some head => return some (isIff, hasRespGuard, s!"is{capitalize head}")
  | none => return none

/-- Generate `def {field}_prop_{i} : Prop := ∀ (h : T), ...` for each parsed
    clause (skipping clauses where no rule matches), plus
    `def {field}_semantics_{i}` for complement-clause sentences. -/
private def generateProperties (structName : String) (fields : Array MergedField)
    : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let structFullName := ns ++ Name.mkSimple structName
  let hasQrField := match Lean.getStructureInfo? env structFullName with
    | some sinfo => sinfo.fieldNames.contains (Name.mkSimple "qr")
    | none => false
  for f in fields do
    if f.description.isEmpty then continue
    let clauses := NLP.parseDescriptionClauses f.description
    for i in [:clauses.size] do
      let some propVal ← mkFormalProp clauses[i]! structName f.name | continue
      let propName : Ident := mkIdent (Name.mkSimple s!"{f.name.toLower}_prop_{i}")
      elabCommand (← `(def $propName : Prop := $propVal))
      let fullName := ns ++ Name.mkSimple s!"{f.name.toLower}_prop_{i}"
      let fmt ← liftCoreM (ppTerm propVal)
      addDocStringCore fullName s!"{f.name} — {clauseLabel clauses[i]!}\n```lean\n{fmt.pretty}\n```"
    -- Complement-clause semantics: "specifies that ..."/"denotes whether ..."
    let sentences := Property.splitSentences f.description
    for i in [:sentences.size] do
      let some (isIff, hasRespGuard, paramName) := deriveComplementSemantics sentences[i]!
        | continue
      let semName := mkIdent (Name.mkSimple s!"{f.name.toLower}_semantics_{i}")
      let structIdent := mkIdent (Name.mkSimple structName)
      let hId := mkIdent (Name.mkSimple "h")
      let emittedId := mkIdent (Name.mkSimple "emitted")
      let paramId := mkIdent (Name.mkSimple paramName)
      let fieldProj := mkIdent (Name.mkSimple structName ++ Name.mkSimple f.name.toLower)
      let bitSet ← `($fieldProj $hId = 1)
      let claim ← `($paramId = true)
      let core ← if isIff then `($bitSet ↔ $claim) else `($bitSet → $claim)
      let body ←
        if hasRespGuard && hasQrField then
          let qrProj := mkIdent (Name.mkSimple structName ++ Name.mkSimple "qr")
          `($qrProj $hId = 1 → $core)
        else pure core
      elabCommand (← `(def $semName ($emittedId : $structIdent → Prop)
        ($paramId : Bool) : Prop :=
        ∀ ($hId : $structIdent), $emittedId $hId → $body))
      let fullName := ns ++ Name.mkSimple s!"{f.name.toLower}_semantics_{i}"
      addDocStringCore fullName
        (s!"{f.name} complement semantics (abstracted over the emitter's " ++
         s!"capability `{paramName}`): \"{sentences[i]!}\"")

-- ============================================================
-- Example diagram generation
-- ============================================================

/-- Check if a cell contains space-separated digit groups (e.g., "1  1"),
    which are literal bit markers in pointer diagrams, NOT byte values. -/
private def isLiteralBitMarker (cell : String) : Bool :=
  let trimmed := trimStr cell
  -- Must contain at least one internal space AND be all digits/spaces
  !trimmed.isEmpty &&
  trimmed.toList.all (fun c => c.isDigit || c == ' ') &&
  trimmed.toList.any (· == ' ')

/-- Parse an example diagram cell value as a byte.
    Handles: single digits ("1" → 1), single letters ("F" → 0x46),
    multi-digit numbers ("20" → 20), and literal bit markers ("1  1" → skip).
    Returns none for unparseable cells. -/
private def parseCellAsByte (cell : String) : Option UInt8 :=
  let trimmed := trimStr cell
  if trimmed.isEmpty then none
  else if isLiteralBitMarker trimmed then none
  else
    -- Try numeric interpretation first (handles "1", "20", "255", etc.)
    match trimmed.toNat? with
    | some n => if n < 256 then some n.toUInt8 else none
    | none =>
      -- Single letter: treat as ASCII character
      if trimmed.length == 1 then some trimmed.toList[0]!.toUInt8
      else none

/-- Generate `def` commands from example diagram groups.
    Each example group's parseable cells are collected into a ByteArray.
    Unparseable cells (like "1  1" bit markers) are skipped.
    Groups with no parseable cells are omitted entirely. -/
private def generateExampleCmd (groups : Array DiagramGroup)
    (structName : String) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  for idx in [:groups.size] do
    let group := groups[idx]!
    -- Collect parseable bytes from the diagram cells, skip unparseable ones
    let mut bytes : Array UInt8 := #[]
    for field in group.fields do
      match parseCellAsByte field.name with
      | some b => bytes := bytes.push b
      | none => continue
    if bytes.isEmpty then continue
    -- Generate: def {structName}_example_{idx} : ByteArray := ⟨#[b0, b1, ...]⟩
    let defName := mkIdent (Name.mkSimple s!"{structName.toLower}_example_{idx}")
    let byteExprs : Array (TSyntax `term) := bytes.map fun b =>
      ⟨Syntax.mkNumLit (toString b.toNat)⟩
    let byteLit ← `(#[$byteExprs,*])
    elabCommand (← `(def $defName : ByteArray := ⟨$byteLit⟩))
    let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_example_{idx}"
    addDocStringCore fullName s!"RFC example byte sequence ({bytes.size} bytes)"

-- ============================================================
-- De-elaboration
-- ============================================================

-- Environment extension storing RFC metadata for de-elaboration
-- Maps declaration names to their RFC descriptions
initialize rfcFieldDescriptions : EnvExtension (Std.HashMap Name String) ←
  registerEnvExtension (pure {})

-- Maps enum constructor names to (code, description) pairs
-- Persistent so that enum codes/descriptions survive across modules (e.g.
-- RRType codes stored in Spec/RRType.lean are needed by the refined-guard
-- derivation when elaborating Spec/Resolver.lean).
initialize rfcEnumDescriptions :
    SimplePersistentEnvExtension (Name × Nat × String) (Std.HashMap Name (Nat × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, c, d) => m.insert n (c, d)
    addImportedFn := fun arrs => arrs.foldl
      (fun m arr => arr.foldl (fun m (n, c, d) => m.insert n (c, d)) m) {}
  }

-- Maps structure names to their ASCII diagram text
initialize rfcDiagramText : EnvExtension (Std.HashMap Name String) ←
  registerEnvExtension (pure {})

/-- Normalize section name to match field names.
    "authority records" → "authority", "question" → "question",
    "additional records" → "additional", "answer" → "answer" -/
private def normalizeSectionName (sect : String) : String :=
  let s := sect.toLower.trimAscii.toString
  -- Strip common suffixes (section first, then records)
  let s := if s.endsWith " section" then
      s.toList.take (s.length - " section".length) |>.foldl String.push ""
    else s
  let s := if s.endsWith " records" then
      s.toList.take (s.length - " records".length) |>.foldl String.push ""
    else s
  s.trimAscii.toString

/-- Resolve a section name to a field name in the merged fields.
    Matches "question" → "question", "answer" → "answer", etc. -/
private def resolveSectionToField (sectionName : String) (fields : Array MergedField)
    : Option String :=
  let norm := normalizeSectionName sectionName
  -- Direct match
  fields.find? (fun f => f.name.toLower == norm) |>.map (·.name)

/-- Get the field names of a Lean structure type, if it exists. -/
private def getStructFieldNames (env : Environment) (structName : Name)
    : Array Name :=
  match Lean.getStructureInfo? env structName with
  | some info => info.fieldNames
  | none => #[]

-- ============================================================
-- Cross-struct rule registration and dispatch
-- ============================================================

cross_struct_rule {
  name := "count_entries"
  pattern := {
    verbs := #["specifying", "specifies"]
    objHead := some #["number"]
    requiredPPs := #[("of", #["entries", "records"])]
  }
  prop := .forallStruct (.eq (.toNat .matchedSubField) (.size (.resolvedFromPP "in")))
}

cross_struct_rule {
  name := "domain_name_valid"
  pattern := {
    verbs := #["represented"]
    requiredPPs := #[("as", #["sequence"])]
  }
  prop := .forallStruct (.forallMatchedIndex
    (.existsTyped "Array ByteArray" (.forallElem (.bound 0)
      (.conj (.lt (.lit 0) (.size (.bound 0)))
             (.le (.size (.bound 0)) (.lit 63))))))
}

field_prop_rule {
  name := "zero_adj"
  pattern := .adjEquals "zero"
  prop := .forallStruct (.eq .currentField (.lit 0))
}

field_prop_rule {
  name := "reserved_np"
  pattern := .hasWord "reserved"
  prop := .forallStruct (.eq .currentField (.lit 0))
}

field_prop_rule {
  name := "reserved_text"
  pattern := .textPrefix "reserved"
  prop := .forallStruct (.eq .currentField (.lit 0))
}

-- Response-only fields: "in response" → must be zero when QR=0 (query)
field_prop_rule {
  name := "response_only"
  pattern := .textContains "in response"
  prop := .forallStruct (.implies
    (.eq (.namedField "qr") (.lit 0))
    (.eq .currentField (.lit 0)))
}

-- Cross-message field copying: "copied" → equal between query and response
field_prop_rule {
  name := "copied_to_response"
  pattern := .textContains "copied"
  prop := .forallPair (.implies
    (.conj (.eq (.pairLeft (.namedField "qr")) (.lit 0))
           (.eq (.pairRight (.namedField "qr")) (.lit 1)))
    (.eq (.pairLeft .currentField) (.pairRight .currentField)))
}

-- RDLENGTH = RDATA size
field_prop_rule {
  name := "length_of_rdata"
  pattern := .textContains "length in octets of the rdata"
  prop := .forallStruct (.eq (.toNat .currentField) (.size (.namedField "rdata")))
}

-- Prose-clause rules: match NLP Clause structure directly

-- "Messages are restricted/limited to N units"
prose_clause_rule {
  name := "size_bound"
  pattern := {
    verbs := #["restricted", "limited"]
    requiredPPs := #[("to", #[])]
    extractions := #[{ name := "value", slot := .ppNumeric "to" }]
  }
  output := .forallStruct (.le (.size (.namedField "data")) (.extractedNat "value"))
}

-- "The message is prefixed with a two byte length field"
prose_clause_rule {
  name := "prefix_field"
  pattern := {
    verbs := #["prefixed"]
    requiredPPs := #[("with", #[])]
    extractions := #[{ name := "bitWidth", slot := .ppBitWidth "with" }]
  }
  output := .seq
    (.declField "lengthField" (.extractedNat "bitWidth"))
    (.forallStruct (.eq (.toNat (.namedField "lengthfield")) (.size (.namedField "data"))))
}

-- "the TC bit is set in the header"
prose_clause_rule {
  name := "bit_set_implies"
  pattern := {
    verbs := #["set"]
    subjHead := some #["bit", "flag"]
    requiredPPs := #[("in", #[])]
    extractions := #[
      { name := "fieldName", slot := .subjPreAdjs },
      { name := "location", slot := .ppLocation "in" }
    ]
  }
  output := .forallStruct (.implies
    (.gt (.size (.namedField "data")) (.extractedNat "threshold"))
    (.eq (.resolvedExtField "location" "fieldName") (.lit 1)))
}

-- Cache-related prose-clause rules

-- "stores the results from previous responses" → entries field
prose_clause_rule {
  name := "stores_results"
  pattern := { verbs := #["stores", "store"], requiredPPs := #[("from", #[])], matchActive := true }
  output := .declField "entries" (.lit 0)
}

-- "convert the interval to absolute time" → absoluteTime field
prose_clause_rule {
  name := "convert_to_absolute"
  pattern := { verbs := #["convert"], requiredPPs := #[("to", #["time"])], matchActive := true }
  output := .declField "absoluteTime" (.lit 32)
}

-- "depends on 32 bit timers in units of seconds" → timer field
prose_clause_rule {
  name := "timer_seconds"
  pattern := { verbs := #["depends"], requiredPPs := #[("on", #[])],
               extractions := #[{ name := "bitWidth", slot := .ppBitWidth "on" }], matchActive := true }
  output := .declField "timer" (.extractedNat "bitWidth")
}

-- "should not be cached" / "the data should not be cached" → cacheable = 0
prose_clause_rule {
  name := "should_not_cache"
  pattern := { verbs := #["cached"], requireNegation := true }
  output := .seq (.declField "cacheable" (.lit 1))
    (.forallStruct (.eq (.namedField "cacheable") (.lit 0)))
}

-- "should never be used in preference to authoritative data"
prose_clause_rule {
  name := "never_prefer_cached"
  pattern := { verbs := #["used"], subjHead := some #["data"],
               requiredPPs := #[("in", #["preference"])], requireNegation := true }
  output := .seq (.declField "preferAuthoritative" (.lit 1))
    (.forallStruct (.eq (.namedField "preferauthoritative") (.lit 1)))
}

-- "should never be combined"
prose_clause_rule {
  name := "never_combine"
  pattern := { verbs := #["combined"], requireNegation := true }
  output := .seq (.declField "sourcesMerged" (.lit 1))
    (.forallStruct (.neg (.eq (.namedField "sourcesmerged") (.lit 1))))
}

-- "data is expired and should be ignored"
prose_clause_rule {
  name := "expired_ignore"
  pattern := { verbs := #["expired", "ignored"], subjHead := some #["data", "TTL"] }
  output := .seq (.declField "expired" (.lit 1))
    (.forallStruct (.implies
      (.le (.lit 2147483648) (.toNat (.namedField "timer")))
      (.eq (.namedField "expired") (.lit 1))))
}

-- Resolver algorithm rules (§5.3.3) — derived via full NLP inference in algorithm path

-- ============================================================
-- Prose clause matching + unified PropSpec interpreter
-- ============================================================

/-- Context for prose-level PropSpec interpretation -/
structure ProseInterpContext where
  structName : String
  structIdent : TSyntax `ident
  ns : Name
  /-- Binder for the primary struct (set when forallStruct processes). -/
  structBinder : Option (TSyntax `ident) := none

/-- Result from interpreting a PropSpec tree: struct fields + prop terms. -/
structure ProseInterpResult where
  structFields : Array (String × Nat)
  propTerms : Array (TSyntax `term)
  deriving Inhabited

instance : Append ProseInterpResult where
  append a b := ⟨a.structFields ++ b.structFields, a.propTerms ++ b.propTerms⟩

/-- Extract a value from a slot in a matched clause. -/
private def extractFromSlot (clause : NLP.Clause) (slot : ValueSlot)
    : Option (Nat ⊕ String) :=
  match slot with
  | .ppNumeric prep =>
    match clause with
    | .svPassive _ _ pps _ =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == prep then
          pp.np.preAdjs.findSome? fun adj => adj.toNat?.map Sum.inl
        else none
    | .svo _ _ _ pps =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == prep then
          pp.np.preAdjs.findSome? fun adj => adj.toNat?.map Sum.inl
        else none
    | _ => none
  | .ppBitWidth prep =>
    match clause with
    | .svPassive _ _ pps _ =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == prep then
          let npWords := pp.np.preAdjs ++ #[pp.np.head]
          (NLP.extractBitWidthFromNPText npWords).map Sum.inl
        else none
    | .svo _ _ _ pps =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == prep then
          let npWords := pp.np.preAdjs ++ #[pp.np.head]
          (NLP.extractBitWidthFromNPText npWords).map Sum.inl
        else none
    | _ => none
  | .subjPreAdjs =>
    match clause with
    | .svPassive subj _ _ _ =>
      let preAdjs := subj.preAdjs.map (·.toLower)
      if preAdjs.isEmpty then none
      else some (.inr (" ".intercalate preAdjs.toList))
    | _ => none
  | .subjQualifier =>
    match clause with
    | .svPassive subj _ _ _ => (NLP.extractProtocolQualifier subj).map Sum.inr
    | _ => none
  | .ppHead prep =>
    match clause with
    | .svPassive _ _ pps _ =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == prep then some (.inr pp.np.head) else none
    | _ => none
  | .ppLocation prep =>
    match clause with
    | .svPassive _ _ pps _ =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == prep then some (.inr pp.np.head) else none
    | _ => none

/-- Match a prose clause pattern against an NLP Clause.
    Returns bindings map on success. -/
private def matchProseClausePattern (clause : NLP.Clause) (pat : ProseClausePattern)
    : Option (Std.HashMap String (Nat ⊕ String)) := do
  -- Match verb and subject
  match clause with
  | .svPassive subj participle pps negated =>
    let p := participle.toLower
    unless pat.verbs.contains p do failure
    -- Subject head filter
    match pat.subjHead with
    | some heads => unless heads.contains subj.head.toLower do failure
    | none => pure ()
    -- Negation check
    if pat.requireNegation && !negated then failure
    -- Required PPs
    for (prep, heads) in pat.requiredPPs do
      let found := pps.any fun pp =>
        pp.prep.toLower == prep &&
        (heads.isEmpty || heads.contains pp.np.head.toLower)
      unless found do failure
    -- Extract bindings
    let mut bindings : Std.HashMap String (Nat ⊕ String) := {}
    for ext in pat.extractions do
      match extractFromSlot clause ext.slot with
      | some val => bindings := bindings.insert ext.name val
      | none => if ext.required then failure
    return bindings
  | .svo subj vp _obj pps =>
    unless pat.matchActive do failure
    let v := vp.verb.toLower
    unless pat.verbs.contains v do failure
    match pat.subjHead with
    | some heads => unless heads.contains subj.head.toLower do failure
    | none => pure ()
    -- Negation check for active voice
    if pat.requireNegation then
      let negated := vp.adv == some "not" || vp.adv == some "never"
      unless negated do failure
    for (prep, heads) in pat.requiredPPs do
      let found := pps.any fun pp =>
        pp.prep.toLower == prep &&
        (heads.isEmpty || heads.contains pp.np.head.toLower)
      unless found do failure
    let mut bindings : Std.HashMap String (Nat ⊕ String) := {}
    for ext in pat.extractions do
      match extractFromSlot clause ext.slot with
      | some val => bindings := bindings.insert ext.name val
      | none => if ext.required then failure
    return bindings
  | _ => failure

/-- Capitalize the first letter of a string. -/
private def capitalize' (s : String) : String :=
  if s.isEmpty then s
  else s.get 0 |>.toUpper |>.toString ++ s.drop 1

/-- Interpret a FieldRef for prose-level rules with binding resolution. -/
private def interpretFieldRefForProse (ref : FieldRef) (ctx : ProseInterpContext)
    (binders : Array (TSyntax `ident))
    (bindings : Std.HashMap String (Nat ⊕ String))
    : CommandElabM (TSyntax `term) := do
  match ref with
  | .namedField name =>
    let projIdent := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple name.toLower)
    -- Use struct binder if set (avoids confusion with ext binders)
    let msgIdent := ctx.structBinder.getD binders[binders.size - 1]!
    `($projIdent $msgIdent)
  | .pairLeft inner =>
    let pairIdent := binders[binders.size - 2]!
    interpretFieldRefForProse inner { ctx with structBinder := some pairIdent } #[pairIdent] bindings
  | .pairRight inner =>
    let pairIdent := binders[binders.size - 1]!
    interpretFieldRefForProse inner { ctx with structBinder := some pairIdent } #[pairIdent] bindings
  | .lit n =>
    let nLit := Syntax.mkNumLit (toString n)
    `($nLit)
  | .extractedNat bindingName =>
    match bindings.get? bindingName with
    | some (.inl n) =>
      let nLit := Syntax.mkNumLit (toString n)
      `($nLit)
    | _ => `(0)
  | .toNat inner =>
    let innerTerm ← interpretFieldRefForProse inner ctx binders bindings
    `(BitVec.toNat $innerTerm)
  | .size inner =>
    let innerTerm ← interpretFieldRefForProse inner ctx binders bindings
    `(ByteArray.size $innerTerm)
  | .bound idx =>
    if idx < binders.size then
      let binderIdent := binders[binders.size - 1 - idx]!
      `($binderIdent)
    else
      `(True)
  | .resolvedExtField locBinding fieldBinding =>
    -- Cross-spec field reference: resolve location to type, fieldName to field
    let env ← getEnv
    let locationStr := match bindings.get? locBinding with
      | some (.inr s) => s | _ => ctx.structName
    let _fieldStr := match bindings.get? fieldBinding with
      | some (.inr s) => s.splitOn " " |>.getLast!.toLower | _ => ""
    let extStructName := capitalize' locationStr.toLower
    let extTypeName := ctx.ns ++ Name.mkSimple extStructName
    if (env.find? extTypeName).isSome then
      let extFieldFQN := extTypeName ++ Name.mkSimple _fieldStr
      if (env.find? extFieldFQN).isSome then
        -- ext binder is the last binder
        let extIdent := binders[binders.size - 1]!
        let extFieldProj := mkIdent extFieldFQN
        `($extFieldProj $extIdent)
      else `(True)
    else `(True)
  | .fieldPath _ _ => `(True)
  | _ => `(True)

/-- Interpret a PropSpec for prose-level rules with binding resolution. -/
private partial def interpretPropSpecForProse (spec : PropSpec) (ctx : ProseInterpContext)
    (binders : Array (TSyntax `ident))
    (bindings : Std.HashMap String (Nat ⊕ String))
    : CommandElabM (ProseInterpResult) := do
  match spec with
  | .declField name bitWidthRef =>
    let bw := match bitWidthRef with
      | .extractedNat bindingName =>
        match bindings.get? bindingName with
        | some (.inl n) => n
        | _ => 16  -- default
      | .lit n => n
      | _ => 16
    return ⟨#[(name, bw)], #[]⟩
  | .seq a b =>
    let ra ← interpretPropSpecForProse a ctx binders bindings
    let rb ← interpretPropSpecForProse b ctx binders bindings
    return ra ++ rb
  | .forallStruct body =>
    -- Check if body contains .resolvedExtField — if so, add extra binder
    let hasExtRef := containsExtRef body
    let msgIdent : TSyntax `ident := mkIdent `msg
    let ctx' := { ctx with structBinder := some msgIdent }
    if hasExtRef then
      -- ∀ (msg : Struct) (ext : ExtStruct), body
      let extIdent : TSyntax `ident := mkIdent `ext
      let binders' := binders.push msgIdent |>.push extIdent
      -- Resolve ext struct type from bindings
      let locationStr := findLocationBinding body bindings
      let extStructName := capitalize' locationStr.toLower
      let extTypeIdent := mkIdent (ctx.ns ++ Name.mkSimple extStructName)
      let bodyResult ← interpretPropSpecForProse body ctx' binders' bindings
      let propTerms ← bodyResult.propTerms.mapM fun bodyTerm => do
        `(∀ ($msgIdent : $(ctx.structIdent)) ($extIdent : $extTypeIdent), $bodyTerm)
      return ⟨bodyResult.structFields, propTerms⟩
    else
      let binders' := binders.push msgIdent
      let bodyResult ← interpretPropSpecForProse body ctx' binders' bindings
      let propTerms ← bodyResult.propTerms.mapM fun bodyTerm => do
        `(∀ ($msgIdent : $(ctx.structIdent)), $bodyTerm)
      return ⟨bodyResult.structFields, propTerms⟩
  | .forallPair body =>
    let aIdent : TSyntax `ident := mkIdent `a
    let bIdent : TSyntax `ident := mkIdent `b
    let binders' := binders.push aIdent |>.push bIdent
    let bodyResult ← interpretPropSpecForProse body ctx binders' bindings
    let propTerms ← bodyResult.propTerms.mapM fun bodyTerm => do
      `(∀ ($aIdent $bIdent : $(ctx.structIdent)), $bodyTerm)
    return ⟨bodyResult.structFields, propTerms⟩
  | .forallElem container body =>
    let elemIdent : TSyntax `ident := mkIdent `elem
    let binders' := binders.push elemIdent
    let containerTerm ← interpretFieldRefForProse container ctx binders bindings
    let bodyResult ← interpretPropSpecForProse body ctx binders' bindings
    let propTerms ← bodyResult.propTerms.mapM fun bodyTerm => do
      `(∀ ($elemIdent : ByteArray), $elemIdent ∈ $containerTerm → $bodyTerm)
    return ⟨bodyResult.structFields, propTerms⟩
  | .eq lhs rhs =>
    let lhsTerm ← interpretFieldRefForProse lhs ctx binders bindings
    -- When comparing resolvedExtField (BitVec) with lit, annotate the literal
    let rhsTerm ← match lhs, rhs with
    | .resolvedExtField locBinding fieldBinding, .lit n =>
      -- Look up the external field to determine its BitVec width
      let env ← getEnv
      let locationStr := match bindings.get? locBinding with
        | some (.inr s) => s | _ => ctx.structName
      let fieldStr := match bindings.get? fieldBinding with
        | some (.inr s) => s.splitOn " " |>.getLast!.toLower | _ => ""
      let extStructName := capitalize' locationStr.toLower
      let extTypeName := ctx.ns ++ Name.mkSimple extStructName
      -- Default to BitVec 1 for bit fields
      let bw := match Lean.getStructureInfo? env extTypeName with
        | some _ => 1  -- default to 1 for bit fields
        | none => 1
      let nLit := Syntax.mkNumLit (toString n)
      let bwLit := Syntax.mkNumLit (toString bw)
      `(($nLit : BitVec $bwLit))
    | _, _ => interpretFieldRefForProse rhs ctx binders bindings
    let t ← `($lhsTerm = $rhsTerm)
    return ⟨#[], #[t]⟩
  | .lt lhs rhs =>
    let lhsTerm ← interpretFieldRefForProse lhs ctx binders bindings
    let rhsTerm ← interpretFieldRefForProse rhs ctx binders bindings
    let t ← `($lhsTerm < $rhsTerm)
    return ⟨#[], #[t]⟩
  | .le lhs rhs =>
    let lhsTerm ← interpretFieldRefForProse lhs ctx binders bindings
    let rhsTerm ← interpretFieldRefForProse rhs ctx binders bindings
    let t ← `($lhsTerm ≤ $rhsTerm)
    return ⟨#[], #[t]⟩
  | .gt lhs rhs =>
    let lhsTerm ← interpretFieldRefForProse lhs ctx binders bindings
    let rhsTerm ← interpretFieldRefForProse rhs ctx binders bindings
    let t ← `($lhsTerm > $rhsTerm)
    return ⟨#[], #[t]⟩
  | .implies ante body =>
    let anteResult ← interpretPropSpecForProse ante ctx binders bindings
    let bodyResult ← interpretPropSpecForProse body ctx binders bindings
    -- Combine: each ante term → each body term (typically one each)
    let mut terms : Array (TSyntax `term) := #[]
    for anteTerm in anteResult.propTerms do
      for bodyTerm in bodyResult.propTerms do
        terms := terms.push (← `($anteTerm → $bodyTerm))
    return ⟨anteResult.structFields ++ bodyResult.structFields, terms⟩
  | .conj a b =>
    let ra ← interpretPropSpecForProse a ctx binders bindings
    let rb ← interpretPropSpecForProse b ctx binders bindings
    let mut terms : Array (TSyntax `term) := #[]
    for at_ in ra.propTerms do
      for bt in rb.propTerms do
        terms := terms.push (← `($at_ ∧ $bt))
    return ⟨ra.structFields ++ rb.structFields, terms⟩
  | .trivial =>
    let t ← `(True)
    return ⟨#[], #[t]⟩
  | .neg body =>
    let bodyResult ← interpretPropSpecForProse body ctx binders bindings
    let propTerms ← bodyResult.propTerms.mapM fun bodyTerm => do
      `(¬ $bodyTerm)
    return ⟨bodyResult.structFields, propTerms⟩
  | .disj a b =>
    let ra ← interpretPropSpecForProse a ctx binders bindings
    let rb ← interpretPropSpecForProse b ctx binders bindings
    let mut terms : Array (TSyntax `term) := #[]
    for at_ in ra.propTerms do
      for bt in rb.propTerms do
        terms := terms.push (← `($at_ ∨ $bt))
    return ⟨ra.structFields ++ rb.structFields, terms⟩
  | .forallNamed _ body =>
    -- Prose context doesn't use named types — fall through to struct-based
    interpretPropSpecForProse body ctx binders bindings
  | .forallNamedPair _ body =>
    interpretPropSpecForProse body ctx binders bindings
  | _ => return ⟨#[], #[]⟩
where
  /-- Check if a PropSpec contains resolvedExtField references. -/
  containsExtRef : PropSpec → Bool
    | .implies a b => containsExtRef a || containsExtRef b
    | .conj a b => containsExtRef a || containsExtRef b
    | .disj a b => containsExtRef a || containsExtRef b
    | .neg body => containsExtRef body
    | .forallStruct body => containsExtRef body
    | .forallPair body => containsExtRef body
    | .forallElem _ body => containsExtRef body
    | .seq a b => containsExtRef a || containsExtRef b
    | .eq lhs rhs => isExtRef lhs || isExtRef rhs
    | .gt lhs rhs => isExtRef lhs || isExtRef rhs
    | .le lhs rhs => isExtRef lhs || isExtRef rhs
    | .lt lhs rhs => isExtRef lhs || isExtRef rhs
    | _ => false
  isExtRef : FieldRef → Bool
    | .resolvedExtField _ _ => true
    | .toNat r => isExtRef r
    | .size r => isExtRef r
    | .pairLeft r => isExtRef r
    | .pairRight r => isExtRef r
    | _ => false
  /-- Find the location string from a resolvedExtField in a PropSpec. -/
  findLocationBinding (spec : PropSpec) (bindings : Std.HashMap String (Nat ⊕ String)) : String :=
    match findLocRef spec with
    | some locBinding =>
      match bindings.get? locBinding with
      | some (.inr s) => s
      | _ => ""
    | none => ""
  findLocRef : PropSpec → Option String
    | .implies a b => findLocRef a |>.orElse fun _ => findLocRef b
    | .conj a b => findLocRef a |>.orElse fun _ => findLocRef b
    | .disj a b => findLocRef a |>.orElse fun _ => findLocRef b
    | .neg body => findLocRef body
    | .forallStruct body => findLocRef body
    | .forallPair body => findLocRef body
    | .forallElem _ body => findLocRef body
    | .seq a b => findLocRef a |>.orElse fun _ => findLocRef b
    | .eq lhs rhs => extractLocFromRef lhs |>.orElse fun _ => extractLocFromRef rhs
    | .gt lhs rhs => extractLocFromRef lhs |>.orElse fun _ => extractLocFromRef rhs
    | .le lhs rhs => extractLocFromRef lhs |>.orElse fun _ => extractLocFromRef rhs
    | .lt lhs rhs => extractLocFromRef lhs |>.orElse fun _ => extractLocFromRef rhs
    | _ => none
  extractLocFromRef : FieldRef → Option String
    | .resolvedExtField loc _ => some loc
    | .toNat r => extractLocFromRef r
    | .size r => extractLocFromRef r
    | .pairLeft r => extractLocFromRef r
    | .pairRight r => extractLocFromRef r
    | _ => none

/-- Check if a PropSpec is purely trivial (True, or ∀/¬ wrapping True). -/
private def isPurelyTrivial : PropSpec → Bool
  | .trivial => true
  | .forallStruct body => isPurelyTrivial body
  | .forallNamed _ body => isPurelyTrivial body
  | .forallNamedPair _ body => isPurelyTrivial body
  | .neg body => isPurelyTrivial body
  | _ => false

-- ============================================================
-- Algorithm property derivation from NLP grammar
-- ============================================================

/-- Collect all structure/inductive names under the namespace. -/
private def collectContextTypes (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc name ci =>
    if name.getPrefix == ns then
      match ci with
      | .inductInfo _ => acc.push name
      | _ =>
        if Lean.isStructure env name then acc.push name
        else acc
    else acc

/-- Domain-specific alias resolution for algorithm-context NP heads.
    Maps common RFC prose words to type names that may be in scope.
    Returns (typeName, optional guard: (fieldName, expectedValue)).
    E.g., "response" → ("Header", some ("qr", 1)) since QR=1 means response. -/
private def aliasDomainWordGuarded (head : String) : Option (String × Option (String × Nat)) :=
  match head.toLower with
  | "response" => some ("Header", some ("qr", 1))
  | "query" => some ("Header", some ("qr", 0))
  | "message" => some ("Header", none)
  | "rr" | "record" => some ("Header", none)
  | "server" | "servers" | "delegation" => some ("SlistEntry", none)
  | _ => none

/-- Simple alias without guard info, for backward compatibility. -/
private def aliasDomainWord (head : String) : Option String :=
  (aliasDomainWordGuarded head).map (·.1)

private def resolveNPToField (head : String) (env : Environment) (ns : Name)
    (contextTypes : Array Name) : Option (Name × Option Name) :=
  let lowerHead := head.toLower
  -- ALL-CAPS: search for field matching lowered name
  if head.toList.all Char.isUpper && head.length > 1 then
    contextTypes.findSome? fun typeName =>
      match Lean.getStructureInfo? env typeName with
      | some sinfo =>
        let fields := sinfo.fieldNames
        if fields.any (·.toString.toLower == lowerHead) then
          some (typeName, some (typeName ++ Name.mkSimple lowerHead))
        else none
      | none => none
  else
    -- Try as type name first
    let capitalized := capitalize' lowerHead
    let typeCand := ns ++ Name.mkSimple capitalized
    if (env.find? typeCand).isSome then
      some (typeCand, none)
    else
      -- Try domain alias
      match aliasDomainWord head with
      | some aliasType =>
        let aliasCand := ns ++ Name.mkSimple aliasType
        if (env.find? aliasCand).isSome then some (aliasCand, none) else none
      | none =>
        -- Search all context types for a matching field
        contextTypes.findSome? fun typeName =>
          match Lean.getStructureInfo? env typeName with
          | some sinfo =>
            let fields := sinfo.fieldNames
            if fields.any (·.toString.toLower == lowerHead) then
              some (typeName, some (typeName ++ Name.mkSimple lowerHead))
            else none
          | none => none

/-- Walk one level of struct fields to find a nested field path.
    E.g., Format has `header : Header`, and Header has `id` → Format.header.id -/
private def walkFieldPath (env : Environment) (typeName : Name) (targetField : String)
    : Option (Name × Name) :=
  match Lean.getStructureInfo? env typeName with
  | some sinfo =>
    -- Direct field
    if sinfo.fieldNames.any (·.toString.toLower == targetField.toLower) then
      some (typeName, typeName ++ Name.mkSimple targetField.toLower)
    else
      -- One-level walk: check each field's type for the target
      sinfo.fieldNames.findSome? fun fieldName =>
        let fieldFQN := typeName ++ fieldName
        match env.find? fieldFQN with
        | some ci =>
          let fieldType := ci.type
          -- Extract the return type name (simplified: look for const in the type)
          match fieldType with
          | .const innerTypeName _ =>
            match Lean.getStructureInfo? env innerTypeName with
            | some innerInfo =>
              if innerInfo.fieldNames.any (·.toString.toLower == targetField.toLower) then
                some (innerTypeName, innerTypeName ++ Name.mkSimple targetField.toLower)
              else none
            | none => none
          | .forallE _ _ body _ =>
            match body with
            | .const innerTypeName _ =>
              match Lean.getStructureInfo? env innerTypeName with
              | some innerInfo =>
                if innerInfo.fieldNames.any (·.toString.toLower == targetField.toLower) then
                  some (innerTypeName, innerTypeName ++ Name.mkSimple targetField.toLower)
                else none
              | none => none
            | _ => none
          | _ => none
        | none => none
  | none => none

-- ============================================================
-- NLP extensions for sub-step guard derivation
-- ============================================================

/-- Drop the last n characters from a string. -/
private def dropLast (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take (s.length - n))

/-- Strip English verb inflection: "answers" → "answer", "contains" → "contain", "shows" → "show". -/
private def stripVerbInflection (verb : String) : String :=
  let v := verb.toLower
  if v.endsWith "es" && v.length > 3 then dropLast v 2
  else if v.endsWith "s" && v.length > 2 then dropLast v 1
  else v

/-- Strip English plural: "servers" → "server", "entries" → "entry".
    The "-es" suffix is only stripped after sibilant stems (-ss, -x, -z,
    -ch, -sh), where English requires it ("addresses" → "address",
    "matches" → "match"); elsewhere the plural is plain "-s" on an
    e-final stem ("names" → "name", "values" → "value"). -/
private def stripPlural (w : String) : String :=
  let s := w.toLower
  if s.endsWith "ies" && s.length > 3 then dropLast s 3 ++ "y"
  else if (s.endsWith "sses" || s.endsWith "xes" || s.endsWith "zes" ||
           s.endsWith "ches" || s.endsWith "shes") && s.length > 4 then
    dropLast s 2
  else if s.endsWith "s" && !s.endsWith "ss" && s.length > 2 then dropLast s 1
  else s

/-- e-final verb roots, whose past participle adds bare "-d"
    ("cached" → "cache"). Morphological lexicon for participle stemming. -/
private def eFinalVerbRoots : Array String :=
  #["cache", "retrieve", "store", "locate", "ignore", "include", "require",
    "release", "update", "combine", "remove", "receive", "serve", "use"]

/-- Stem an "-ed" past participle to its verb root: "stored" → "store",
    "returned" → "return", "cached" → "cache", "tried" → "try". -/
private def participleStem (w : String) : String :=
  let v := w.toLower
  if v.endsWith "ied" && v.length > 4 then dropLast v 3 ++ "y"
  else if v.endsWith "ed" && v.length > 3 then
    let bare := dropLast v 2
    if eFinalVerbRoots.contains (bare ++ "e") then bare ++ "e" else bare
  else v

-- ============================================================
-- Entry-structure derivation from algorithm prose
-- ============================================================

/-- A per-entry field derived from algorithm prose. -/
private structure EntryField where
  name : String        -- field name (singular NP head, camelCased)
  typeStr : String     -- resolved Lean type, as source text
  optional : Bool      -- wrapped in Option (modal partiality)
  src : String         -- source sentence for the docstring
  deriving Repr, Inhabited

/-- Is this word an ALL-CAPS structure reference (e.g. "SLIST")? -/
private def isAllCapsRef (w : String) : Bool :=
  w.length >= 2 && w.toList.all Char.isUpper

/-- Derive a per-entry structure for an ALL-CAPS structure referenced in
    algorithm prose (RFC 1034 §5.3.3). Grammar-driven, in sentence order:

    1. **Membership imperative** — a verb-first clause whose plural object
       moves "into" an ALL-CAPS structure ("Copy the names into SLIST") —
       declares the structure's elements: entries identified by the object's
       referent. The object head (singular) becomes the first entry field.
    2. **Possessive-anaphor imperative** — a later imperative whose object
       is determined by "their" ("Set up THEIR addresses …"), the anaphor
       referring to the just-established entries — adds a per-entry field
       from its object head.
    3. **Modal partiality** — "may" + expletive copula + "case" head with a
       that-relClause whose sub-clause negates an adjectival predication
       over a known field's plural ("the addresses are not available") —
       makes that field's knowledge partial: the type wraps in `Option`.
    4. **Keep-track purpose** — "keep track of previous ⟨plural⟩"
       ("… keep track of previous transmissions") — adds a per-entry `Nat`
       counter for those past events, named `⟨singular⟩Count`. Detected at
       token level because purpose-infinitive coordination ("to control …
       and keep track …") is lossy at clause level.

    Returns (target, fields) when a membership imperative anchored the
    derivation, none otherwise. -/
private def deriveEntryStructure (prose : String) (env : Environment) (ns : Name)
    : Option (String × Array EntryField) := Id.run do
  let sentences := Property.splitSentences prose
  let emptyNP : NLP.NounPhrase := ⟨none, #[], "", .unknown, #[]⟩
  let mut target : Option String := none
  let mut fields : Array EntryField := #[]
  for s in sentences do
    let toks := NLP.tagPOS (NLP.tokenize s)
    if toks.isEmpty then continue
    -- Imperative passes (verb-first clause)
    if toks[0]!.pos == .verb then
      if let some (.svo _ _ obj pps) := NLP.parseImperativeClause toks emptyNP then
        match target with
        | none =>
          -- 1: membership imperative
          if obj.number == .plural then
            if let some pp := pps.find? fun pp =>
                pp.prep.toLower == "into" && isAllCapsRef pp.np.head then
              target := some pp.np.head
              let fname := stripPlural obj.head
              let (tstr, _) := resolveNPType obj.head obj.preAdjs obj.number env ns
              fields := fields.push ⟨fname, tstr, false, s⟩
        | some _ =>
          -- 2: possessive-anaphor imperative
          if obj.det == some "their" && obj.number == .plural then
            let fname := stripPlural obj.head
            unless fields.any (·.name == fname) do
              let (tstr, _) := resolveNPType obj.head obj.preAdjs obj.number env ns
              fields := fields.push ⟨fname, tstr, false, s⟩
    if target.isSome then
      -- 3: modal partiality over a known field's plural
      match NLP.parseClause toks with
      | .svo _ vp obj _ =>
        if vp.adv == some "may" && vp.isCopula && obj.head.toLower == "case" then
          for pm in obj.postMods do
            if let .relClause _ relText := pm then
              if let .svAdj subj _ comp _ := NLP.parseSentenceClause relText then
                if comp.adv == some "not" then
                  fields := fields.map fun f =>
                    if f.name == stripPlural subj.head then
                      { f with optional := true, src := f.src ++ "\" / \"" ++ s }
                    else f
      | _ => pure ()
      -- 4: keep-track counter (token-level: purpose coordination is lossy)
      for i in [:toks.size] do
        if i + 3 < toks.size && stripVerbInflection toks[i]!.word == "keep" &&
            toks[i+1]!.word.toLower == "track" && toks[i+2]!.word.toLower == "of" then
          if let some (np, _) := NLP.parseNP toks (i + 3) then
            if np.number == .plural && np.preAdjs.any (·.toLower == "previous") then
              let fname := stripPlural np.head ++ "Count"
              unless fields.any (·.name == fname) do
                fields := fields.push ⟨fname, "Nat", false, s⟩
  match target with
  | some t => if fields.isEmpty then none else some (t, fields)
  | none => none

/-- Generate the per-entry structure derived by `deriveEntryStructure`, with
    docstrings citing the source sentences. Returns (name × srcSentence)
    pairs for RFC-text hover linking. -/
private def generateEntryStructure (prose : String)
    : CommandElabM (Array (Name × String)) := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let some (target, fields) := deriveEntryStructure prose env ns | return #[]
  let structShort := capitalize target.toLower ++ "Entry"
  let structName := Name.mkSimple structShort
  if (env.find? (ns ++ structName)).isSome then return #[]
  let mut fieldNames : Array Ident := #[]
  let mut fieldTypes : Array (TSyntax `term) := #[]
  for f in fields do
    let base : TSyntax `term ←
      match Lean.Parser.runParserCategory env `term f.typeStr "<entry-field>" with
      | .ok stx => pure ⟨stx⟩
      | .error e => throwError "entry-field type parse error: {e}"
    let t ← if f.optional then `(Option $base) else pure base
    fieldNames := fieldNames.push (mkIdent (Name.mkSimple f.name))
    fieldTypes := fieldTypes.push t
  elabCommand (mkStructureCmd (mkIdent structName) fieldNames fieldTypes
    #[``BEq, ``Inhabited])
  let fullName := ns ++ structName
  let fieldLines := String.join (fields.toList.map fun f =>
    s!"- `{f.name}`{if f.optional then " (partial)" else ""}: \"{f.src}\"\n")
  addDocStringCore fullName
    (s!"Per-entry structure of {target}, derived from the algorithm prose: " ++
     s!"a membership imperative fixes the entry identity, a possessive-anaphor " ++
     s!"imperative adds a per-entry field, modal partiality (\"may ... not ...\") " ++
     s!"wraps a field in `Option`, and a keep-track purpose adds a counter.\n\n" ++
     fieldLines)
  for f in fields do
    addDocStringCore (fullName ++ Name.mkSimple f.name) s!"\"{f.src}\""
  let mut srcs : Array (Name × String) := #[]
  if let some f0 := fields[0]? then
    srcs := srcs.push (fullName, f0.src)
  return srcs

/-- Search inductives in contextTypes for a constructor whose lowered name contains the candidate.
    Returns (inductiveName, ctorName). -/
private def resolveNPToEnumCtor (words : Array String) (env : Environment)
    (contextTypes : Array Name) : Option (Name × Name) := Id.run do
  -- Build candidate: strip plurals, camelCase
  let stripped := words.map stripPlural
  let candidate := toCamelCase stripped.toList
  if candidate.isEmpty then return none
  let candidateLower := candidate.toLower
  -- Pass 1: exact camelCase match (highest priority)
  for typeName in contextTypes do
    match env.find? typeName with
    | some (.inductInfo ival) =>
      if (Lean.getStructureInfo? env typeName).isNone then  -- skip structs
        for ctor in ival.ctors do
          let ctorLocal := ctor.components.getLast!.toString.toLower
          if ctorLocal == candidateLower then return some (typeName, ctor)
    | _ => pure ()
  -- Pass 2: compound substring match (multi-word only)
  if words.size > 1 then
    for typeName in contextTypes do
      match env.find? typeName with
      | some (.inductInfo ival) =>
        if (Lean.getStructureInfo? env typeName).isNone then
          for ctor in ival.ctors do
            let ctorLocal := ctor.components.getLast!.toString.toLower
            if hasSub ctorLocal candidateLower then return some (typeName, ctor)
      | _ => pure ()
  return none

/-- Trace field chain from a target type back to a root struct in contextTypes.
    E.g., Rcode → Header.rcode → Format.header → path: [("Format","header"), ("Header","rcode")].
    Returns the chain from root to target. -/
private def traceFieldChain (env : Environment) (targetType : Name)
    (contextTypes : Array Name) : Option (Array (Name × Name)) := Id.run do
  -- Find structs that contain a field of the target type
  for typeName in contextTypes do
    match Lean.getStructureInfo? env typeName with
    | some sinfo =>
      for fieldName in sinfo.fieldNames do
        let fieldFQN := typeName ++ fieldName
        match env.find? fieldFQN with
        | some ci =>
          let fieldType := ci.type
          let innerTypeName? := match fieldType with
            | .const n _ => some n
            | .forallE _ _ (.const n _) _ => some n
            | _ => none
          if let some innerTypeName := innerTypeName? then
            if innerTypeName == targetType then
              -- Found! Now check if typeName itself is reachable from a root struct
              -- Try one more level
              for rootTypeName in contextTypes do
                if rootTypeName == typeName then
                  return some #[(typeName, fieldName)]
                match Lean.getStructureInfo? env rootTypeName with
                | some rootInfo =>
                  for rootFieldName in rootInfo.fieldNames do
                    let rootFieldFQN := rootTypeName ++ rootFieldName
                    match env.find? rootFieldFQN with
                    | some rci =>
                      let rootFieldType := rci.type
                      let rootInner? := match rootFieldType with
                        | .const n _ => some n
                        | .forallE _ _ (.const n _) _ => some n
                        | _ => none
                      if let some rootInner := rootInner? then
                        if rootInner == typeName then
                          return some #[(rootTypeName, rootFieldName), (typeName, fieldName)]
                    | none => pure ()
                | none => pure ()
        | none => pure ()
    | none => pure ()
  return none

/-- Extract noun phrases from clause text for NP-based resolution.
    Returns content words excluding common stop words. -/
private def extractNPWords (text : String) : Array String :=
  let words := text.toLower.splitOn " " |>.filter (!·.isEmpty) |>.toArray
  let stopWords := #["if", "the", "a", "an", "that", "is", "not", "itself",
                      "or", "and", "it", "as", "well", "back", "to", "from", "in"]
  words.filter fun w => !stopWords.contains w && w.length > 1

/-- Derive a guard PropSpec for a single sub-clause of a sub-step description.
    Applies strategies in order: (1) verb stem field match, (2) compound NP enum search,
    (3) delegation/authority hints. Strategy order matters: verbs first catches "answers the
    question" without false-matching enums; compound NP second catches "name error" → nameError. -/
private def deriveSubClauseGuard (text : String) (env : Environment) (ns : Name)
    (contextTypes : Array Name) : Option PropSpec := Id.run do
  let lower := text.toLower
  let npWords := extractNPWords text

  -- Strategy 1: Verb stem → Array field size check
  -- "answers the question" → verb "answers" → stem "answer" → Format.answer.size > 0
  let allWords := lower.splitOn " " |>.filter (!·.isEmpty) |>.toArray
  for w in allWords do
    -- Check for verbs (words ending in 's' that could be inflected)
    if w.endsWith "s" && w.length > 3 then
      let stem := stripVerbInflection w
      -- Search struct fields in contextTypes for a matching Array field
      for typeName in contextTypes do
        match Lean.getStructureInfo? env typeName with
        | some sinfo =>
          for fieldName in sinfo.fieldNames do
            if fieldName.toString.toLower == stem then
              let fieldFQN := typeName ++ fieldName
              match env.find? fieldFQN with
              | some ci =>
                let isArr := match ci.type with
                  | .app (.const ``Array _) _ => true
                  | .forallE _ _ (.app (.const ``Array _) _) _ => true
                  | _ => false
                if isArr then
                  let typeName' := typeName.components.getLast!.toString
                  return some (.gt (.size (.fieldPath typeName' fieldName.toString)) (.lit 0))
              | none => pure ()
        | none => pure ()

  -- Strategy 2: Multi-word NP → camelCase enum constructor search
  -- "name error" → ["name", "error"] → strip plural → camelCase "nameError" → Rcode.nameError
  -- Only use compound matches (2+ content words forming a camelCase candidate)
  let nounWords := npWords.filter fun w =>
    !#["response", "contains", "shows", "answers", "question",
       "better", "other", "bizarre", "contents", "data", "cache",
       "returning", "client", "information", "go", "step",
       "delete", "change", "server"].contains w
  if nounWords.size >= 2 then
    -- Try consecutive pairs and triples of noun words
    for i in [:nounWords.size - 1] do
      let pair := #[nounWords[i]!, nounWords[i + 1]!]
      if let some (indName, ctorName) := resolveNPToEnumCtor pair env contextTypes then
        if let some chain := traceFieldChain env indName contextTypes then
          let fieldPath := chain.map (·.2.toString) |>.toList
          let pathStr := ".".intercalate fieldPath
          let formatName := chain[0]!.1.components.getLast!.toString
          let ctorLocal := ctorName.components.getLast!.toString
          let indLocal := indName.components.getLast!.toString
          return some (.eq (.fieldPath formatName pathStr) (.fieldPath indLocal ctorLocal))

  -- Strategy 3: Single keyword enum constructor (exact camelCase match only)
  -- "servers failure" → strip plural "server" + "failure" → "serverFailure" → exact match
  if nounWords.size >= 1 then
    let stripped := nounWords.map stripPlural
    let candidate := toCamelCase stripped.toList
    if candidate.length >= 6 then  -- avoid false matches on short candidates
      for typeName in contextTypes do
        match env.find? typeName with
        | some (.inductInfo ival) =>
          if (Lean.getStructureInfo? env typeName).isNone then  -- skip structs
            for ctor in ival.ctors do
              let ctorLocal := ctor.components.getLast!.toString.toLower
              if ctorLocal == candidate.toLower then
                if let some chain := traceFieldChain env typeName contextTypes then
                  let fieldPath := chain.map (·.2.toString) |>.toList
                  let pathStr := ".".intercalate fieldPath
                  let formatName := chain[0]!.1.components.getLast!.toString
                  let ctorLocalName := ctor.components.getLast!.toString
                  let indLocal := typeName.components.getLast!.toString
                  return some (.eq (.fieldPath formatName pathStr) (.fieldPath indLocal ctorLocalName))
        | _ => pure ()

  -- Strategy 4: Delegation / authority hints → authority.size > 0
  if npWords.any (fun w => w == "delegation" || hasSub w "delegat") then
    for typeName in contextTypes do
      match Lean.getStructureInfo? env typeName with
      | some sinfo =>
        for fieldName in sinfo.fieldNames do
          if fieldName.toString.toLower == "authority" then
            let typeName' := typeName.components.getLast!.toString
            return some (.gt (.size (.fieldPath typeName' "authority")) (.lit 0))
      | none => pure ()

  -- Strategy 5: CNAME keyword → answer.size > 0 (CNAME records appear in answer section)
  if hasSub lower "cname" then
    for typeName in contextTypes do
      match Lean.getStructureInfo? env typeName with
      | some sinfo =>
        for fieldName in sinfo.fieldNames do
          if fieldName.toString.toLower == "answer" then
            let typeName' := typeName.components.getLast!.toString
            return some (.gt (.size (.fieldPath typeName' "answer")) (.lit 0))
      | none => pure ()

  return none

/-- Derive a guard PropSpec from a sub-step description.
    Handles " or " / " and " coordination by splitting and combining. -/
private def deriveSubStepGuard (subStep : AlgorithmStep) (env : Environment)
    (ns : Name) (contextTypes : Array Name) : Option PropSpec := Id.run do
  let desc := subStep.description
  -- Extract the guard text (after "if" and before the main verb clause)
  let lower := desc.toLower
  let guardText := if hasSub lower "if " then
    let afterIf := (lower.splitOn "if ").getD 1 ""
    -- Cut at first comma to isolate the conditional clause
    let parts := afterIf.splitOn ","
    parts[0]!
  else lower

  -- Check for " or " coordination
  if hasSub guardText " or " then
    let clauses := guardText.splitOn " or "
    let mut resolved : Array PropSpec := #[]
    for clause in clauses do
      let trimmed := trimStr clause
      if let some prop := deriveSubClauseGuard trimmed env ns contextTypes then
        resolved := resolved.push prop
    if resolved.isEmpty then return none
    if resolved.size == 1 then return some resolved[0]!
    -- Combine with disj
    let mut result := resolved[0]!
    for i in [1:resolved.size] do
      result := .disj result resolved[i]!
    return some result

  -- Check for " and " coordination (within guard)
  if hasSub guardText " and " then
    let clauses := guardText.splitOn " and "
    let mut resolved : Array PropSpec := #[]
    for clause in clauses do
      let trimmed := trimStr clause
      if let some prop := deriveSubClauseGuard trimmed env ns contextTypes then
        resolved := resolved.push prop
    if resolved.isEmpty then return none
    if resolved.size == 1 then return some resolved[0]!
    let mut result := resolved[0]!
    for i in [1:resolved.size] do
      result := .conj result resolved[i]!
    return some result

  -- No coordination — single clause
  deriveSubClauseGuard guardText env ns contextTypes

/-- Render a PropSpec guard body to a string suitable for `def guard_X (resp : Format) : Prop := ...`.
    Uses `resp` as the binder name and resolves field paths through the struct hierarchy.
    `complementOf` (from an "or other ⟨X⟩" disjunct) appends the complement of
    the named sibling guards: contents not covered by any of them. -/
private def buildGuardDefString (guardName : String) (formatTypeName : String)
    (spec : PropSpec) (ns : Name) (env : Environment)
    (complementOf : Array String := #[]) : String :=
  let body := renderGuardBody spec
  let body := if complementOf.isEmpty then body
    else "(" ++ body ++ ") ∨ ("
      ++ " ∧ ".intercalate (complementOf.toList.map (s!"¬ {·} resp")) ++ ")"
  s!"def {guardName} (resp : {formatTypeName}) : Prop := {body}"
where
  renderGuardBody (spec : PropSpec) : String :=
    match spec with
    | .eq lhs rhs => s!"{renderGuardRef lhs} = {renderGuardRef rhs}"
    | .gt lhs rhs => s!"{renderGuardRef lhs} > {renderGuardRef rhs}"
    | .lt lhs rhs => s!"{renderGuardRef lhs} < {renderGuardRef rhs}"
    | .disj a b => s!"({renderGuardBody a}) ∨ ({renderGuardBody b})"
    | .conj a b => s!"({renderGuardBody a}) ∧ ({renderGuardBody b})"
    | .neg body => s!"¬ ({renderGuardBody body})"
    | .implies a b => s!"({renderGuardBody a}) → ({renderGuardBody b})"
    | .trivial => "True"
    | _ => "True"
  renderGuardRef (ref : FieldRef) : String :=
    match ref with
    | .fieldPath structName fieldName =>
      let typeName := ns ++ Name.mkSimple (capitalize' structName)
      -- Check if this is an enum constructor reference (not a struct field access)
      -- Structures are also inductives, so check getStructureInfo? to distinguish
      let isEnum := match env.find? typeName with
        | some (.inductInfo _) => (Lean.getStructureInfo? env typeName).isNone
        | _ => false
      if isEnum then
        -- This is an enum type: render as Type.ctor (e.g., Rcode.serverFailure)
        s!"{capitalize' structName}.{fieldName}"
      else
        if hasSub fieldName "." then
          -- Multi-level path: use explicit function application
          -- e.g., "header.rcode" → "(Format.header resp).rcode"
          let parts := fieldName.splitOn "."
          if parts.length == 2 then
            let p1 := parts[0]!
            let p2 := parts[1]!
            s!"({capitalize' structName}.{p1} resp).{p2}"
          else if parts.length == 3 then
            let p1 := parts[0]!
            let p2 := parts[1]!
            let p3 := parts[2]!
            s!"(({capitalize' structName}.{p1} resp).{p2}).{p3}"
          else s!"(resp.{fieldName})"
        else
          -- Simple single-level field
          s!"({capitalize' structName}.{fieldName} resp)"
    | .size inner => s!"({renderGuardRef inner}).size"
    | .toNat inner => s!"({renderGuardRef inner}).toNat"
    | .lit n => toString n
    | _ => "True"

-- ============================================================
-- Refined guards and obligations (modality + content fidelity)
--
-- The base guards above are PERMISSIONS: StepSpec says which transitions are
-- allowed, and soundness proofs cannot detect an implementation that never
-- takes an allowed transition. Refined guards recover the prose content that
-- the base derivation weakens (RR-type mentions, "answers the question"),
-- expressed over abstract predicate parameters since RR sections are opaque
-- ByteArrays at the Spec level. Obligations then state the missing direction:
-- when exactly one refined guard holds, the corresponding transition MUST be
-- taken.
-- ============================================================

/-- A refined guard conjunct over abstract content predicates. -/
private inductive RefinedConjunct where
  /-- `hasRRType resp.<sectionField> <code> = true` — the section contains an
      RR of the enum constructor's stored code. Used for enums (e.g. RRType)
      not traceable to a Format field. -/
  | hasRRType (sectionField : String) (code : Nat)
  /-- `answersQuery resp = true/false` — abstract "the response answers the
      question" predicate. -/
  | answersQuery (positive : Bool)
  /-- Field-path equation against a traceable enum constructor
      (e.g. `(Format.header resp).rcode = Rcode.nameError`). -/
  | enumFieldEq (chain : Array (String × String)) (enumType ctor : String)
  /-- `handled resp = false` — the complement class from an "or other
      ⟨adj⟩ ⟨noun⟩" disjunct ("or other bizarre contents"): contents the
      implementation does not otherwise handle. `handled` is abstract since
      "other" is relative to the full set of behaviors in scope (which may
      come from other RFCs, e.g. RFC 2308 NODATA). -/
  | otherUnhandled
  deriving Repr, Inhabited

/-- Find an enum constructor whose stored RFC description's head noun matches
    the given (plural-stripped) word. E.g. "servers" → "server" matches the
    head of NS's description "an authoritative name server". -/
private def resolveByDescriptionHead (word : String) (env : Environment)
    (contextTypes : Array Name) : Option (Name × Name) := Id.run do
  let target := (stripPlural word).toLower
  if target.length < 4 then return none
  let descs := rfcEnumDescriptions.getState env
  for typeName in contextTypes do
    match env.find? typeName with
    | some (.inductInfo ival) =>
      if (Lean.getStructureInfo? env typeName).isNone then
        for ctor in ival.ctors do
          if let some (_, desc) := descs[ctor]? then
            -- Head noun: last word of the description, parentheticals stripped
            let cleaned := (desc.splitOn "(").headD desc
            let dwords := cleaned.toLower.splitOn " " |>.filter (!·.isEmpty)
            if let some headWord := dwords.getLast? then
              if (stripPlural headWord) == target then
                return some (typeName, ctor)
    | _ => pure ()
  return none

/-- Derive a refined conjunct from a single guard sub-clause. -/
private def deriveRefinedConjunct (text : String) (env : Environment)
    (contextTypes : Array Name) : Option RefinedConjunct := Id.run do
  let lower := text.toLower
  let words := lower.splitOn " " |>.filter (!·.isEmpty) |>.toArray
  -- (1) Negated copula over "answer": "that is not the answer itself"
  if words.contains "not" && (words.contains "answer" || words.contains "answers") then
    return some (.answersQuery false)
  -- (2) "answers the question" → positive answersQuery
  if words.contains "answers" && words.contains "question" then
    return some (.answersQuery true)
  -- (3) Enum constructor resolution. Traceable enums (a Format field path
  -- exists, e.g. Rcode) give field equations; untraceable ones (e.g. RRType —
  -- sections are opaque bytes) give hasRRType conjuncts with the stored code.
  let sectionField := if hasSub lower "delegat" then "authority" else "answer"
  let npWords := extractNPWords text
  let nounWords := npWords.filter fun w =>
    !#["response", "contains", "shows", "answers", "question",
       "better", "other", "bizarre", "contents", "data", "cache",
       "returning", "client", "information", "go", "step",
       "delete", "change"].contains w
  let mkConjunct (indName ctor : Name) : Option RefinedConjunct := Id.run do
    match traceFieldChain env indName contextTypes with
    | some chain =>
      -- Only accept chains rooted at Format: the guard binder is a Format.
      -- (Other roots arise from generated algorithm types, e.g.
      -- Transition.action : ResponseAction, and must not be used.)
      if chain[0]!.1.components.getLast!.toString != "Format" then return none
      let chainStr := chain.map fun (t, f) =>
        (t.components.getLast!.toString, f.toString)
      return some (.enumFieldEq chainStr (indName.components.getLast!.toString)
        (ctor.components.getLast!.toString))
    | none =>
      match (rfcEnumDescriptions.getState env)[ctor]? with
      | some (code, _) => return some (.hasRRType sectionField code)
      | none => return none
  -- (3a) Name-based: pairs then singles (mirrors deriveSubClauseGuard)
  if nounWords.size >= 2 then
    for i in [:nounWords.size - 1] do
      let pair := #[nounWords[i]!, nounWords[i + 1]!]
      if let some (indName, ctor) := resolveNPToEnumCtor pair env contextTypes then
        if let some c := mkConjunct indName ctor then return some c
  for w in nounWords do
    if let some (indName, ctor) := resolveNPToEnumCtor #[w] env contextTypes then
      if let some c := mkConjunct indName ctor then return some c
  -- (3b) Description-head fallback: "servers" → NS ("an authoritative name server")
  for w in nounWords do
    if let some (indName, ctor) := resolveByDescriptionHead w env contextTypes then
      if let some c := mkConjunct indName ctor then return some c
  return none

/-- Is this " or "-coordinated disjunct a complement class? An NP headed by
    the exclusion marker "other" that resolves to no enum/field ("other
    bizarre contents") denotes everything NOT covered by the sibling
    guards / the implementation's other handling. -/
private def isOtherComplementClause (clause : String) (env : Environment)
    (contextTypes : Array Name) : Bool := Id.run do
  let t := trimStr clause
  let tokens := NLP.tagPOS (NLP.tokenize t)
  let some tok := tokens[0]? | return false
  return tok.word.toLower == "other"
    && (deriveRefinedConjunct t env contextTypes).isNone

/-- Derive a refined guard in DNF (outer disjunction of conjunction rows) from
    a sub-step description. `or`-coordination keeps resolved disjuncts
    (narrowing a guard hypothesis is sound for obligations); an "other ⟨X⟩"
    disjunct becomes the abstract complement conjunct `otherUnhandled`;
    `and`-coordination requires all conjuncts to resolve (dropping one would
    widen the region). -/
private def deriveRefinedGuard (subStep : AlgorithmStep) (env : Environment)
    (contextTypes : Array Name) : Option (Array (Array RefinedConjunct)) := Id.run do
  let desc := subStep.description
  let lower := desc.toLower
  let guardText := if hasSub lower "if " then
    let afterIf := (lower.splitOn "if ").getD 1 ""
    (afterIf.splitOn ",")[0]!
  else lower
  if hasSub guardText " or " then
    let clauses := guardText.splitOn " or "
    let mut rows : Array (Array RefinedConjunct) := #[]
    for clause in clauses do
      if let some c := deriveRefinedConjunct (trimStr clause) env contextTypes then
        rows := rows.push #[c]
      else if isOtherComplementClause clause env contextTypes then
        rows := rows.push #[.otherUnhandled]
    if rows.isEmpty then return none
    return some rows
  if hasSub guardText " and " then
    let clauses := guardText.splitOn " and "
    let mut conjs : Array RefinedConjunct := #[]
    for clause in clauses do
      match deriveRefinedConjunct (trimStr clause) env contextTypes with
      | some c => conjs := conjs.push c
      | none => return none  -- all-or-nothing for conjunctions
    if conjs.isEmpty then return none
    return some #[conjs]
  match deriveRefinedConjunct guardText env contextTypes with
  | some c => return some #[#[c]]
  | none => return none

/-- Render a refined conjunct as a term, given the binder idents. -/
private def renderRefinedConjunct (aqId hrId handledId respId : Ident)
    (c : RefinedConjunct) : CommandElabM (TSyntax `term) := do
  match c with
  | .answersQuery pos =>
    if pos then `($aqId $respId = true) else `($aqId $respId = false)
  | .hasRRType sectionField code =>
    let sectProj := mkIdent (Name.mkSimple "Format" ++ Name.mkSimple sectionField)
    let codeLit : TSyntax `term := ⟨Syntax.mkNumLit (toString code)⟩
    `($hrId ($sectProj $respId) ($codeLit : BitVec 16) = true)
  | .enumFieldEq chain enumType ctor =>
    let mut acc : TSyntax `term := respId
    for (structName, fieldName) in chain do
      let projId := mkIdent (Name.mkSimple structName ++ Name.mkSimple fieldName)
      acc ← `($projId $acc)
    let ctorId := mkIdent (Name.mkSimple enumType ++ Name.mkSimple ctor)
    `($acc = $ctorId)
  | .otherUnhandled =>
    `($handledId $respId = false)

/-- Render a refined guard (DNF) as a term. -/
private def renderRefinedGuard (aqId hrId handledId respId : Ident)
    (dnf : Array (Array RefinedConjunct)) : CommandElabM (TSyntax `term) := do
  let mut rows : Array (TSyntax `term) := #[]
  for row in dnf do
    let mut acc? : Option (TSyntax `term) := none
    for c in row do
      let t ← renderRefinedConjunct aqId hrId handledId respId c
      acc? := some (← match acc? with
        | none => pure t
        | some a => `($a ∧ $t))
    if let some a := acc? then rows := rows.push a
  let mut result? : Option (TSyntax `term) := none
  for r in rows do
    result? := some (← match result? with
      | none => pure r
      | some a => `($a ∨ $r))
  match result? with
  | some r => pure r
  | none => `(True)

/-- Render a prep phrase as a camelCase name fragment: prep + pre-adjectives +
    head ("in local information" → "InLocalInformation"). -/
private def renderPPName (pp : NLP.PrepPhrase) : String :=
  capitalize pp.prep
    ++ String.join (pp.np.preAdjs.map capitalize).toList
    ++ capitalize pp.np.head

/-- Derive a predicate name from a parsed clause.
    Condition clauses (`isAction := false`) name the state of affairs:
    subject head + PPs ("the answer is in local information" →
    `answerInLocalInformation`). Action clauses name the act: verb +
    object head (an anaphor already resolved to its antecedent) + PPs
    ("return it to the client" → `returnAnswerToClient`). -/
private def predNameOfClause (c : NLP.Clause) (isAction : Bool) : Option String :=
  let sanitize (s : String) : Option String :=
    let cleaned := String.ofList (s.toList.filter (fun ch => ch.isAlphanum))
    if cleaned.isEmpty || !(cleaned.get 0).isAlpha then none else some cleaned
  match c with
  | .svo subj vp obj pps =>
    let ppPart := String.join (pps.map renderPPName).toList
    if isAction then
      sanitize (vp.verb ++ capitalize obj.head ++ ppPart)
    else
      sanitize (subj.head ++ ppPart)
  | .svAdj subj _ comp pps =>
    sanitize (subj.head ++ capitalize comp.adj ++ String.join (pps.map renderPPName).toList)
  | .svPassive subj participle pps _ =>
    sanitize (subj.head ++ capitalize participle ++ String.join (pps.map renderPPName).toList)
  | _ => none

/-- Generate guard defs, StepSpec, StepSpecStar, and isTerminal from algorithm steps.
    Called after generateAlgorithmTypes when context types are in scope.
    Returns (name × source sub-step text) pairs for generated refined guards
    and obligations, for prose hover support. -/
private def generateStepRelation (sectionName : String)
    (topSteps : Array AlgorithmStep) (subSteps : Array AlgorithmStep)
    : CommandElabM (Array (Name × String)) := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let contextTypes := collectContextTypes env ns
  let stepTypeName := sectionName ++ "Step"

  -- 1. Generate guard definitions from NLP-derived sub-step analysis
  let mut guardNames : Array (String × String × Option Nat) := #[]
  for s in subSteps do
    let actionName := deriveConstructorName s.description true
    let guardDefName := s!"guard_{actionName}"
    let guardSpec? := deriveSubStepGuard s env ns contextTypes
    match guardSpec? with
    | some guardSpec =>
      let formatName := ns ++ Name.mkSimple "Format"
      if (env.find? formatName).isSome then
        -- "X or other ⟨adj⟩ ⟨noun⟩": the "other" disjunct is the complement
        -- of the sibling sub-step guards (generated before this one, in
        -- sub-step order), e.g. "a servers failure or other bizarre
        -- contents" → ∨ (¬guard_answerOrError ∧ ¬guard_delegation ∧ ...).
        let lowerDesc := s.description.toLower
        let guardText := if hasSub lowerDesc "if " then
          (((lowerDesc.splitOn "if ").getD 1 "").splitOn ",")[0]!
          else lowerDesc
        let complementOf : Array String :=
          if hasSub guardText " or " &&
              ((guardText.splitOn " or ").drop 1).any
                (fun cl => isOtherComplementClause cl env contextTypes) then
            guardNames.map (fun (_, gn, _) => gn)
          else #[]
        let guardStr := buildGuardDefString guardDefName "Format" guardSpec ns env
          complementOf
        elabCommandStr guardStr
        let fullGuardName := ns ++ Name.mkSimple guardDefName
        addDocStringCore fullGuardName s!"Guard for sub-step {actionName}: derived from NLP analysis of \"{s.description}\""
        guardNames := guardNames.push (actionName, guardDefName, s.gotoTarget)
    | none => pure ()

  -- 2. Generate StepSpec inductive (step relation with guards)
  if !guardNames.isEmpty then
    let mut stepSpecCtors := ""
    -- Sequential transitions: adjacent top-level steps
    for i in [:topSteps.size - 1] do
      let fromCtor := deriveConstructorName topSteps[i]!.description false
      let toCtor := deriveConstructorName topSteps[i + 1]!.description false
      stepSpecCtors := stepSpecCtors ++ s!"\n  | seq_{fromCtor}_{toCtor} : StepSpec .{fromCtor} .{toCtor}"
    -- Conditional transitions: sub-steps with goto targets and guards
    let sourceCtorName := if topSteps.size >= 4
      then deriveConstructorName topSteps[topSteps.size - 1]!.description false
      else "unknown"
    for (actionName, guardDefName, gotoTarget?) in guardNames do
      if let some target := gotoTarget? then
        let targetCtorName := if target > 0 && target ≤ topSteps.size
          then deriveConstructorName topSteps[target - 1]!.description false
          else "unknown"
        stepSpecCtors := stepSpecCtors ++ s!"\n  | {actionName} (resp : Format) : {guardDefName} resp → StepSpec .{sourceCtorName} .{targetCtorName}"
    let stepSpecStr := s!"inductive StepSpec : {stepTypeName} → {stepTypeName} → Prop where{stepSpecCtors}"
    elabCommandStr stepSpecStr

    -- 3. Generate StepSpecStar transitive closure
    let starStr := s!"inductive StepSpecStar : {stepTypeName} → {stepTypeName} → Prop where
  | refl (s : {stepTypeName}) : StepSpecStar s s
  | trans (s₁ s₂ s₃ : {stepTypeName}) : StepSpec s₁ s₂ → StepSpecStar s₂ s₃ → StepSpecStar s₁ s₃"
    elabCommandStr starStr

    -- 4. Generate isTerminal for sub-steps without gotoTarget (terminal actions)
    let terminalGuards := subSteps.filter (·.gotoTarget.isNone)
    if !terminalGuards.isEmpty then
      let mut termDisjuncts : Array String := #[]
      for s in terminalGuards do
        let actionName := deriveConstructorName s.description true
        let guardDefName := s!"guard_{actionName}"
        let fullGuardName := ns ++ Name.mkSimple guardDefName
        let env' ← getEnv
        if (env'.find? fullGuardName).isSome then
          termDisjuncts := termDisjuncts.push s!"{guardDefName} resp"
      if !termDisjuncts.isEmpty then
        let termBody := " ∧ ".intercalate
          [s!"step = .{sourceCtorName}",
           if termDisjuncts.size == 1 then termDisjuncts[0]!
           else "(" ++ " ∨ ".intercalate termDisjuncts.toList ++ ")"]
        let termStr := s!"def isTerminal (step : {stepTypeName}) (resp : Format) : Prop := {termBody}"
        elabCommandStr termStr

    -- 5. Generate responseHandled: disjunction of ALL sub-step guards
    let allGuardExprs := guardNames.map (fun (_, gn, _) => s!"{gn} resp")
    if !allGuardExprs.isEmpty then
      let disjBody :=
        if allGuardExprs.size == 1 then allGuardExprs[0]!
        else "(" ++ " ∨ ".intercalate allGuardExprs.toList ++ ")"
      let rhStr := s!"def responseHandled (resp : Format) : Prop := {disjBody}"
      elabCommandStr rhStr

  -- 6. Refined guards + obligations. Base guards are permissions (soundness
  -- cannot detect a never-taken transition) and weaken content (e.g. "shows a
  -- CNAME" → answer.size > 0). Refined guards recover the content over
  -- abstract predicates; obligations state that in a single-guard region the
  -- corresponding transition MUST be taken.
  let mut propSrcs : Array (Name × String) := #[]
  let formatName := ns ++ Name.mkSimple "Format"
  if (env.find? formatName).isSome then
    let mut refined : Array (String × Array (Array RefinedConjunct) × Option Nat × String) := #[]
    for s in subSteps do
      let actionName := deriveConstructorName s.description true
      match deriveRefinedGuard s env contextTypes with
      | some dnf => refined := refined.push (actionName, dnf, s.gotoTarget, s.description)
      | none =>
        logInfo s!"generateStepRelation: no refined guard derivable for sub-step \"{s.description}\" — obligation skipped"
    let aqId := mkIdent (Name.mkSimple "answersQuery")
    let hrId := mkIdent (Name.mkSimple "hasRRType")
    let handledId := mkIdent (Name.mkSimple "handled")
    let trId := mkIdent (Name.mkSimple "transition")
    let respId := mkIdent (Name.mkSimple "resp")
    let fmtId := mkIdent (Name.mkSimple "Format")
    let stepTyId := mkIdent (Name.mkSimple stepTypeName)
    -- 6a. Refined guard defs
    for (actionName, dnf, _, desc) in refined do
      let gname := mkIdent (Name.mkSimple s!"guardRefined_{actionName}")
      let body ← renderRefinedGuard aqId hrId handledId respId dnf
      elabCommand (← `(def $gname ($aqId : $fmtId → Bool)
        ($hrId : Array ByteArray → BitVec 16 → Bool)
        ($handledId : $fmtId → Bool) ($respId : $fmtId) : Prop := $body))
      let fullName := ns ++ Name.mkSimple s!"guardRefined_{actionName}"
      addDocStringCore fullName
        s!"Refined guard for sub-step {actionName}, over abstract content predicates: \"{desc}\""
      propSrcs := propSrcs.push (fullName, desc)
    -- 6b. Obligation defs (one per sub-step with a refined guard)
    for (actionName, _, gotoTarget?, desc) in refined do
      let obName := mkIdent (Name.mkSimple s!"obligation_{actionName}")
      let targetTerm : TSyntax `term ← match gotoTarget? with
        | some target =>
          let targetCtorName := if target > 0 && target ≤ topSteps.size
            then deriveConstructorName topSteps[target - 1]!.description false
            else "unknown"
          let ctorId := mkIdent (Name.mkSimple stepTypeName ++ Name.mkSimple targetCtorName)
          `(some $ctorId)
        | none => `(none)
      let mut body : TSyntax `term ← `($trId $respId $targetTerm)
      for (otherName, _, _, _) in refined.reverse do
        if otherName != actionName then
          let og := mkIdent (Name.mkSimple s!"guardRefined_{otherName}")
          body ← `(¬ $og $aqId $hrId $handledId $respId → $body)
      let own := mkIdent (Name.mkSimple s!"guardRefined_{actionName}")
      body ← `($own $aqId $hrId $handledId $respId → $body)
      elabCommand (← `(def $obName ($aqId : $fmtId → Bool)
        ($hrId : Array ByteArray → BitVec 16 → Bool)
        ($handledId : $fmtId → Bool)
        ($trId : $fmtId → Option $stepTyId → Prop) : Prop :=
        ∀ ($respId : $fmtId), $body))
      let fullName := ns ++ Name.mkSimple s!"obligation_{actionName}"
      addDocStringCore fullName
        (s!"Obligation for sub-step {actionName} (the direction StepSpec cannot express: " ++
         s!"when only this refined guard holds, the transition MUST be taken): \"{desc}\"")
      propSrcs := propSrcs.push (fullName, desc)
  -- 6c. Top-level conditional obligations: imperative steps with an anaphoric
  -- conditional ("See if <condition>, and if so <action>"). StepSpec records
  -- only the sequential PERMISSION for these steps (e.g. checkAnswer →
  -- findServers), so an implementation that never takes the conditional
  -- action still satisfies soundness. The obligation states the MUST
  -- direction over an abstract state type: whenever the condition holds, the
  -- action is taken. Predicate names are derived from the parsed clauses
  -- (condition: subject head + PPs; action: verb + resolved anaphor + PPs).
  for s in topSteps do
    match NLP.parseIfSoStep s.description with
    | none => pure ()
    | some (cond, act) =>
      let stepCtor := deriveConstructorName s.description false
      match predNameOfClause cond false, predNameOfClause act true with
      | some condName, some actName =>
        let obName := s!"obligation_{stepCtor}"
        let obId := mkIdent (Name.mkSimple obName)
        let sigmaId := mkIdent (Name.mkSimple "σ")
        let condId := mkIdent (Name.mkSimple condName)
        let actId := mkIdent (Name.mkSimple actName)
        let sId := mkIdent (Name.mkSimple "s")
        elabCommand (← `(def $obId ($sigmaId : Type)
            ($condId $actId : $sigmaId → Prop) : Prop :=
          ∀ ($sId : $sigmaId), $condId $sId → $actId $sId))
        let fullName := ns ++ Name.mkSimple obName
        addDocStringCore fullName
          (s!"Obligation for top-level step {stepCtor} (the conditional direction " ++
           s!"StepSpec cannot express: when {condName} holds, {actName} MUST hold): " ++
           s!"\"{s.description}\"")
        propSrcs := propSrcs.push (fullName, s.description)
      | _, _ =>
        logInfo s!"generateStepRelation: no predicate names derivable for top-level conditional \"{s.description}\" — obligation skipped"
  return propSrcs

/-- Build a guard PropSpec from subject/object domain-word guards.
    pairLeft = subject (first binder), pairRight = object (second binder).
    E.g., subject="response" (qr=1), object="query" (qr=0) produces:
    a.qr.toNat = 1 ∧ b.qr.toNat = 0 -/
private def buildDomainGuard (_typeName : String)
    (subjGuard objGuard : Option (String × Nat)) : Option PropSpec :=
  match subjGuard, objGuard with
  | some (sf, sv), some (of, ov) =>
    some (.conj
      (.eq (.toNat (.pairLeft (.fieldPath "Header" sf))) (.lit sv))
      (.eq (.toNat (.pairRight (.fieldPath "Header" of))) (.lit ov)))
  | some (sf, sv), none =>
    some (.eq (.toNat (.pairLeft (.fieldPath "Header" sf))) (.lit sv))
  | none, some (of, ov) =>
    some (.eq (.toNat (.pairRight (.fieldPath "Header" of))) (.lit ov))
  | none, none => none

/-- Derive a PropSpec from a ConditionalClause using grammatical pattern matching.
    Returns none for unresolvable clauses. -/
private def deriveAlgorithmProperty (cc : NLP.ConditionalClause) (env : Environment)
    (ns : Name) (contextTypes : Array Name) : Option PropSpec :=
  match cc with
  | .conditional guard body =>
    -- Pattern 3: Conditional → implies
    let guardProp := deriveFromClause guard env ns contextTypes
    let bodyProp := deriveFromClause body env ns contextTypes
    match guardProp, bodyProp with
    | some gp, some bp =>
      -- Both sides resolved: conditional property
      let typeName := extractTypeName gp |>.orElse fun _ => extractTypeName bp
      match typeName with
      | some tn => some (.forallNamed tn (.implies gp bp))
      | none => some (.implies gp bp)
    | some gp, none =>
      -- Only guard resolved: the guard IS the interesting constraint
      -- e.g., "if TTL > 0, cache the data" → TTL > 0 is the property
      some gp
    | none, some bp =>
      -- Only body resolved: e.g., "if X fails, initializes SLIST from SBELT"
      some bp
    | none, none => none
  | .simple clause => deriveFromClause clause env ns contextTypes
where
  /-- Extract type name from a PropSpec that references a named type. -/
  extractTypeName : PropSpec → Option String
    | .forallNamed tn _ => some tn
    | .forallNamedPair tn _ => some tn
    | .eq (.fieldPath sn _) _ => some sn
    | .eq _ (.fieldPath sn _) => some sn
    | .gt (.fieldPath sn _) _ => some sn
    | .gt (.toNat (.fieldPath sn _)) _ => some sn
    | .lt (.fieldPath sn _) _ => some sn
    | _ => none
  /-- Derive from a single clause. -/
  deriveFromClause (clause : NLP.Clause) (env : Environment) (ns : Name)
      (contextTypes : Array Name) : Option PropSpec :=
    match clause with
    | .svo subj vp obj pps =>
      if vp.isCopula then
        -- Copula SVO: "X is greater/closer..." — treat obj as adjective complement
        let adjWord := obj.head.toLower
        let isComparative := adjWord.endsWith "er" || adjWord == "greater" || adjWord == "less"
        if isComparative then
          -- Check for "than" PP to find comparison target type
          let thanPP := pps.find? fun pp => pp.prep.toLower == "than"
          -- Try subject as type
          let subjRef := resolveNPToField subj.head env ns contextTypes
          -- Try to find the type from "than" PP if subject doesn't resolve
          let typeRef := subjRef.orElse fun _ =>
            thanPP.bind fun pp => resolveNPToField pp.np.head env ns contextTypes
          match typeRef with
          | some (resolvedType, _) =>
            match Lean.getStructureInfo? env resolvedType with
            | some sinfo =>
              let metricField := sinfo.fieldNames.find? fun fn =>
                let s := fn.toString.toLower
                s.endsWith "count" || s.endsWith "measure" || s.endsWith "score"
              match metricField with
              | some mf =>
                let typeName := resolvedType.components.getLast!.toString
                let cmp := if adjWord == "less" then PropSpec.lt else PropSpec.gt
                some (.forallNamedPair typeName
                  (cmp (.fieldPath typeName mf.toString)
                       (.fieldPath typeName mf.toString)))
              | none => none
            | none => none
          | none =>
            -- Pattern 4: "TTL is greater than zero" (numeric comparison)
            let subjRef' := resolveNPToField subj.head env ns contextTypes
            match subjRef' with
            | some (subjType, some subjField) =>
              let typeName := subjType.components.getLast!.toString
              let cmp := if adjWord == "less" then PropSpec.lt else PropSpec.gt
              some (.forallNamed typeName
                (cmp (.toNat (.fieldPath typeName subjField.toString)) (.lit 0)))
            | _ => none
        else none
      else
        -- Active transitive verb
        let subjRef := resolveNPToField subj.head env ns contextTypes
        let objRef := resolveNPToField obj.head env ns contextTypes
        -- Extract domain-word guards for subject and object
        let subjGuard := (aliasDomainWordGuarded subj.head).bind (·.2)
        let objGuard := (aliasDomainWordGuarded obj.head).bind (·.2)
        -- Check for "using NP" PP
        let usingPP := pps.find? fun pp => pp.prep.toLower == "using"
        -- Check for "from NP" PP
        let fromPP := pps.find? fun pp => pp.prep.toLower == "from"
        -- Helper: wrap a forallNamedPair body with domain guards if available
        let wrapWithGuard := fun (typeName : String) (body : PropSpec) =>
          match buildDomainGuard typeName subjGuard objGuard with
          | some guard => PropSpec.implies guard body
          | none => body
        match subjRef, objRef with
        | some (subjType, _), some (objType, _) =>
          if subjType == objType then
            let typeName := subjType.components.getLast!.toString
            -- Same type: ∀ (a b : T), [guard →] compare via "using" field or "id"
            match usingPP with
            | some pp =>
              let fieldHead := pp.np.head.toLower
              match walkFieldPath env subjType fieldHead with
              | some (innerType, fieldFQN) =>
                let innerName := innerType.components.getLast!.toString
                let fieldLocal := fieldFQN.components.getLast!.toString
                let body := PropSpec.eq (.fieldPath innerName fieldLocal)
                                        (.fieldPath innerName fieldLocal)
                some (.forallNamedPair typeName (wrapWithGuard typeName body))
              | none => none
            | none =>
              -- No "using" PP: check for match verbs → ID-based equality
              let verb := vp.verb.toLower
              let isMatchVerb := verb == "matches" || verb == "match" || verb == "equals"
              if isMatchVerb then
                match walkFieldPath env subjType "id" with
                | some (innerType, fieldFQN) =>
                  let innerName := innerType.components.getLast!.toString
                  let fieldLocal := fieldFQN.components.getLast!.toString
                  let body := PropSpec.eq (.fieldPath innerName fieldLocal)
                                          (.fieldPath innerName fieldLocal)
                  some (.forallNamedPair typeName (wrapWithGuard typeName body))
                | none =>
                  match Lean.getStructureInfo? env subjType with
                  | some sinfo =>
                    let idField := sinfo.fieldNames.find? fun fn =>
                      fn.toString.toLower == "id"
                    match idField with
                    | some mf =>
                      let body := PropSpec.eq (.fieldPath typeName mf.toString)
                                              (.fieldPath typeName mf.toString)
                      some (.forallNamedPair typeName (wrapWithGuard typeName body))
                    | none => none
                  | none => none
              else none
          else none
        | _, _ =>
          -- Try: SVO with "from" PP (initialization/assignment)
          -- "resolver initializes SLIST from SBELT" → obj=SLIST, fromPP.np=SBELT
          match objRef, fromPP with
          | some (objType, some objField), some pp =>
            let srcRef := resolveNPToField pp.np.head env ns contextTypes
            match srcRef with
            | some (_, some srcField) =>
              let typeName := objType.components.getLast!.toString
              some (.forallNamed typeName
                (.eq (.fieldPath typeName objField.components.getLast!.toString)
                     (.fieldPath typeName srcField.components.getLast!.toString)))
            | _ => none
          | _, _ =>
            -- Fallback: verb implies equality and subject resolves to type
            let verb := vp.verb.toLower
            let isMatchVerb := verb == "matches" || verb == "match" || verb == "equals"
            match subjRef, isMatchVerb with
            | some (subjType, none), true =>
              let typeName := subjType.components.getLast!.toString
              match walkFieldPath env subjType "id" with
              | some (innerType, fieldFQN) =>
                let innerName := innerType.components.getLast!.toString
                let fieldLocal := fieldFQN.components.getLast!.toString
                let body := PropSpec.eq (.fieldPath innerName fieldLocal)
                                        (.fieldPath innerName fieldLocal)
                some (.forallNamedPair typeName (wrapWithGuard typeName body))
              | none =>
                match Lean.getStructureInfo? env subjType with
                | some sinfo =>
                  let idField := sinfo.fieldNames.find? fun fn =>
                    fn.toString.toLower == "id"
                  match idField with
                  | some mf =>
                    let body := PropSpec.eq (.fieldPath typeName mf.toString)
                                            (.fieldPath typeName mf.toString)
                    some (.forallNamedPair typeName (wrapWithGuard typeName body))
                  | none => none
                | none => none
            | _, _ => none
    | .svAdj subj _vp comp adjPPs =>
      let adjWord := comp.adj.toLower
      let isComparative := adjWord.endsWith "er" || adjWord == "greater" || adjWord == "less"
      if isComparative then
        -- Check for "than NP" PP to get comparison value
        let thanPP := adjPPs.find? fun pp => pp.prep.toLower == "than"
        let subjRef := resolveNPToField subj.head env ns contextTypes
        match subjRef with
        | some (subjType, some subjField) =>
          -- Pattern 4: "X is greater/less than <numeric>" (e.g., "TTL is greater than zero")
          match thanPP with
          | some pp =>
            let numWord := pp.np.head.toLower
            let numVal := if numWord == "zero" then some 0 else numWord.toNat?
            match numVal with
            | some n =>
              let typeName := subjType.components.getLast!.toString
              let fieldName := subjField.components.getLast!.toString
              let cmp := if adjWord == "less" then PropSpec.lt else PropSpec.gt
              some (.forallNamed typeName
                (cmp (.toNat (.fieldPath typeName fieldName)) (.lit n)))
            | none => none
          | none => none
        | some (subjType, none) =>
          -- Subject is a type (not a field): compare metric fields
          match Lean.getStructureInfo? env subjType with
          | some sinfo =>
            let metricField := sinfo.fieldNames.find? fun fn =>
              let s := fn.toString.toLower
              s.endsWith "count" || s.endsWith "measure" || s.endsWith "score"
            match metricField with
            | some mf =>
              let typeName := subjType.components.getLast!.toString
              let cmp := if adjWord == "less" then PropSpec.lt else PropSpec.gt
              some (.forallNamedPair typeName
                (cmp (.fieldPath typeName mf.toString)
                     (.fieldPath typeName mf.toString)))
            | none => none
          | none => none
        | none => none
      else none
    | .svPassive subj _participle _pps negated =>
      if negated then
        let subjRef := resolveNPToField subj.head env ns contextTypes
        match subjRef with
        | some (subjType, _) =>
          let typeName := subjType.components.getLast!.toString
          some (.forallNamed typeName (.neg .trivial))
        | none => none
      else none
    | _ => none

/-- Interpret a FieldRef for algorithm-level rules.
    `binders` is the "active" binder set (may be narrowed by pairLeft/pairRight or eq splitting).
    `allBinders` is the full binder set from the enclosing forallNamedPair. -/
private def interpretFieldRefForAlgorithm (ref : FieldRef) (env : Environment) (ns : Name)
    (binders : Array (TSyntax `ident)) (allBinders : Array (TSyntax `ident) := #[])
    : CommandElabM (TSyntax `term) := do
  match ref with
  | .pairLeft inner =>
    -- Select the first binder of the pair (a in ∀ a b : T)
    let abs := if allBinders.isEmpty then binders else allBinders
    let selected := if abs.size >= 2 then #[abs[abs.size - 2]!] else binders
    interpretFieldRefForAlgorithm inner env ns selected allBinders
  | .pairRight inner =>
    -- Select the second binder of the pair (b in ∀ a b : T)
    let abs := if allBinders.isEmpty then binders else allBinders
    let selected := if abs.size >= 2 then #[abs[abs.size - 1]!] else binders
    interpretFieldRefForAlgorithm inner env ns selected allBinders
  | .fieldPath structName fieldName =>
    -- Try to resolve the field path through the environment
    let typeName := ns ++ Name.mkSimple (capitalize' structName)
    -- Check if fieldName is a full qualified name or just a field
    let parts := fieldName.splitOn "."
    if parts.length > 1 then
      -- Already qualified — try to use it directly
      let fieldIdent := mkIdent (Name.mkStr1 fieldName)
      let binderIdent := binders[binders.size - 1]!
      `($fieldIdent $binderIdent)
    else
      -- Simple field name — look it up
      let fieldFQN := typeName ++ Name.mkSimple fieldName.toLower
      if (env.find? fieldFQN).isSome then
        let fieldIdent := mkIdent fieldFQN
        let binderIdent := binders[binders.size - 1]!
        `($fieldIdent $binderIdent)
      else
        -- Walk one level
        match walkFieldPath env typeName fieldName with
        | some (_, resolvedFQN) =>
          let fieldIdent := mkIdent resolvedFQN
          let binderIdent := binders[binders.size - 1]!
          `($fieldIdent $binderIdent)
        | none => `(True)
  | .toNat inner =>
    let innerTerm ← interpretFieldRefForAlgorithm inner env ns binders allBinders
    `(BitVec.toNat $innerTerm)
  | .size inner =>
    let innerTerm ← interpretFieldRefForAlgorithm inner env ns binders allBinders
    `(Array.size $innerTerm)
  | .lit n =>
    let nLit := Syntax.mkNumLit (toString n)
    `($nLit)
  | _ => `(True)

/-- Count the number of type parameters in a ConstantInfo type
    (number of leading forall-E binders before the final Sort). -/
private def countTypeParams : Expr → Nat
  | .forallE _ _ body _ => 1 + countTypeParams body
  | _ => 0

/-- Render a FieldRef body to a string for polymorphic prop construction.
    Uses `x` as the binder name for the struct instance. -/
private def renderFieldRefStr (ref : FieldRef) (binderName : String) : String :=
  match ref with
  | .fieldPath _structName fieldName => s!"{binderName}.{fieldName}"
  | .toNat inner => s!"BitVec.toNat ({renderFieldRefStr inner binderName})"
  | .size inner => s!"Array.size ({renderFieldRefStr inner binderName})"
  | .lit n => toString n
  | .pairLeft inner => renderFieldRefStr inner "a"
  | .pairRight inner => renderFieldRefStr inner "b"
  | _ => "True"

/-- Render a PropSpec body to a string for polymorphic prop construction. -/
private def renderPropSpecStr (spec : PropSpec) (binderName : String) : Option String :=
  match spec with
  | .eq lhs rhs =>
    some s!"{renderFieldRefStr lhs binderName} = {renderFieldRefStr rhs binderName}"
  | .gt lhs rhs =>
    some s!"{renderFieldRefStr lhs binderName} > {renderFieldRefStr rhs binderName}"
  | .lt lhs rhs =>
    some s!"{renderFieldRefStr lhs binderName} < {renderFieldRefStr rhs binderName}"
  | .implies ante body =>
    match renderPropSpecStr ante binderName, renderPropSpecStr body binderName with
    | some a, some b => some s!"{a} → {b}"
    | _, _ => none
  | .conj a b =>
    match renderPropSpecStr a binderName, renderPropSpecStr b binderName with
    | some as_, some bs => some s!"{as_} ∧ {bs}"
    | _, _ => none
  | .neg body =>
    match renderPropSpecStr body binderName with
    | some b => some s!"¬ ({b})"
    | none => none
  | .disj a b =>
    match renderPropSpecStr a binderName, renderPropSpecStr b binderName with
    | some as_, some bs => some s!"{as_} ∨ {bs}"
    | _, _ => none
  | .trivial => some "True"
  | _ => none

/-- Render the forall preamble for a polymorphic type.
    E.g., for `Resources : (S C NS RR : Type) → [SlistSpec S NS] → [CacheSpec C RR] → Type`
    produces `∀ (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] (x : Resources S C NS RR), `
    Walks the Expr, collecting binder names. Instance constraints are rendered
    by substituting de Bruijn vars with the collected parameter names. -/
private def renderPolymorphicPreamble (typeExpr : Expr) (typeFullName : String)
    (binderName : String) : CommandElabM String := do
  -- First pass: collect all parameter names and their binder info
  let mut paramNames : Array String := #[]
  let mut paramKinds : Array (Bool × String) := #[]  -- (isInst, rendered)
  let mut expr := typeExpr
  while true do
    match expr with
    | .forallE name _domain body bi =>
      let paramName := if name.toString.startsWith "_" then
        s!"p{paramNames.size}"
      else name.toString
      paramNames := paramNames.push paramName
      paramKinds := paramKinds.push (bi == .instImplicit, paramName)
      expr := body
    | _ => break
  -- Second pass: render instance constraints with resolved names
  -- De Bruijn index 0 = innermost (last param), so index i from the end = paramNames[paramNames.size - 1 - i]
  let mut typeParams : Array String := #[]
  let mut instParams : Array String := #[]
  expr := typeExpr
  let mut paramIdx : Nat := 0
  while true do
    match expr with
    | .forallE _name domain body bi =>
      match bi with
      | .instImplicit =>
        -- Render instance constraint by resolving bvar references
        let instStr := renderExprWithNames domain paramNames paramIdx
        instParams := instParams.push s!"[{instStr}]"
      | _ =>
        -- Type parameter: check if it's Type
        match domain with
        | .sort _ => typeParams := typeParams.push paramNames[paramIdx]!
        | _ => typeParams := typeParams.push s!"({paramNames[paramIdx]!} : ...)"
      paramIdx := paramIdx + 1
      expr := body
    | _ => break
  -- Build the preamble string
  let mut parts : Array String := #[]
  if !typeParams.isEmpty then
    let simpleTypeParams := typeParams.filter fun p => !p.startsWith "("
    let complexTypeParams := typeParams.filter fun p => p.startsWith "("
    if !simpleTypeParams.isEmpty then
      parts := parts.push s!"({" ".intercalate simpleTypeParams.toList} : Type)"
    for p in complexTypeParams do
      parts := parts.push p
  for inst in instParams do
    parts := parts.push inst
  -- The binder for the struct instance
  let typeApp := s!"{typeFullName} {" ".intercalate typeParams.toList}"
  parts := parts.push s!"({binderName} : {typeApp})"
  return s!"∀ {" ".intercalate parts.toList}, "
where
  /-- Render an Expr to a string, substituting bvar indices with collected parameter names.
      `paramNames` is the full array of params in order; `depth` is the current binder depth
      (how many forallE binders we've entered so far). -/
  renderExprWithNames (e : Expr) (paramNames : Array String) (depth : Nat) : String :=
    match e with
    | .app fn arg =>
      let fnStr := renderExprWithNames fn paramNames depth
      let argStr := renderExprWithNames arg paramNames depth
      -- Check if arg needs parens (is it an application?)
      match arg with
      | .app _ _ => s!"{fnStr} ({argStr})"
      | _ => s!"{fnStr} {argStr}"
    | .const name _ => name.toString
    | .bvar idx =>
      -- De Bruijn: index 0 = the most recent binder, which at depth `depth`
      -- is paramNames[depth - 1]. But we're inside the `depth`-th forallE,
      -- so bvar 0 = paramNames[depth - 1], bvar 1 = paramNames[depth - 2], etc.
      -- Actually: at depth d (0-indexed), we've entered d forallE's.
      -- The binders in scope are paramNames[0..d-1].
      -- bvar 0 = paramNames[d-1], bvar 1 = paramNames[d-2], etc.
      -- But we haven't entered the current forallE yet (we're looking at its domain),
      -- so the binders in scope are paramNames[0..depth-1].
      -- bvar 0 = paramNames[depth - 1], bvar idx = paramNames[depth - 1 - idx]
      if depth > idx then
        paramNames[depth - 1 - idx]!
      else s!"#{idx}"
    | .sort _ => "Type"
    | _ => "_"

/-- Interpret a PropSpec for algorithm-level properties.
    Returns an array of Lean term syntax for each generated prop. -/
private partial def interpretPropSpecForAlgorithm (spec : PropSpec) (env : Environment)
    (ns : Name) (binders : Array (TSyntax `ident))
    : CommandElabM (Array (TSyntax `term)) := do
  match spec with
  | .forallNamed typeName body =>
    let typeFullName := ns ++ Name.mkSimple (capitalize' typeName)
    match env.find? typeFullName with
    | some ci =>
      let numParams := countTypeParams ci.type
      if numParams == 0 then
        let xIdent : TSyntax `ident := mkIdent `x
        let typeIdent := mkIdent typeFullName
        let binders' := binders.push xIdent
        let bodyTerms ← interpretPropSpecForAlgorithm body env ns binders'
        bodyTerms.mapM fun bodyTerm => do
          `(∀ ($xIdent : $typeIdent), $bodyTerm)
      else
        -- Polymorphic type: use string-based elaboration
        match renderPropSpecStr body "x" with
        | some bodyStr =>
          let preamble ← renderPolymorphicPreamble ci.type typeFullName.toString "x"
          let propStr := s!"{preamble}{bodyStr}"
          match Lean.Parser.runParserCategory (← getEnv) `term propStr "<algo-poly>" with
          | .ok stx =>
            let stx : TSyntax `term := ⟨stx⟩
            return #[stx]
          | .error _ => return #[]
        | none => return #[]
    | none => return #[]
  | .forallNamedPair typeName body =>
    let typeFullName := ns ++ Name.mkSimple (capitalize' typeName)
    match env.find? typeFullName with
    | some ci =>
      let numParams := countTypeParams ci.type
      if numParams == 0 then
        let aIdent : TSyntax `ident := mkIdent `a
        let bIdent : TSyntax `ident := mkIdent `b
        let typeIdent := mkIdent typeFullName
        let binders' := binders.push aIdent |>.push bIdent
        let bodyTerms ← interpretPropSpecForAlgorithm body env ns binders'
        bodyTerms.mapM fun bodyTerm => do
          `(∀ ($aIdent $bIdent : $typeIdent), $bodyTerm)
      else
        -- Polymorphic type: use string-based elaboration
        match renderPropSpecStr body "x" with
        | some bodyStr =>
          let preamble ← renderPolymorphicPreamble ci.type typeFullName.toString "x"
          let propStr := s!"{preamble}{bodyStr}"
          match Lean.Parser.runParserCategory (← getEnv) `term propStr "<algo-poly>" with
          | .ok stx =>
            let stx : TSyntax `term := ⟨stx⟩
            return #[stx]
          | .error _ => return #[]
        | none => return #[]
    | none => return #[]
  | .eq lhs rhs =>
    -- When we have pair binders (forallNamedPair), use left binder for lhs, right for rhs
    -- pairLeft/pairRight in the FieldRef override this positional split
    let lhsBinders := if binders.size >= 2 then #[binders[binders.size - 2]!] else binders
    let rhsBinders := if binders.size >= 2 then #[binders[binders.size - 1]!] else binders
    let lhsTerm ← interpretFieldRefForAlgorithm lhs env ns lhsBinders binders
    let rhsTerm ← interpretFieldRefForAlgorithm rhs env ns rhsBinders binders
    let t ← `($lhsTerm = $rhsTerm)
    return #[t]
  | .gt lhs rhs =>
    let lhsBinders := if binders.size >= 2 then #[binders[binders.size - 2]!] else binders
    let rhsBinders := if binders.size >= 2 then #[binders[binders.size - 1]!] else binders
    let lhsTerm ← interpretFieldRefForAlgorithm lhs env ns lhsBinders binders
    let rhsTerm ← interpretFieldRefForAlgorithm rhs env ns rhsBinders binders
    let t ← `($lhsTerm > $rhsTerm)
    return #[t]
  | .lt lhs rhs =>
    let lhsBinders := if binders.size >= 2 then #[binders[binders.size - 2]!] else binders
    let rhsBinders := if binders.size >= 2 then #[binders[binders.size - 1]!] else binders
    let lhsTerm ← interpretFieldRefForAlgorithm lhs env ns lhsBinders binders
    let rhsTerm ← interpretFieldRefForAlgorithm rhs env ns rhsBinders binders
    let t ← `($lhsTerm < $rhsTerm)
    return #[t]
  | .conj a b =>
    let aTerms ← interpretPropSpecForAlgorithm a env ns binders
    let bTerms ← interpretPropSpecForAlgorithm b env ns binders
    let mut terms : Array (TSyntax `term) := #[]
    for aTerm in aTerms do
      for bTerm in bTerms do
        terms := terms.push (← `($aTerm ∧ $bTerm))
    return terms
  | .implies ante body =>
    let anteTerms ← interpretPropSpecForAlgorithm ante env ns binders
    let bodyTerms ← interpretPropSpecForAlgorithm body env ns binders
    let mut terms : Array (TSyntax `term) := #[]
    for anteTerm in anteTerms do
      for bodyTerm in bodyTerms do
        terms := terms.push (← `($anteTerm → $bodyTerm))
    return terms
  | .neg body =>
    let bodyTerms ← interpretPropSpecForAlgorithm body env ns binders
    bodyTerms.mapM fun bodyTerm => do
      `(¬ $bodyTerm)
  | .disj a b =>
    let aTerms ← interpretPropSpecForAlgorithm a env ns binders
    let bTerms ← interpretPropSpecForAlgorithm b env ns binders
    let mut terms : Array (TSyntax `term) := #[]
    for aTerm in aTerms do
      for bTerm in bTerms do
        terms := terms.push (← `($aTerm ∨ $bTerm))
    return terms
  | .trivial =>
    return #[← `(True)]
  | _ => return #[]

/-- Walk a PropSpec and collect .declField entries into struct fields. -/
private def collectDeclFields (spec : PropSpec)
    (bindings : Std.HashMap String (Nat ⊕ String))
    : Array (String × Nat) :=
  match spec with
  | .declField name bitWidthRef =>
    let bw := match bitWidthRef with
      | .extractedNat bindingName =>
        match bindings.get? bindingName with
        | some (.inl n) => n
        | _ => 16
      | .lit n => n
      | _ => 16
    #[(name, bw)]
  | .seq a b =>
    collectDeclFields a bindings ++ collectDeclFields b bindings
  | .neg body => collectDeclFields body bindings
  | .disj a b =>
    collectDeclFields a bindings ++ collectDeclFields b bindings
  | .forallStruct body => collectDeclFields body bindings
  | .forallPair body => collectDeclFields body bindings
  | .implies a b =>
    collectDeclFields a bindings ++ collectDeclFields b bindings
  | _ => #[]

/-- Extract the bound ref (typically .extractedNat) from a size bound spec. -/
private def extractBoundRef (spec : PropSpec) (bindings : Std.HashMap String (Nat ⊕ String))
    : FieldRef :=
  match spec with
  | .forallStruct (.le _ rhs) => resolveRef rhs bindings
  | _ => .lit 0
where resolveRef (ref : FieldRef) (bindings : Std.HashMap String (Nat ⊕ String)) : FieldRef :=
  match ref with
  | .extractedNat name =>
    match bindings.get? name with
    | some (.inl n) => .lit n
    | _ => ref
  | _ => ref

/-- Check if a PostMod matches a ParticiplePattern -/
private def matchesPattern (pm : NLP.PostMod) (pat : ParticiplePattern) : Bool :=
  match pm with
  | .participle verb obj pps =>
    let v := verb.toLower
    pat.verbs.contains v &&
    (match pat.objHead with
     | none => true
     | some heads => match obj with
       | some o => heads.contains o.head.toLower
       | none => false) &&
    pat.requiredPPs.all fun (prep, heads) =>
      pps.any fun pp =>
        pp.prep.toLower == prep && heads.contains pp.np.head.toLower
  | _ => false

-- ============================================================
-- PropSpec interpreter
-- ============================================================

/-- Context for PropSpec interpretation (cross-struct rules) -/
structure InterpContext where
  structName : String
  structIdent : TSyntax `ident
  field : MergedField
  subStructName : Name
  sfName : Name
  pps : Array NLP.PPData
  allFields : Array MergedField
  ns : Name

/-- Interpret a FieldRef into a syntax term within the cross-struct context.
    `binders` tracks de Bruijn-indexed bound variables (innermost = index 0). -/
private def interpretFieldRef (ref : FieldRef) (ctx : InterpContext)
    (binders : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  match ref with
  | .currentField =>
    let projIdent := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple ctx.field.name.toLower)
    let msgIdent := binders[binders.size - 1]!  -- outermost binder = struct var
    `($projIdent $msgIdent)
  | .matchedSubField =>
    let countProj := mkIdent (ctx.subStructName ++ ctx.sfName)
    let parentProj := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple ctx.field.name.toLower)
    let msgIdent := binders[binders.size - 1]!
    `($countProj ($parentProj $msgIdent))
  | .namedField name =>
    let projIdent := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple name.toLower)
    let msgIdent := binders[binders.size - 1]!
    `($projIdent $msgIdent)
  | .resolvedFromPP prep =>
    -- Find the PP with given preposition, resolve its NP to a field
    let mut resolved : Option String := none
    for pp in ctx.pps do
      if pp.prep.toLower == prep then
        let sectionWords := pp.np.preAdjs ++ #[pp.np.head]
        let sect := " ".intercalate (sectionWords.map (·.toLower)).toList
        resolved := resolveSectionToField sect ctx.allFields
        break
    match resolved with
    | some targetField =>
      let projIdent := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple targetField.toLower)
      let msgIdent := binders[binders.size - 1]!
      `($projIdent $msgIdent)
    | none =>
      -- Fallback: return True term as placeholder
      `(True)
  | .toNat inner =>
    let innerTerm ← interpretFieldRef inner ctx binders
    `(BitVec.toNat $innerTerm)
  | .size inner =>
    let innerTerm ← interpretFieldRef inner ctx binders
    -- Use ByteArray.size for bound variables (from forallElem), Array.size for fields
    match inner with
    | .bound _ => `(ByteArray.size $innerTerm)
    | _ => `(Array.size $innerTerm)
  | .lit n =>
    let nLit := Syntax.mkNumLit (toString n)
    `($nLit)
  | .bound idx =>
    -- De Bruijn: index 0 = innermost (last pushed binder)
    if idx < binders.size then
      let binderIdent := binders[binders.size - 1 - idx]!
      `($binderIdent)
    else
      `(True)
  | .pairLeft inner => interpretFieldRef inner ctx binders
  | .pairRight inner => interpretFieldRef inner ctx binders
  | .extractedNat _ => `(True)  -- only used by prose-clause rules
  | .resolvedExtField _ _ => `(True)  -- only used by prose-clause rules
  | .fieldPath _ _ => `(True)  -- only used by algorithm rules

/-- Interpret a PropSpec into a Lean syntax term (cross-struct context). -/
private partial def interpretPropSpec (spec : PropSpec) (ctx : InterpContext)
    (binders : Array (TSyntax `ident)) : CommandElabM (TSyntax `term) := do
  match spec with
  | .forallStruct body =>
    let msgIdent : TSyntax `ident := mkIdent `msg
    let binders' := binders.push msgIdent
    let bodyTerm ← interpretPropSpec body ctx binders'
    `(∀ ($msgIdent : $(ctx.structIdent)), $bodyTerm)
  | .forallPair body =>
    let aIdent : TSyntax `ident := mkIdent `a
    let bIdent : TSyntax `ident := mkIdent `b
    let binders' := binders.push aIdent |>.push bIdent
    let bodyTerm ← interpretPropSpec body ctx binders'
    `(∀ ($aIdent $bIdent : $(ctx.structIdent)), $bodyTerm)
  | .forallMatchedIndex body =>
    if ctx.field.isArray then
      let iIdent : TSyntax `ident := mkIdent `i
      let parentProj := mkIdent (Name.mkSimple ctx.structName ++ Name.mkSimple ctx.field.name.toLower)
      let msgIdent := binders[binders.size - 1]!
      let binders' := binders.push iIdent
      let bodyTerm ← interpretPropSpec body ctx binders'
      `(∀ ($iIdent : Fin (Array.size ($parentProj $msgIdent))), $bodyTerm)
    else
      interpretPropSpec body ctx binders
  | .existsTyped typeName body =>
    let xIdent : TSyntax `ident := mkIdent `labels
    let binders' := binders.push xIdent
    let bodyTerm ← interpretPropSpec body ctx binders'
    -- Build ∃ with typed binder using fun syntax
    let typeStx ← match typeName with
      | "Array ByteArray" => `(Array ByteArray)
      | "ByteArray" => `(ByteArray)
      | other => `($(mkIdent (Name.mkSimple other)))
    `(Exists (fun ($xIdent : $typeStx) => $bodyTerm))
  | .forallElem container body =>
    let lIdent : TSyntax `ident := mkIdent `l
    let binders' := binders.push lIdent
    let containerTerm ← interpretFieldRef container ctx binders
    let bodyTerm ← interpretPropSpec body ctx binders'
    `(∀ ($lIdent : ByteArray), $lIdent ∈ $containerTerm → $bodyTerm)
  | .eq lhs rhs =>
    let lhsTerm ← interpretFieldRef lhs ctx binders
    let rhsTerm ← interpretFieldRef rhs ctx binders
    `($lhsTerm = $rhsTerm)
  | .lt lhs rhs =>
    let lhsTerm ← interpretFieldRef lhs ctx binders
    let rhsTerm ← interpretFieldRef rhs ctx binders
    `($lhsTerm < $rhsTerm)
  | .le lhs rhs =>
    let lhsTerm ← interpretFieldRef lhs ctx binders
    let rhsTerm ← interpretFieldRef rhs ctx binders
    `($lhsTerm ≤ $rhsTerm)
  | .gt lhs rhs =>
    let lhsTerm ← interpretFieldRef lhs ctx binders
    let rhsTerm ← interpretFieldRef rhs ctx binders
    `($lhsTerm > $rhsTerm)
  | .implies ante body =>
    let anteTerm ← interpretPropSpec ante ctx binders
    let bodyTerm ← interpretPropSpec body ctx binders
    `($anteTerm → $bodyTerm)
  | .conj a b =>
    let aTerm ← interpretPropSpec a ctx binders
    let bTerm ← interpretPropSpec b ctx binders
    `($aTerm ∧ $bTerm)
  | .trivial => `(True)
  | .neg body =>
    let bodyTerm ← interpretPropSpec body ctx binders
    `(¬ $bodyTerm)
  | .disj a b =>
    let aTerm ← interpretPropSpec a ctx binders
    let bTerm ← interpretPropSpec b ctx binders
    `($aTerm ∨ $bTerm)
  | .declField _ _ => `(True)  -- only used by prose-clause rules
  | .seq _ _ => `(True)  -- only used by prose-clause rules
  | .forallNamed _ body => interpretPropSpec body ctx binders  -- only used by algorithm rules
  | .forallNamedPair _ body => interpretPropSpec body ctx binders  -- only used by algorithm rules

/-- Generate cross-struct property definitions by matching registered rules
    against NLP-parsed clause structure from sub-struct field docstrings.

    Rules are registered declaratively via `cross_struct_rule` and stored in a
    persistent environment extension, making them extensible across modules. -/
private def generateCrossStructProps (structName : String) (fields : Array MergedField)
    : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let rules := crossStructRuleExt.getState env
  let structIdent := mkIdent (Name.mkSimple structName)

  for f in fields do
    let some subStructName := f.resolvedType | continue
    let subFieldNames := getStructFieldNames env subStructName
    for sfName in subFieldNames do
      let sfFQN := subStructName ++ sfName
      let some doc ← Lean.findDocString? env sfFQN | continue
      let clauses := NLP.parseDescriptionClauses doc
      for clause in clauses do
        match clause with
        | .npOnly np =>
          for pm in np.postMods do
            match pm with
            | .participle _ _ pps =>
              for rule in rules do
                if matchesPattern pm rule.pattern then
                  let ctx : InterpContext := {
                    structName, structIdent, field := f,
                    subStructName, sfName, pps, allFields := fields, ns
                  }
                  let propTerm ← interpretPropSpec rule.prop ctx #[]
                  -- Generate the prop name based on the rule
                  let propName ← match rule.prop with
                    | .forallStruct (.eq (.toNat .matchedSubField) (.size (.resolvedFromPP prep))) =>
                      -- Count rule: find target field name
                      let mut target := ""
                      for pp in pps do
                        if pp.prep.toLower == prep then
                          let sectionWords := pp.np.preAdjs ++ #[pp.np.head]
                          let sect := " ".intercalate (sectionWords.map (·.toLower)).toList
                          match resolveSectionToField sect fields with
                          | some tf => target := tf.toLower
                          | none => pure ()
                      pure (mkIdent (Name.mkSimple
                        s!"{structName.toLower}_{sfName.toString.toLower}_counts_{target}"))
                    | _ =>
                      -- Domain name / other: field_subfield_valid
                      pure (mkIdent (Name.mkSimple
                        s!"{structName.toLower}_{f.name.toLower}_{sfName.toString.toLower}_valid"))
                  elabCommand (← `(def $propName : Prop := $propTerm))
                  let fullName := ns ++ propName.getId
                  let fmt ← liftCoreM (ppTerm propTerm)
                  let propText := fmt.pretty
                  -- Generate docstring based on rule
                  match rule.prop with
                  | .forallStruct (.eq (.toNat .matchedSubField) (.size (.resolvedFromPP prep))) =>
                    let mut target := ""
                    for pp in pps do
                      if pp.prep.toLower == prep then
                        let sectionWords := pp.np.preAdjs ++ #[pp.np.head]
                        let sect := " ".intercalate (sectionWords.map (·.toLower)).toList
                        match resolveSectionToField sect fields with
                        | some tf => target := tf
                        | none => pure ()
                    addDocStringCore fullName
                      s!"{sfName} counts entries in {target} section\n```lean\n{propText}\n```"
                  | _ =>
                    addDocStringCore fullName
                      s!"{f.name}.{sfName} is a valid domain name\n```lean\n{propText}\n```"
            | _ => pure ()
        | _ => pure ()

/-- Store field descriptions in the environment for de-elaboration -/
private def storeFieldDescriptions (structName : String) (fields : Array MergedField)
    : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let sName := ns ++ Name.mkSimple structName
  for f in fields do
    let fName := sName ++ Name.mkSimple (f.name.toLower)
    modifyEnv fun env =>
      rfcFieldDescriptions.modifyState env (·.insert fName f.description)

/-- Store enum descriptions for de-elaboration -/
private def storeEnumDescriptions (typeName : Name) (values : Array EnumValue)
    : CommandElabM Unit := do
  for v in values do
    let cName := typeName ++ Name.mkSimple v.name
    modifyEnv fun env =>
      rfcEnumDescriptions.addEntry env (cName, v.code, v.description)

/-- Render an NP (with pp post-modifiers) as a camelCase name fragment:
    "the requested kind of query" → "RequestedKindOfQuery". -/
private def renderNPName (np : NLP.NounPhrase) : String := Id.run do
  let mut out := String.join (np.preAdjs.map capitalize).toList ++ capitalize np.head
  for pm in np.postMods do
    if let .pp prep npd := pm then
      out := out ++ capitalize prep
        ++ String.join (npd.preAdjs.map capitalize).toList ++ capitalize npd.head
  return out

/-- Derive a negated-capability condition from an enum value description:
    "⟨Label⟩ - The name server was unable to ⟨verb⟩ ⟨np⟩",
    "... does not ⟨verb⟩ ⟨np⟩", or "... refuses to ⟨verb⟩ ⟨np⟩" (a refusal
    is the willingness-capability failing). The value's use condition is
    the capability's failure. Returns (capability name, condition text). -/
private def deriveNegatedCapability (desc : String) : Option (String × String) := Id.run do
  -- strip the "⟨Label⟩ - " prefix
  let body := match desc.splitOn " - " with
    | _ :: rest@(_ :: _) => " - ".intercalate rest
    | _ => desc
  let tokens := NLP.tagPOS (NLP.tokenize body.toLower)
  for i in [:tokens.size] do
    if i + 2 < tokens.size && tokens[i + 2]!.pos == .verb then
      let w := tokens[i]!.word
      let next := tokens[i + 1]!.word
      let isUnableTo := w == "unable" && next == "to"
      let isDoesNot := (w == "does" || w == "do") && next == "not"
      let isRefusesTo := tokens[i]!.pos == .verb
        && (w == "refuses" || w == "refuse") && next == "to"
      if isUnableTo || isDoesNot || isRefusesTo then
        let verb := tokens[i + 2]!.word
        let capName := match NLP.parseNP tokens (i + 3) with
          | some (np, _) => verb ++ renderNPName np
          | none => verb
        return some (capName, trimStr body)
  return none

/-- Generate use-condition semantics for enum values whose description is a
    negated-capability clause (e.g. RFC 1035 §4.1.1 RCODE 1 "The name server
    was unable to interpret the query", RCODE 4 "The name server does not
    support the requested kind of query"): when the capability fails, the
    server responds with that value. -/
private def generateNegatedCapabilitySemantics (typeName : Name)
    (values : Array EnumValue) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let enumShort := typeName.components.getLast!.toString
  for v in values do
    if let some (capName, condText) := deriveNegatedCapability v.description then
      let defShort := s!"{enumShort.toLower}_{v.name}_semantics"
      let dName := mkIdent (Name.mkSimple defShort)
      let sigmaId := mkIdent (Name.mkSimple "σ")
      let capId := mkIdent (Name.mkSimple capName)
      let respId := mkIdent (Name.mkSimple s!"responds{capitalize v.name}")
      let sId := mkIdent (Name.mkSimple "s")
      elabCommand (← `(def $dName ($sigmaId : Type)
          ($capId : $sigmaId → Bool) ($respId : $sigmaId → Prop) : Prop :=
        ∀ ($sId : $sigmaId), $capId $sId = false → $respId $sId))
      addDocStringCore (ns ++ Name.mkSimple defShort)
        (s!"Use condition for {enumShort}.{v.name}: when the capability " ++
         s!"`{capName}` fails, the server responds with this code. " ++
         s!"Derived from \"{condText}\"")

/-- Store the diagram text for structure de-elaboration -/
private def storeDiagramText (structName : String) (diagramText : String)
    : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let sName := ns ++ Name.mkSimple structName
  modifyEnv fun env =>
    rfcDiagramText.modifyState env (·.insert sName diagramText)

/-- Extract the bit diagram portion from RFC text -/
private def extractDiagramText (text : String) : String := Id.run do
  let lines := text.splitOn "\n"
  let mut diagramLines : Array String := #[]
  let mut inDiagram := false
  for line in lines do
    if hasSub line "+--+" then
      inDiagram := true
      diagramLines := diagramLines.push line
    else if inDiagram then
      if line.any (· == '|') || line.any (· == '/') then
        diagramLines := diagramLines.push line
      else if (trimStr line).isEmpty then
        continue
      else
        let trimmed := trimStr line
        if !trimmed.isEmpty && trimmed.toList[0]!.isDigit then
          diagramLines := diagramLines.push line
        else
          break
  return "\n".intercalate diagramLines.toList

-- ============================================================
-- Info tree entries for hover support
-- ============================================================

/-- Push hover info for all ident nodes from the parser.
    Field name idents get hover linking to their struct field.
    Other idents (section title, diagram) get hover linking to the struct.
    Uses the parser ident positions directly — no text re-scanning. -/
def pushHoverInfoFromIdents (structName : String) (identNodes : Array Syntax)
    : CommandElabM Unit := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let fullStructName := ns ++ Name.mkSimple structName
  if !(env.find? fullStructName).isSome then return

  for ident in identNodes do
    -- Extract raw text from the ident (not getId.toString which escapes dots)
    let .ident _ rawVal _ _ := ident | continue
    let some _ := ident.getPos? | continue
    let rawText := rawVal.toString
    -- Check if this ident matches a struct field (field names are uppercase in RFC)
    let fieldFQN := fullStructName ++ Name.mkSimple rawText.toLower
    -- For field names, point to the projection function (gives hover with field type).
    -- For title/diagram, point to the structure type itself.
    let hoverExpr :=
      if (env.find? fieldFQN).isSome then Expr.const fieldFQN []
      else Expr.const fullStructName []
    -- Use the exact parser ident as the TermInfo stx so that SubVerso's
    -- infoForSyntax matches by position (getPos?/getTailPos?).
    -- The generated struct uses synthetic syntax with no source positions,
    -- so without this, SubVerso would classify all RFC text idents as unknown.
    pushInfoLeaf (.ofTermInfo {
      elaborator := `VeriDNS.RFC.includeRfc
      stx := ident
      expr := hoverExpr
      lctx := {}
      expectedType? := none
    })

/-- Push hover info for glossary entry idents from the parser.
    Entries that generated typeclasses (SLIST → SlistSpec, CACHE → CacheSpec) get hover
    pointing to the class. Plain entries (SNAME, STYPE) point to the parent struct field. -/
def pushGlossaryHoverInfo (structName : String) (identNodes : Array Syntax)
    (classNames : Std.HashMap String Name) : CommandElabM Unit := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let fullStructName := ns ++ Name.mkSimple structName
  for ident in identNodes do
    let .ident _ rawVal _ _ := ident | continue
    let some _ := ident.getPos? | continue
    let rawText := rawVal.toString
    -- Prefer the class if this entry generated one
    let hoverExpr? : Option Expr :=
      if let some className := classNames.get? rawText then
        if (env.find? className).isSome then some (Expr.const className [])
        else some (Expr.const fullStructName [])
      else
        -- Fall back to struct field projection
        let fieldFQN := fullStructName ++ Name.mkSimple rawText.toLower
        if (env.find? fieldFQN).isSome then some (Expr.const fieldFQN [])
        else if (env.find? fullStructName).isSome then some (Expr.const fullStructName [])
        else none
    if let some hoverExpr := hoverExpr? then
      pushInfoLeaf (.ofTermInfo {
        elaborator := `VeriDNS.RFC.includeRfc
        stx := ident
        expr := hoverExpr
        lctx := {}
        expectedType? := none
      })

/-- Normalize text for prose hover matching: drop parentheticals, collapse
    whitespace runs to single spaces, lowercase. Applied to both the parser
    ident text (raw RFC text with line breaks and indentation) and the prop
    source sentence (already parenthetical-stripped) so substring containment
    is insensitive to layout differences. -/
private def normalizeForHoverMatch (s : String) : String := Id.run do
  let mut out := ""
  let mut depth : Nat := 0
  let mut lastSpace := true
  for c in s.toList do
    if c == '(' then
      depth := depth + 1
    else if c == ')' then
      if depth > 0 then depth := depth - 1
    else if depth == 0 then
      if c == ' ' || c == '\n' || c == '\t' then
        if !lastSpace then out := out.push ' '
        lastSpace := true
      else
        out := out.push c.toLower
        lastSpace := false
  return trimStr out

/-- Map from ident start byte position to the declaration whose hover claimed
    that ident. SubVerso renders exactly ONE TermInfo per token, so every
    pusher must consult this map: the first declaration to land on an ident
    becomes its hover target, and later ones are appended to that primary's
    docstring (see `appendSiblingDoc`) instead of being pushed and lost. -/
abbrev HoverClaims := Std.HashMap Nat Name

/-- Pretty-print a generated declaration for embedding in a hover docstring.
    Zero-binder `Prop` defs show their body (the proposition is the payload;
    the type `Prop` says nothing), parameterized defs and everything else
    show their type, and inductives list their constructors in order. -/
private def ppGeneratedDecl (name : Name) : CommandElabM (Option String) := do
  let env ← getEnv
  let some ci := env.find? name | return none
  let short := name.components.getLast!.toString
  match ci with
  | .inductInfo ind =>
    let ctors := ind.ctors.map (fun c => c.components.getLast!.toString)
    return some s!"inductive {short}\n  | {"\n  | ".intercalate ctors}"
  | .defnInfo d =>
    if d.type.isProp then
      let body ← liftCoreM <| MetaM.run' (Meta.ppExpr d.value)
      return some s!"{short} : Prop :=\n  {body.pretty}"
    else
      let ty ← liftCoreM <| MetaM.run' (Meta.ppExpr d.type)
      return some s!"{short} : {ty.pretty}"
  | _ =>
    let ty ← liftCoreM <| MetaM.run' (Meta.ppExpr ci.type)
    return some s!"{short} : {ty.pretty}"

/-- Append `sibling`'s rendered declaration to `primary`'s docstring under an
    "Also generated from this passage" section, so a definition that lost the
    one-hover-per-token race is still visible from the passage's hover. -/
private def appendSiblingDoc (primary sibling : Name) : CommandElabM Unit := do
  if primary == sibling then return
  let some rendered ← ppGeneratedDecl sibling | return
  let env ← getEnv
  let old := (← findDocString? env primary).getD ""
  let entry := s!"```lean\n{rendered}\n```"
  if hasSub old entry then return
  let sectionHeader := "**Also generated from this passage:**"
  let base := if hasSub old sectionHeader then old
    else if old.isEmpty then sectionHeader
    else s!"{old}\n\n{sectionHeader}"
  addDocStringCore primary s!"{base}\n{entry}"

/-- Claim hover on `arg` (an ident starting at byte `pos`) for `target`.
    First claimant pushes TermInfo; later claimants are folded into the
    claimant's docstring. Returns the updated claims map. -/
def claimHover (claims : HoverClaims) (arg : Syntax) (pos : Nat) (target : Name)
    : CommandElabM HoverClaims := do
  match claims.get? pos with
  | some primary =>
    appendSiblingDoc primary target
    return claims
  | none =>
    pushInfoLeaf (.ofTermInfo {
      elaborator := `VeriDNS.RFC.includeRfc
      stx := arg
      expr := .const target []
      lctx := {}
      expectedType? := none
    })
    return claims.insert pos target

/-- Push hover info linking prose sentence idents to their generated props.
    Each (propName, srcSentence) pair is matched against parser ident text by
    normalized substring containment; the prop attaches to the first ident
    whose text contains its source sentence. Used by prose-only, algorithm,
    and glossary-intro sections where props derive from free prose rather
    than where-block field descriptions.
    Returns the hover claims map (ident position → hover target) so later
    pushers fold colliding hovers into docstrings and the generic
    struct-hover fallback skips claimed idents. -/
def pushProseHoverInfo (propSrcs : Array (Name × String)) (rfcNodeArgs : Array Syntax)
    : CommandElabM HoverClaims := do
  let env ← getEnv
  let mut claims : HoverClaims := {}
  for (propName, src) in propSrcs do
    if !(env.find? propName).isSome then continue
    let srcNorm := normalizeForHoverMatch src
    if srcNorm.isEmpty then continue
    for arg in rfcNodeArgs do
      let .ident _ rawVal _ _ := arg | continue
      let some pos := arg.getPos? | continue
      if hasSub (normalizeForHoverMatch rawVal.toString) srcNorm then
        claims ← claimHover claims arg pos.byteIdx propName
        break
  return claims

/-- Push hover info for parsed description sentences.
    Walks parser ident nodes: field-name idents set the current field,
    subsequent non-field idents are sentence fragments that get TermInfo
    pointing to the corresponding property def (e.g., `id_prop_0`).
    Sentence idents exist because rfcTextBodyFn splits descriptions at
    sentence boundaries via findSentenceSplitPoints. -/
def pushSentenceHoverInfo (structName : String) (rfcNodeArgs : Array Lean.Syntax)
    (fields : Array MergedField) (claims : HoverClaims) : CommandElabM HoverClaims := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let fullStructName := ns ++ Name.mkSimple structName
  if !(env.find? fullStructName).isSome then return claims
  let fieldNames := fields.map (·.name.toUpper)
  let mut claims := claims
  let mut currentField : Option MergedField := none
  let mut sentenceIdx : Nat := 0
  for arg in rfcNodeArgs do
    if !arg.isIdent then continue
    let .ident _ rawVal _ _ := arg | continue
    let rawText := rawVal.toString
    -- Check if this is a field name ident
    if fieldNames.contains rawText.toUpper then
      currentField := fields.find? (fun f => f.name.toUpper == rawText.toUpper)
      sentenceIdx := 0
      continue
    -- If we have a current field, this is a sentence ident
    let some field := currentField | continue
    if field.description.isEmpty then continue
    let some pos := arg.getPos? | continue
    let propName := ns ++ Name.mkSimple s!"{field.name.toLower}_prop_{sentenceIdx}"
    -- The complement-semantics def (e.g. ra_semantics_0 from "denotes
    -- whether ..." sentences) may coexist with the clause prop; the prop
    -- claims the hover and the semantics def rides along in its docstring.
    let semName := ns ++ Name.mkSimple s!"{field.name.toLower}_semantics_{sentenceIdx}"
    let targets := #[propName, semName].filter (env.find? · |>.isSome)
    for target in targets do
      claims ← claimHover claims arg pos.byteIdx target
    sentenceIdx := sentenceIdx + 1
  return claims

/-- Generate formal Prop definitions from example sentences in RFC text.
    Analyzes "For example" / "e.g." / "i.e." patterns via the NLP pipeline
    and generates ∀-quantified Prop definitions over the struct.
    Also pushes hover info linking trigger phrases to generated definitions. -/
def generateExampleProps (structName : String) (text : String)
    (mergedFields : Array MergedField) (rfcNodeArgs : Array Lean.Syntax)
    (claims : HoverClaims) : CommandElabM HoverClaims := do
  let ns ← getCurrNamespace
  let fieldNames := mergedFields.map (·.name)
  let examples := NLP.analyzeExamples text fieldNames
  if examples.isEmpty then return claims
  let structIdent := mkIdent (Name.mkSimple structName)
  let wIdent := mkIdent `w
  for idx in [:examples.size] do
    let prop := examples[idx]!
    match prop with
    | .conditional (.fieldEq field value) (.fieldAccess targetField targetValue) =>
      let propName := mkIdent (Name.mkSimple s!"{structName.toLower}_example_{idx}")
      -- Resolve field bit width for the BitVec cast
      let bw := findFieldBitWidth field mergedFields |>.getD 8
      let bwLit := Syntax.mkNumLit (toString bw)
      let valLit := Syntax.mkNumLit (toString value)
      let fieldProj := mkIdent (Name.mkSimple structName ++ Name.mkSimple field.toLower)
      -- Check if target field is variable-length (ByteArray)
      let mut propText := ""
      if isVariableField targetField mergedFields then
        let accessorIdent := mkIdent `getBit
        let targetProj := mkIdent (Name.mkSimple structName ++ Name.mkSimple targetField.toLower)
        let targetValLit := Syntax.mkNumLit (toString targetValue)
        let propVal ← `(∀ ($wIdent : $structIdent)
          ($accessorIdent : ByteArray → Nat → Bool),
          $fieldProj $wIdent = ($valLit : BitVec $bwLit) →
          $accessorIdent ($targetProj $wIdent) $targetValLit = true)
        elabCommand (← `(def $propName : Prop := $propVal))
        let fmt ← liftCoreM (ppTerm propVal)
        propText := fmt.pretty
      else
        -- Non-variable target field: simpler prop without accessor
        let targetProj := mkIdent (Name.mkSimple structName ++ Name.mkSimple targetField.toLower)
        let targetValLit := Syntax.mkNumLit (toString targetValue)
        let targetBw := findFieldBitWidth targetField mergedFields |>.getD 8
        let targetBwLit := Syntax.mkNumLit (toString targetBw)
        let propVal ← `(∀ ($wIdent : $structIdent),
          $fieldProj $wIdent = ($valLit : BitVec $bwLit) →
          $targetProj $wIdent = ($targetValLit : BitVec $targetBwLit))
        elabCommand (← `(def $propName : Prop := $propVal))
        let fmt ← liftCoreM (ppTerm propVal)
        propText := fmt.pretty
      let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_example_{idx}"
      addDocStringCore fullName
        s!"Example: {field} = {value} → {targetField} access at {targetValue}\n```lean\n{propText}\n```"
    | .conditional (.fieldEq field value) (.unresolved _) =>
      let propName := mkIdent (Name.mkSimple s!"{structName.toLower}_example_{idx}")
      let bw := findFieldBitWidth field mergedFields |>.getD 8
      let bwLit := Syntax.mkNumLit (toString bw)
      let valLit := Syntax.mkNumLit (toString value)
      let fieldProj := mkIdent (Name.mkSimple structName ++ Name.mkSimple field.toLower)
      let pIdent := mkIdent `P
      let propVal ← `(∀ ($wIdent : $structIdent) ($pIdent : $structIdent → Prop),
        $fieldProj $wIdent = ($valLit : BitVec $bwLit) → $pIdent $wIdent)
      elabCommand (← `(def $propName : Prop := $propVal))
      let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_example_{idx}"
      let fmt ← liftCoreM (ppTerm propVal)
      addDocStringCore fullName s!"Example: {field} = {value} → (opaque consequent)\n```lean\n{fmt.pretty}\n```"
    | .assignment lhs rhs =>
      -- Skip simple assignments — they don't produce useful Props
      let _ := (lhs, rhs)
      pure ()
    | _ => pure ()
  -- Push hover info on idents containing example triggers
  let exampleTriggers := ["e.g.", "i.e.", "For example", "for example"]
  let mut claims := claims
  for arg in rfcNodeArgs do
    if !arg.isIdent then continue
    let .ident _ rawVal _ _ := arg | continue
    let some pos := arg.getPos? | continue
    let rawText := rawVal.toString
    if exampleTriggers.any (fun t => hasSub rawText t) then
      let env ← getEnv
      -- Point hover to the first generated example prop if it exists
      let examplePropName := ns ++ Name.mkSimple s!"{structName.toLower}_example_0"
      let fullStructName := ns ++ Name.mkSimple structName
      let target := if (env.find? examplePropName).isSome then examplePropName
        else if (env.find? fullStructName).isSome then fullStructName
        else ``True
      claims ← claimHover claims arg pos.byteIdx target
  return claims

-- ============================================================
-- Main pipeline
-- ============================================================

/-- Process verified RFC text to generate formal Lean specifications.

    Recognizes section headers, bit diagrams, and where blocks.
    Generates structures with BitVec fields and inductive types
    for value enumerations. Stores metadata for de-elaboration.
    Returns the struct name, merged fields (if any), and prop-source pairs
    (prop name × source sentence) for hover support. -/
def processRfcText (text : String) (rfcNodeArgs : Array Syntax := #[])
    : CommandElabM (Option (String × Array MergedField × Array (Name × String))) := do
  let title := extractSectionTitle text |>.getD "Fields"
  let structName := deriveStructName title

  let allGroups := parseBitDiagrams text
  let diagramFields := match allGroups[0]? with
    | some group => group.fields
    | none => #[]
  let exampleGroups := allGroups.filter (·.isExample)
  let whereFields := parseWhereBlock text

  if diagramFields.isEmpty then
    -- Try section diagram path (e.g., RFC 1035 section 4.1)
    let (sectionFields, sectionWhereFields) := parseSectionDiagram text
    if !sectionFields.isEmpty then
      let merged' := mergeFields sectionFields sectionWhereFields
      let prose := extractAllProse text
      let env ← getEnv
      let ns ← getCurrNamespace
      let merged := merged'.map fun mf =>
        let resolved := resolveFieldType env ns mf.name
        let isArr := shouldBeArray mf.name mf.description prose
        { mf with resolvedType := resolved, isArray := isArr }
      let sectionHeader := extractSectionHeader text |>.getD ""
      let preProse := extractProse text
      let docstring := if preProse.isEmpty then sectionHeader
        else s!"{sectionHeader}\n\n{preProse}"
      generateStructure structName docstring merged
      generateProperties structName merged
      generateCrossStructProps structName merged
      storeFieldDescriptions structName merged
      return some (structName, merged, #[])
    -- Glossary path (e.g., RFC 1034 §5.3.2: NAME  description format)
    -- Require at least 2 entries: a single match is a column-header line
    -- (e.g., "TYPE  value and meaning" in §3.2.2), not a glossary.
    let glossaryEntries := parseGlossaryList text
    if glossaryEntries.size >= 2 then
      let env ← getEnv
      let ns ← getCurrNamespace
      let resolvedTypes := resolveGlossaryFieldTypes glossaryEntries env ns

      -- Phase 1: Classify entries and derive typeclasses for "structure" descriptions
      let mut classSpecs : Array (String × ClassSpec) := #[]  -- (entryName, spec)
      let mut classNames : Std.HashMap String Name := {}  -- entryName → class full name
      let mut allTypeParams : Array (String × String) := #[]  -- (letter, concept) across all classes
      let mut seenParamLetters : Array String := #[]
      let mut sameFormRefs : Array (String × String) := #[]  -- (entry, refTarget)

      for entry in glossaryEntries do
        let desc := entry.description.toLower
        if let some refName := sameFormReference entry.description then
          sameFormRefs := sameFormRefs.push (entry.name, refName)
        else if hasSub desc "structure" then
          -- Full NLP inference for structure descriptions
          let clauses := NLP.parseProseClauses entry.description
          let spec := inferClassFromClauses entry.name clauses env ns entry.description
          classSpecs := classSpecs.push (entry.name, spec)
          -- Collect type params
          for (letter, concept) in spec.typeParams do
            unless seenParamLetters.contains letter do
              allTypeParams := allTypeParams.push (letter, concept)
              seenParamLetters := seenParamLetters.push letter

      -- Phase 2: Generate class declarations
      for (entryName, spec) in classSpecs do
        let fullName ← generateGlossaryClass spec
        classNames := classNames.insert entryName fullName

      -- Propagate "same form as X" references
      for (entry, refName) in sameFormRefs do
        if let some refClass := classNames.get? refName then
          classNames := classNames.insert entry refClass

      -- Phase 3: Build polymorphic parent structure
      let mut glossaryFields : Array MergedField := #[]
      let mut selfParamLetters : Array String := #[]
      for (_entryName, spec) in classSpecs do
        let selfLetter := (spec.className.take 1).toString
        selfParamLetters := selfParamLetters.push selfLetter

      -- Build fields with resolved types (concrete fields use env lookup, abstract use type params)
      for (name, resolvedType) in resolvedTypes do
        let entry := glossaryEntries.find? (fun e => e.name == name) |>.get!
        -- Check if this entry has a class associated
        if let some className := classNames.get? name then
          -- Find the self-param letter for this class
          let classSpec := classSpecs.find? (fun (n, _) => n == name) |>.map (·.2)
          -- For "same form as" refs, find the original's spec
          let effectiveSpec := classSpec <|>
            (sameFormRefs.find? (fun (e, _) => e == name) |>.bind fun (_, ref) =>
              classSpecs.find? (fun (n, _) => n == ref) |>.map (·.2))
          if let some spec := effectiveSpec then
            let selfLetter := (spec.className.take 1).toString
            glossaryFields := glossaryFields.push
              ⟨name, none, true, entry.description, #[], none,
               some (ns ++ Name.mkSimple selfLetter), false⟩
          else
            glossaryFields := glossaryFields.push
              ⟨name, none, true, entry.description, #[], none, resolvedType, false⟩
        else
          glossaryFields := glossaryFields.push
            ⟨name, none, true, entry.description, #[], none, resolvedType, false⟩

      let sectionHeader := extractSectionHeader text |>.getD ""
      let introProse := extractProseBeforeGlossary text glossaryEntries
      let docstring := if introProse.isEmpty then sectionHeader
        else s!"{sectionHeader}\n\n{introProse}"

      if !allTypeParams.isEmpty || !classSpecs.isEmpty then
        -- Generate polymorphic structure via string
        let polyTypeParams := selfParamLetters ++ allTypeParams.map (·.1)
        let polyInstSpecs := classSpecs.map fun (_name, spec) =>
          let selfLetter := (spec.className.take 1).toString
          let paramNames := spec.typeParams.map (·.1)
          (spec.className, #[selfLetter] ++ paramNames)
        let polyFieldNames := glossaryFields.map (·.name.toLower)
        let mut polyFieldTypes : Array String := #[]
        for f in glossaryFields do
          match f.resolvedType with
          | some n => polyFieldTypes := polyFieldTypes.push (toString n.components.getLast!)
          | none => match f.bits with
            | some b => polyFieldTypes := polyFieldTypes.push s!"BitVec {b}"
            | none => polyFieldTypes := polyFieldTypes.push "ByteArray"
        let structStr := mkPolymorphicStructString structName polyTypeParams
          polyInstSpecs polyFieldNames polyFieldTypes #["Inhabited"]
        elabCommandStr structStr
        let fullName := ns ++ Name.mkSimple structName
        if !docstring.isEmpty then
          addDocStringCore fullName docstring
      else
        generateStructure structName docstring glossaryFields

      -- Generate props from intro prose via prose_clause_rules
      let env ← getEnv
      let clausesWithSrc := NLP.parseProseClausesWithSrc introProse
      let rules := proseClauseRuleExt.getState env
      let structIdent := mkIdent (Name.mkSimple structName)
      let ctx : ProseInterpContext := { structName, structIdent, ns }
      let mut propIdx : Nat := 0
      let mut propSrcs : Array (Name × String) := #[]
      let mut allBindings : Std.HashMap String (Nat ⊕ String) := {}
      for (clause, src) in clausesWithSrc do
        for rule in rules do
          if let some bindings := matchProseClausePattern clause rule.pattern then
            for (k, v) in bindings do
              allBindings := allBindings.insert k v
            if isPurelyTrivial rule.output then continue
            let result ← interpretPropSpecForProse rule.output ctx #[] allBindings
            for propTerm in result.propTerms do
              let propName := mkIdent (Name.mkSimple s!"{structName.toLower}_prop_{propIdx}")
              elabCommand (← `(def $propName : Prop := $propTerm))
              let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_prop_{propIdx}"
              let fmt ← liftCoreM (ppTerm propTerm)
              addDocStringCore fullName s!"{structName}: prop {propIdx}\n```lean\n{fmt.pretty}\n```"
              propSrcs := propSrcs.push (fullName, src)
              propIdx := propIdx + 1
      -- Push hover info for glossary entry idents
      let glossaryIdents := rfcNodeArgs.filter fun arg =>
        match arg with
        | .ident _ _ _ _ => true
        | _ => false
      pushGlossaryHoverInfo structName glossaryIdents classNames
      return some (structName, glossaryFields, propSrcs)
    -- Algorithm path (e.g., RFC 1034 §5.3.3: numbered step lists)
    let (algorithmTopSteps, algorithmSubSteps) := parseNumberedAlgorithm text
    if !algorithmTopSteps.isEmpty then
      let ns ← getCurrNamespace
      generateAlgorithmTypes structName algorithmTopSteps algorithmSubSteps
      -- Generate step relation (guards, StepSpec, StepSpecStar, isTerminal)
      -- plus refined guards and obligations (returned for hover support)
      let obligationSrcs ← generateStepRelation structName algorithmTopSteps algorithmSubSteps
      -- Parse algorithm prose with conditional awareness (NLP-driven)
      let env ← getEnv
      let prose := extractAllProse text
      let condClauses := NLP.parseAlgorithmClausesWithSrc prose
      let contextTypes := collectContextTypes env ns
      -- Derive properties from grammatical structure
      let mut propIdx : Nat := 0
      let mut propSrcs : Array (Name × String) := obligationSrcs
      for (cc, src) in condClauses do
        let propSpec? := deriveAlgorithmProperty cc env ns contextTypes
        if let some propSpec := propSpec? then
          if isPurelyTrivial propSpec then continue
          let propTerms ← interpretPropSpecForAlgorithm propSpec env ns #[]
          if !propTerms.isEmpty then
            for propTerm in propTerms do
              let propName := mkIdent (Name.mkSimple s!"{structName.toLower}_prop_{propIdx}")
              elabCommand (← `(def $propName : Prop := $propTerm))
              let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_prop_{propIdx}"
              let fmt ← liftCoreM (ppTerm propTerm)
              addDocStringCore fullName s!"Algorithm: prop {propIdx}\n```lean\n{fmt.pretty}\n```"
              propSrcs := propSrcs.push (fullName, src)
              propIdx := propIdx + 1
      -- Entry-structure derivation: membership/possessive imperatives, modal
      -- partiality, and keep-track purposes describe the per-entry contents
      -- of an ALL-CAPS structure ("Copy the names into SLIST", "Set up their
      -- addresses ...", "may ... the addresses are not available", "keep
      -- track of previous transmissions") → structure SlistEntry.
      let entrySrcs ← generateEntryStructure prose
      propSrcs := propSrcs ++ entrySrcs
      -- Recommendation derivation: modal partiality + superlative recommendation.
      -- "It may be the case that ⟨C⟩" states the situation MAY occur (partiality
      -- of the underlying operation); "the best is to ⟨action⟩" recommends the
      -- reaction. C is a negated copula over an availability adjective →
      -- abstract Bool predicate over an abstract state σ; the action's gerund +
      -- "for the ⟨obj⟩" → abstract action predicate. Generates:
      --   ∀ s : σ, ⟨pred⟩ s = false → ⟨action⟩ s
      if hasSub prose "the case that " && hasSub prose "the best is to " then
        let comp := trimStr (((prose.splitOn "the case that ").getD 1 "").splitOn "."
          |>.headD "")
        let action := trimStr (((prose.splitOn "the best is to ").getD 1 "").splitOn "."
          |>.headD "")
        let compWords := comp.toLower.splitOn " " |>.filter (!·.isEmpty) |>.toArray
        let isNegated := compWords.contains "not"
        let copIdx? := compWords.findIdx? (fun w => w == "is" || w == "are")
        match copIdx?, compWords.back? with
        | some ci, some adjWord =>
          if isNegated && ci > 0 then
            let subjHead := compWords[ci - 1]!
            let predName := s!"{subjHead}{capitalize adjWord}"
            let actWords := action.toLower.splitOn " " |>.filter (!·.isEmpty) |>.toArray
            let gerIdx? := actWords.findIdx? (fun w => w.endsWith "ing" && w.length > 4)
            match gerIdx? with
            | some gi =>
              let stem := (actWords[gi]!.dropEnd 3).toString
              -- object: first non-determiner word after a following "for"
              let objWord? : Option String := Id.run do
                for j in [gi + 1:actWords.size] do
                  if actWords[j]! == "for" then
                    for k in [j + 1:actWords.size] do
                      if !#["the", "a", "an"].contains actWords[k]! then
                        return some actWords[k]!
                    return none
                return none
              if let some objWord := objWord? then
                let actName := s!"{stem}{capitalize objWord}"
                let recName := mkIdent (Name.mkSimple s!"recommendation_{predName}")
                let sigmaId := mkIdent (Name.mkSimple "σ")
                let sId := mkIdent (Name.mkSimple "s")
                let predId := mkIdent (Name.mkSimple predName)
                let actId := mkIdent (Name.mkSimple actName)
                elabCommand (← `(def $recName ($sigmaId : Type)
                  ($predId : $sigmaId → Bool) ($actId : $sigmaId → Prop) : Prop :=
                  ∀ ($sId : $sigmaId), $predId $sId = false → $actId $sId))
                let fullName := ns ++ Name.mkSimple s!"recommendation_{predName}"
                addDocStringCore fullName
                  (s!"Recommendation (modal \"may\" marks `{predName}` as partial; " ++
                   s!"\"the best is to\" recommends `{actName}` when it fails): " ++
                   s!"\"It may be the case that {comp}. The best is to {action}.\"")
                propSrcs := propSrcs.push (fullName, comp)
            | none => pure ()
        | _, _ => pure ()
      -- "should check (to see) that ⟨condition⟩. ... If not, ⟨np⟩ ...
      -- should be ⟨participle⟩." (§5.3.3 delegation validation): the
      -- anaphoric "not" negates the checked condition; the consequent is
      -- OBLIGATED on its failure. The condition clause is parsed for its
      -- predicate name (subject + comparative + PPs); the consequent's
      -- subject NP and modal passive give the action name.
      let sentences := Property.splitSentences prose
      for i in [:sentences.size] do
        for j in [i+1:min sentences.size (i+3)] do
          let s1 := sentences[i]!.toLower
          let s2 := trimStr (sentences[j]!.toLower)
          let marker? := if hasSub s1 "check to see that " then some "check to see that "
            else if hasSub s1 "check that " then some "check that " else none
          match marker? with
          | some marker =>
            if s2.startsWith "if not" then
              -- strip RFC scare quotes before parsing
              let condText := trimStr (String.join
                (((s1.splitOn marker).getD 1 "").splitOn "\""))
              let condClause := NLP.parseSentenceClause condText
              let actTokens := NLP.tagPOS (NLP.tokenize s2)
              -- consequent subject: first NP after "if not,"
              let subjHead? : Option String := Id.run do
                for k in [:actTokens.size] do
                  if actTokens[k]!.pos == .det then
                    if let some (np, _) := NLP.parseNP actTokens k then
                      return some np.head
                    return none
                return none
              -- modal passive: "be ⟨participle⟩"
              let participle? : Option String := Id.run do
                for k in [:actTokens.size] do
                  if k + 1 < actTokens.size && actTokens[k]!.word == "be" then
                    let t := actTokens[k + 1]!
                    if t.pos == .verb || (t.pos == .adj && t.word.endsWith "ed") then
                      return some t.word
                return none
              match predNameOfClause condClause false, subjHead?, participle? with
              | some condName, some subjHead, some participle =>
                let actName := subjHead ++ capitalize participle
                let defShort := s!"obligation_{actName}"
                let obId := mkIdent (Name.mkSimple defShort)
                let sigmaId := mkIdent (Name.mkSimple "σ")
                let condId := mkIdent (Name.mkSimple condName)
                let actId := mkIdent (Name.mkSimple actName)
                let sId := mkIdent (Name.mkSimple "s")
                elabCommand (← `(def $obId ($sigmaId : Type)
                    ($condId : $sigmaId → Bool) ($actId : $sigmaId → Prop) : Prop :=
                  ∀ ($sId : $sigmaId), $condId $sId = false → $actId $sId))
                let fullName := ns ++ Name.mkSimple defShort
                addDocStringCore fullName
                  (s!"Obligation on the failure of a checked condition: when " ++
                   s!"`{condName}` fails, `{actName}` MUST hold. Derived from " ++
                   s!"\"{s1}\" + \"{s2}\" (anaphoric \"if not\").")
                propSrcs := propSrcs.push (fullName, s2)
              | _, _, _ =>
                logInfo s!"check-that/if-not rule: no names derivable from \"{s1}\" / \"{s2}\""
          | none => pure ()
      return some (structName, #[], propSrcs)
    -- Prose-only section: derive structure + ∀ constraints from clause matching
    let ns ← getCurrNamespace
    let prose := extractAllProse text
    let clausesWithSrc := NLP.parseProseClausesWithSrc prose
    let structFieldsRaw := NLP.deriveStructFields prose
    -- MUST-match obligation (e.g. RFC 5452 §9.1): "MUST match responses to
    -- all of the following attributes" + "o ⟨attribute⟩" bullets +
    -- "a mismatch ... MUST be considered invalid" → accepted responses
    -- satisfy every attribute matcher (abstract Bool predicates, one per
    -- bullet — the Spec cannot observe addresses, ports, or wire contents).
    let mut matchObSrcs : Array (Name × String) := #[]
    -- Ranked-list rule (RFC 2181 §5.4.1): a sentence carrying an ordering
    -- directive ("… from ⟨pole⟩ to ⟨pole⟩ …", parsed by
    -- `NLP.parseOrderingDirective` — the superlative poles are lexical and
    -- the "from…to…" frame structural, so nothing is keyed on a fixed
    -- phrase) followed by "+"-prefixed bullets → an ordered enum whose
    -- constructor order IS the ranking (0 = the high pole; bullets are
    -- reversed when the directive runs low→high). The type name is the
    -- directive sentence's subject noun. The generated `toCode` doubles as
    -- the rank; a companion `⟨name⟩.atLeastAsTrustworthy` order relation
    -- (rank ≤) is emitted, and a negated-passive "be returned as answers"
    -- clause yields the answer-grade obligation over that rank.
    let rankDir? : Option (Bool × String × Nat) := Id.run do
      let lines := (text.splitOn "\n").toArray
      for li in [:lines.size] do
        let toks := NLP.tagPOS (NLP.tokenize (trimStr lines[li]!))
        if let some dir := NLP.parseOrderingDirective toks then
          -- subject = first nominal token on the directive line
          let subj? := toks.findSome? fun t =>
            if (t.pos == .noun || t.pos == .nounPlural || t.pos == .propNoun)
                && t.word.length > 2 && t.word.toList.all Char.isAlpha
            then some t.word else none
          return some (dir, capitalize (subj?.getD "rank").toLower, li)
      return none
    if let some (dir, typeNm, markerLine) := rankDir? then
      let lines := (text.splitOn "\n").toArray
      -- collect "+" bullets after the directive line; a bullet may wrap
      -- across indented continuation lines (no leading "+").
      let bulletsRaw : Array String := Id.run do
        let mut out : Array String := #[]
        let mut cur := ""
        for li in [markerLine + 1 : lines.size] do
          let t := trimStr lines[li]!
          if t.startsWith "+" then
            if !cur.isEmpty then out := out.push cur
            cur := trimStr (t.drop 1).toString
          else if t.isEmpty then
            if !cur.isEmpty then out := out.push cur
            cur := ""
            if !out.isEmpty then return out  -- blank line ends the list
          else if !cur.isEmpty then
            cur := cur ++ " " ++ t
        if !cur.isEmpty then out := out.push cur
        return out
      -- `dir = true` means high→low (item 0 already most-trustworthy);
      -- otherwise reverse so rank 0 is the most-trustworthy end.
      let bullets := if dir then bulletsRaw else bulletsRaw.reverse
      if bullets.size >= 2 then
        -- derive a constructor name: first two content words (noun/adj,
        -- minus generic stems), camelCased; dedup by suffixing the index.
        let rankStops := #["data", "information", "the", "a", "an", "of",
          "from", "in", "other", "than", "included", "or", "and", "rrset",
          "rrs", "reply", "answer"]
        let mut values : Array EnumValue := #[]
        let mut usedNames : Array String := #[]
        for i in [:bullets.size] do
          let toks := NLP.tagPOS (NLP.tokenize bullets[i]!.toLower)
          -- strip non-alphanumerics so hyphenated words ("non-authoritative")
          -- yield valid identifier fragments ("nonauthoritative")
          let clean := fun (w : String) =>
            String.ofList (w.toList.filter Char.isAlphanum)
          let content := toks.filterMap fun t =>
            if (t.pos == .noun || t.pos == .nounPlural || t.pos == .adj)
                && !rankStops.contains t.word.toLower && t.word.length > 2
            then some (clean t.word.toLower) else none
          let picked := (content.toList.filter (!·.isEmpty)).take 2
          let baseName := if picked.isEmpty then s!"tier{i}"
            else toCamelCase picked
          let name := if usedNames.contains baseName then s!"{baseName}{i}"
            else baseName
          usedNames := usedNames.push name
          values := values.push ⟨i, name, trimStr bullets[i]!⟩
        let credName ← generateValueListType typeNm values
        let short := credName.components.getLast!.toString
        -- Type-level docstring: the ranked tier list, so the hover on the
        -- ordering-directive sentence shows the full generated enum.
        let tierLines := values.map fun v => s!"{v.code}. `{v.name}` — {v.description}"
        addDocStringCore credName
          (s!"Ranked tiers from the ordering directive (rank 0 = the " ++
           s!"most-trustworthy pole):\n\n" ++ "\n".intercalate tierLines.toList)
        -- order relation: a is at least as trustworthy as b  ⟺  rank a ≤ rank b
        elabCommandStr (s!"def {short}.atLeastAsTrustworthy (a b : {short}) : Prop := " ++
          s!"{short}.toCode a ≤ {short}.toCode b")
        addDocStringCore (credName ++ Name.mkSimple "atLeastAsTrustworthy")
          ("Trust order from RFC 2181 §5.4.1 ordering directive: rank 0 is the " ++
           "most-trustworthy pole; `a` is at least as trustworthy as `b` iff " ++
           "its rank is ≤.")
        -- answer-grade obligation: a negated passive "be returned as
        -- answers" (negation + participle "returned" + object "answers")
        -- → the least-trustworthy tier (max rank) is not answerable.
        let notAnswerable : Bool := Id.run do
          for sentence in Property.splitSentences prose do
            let toks := NLP.tagPOS (NLP.tokenize sentence.toLower)
            let hasNeg := toks.any fun t =>
              t.word.toLower == "not" || t.word.toLower == "never"
            let retIdx? := (Array.range toks.size).find? fun i =>
              toks[i]!.pos == .verb && toks[i]!.word.toLower == "returned"
            if hasNeg then
              if let some ri := retIdx? then
                if (toks.extract ri toks.size).any
                    (fun t => stripPlural t.word.toLower == "answer") then
                  return true
          return false
        if notAnswerable then
          let floor := bullets.size - 1
          let obId := mkIdent (Name.mkSimple "obligation_untrustworthyNotAnswerable")
          let sigmaId := mkIdent (Name.mkSimple "σ")
          let credId := mkIdent (Name.mkSimple "credibility")
          let ansId := mkIdent (Name.mkSimple "returnedAsAnswer")
          let sId := mkIdent (Name.mkSimple "s")
          let credTy := mkIdent credName
          let rankFn := mkIdent (credName ++ Name.mkSimple "toCode")
          let floorLit : TSyntax `term := ⟨Syntax.mkNumLit (toString floor)⟩
          elabCommand (← `(def $obId
              ($sigmaId : Type) ($credId : $sigmaId → $credTy)
              ($ansId : $sigmaId → Bool) : Prop :=
            ∀ ($sId : $sigmaId), $rankFn ($credId $sId) ≥ $floorLit →
              $ansId $sId = false))
          addDocStringCore (ns ++ Name.mkSimple "obligation_untrustworthyNotAnswerable")
            ("RFC 2181 §5.4.1: data cached from the least-trustworthy grouping " ++
             "(max rank) must never be returned as an answer to a query " ++
             "(it may still appear as additional information): \"should not be " ++
             "cached in such a way that they would ever be returned as answers\".")
          matchObSrcs := matchObSrcs.push
            (ns ++ Name.mkSimple "obligation_untrustworthyNotAnswerable",
             "returned as answers")
        -- The ordering-directive sentence is the source of both the ranked
        -- enum and its order relation; the enum claims the hover and the
        -- relation rides along in its docstring (claimHover collision rule).
        let directiveSrc := trimStr lines[markerLine]!
        matchObSrcs := matchObSrcs.push (credName, directiveSrc)
        matchObSrcs := matchObSrcs.push
          (credName ++ Name.mkSimple "atLeastAsTrustworthy", directiveSrc)
    if hasSub prose.toLower "must match responses to all of the following attributes" then
      -- Collect only the bullets immediately following the trigger sentence
      -- (stop at the first non-blank, non-bullet line).
      let bullets : Array String := Id.run do
        let lines := text.splitOn "\n"
        let mut out : Array String := #[]
        let mut inList := false
        for l in lines do
          let t := trimStr l
          if !inList then
            if hasSub t.toLower "following attributes" then inList := true
          else
            if t.isEmpty then continue
            else if t.startsWith "o  " then
              out := out.push (trimStr ((t.drop 3).toString))
            else
              break
        return out
      if !bullets.isEmpty then
        let mut paramNames : Array String := #[]
        for b in bullets do
          let core := (b.splitOn " against ").headD b
          let words := core.toLower.splitOn " " |>.filter (!·.isEmpty)
          let pn := match words with
            | [] => "attr"
            | w :: ws => w ++ String.join (ws.map capitalize)
          -- dedup
          let pn := if paramNames.contains pn then pn ++ toString paramNames.size else pn
          paramNames := paramNames.push pn
        let obName := mkIdent (Name.mkSimple s!"{structName.toLower}_match_obligation")
        let rhoId := mkIdent (Name.mkSimple "ρ")
        let rId := mkIdent (Name.mkSimple "r")
        let accId := mkIdent (Name.mkSimple "accepted")
        let paramIds := paramNames.map (fun pn => mkIdent (Name.mkSimple pn))
        -- conjunction of (pᵢ r = true)
        let mut conj? : Option (TSyntax `term) := none
        for pid in paramIds do
          let t ← `($pid $rId = true)
          conj? := some (← match conj? with
            | none => pure t
            | some a => `($a ∧ $t))
        if let some conj := conj? then
          let mut body ← `(∀ ($rId : $rhoId), $accId $rId = true → $conj)
          for pid in paramIds.reverse do
            body ← `(fun ($pid : $rhoId → Bool) => $body)
          let lam ← `(fun ($rhoId : Type) ($accId : $rhoId → Bool) => $body)
          elabCommand (← `(def $obName := $lam))
          let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_match_obligation"
          addDocStringCore fullName
            (s!"Accepted responses satisfy every attribute matcher (one abstract " ++
             s!"predicate per bullet, in order: {String.intercalate ", " bullets.toList}): " ++
             "\"MUST match responses to all of the following attributes of the query " ++
             "... A mismatch and the response MUST be considered invalid.\"")
          matchObSrcs := matchObSrcs.push (fullName, "all of the following attributes")
    -- Duration-cap rule (RFC 2308 §5): one sentence limits how long an
    -- entity may be cached ("… to limit for how long it will cache a
    -- negative response …"); a companion sentence carries the recommended
    -- duration range inside the "of" PP of a subject headed "values" and
    -- predicates a default ("Values of one to three hours … would make
    -- sensible a default"). Both facts are read grammatically: the capped
    -- entity is the object NP of the verb "cache" in the limit sentence;
    -- the bound is a ⟨numeral to numeral time-unit⟩ range parsed by
    -- `NLP.parseDurationRange` (word numerals are `.quant` tokens). The
    -- generated Prop caps every cached TTL for the entity at the range's
    -- upper bound.
    let mut capEntity? : Option String := none
    let mut capSecs? : Option Nat := none
    for sentence in Property.splitSentences prose do
      let toks := NLP.tagPOS (NLP.tokenize sentence.toLower)
      let hasLimitVerb := toks.any fun t => t.pos == .verb && t.word == "limit"
      if hasLimitVerb && capEntity?.isNone then
        for i in [:toks.size] do
          if capEntity?.isNone && toks[i]!.pos == .verb && toks[i]!.word == "cache" then
            if let some (np, _) := NLP.parseNP toks (i + 1) (absorbPP := false) then
              let frags := ((np.preAdjs.push np.head).toList.map fun w =>
                String.ofList (w.toList.filter Char.isAlphanum)).filter (!·.isEmpty)
              if !frags.isEmpty then
                capEntity? := some (String.join frags)
      if capSecs?.isNone then
        let hasDefault := toks.any fun t =>
          (t.pos == .noun || t.pos == .nounPlural) && t.word == "default"
        if hasDefault then
          for i in [:toks.size] do
            if capSecs?.isNone && i > 0 && toks[i]!.pos == .prep
                && toks[i]!.word == "of" then
              let hw := toks[i - 1]!.word.toLower
              if hw == "values" || hw == "value" then
                if let some (_, hi, _) := NLP.parseDurationRange toks (i + 1) then
                  capSecs? := some hi
    if let some entity := capEntity? then
      if let some secs := capSecs? then
        let defShort := s!"{structName.toLower}_limit_{entity}_ttl"
        let dName := mkIdent (Name.mkSimple defShort)
        let sigmaId := mkIdent (Name.mkSimple "σ")
        let ttlId := mkIdent (Name.mkSimple "cachedTtl")
        let sId := mkIdent (Name.mkSimple "s")
        let secLit : TSyntax `term := ⟨Syntax.mkNumLit (toString secs)⟩
        elabCommand (← `(def $dName ($sigmaId : Type)
            ($ttlId : $sigmaId → Nat) : Prop :=
          ∀ ($sId : $sigmaId), $ttlId $sId ≤ $secLit))
        let fullName := ns ++ Name.mkSimple defShort
        addDocStringCore fullName
          (s!"Cache-duration cap ({secs} seconds — the upper bound of the " ++
           "recommended default range): every cached TTL for the entity is " ++
           "≤ the cap. Derived from the limit sentence (object NP of " ++
           "\"cache\") and the duration-range default sentence.")
        matchObSrcs := matchObSrcs.push (fullName, "limit for how long")
    -- MUST-add-to obligation (RFC 2308 §6): "When ⟨…⟩ ⟨guard-verb⟩s
    -- ⟨guard-object⟩ it MUST ⟨verb⟩ ⟨object⟩ to ⟨target⟩ with ⟨np
    -- ⟨participle⟩ …⟩." → a conditional membership obligation: whenever
    -- the guard holds and the object exists, its transformed form is a
    -- member of the target collection. Guard, object, target, and
    -- transform are all read from the parse: the when-clause's last
    -- verb + object NP; the imperative's object NP after the modal; the
    -- "to" PP; and the "with" PP's head noun + participle postmodifier.
    for sentence in Property.splitSentences prose do
      let toks := NLP.tagPOS (NLP.tokenize sentence.toLower)
      let isWhenLead : Bool := match toks[0]? with
        | some t => t.pos == .subConj && t.word == "when"
        | none => false
      if !isWhenLead then continue
      let mut mi? : Option Nat := none
      for i in [:toks.size] do
        if mi?.isNone && toks[i]!.word == "must" && i + 1 < toks.size
            && toks[i + 1]!.pos == .verb then
          mi? := some i
      let some mi := mi? | continue
      let mainVerb := toks[mi + 1]!.word
      let some (obj, afterObj) := NLP.parseNP toks (mi + 2) (absorbPP := false)
        | continue
      let (pps, _) := NLP.parsePPs toks afterObj
      let some toPP := pps.find? (fun pp => pp.prep == "to") | continue
      let some withPP := pps.find? (fun pp => pp.prep == "with") | continue
      -- the "with" NP must carry a participle postmodifier (the transform)
      let some partVerb := withPP.np.postMods.findSome? (fun pm =>
        match pm with
        | .participle v _ _ => some v
        | _ => none) | continue
      -- guard: the last ⟨verb, object NP⟩ inside the when-clause (skips
      -- intervening gerund asides like "in answering a query")
      let mut guard? : Option (String × NLP.NounPhrase) := none
      for i in [1:mi] do
        if toks[i]!.pos == .verb then
          if let some (gobj, _) := NLP.parseNP toks (i + 1) (absorbPP := false) then
            guard? := some (toks[i]!.word, gobj)
      let some (gVerb, gObj) := guard? | continue
      let clean := fun (w : String) =>
        String.ofList (w.toList.filter Char.isAlphanum)
      let npWords := fun (np : NLP.NounPhrase) =>
        ((np.preAdjs.push np.head).toList.map clean).filter (!·.isEmpty)
      let objWords := npWords obj
      let targetWords := npWords toPP.np
      if objWords.isEmpty || targetWords.isEmpty then continue
      let objCamel := toCamelCase objWords
      let targetCamel := toCamelCase targetWords
      let guardName := gVerb ++ String.join ((npWords gObj).map capitalize)
      let transformName := "with" ++ capitalize (clean withPP.np.head)
        ++ capitalize (clean partVerb)
      let defShort := s!"obligation_{mainVerb}{capitalize objCamel}To{capitalize targetCamel}"
      let dName := mkIdent (Name.mkSimple defShort)
      let sigmaId := mkIdent (Name.mkSimple "σ")
      let rrTyId := mkIdent (Name.mkSimple "RR")
      let guardId := mkIdent (Name.mkSimple guardName)
      let objId := mkIdent (Name.mkSimple objCamel)
      let transId := mkIdent (Name.mkSimple transformName)
      let targetId := mkIdent (Name.mkSimple targetCamel)
      let sId := mkIdent (Name.mkSimple "s")
      let rrId := mkIdent (Name.mkSimple "rr")
      elabCommand (← `(def $dName ($sigmaId : Type) ($rrTyId : Type)
          ($guardId : $sigmaId → Bool)
          ($objId : $sigmaId → Option $rrTyId)
          ($transId : $sigmaId → $rrTyId → $rrTyId)
          ($targetId : $sigmaId → Array $rrTyId) : Prop :=
        ∀ ($sId : $sigmaId), $guardId $sId = true →
          ∀ ($rrId : $rrTyId), $objId $sId = some $rrId →
            $transId $sId $rrId ∈ $targetId $sId))
      let fullName := ns ++ Name.mkSimple defShort
      addDocStringCore fullName
        (s!"Conditional membership obligation: whenever `{guardName}` holds " ++
         s!"and a `{objCamel}` exists, its `{transformName}` form is a member " ++
         s!"of `{targetCamel}`. Derived from the when-led MUST-{mainVerb} " ++
         s!"sentence: \"{sentence}\"")
      matchObSrcs := matchObSrcs.push (fullName, s!"must {mainVerb} the")
      -- Keyed authority companion class: the when-clause's object ("a
      -- CACHED NEGATIVE response") anaphorically references the keyed
      -- negative-cache class — its premodifiers (participle + adjective)
      -- reconstruct that class's name. The obligation's pieces then also
      -- generate a companion class extending it: the object must first get
      -- INTO the cache ("... the amount of time it was STORED in the
      -- cache" → store method, keyed like the parent, taking the record),
      -- and the "to"-target is served back for the same key ("add ... to
      -- the authority section" → accessor returning the target collection,
      -- transformed per the "with" participle).
      let gWords := (npWords gObj).toArray
      let parentName? : Option String := Id.run do
        let mut adjW : Option String := none
        let mut partW : Option String := none
        for w in gWords.pop do  -- premodifiers only (drop the head)
          if w.endsWith "ed" then partW := some (participleStem w)
          else if adjW.isNone then adjW := some w
        match adjW, partW with
        | some a, some p => return some (capitalize a ++ capitalize p ++ "Spec")
        | _, _ => return none
      if let some parentName := parentName? then
        let curEnv ← getEnv
        let parentFull := ns ++ Name.mkSimple parentName
        if (curEnv.find? parentFull).isSome then
          if let some psi := Lean.getStructureInfo? curEnv parentFull then
            if let some storeField := psi.fieldNames[0]? then
              if let some pi := curEnv.find? (parentFull ++ storeField) then
                -- explicit argument domains of the parent's store
                -- projection: [self, key..., answer-class, time?]
                let doms ← liftTermElabM <|
                  Lean.Meta.forallTelescope pi.type fun args _ => do
                    let mut acc : Array String := #[]
                    for a in args do
                      if (← a.fvarId!.getBinderInfo) == .default then
                        let d ← Lean.Meta.inferType a
                        let stx ← Lean.PrettyPrinter.delab d
                        acc := acc.push (← ppTerm stx).pretty
                    return acc
                if doms.size >= 4 then
                  let hasTime := doms.back? == some "UInt32"
                  let coreEnd := if hasTime then doms.size - 1 else doms.size
                  let key := doms.extract 1 (coreEnd - 1)
                  let keyStr := " → ".intercalate key.toList
                  let timePart := if hasTime then "UInt32 → " else ""
                  -- the storage passive inside the "with" transform:
                  -- participle governing a "in the cache" PP
                  let storedPart? : Option String := Id.run do
                    for k in [:toks.size] do
                      if (toks[k]!.pos == .verb || toks[k]!.pos == .adj) &&
                          toks[k]!.word.endsWith "ed" then
                        if let some (pp, _) := NLP.parsePP toks (k + 1) then
                          if pp.prep == "in" && pp.np.head == "cache" then
                            return some toks[k]!.word
                    return none
                  if let some storedPart := storedPart? then
                    let storeObj := toCamelCase
                      (objWords.filter (fun w => !w.endsWith "ed"))
                    let storeM := participleStem storedPart ++ capitalize storeObj
                    let serveM := targetCamel
                    let clsName := capitalize
                        ((gWords.pop.filter (fun w => !w.endsWith "ed")).toList.headD "negative")
                      ++ capitalize (targetWords.headD "authority") ++ "Spec"
                    if (curEnv.find? (ns ++ Name.mkSimple clsName)).isNone &&
                        storeM != serveM then
                      elabCommandStr
                        (s!"class {clsName} (C RR : Type) extends {parentName} C where\n" ++
                         s!"  {storeM} : C → {keyStr} → RR → {timePart}C\n" ++
                         s!"  {serveM} : C → {keyStr} → {timePart}Array RR")
                      let clsFull := ns ++ Name.mkSimple clsName
                      addDocStringCore clsFull
                        (s!"Authority companion to `{parentName}` (the when-clause's " ++
                         s!"\"cached negative response\" anaphor): the `{storeObj}` is " ++
                         s!"stored with the negative entry and served back in the " ++
                         s!"`{serveM}` for the same key, `{transformName}`. Derived " ++
                         s!"from: \"{sentence}\"")
                      addDocStringCore (clsFull ++ Name.mkSimple storeM)
                        (s!"\"... the amount of time it was {storedPart} in the cache\" " ++
                         s!"— the record enters the cache keyed like the parent's " ++
                         s!"negative entry.")
                      addDocStringCore (clsFull ++ Name.mkSimple serveM)
                        (s!"\"{mainVerb} the {storeObj} to the {targetCamel} ... " ++
                         s!"{transformName}\" — the served target collection for the key.")
                      matchObSrcs := matchObSrcs.push (clsFull, s!"must {mainVerb} the")
    -- Insensitive-comparison rule (RFC 1035 §3.1): "… must compare
    -- ⟨objects⟩ in a ⟨X⟩-insensitive manner (i.e., A=a), assuming ASCII …
    -- Non-⟨alphabetic⟩ codes must match exactly." Three props, all from
    -- the parse:
    --  • the manner-PP frame (verb "compare" + PP "in a ⟨X⟩-insensitive
    --    manner"; the folded dimension X is the hyphenated adjective's
    --    first segment) → comparison cannot distinguish values identified
    --    by an abstract fold⟨X⟩;
    --  • the "i.e."-marked ⟨A⟩=⟨a⟩ example (two single-letter tokens
    --    differing only in case, "=" between them, ASCII sanctioned in the
    --    same sentence) → the comparison identifies that byte pair;
    --  • the exactness sentence (negated-adjective plural subject headed
    --    "codes" + MUST + verb "match" + adverb "exactly") → outside the
    --    ⟨alphabetic⟩ range the byte comparison is exact equality.
    let mut insensDone := false
    for sentence in Property.splitSentences prose do
      if insensDone then break
      let toksL := NLP.tagPOS (NLP.tokenize sentence.toLower)
      let mut vIdx? : Option Nat := none
      for i in [:toksL.size] do
        if vIdx?.isNone && toksL[i]!.pos == .verb
            && (toksL[i]!.word == "compare" || toksL[i]!.word == "compared") then
          vIdx? := some i
      let some vIdx := vIdx? | continue
      let some (_, afterObj) := NLP.parseNP toksL (vIdx + 1) (absorbPP := false)
        | continue
      let (pps, _) := NLP.parsePPs toksL afterObj
      let mut dim? : Option String := none
      for pp in pps do
        if dim?.isNone && pp.prep == "in" && pp.np.head == "manner" then
          for adjw in pp.np.preAdjs do
            if dim?.isNone && adjw.endsWith "-insensitive" then
              dim? := some ((adjw.splitOn "-").headD "x")
      let some x := dim? | continue
      insensDone := true
      let xc := capitalize x
      -- (1) fold-invariance of the comparison, over an abstract carrier
      let defShort := s!"{structName.toLower}_compare_{x}insensitive"
      let dName := mkIdent (Name.mkSimple defShort)
      let alphaId := mkIdent (Name.mkSimple "α")
      let cmpId := mkIdent (Name.mkSimple "compare")
      let foldId := mkIdent (Name.mkSimple s!"fold{xc}")
      let aId := mkIdent (Name.mkSimple "a")
      let bId := mkIdent (Name.mkSimple "b")
      elabCommand (← `(def $dName ($alphaId : Type)
          ($cmpId : $alphaId → $alphaId → Bool)
          ($foldId : $alphaId → $alphaId) : Prop :=
        ∀ ($aId $bId : $alphaId), $foldId $aId = $foldId $bId →
          $cmpId $aId $bId = true))
      let fullName := ns ++ Name.mkSimple defShort
      addDocStringCore fullName
        (s!"A {x}-insensitive comparison cannot distinguish values " ++
         s!"identified by `fold{xc}`: values equal up to {x} compare equal. " ++
         s!"Derived from the manner-PP frame of \"{sentence}\"")
      matchObSrcs := matchObSrcs.push (fullName, s!"{x}-insensitive manner")
      -- (2) the "i.e." example pins the byte-level comparison: scan the
      -- ORIGINAL-case sentence for ⟨upper⟩=⟨lower⟩ after an "i.e." marker,
      -- with ASCII mentioned (sanctioning the numeric codes)
      let toksO := NLP.tagPOS (NLP.tokenize sentence)
      let hasAscii := toksO.any fun t => t.word.toLower == "ascii"
      let mut ieIdx? : Option Nat := none
      for j in [:toksO.size] do
        if ieIdx?.isNone && toksO[j]!.word.toLower == "i.e." then
          ieIdx? := some j
      if hasAscii then
        if let some ieIdx := ieIdx? then
          for j in [ieIdx:toksO.size] do
            if j ≥ 1 && j + 1 < toksO.size && toksO[j]!.word == "=" then
              let l := toksO[j - 1]!.word
              let r := toksO[j + 1]!.word
              if l.length == 1 && r.length == 1 && l != r
                  && l.toLower == r.toLower
                  && l.toList.all Char.isAlpha && r.toList.all Char.isAlpha then
                let exShort := s!"{structName.toLower}_compare_example"
                let exName := mkIdent (Name.mkSimple exShort)
                let lLit : TSyntax `term :=
                  ⟨Syntax.mkNumLit (toString (l.toList.headD 'A').toNat)⟩
                let rLit : TSyntax `term :=
                  ⟨Syntax.mkNumLit (toString (r.toList.headD 'a').toNat)⟩
                elabCommand (← `(def $exName
                    ($cmpId : UInt8 → UInt8 → Bool) : Prop :=
                  $cmpId $lLit $rLit = true))
                addDocStringCore (ns ++ Name.mkSimple exShort)
                  (s!"The example pair \"{l}={r}\" (ASCII codes, sanctioned " ++
                   s!"by \"assuming ASCII\" in the same sentence): the byte " ++
                   "comparison identifies the pair.")
                matchObSrcs := matchObSrcs.push
                  (ns ++ Name.mkSimple exShort, s!"{l}={r}")
                break
      -- (3) exactness sentence elsewhere in the block: "Non-⟨pred⟩ codes
      -- must match exactly."
      for sentence2 in Property.splitSentences prose do
        let toks2 := NLP.tagPOS (NLP.tokenize sentence2.toLower)
        let some (np, afterNP) := NLP.parseNP toks2 0 (absorbPP := false)
          | continue
        if (np.head != "codes" && np.head != "code") || np.number != .plural then
          continue
        let some pred := np.preAdjs.findSome? (fun w =>
          if w.startsWith "non-" then some ((w.drop 4).toString) else none)
          | continue
        let rest := toks2.extract afterNP toks2.size
        let hasMust := rest.any (·.word == "must")
        let hasMatch := rest.any fun t => t.pos == .verb && t.word == "match"
        let hasExactly := rest.any fun t => t.pos == .adv && t.word == "exactly"
        if hasMust && hasMatch && hasExactly then
          let exaShort := s!"{structName.toLower}_non{pred}_match_exactly"
          let exaName := mkIdent (Name.mkSimple exaShort)
          let predId := mkIdent (Name.mkSimple pred)
          elabCommand (← `(def $exaName
              ($cmpId : UInt8 → UInt8 → Bool)
              ($predId : UInt8 → Bool) : Prop :=
            ∀ ($aId $bId : UInt8), $predId $aId = false → $predId $bId = false →
              $cmpId $aId $bId = ($aId == $bId)))
          addDocStringCore (ns ++ Name.mkSimple exaShort)
            (s!"Outside the {pred} range the byte comparison is exact " ++
             s!"equality (\"{sentence2}\").")
          matchObSrcs := matchObSrcs.push
            (ns ++ Name.mkSimple exaShort, "match exactly")
          break
    let env ← getEnv
    -- Minimum-of-two-fields derivation (RFC 2308 §3: "The TTL of this record
    -- is set from the minimum of the MINIMUM field of the SOA record and the
    -- TTL of the SOA itself, and indicates how long a resolver may cache the
    -- negative answer"): the negative TTL computation is an abstract function
    -- constrained to the min of the resolved field and the record's TTL.
    if hasSub prose.toLower "minimum of the " && hasSub prose.toLower " field of the "
        && hasSub prose.toLower "ttl of the " then
      let lower := prose.toLower
      let fieldWord := trimStr (((lower.splitOn "minimum of the ").getD 1 "").splitOn " field"
        |>.headD "")
      let structWord := trimStr (((lower.splitOn " field of the ").getD 1 "").splitOn " record"
        |>.headD "")
      -- Resolve the record struct anywhere under the namespace (generated
      -- RDATA structs live in nested namespaces, e.g. RData.Soa.SoaRdata)
      let findStruct (cand : String) : Option Name :=
        let direct := ns ++ Name.mkSimple cand
        if (env.find? direct).isSome then some direct
        else env.constants.fold (init := none) fun acc name _ =>
          acc <|> (if ns.isPrefixOf name
                      && name.components.getLast!.toString == cand
                      && Lean.isStructure env name then some name else none)
      let candidates := #[capitalize structWord ++ "Rdata", capitalize structWord]
      let structName? := candidates.findSome? findStruct
      if let some recStructFull := structName? then
        let hasField := match Lean.getStructureInfo? env recStructFull with
          | some si => si.fieldNames.contains (Name.mkSimple fieldWord)
          | none => false
        if hasField then
          let dName := mkIdent (Name.mkSimple s!"{structName.toLower}_negative_ttl")
          let recId := mkIdent recStructFull
          let projId := mkIdent (recStructFull ++ Name.mkSimple fieldWord)
          let negId := mkIdent (Name.mkSimple "negTtl")
          let rId := mkIdent (Name.mkSimple "r")
          let tId := mkIdent (Name.mkSimple "t")
          elabCommand (← `(def $dName ($negId : $recId → BitVec 32 → BitVec 32) : Prop :=
            ∀ ($rId : $recId) ($tId : BitVec 32),
              $negId $rId $tId = if $projId $rId ≤ $tId then $projId $rId else $tId))
          let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_negative_ttl"
          addDocStringCore fullName
            (s!"The negative-answer TTL is the minimum of {recStructFull}.{fieldWord} and " ++
             "the record's own TTL: \"The TTL of this record is set from the minimum " ++
             "of the MINIMUM field of the SOA record and the TTL of the SOA itself, " ++
             "and indicates how long a resolver may cache the negative answer.\"")
          matchObSrcs := matchObSrcs.push (fullName, "minimum of the")
    -- "X is indicated by ⟨conditions⟩" derivation (RFC 2308 §2.2: "NODATA is
    -- indicated by an answer with the RCODE set to NOERROR and no relevant
    -- answers in the answer section"): each conjunct resolves to an enum
    -- field equation ("RCODE set to ⟨ctor⟩") or an empty-section condition
    -- ("no ⟨X⟩s in the ⟨F⟩ section").
    if hasSub prose.toLower " is indicated by " then
      let lower := prose.toLower
      let pre := (lower.splitOn " is indicated by ").headD ""
      let subjWord := (pre.splitOn " " |>.filter (!·.isEmpty)).getLastD "response"
      let condText := trimStr (((lower.splitOn " is indicated by ").getD 1 "").splitOn "."
        |>.headD "")
      let contextTypes := collectContextTypes env ns
      let respId := mkIdent (Name.mkSimple "resp")
      let mut conjuncts : Array (TSyntax `term) := #[]
      for clause in condText.splitOn " and " do
        let words := clause.splitOn " " |>.filter (!·.isEmpty) |>.toArray
        -- "set to ⟨ctor⟩": enum constructor after "set to"
        if hasSub clause "set to " then
          let ctorWord := trimStr (((clause.splitOn "set to ").getD 1 "").splitOn " "
            |>.headD "")
          if let some (indName, ctor) := resolveNPToEnumCtor #[ctorWord] env contextTypes then
            if let some chain := traceFieldChain env indName contextTypes then
              if chain[0]!.1.components.getLast!.toString == "Format" then
                let mut acc : TSyntax `term := respId
                for (sn, fn) in chain.map (fun (t, f) =>
                    (t.components.getLast!.toString, f.toString)) do
                  let pId := mkIdent (Name.mkSimple sn ++ Name.mkSimple fn)
                  acc ← `($pId $acc)
                let ctorId := mkIdent (Name.mkSimple (indName.components.getLast!.toString)
                  ++ Name.mkSimple (ctor.components.getLast!.toString))
                conjuncts := conjuncts.push (← `($acc = $ctorId))
        -- "no ⟨X⟩s ...": stem resolves to an Array field of Format → size = 0
        else if words.contains "no" then
          let fmtName := ns ++ Name.mkSimple "Format"
          if let some si := Lean.getStructureInfo? env fmtName then
            for w in words do
              let stem := stripPlural w
              if si.fieldNames.contains (Name.mkSimple stem) then
                let pId := mkIdent (Name.mkSimple "Format" ++ Name.mkSimple stem)
                conjuncts := conjuncts.push (← `(($pId $respId).size = 0))
                break
      if conjuncts.size >= 2 then
        let dName := mkIdent (Name.mkSimple s!"{subjWord}_indicated")
        let fmtId := mkIdent (Name.mkSimple "Format")
        let mut body := conjuncts[0]!
        for i in [1:conjuncts.size] do
          body ← `($body ∧ $(conjuncts[i]!))
        elabCommand (← `(def $dName ($respId : $fmtId) : Prop := $body))
        let fullName := ns ++ Name.mkSimple s!"{subjWord}_indicated"
        addDocStringCore fullName
          s!"{subjWord.toUpper} detection, derived from \"{subjWord} is indicated by {condText}\""
        matchObSrcs := matchObSrcs.push (fullName, "is indicated by")
    -- "⟨np⟩ is ⟨participle⟩ and the state should be altered to prevent its
    -- ⟨nominalization⟩ again ..." (RFC 1035 §7.2 server selection): after
    -- the triggering event, the nominalized action's predicate is false for
    -- the anaphor's referent ("its" → the event's subject). The "until all
    -- other addresses have been tried" qualifier is the implementation's
    -- escape: a reset (retry cycle) may make it selectable again.
    if hasSub prose.toLower "prevent " && hasSub prose.toLower " again" then
      let mut preventSentence? : Option String := none
      for sentence in Property.splitSentences prose do
        let lowerS := sentence.toLower
        if hasSub lowerS "prevent " && hasSub lowerS " again" then
          preventSentence? := some lowerS
      if let some lowerS := preventSentence? then
        let tokens := NLP.tagPOS (NLP.tokenize lowerS)
        -- "prevent ⟨possessive-anaphor⟩ ⟨noun⟩": the prevented action
        let mut prevented? : Option String := none
        for i in [:tokens.size] do
          if tokens[i]!.word == "prevent" && i + 2 < tokens.size then
            let poss := tokens[i + 1]!.word
            if poss == "its" || poss == "their" then
              let nounTok := tokens[i + 2]!
              if nounTok.pos == .noun || nounTok.pos == .nounPlural then
                prevented? := some nounTok.word
        -- the triggering event: an svPassive clause in the sentence
        -- ("an address is chosen" → subject + participle)
        let mut event? : Option (String × String) := none
        for clause in NLP.parseClauses tokens do
          if let .svPassive subj participle _ negated := clause then
            if !negated && event?.isNone then
              event? := some (subj.head, participle)
        match prevented?, event? with
        | some prevented, some (evSubj, evPart) =>
          let evName := evSubj ++ capitalize evPart
          let defShort := s!"{structName.toLower}_prevent_{prevented}"
          let dName := mkIdent (Name.mkSimple defShort)
          let sigmaId := mkIdent (Name.mkSimple "σ")
          let aId := mkIdent (Name.mkSimple "A")
          let evId := mkIdent (Name.mkSimple evName)
          let prevId := mkIdent (Name.mkSimple prevented)
          let sId := mkIdent (Name.mkSimple "s")
          let sId' := mkIdent (Name.mkSimple "s'")
          let xId := mkIdent (Name.mkSimple "a")
          elabCommand (← `(def $dName ($sigmaId $aId : Type)
              ($evId : $sigmaId → $aId → $sigmaId → Prop)
              ($prevId : $sigmaId → $aId → Bool) : Prop :=
            ∀ ($sId : $sigmaId) ($xId : $aId) ($sId' : $sigmaId),
              $evId $sId $xId $sId' → $prevId $sId' $xId = false))
          let fullName := ns ++ Name.mkSimple defShort
          addDocStringCore fullName
            (s!"After `{evName}` (the event yielding the new state), " ++
             s!"`{prevented}` of the same item is prevented. " ++
             s!"Derived from \"{lowerS}\"")
          matchObSrcs := matchObSrcs.push (fullName, "prevent its selection")
        | _, _ => pure ()
    -- Tuple-key rule (RFC 2308 §5): a modal passive "should be cached such
    -- that it can be retrieved and returned ... for the same ⟨TUPLE⟩".
    -- The tuple "<QNAME, QCLASS>" is one lexical token (notation, like a
    -- numeral); the keyed PP is found grammatically (prep "for" + NP with
    -- "same" premodifier and a tuple-token head); the negative-answer
    -- class is the enum-resolvable NP governed by "from" in the subject's
    -- relative clause ("resulted from a name error" → Rcode.nameError).
    -- Tuple components map to the Question struct's fields; the entry is
    -- retrievable for ANY value of the OMITTED fields — rendered as
    -- invariance of an abstract retrieve function in those fields
    -- (NXDOMAIN's <QNAME, QCLASS> omits QTYPE → qtype-invariance). A
    -- tuple naming every field (NODATA) yields no invariance: skipped.
    if hasSub prose "<" then
      let tupContextTypes := collectContextTypes env ns
      -- Aggregated across the keyed sentences, for the class generation
      -- after the loop: tuple-field union, resolved answer enum, the
      -- subject's premodifier, and the store/retrieve participle pair.
      let mut negKeyComps : Array String := #[]
      let mut negEnumName : Option Name := none
      let mut negSubjAdj : Option String := none
      let mut negOps : Option (String × String) := none
      let mut negSrcs : Array String := #[]
      for sentence in Property.splitSentences prose do
        let tokens := NLP.tagPOS (NLP.tokenize sentence.toLower)
        let hasVerb := fun (w : String) =>
          tokens.any fun t => t.pos == .verb && t.word == w
        if hasVerb "cached" && hasVerb "retrieved" then
          -- keyed PP: "for ⟨the same TUPLE⟩"
          let tuple? : Option String := Id.run do
            for k in [:tokens.size] do
              if tokens[k]!.pos == .prep && tokens[k]!.word == "for" then
                if let some (pp, _) := NLP.parsePP tokens k then
                  if (pp.np.preAdjs.contains "same" || pp.np.det == some "same")
                      && pp.np.head.startsWith "<" then
                    return some pp.np.head
            return none
          -- answer class: enum-resolvable NP after "from"
          let ctor? : Option Name := Id.run do
            for k in [:tokens.size] do
              if tokens[k]!.pos == .prep && tokens[k]!.word == "from" then
                if let some (np, _) := NLP.parseNP tokens (k + 1) then
                  let words := np.preAdjs.push np.head
                  if let some (_, c) := resolveNPToEnumCtor words env tupContextTypes then
                    return some c
                  for w in [:words.size - 1] do
                    if let some (_, c) := resolveNPToEnumCtor #[words[w]!, words[w + 1]!]
                        env tupContextTypes then
                      return some c
            return none
          -- Collect class-generation evidence from every keyed sentence
          if let some tup := tuple? then
            let tupText := String.ofList
              (tup.toList.filter (fun c => c != '<' && c != '>'))
            for comp in (tupText.splitOn ",").map trimStr do
              if !comp.isEmpty && !negKeyComps.contains comp then
                negKeyComps := negKeyComps.push comp
            negSrcs := negSrcs.push sentence
            -- subject premodifier ("a NEGATIVE answer ... should be cached")
            if negSubjAdj.isNone then
              if let some (np, _) := NLP.parseNP tokens 0 then
                negSubjAdj := np.preAdjs[0]?
            -- the operation pair: passive participles after "be" — main
            -- clause ("should be CACHED") = store, complement ("can be
            -- RETRIEVED and returned") = retrieve (first coordinate)
            if negOps.isNone then
              let mut parts : Array String := #[]
              for k in [:tokens.size] do
                if tokens[k]!.word == "be" && k + 1 < tokens.size &&
                    tokens[k + 1]!.pos == .verb then
                  parts := parts.push tokens[k + 1]!.word
              if let (some p0, some p1) := (parts[0]?, parts[1]?) then
                negOps := some (p0, p1)
          if negEnumName.isNone then
            if let some ctor := ctor? then
              negEnumName := some ctor.getPrefix
          match tuple?, ctor? with
          | some tup, some ctor =>
            let marker := ctor.components.getLast!.toString
            let tupleText := String.ofList
              (tup.toList.filter (fun c => c != '<' && c != '>'))
            let comps := (tupleText.splitOn ",").map trimStr |>.filter (!·.isEmpty)
            let qStructName := ns ++ Name.mkSimple "Question"
            if let some si := Lean.getStructureInfo? env qStructName then
              let fields := si.fieldNames
              let omitted := fields.filter
                (fun f => !comps.any (fun c => c == f.toString.toLower))
              if !omitted.isEmpty then
                -- field types from the struct projections
                let mut fieldData : Array (Name × TSyntax `term) := #[]
                let mut ok := true
                for f in fields do
                  match env.find? (qStructName ++ f) with
                  | some projInfo =>
                    match projInfo.type with
                    | .forallE _ _ fbody _ =>
                      let tyStx ← liftTermElabM (Lean.PrettyPrinter.delab fbody)
                      fieldData := fieldData.push (f, tyStx)
                    | _ => ok := false
                  | none => ok := false
                if ok then
                  let sigmaId := mkIdent (Name.mkSimple "σ")
                  let rhoId := mkIdent (Name.mkSimple "ρ")
                  let retId := mkIdent (Name.mkSimple "retrieve")
                  let sId := mkIdent (Name.mkSimple "s")
                  let mut fnType : TSyntax `term ← `($rhoId)
                  for (_, ty) in fieldData.reverse do
                    fnType ← `($ty → $fnType)
                  fnType ← `($sigmaId → $fnType)
                  let mut app1 : TSyntax `term ← `($retId $sId)
                  let mut app2 : TSyntax `term ← `($retId $sId)
                  let mut foralls : Array (Ident × TSyntax `term) :=
                    #[(sId, ← `($sigmaId))]
                  for (f, ty) in fieldData do
                    let x := mkIdent (Name.mkSimple f.toString)
                    if omitted.contains f then
                      let x' := mkIdent (Name.mkSimple (f.toString ++ "'"))
                      foralls := foralls.push (x, ty) |>.push (x', ty)
                      app1 ← `($app1 $x)
                      app2 ← `($app2 $x')
                    else
                      foralls := foralls.push (x, ty)
                      app1 ← `($app1 $x)
                      app2 ← `($app2 $x)
                  let mut obBody : TSyntax `term ← `($app1 = $app2)
                  for (x, ty) in foralls.reverse do
                    obBody ← `(∀ ($x : $ty), $obBody)
                  let defShort := s!"{structName.toLower}_{marker}_retrieval"
                  let dName := mkIdent (Name.mkSimple defShort)
                  elabCommand (← `(def $dName ($sigmaId $rhoId : Type)
                      ($retId : $fnType) : Prop := $obBody))
                  let fullName := ns ++ Name.mkSimple defShort
                  let omittedStr := ", ".intercalate
                    (omitted.toList.map (·.toString))
                  addDocStringCore fullName
                    (s!"{marker.toUpper} retrieval is keyed by <{tupleText}> only: " ++
                     s!"invariant in the omitted question field(s) {omittedStr}. " ++
                     s!"Derived from \"{sentence}\"")
                  matchObSrcs := matchObSrcs.push (fullName, "for the same <")
          | _, _ => pure ()
      -- Negative-cache operations: the keyed cached/retrieved frame
      -- generates a store/retrieve typeclass. The store key is the UNION
      -- of the tuple fields across the keyed sentences (NXDOMAIN names
      -- ⟨QNAME, QCLASS⟩, NODATA ⟨QNAME, QTYPE, QCLASS⟩ — the store must
      -- carry the full key; the NXDOMAIN retrieval ignores QTYPE via the
      -- invariance prop above). The answer class is the enum resolved from
      -- the subject's relative clause ("resulted from a name error" →
      -- Rcode); retrieval is partial — only "another query ... that
      -- resulted in the cached negative response" hits. The TTL-countdown
      -- sentence ("This TTL decrements ... upon reaching zero (0) ...
      -- MUST NOT be used again") adds the absolute-time argument (the
      -- §5.3.2 storeAt convention).
      if !negKeyComps.isEmpty then
        if let some enumFull := negEnumName then
        if let some (storePart, retrPart) := negOps then
          let adj := (negSubjAdj.getD "negative").toLower
          let hasCountdown := Id.run do
            for sentence in Property.splitSentences prose do
              let toks := NLP.tagPOS (NLP.tokenize sentence.toLower)
              for i in [:toks.size] do
                if i + 1 < toks.size && toks[i]!.word == "ttl" &&
                    stripVerbInflection toks[i + 1]!.word == "decrement" then
                  return true
            return false
          let qStructName := ns ++ Name.mkSimple "Question"
          if let some si := Lean.getStructureInfo? env qStructName then
            let keyFields := si.fieldNames.filter fun f =>
              negKeyComps.any (fun c => c.toLower == f.toString.toLower)
            if keyFields.size == negKeyComps.size then
              let mut keyTypeStrs : Array String := #[]
              let mut ok := true
              for f in keyFields do
                match env.find? (qStructName ++ f) with
                | some projInfo =>
                  match projInfo.type with
                  | .forallE _ _ fbody _ =>
                    let tyStx ← liftTermElabM (Lean.PrettyPrinter.delab fbody)
                    keyTypeStrs := keyTypeStrs.push (← liftCoreM (ppTerm tyStx)).pretty
                  | _ => ok := false
                | none => ok := false
              if ok then
                let enumStr := (enumFull.replacePrefix ns Name.anonymous).toString
                let keyStr := " → ".intercalate keyTypeStrs.toList
                let timePart := if hasCountdown then "UInt32 → " else ""
                let storeM := participleStem storePart ++ capitalize adj
                let retrM := participleStem retrPart ++ capitalize adj
                let className := capitalize adj ++
                  capitalize (participleStem storePart) ++ "Spec"
                if (env.find? (ns ++ Name.mkSimple className)).isNone then
                  let storeSig := s!"C → {keyStr} → {enumStr} → {timePart}C"
                  let retrSig := s!"C → {keyStr} → {timePart}Option {enumStr}"
                  elabCommandStr (mkClassString className #["C"]
                    #[storeM, retrM] #[storeSig, retrSig])
                  let classFull := ns ++ Name.mkSimple className
                  let sanitize (s : String) : String := String.ofList
                    (s.toList.map fun c =>
                      if c == '<' then '⟨' else if c == '>' then '⟩' else c)
                  let srcsStr := " / ".intercalate
                    (negSrcs.toList.map (fun s => "\"" ++ sanitize s ++ "\""))
                  addDocStringCore classFull
                    (s!"Negative-cache store/retrieve operations, keyed by the " ++
                     s!"union of the tuple fields across the keyed sentences, " ++
                     s!"parameterized by the resolved answer class `{enumStr}`" ++
                     (if hasCountdown then
                       ", with an absolute-time argument from the TTL-countdown sentence"
                      else "") ++ s!". Derived from {srcsStr}")
                  addDocStringCore (classFull ++ Name.mkSimple storeM)
                    (s!"\"should be {storePart} such that it can be {retrPart} " ++
                     s!"and returned\" — the store side, keyed by the full union " ++
                     s!"key, tagged with the `{enumStr}` answer class.")
                  addDocStringCore (classFull ++ Name.mkSimple retrM)
                    (s!"The retrieve side — partial: only a query for the same " ++
                     s!"key \"that resulted in the {adj} response\" hits.")
                  matchObSrcs := matchObSrcs.push (classFull, "for the same <")
    -- "either ⟨discard ...⟩, or limit all TTLs in the response to ⟨duration⟩"
    -- (RFC 1035 §7.3 TTL sanity). The sentence sanctions two behaviors;
    -- both are captured by one Option-valued process: a discarded response
    -- (none) is unconstrained, a kept response has every parsed RR's TTL
    -- bounded by the duration. The or-arm is an imperative — parsed with
    -- the same imperative-clause parser as the step-1 conditional — and the
    -- duration is read from a numeral + time-unit noun pair.
    if hasSub prose.toLower "either " && hasSub prose.toLower " or " then
      let mut limitSentence? : Option String := none
      for sentence in Property.splitSentences prose do
        let lowerS := sentence.toLower
        if hasSub lowerS "either " && hasSub lowerS " or " then
          limitSentence? := some lowerS
      if let some lowerS := limitSentence? then
        let orArm := trimStr ((lowerS.splitOn " or ").getLastD "")
        let armTokens := NLP.tagPOS (NLP.tokenize orArm)
        let dummyNP : NLP.NounPhrase := ⟨none, #[], "", .unknown, #[]⟩
        if let some (.svo _ vp obj _) := NLP.parseImperativeClause armTokens dummyNP then
          -- duration: numeral followed by a time-unit noun
          let unitSeconds := fun (u : String) =>
            if u.startsWith "week" then some 604800
            else if u.startsWith "day" then some 86400
            else if u.startsWith "hour" then some 3600
            else if u.startsWith "minute" then some 60
            else if u.startsWith "second" then some 1
            else none
          let mut secs? : Option Nat := none
          for i in [:armTokens.size] do
            if i + 1 < armTokens.size then
              let w := armTokens[i]!.word
              if !w.isEmpty && w.toList.all Char.isDigit then
                if let some m := unitSeconds armTokens[i + 1]!.word.toLower then
                  secs? := some ((w.toNat?).getD 1 * m)
          match secs? with
          | some secs =>
            if (vp.verb == "limit" || vp.verb == "restrict")
                && stripPlural obj.head.toLower == "ttl" then
              -- "in the response": every Array ByteArray section of Format
              let fmtName := ns ++ Name.mkSimple "Format"
              let mut sectionFields : Array Name := #[]
              if let some si := Lean.getStructureInfo? env fmtName then
                for fn in si.fieldNames do
                  if let some projInfo := env.find? (fmtName ++ fn) then
                    match projInfo.type with
                    | .forallE _ _ body _ =>
                      if body.isAppOfArity ``Array 1
                          && body.appArg!.isConstOf ``ByteArray then
                        sectionFields := sectionFields.push fn
                    | _ => pure ()
              let respId := mkIdent (Name.mkSimple "resp")
              let respId' := mkIdent (Name.mkSimple "resp'")
              let bytesId := mkIdent (Name.mkSimple "bytes")
              let mut memDisj? : Option (TSyntax `term) := none
              for fn in sectionFields do
                let pId := mkIdent (Name.mkSimple "Format" ++ fn)
                let t ← `($bytesId ∈ $pId $respId')
                memDisj? := some (← match memDisj? with
                  | none => pure t
                  | some a => `($a ∨ $t))
              if let some memDisj := memDisj? then
                let dName := mkIdent (Name.mkSimple s!"{structName.toLower}_limit_ttls")
                let rrTyId := mkIdent (Name.mkSimple "RR")
                let parseId := mkIdent (Name.mkSimple "parse")
                let ttlOfId := mkIdent (Name.mkSimple "ttlOf")
                let processId := mkIdent (Name.mkSimple "process")
                let fmtId := mkIdent (Name.mkSimple "Format")
                let rrId := mkIdent (Name.mkSimple "rr")
                let secLit : TSyntax `term := ⟨Syntax.mkNumLit (toString secs)⟩
                elabCommand (← `(def $dName ($rrTyId : Type)
                    ($parseId : ByteArray → Option $rrTyId)
                    ($ttlOfId : $rrTyId → Nat)
                    ($processId : $fmtId → Option $fmtId) : Prop :=
                  ∀ ($respId $respId' : $fmtId), $processId $respId = some $respId' →
                    ∀ ($bytesId : ByteArray), $memDisj →
                      ∀ ($rrId : $rrTyId), $parseId $bytesId = some $rrId →
                        $ttlOfId $rrId ≤ $secLit))
                let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_limit_ttls"
                addDocStringCore fullName
                  (s!"TTL sanity (bound: {secs} seconds): a processed response is either " ++
                   s!"discarded (none) or every RR it carries has TTL ≤ {secs}. " ++
                   s!"Derived from \"{orArm}\" (either/or sentence).")
                matchObSrcs := matchObSrcs.push (fullName, "limit all ttls")
          | none => pure ()
    let rules := proseClauseRuleExt.getState env
    -- Match clauses against rules, accumulate bindings and results
    let mut allBindings : Std.HashMap String (Nat ⊕ String) := {}
    let mut ruleStructFields : Array (String × Nat) := #[]
    let mut matchedSpecs : Array (PropSpec × Std.HashMap String (Nat ⊕ String) × String) := #[]
    for (clause, src) in clausesWithSrc do
      for rule in rules do
        if let some bindings := matchProseClausePattern clause rule.pattern then
          -- Merge bindings into shared pool
          for (k, v) in bindings do
            allBindings := allBindings.insert k v
          matchedSpecs := matchedSpecs.push (rule.output, bindings, src)
    -- Share bindings across rules (e.g., "threshold" alias for "value")
    -- bit_set_implies needs "threshold" which comes from size_bound's "value"
    if allBindings.contains "value" && !allBindings.contains "threshold" then
      if let some v := allBindings.get? "value" then
        allBindings := allBindings.insert "threshold" v
    -- Process matched specs to collect struct fields
    for (spec, _, _) in matchedSpecs do
      ruleStructFields := ruleStructFields ++ collectDeclFields spec allBindings
    -- Dedup by field name (keep first occurrence)
    let mut seenFieldNames : Array String := #[]
    let mut dedupedFields : Array (String × Nat) := #[]
    for (name, bits) in ruleStructFields do
      unless seenFieldNames.contains name do
        seenFieldNames := seenFieldNames.push name
        dedupedFields := dedupedFields.push (name, bits)
    ruleStructFields := dedupedFields
    -- Determine if any rules matched
    let hasMeaningfulProps := !matchedSpecs.isEmpty
    -- Build final struct fields: rule-derived fields + NLP-derived + default data field
    let mut allStructFields : Array MergedField := #[]
    for (name, bits) in ruleStructFields do
      allStructFields := allStructFields.push ⟨name, some bits, false, "", #[], none, none, false⟩
    if !structFieldsRaw.isEmpty then
      for (name, isArr) in structFieldsRaw do
        allStructFields := allStructFields.push ⟨name, none, true, "", #[], none, none, isArr⟩
    else if hasMeaningfulProps then
      -- Default data field for transport-style sections
      allStructFields := allStructFields.push ⟨"data", none, true, "", #[], none, none, false⟩
    if !allStructFields.isEmpty then
      let sectionHeader := extractSectionHeader text |>.getD ""
      generateStructure structName sectionHeader allStructFields
      -- Generate Props from matched specs via unified interpreter
      let structIdent := mkIdent (Name.mkSimple structName)
      let ctx : ProseInterpContext := { structName, structIdent, ns }
      let mut propIdx : Nat := 0
      let mut propSrcs : Array (Name × String) := matchObSrcs
      for (spec, localBindings, src) in matchedSpecs do
        -- Merge local bindings with shared bindings (local takes precedence for its own extractions)
        let mut merged := allBindings
        for (k, v) in localBindings do
          merged := merged.insert k v
        -- Check if any NLP-derived field is an array (element-level bound for size_bound)
        let matchingArrayField := structFieldsRaw.find? fun (_, isArr) => isArr
        let finalSpec := match matchingArrayField with
          | some (fieldName, _) =>
            -- If spec is a simple size bound, wrap in forallElem for array fields
            match spec with
            | .forallStruct (.le (.size _) _) =>
              .forallStruct (.forallElem (.namedField fieldName)
                (.le (.size (.bound 0)) (extractBoundRef spec merged)))
            | _ => spec
          | none => spec
        -- Skip purely trivial specs (True, ∀ _ True, ¬ True)
        if isPurelyTrivial finalSpec then continue
        let result ← interpretPropSpecForProse finalSpec ctx #[] merged
        -- Emit prop defs
        for propTerm in result.propTerms do
          let propName := mkIdent (Name.mkSimple s!"{structName.toLower}_prop_{propIdx}")
          elabCommand (← `(def $propName : Prop := $propTerm))
          let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_prop_{propIdx}"
          let fmt ← liftCoreM (ppTerm propTerm)
          addDocStringCore fullName s!"{structName}: prop {propIdx}\n```lean\n{fmt.pretty}\n```"
          propSrcs := propSrcs.push (fullName, src)
          propIdx := propIdx + 1
      -- Discard-unrequested derivation (RFC 1035 §7.4: "When a resolver
      -- receives unsolicited responses or RR data other than that requested,
      -- it should discard it without caching it"): data that was not
      -- requested must not be cached, over abstract requested/cached
      -- predicates (the Spec cannot know what was asked or stored).
      if hasSub prose "other than that requested" && hasSub prose "without caching" then
        let dName := mkIdent (Name.mkSimple s!"{structName.toLower}_discard_unrequested")
        let rhoId := mkIdent (Name.mkSimple "ρ")
        let rId := mkIdent (Name.mkSimple "r")
        let reqId := mkIdent (Name.mkSimple "requested")
        let cachedId := mkIdent (Name.mkSimple "cached")
        elabCommand (← `(def $dName ($rhoId : Type)
          ($reqId : $rhoId → Bool) ($cachedId : $rhoId → Bool) : Prop :=
          ∀ ($rId : $rhoId), $reqId $rId = false → $cachedId $rId = false))
        let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_discard_unrequested"
        addDocStringCore fullName
          ("Unrequested data must not be cached (abstract `requested`/`cached` " ++
           "predicates): \"When a resolver receives unsolicited responses or RR " ++
           "data other than that requested, it should discard it without caching it.\"")
        propSrcs := propSrcs.push (fullName, "other than that requested")
      -- Generate numeric constants from extractConstraintValues
      let rawConstraints := extractConstraintValues prose
      for i in [:rawConstraints.size] do
        let (value, unit, srcPhrase) := rawConstraints[i]!
        let constName := mkIdent (Name.mkSimple s!"{structName.toLower}_limit_{i}")
        let constVal := Syntax.mkNumLit (toString value)
        elabCommand (← `(def $constName : Nat := $constVal))
        let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_limit_{i}"
        addDocStringCore fullName s!"{structName}: {value} {unit}"
        propSrcs := propSrcs.push (fullName, srcPhrase)
      return some (structName, allStructFields, propSrcs)
    -- Sections that yielded only a MUST-match obligation (no struct):
    -- still return it for hover support
    if !matchObSrcs.isEmpty then
      return some (structName, #[], matchObSrcs)
    -- Value-list section: generate inductive type from enumeration entries
    let valueEntries := parseValueList text
    if !valueEntries.isEmpty then
      let categoryWord := title.splitOn " " |>.head? |>.getD title
      let rawName := capitalize categoryWord.toLower
      -- Avoid Lean keyword conflicts: Type/Class → RRType/RRClass
      let enumName := if rawName == "Type" || rawName == "Class"
        then "RR" ++ rawName else rawName
      let fullName ← generateValueListType enumName valueEntries
      storeEnumDescriptions fullName valueEntries
      let sectionHeader := extractSectionHeader text |>.getD ""
      addDocStringCore fullName sectionHeader
      return some (enumName, #[], #[])
    -- Fallback: no fields derived, just extract numeric constants.
    -- Still return the limit sources so the constants are hover-reachable
    -- from the sentences that produced them (the struct-hover and sentence
    -- pushers no-op when no struct named `structName` exists).
    let rawConstraints := extractConstraintValues prose
    let mut limitSrcs : Array (Name × String) := #[]
    for i in [:rawConstraints.size] do
      let (value, unit, srcPhrase) := rawConstraints[i]!
      let constName := mkIdent (Name.mkSimple s!"{structName.toLower}_limit_{i}")
      let constVal := Syntax.mkNumLit (toString value)
      elabCommand (← `(def $constName : Nat := $constVal))
      let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_limit_{i}"
      addDocStringCore fullName s!"{structName}: max {value} {unit}"
      limitSrcs := limitSrcs.push (fullName, srcPhrase)
    if !limitSrcs.isEmpty then
      return some (structName, #[], limitSrcs)
    return none

  let merged' := mergeFields diagramFields whereFields
  -- Filter out literal bit value fields (e.g., "1  1" in pointer diagrams)
  let merged := merged'.filter fun f => !isLiteralBitValue f.name
  if merged.isEmpty then return none

  -- Generate enum types first (they're referenced by the structure)
  for f in merged do
    if f.values.size > 0 then
      if let some _ := f.enumTypeName then
        let tn ← generateEnum f.name f.values
        storeEnumDescriptions tn f.values
        -- Use-condition semantics from negated-capability descriptions
        -- (e.g. RCODE 1/4: "unable to interpret", "does not support")
        generateNegatedCapabilitySemantics tn f.values

  -- Build docstring from section header + prose
  let sectionHeader := extractSectionHeader text |>.getD ""
  let prose := extractProse text
  let docstring := if prose.isEmpty then sectionHeader
    else s!"{sectionHeader}\n\n{prose}"

  -- Generate the structure
  generateStructure structName docstring merged

  -- Generate property definitions from field descriptions
  generateProperties structName merged

  -- Store metadata for de-elaboration
  storeFieldDescriptions structName merged
  let diagramText := extractDiagramText text
  storeDiagramText structName diagramText

  -- Generate example definitions from subsequent diagrams
  if !exampleGroups.isEmpty then
    generateExampleCmd exampleGroups structName

  return some (structName, merged, #[])

-- ============================================================
-- Public API for querying RFC metadata (used by de-elaborators)
-- ============================================================

/-- Look up the RFC description for a field projection -/
def getFieldDescription (env : Environment) (fieldName : Name) : Option String :=
  (rfcFieldDescriptions.getState env)[fieldName]?

/-- Look up the RFC code and description for an enum constructor -/
def getEnumDescription (env : Environment) (ctorName : Name) : Option (Nat × String) :=
  (rfcEnumDescriptions.getState env)[ctorName]?

/-- Look up the ASCII diagram for a structure -/
def getDiagramText (env : Environment) (structName : Name) : Option String :=
  (rfcDiagramText.getState env)[structName]?

end VeriDNS.RFC.Syntax
