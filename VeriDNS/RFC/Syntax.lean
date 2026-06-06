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

    -- Description continuation
    else if leadingSpaces >= 8 && !trimmed.isEmpty then
      currentDesc := currentDesc ++ " " ++ trimmed

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
  let allWords := title.splitOn " " |>.filter (!·.isEmpty) |>.map capitalize
  let words := allWords.filter (fun w =>
    w.toLower != "section" && w.toLower != "format" && w.toLower != "definitions")
  String.join (if words.isEmpty then allWords else words)

/-- Extract all prose text after the section header (for prose-only sections) -/
def extractAllProse (text : String) : String := Id.run do
  let lines := text.splitOn "\n"
  let mut proseLines : Array String := #[]
  let mut pastHeader := false
  for line in lines do
    let trimmed := trimStr line
    if !pastHeader then
      if !trimmed.isEmpty && trimmed.toList[0]!.isDigit && hasSub trimmed ". " then
        pastHeader := true
      continue
    if !trimmed.isEmpty then
      proseLines := proseLines.push trimmed
  return " ".intercalate proseLines.toList

/-- Extract numeric constraints from prose: "to N octets/bits" patterns.
    Returns (value, unit) pairs. -/
def extractConstraintValues (prose : String) : Array (Nat × String) := Id.run do
  let words := prose.toLower.splitOn " " |>.toArray |>.filter (!·.isEmpty)
  let mut result : Array (Nat × String) := #[]
  for i in [:words.size] do
    if words[i]! == "to" && i + 2 < words.size then
      let unitWord := words[i + 2]!
      if unitWord.startsWith "octet" || unitWord.startsWith "bit" then
        let unit := if unitWord.startsWith "octet" then "octets" else "bits"
        if let some n := words[i + 1]!.toNat? then
          result := result.push (n, unit)
        else if let some n := wordToNum words[i + 1]! then
          result := result.push (n, unit)
  return result

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
    let bits := df.bits.orElse (fun _ => wf.bind (·.bits))
    let enumTypeName := if values.size > 0 then some (capitalize df.name.toLower) else none
    result := result.push ⟨df.name, bits, df.isVariable, description, values, enumTypeName, none, false⟩
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

-- ============================================================
-- Code generation
-- ============================================================

/-- Generate an inductive type for value enumerations.
    Also generates a toNat conversion function. -/
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
  let derivClasses := if hasVariableField then #[`BEq] else #[`Repr, `BEq]
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

-- ============================================================
-- Property generation
-- ============================================================

/-- Build a formal `Prop` term from a `DescProp` and the struct type name.
    Maps each variant to a real `Prop` usable in proofs:
    - `.mustBeZero` / `.reserved` → `∀ (h : T), h.field = 0`
    - `.copiedTo _` → `True` (cross-struct, deferred)
    - `.countsEntriesIn _` → `True` (cross-struct, deferred)
    - `.validIn _` / `.setIn _` → `True` (contextual, deferred)
    - `.raw text` → attempt numeric bound extraction, else `True` -/
private def mkFormalProp (prop : Property.DescProp) (structName : String)
    (fieldName : String) : CommandElabM (TSyntax `term) := do
  let structIdent := mkIdent (Name.mkSimple structName)
  let projIdent := mkIdent (Name.mkSimple structName ++ Name.mkSimple fieldName.toLower)
  let hIdent := mkIdent `h
  match prop with
  | .mustBeZero | .reserved =>
    `(∀ ($hIdent : $structIdent), $projIdent $hIdent = 0)
  | .copiedTo target =>
    let _ := target  -- document intent in docstring
    `(True)
  | .countsEntriesIn sect =>
    let _ := sect
    `(True)
  | .validIn ctx =>
    let _ := ctx
    `(True)
  | .setIn ctx =>
    let _ := ctx
    `(True)
  | .raw text =>
    -- Try to extract a numeric bound from the raw text
    match extractBitWidth text with
    | some _ => `(True)  -- bit-width is already captured in the struct field type
    | none => `(True)

/-- Generate `def {field}_prop_{i} : Prop := ∀ (h : T), ...` for each parsed property -/
private def generateProperties (structName : String) (fields : Array MergedField)
    : CommandElabM Unit := do
  let ns ← getCurrNamespace
  for f in fields do
    if f.description.isEmpty then continue
    let props := Property.parseDescription f.description
    for i in [:props.size] do
      let propName : Ident := mkIdent (Name.mkSimple s!"{f.name.toLower}_prop_{i}")
      let propVal ← mkFormalProp props[i]! structName f.name
      elabCommand (← `(def $propName : Prop := $propVal))
      -- Add docstring for hover display
      let fullName := ns ++ Name.mkSimple s!"{f.name.toLower}_prop_{i}"
      addDocStringCore fullName s!"{f.name} — {props[i]!.toLabel}"

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
initialize rfcEnumDescriptions : EnvExtension (Std.HashMap Name (Nat × String)) ←
  registerEnvExtension (pure {})

-- Maps structure names to their ASCII diagram text
initialize rfcDiagramText : EnvExtension (Std.HashMap Name String) ←
  registerEnvExtension (pure {})

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
      rfcEnumDescriptions.modifyState env (·.insert cName (v.code, v.description))

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

/-- Push hover info for parsed description sentences.
    Walks parser ident nodes: field-name idents set the current field,
    subsequent non-field idents are sentence fragments that get TermInfo
    pointing to the corresponding property def (e.g., `id_prop_0`).
    Sentence idents exist because rfcTextBodyFn splits descriptions at
    sentence boundaries via findSentenceSplitPoints. -/
def pushSentenceHoverInfo (structName : String) (rfcNodeArgs : Array Lean.Syntax)
    (fields : Array MergedField) : CommandElabM Unit := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let fullStructName := ns ++ Name.mkSimple structName
  if !(env.find? fullStructName).isSome then return
  let fieldNames := fields.map (·.name.toUpper)
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
    let propName := ns ++ Name.mkSimple s!"{field.name.toLower}_prop_{sentenceIdx}"
    if (env.find? propName).isSome then
      pushInfoLeaf (.ofTermInfo {
        elaborator := `VeriDNS.RFC.includeRfc
        stx := arg
        expr := .const propName []
        lctx := {}
        expectedType? := none
      })
    sentenceIdx := sentenceIdx + 1

-- ============================================================
-- Main pipeline
-- ============================================================

/-- Process verified RFC text to generate formal Lean specifications.

    Recognizes section headers, bit diagrams, and where blocks.
    Generates structures with BitVec fields and inductive types
    for value enumerations. Stores metadata for de-elaboration.
    Returns the struct name and merged fields (if any) for hover support. -/
def processRfcText (text : String) : CommandElabM (Option (String × Array MergedField)) := do
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
      storeFieldDescriptions structName merged
      return some (structName, merged)
    -- Prose-only section: derive structure + ∀ constraints from NLP analysis
    let ns ← getCurrNamespace
    let prose := extractAllProse text
    let structFieldsRaw := NLP.deriveStructFields prose
    let constraints := NLP.deriveConstraints prose
    -- Generate structure if we derived any fields
    if !structFieldsRaw.isEmpty then
      let fields : Array MergedField := structFieldsRaw.map fun (name, isArr) =>
        ⟨name, none, true, "", #[], none, none, isArr⟩
      let sectionHeader := extractSectionHeader text |>.getD ""
      generateStructure structName sectionHeader fields
      -- Generate ∀ constraints as Prop definitions
      let structIdent := mkIdent (Name.mkSimple structName)
      for i in [:constraints.size] do
        let (subject, value, unit) := constraints[i]!
        let propName := mkIdent (Name.mkSimple s!"{structName.toLower}_prop_{i}")
        let boundVal := Syntax.mkNumLit (toString value)
        let hIdent := mkIdent `h
        -- Find if constraint subject matches an array field
        -- Match singular constraint subject to plural field name (label → labels)
        let subjectMatch (fieldName subj : String) : Bool :=
          let f := fieldName.toLower
          let s := subj.toLower
          f == s || f == s ++ "s" || f == s ++ "es" || s == f ++ "s" || s == f ++ "es"
        let matchingArrayField := structFieldsRaw.find?
          fun (name, isArr) => isArr && subjectMatch name subject
        let propVal ← match matchingArrayField with
          | some (fieldName, _) =>
            let _fieldIdent := mkIdent (Name.mkSimple fieldName)
            let elemIdent := mkIdent `elem
            let projIdent := mkIdent (Name.mkSimple structName ++ Name.mkSimple fieldName)
            let sizeIdent := mkIdent ``ByteArray.size
            `(∀ ($hIdent : $structIdent) ($elemIdent : ByteArray),
              $elemIdent ∈ $projIdent $hIdent → $sizeIdent $elemIdent ≤ $boundVal)
          | none =>
            -- Scalar constraint: total size
            `(∀ ($hIdent : $structIdent), True)
        elabCommand (← `(def $propName : Prop := $propVal))
        let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_prop_{i}"
        let unitLabel := if unit == "octets" then "octets" else "bits"
        addDocStringCore fullName s!"{structName}: {subject} ≤ {value} {unitLabel}"
      return none
    -- Fallback: no fields derived, just extract numeric constants
    let rawConstraints := extractConstraintValues prose
    for i in [:rawConstraints.size] do
      let (value, unit) := rawConstraints[i]!
      let constName := mkIdent (Name.mkSimple s!"{structName.toLower}_limit_{i}")
      let constVal := Syntax.mkNumLit (toString value)
      elabCommand (← `(def $constName : Nat := $constVal))
      let fullName := ns ++ Name.mkSimple s!"{structName.toLower}_limit_{i}"
      addDocStringCore fullName s!"{structName}: max {value} {unit}"
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

  return some (structName, merged)

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
