/-
  The `include_rfc` command macro.

  Syntax:
    include_rfc[1035][1401:1529] {
      4.1.1. Header section format
      ...exact RFC text...
    }

  At elaboration time:
  1. Loads rfc/rfc-{number}.txt relative to the project root
  2. Extracts lines from:to (1-indexed, inclusive)
  3. Strips page break artifacts
  4. Checks the text in { } matches EXACTLY
  5. Compile error with diff on mismatch
-/
import Lean
import VeriDNS.RFC.Parser
import VeriDNS.RFC.Syntax

open Lean Elab Command Parser

namespace VeriDNS.RFC

/-- Find project root by walking up from a directory until we find lakefile.lean -/
private def findProjectRoot (dir : System.FilePath) : IO System.FilePath := do
  -- Resolve to absolute path if relative
  let cwd ← IO.currentDir
  let mut cur := if dir.toString.startsWith "/" then dir else cwd / dir
  for _ in List.range 20 do
    if ← (cur / "lakefile.lean").pathExists then return cur
    if ← (cur / "lakefile.toml").pathExists then return cur
    match cur.parent with
    | some p => cur := p
    | none => break
  throw <| IO.userError s!"Could not find project root from {dir}"

/-- Extract a substring from an InputContext between two raw positions -/
private def extractText (c : InputContext) (startPos endPos : String.Pos.Raw) : String := c.substring startPos endPos |>.toString

/-- Find byte offset ranges of field names in the where block of RFC text.
    Returns array of (byteOffset, byteLength) pairs for each uppercase field name. -/
private def findFieldSplitPoints (text : String) : Array (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut result : Array (Nat × Nat) := #[]
  let mut offset : Nat := 0
  let mut inWhere := false
  for line in lines do
    let trimmed := line.trimAscii.toString
    if trimmed == "where:" then
      inWhere := true
    else if inWhere && !trimmed.isEmpty then
      let chars := line.toList
      let spaces := chars.takeWhile (· == ' ') |>.length
      if spaces < 8 && chars.length > spaces && chars[spaces]!.isUpper then
        let nameStart := offset + spaces
        -- Find end of name (first space after uppercase chars)
        let mut nameLen := 0
        for j in [spaces:chars.length] do
          if chars[j]! == ' ' then break
          nameLen := nameLen + 1
        if nameLen > 0 then
          result := result.push (nameStart, nameLen)
    offset := offset + line.utf8ByteSize + 1
  return result

/-- Find byte offset and length of glossary entry names (ALL-CAPS followed by 2+ spaces).
    Mirrors Syntax.parseGlossaryList detection but returns positions for ident creation. -/
private def findGlossarySplitPoints (text : String) : Array (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut result : Array (Nat × Nat) := #[]
  let mut offset : Nat := 0
  for line in lines do
    let trimmed := line.trimAscii.toString
    if !trimmed.isEmpty then
      let parts := trimmed.splitOn " " |>.filter (!·.isEmpty)
      if parts.length >= 2 then
        let name := parts[0]!
        let isAllCaps := !name.isEmpty && name.toList.all (fun c => c.isUpper)
        if isAllCaps && !(parts[1]!.toNat?.isSome) then
          -- Check 2+ spaces between name and description
          let leadingSpaces := line.toList.takeWhile (· == ' ') |>.length
          let nameChars := line.toList.dropWhile (· == ' ') |>.takeWhile (· != ' ')
          let afterName := line.toList.drop (leadingSpaces + nameChars.length)
          let spacesAfterName := afterName.takeWhile (· == ' ') |>.length
          if spacesAfterName >= 2 then
            result := result.push (offset + leadingSpaces, name.utf8ByteSize)
    offset := offset + line.utf8ByteSize + 1
  -- Mirror Syntax.processRfcText: a single match is a column-header line
  -- (e.g., "TYPE  value and meaning"), not a glossary.
  if result.size < 2 then return #[]
  return result

/-- Find byte offset ranges of sentences within field descriptions.
    Given field name positions, finds ". " and ".\n" sentence boundaries
    in the description text between consecutive fields.
    Returns array of (byteOffset, byteLength) pairs for each sentence. -/
private def findSentenceSplitPoints (text : String) (fieldSplits : Array (Nat × Nat))
    : Array (Nat × Nat) := Id.run do
  if fieldSplits.isEmpty then return #[]
  let textBytes := text.utf8ByteSize
  let mut result : Array (Nat × Nat) := #[]
  for i in [:fieldSplits.size] do
    let (fieldOff, fieldLen) := fieldSplits[i]!
    let descStart := fieldOff + fieldLen
    let descEnd := if i + 1 < fieldSplits.size then fieldSplits[i + 1]!.1 else textBytes
    if descEnd <= descStart then continue
    let descText := (⟨text, ⟨descStart⟩, ⟨descEnd⟩⟩ : Substring.Raw).toString
    let splits := VeriDNS.RFC.Property.findSentenceSplitBytes descText
    if splits.isEmpty then
      result := result.push (descStart, descEnd - descStart)
      continue
    result := result.push (descStart, splits[0]!)
    for j in [:splits.size - 1] do
      result := result.push (descStart + splits[j]!, splits[j + 1]! - splits[j]!)
    result := result.push (descStart + splits[splits.size - 1]!,
      descEnd - descStart - splits[splits.size - 1]!)
  return result

/-- Find byte offset ranges of sentences in prose paragraphs, for sections
    without a where-block. Used to create idents that prose-derived props
    (prose-clause rules, algorithm properties, glossary intro props) can
    attach hover info to.
    Sentences end at "." followed by a space or end-of-line; they never span
    blank lines or diagram-ish lines (borders, scales). The first non-blank
    line (the section title) is skipped — it gets its own split point.
    Scanning stops at `stopAt` (byte offset of the first glossary or
    value-list entry) so entry-name idents are not swallowed. -/
private def findProseSentenceSplitPoints (text : String) (stopAt : Nat)
    : Array (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut result : Array (Nat × Nat) := #[]
  let mut offset : Nat := 0
  let mut seenTitle := false
  let mut sentStart : Option Nat := none
  let mut lastEnd : Nat := 0
  for line in lines do
    if offset >= stopAt then break
    let trimmed := line.trimAscii.toString
    let isBlank := trimmed.isEmpty
    let isDiagramish := !isBlank && (
      trimmed.startsWith "+" || trimmed.startsWith "|" || trimmed.startsWith "/" ||
      trimmed.toList.all (fun c => c.isDigit || c == ' '))
    if isBlank || isDiagramish then
      -- Paragraph boundary: flush any open sentence
      if let some s := sentStart then
        if lastEnd > s then result := result.push (s, lastEnd - s)
      sentStart := none
    else if !seenTitle then
      -- Skip the section title line (handled by findSectionTitlePosition)
      seenTitle := true
    else
      -- Prose line: scan for sentence boundaries
      let chars := line.toList
      let mut b := offset
      for j in [:chars.length] do
        let c := chars[j]!
        if c != ' ' then
          if sentStart.isNone then sentStart := some b
          lastEnd := b + c.utf8Size
          if c == '.' && (j + 1 >= chars.length || chars[j + 1]! == ' ') then
            if let some s := sentStart then
              result := result.push (s, b + 1 - s)
            sentStart := none
        b := b + c.utf8Size
    offset := offset + line.utf8ByteSize + 1
  -- Flush trailing sentence at end of text / stopAt
  if let some s := sentStart then
    if lastEnd > s then result := result.push (s, lastEnd - s)
  return result

/-- Create an atom with .original source info at the given byte range. -/
private def mkOrigAtom (input : String) (startByte endByte : Nat) : Syntax :=
  let text := (input.toRawSubstring.extract ⟨startByte⟩ ⟨endByte⟩).toString
  Syntax.atom
    (.original ⟨input, ⟨startByte⟩, ⟨startByte⟩⟩ ⟨startByte⟩
               ⟨input, ⟨endByte⟩, ⟨endByte⟩⟩ ⟨endByte⟩)
    text

/-- Create an ident with .original source info at the given byte range.
    Used for field names so SubVerso picks up TermInfo for hover. -/
private def mkOrigIdent (input : String) (startByte endByte : Nat) (name : Name) : Syntax :=
  let rawVal := input.toRawSubstring.extract ⟨startByte⟩ ⟨endByte⟩
  .ident
    (.original ⟨input, ⟨startByte⟩, ⟨startByte⟩⟩ ⟨startByte⟩
               ⟨input, ⟨endByte⟩, ⟨endByte⟩⟩ ⟨endByte⟩)
    rawVal name []

/-- Find byte offset and length of the section title line ("N.N.N. Title").
    Returns (byteOffset, byteLength) relative to text start. -/
private def findSectionTitlePosition (text : String) : Option (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut offset : Nat := 0
  for line in lines do
    let trimmed := line.trimAscii.toString
    if !trimmed.isEmpty then
      let chars := trimmed.toList
      if chars[0]!.isDigit then
        let mut i := 0
        let mut dotCount := 0
        let mut found := false
        while i < chars.length do
          if chars[i]! == '.' then
            dotCount := dotCount + 1
            if i + 1 < chars.length && chars[i + 1]! == ' ' && dotCount >= 2 then
              found := true
              break
          else if !chars[i]!.isDigit then
            break
          i := i + 1
        if found then
          let spaces := line.toList.takeWhile (· == ' ') |>.length
          return some (offset + spaces, trimmed.utf8ByteSize)
    offset := offset + line.utf8ByteSize + 1
  return none

/-- Find byte offset and length of the entire bit diagram (number scales + grid).
    Returns (byteOffset, byteLength) relative to text start. -/
private def findDiagramPosition (text : String) : Option (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut offset : Nat := 0
  let mut startOffset : Option Nat := none
  let mut endOffset : Nat := 0
  let mut inDiagram := false
  let mut preScaleStart : Option Nat := none
  for line in lines do
    let lineByteLen := line.utf8ByteSize
    let trimmed := line.trimAscii.toString
    if (line.splitOn "+--+").length > 1 then
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
        if trimmed.toList.all (fun c => c.isDigit || c == ' ') then
          if preScaleStart.isNone then
            preScaleStart := some offset
        else
          preScaleStart := none
    offset := offset + lineByteLen + 1
  match startOffset with
  | some s => some (s, endOffset - s)
  | none => none

/-- Find byte offset ranges of example trigger phrases using the NLP tokenizer.
    Tokenizes the text, POS-tags it, finds `.discMarker` tokens, then merges
    consecutive markers (e.g., "For" + "example") into single (offset, length) spans.
    Returns array of (byteOffset, byteLength) pairs for each occurrence.
    Note: offsets are character-based (matching the tokenizer), converted to byte
    offsets via scanning the text. -/
private def findExampleSplitPoints (text : String) : Array (Nat × Nat) := Id.run do
  let tokens := VeriDNS.RFC.NLP.tagPOS (VeriDNS.RFC.NLP.tokenize text)
  -- Collect discMarker token positions
  let mut markers : Array (Nat × Nat) := #[]
  for t in tokens do
    if t.pos == .discMarker then
      markers := markers.push (t.offset, t.word.length)
  if markers.isEmpty then return #[]
  -- Merge consecutive markers (e.g., "For" at 0 + "example" at 4 → (0, 11))
  let mut merged : Array (Nat × Nat) := #[]
  let mut curStart := markers[0]!.1
  let mut curEnd := markers[0]!.1 + markers[0]!.2
  for i in [1:markers.size] do
    let (off, len) := markers[i]!
    -- Consecutive if the gap between end of last and start of next is small (whitespace)
    if off <= curEnd + 2 then
      curEnd := off + len
    else
      merged := merged.push (curStart, curEnd - curStart)
      curStart := off
      curEnd := off + len
  merged := merged.push (curStart, curEnd - curStart)
  -- Convert character offsets to byte offsets
  let chars := text.toList.toArray
  -- Build char→byte offset mapping
  let mut charToByteArr : Array Nat := #[]
  let mut byteOff : Nat := 0
  for c in chars do
    charToByteArr := charToByteArr.push byteOff
    byteOff := byteOff + c.utf8Size
  let charToByte (charOff : Nat) : Nat :=
    if charOff < charToByteArr.size then charToByteArr[charOff]!
    else text.utf8ByteSize
  let mut result : Array (Nat × Nat) := #[]
  for (charOff, charLen) in merged do
    let bStart := charToByte charOff
    let bEnd := charToByte (charOff + charLen)
    result := result.push (bStart, bEnd - bStart)
  return result

/-- Find byte offset ranges of value-list entry names (e.g., "A  1 ...", "NS  2 ...").
    Only matches in sections without "where:" or "+--+" diagrams.
    Returns array of (byteOffset, byteLength) pairs. -/
private def findValueListSplitPoints (text : String) : Array (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let hasWhere := lines.any (fun l => l.trimAscii.toString == "where:")
  let hasDiagram := lines.any (fun l => (l.splitOn "+--+").length > 1)
  if hasWhere || hasDiagram then return #[]
  let mut result : Array (Nat × Nat) := #[]
  let mut offset : Nat := 0
  for line in lines do
    let trimmed := line.trimAscii.toString
    if !trimmed.isEmpty then
      let leadingSpaces := line.toList.takeWhile (· == ' ') |>.length
      if leadingSpaces < 8 then
        let parts := trimmed.splitOn " " |>.filter (!·.isEmpty)
        if parts.length >= 2 then
          let name := parts[0]!
          let isValidName := (name == "*") ||
            (!name.isEmpty && name.toList.all (fun c => c.isUpper || c.isDigit || c == '-'))
          if isValidName then
            if let some _ := parts[1]!.toNat? then
              result := result.push (offset + leadingSpaces, name.utf8ByteSize)
    offset := offset + line.utf8ByteSize + 1
  return result

/-- Custom parser that reads RFC text between braces, splitting field names
    in the where block into separate atoms for SubVerso hover support.
    Output: a null node containing multiple atom children. -/
private partial def rfcTextBodyFn : ParserFn := fun c s =>
  let startPos := s.pos
  -- Phase 1: Find closing brace
  let rec findClose (pos : String.Pos.Raw) (depth : Nat) : Option String.Pos.Raw :=
      if c.atEnd pos then none
      else
        let ch := c.get pos
        let pos' := ⟨pos.byteIdx + ch.utf8Size⟩
        if ch == '{' then findClose pos' (depth + 1)
        else if ch == '}' then
          if depth == 0 then some pos else findClose pos' (depth - 1)
        else findClose pos' depth
  match findClose startPos 0 with
  | none => s.mkError "unexpected end of input in RFC text block"
  | some closePos =>
    let text := extractText c startPos closePos
    let input := c.toInputContext.inputString
    let base := startPos.byteIdx
    let endByte := closePos.byteIdx
    -- Phase 2: Find split points (section title, diagram, field names)
    let fieldSplits := findFieldSplitPoints text
    let titleAndDiagram : Array (Nat × Nat) := Id.run do
      let mut arr : Array (Nat × Nat) := #[]
      if let some pos := findSectionTitlePosition text then
        arr := arr.push pos
      if let some pos := findDiagramPosition text then
        arr := arr.push pos
      return arr
    let glossarySplits := findGlossarySplitPoints text
    let valueListSplits := findValueListSplitPoints text
    let exampleSplits := findExampleSplitPoints text
    let sentenceSplits := findSentenceSplitPoints text fieldSplits
    -- Prose sentence splits for sections without a where-block, stopping
    -- before the first glossary/value-list entry so their names stay idents.
    let proseSentenceSplits :=
      if fieldSplits.isEmpty then
        let stopAt := match glossarySplits[0]?, valueListSplits[0]? with
          | some g, some v => min g.1 v.1
          | some g, none => g.1
          | none, some v => v.1
          | none, none => text.utf8ByteSize
        findProseSentenceSplitPoints text stopAt
      else #[]
    -- Sort by offset, then deduplicate overlapping splits (prefer longer)
    let allSplits := (titleAndDiagram ++ fieldSplits ++ glossarySplits ++ valueListSplits
        ++ exampleSplits ++ sentenceSplits ++ proseSentenceSplits).qsort
      (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 > b.2))
    let splits := Id.run do
      let mut result : Array (Nat × Nat) := #[]
      let mut lastEnd : Nat := 0
      for s in allSplits do
        if s.1 >= lastEnd then
          result := result.push s
          lastEnd := s.1 + s.2
      return result
    -- Phase 3: Build segmented atoms
    let atoms := Id.run do
      if splits.isEmpty then
        -- No where block — single atom
        return #[mkOrigAtom input base endByte]
      let mut result : Array Syntax := #[]
      let mut cursor : Nat := base
      for (splitOffset, splitLen) in splits do
        let nameStart := base + splitOffset
        let nameEnd := nameStart + splitLen
        -- Skip splits that overlap with already-processed regions
        if nameStart < cursor then continue
        -- Segment before this field name
        if nameStart > cursor then
          result := result.push (mkOrigAtom input cursor nameStart)
        -- Field name ident (SubVerso processes idents for hover, not atoms)
        let fieldText := (input.toRawSubstring.extract ⟨nameStart⟩ ⟨nameEnd⟩).toString
        result := result.push (mkOrigIdent input nameStart nameEnd (Name.mkSimple fieldText))
        cursor := nameEnd
      -- Final segment after last field name
      if cursor < endByte then
        result := result.push (mkOrigAtom input cursor endByte)
      return result
    (s.pushSyntax (mkNullNode atoms)).setPos closePos

/-- Parser wrapper for RFC text body -/
@[inline] def rfcTextBody : Parser where
  fn := rfcTextBodyFn

/-- Get the text content from an atom or ident syntax node. -/
private def getSyntaxText : Syntax → String
  | .atom _ val => val
  | .ident _ rawVal _ _ => rawVal.toString
  | _ => ""

@[combinator_formatter rfcTextBody]
def rfcTextBody.formatter : PrettyPrinter.Formatter :=
  open Lean.Syntax.MonadTraverser PrettyPrinter.Formatter in do
  let stx ← getCur
  if stx.isAtom || stx.isIdent then
    push (getSyntaxText stx).toFormat
  else
    for arg in stx.getArgs do
      push (getSyntaxText arg).toFormat
  goLeft

@[combinator_parenthesizer rfcTextBody]
def rfcTextBody.parenthesizer : PrettyPrinter.Parenthesizer := pure ()

declare_syntax_cat rfcTextContents
syntax rfcTextBody : rfcTextContents 

/-- The include_rfc command syntax.
    Use `unsafe` flag to skip re-parsing the RFC text as commands:
      include_rfc "noparse" [1035][1401:1529] { ... } -/
syntax (name := includeRfc)
  "include_rfc" ("noparse")? "[" num "]" "[" num ":" num "]"
  " {" rfcTextContents "}" : command

/-- Compute a simple line diff between expected and actual text -/
private def computeDiff (expected actual : String) : String := Id.run do
  let expLines := expected.splitOn "\n"
  let actLines := actual.splitOn "\n"
  let maxLen := max expLines.length actLines.length
  let mut result := ""
  let mut diffCount := 0
  for i in [:maxLen] do
    let expLine := expLines.getD i ""
    let actLine := actLines.getD i ""
    if expLine != actLine then
      diffCount := diffCount + 1
      result := result ++ s!"  line {i + 1}:\n"
      result := result ++ s!"    expected: {repr expLine}\n"
      result := result ++ s!"    actual:   {repr actLine}\n"
      if diffCount >= 5 then
        result := result ++ s!"  ... ({maxLen - i - 1} more lines)\n"
        break
  if expLines.length != actLines.length then
    result := result ++ s!"  expected {expLines.length} lines, got {actLines.length} lines\n"
  return result

/-- Normalize text for comparison: strip trailing whitespace per line,
    trim leading/trailing blank lines -/
private def normalizeText (s : String) : String :=
  let lines := s.splitOn "\n" |>.map (·.trimAsciiEnd.toString)
  -- trim leading blank lines
  let lines := lines.dropWhile (·.trimAscii.toString.isEmpty)
  -- trim trailing blank lines
  let lines := lines.reverse.dropWhile (·.trimAscii.toString.isEmpty) |>.reverse
  "\n".intercalate lines

@[command_elab includeRfc]
def elabIncludeRfc : CommandElab := fun stx => do
  let (noParse, rfcNumStx, fromStx, toStx, contents) <- match stx with
    | `(include_rfc [$rfcNumStx:num] [$fromStx:num : $toStx:num] { $contents:rfcTextContents }) => pure (false, rfcNumStx, fromStx, toStx, contents)
    | `(include_rfc noparse [$rfcNumStx:num] [$fromStx:num : $toStx:num] { $contents:rfcTextContents }) => pure (true, rfcNumStx, fromStx, toStx, contents)
    | _ => throwUnsupportedSyntax
  let rfcNum := rfcNumStx.getNat
  let fromLine := fromStx.getNat
  let toLine := toStx.getNat
  -- Parser outputs a null node with atom/ident children (field names are idents)
  let rfcNode := contents.raw[0]!
  let userText := if rfcNode.isAtom then rfcNode.getAtomVal
    else String.join (rfcNode.getArgs.toList.map getSyntaxText)

  -- Resolve the RFC file path
  let srcFile ← getFileName
  let srcDir := System.FilePath.mk srcFile |>.parent |>.getD "."
  let projectRoot ← findProjectRoot srcDir
  let rfcPath := projectRoot / "rfc" / s!"rfc-{rfcNum}.txt"

  -- Read the RFC file
  let rfcContent ← IO.FS.readFile rfcPath

  -- Extract the line range
  let rfcExtracted ← match RFC.Parser.extractLines rfcContent fromLine toLine with
    | .ok text => pure text
    | .error msg => throwError "include_rfc: {msg}"

  -- Normalize both texts and compare
  let normalizedRfc := normalizeText rfcExtracted
  let normalizedUser := normalizeText userText

  if normalizedRfc != normalizedUser then
    let diff := computeDiff normalizedRfc normalizedUser
    throwError "include_rfc[{rfcNum}][{fromLine}:{toLine}]: RFC text mismatch\n{diff}"

  -- Process verified RFC text through custom syntax pipeline.
  -- Recognizes bit diagrams, where blocks, and section headers,
  -- and generates formal Lean definitions (structures, inductives).
  -- Use `noparse` flag to skip processing (verification only).
  if noParse then
    return

  let rfcArgs := rfcNode.getArgs
  if let some (structName, mergedFields, propSrcs) ← VeriDNS.RFC.Syntax.processRfcText userText rfcArgs then
    -- Push TermInfo for parser ident nodes so SubVerso renders them with hover.
    -- Without this, all RFC text renders as `unknown token` because the generated
    -- struct syntax uses mkIdent/mkNode (synthetic, no source positions), so SubVerso's
    -- position-based matching (infoForSyntax) can't link parser idents to definitions.
    -- NOTE: When modifying this code, delete .lake/build/literate/ before rebuilding
    -- docs — the literate cache is NOT invalidated by lake build.
    -- All pushers share one claims map (ident position → hover target):
    -- SubVerso renders a single TermInfo per token, so the first definition
    -- to claim an ident owns its hover and later ones are appended to the
    -- owner's docstring ("Also generated from this passage"). Order =
    -- priority: prose props, then per-sentence props, then example props,
    -- then the generic struct/field fallback on whatever remains unclaimed.
    let mut claims ← VeriDNS.RFC.Syntax.pushProseHoverInfo propSrcs rfcArgs
    claims ← VeriDNS.RFC.Syntax.pushSentenceHoverInfo structName rfcArgs mergedFields claims
    claims ← VeriDNS.RFC.Syntax.generateExampleProps structName userText mergedFields rfcArgs claims
    -- Filter: only pass field name + title/diagram idents to pushHoverInfoFromIdents.
    -- Sentence idents (after field names) are handled exclusively by pushSentenceHoverInfo.
    let fieldNameSet := mergedFields.map (·.name.toUpper)
    let mut structIdents : Array Syntax := #[]
    let mut seenFieldName := false
    for arg in rfcArgs do
      if !arg.isIdent then continue
      if let some pos := arg.getPos? then
        if claims.contains pos.byteIdx then continue
      match arg with
      | .ident _ rawVal _ _ =>
        if fieldNameSet.contains rawVal.toString.toUpper then
          seenFieldName := true
          structIdents := structIdents.push arg
        else if !seenFieldName then
          structIdents := structIdents.push arg
      | _ => continue
    VeriDNS.RFC.Syntax.pushHoverInfoFromIdents structName structIdents

end VeriDNS.RFC
