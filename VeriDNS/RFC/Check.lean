import Lean
import Pseudoprint

open Lean Elab Command Parser

namespace VeriDNS.RFC

private def containsSub (s sub : String) : Bool := (s.splitOn sub).length > 1

def isPageFooter (line : String) : Bool := containsSub line "[Page " && containsSub line "]"
def isFormFeed (line : String) : Bool := line.any (· == '\x0c')
def isRfcHeader (line : String) : Bool := (line.trimAsciiStart).toString.startsWith "RFC "

def stripPageBreaks (lines : Array String) : Array String := Id.run do
  let mut toRemove : Array Bool := Array.replicate lines.size false
  for i in [:lines.size] do
    if isFormFeed lines[i]! then
      toRemove := toRemove.set! i true
      let mut j := i
      while j > 0 do
        j := j - 1
        let line := lines[j]!
        if line.trimAscii.toString.isEmpty then
          toRemove := toRemove.set! j true
        else if isPageFooter line then
          toRemove := toRemove.set! j true
          while j > 0 do
            j := j - 1
            if lines[j]!.trimAscii.toString.isEmpty then toRemove := toRemove.set! j true
            else break
          break
        else break
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
        else break
  let mut result : Array String := #[]
  for i in [:lines.size] do
    if !toRemove[i]! then result := result.push lines[i]!
  return result

def extractLines (rfcText : String) (from_ to_ : Nat) : Except String String := do
  if from_ == 0 then .error "Line numbers are 1-indexed"
  if from_ > to_ then .error s!"Invalid range: {from_} > {to_}"
  let allLines := rfcText.splitOn "\n" |>.toArray
  if to_ > allLines.size then .error s!"Line {to_} exceeds file length ({allLines.size} lines)"
  let rawSlice := allLines.extract (from_ - 1) to_
  let cleaned := (stripPageBreaks rawSlice).map (·.trimAsciiEnd.toString)
  .ok ("\n".intercalate cleaned.toList)

private def findProjectRoot (dir : System.FilePath) : IO System.FilePath := do
  let cwd ← IO.currentDir
  let mut cur := if dir.toString.startsWith "/" then dir else cwd / dir
  for _ in List.range 20 do
    if ← (cur / "lakefile.lean").pathExists then return cur
    if ← (cur / "lakefile.toml").pathExists then return cur
    match cur.parent with
    | some p => cur := p
    | none => break
  throw <| IO.userError s!"Could not find project root from {dir}"

def normalizeText (s : String) : String :=
  let lines := s.splitOn "\n" |>.map (·.trimAsciiEnd.toString)
  let lines := lines.dropWhile (·.trimAscii.toString.isEmpty)
  let lines := lines.reverse.dropWhile (·.trimAscii.toString.isEmpty) |>.reverse
  "\n".intercalate lines

def collapseWs (s : String) : String := Id.run do
  let mut out := ""
  let mut prevSpace := true
  for c in s do
    if c.isWhitespace then
      if !prevSpace then out := out.push ' '
      prevSpace := true
    else
      out := out.push c
      prevSpace := false
  return out.trimAsciiEnd.toString

private def computeDiff (expected actual : String) : String := Id.run do
  let expLines := expected.splitOn "\n"
  let actLines := actual.splitOn "\n"
  let maxLen := max expLines.length actLines.length
  let mut result := ""
  let mut diffCount := 0
  for i in [:maxLen] do
    let e := expLines.getD i ""
    let a := actLines.getD i ""
    if e != a then
      diffCount := diffCount + 1
      result := result ++ s!"  line {i + 1}:\n    expected: {repr e}\n    actual:   {repr a}\n"
      if diffCount >= 5 then
        result := result ++ s!"  ... ({maxLen - i - 1} more lines)\n"
        break
  if expLines.length != actLines.length then
    result := result ++ s!"  expected {expLines.length} lines, got {actLines.length} lines\n"
  return result

private def readRfc (num : Nat) : CommandElabM String := do
  let srcDir := System.FilePath.mk (← getFileName) |>.parent |>.getD "."
  let root ← findProjectRoot srcDir
  IO.FS.readFile (root / "rfc" / s!"rfc-{num}.txt")

private def mkOrigAtom (input : String) (startByte endByte : Nat) : Syntax :=
  let text := (input.toRawSubstring.extract ⟨startByte⟩ ⟨endByte⟩).toString
  Syntax.atom
    (.original ⟨input, ⟨startByte⟩, ⟨startByte⟩⟩ ⟨startByte⟩
               ⟨input, ⟨endByte⟩, ⟨endByte⟩⟩ ⟨endByte⟩)
    text

private partial def rfcTextBodyFn : ParserFn := fun c s =>
  let startPos := s.pos
  let rec findClose (pos : String.Pos.Raw) (depth : Nat) : Option String.Pos.Raw :=
    if c.atEnd pos then none
    else
      let ch := c.get pos
      let pos' : String.Pos.Raw := ⟨pos.byteIdx + ch.utf8Size⟩
      if ch == '{' then findClose pos' (depth + 1)
      else if ch == '}' then (if depth == 0 then some pos else findClose pos' (depth - 1))
      else findClose pos' depth
  match findClose startPos 0 with
  | none => s.mkError "unexpected end of input in RFC text block"
  | some closePos =>
    let input := c.toInputContext.inputString
    let atom := mkOrigAtom input startPos.byteIdx closePos.byteIdx
    (s.pushSyntax (mkNullNode #[atom])).setPos closePos

@[inline] def rfcTextBody : Parser where
  fn := rfcTextBodyFn

private def getSyntaxText : Syntax → String
  | .atom _ val => val
  | .ident _ rawVal _ _ => rawVal.toString
  | _ => ""

@[combinator_formatter rfcTextBody]
def rfcTextBody.formatter : PrettyPrinter.Formatter :=
  open Lean.Syntax.MonadTraverser PrettyPrinter.Formatter in do
  let stx ← getCur
  if stx.isAtom || stx.isIdent then push (getSyntaxText stx).toFormat
  else for arg in stx.getArgs do push (getSyntaxText arg).toFormat
  goLeft

@[combinator_parenthesizer rfcTextBody]
def rfcTextBody.parenthesizer : PrettyPrinter.Parenthesizer := pure ()

declare_syntax_cat rfcTextContents
syntax rfcTextBody : rfcTextContents

syntax (name := includeRfc)
  "include_rfc" "[" num "]" "[" num ":" num "]" " {" rfcTextContents "}" : command

@[command_elab includeRfc]
def elabIncludeRfc : CommandElab := fun stx => do
  let (numStx, fromStx, toStx, contents) ← match stx with
    | `(include_rfc [$n:num] [$f:num : $t:num] { $c:rfcTextContents }) => pure (n, f, t, c)
    | _ => throwUnsupportedSyntax
  let num := numStx.getNat
  let fromLine := fromStx.getNat
  let toLine := toStx.getNat
  let rfcNode := contents.raw[0]!
  let userText := if rfcNode.isAtom then rfcNode.getAtomVal
    else String.join (rfcNode.getArgs.toList.map getSyntaxText)
  let rfcContent ← readRfc num
  let extracted ← match extractLines rfcContent fromLine toLine with
    | .ok t => pure t
    | .error m => throwError "include_rfc: {m}"
  if normalizeText extracted != normalizeText userText then
    throwError "include_rfc[{num}][{fromLine}:{toLine}]: RFC text mismatch\n{computeDiff (normalizeText extracted) (normalizeText userText)}"

  liftCoreM <| do
    Pseudoprint.registerSourceDoc
      { id := s!"rfc-{num}", kind := "rfc", title := s!"RFC {num}", text := rfcContent }
    Pseudoprint.registerSourceScope
      { docId := s!"rfc-{num}", «from» := fromLine, to := toLine }

private def elabViaClause (stmt : Name) (via? : Option Syntax) :
    CommandElabM (Option (String × Name)) := do
  let some viaStx := via? | return none
  let proof ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo viaStx
  liftCoreM <| do
    Pseudoprint.registerDischarge stmt proof
    Pseudoprint.registerSourceLink stmt
      { kind := "proof"
        label := s!"proven by {proof}"
        href := none
        text := none }
    return some ((← Pseudoprint.declStatusName proof).toString, proof)

syntax (name := checkRfcDoc)
  "check_rfc_doc" ident "[" num "]" "[" num ":" num "]" (" via " ident)? : command

@[command_elab checkRfcDoc]
def elabCheckRfcDoc : CommandElab := fun stx => do
  let (declStx, numStx, fromStx, toStx, via?) ← match stx with
    | `(check_rfc_doc $d:ident [$n:num] [$f:num : $t:num] via $p:ident) =>
      pure (d, n, f, t, some p.raw)
    | `(check_rfc_doc $d:ident [$n:num] [$f:num : $t:num]) => pure (d, n, f, t, none)
    | _ => throwUnsupportedSyntax
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declStx
  let some doc ← liftCoreM <| findDocString? (← getEnv) declName
    | throwError "check_rfc_doc: `{declName}` has no docstring"
  let num := numStx.getNat
  let fromL := fromStx.getNat
  let toL := toStx.getNat
  let rfcContent ← readRfc num
  let extracted ← match extractLines rfcContent fromL toL with
    | .ok t => pure t
    | .error m => throwError "check_rfc_doc: {m}"
  let normDoc := collapseWs doc
  let normRfc := collapseWs extracted
  unless containsSub normRfc normDoc do
    throwError "check_rfc_doc: docstring of `{declName}` is not an excerpt of \
      RFC {num} [{fromL}:{toL}].\n  docstring: {repr normDoc}\n  section:   {repr normRfc}"

  let viaInfo ← elabViaClause declName via?
  let env ← getEnv
  let nodeId := (Pseudoprint.nodeDeclMap env).find? declName |>.getD declName.toString
  liftCoreM <| do

    let status := (viaInfo.map (·.1)).getD (← Pseudoprint.declStatusName declName).toString
    let provenBy := (viaInfo.map (fun x => #[x.2])).getD #[]
    Pseudoprint.registerSourceDoc
      { id := s!"rfc-{num}", kind := "rfc", title := s!"RFC {num}", text := rfcContent }
    Pseudoprint.registerSourceSpan
      { docId := s!"rfc-{num}", «from» := fromL, to := toL, node := nodeId, status, provenBy }
    Pseudoprint.registerSourceLink declName
      { kind := "rfc"
        label := s!"RFC {num} · lines {fromL}–{toL}"
        href := some s!"source/rfc-{num}.html#L{fromL}"
        text := some extracted }

syntax (name := rfcOutOfScope)
  "rfc_out_of_scope" "[" num "]" "[" num ":" num "]" : command

@[command_elab rfcOutOfScope]
def elabRfcOutOfScope : CommandElab := fun stx => do
  let (numStx, fromStx, toStx) ← match stx with
    | `(rfc_out_of_scope [$n:num] [$f:num : $t:num]) => pure (n, f, t)
    | _ => throwUnsupportedSyntax
  let num := numStx.getNat
  let fromL := fromStx.getNat
  let toL := toStx.getNat
  if fromL == 0 || fromL > toL then
    throwError "rfc_out_of_scope[{num}][{fromL}:{toL}]: invalid line range"
  let rfcContent ← readRfc num
  liftCoreM <| do
    Pseudoprint.registerSourceDoc
      { id := s!"rfc-{num}", kind := "rfc", title := s!"RFC {num}", text := rfcContent }
    Pseudoprint.registerSourceExclusion { docId := s!"rfc-{num}", «from» := fromL, to := toL }

syntax (name := rfcProves)
  "rfc_proves" ident "[" num "]" "[" num ":" num "]" (" via " ident)? : command

@[command_elab rfcProves]
def elabRfcProves : CommandElab := fun stx => do
  let (declStx, numStx, fromStx, toStx, via?) ← match stx with
    | `(rfc_proves $d:ident [$n:num] [$f:num : $t:num] via $p:ident) =>
      pure (d, n, f, t, some p.raw)
    | `(rfc_proves $d:ident [$n:num] [$f:num : $t:num]) => pure (d, n, f, t, none)
    | _ => throwUnsupportedSyntax
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declStx
  let num := numStx.getNat
  let fromL := fromStx.getNat
  let toL := toStx.getNat
  let rfcContent ← readRfc num
  let extracted ← match extractLines rfcContent fromL toL with
    | .ok t => pure t
    | .error m => throwError "rfc_proves: {m}"
  let viaInfo ← elabViaClause declName via?
  let env ← getEnv
  let nodeId := (Pseudoprint.nodeDeclMap env).find? declName |>.getD declName.toString
  liftCoreM <| do
    let status := (viaInfo.map (·.1)).getD (← Pseudoprint.declStatusName declName).toString
    let provenBy := (viaInfo.map (fun x => #[x.2])).getD #[]
    Pseudoprint.registerSourceDoc
      { id := s!"rfc-{num}", kind := "rfc", title := s!"RFC {num}", text := rfcContent }
    Pseudoprint.registerSourceSpan
      { docId := s!"rfc-{num}", «from» := fromL, to := toL, node := nodeId, status, provenBy }
    Pseudoprint.registerSourceLink declName
      { kind := "rfc"
        label := s!"proven against RFC {num} · lines {fromL}–{toL}"
        href := some s!"source/rfc-{num}.html#L{fromL}"
        text := some extracted }

end VeriDNS.RFC
