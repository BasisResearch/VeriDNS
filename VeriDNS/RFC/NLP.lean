/-
  Rule-based NLP pipeline for RFC technical prose.

  Parses sentences into Subject-Verb-Object structure, derives semantic
  properties from the grammatical parse, then uses those properties to
  decide whether a section diagram field should be Array-wrapped.

  Pipeline stages:
  1. Tokenizer — split on whitespace, separate punctuation
  2. POS Tagger — disambiguation, lexicon, morphology
  3. Phrase Chunker — greedy left-to-right NP/VP/AdjP parsing
  4. Clause Extractor — SVO, SVAdj, NP-only, or unparsed
  5. Semantic Derivation — map clauses to SectionProp values
  6. Public API — analyzeField, shouldBeArrayNLP
-/
import VeriDNS.RFC.Property

set_option autoImplicit false

namespace VeriDNS.RFC.NLP

-- ============================================================
-- Types
-- ============================================================

inductive POS where
  | det | noun | nounPlural | propNoun | verb | verbPart
  | copula | adj | adv | prep | conj | relPron | punct | quant | unknown
  deriving Repr, BEq, Inhabited

structure Token where
  word : String
  pos  : POS
  deriving Repr, Inhabited

inductive Number where
  | singular | plural | unknown
  deriving Repr, BEq, Inhabited

structure NounPhrase where
  det      : Option String
  preAdjs  : Array String
  head     : String
  number   : Number
  postMods : Array String
  deriving Repr, Inhabited

structure VerbPhrase where
  adv      : Option String
  verb     : String
  isCopula : Bool
  deriving Repr, Inhabited

structure AdjPhrase where
  adv : Option String
  adj : String
  deriving Repr, Inhabited

inductive Clause where
  | svo     (subj : NounPhrase) (verb : VerbPhrase) (obj : NounPhrase)
  | svAdj   (subj : NounPhrase) (verb : VerbPhrase) (comp : AdjPhrase)
  | npOnly  (np : NounPhrase)
  | unparsed (text : String)
  deriving Repr, Inhabited

inductive SectionProp where
  | alwaysPresent
  | pluralHead (head : String)
  | containsPlural (contained : String)
  | possiblyEmptyList
  | someEmpty
  | containsFields
  | structField (fieldName : String) (isArray : Bool)
  | numericBound (subject : String) (value : Nat) (unit : String)
  | unclassified (text : String)
  deriving Repr, BEq, Inhabited

def SectionProp.impliesArray : SectionProp → Bool
  | .alwaysPresent => false
  | .containsFields => false
  | .structField _ _ => false
  | .numericBound _ _ _ => false
  | .unclassified _ => false
  | .pluralHead _ => true
  | .containsPlural _ => true
  | .possiblyEmptyList => true
  | .someEmpty => true

-- ============================================================
-- Helpers
-- ============================================================

private def hasSub (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

private def trim (s : String) : String := s.trimAscii.toString

-- ============================================================
-- Stage 1: Tokenizer
-- ============================================================

private def isPunct (c : Char) : Bool :=
  c == ',' || c == ';' || c == ':' || c == '.' || c == '(' || c == ')'

/-- Split text into tokens, separating punctuation into own tokens. -/
def tokenize (text : String) : Array Token := Id.run do
  let mut tokens : Array Token := #[]
  let mut current := ""
  for c in text.toList do
    if c == ' ' then
      if !current.isEmpty then
        tokens := tokens.push ⟨current, .unknown⟩
        current := ""
    else if isPunct c then
      if !current.isEmpty then
        tokens := tokens.push ⟨current, .unknown⟩
        current := ""
      tokens := tokens.push ⟨String.ofList [c], .punct⟩
    else
      current := current.push c
  if !current.isEmpty then
    tokens := tokens.push ⟨current, .unknown⟩
  return tokens

-- ============================================================
-- Stage 2: POS Tagger
-- ============================================================

private def knownDeterminers : Array String :=
  #["the", "a", "an", "this", "that", "these", "those", "each", "every"]

private def knownCopula : Array String :=
  #["is", "are", "was", "were"]

private def knownVerbs : Array String :=
  #["contains", "includes", "specify", "specifies", "have", "has",
    "hold", "holds", "holding", "carry", "carries", "define", "defines",
    "describe", "describes", "point", "points", "pointing", "answer",
    "answering", "provide", "provides", "expressed", "restricted",
    "limited", "limit"]

private def knownAdjs : Array String :=
  #["present", "empty", "same", "additional", "optional", "variable",
    "unsigned", "authoritative", "recursive", "available", "truncated",
    "standard", "inverse", "total", "remaining"]

private def knownAdvs : Array String :=
  #["always", "possibly", "currently", "only", "not", "never"]

private def knownPreps : Array String :=
  #["in", "of", "for", "to", "from", "with", "toward", "towards",
    "by", "at", "into", "within", "about", "between", "after", "before"]

private def knownConjs : Array String :=
  #["and", "or", "but"]

private def knownQuants : Array String :=
  #["some", "all", "many", "several", "no", "any", "one", "two",
    "three", "four", "five"]

private def knownSingularNouns : Array String :=
  #["section", "field", "question", "name", "server", "list", "format",
    "record", "header", "message", "query", "response", "authority",
    "answer", "information", "opcode", "type", "class", "identifier",
    "data", "length", "address", "zone", "domain", "protocol",
    "octet", "bit", "sequence", "label"]

/-- Lexicon-based POS lookup -/
private def lexiconLookup (word : String) : POS :=
  let w := word.toLower
  if knownDeterminers.contains w then .det
  else if knownCopula.contains w then .copula
  else if knownVerbs.contains w then .verb
  else if knownAdjs.contains w then .adj
  else if knownAdvs.contains w then .adv
  else if knownPreps.contains w then .prep
  else if knownConjs.contains w then .conj
  else if knownQuants.contains w then .quant
  else if w == "which" || w == "who" || w == "whom" then .relPron
  else .unknown

/-- Morphological fallback: guess POS from suffixes -/
private def morphologyGuess (word : String) : POS :=
  let w := word.toLower
  -- Specific known plurals
  if w == "rrs" then .nounPlural
  -- Suffix rules
  else if w.endsWith "ies" then .nounPlural
  else if w.endsWith "s" && !w.endsWith "ss" && w.length > 2 then .nounPlural
  else if w.endsWith "ing" then .verbPart
  else if w.endsWith "ed" then .adj
  -- Capitalized words (not at sentence start, but we don't track position — treat as propNoun)
  else if !word.isEmpty && word.toList[0]!.isUpper then .propNoun
  else .noun

/-- Context-sensitive disambiguation: resolve ambiguous words based on neighbors -/
private def disambiguate (tokens : Array Token) : Array Token := Id.run do
  let mut result := tokens
  for i in [:tokens.size] do
    let w := tokens[i]!.word.toLower
    -- "present" is always adj in RFC prose
    if w == "present" then
      result := result.set! i { tokens[i]! with pos := .adj }
    -- "answer" after det → noun; otherwise keep as-is
    else if w == "answer" then
      if i > 0 && result[i - 1]!.pos == .det then
        result := result.set! i { tokens[i]! with pos := .noun }
    -- "that" after noun or verb → relPron
    else if w == "that" then
      if i > 0 then
        let prev := result[i - 1]!.pos
        if prev == .noun || prev == .nounPlural || prev == .propNoun ||
           prev == .verb || prev == .copula then
          result := result.set! i { tokens[i]! with pos := .relPron }
        else
          result := result.set! i { tokens[i]! with pos := .det }
      else
        result := result.set! i { tokens[i]! with pos := .det }
  return result

/-- Full POS tagging pipeline: lexicon → morphology fallback → disambiguation -/
def tagPOS (tokens : Array Token) : Array Token := Id.run do
  -- First pass: lexicon + morphology
  let mut tagged := tokens
  for i in [:tokens.size] do
    let t := tokens[i]!
    if t.pos == .punct then continue
    let lexPos := lexiconLookup t.word
    let pos := if lexPos != .unknown then lexPos else morphologyGuess t.word
    tagged := tagged.set! i { t with pos := pos }
  -- Second pass: disambiguation
  tagged := disambiguate tagged
  return tagged

-- ============================================================
-- Stage 3: Phrase Chunker
-- ============================================================

private def isNominal (p : POS) : Bool :=
  p == .noun || p == .nounPlural || p == .propNoun

private def isPreAdj (p : POS) : Bool :=
  p == .adj || p == .adv || p == .quant

/-- Try to parse a NounPhrase starting at position `pos`. Returns (NP, nextPos). -/
def parseNP (tokens : Array Token) (pos : Nat) : Option (NounPhrase × Nat) := Id.run do
  if pos >= tokens.size then return none
  let mut i := pos

  -- Optional determiner
  let mut det : Option String := none
  if i < tokens.size && tokens[i]!.pos == .det then
    det := some tokens[i]!.word
    i := i + 1

  -- Pre-modifiers (adj, adv, quant)
  let mut preAdjs : Array String := #[]
  while i < tokens.size && isPreAdj tokens[i]!.pos do
    preAdjs := preAdjs.push tokens[i]!.word
    i := i + 1

  -- Head noun (required)
  if i >= tokens.size || !isNominal tokens[i]!.pos then
    return none
  let head := tokens[i]!.word
  let number : Number := match tokens[i]!.pos with
    | .nounPlural => .plural
    | .noun => .singular
    | _ => .unknown
  i := i + 1

  -- Skip compound "section" (e.g., "header section" → head is "header")
  if i < tokens.size && tokens[i]!.word.toLower == "section" then
    i := i + 1

  -- Post-modifiers: PPs, relative clauses, participial phrases
  let mut postMods : Array String := #[]

  -- Absorb PP: prep + tokens until next phrase boundary
  if i < tokens.size && tokens[i]!.pos == .prep then
    let mut ppWords : Array String := #[tokens[i]!.word]
    i := i + 1
    while i < tokens.size &&
          tokens[i]!.pos != .verb && tokens[i]!.pos != .copula &&
          tokens[i]!.pos != .prep && tokens[i]!.pos != .conj &&
          tokens[i]!.pos != .punct && tokens[i]!.pos != .relPron do
      ppWords := ppWords.push tokens[i]!.word
      i := i + 1
    postMods := postMods.push (" ".intercalate ppWords.toList)

  -- Absorb relative clause: relPron + tokens until punct/end
  if i < tokens.size && tokens[i]!.pos == .relPron then
    let mut relWords : Array String := #[tokens[i]!.word]
    i := i + 1
    while i < tokens.size && tokens[i]!.pos != .punct do
      relWords := relWords.push tokens[i]!.word
      i := i + 1
    postMods := postMods.push (" ".intercalate relWords.toList)

  -- Absorb participial phrase: verbPart + tokens until punct/end
  if i < tokens.size && tokens[i]!.pos == .verbPart then
    let mut partWords : Array String := #[tokens[i]!.word]
    i := i + 1
    while i < tokens.size && tokens[i]!.pos != .punct &&
          tokens[i]!.pos != .verb && tokens[i]!.pos != .copula do
      partWords := partWords.push tokens[i]!.word
      i := i + 1
    postMods := postMods.push (" ".intercalate partWords.toList)

  return some (⟨det, preAdjs, head, number, postMods⟩, i)

/-- Try to parse a VerbPhrase starting at position `pos`. -/
def parseVP (tokens : Array Token) (pos : Nat) : Option (VerbPhrase × Nat) := Id.run do
  if pos >= tokens.size then return none
  let mut i := pos

  -- Optional adverb
  let mut adv : Option String := none
  if i < tokens.size && tokens[i]!.pos == .adv then
    adv := some tokens[i]!.word
    i := i + 1

  -- Verb or copula (required)
  if i >= tokens.size then return none
  let t := tokens[i]!
  if t.pos == .copula then
    return some (⟨adv, t.word, true⟩, i + 1)
  else if t.pos == .verb then
    return some (⟨adv, t.word, false⟩, i + 1)
  else
    return none

/-- Try to parse an AdjPhrase starting at position `pos`. -/
def parseAdjP (tokens : Array Token) (pos : Nat) : Option (AdjPhrase × Nat) := Id.run do
  if pos >= tokens.size then return none
  let mut i := pos

  -- Optional adverb
  let mut adv : Option String := none
  if i < tokens.size && tokens[i]!.pos == .adv then
    adv := some tokens[i]!.word
    i := i + 1

  -- Adjective (required)
  if i >= tokens.size || tokens[i]!.pos != .adj then
    return none

  return some (⟨adv, tokens[i]!.word⟩, i + 1)

-- ============================================================
-- Stage 4: Clause Extractor
-- ============================================================

/-- Parse a token sequence into a Clause. Tries SVO, SVAdj, NP-only, then unparsed. -/
def parseClause (tokens : Array Token) : Clause := Id.run do
  -- Filter out punctuation for clause parsing
  let filtered := tokens.filter (·.pos != .punct)
  if filtered.isEmpty then return .unparsed ""

  -- Try NP + VP + ...
  if let some (np, afterNP) := parseNP filtered 0 then
    if let some (vp, afterVP) := parseVP filtered afterNP then
      -- Try SVO: NP + VP + NP
      if let some (obj, _) := parseNP filtered afterVP then
        return .svo np vp obj
      -- Try SVAdj: NP + VP(copula) + AdjP
      if vp.isCopula then
        if let some (adjP, _) := parseAdjP filtered afterVP then
          return .svAdj np vp adjP
    -- NP-only fragment
    return .npOnly np

  return .unparsed (" ".intercalate (filtered.map (·.word)).toList)

/-- Parse a token sequence, trying SVO/SVAdj from every determiner position.
    Used for prose segments that may contain non-sentence content (e.g., diagram
    artifacts) before the actual sentence. Returns all successfully parsed
    SVO/SVAdj clauses. Falls back to npOnly or unparsed if none found. -/
def parseClauses (tokens : Array Token) : Array Clause := Id.run do
  let filtered := tokens.filter (·.pos != .punct)
  if filtered.isEmpty then return #[.unparsed ""]

  let mut clauses : Array Clause := #[]

  -- Try full clause parse (SVO/SVAdj) from each determiner position
  for startPos in [:filtered.size] do
    if filtered[startPos]!.pos != .det then continue
    if let some (np, afterNP) := parseNP filtered startPos then
      if let some (vp, afterVP) := parseVP filtered afterNP then
        if let some (obj, _) := parseNP filtered afterVP then
          clauses := clauses.push (.svo np vp obj)
        else if vp.isCopula then
          if let some (adjP, _) := parseAdjP filtered afterVP then
            clauses := clauses.push (.svAdj np vp adjP)

  -- If no full clauses found, try NP-only from position 0
  if clauses.isEmpty then
    if let some (np, _) := parseNP filtered 0 then
      return #[.npOnly np]
    else
      return #[.unparsed (" ".intercalate (filtered.map (·.word)).toList)]

  return clauses

-- ============================================================
-- Stage 5: Semantic Derivation
-- ============================================================

/-- Check if a noun refers to internal structure rather than collection items -/
private def isStructuralNoun (head : String) : Bool :=
  let w := head.toLower
  w == "fields" || w == "field" || w == "parameters" || w == "components"

/-- Derive a SectionProp from a parsed Clause and field name. -/
def deriveSectionProp (_fieldName : String) (clause : Clause) : SectionProp :=
  match clause with
  | .svAdj _subj vp comp =>
    if vp.isCopula && comp.adj.toLower == "present" then
      .alwaysPresent
    else .unclassified ""
  | .svo _subj vp obj =>
    let v := vp.verb.toLower
    if v == "contains" || v == "includes" || v == "have" || v == "has" then
      if isStructuralNoun obj.head then
        .containsFields
      else if obj.number == .plural then
        .containsPlural obj.head
      else if obj.head.toLower == "list" then
        .possiblyEmptyList
      else
        .unclassified ""
    else if v == "expressed" then
      -- "expressed in terms of a sequence of X" → structField
      let allPostText := " ".intercalate obj.postMods.toList
      if hasSub allPostText "sequence" then
        -- Extract the noun after "sequence of"
        let parts := allPostText.toLower.splitOn "sequence of "
        if parts.length > 1 then
          let fieldName := trim (parts[parts.length - 1]!.splitOn " ")[0]!
          .structField fieldName true
        else .unclassified ""
      else .unclassified ""
    else
      .unclassified ""
  | .npOnly np =>
    if np.number == .plural then
      .pluralHead np.head
    else
      .unclassified ""
  | .unparsed text => .unclassified text

-- ============================================================
-- Stage 6: Sentence Relevance
-- ============================================================

/-- Check if a clause refers to a given field name.
    Subject head matches field name, or field name appears in preAdjs. -/
def clauseRefersTo (fieldName : String) (clause : Clause) : Bool :=
  let fnLower := fieldName.toLower
  let npMatches (np : NounPhrase) : Bool :=
    np.head.toLower == fnLower ||
    np.preAdjs.any (·.toLower == fnLower) ||
    -- Handle "the additional records section" matching "Additional"
    (np.det.isSome && np.preAdjs.any (·.toLower == fnLower))
  match clause with
  | .svo subj _ _ => npMatches subj
  | .svAdj subj _ _ => npMatches subj
  | .npOnly np => npMatches np
  | .unparsed _ => false

-- ============================================================
-- Stage 7: Public API
-- ============================================================

/-- Analyze a section diagram field, returning all derived semantic properties.
    Parses inline description as NP fragment and prose sentences as clauses. -/
def analyzeField (fieldName inlineDesc prose : String) : Array SectionProp := Id.run do
  let mut props : Array SectionProp := #[]

  -- 1. Parse inline desc as NP fragment
  if !inlineDesc.isEmpty then
    let tokens := tagPOS (tokenize inlineDesc)
    let clause := parseClause tokens
    let prop := deriveSectionProp fieldName clause
    props := props.push prop

  -- 2. Split prose into clauses (on ". " and "; ")
  let proseParts := prose.splitOn ". "
  let mut allParts : Array String := #[]
  for part in proseParts do
    let subParts := part.splitOn "; "
    for sp in subParts do
      let t := trim sp
      if !t.isEmpty then
        allParts := allParts.push t

  -- 3. Parse each part into clauses (trying multiple positions for robustness
  --    against non-sentence content like diagram artifacts in the prose)
  for part in allParts do
    let tokens := tagPOS (tokenize part)
    let clauses := parseClauses tokens
    for clause in clauses do
      if clauseRefersTo fieldName clause then
        let prop := deriveSectionProp fieldName clause
        props := props.push prop

  -- 4. Add .someEmpty if prose contains "some of which are empty"
  if hasSub prose.toLower "some of which are empty" then
    props := props.push .someEmpty

  return props

/-- Determine if a section diagram field should be Array-wrapped,
    using grammatical parsing and semantic derivation.
    `.alwaysPresent` is a hard override (singular regardless of other evidence). -/
def shouldBeArrayNLP (fieldName inlineDesc prose : String) : Bool :=
  let props := analyzeField fieldName inlineDesc prose
  if props.any (· == .alwaysPresent) then false
  else props.any SectionProp.impliesArray

-- ============================================================
-- Prose-only section analysis
-- ============================================================

/-- Extract numeric bounds from prose using pattern matching on word sequences.
    Matches patterns like "limit the X to N octets", "restricted to N octets". -/
def extractNumericBounds (prose : String) : Array SectionProp := Id.run do
  let words := prose.toLower.splitOn " " |>.toArray |>.filter (!·.isEmpty)
  let mut result : Array SectionProp := #[]
  for i in [:words.size] do
    -- Pattern: "limit/restricted/limited ... to N octets/bits"
    let w := words[i]!
    if (w == "limit" || w == "limited" || w.startsWith "restrict") && i + 1 < words.size then
      -- Scan forward for "to N unit"
      for j in [i:words.size] do
        if words[j]! == "to" && j + 2 < words.size then
          let unitWord := words[j + 2]!
          if unitWord.startsWith "octet" || unitWord.startsWith "bit" then
            let unit := if unitWord.startsWith "octet" then "octets" else "bits"
            if let some n := words[j + 1]!.toNat? then
              -- Look backward for the subject (nearest content noun)
              let mut subject := "value"
              let skipWords := #["the", "to", "a", "an", "is", "are", "of", "and",
                "or", "in", "that", "this", "its", "six", "remaining"]
              let searchStart := if i >= 6 then i - 6 else 0
              for k in List.range (j - searchStart) do
                let idx := j - k - 1
                if idx >= searchStart then
                  let candidate := words[idx]!
                  if !skipWords.contains candidate &&
                     !candidate.startsWith "limit" && !candidate.startsWith "restrict" then
                    -- Strip trailing punctuation from subject
                    subject := String.ofList (candidate.toList.filter (fun c => !isPunct c))
                    break
              result := result.push (.numericBound subject n unit)
            break
  return result

/-- Derive structure fields from prose text.
    Scans for "sequence of X" patterns directly, since the general SVO parser
    cannot handle passive voice ("are expressed") and compound nouns. -/
def deriveStructFields (prose : String) : Array (String × Bool) := Id.run do
  let words := prose.toLower.splitOn " " |>.toArray |>.filter (!·.isEmpty)
  let mut result : Array (String × Bool) := #[]
  for i in [:words.size] do
    if words[i]! == "sequence" && i + 1 < words.size && words[i + 1]! == "of" then
      if i + 2 < words.size then
        -- Clean trailing punctuation from field name
        let raw := words[i + 2]!
        let fieldName := String.ofList (raw.toList.filter (fun c => !isPunct c))
        if !fieldName.isEmpty then
          result := result.push (fieldName, true)
  return result

/-- Derive numeric constraints from prose text.
    Extracts "limit/restricted to N octets/bits" patterns. -/
def deriveConstraints (prose : String) : Array (String × Nat × String) := Id.run do
  let bounds := extractNumericBounds prose
  let mut result : Array (String × Nat × String) := #[]
  for b in bounds do
    match b with
    | .numericBound subj val unit => result := result.push (subj, val, unit)
    | _ => pure ()
  return result

end VeriDNS.RFC.NLP
