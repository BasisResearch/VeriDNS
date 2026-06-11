/-
  Rule-based NLP pipeline for RFC technical prose.

  Parses sentences into Subject-Verb-Object structure, derives semantic
  properties from the grammatical parse, then uses those properties to
  decide whether a section diagram field should be Array-wrapped.

  Pipeline stages:
  1. Tokenizer — split on whitespace, separate punctuation
  2. POS Tagger — disambiguation, lexicon, morphology
  3. Phrase Chunker — greedy left-to-right NP/VP/AdjP/PP parsing
  4. Clause Extractor — SVO, SVPassive, SVAdj, NP-only, or unparsed
  5. Semantic Derivation — map clauses to SectionProp values
  6. Public API — analyzeField, shouldBeArrayNLP, analyzeProse
-/
import VeriDNS.RFC.Property

set_option autoImplicit false

namespace VeriDNS.RFC.NLP

-- ============================================================
-- Types
-- ============================================================

inductive POS where
  | det | noun | nounPlural | propNoun | verb | verbPart
  | copula | adj | adv | prep | conj | relPron | punct | quant | num
  | discMarker | subConj | unknown
  deriving Repr, BEq, Inhabited

structure Token where
  word   : String
  pos    : POS
  offset : Nat := 0
  deriving Repr, Inhabited

inductive Number where
  | singular | plural | unknown
  deriving Repr, BEq, Inhabited

/-- Flat NounPhrase data for PostMod (avoids mutual recursion with NounPhrase) -/
structure NPData where
  det      : Option String
  preAdjs  : Array String
  head     : String
  number   : Number
  deriving Repr, Inhabited

/-- Flat PrepPhrase data for PostMod -/
structure PPData where
  prep : String
  np   : NPData
  deriving Repr, Inhabited

/-- A post-modifier of a noun phrase, parsed into structure -/
inductive PostMod where
  | pp (prep : String) (np : NPData)
  | relClause (relPron : String) (text : String)
  | participle (verb : String) (obj : Option NPData) (pps : Array PPData)
  | raw (text : String)
  deriving Repr, Inhabited

structure NounPhrase where
  det      : Option String
  preAdjs  : Array String
  head     : String
  number   : Number
  postMods : Array PostMod
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

structure PrepPhrase where
  prep : String
  np   : NounPhrase
  deriving Repr, Inhabited

/-- Convert a NounPhrase to NPData (drops postMods) -/
def NounPhrase.toData (np : NounPhrase) : NPData :=
  ⟨np.det, np.preAdjs, np.head, np.number⟩

/-- Convert a PrepPhrase to PPData (drops postMods from NP) -/
def PrepPhrase.toData (pp : PrepPhrase) : PPData :=
  ⟨pp.prep, pp.np.toData⟩

inductive Clause where
  | svo      (subj : NounPhrase) (verb : VerbPhrase) (obj : NounPhrase) (pps : Array PrepPhrase)
  | svAdj    (subj : NounPhrase) (verb : VerbPhrase) (comp : AdjPhrase) (pps : Array PrepPhrase)
  | svPassive (subj : NounPhrase) (participle : String) (pps : Array PrepPhrase) (negated : Bool)
  | npOnly   (np : NounPhrase)
  | unparsed (text : String)
  deriving Repr, Inhabited

/-- A clause that may carry conditional (if/when) structure. -/
inductive ConditionalClause where
  | simple (clause : Clause)
  | conditional (guard : Clause) (body : Clause)
  deriving Repr, Inhabited

inductive SectionProp where
  | alwaysPresent
  | pluralHead (head : String)
  | containsPlural (contained : String)
  | possiblyEmptyList
  | someEmpty
  | containsFields
  | structField (fieldName : String) (isArray : Bool)
  | countsEntriesIn (sect : String)
  | domainNameField
  | unclassified (text : String)
  deriving Repr, BEq, Inhabited

inductive ExamplePred where
  | fieldEq (field : String) (value : Nat)
  | fieldAccess (field : String) (value : Nat)
  | unresolved (text : String)
  deriving Repr, BEq, Inhabited

inductive ExampleProp where
  | conditional (antecedent : ExamplePred) (consequent : ExamplePred)
  | assignment (lhs : String) (rhs : String)
  deriving Repr, BEq, Inhabited

def SectionProp.impliesArray : SectionProp → Bool
  | .alwaysPresent => false
  | .containsFields => false
  | .structField _ _ => false
  | .countsEntriesIn _ => false
  | .domainNameField => false
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
  c == ',' || c == ';' || c == ':' || c == '.' || c == '(' || c == ')' || c == '='

/-- Check if chars starting at index i form an abbreviation like "e.g." or "i.e." -/
private def isAbbreviation (chars : Array Char) (i : Nat) : Option Nat :=
  -- Check for "e.g." or "i.e." (4 chars)
  if i + 3 < chars.size then
    let s := String.ofList [chars[i]!, chars[i+1]!, chars[i+2]!, chars[i+3]!]
    if s == "e.g." || s == "i.e." then some 4 else none
  else none

/-- Split text into tokens, separating punctuation into own tokens.
    Tracks character offsets and handles abbreviation lookahead. -/
def tokenize (text : String) : Array Token := Id.run do
  let chars := text.toList.toArray
  let mut tokens : Array Token := #[]
  let mut current := ""
  let mut currentStart : Nat := 0
  let mut i : Nat := 0
  while i < chars.size do
    let c := chars[i]!
    -- Tuple notation "<A, B, ...>" is one lexical token (a nominal), like
    -- a numeral: RFC prose uses it for composite keys (RFC 2308 §5's
    -- "the same <QNAME, QCLASS>"). Only when a matching '>' is near.
    if c == '<' then
      let close? : Option Nat := Id.run do
        for j in [i+1 : min chars.size (i + 64)] do
          if chars[j]! == '>' then return some j
        return none
      if let some j := close? then
        if !current.isEmpty then
          tokens := tokens.push ⟨current, .unknown, currentStart⟩
          current := ""
        let tup := String.ofList (chars.toList.drop i |>.take (j + 1 - i))
        tokens := tokens.push ⟨tup, .unknown, i⟩
        i := j + 1
        continue
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      if !current.isEmpty then
        tokens := tokens.push ⟨current, .unknown, currentStart⟩
        current := ""
      i := i + 1
    else if isPunct c then
      -- Check for abbreviation before treating '.' as punct
      if c == '.' || c == ',' || c == ')' then
        -- Lookahead: if current + remaining chars form an abbreviation
        -- e.g., we've accumulated "e" and see ".g."
        if !current.isEmpty then
          let testStart := i - current.length
          match isAbbreviation chars testStart with
          | some len =>
            let abbrStr := String.ofList (chars.toList.drop testStart |>.take len)
            tokens := tokens.push ⟨abbrStr, .unknown, testStart⟩
            current := ""
            i := testStart + len
            -- Skip trailing comma/paren after abbreviation
            if i < chars.size && (chars[i]! == ',' || chars[i]! == ')') then
              tokens := tokens.push ⟨String.ofList [chars[i]!], .punct, i⟩
              i := i + 1
            continue
          | none => pure ()
      if !current.isEmpty then
        tokens := tokens.push ⟨current, .unknown, currentStart⟩
        current := ""
      tokens := tokens.push ⟨String.ofList [c], .punct, i⟩
      i := i + 1
    else
      if current.isEmpty then
        currentStart := i
      current := current.push c
      i := i + 1
  if !current.isEmpty then
    tokens := tokens.push ⟨current, .unknown, currentStart⟩
  return tokens

-- ============================================================
-- Stage 2: POS Tagger
-- ============================================================

private def knownDeterminers : Array String :=
  #["the", "a", "an", "this", "that", "these", "those", "each", "every", "its",
    "their"]

private def knownCopula : Array String :=
  #["is", "are", "was", "were", "be"]

private def knownVerbs : Array String :=
  #["contains", "includes", "specify", "specifies", "have", "has",
    "hold", "holds", "holding", "carry", "carries", "define", "defines",
    "describe", "describes", "point", "points", "pointing", "answer",
    "answering", "provide", "provides", "expressed", "restricted",
    "limited", "limit", "specifying", "specified", "represented",
    "terminated", "followed", "corresponds", "carried", "sent",
    "prefixed", "uses", "use", "set",
    "stores", "store", "discard", "convert", "ignore", "receives", "keeps", "keep",
    "reclaim", "depends",
    "initializes", "initialize", "matches", "match", "check", "checks",
    "searches", "search", "cycle", "analyze", "cache", "restart",
    "pass", "enter", "return", "give", "copy", "find", "list",
    "resolve", "look", "consult", "delete", "fail", "show",
    "omit", "omitted", "compose", "composing", "insert", "inserted",
    "guarantee", "parse", "parsing", "truncate", "duplicate", "duplicated",
    "chosen", "prevent", "tried", "altered",
    "cached", "retrieved", "returned", "resulted",
    "refuse", "add", "encounter", "encounters", "decremented",
    "compare", "compared"]

private def knownAdjs : Array String :=
  #["present", "empty", "same", "additional", "optional", "variable",
    "unsigned", "authoritative", "recursive", "available", "truncated",
    "standard", "inverse", "total", "remaining", "less", "fewer",
    "absolute", "dubious", "partial", "unsolicited", "relative",
    "positive", "negative", "timing", "refreshing",
    "great", "close", "large", "small", "short", "long", "high", "low",
    "valid", "bogus", "local", "aggressive", "paranoid", "desired",
    "unable", "able", "closer", "greater",
    -- irregular comparatives
    "better", "worse",
    -- superlative poles (ranking directives, RFC 2181 §5.4.1)
    "most", "least", "highest", "lowest", "greatest", "best", "worst",
    -- (in)sensitivity compounds and their stems (RFC 1035 §2.3.3/§3.1);
    -- '-' is not punctuation, so hyphenated compounds are single tokens
    "case-insensitive", "case-sensitive", "insensitive", "sensitive",
    "alphabetic", "non-alphabetic"]

private def knownAdvs : Array String :=
  #["always", "possibly", "currently", "only", "not", "never", "then",
    "exactly"]

private def knownPreps : Array String :=
  #["in", "of", "for", "to", "from", "with", "toward", "towards",
    "by", "at", "into", "within", "about", "between", "after", "before",
    "on", "as", "than"]

private def knownConjs : Array String :=
  #["and", "or", "but"]

private def knownQuants : Array String :=
  #["some", "all", "many", "several", "no", "any", "one", "two",
    "three", "four", "five", "six", "seven", "eight", "nine", "ten", "zero"]

private def knownSingularNouns : Array String :=
  #["section", "field", "question", "name", "server", "list", "format",
    "record", "header", "message", "query", "response", "authority",
    "answer", "information", "opcode", "type", "class", "identifier",
    "data", "length", "address", "zone", "domain", "protocol",
    "octet", "bit", "sequence", "label",
    "cache", "resolver", "interval", "timer", "entry", "result", "track", "guess", "equivalent",
    "timestamp", "preference", "sweep", "reliability",
    "delegation", "timeout", "sname", "stype", "sclass", "slist", "sbelt",
    "qtype", "qclass", "id", "cname",
    "datagram", "truncation", "connection", "transmission", "retransmission"]

/-- Lexicon-based POS lookup -/
private def lexiconLookup (word : String) : POS :=
  let w := word.toLower
  if w == "e.g." || w == "i.e." then .discMarker
  else if w == "if" || w == "when" then .subConj
  else if knownDeterminers.contains w then .det
  else if knownCopula.contains w then .copula
  else if knownVerbs.contains w then .verb
  else if knownAdjs.contains w then .adj
  else if knownAdvs.contains w then .adv
  else if knownPreps.contains w then .prep
  else if knownConjs.contains w then .conj
  else if knownQuants.contains w then .quant
  else if w == "which" || w == "who" || w == "whom" || w == "whose" then .relPron
  else .unknown

/-- Strip ordinal suffix ("th", "st", "nd", "rd") and check if remainder is numeric -/
private def isOrdinal (w : String) : Bool :=
  let suffixes := ["th", "st", "nd", "rd"]
  suffixes.any fun suf =>
    if w.endsWith suf && w.length > suf.length then
      let stem := w.toList.take (w.length - suf.length) |>.foldl String.push ""
      stem.toNat?.isSome
    else false

/-- Morphological fallback: guess POS from suffixes -/
private def morphologyGuess (word : String) : POS :=
  let w := word.toLower
  -- Numeric literals
  if w.toNat?.isSome then .num
  -- Ordinal numbers: "26th", "1st", "2nd", "3rd"
  else if isOrdinal w then .num
  -- Specific known plurals
  else if w == "rrs" then .nounPlural
  -- Suffix rules
  else if w.endsWith "ies" then .nounPlural
  -- Verb -s inflection: strip -es/-s and check if stem is a known verb
  else if w.endsWith "es" && w.length > 3 then
    let stem := (w.dropEnd 2).toString  -- "caches" → "cach"
    if knownVerbs.contains stem || knownVerbs.contains (stem ++ "e") then .verb
    else if !w.endsWith "ss" then .nounPlural
    else .noun
  else if w.endsWith "s" && !w.endsWith "ss" && w.length > 2 then
    let stem := (w.dropEnd 1).toString  -- "shows" → "show"
    if knownVerbs.contains stem then .verb
    else .nounPlural
  else if w.endsWith "ing" then .verbPart
  else if w.endsWith "ed" then .adj
  -- Comparative adjective: stem + -er where stem is known adj
  else if w.endsWith "er" && w.length > 3 then
    let stem := (w.dropEnd 2).toString   -- "larger" → "larg"
    let stemE := (w.dropEnd 1).toString  -- "closer" → "close"
    if knownAdjs.contains stem || knownAdjs.contains stemE ||
       knownAdjs.contains (stem ++ "e") then .adj
    else .noun
  -- Capitalized words (not at sentence start, but we don't track position — treat as propNoun)
  else if !word.isEmpty && word.toList[0]!.isUpper then .propNoun
  else .noun

/-- Context-sensitive disambiguation: resolve ambiguous words based on neighbors -/
private def disambiguate (tokens : Array Token) : Array Token := Id.run do
  let mut result := tokens
  for i in [:tokens.size] do
    let w := tokens[i]!.word.toLower
    -- "example" after "for" (case-insensitive) → retag both as discMarker
    if w == "example" && i > 0 && tokens[i - 1]!.word.toLower == "for" then
      result := result.set! (i - 1) { result[i - 1]! with pos := .discMarker }
      result := result.set! i { tokens[i]! with pos := .discMarker }
    -- "must"/"should"/"may" before copula/verb/adv → retag as adverb (modal
    -- modifier). "may" marks permission/partiality (RFC 2119-style): e.g.
    -- "It may be the case that the addresses are not available" (§5.3.3).
    else if (w == "should" || w == "must" || w == "may") then
      if i + 1 < tokens.size then
        let nextPos := result[i + 1]!.pos
        if nextPos == .copula || nextPos == .verb || nextPos == .adv then
          result := result.set! i { tokens[i]! with pos := .adv }
    -- "present" is always adj in RFC prose
    else if w == "present" then
      result := result.set! i { tokens[i]! with pos := .adj }
    -- nominal after infinitive "to" following "(un)able" or an
    -- infinitive-taking verb of refusal → verb
    -- ("unable to interpret the query", "refuses to perform the operation")
    else if (tokens[i]!.pos == .noun || tokens[i]!.pos == .nounPlural) && i >= 2 &&
            result[i - 1]!.word.toLower == "to" &&
            (result[i - 2]!.word.toLower == "unable" ||
             result[i - 2]!.word.toLower == "able" ||
             result[i - 2]!.word.toLower == "refuses" ||
             result[i - 2]!.word.toLower == "refuse") then
      result := result.set! i { tokens[i]! with pos := .verb }
    -- finite-verb form after "as" is a nominal complement ("returned as
    -- ANSWERS to a query"); participles stay verbal ("as described in")
    else if tokens[i]!.pos == .verb && i > 0 &&
            result[i - 1]!.word.toLower == "as" &&
            !tokens[i]!.word.toLower.endsWith "ed" &&
            !tokens[i]!.word.toLower.endsWith "ing" then
      result := result.set! i { tokens[i]! with
        pos := if tokens[i]!.word.toLower.endsWith "s" then .nounPlural else .noun }
    -- infinitive after the complementizer "whether" → verb
    -- ("considering whether to accept an RRSet")
    else if (tokens[i]!.pos == .noun || tokens[i]!.pos == .nounPlural) && i >= 2 &&
            result[i - 1]!.word.toLower == "to" &&
            result[i - 2]!.word.toLower == "whether" then
      result := result.set! i { tokens[i]! with pos := .verb }
    -- nominal after negated auxiliary "does not"/"do not" → verb
    -- ("does not support the requested kind of query")
    else if (tokens[i]!.pos == .noun || tokens[i]!.pos == .nounPlural) && i >= 2 &&
            result[i - 1]!.word.toLower == "not" &&
            (result[i - 2]!.word.toLower == "does" ||
             result[i - 2]!.word.toLower == "do") then
      result := result.set! i { tokens[i]! with pos := .verb }
    -- verb/verbPart immediately after a determiner — or after an adjective
    -- that itself follows a determiner/adjective ("a negative ANSWER") —
    -- sits in a noun slot: a -ed form followed by an adjective or nominal
    -- is a participial premodifier ("the cached negative response", "the
    -- specified operation") → adj; otherwise a nominal use ("the cache",
    -- "a negative answer") → noun (det can't govern verbs)
    else if (tokens[i]!.pos == .verb || tokens[i]!.pos == .verbPart) &&
            i > 0 && (result[i - 1]!.pos == .det ||
              (result[i - 1]!.pos == .adj && i > 1 &&
               (result[i - 2]!.pos == .det || result[i - 2]!.pos == .adj))) then
      let nextIsModifiable := i + 1 < tokens.size &&
        (result[i + 1]!.pos == .adj || result[i + 1]!.pos == .noun ||
         result[i + 1]!.pos == .nounPlural || result[i + 1]!.pos == .propNoun)
      if tokens[i]!.word.toLower.endsWith "ed" && nextIsModifiable then
        result := result.set! i { tokens[i]! with pos := .adj }
      else
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
    let pos :=
      -- tuple notation "<A, B>" is a nominal (composite-key literal)
      if t.word.startsWith "<" && t.word.endsWith ">" then .noun
      else if lexPos != .unknown then lexPos else morphologyGuess t.word
    tagged := tagged.set! i { t with pos := pos }
  -- Second pass: disambiguation
  tagged := disambiguate tagged
  return tagged

-- ============================================================
-- Stage 3: Phrase Chunker
-- ============================================================

private def isNominal (p : POS) : Bool :=
  p == .noun || p == .nounPlural || p == .propNoun || p == .num

private def isPreAdj (p : POS) : Bool :=
  p == .adj || p == .quant

/-- Try to parse a NounPhrase starting at position `pos`. Returns (NP, nextPos).
    When `absorbPP` is false, PPs are not absorbed as post-modifiers, leaving
    them available for clause-level parsing. -/
partial def parseNP (tokens : Array Token) (pos : Nat) (absorbPP : Bool := true)
    : Option (NounPhrase × Nat) := Id.run do
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

  -- Head noun (required — fallback: promote last quant preAdj as pronoun)
  if i >= tokens.size || !isNominal tokens[i]!.pos then
    -- Only promote quantifiers ("two", "three") as pronoun-like heads
    if !preAdjs.isEmpty && i > pos then
      let lastPreAdjPos := tokens[i - 1]!.pos
      if lastPreAdjPos == .quant then
        let head := preAdjs.back!
        preAdjs := preAdjs.pop
        let number : Number := .unknown
        let postMods : Array PostMod := #[]
        return some (⟨det, preAdjs, head, number, postMods⟩, i)
    return none
  let mut head := tokens[i]!.word
  let mut number : Number := match tokens[i]!.pos with
    | .nounPlural => .plural
    | .noun => .singular
    | _ => .unknown
  i := i + 1

  -- Compound nouns: absorb consecutive nominals, last one becomes head
  -- Break on pronouns: "the query it sent" → head="query", not "it"
  let isPronouns := fun (w : String) =>
    let wl := w.toLower
    wl == "it" || wl == "they" || wl == "them" || wl == "he" || wl == "she" || wl == "him" || wl == "her"
  while i < tokens.size && isNominal tokens[i]!.pos && !isPronouns tokens[i]!.word do
    preAdjs := preAdjs.push head
    head := tokens[i]!.word
    number := match tokens[i]!.pos with
      | .nounPlural => .plural
      | .noun => .singular
      | _ => number
    i := i + 1

  -- Skip compound "section" (e.g., "header section" → head is "header")
  if i < tokens.size && tokens[i]!.word.toLower == "section" then
    i := i + 1

  -- Post-modifiers: PPs, relative clauses, participial phrases
  let mut postMods : Array PostMod := #[]

  -- Helper: is this token a participial verb? (verb or verbPart that looks like a participle)
  let isParticipial := fun (t : Token) =>
    t.pos == .verbPart ||
    (t.pos == .verb && (t.word.toLower.endsWith "ing" || t.word.toLower.endsWith "ed")) ||
    (t.pos == .adj && t.word.toLower.endsWith "ed")

  -- Absorb PP only when requested (subject NPs absorb; object/PP-internal NPs don't)
  if absorbPP then
    -- Absorb chain of PPs
    while i < tokens.size && tokens[i]!.pos == .prep do
      let prep := tokens[i]!.word
      match parseNP tokens (i + 1) (absorbPP := false) with
      | some (ppNP, afterPPNP) =>
        postMods := postMods.push (.pp prep ppNP.toData)
        i := afterPPNP
      | none =>
        -- Fallback: absorb raw tokens until next boundary
        let mut ppWords : Array String := #[prep]
        i := i + 1
        while i < tokens.size &&
              tokens[i]!.pos != .verb && tokens[i]!.pos != .copula &&
              tokens[i]!.pos != .prep && tokens[i]!.pos != .conj &&
              tokens[i]!.pos != .punct && tokens[i]!.pos != .relPron do
          ppWords := ppWords.push tokens[i]!.word
          i := i + 1
        postMods := postMods.push (.raw (" ".intercalate ppWords.toList))

  -- Absorb relative clause: relPron + tokens until punct/end
  if i < tokens.size && tokens[i]!.pos == .relPron then
    let relPron := tokens[i]!.word
    let mut relWords : Array String := #[]
    i := i + 1
    while i < tokens.size && tokens[i]!.pos != .punct do
      relWords := relWords.push tokens[i]!.word
      i := i + 1
    postMods := postMods.push (.relClause relPron (" ".intercalate relWords.toList))

  -- Absorb participial phrase: verb/verbPart + object NP + PP chain
  if i < tokens.size && isParticipial tokens[i]! then
    let verb := tokens[i]!.word
    i := i + 1
    -- Try to parse object NP
    let (obj, afterObj) := match parseNP tokens i (absorbPP := false) with
      | some (objNP, afterObjNP) => (some objNP.toData, afterObjNP)
      | none => (none, i)
    i := afterObj
    -- Parse PP chain after object
    let mut partPPs : Array PPData := #[]
    for _ in [:tokens.size] do
      if i >= tokens.size || tokens[i]!.pos != .prep then break
      let prep := tokens[i]!.word
      match parseNP tokens (i + 1) (absorbPP := false) with
      | some (ppNP, afterPPNP) =>
        partPPs := partPPs.push ⟨prep, ppNP.toData⟩
        i := afterPPNP
      | none => break
    postMods := postMods.push (.participle verb obj partPPs)

  return some (⟨det, preAdjs, head, number, postMods⟩, i)

/-- Try to parse a VerbPhrase starting at position `pos`. -/
def parseVP (tokens : Array Token) (pos : Nat) : Option (VerbPhrase × Nat) := Id.run do
  if pos >= tokens.size then return none
  let mut i := pos

  -- Optional adverb(s) — keep last one (for negation: "should not" → "not")
  let mut adv : Option String := none
  while i < tokens.size && tokens[i]!.pos == .adv do
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

/-- Try to parse a PrepPhrase (preposition + NP) starting at position `pos`.
    PP-internal NPs do not absorb further PPs, keeping them available
    for clause-level parsing. -/
def parsePP (tokens : Array Token) (pos : Nat) : Option (PrepPhrase × Nat) :=
  if pos >= tokens.size || tokens[pos]!.pos != .prep then none
  else
    let prep := tokens[pos]!.word
    match parseNP tokens (pos + 1) (absorbPP := false) with
    | some (np, afterNP) => some (⟨prep, np⟩, afterNP)
    | none => none

/-- Parse a sequence of PrepPhrases starting at position `pos`. -/
def parsePPs (tokens : Array Token) (pos : Nat) : Array PrepPhrase × Nat := Id.run do
  let mut pps : Array PrepPhrase := #[]
  let mut i := pos
  for _ in [:tokens.size] do
    if let some (pp, afterPP) := parsePP tokens i then
      pps := pps.push pp
      i := afterPP
    else
      break
  return (pps, i)

-- ============================================================
-- Stage 4: Clause Extractor
-- ============================================================

/-- Parse a token sequence into a Clause.
    Tries SVO, SVPassive, SVAdj, NP-only, then unparsed. -/
def parseClause (tokens : Array Token) : Clause := Id.run do
  -- Filter out punctuation, discourse markers, and subordinating conjunctions
  let filtered := tokens.filter fun t =>
    t.pos != .punct && t.pos != .discMarker && t.pos != .subConj
  if filtered.isEmpty then return .unparsed ""

  -- Try NP + VP + ...
  if let some (np, afterNP) := parseNP filtered 0 then
    if let some (vp, afterVP) := parseVP filtered afterNP then
      -- Try SVO: NP + VP + NP (object NP doesn't absorb PPs)
      if let some (obj, afterObj) := parseNP filtered afterVP (absorbPP := false) then
        let (pps, _) := parsePPs filtered afterObj
        return .svo np vp obj pps
      -- Try passive: copula + past participle (verb or adj ending in "ed") + PPs
      if vp.isCopula && afterVP < filtered.size then
        let nextT := filtered[afterVP]!
        let isPassiveParticiple := nextT.pos == .verb ||
          (nextT.pos == .adj && nextT.word.toLower.endsWith "ed")
        if isPassiveParticiple then
          let participle := nextT.word
          let (pps, _) := parsePPs filtered (afterVP + 1)
          let negated := vp.adv == some "not" || vp.adv == some "never"
          return .svPassive np participle pps negated
      -- Try SVAdj: NP + VP(copula) + AdjP + PPs
      if vp.isCopula then
        if let some (adjP, afterAdj) := parseAdjP filtered afterVP then
          let (adjPPs, _) := parsePPs filtered afterAdj
          return .svAdj np vp adjP adjPPs
      -- Fallback: NP + VP + PPs (no object, e.g., "depends on 32 bit timers")
      let (pps, _) := parsePPs filtered afterVP
      let dummyObj : NounPhrase := ⟨none, #[], "", .unknown, #[]⟩
      return .svo np vp dummyObj pps
    -- NP-only fragment
    return .npOnly np

  return .unparsed (" ".intercalate (filtered.map (·.word)).toList)

/-- Parse a token sequence, trying clause parses from multiple positions.
    Tries position 0 first (handles sentences without leading determiners),
    then from each determiner position > 0 (handles diagram artifacts and
    conjuncts). Falls back to npOnly or unparsed if none found. -/
def parseClauses (tokens : Array Token) : Array Clause := Id.run do
  let filtered := tokens.filter fun t =>
    t.pos != .punct && t.pos != .discMarker && t.pos != .subConj
  if filtered.isEmpty then return #[.unparsed ""]

  let mut clauses : Array Clause := #[]

  -- Helper: try full clause parse from a given start position
  let tryFrom := fun (startPos : Nat)
      (cs : Array Clause) => Id.run do
    let mut result := cs
    if let some (np, afterNP) := parseNP filtered startPos then
      if let some (vp, afterVP) := parseVP filtered afterNP then
        -- Try SVO
        if let some (obj, afterObj) := parseNP filtered afterVP (absorbPP := false) then
          let (pps, _) := parsePPs filtered afterObj
          result := result.push (.svo np vp obj pps)
        else if vp.isCopula then
          -- Try passive: copula + past participle (verb or adj ending in "ed")
          if afterVP < filtered.size then
            let nextT := filtered[afterVP]!
            let isPassiveParticiple := nextT.pos == .verb ||
              (nextT.pos == .adj && nextT.word.toLower.endsWith "ed")
            if isPassiveParticiple then
              let participle := nextT.word
              let (pps, _) := parsePPs filtered (afterVP + 1)
              let negated := vp.adv == some "not" || vp.adv == some "never"
              result := result.push (.svPassive np participle pps negated)
          if result.size == cs.size then  -- no passive match → try SVAdj
            if let some (adjP, afterAdj) := parseAdjP filtered afterVP then
              let (adjPPs, _) := parsePPs filtered afterAdj
              result := result.push (.svAdj np vp adjP adjPPs)
        else
          -- Fallback: NP + VP + PPs (no object, e.g., "depends on X")
          let (pps, _) := parsePPs filtered afterVP
          if !pps.isEmpty then
            let dummyObj : NounPhrase := ⟨none, #[], "", .unknown, #[]⟩
            result := result.push (.svo np vp dummyObj pps)
    return result

  -- Try from position 0 (handles sentences starting without a determiner)
  clauses := tryFrom 0 clauses

  -- Try from each later determiner position (handles diagram artifacts, conjuncts)
  for startPos in [1:filtered.size] do
    if filtered[startPos]!.pos != .det then continue
    clauses := tryFrom startPos clauses

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

/-- Extract protocol qualifier from subject's postMods (e.g., "carried by UDP" → "UDP") -/
def extractProtocolQualifier (subj : NounPhrase) : Option String :=
  subj.postMods.findSome? fun pm => match pm with
    | .participle _ _ pps =>
      pps.findSome? fun pp =>
        if pp.prep.toLower == "by" || pp.prep.toLower == "over" || pp.prep.toLower == "using" then
          some pp.np.head
        else none
    | .pp prep npd =>
      if prep.toLower == "by" || prep.toLower == "over" || prep.toLower == "using" then
        some npd.head
      else none
    | _ => none

/-- Extract bit width from NP text like "two byte" → 16, "two octet" → 16. -/
def extractBitWidthFromNPText (words : Array String) : Option Nat := Id.run do
  for i in [:words.size] do
    let w := words[i]!.toLower
    if i + 1 < words.size then
      let next := words[i + 1]!.toLower
      if next.startsWith "byte" || next.startsWith "octet" then
        if let some n := w.toNat? then return some (n * 8)
        match w with
        | "one" => return some 8
        | "two" => return some 16
        | "three" => return some 24
        | "four" => return some 32
        | _ => pure ()
      if next.startsWith "bit" then
        if let some n := w.toNat? then return some n
        match w with
        | "one" => return some 1
        | "two" => return some 2
        | "eight" => return some 8
        | "sixteen" => return some 16
        | _ => pure ()
  return none

/-- Derive a SectionProp from a parsed Clause and field name. -/
def deriveSectionProp (_fieldName : String) (clause : Clause) : SectionProp := Id.run do
  match clause with
  | .svAdj _subj vp comp _ =>
    if vp.isCopula && comp.adj.toLower == "present" then
      return .alwaysPresent
    else return .unclassified ""
  | .svo _subj vp obj pps =>
    let v := vp.verb.toLower
    if v == "contains" || v == "includes" || v == "have" || v == "has" then
      if isStructuralNoun obj.head then
        return .containsFields
      else if obj.number == .plural then
        return .containsPlural obj.head
      else if obj.head.toLower == "list" then
        return .possiblyEmptyList
      else
        return .unclassified ""
    else if v == "expressed" then
      -- Active: "expressed NP in terms of a sequence of X"
      -- Check clause-level PPs for "sequence of X"
      for i in [:pps.size] do
        if pps[i]!.np.head.toLower == "sequence" then
          if i + 1 < pps.size then
            return .structField pps[i + 1]!.np.head true
      return .unclassified ""
    else
      return .unclassified ""
  | .svPassive subj participle pps _ =>
    let p := participle.toLower
    if p == "expressed" then
      -- "X are expressed in terms of a sequence of Y"
      -- PP chain: in(terms), of(a sequence), of(Y)
      for i in [:pps.size] do
        let pp := pps[i]!
        -- Check if this PP's NP head is "sequence"
        if pp.np.head.toLower == "sequence" then
          if i + 1 < pps.size then
            return .structField pps[i + 1]!.np.head true
        -- Also check NP postMods for "sequence" (when PP absorption captured it)
        let hasSequence := pp.np.postMods.any fun m => match m with
          | .raw t => hasSub t.toLower "sequence"
          | .pp _ npd => npd.head.toLower == "sequence"
          | _ => false
        if hasSequence then
          if i + 1 < pps.size then
            return .structField pps[i + 1]!.np.head true
      return .unclassified ""
    else return .unclassified ""
  | .npOnly np =>
    -- Check postMods for participial phrases with semantic content
    for pm in np.postMods do
      match pm with
      | .participle verb (some obj) pps =>
        let v := verb.toLower
        -- "specifying/specifies the number of entries in X" → countsEntriesIn
        if (v == "specifying" || v == "specifies") && obj.head.toLower == "number" then
          -- Look for "of" PP (what's being counted) and "in" PP (which section)
          let hasOfEntries := pps.any fun pp =>
            pp.prep.toLower == "of" &&
            (pp.np.head.toLower == "entries" || pp.np.head.toLower == "records")
          if hasOfEntries then
            for pp in pps do
              if pp.prep.toLower == "in" then
                -- Build section name from preAdjs + head
                let sectionWords := pp.np.preAdjs ++ #[pp.np.head]
                let sectionName := " ".intercalate (sectionWords.map (·.toLower)).toList
                return .countsEntriesIn sectionName
        -- "represented as a sequence of labels" → domainNameField
        if v == "represented" then
          let asSequence := pps.any fun pp =>
            pp.prep.toLower == "as" && pp.np.head.toLower == "sequence"
          if asSequence then
            return .domainNameField
      | .participle verb none pps =>
        let v := verb.toLower
        if v == "represented" then
          let asSequence := pps.any fun pp =>
            pp.prep.toLower == "as" && pp.np.head.toLower == "sequence"
          if asSequence then
            return .domainNameField
      | _ => pure ()
    -- Check if NP itself is "domain name" (preAdjs + head)
    if np.preAdjs.any (·.toLower == "domain") && np.head.toLower == "name" then
      if np.postMods.any fun pm => match pm with
        | .participle _ _ _ => true
        | _ => false
      then return .domainNameField
    if np.number == .plural then
      return .pluralHead np.head
    else
      return .unclassified ""
  | .unparsed text => return .unclassified text

-- ============================================================
-- Stage 6: Sentence Relevance
-- ============================================================

/-- Extract searchable text from a PostMod -/
private def postModText : PostMod → String
  | .pp _prep npd => npd.head
  | .relClause _ text => text
  | .participle verb _ _ => verb
  | .raw text => text

/-- Check if a clause refers to a given field name.
    Subject head matches field name, or field name appears in preAdjs or postMods. -/
def clauseRefersTo (fieldName : String) (clause : Clause) : Bool :=
  let fnLower := fieldName.toLower
  let npMatches (np : NounPhrase) : Bool :=
    np.head.toLower == fnLower ||
    np.preAdjs.any (·.toLower == fnLower) ||
    -- Handle "the additional records section" matching "Additional"
    (np.det.isSome && np.preAdjs.any (·.toLower == fnLower)) ||
    -- Check postMods for field name references
    np.postMods.any (fun pm => hasSub (postModText pm).toLower fnLower)
  match clause with
  | .svo subj _ _ _ => npMatches subj
  | .svAdj subj _ _ _ => npMatches subj
  | .svPassive subj _ _ _ => npMatches subj
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

  -- 4. Partitive relative predicating emptiness over the members
  --    ("... sections (some of which are empty ...)"): quantifier + "of" +
  --    relative pronoun + copula + adjective "empty"
  for part in allParts do
    let tokens := tagPOS (tokenize part)
    for i in [:tokens.size] do
      if i + 4 < tokens.size &&
          tokens[i]!.pos == .quant &&
          tokens[i + 1]!.pos == .prep && tokens[i + 1]!.word.toLower == "of" &&
          tokens[i + 2]!.pos == .relPron &&
          tokens[i + 3]!.pos == .copula &&
          tokens[i + 4]!.word.toLower == "empty" then
        if !props.contains .someEmpty then
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

/-- Strip parenthetical expressions from text before parsing. -/
private def stripParentheticals (text : String) : String := Id.run do
  let mut result := ""
  let mut depth : Nat := 0
  for c in text.toList do
    if c == '(' then depth := depth + 1
    else if c == ')' then
      if depth > 0 then depth := depth - 1
    else if depth == 0 then result := result.push c
  return result

/-- Analyze prose text using the full NLP pipeline.
    Strips parentheticals, splits into sentences, then runs each through
    POS tagging → clause parsing → semantic derivation. -/
def analyzeProse (prose : String) : Array SectionProp := Id.run do
  let mut props : Array SectionProp := #[]
  let cleaned := stripParentheticals prose
  -- Split into sentences on ". " and "; "
  let proseParts := cleaned.splitOn ". "
  let mut allParts : Array String := #[]
  for part in proseParts do
    let subParts := part.splitOn "; "
    for sp in subParts do
      let t := trim sp
      if !t.isEmpty then
        allParts := allParts.push t
  -- Parse each sentence through the full pipeline
  for part in allParts do
    let tokens := tagPOS (tokenize part)
    let clauses := parseClauses tokens
    for clause in clauses do
      let prop := deriveSectionProp "" clause
      match prop with
      | .unclassified _ => pure ()
      | _ =>
        -- Deduplicate: multi-position parsing can produce identical props
        if !props.contains prop then
          props := props.push prop
  return props

/-- Derive structure fields from prose text using the full NLP pipeline.
    Tokenizes, POS-tags, parses into SVO/passive clauses, then extracts
    `structField` properties from the semantic derivation. -/
def deriveStructFields (prose : String) : Array (String × Bool) := Id.run do
  let props := analyzeProse prose
  let mut result : Array (String × Bool) := #[]
  for prop in props do
    match prop with
    | .structField name isArr => result := result.push (name, isArr)
    | _ => pure ()
  return result

/-- Parse prose text into raw Clauses using the full NLP pipeline,
    pairing each clause with the source sentence fragment it was parsed
    from (parenthetical-stripped, trimmed). Used to link generated props
    back to their RFC text positions for hover support.
    Strips parentheticals, splits sentences, tokenizes + POS tags + parseClauses.
    Deduplicates and filters out `.unparsed` clauses. -/
def parseProseClausesWithSrc (prose : String) : Array (Clause × String) := Id.run do
  let mut result : Array (Clause × String) := #[]
  let cleaned := stripParentheticals prose
  let proseParts := cleaned.splitOn ". "
  let mut allParts : Array String := #[]
  for part in proseParts do
    let subParts := part.splitOn "; "
    for sp in subParts do
      let t := trim sp
      if !t.isEmpty then
        allParts := allParts.push t
  for part in allParts do
    let tokens := tagPOS (tokenize part)
    let clauses := parseClauses tokens
    for clause in clauses do
      match clause with
      | .unparsed _ => pure ()
      | _ =>
        -- Deduplicate via Repr (structural equality)
        let r := reprStr clause
        let isDup := result.any fun (c, _) => reprStr c == r
        if !isDup then
          result := result.push (clause, part)
  return result

/-- Parse prose text into raw Clauses using the full NLP pipeline.
    Strips parentheticals, splits sentences, tokenizes + POS tags + parseClauses.
    Deduplicates and filters out `.unparsed` clauses. -/
def parseProseClauses (prose : String) : Array Clause :=
  (parseProseClausesWithSrc prose).map (·.1)

/-- Parse algorithm prose into ConditionalClauses, preserving if/when structure,
    pairing each clause with the source sentence fragment it was parsed from
    (for hover support). Unlike parseProseClauses which filters out subConj
    tokens, this function detects conditional sentences and splits them into
    guard/body pairs. -/
def parseAlgorithmClausesWithSrc (prose : String) : Array (ConditionalClause × String) := Id.run do
  let mut result : Array (ConditionalClause × String) := #[]
  let cleaned := stripParentheticals prose
  let proseParts := cleaned.splitOn ". "
  let mut allParts : Array String := #[]
  for part in proseParts do
    let subParts := part.splitOn "; "
    for sp in subParts do
      let t := trim sp
      if !t.isEmpty then
        allParts := allParts.push t
  for part in allParts do
    let tokens := tagPOS (tokenize part)
    let hasSubConj := tokens.any (·.pos == .subConj)
    if hasSubConj then
      -- Find the subConj position
      let mut subConjIdx : Option Nat := none
      for i in [:tokens.size] do
        if tokens[i]!.pos == .subConj then
          subConjIdx := some i
          break
      if let some sci := subConjIdx then
        -- Check if postposed: subConj appears after a verb (not at sentence start)
        let beforeConj := tokens.extract 0 sci
        let isPostposed : Bool := (sci > 0) && (beforeConj.any fun t =>
          t.pos == .verb || t.pos == .copula)
        -- Split at comma (depth-aware) in the tokens after subConj
        let afterConj := tokens.extract (sci + 1) tokens.size
        let mut splitIdx : Option Nat := none
        let mut depth : Nat := 0
        for i in [:afterConj.size] do
          let t := afterConj[i]!
          if t.word == "(" then depth := depth + 1
          else if t.word == ")" then
            if depth > 0 then depth := depth - 1
          else if t.word == "," && depth == 0 then
            splitIdx := some i
            break
        match splitIdx with
        | some si =>
          -- Preposed conditional: "if X, Y"
          let guardTokens := afterConj.extract 0 si
          let mut bodyTokens := afterConj.extract (si + 1) afterConj.size
          -- Strip leading "then"/"and"/"so" connectors from body
          if bodyTokens.size > 0 && (bodyTokens[0]!.pos == .adv || bodyTokens[0]!.pos == .conj) &&
             (bodyTokens[0]!.word.toLower == "then" || bodyTokens[0]!.word.toLower == "and" ||
              bodyTokens[0]!.word.toLower == "so") then
            bodyTokens := bodyTokens.extract 1 bodyTokens.size
          let guard := parseClause guardTokens
          let body := parseClause bodyTokens
          match guard, body with
          | .unparsed _, _ => pure ()
          | _, .unparsed _ => pure ()
          | _, _ => result := result.push (.conditional guard body, part)
        | none =>
          if isPostposed then
            -- Postposed: "cache the data if its TTL > 0"
            -- beforeConj = body, afterConj = guard
            let guard := parseClause afterConj
            let body := parseClause beforeConj
            match guard, body with
            | .unparsed _, _ => pure ()
            | _, .unparsed _ => pure ()
            | _, _ => result := result.push (.conditional guard body, part)
          else
            -- No comma and not postposed — parse whole thing as simple
            let clauses := parseClauses tokens
            for clause in clauses do
              match clause with
              | .unparsed _ => pure ()
              | _ => result := result.push (.simple clause, part)
    else
      -- No conditional — parse normally
      let clauses := parseClauses tokens
      for clause in clauses do
        match clause with
        | .unparsed _ => pure ()
        | _ => result := result.push (.simple clause, part)
  return result

/-- Parse a sentence into a Clause via the full NLP pipeline.
    Runs tokenize → POS tag → clause parse. -/
def parseSentenceClause (sentence : String) : Clause :=
  let tokens := tagPOS (tokenize sentence)
  parseClause tokens

/-- Parse a field description into Clauses via the full NLP pipeline.
    Splits on sentence boundaries, then runs each through
    tokenize → POS tag → clause parse. -/
def parseDescriptionClauses (desc : String) : Array Clause :=
  (Property.splitSentences desc).map parseSentenceClause

/-- Is this word a third-person object pronoun (anaphor)? -/
private def isObjectPronoun (w : String) : Bool :=
  let wl := w.toLower
  wl == "it" || wl == "them" || wl == "they"

/-- Verb particles: closed-class function words that combine with a verb into
    a phrasal verb ("set up", "look out"). After a clause-initial verb they
    belong to the verb, not the object NP. -/
private def isVerbParticle (w : String) : Bool :=
  let wl := w.toLower
  wl == "up" || wl == "out" || wl == "off" || wl == "down" || wl == "away"

/-- Parse an imperative clause ("return it to the client"): verb-first, no
    surface subject. An object pronoun resolves to `antecedent` (the NP it
    refers back to). A verb particle right after the verb attaches to the
    verb phrase ("Set up their addresses" — object starts at "their").
    Returns an svo clause with an empty understood subject. -/
def parseImperativeClause (tokens : Array Token) (antecedent : NounPhrase)
    : Option Clause := Id.run do
  let filtered := tokens.filter fun t =>
    t.pos != .punct && t.pos != .discMarker && t.pos != .subConj
  if filtered.isEmpty then return none
  let t0 := filtered[0]!
  if t0.pos != .verb then return none
  -- Phrasal verb: absorb a particle into the VP
  let (vp, objStart) : VerbPhrase × Nat :=
    if filtered.size > 1 && isVerbParticle filtered[1]!.word then
      (⟨none, t0.word ++ " " ++ filtered[1]!.word, false⟩, 2)
    else (⟨none, t0.word, false⟩, 1)
  -- Object: a pronoun is an anaphor for the antecedent; otherwise a full NP
  let (obj, afterObj) :=
    if filtered.size > objStart && isObjectPronoun filtered[objStart]!.word then
      (antecedent, objStart + 1)
    else match parseNP filtered objStart (absorbPP := false) with
      | some (np, after) => (np, after)
      | none => (⟨none, #[], "", .unknown, #[]⟩, objStart)
  let (pps, _) := parsePPs filtered afterObj
  let emptySubj : NounPhrase := ⟨none, #[], "", .unknown, #[]⟩
  return some (.svo emptySubj vp obj pps)

/-- Parse an imperative step with an anaphoric conditional:
    "See if `<condition>`, and if so `<action>`."
    The "if" after the imperative verb is a complementizer introducing the
    condition clause; "so" in "if so" is an anaphor for that condition; an
    object pronoun in the action resolves to the condition's subject.
    Returns (condition, action). -/
def parseIfSoStep (desc : String) : Option (Clause × Clause) := Id.run do
  let tokens := tagPOS (tokenize desc)
  -- Locate the anaphoric "if so"
  let mut ifSoIdx : Option Nat := none
  for i in [:tokens.size] do
    if tokens[i]!.word.toLower == "if" && i + 1 < tokens.size &&
        tokens[i + 1]!.word.toLower == "so" then
      ifSoIdx := some i
  let some isi := ifSoIdx | return none
  -- Condition: after the first complementizer "if" (not the "if so" one),
  -- up to (excluding) the connectors before "if so"
  let mut condStart : Option Nat := none
  for i in [:isi] do
    if tokens[i]!.word.toLower == "if" then
      condStart := some (i + 1)
      break
  let some cs := condStart | return none
  if cs > isi then return none
  let mut condEnd := isi
  -- Drop trailing connector tokens (",", "and") before "if so"
  while condEnd > cs &&
      (tokens[condEnd - 1]!.word == "," || tokens[condEnd - 1]!.word.toLower == "and") do
    condEnd := condEnd - 1
  let cond := parseClause (tokens.extract cs condEnd)
  let condSubj? : Option NounPhrase := match cond with
    | .svo subj _ _ _ => some subj
    | .svAdj subj _ _ _ => some subj
    | .svPassive subj _ _ _ => some subj
    | _ => none
  let some condSubj := condSubj? | return none
  -- Action: the imperative clause after "if so"
  let some act := parseImperativeClause (tokens.extract (isi + 2) tokens.size) condSubj
    | return none
  return some (cond, act)

/-- Superlative ranking poles and their polarity: `true` = the high end
    (most trustworthy / greatest / best), `false` = the low end. Lexical,
    POS-independent — used to read the direction of an ordering range. -/
def superlativePole (w : String) : Option Bool :=
  match w.toLower with
  | "most" | "highest" | "greatest" | "best" => some true
  | "least" | "lowest" | "worst" | "fewest" => some false
  | _ => none

/-- Detect an ordering directive of the form "… from ⟨pole⟩ … to ⟨pole⟩ …"
    (e.g. "in order from most to least"). Returns `some true` when the range
    runs high→low (the first listed item is the most/greatest end, so list
    position 0 is the top rank), `some false` for low→high, and `none` when
    there is no such directive. The poles are recognized lexically and the
    "from … to …" frame structurally, so "from least to most" or "from
    highest to lowest" parse equally — nothing is keyed on a fixed phrase. -/
def parseOrderingDirective (tokens : Array Token) : Option Bool := Id.run do
  let mut poles : Array (Nat × Bool) := #[]
  for i in [:tokens.size] do
    if let some p := superlativePole tokens[i]!.word then
      poles := poles.push (i, p)
  if poles.size < 2 then return none
  let (i1, pole1) := poles[0]!
  let (i2, _) := poles[1]!
  let mut hasFrom := false
  for j in [:i1] do
    if tokens[j]!.word.toLower == "from" then hasFrom := true
  let mut hasTo := false
  for j in [i1 + 1 : i2] do
    if tokens[j]!.word.toLower == "to" then hasTo := true
  if hasFrom && hasTo then return some pole1
  return none

/-- Numeral value of a token word: digit strings ("68") or the word
    numerals the tagger marks `.quant` ("three"). -/
def numeralValue (w : String) : Option Nat :=
  match w.toNat? with
  | some n => some n
  | none =>
    match w.toLower with
    | "zero" => some 0 | "one" => some 1 | "two" => some 2
    | "three" => some 3 | "four" => some 4 | "five" => some 5
    | "six" => some 6 | "seven" => some 7 | "eight" => some 8
    | "nine" => some 9 | "ten" => some 10
    | _ => none

/-- Seconds denoted by a time-unit noun ("hour"/"hours" → 3600). -/
def timeUnitSeconds (w : String) : Option Nat :=
  let lw := w.toLower
  let base := if lw.endsWith "s" then (lw.dropEnd 1).toString else lw
  match base with
  | "week" => some 604800
  | "day" => some 86400
  | "hour" => some 3600
  | "minute" => some 60
  | "second" => some 1
  | "year" => some 31536000
  | _ => none

/-- Parse a duration (range) at `pos`: ⟨numeral⟩ [to ⟨numeral⟩] ⟨time-unit⟩.
    Numerals are `.quant`/`.num` tokens (word or digit numerals), the unit
    a nominal time noun: "one to three hours" → (3600, 10800, next). A
    single "⟨numeral⟩ ⟨unit⟩" duration yields lo = hi. The range frame is
    structural (numeral – "to" – numeral – unit), not keyed on any fixed
    phrase. -/
def parseDurationRange (tokens : Array Token) (pos : Nat) :
    Option (Nat × Nat × Nat) := Id.run do
  let isNumeral := fun (t : Token) =>
    (t.pos == .quant || t.pos == .num) && (numeralValue t.word).isSome
  let some t0 := tokens[pos]? | return none
  unless isNumeral t0 do return none
  let some lo := numeralValue t0.word | return none
  let mut hi := lo
  let mut uPos := pos + 1
  -- "to ⟨numeral⟩": a bounded range between the two values
  if let some tTo := tokens[pos + 1]? then
    if tTo.word.toLower == "to" then
      if let some t2 := tokens[pos + 2]? then
        if isNumeral t2 then
          hi := (numeralValue t2.word).getD lo
          uPos := pos + 3
  let some tu := tokens[uPos]? | return none
  unless tu.pos == .noun || tu.pos == .nounPlural do return none
  let some mult := timeUnitSeconds tu.word | return none
  return some (lo * mult, hi * mult, uPos + 1)

-- ============================================================
-- Example sentence analysis
-- ============================================================

/-- Fuzzy match a token against struct field names (prefix/substring/case-insensitive). -/
private def resolveFieldName (token : String) (fieldNames : Array String) : Option String :=
  let t := token.toLower
  -- Exact match (case-insensitive)
  match fieldNames.find? (fun f => f.toLower == t) with
  | some f => some f
  | none =>
    -- Prefix match: token is a prefix of some field name
    match fieldNames.find? (fun f => f.toLower.startsWith t && t.length >= 3) with
    | some f => some f
    | none =>
      -- Substring match: token appears in some field name
      fieldNames.find? (fun f => hasSub f.toLower t && t.length >= 3)

/-- Parse antecedent tokens: match NOUN = NOUN ( NUM ) pattern.
    Returns a predicate like `fieldEq "protocol" 6`. -/
private def parseAntecedent (tokens : Array Token) (fieldNames : Array String) : ExamplePred :=
  Id.run do
  -- Look for pattern: propNoun = propNoun ( num )
  -- Find the = sign
  let mut eqIdx : Option Nat := none
  for i in [:tokens.size] do
    if tokens[i]!.word == "=" && tokens[i]!.pos == .punct then
      eqIdx := some i
      break
  let some ei := eqIdx | return .unresolved "no assignment"
  -- Field name: propNoun before =
  if ei == 0 then return .unresolved "no field before ="
  let fieldToken := tokens[ei - 1]!.word
  -- Look for numeric value in parentheses after =
  let mut numVal : Option Nat := none
  for i in [ei + 1:tokens.size] do
    if tokens[i]!.pos == .num then
      numVal := tokens[i]!.word.toLower.toNat?
      break
  let some nv := numVal | return .unresolved s!"no numeric value after {fieldToken}="
  -- Resolve field name
  let resolved := resolveFieldName fieldToken fieldNames
  let field := resolved.getD fieldToken.toLower
  return .fieldEq field nv

/-- Parse consequent tokens: extract field reference + numeric value.
    Returns a predicate like `fieldAccess "bitMap" 25`. -/
private def parseConsequent (tokens : Array Token) (fieldNames : Array String) : ExamplePred :=
  Id.run do
  -- Find noun heads and resolve against field names
  let mut resolvedField : Option String := none
  for t in tokens do
    if t.pos == .noun || t.pos == .nounPlural || t.pos == .propNoun then
      match resolveFieldName t.word fieldNames with
      | some f => resolvedField := some f; break
      | none => continue
  -- Extract numeric values from consequent
  let mut numVal : Option Nat := none
  for t in tokens do
    if t.pos == .num then
      -- Skip ordinals (like "26th") — they describe position, not target value
      if isOrdinal t.word.toLower then continue
      numVal := t.word.toLower.toNat?
      break
  match resolvedField, numVal with
  | some f, some n => .fieldAccess f n
  | some f, none => .fieldAccess f 0
  | none, _ =>
    let text := " ".intercalate (tokens.map (·.word)).toList
    .unresolved text

/-- Analyze example sentences in text, returning semantic propositions.
    Takes struct field names for resolution against field references. -/
def analyzeExamples (text : String) (fieldNames : Array String) : Array ExampleProp := Id.run do
  let mut results : Array ExampleProp := #[]
  -- Split into sentences on ". "
  let sentences := text.splitOn ". "
  for sentence in sentences do
    let sent := trim sentence
    if sent.isEmpty then continue
    let tokens := tagPOS (tokenize sent)
    -- Check for discourse markers
    let hasDiscMarker := tokens.any (·.pos == .discMarker)
    if !hasDiscMarker then continue
    -- Find subordinating conjunction ("if", "when") → conditional example
    let hasSubConj := tokens.any (·.pos == .subConj)
    if !hasSubConj then continue
    -- Skip discourse markers and punctuation at start
    let mut startIdx : Nat := 0
    for i in [:tokens.size] do
      if tokens[i]!.pos == .discMarker || tokens[i]!.pos == .punct then
        startIdx := i + 1
      else break
    -- Find the subConj position
    let mut subConjIdx : Option Nat := none
    for i in [startIdx:tokens.size] do
      if tokens[i]!.pos == .subConj then
        subConjIdx := some i
        break
    let some sci := subConjIdx | continue
    -- Split into antecedent and consequent at comma (paren-depth aware)
    let afterConj := tokens.extract (sci + 1) tokens.size
    let mut splitIdx : Option Nat := none
    let mut depth : Nat := 0
    for i in [:afterConj.size] do
      let t := afterConj[i]!
      if t.word == "(" then depth := depth + 1
      else if t.word == ")" then
        if depth > 0 then depth := depth - 1
      else if t.word == "," && depth == 0 then
        splitIdx := some i
        break
    let some si := splitIdx | continue
    let antTokens := afterConj.extract 0 si
    let consTokens := afterConj.extract (si + 1) afterConj.size
    let ante := parseAntecedent antTokens fieldNames
    let cons := parseConsequent consTokens fieldNames
    results := results.push (.conditional ante cons)
  return results

-- ============================================================
-- Typeclass derivation helpers
-- ============================================================

/-- Re-parse a relative clause's text into Clauses.
    The text comes after the relative pronoun, so may start with a verb.
    Prepends "it" as implicit subject when text starts with a verb.
    Also splits coordinated objects: "describes X and Y" → two SVO clauses.
    "stores the results from previous responses" → SVO clause -/
def reparseRelClause (text : String) : Array Clause := Id.run do
  -- Try parsing as-is first
  let tokens := tagPOS (tokenize text)
  let mut usedTokens := tokens
  let mut clauses := parseClauses tokens |>.filter fun c =>
    match c with | .unparsed _ => false | _ => true
  -- If nothing parsed, prepend implicit subject "it" for verb-first relative clauses
  if clauses.isEmpty then
    let tokens' := tagPOS (tokenize ("it " ++ text))
    usedTokens := tokens'
    clauses := parseClauses tokens' |>.filter fun c =>
      match c with | .unparsed _ => false | _ => true
  -- Post-process: split coordinated objects in SVO clauses at TOKEN level:
  -- a conjunction "and" right after the parsed object introduces another
  -- object of the same verb ("describes X and Y" → two SVO clauses)
  let mut expanded : Array Clause := #[]
  for clause in clauses do
    expanded := expanded.push clause
    match clause with
    | .svo subj vp _ _ =>
      if let some vi := usedTokens.findIdx?
          (fun t => t.word.toLower == vp.verb.toLower) then
        if let some (_, afterObj) := parseNP usedTokens (vi + 1) (absorbPP := false) then
          let mut pos := afterObj
          while pos + 1 < usedTokens.size && usedTokens[pos]!.pos == .conj &&
              usedTokens[pos]!.word.toLower == "and" do
            match parseNP usedTokens (pos + 1) (absorbPP := false) with
            | some (np2, after2) =>
              expanded := expanded.push (.svo subj vp np2 #[])
              pos := after2
            | none => pos := usedTokens.size
    | _ => pure ()
  return expanded

-- ============================================================
-- Debug rendering (for the #naturallanguage command)
-- ============================================================

/-- Short POS tag for debug rendering. -/
def POS.short : POS → String
  | .det => "DET" | .noun => "N" | .nounPlural => "Ns" | .propNoun => "PN"
  | .verb => "V" | .verbPart => "Vp" | .copula => "COP" | .adj => "ADJ"
  | .adv => "ADV" | .prep => "P" | .conj => "CONJ" | .relPron => "REL"
  | .punct => "·" | .quant => "Q" | .num => "NUM" | .discMarker => "DM"
  | .subConj => "SUB" | .unknown => "?"

def NPData.render (np : NPData) : String :=
  let det := match np.det with | some d => d ++ " " | none => ""
  let pre := String.join (np.preAdjs.toList.map (· ++ " "))
  let num := match np.number with
    | .plural => "/pl" | .singular => "/sg" | .unknown => ""
  s!"⟨{det}{pre}{np.head}{num}⟩"

def PostMod.render : PostMod → String
  | .pp prep np => s!"PP({prep} {np.render})"
  | .relClause pron text => s!"Rel({pron} \"{text}\")"
  | .participle v obj pps =>
    let o := match obj with | some np => " " ++ np.render | none => ""
    let ps := String.join (pps.toList.map fun pp => s!" PP({pp.prep} {pp.np.render})")
    s!"Part({v}{o}{ps})"
  | .raw text => s!"Raw(\"{text}\")"

def NounPhrase.render (np : NounPhrase) : String :=
  let base := NPData.render np.toData
  if np.postMods.isEmpty then base
  else base ++ String.join (np.postMods.toList.map fun pm => " " ++ pm.render)

def VerbPhrase.render (vp : VerbPhrase) : String :=
  let adv := match vp.adv with | some a => a ++ " " | none => ""
  s!"{adv}{vp.verb}{if vp.isCopula then "[cop]" else ""}"

def Clause.render : Clause → String
  | .svo subj vp obj pps =>
    let ps := String.join (pps.toList.map fun pp => s!" + PP({pp.prep} {pp.np.render})")
    s!"SVO {subj.render} · {vp.render} · {obj.render}{ps}"
  | .svAdj subj vp comp pps =>
    let ps := String.join (pps.toList.map fun pp => s!" + PP({pp.prep} {pp.np.render})")
    let adv := match comp.adv with | some a => a ++ " " | none => ""
    s!"SVAdj {subj.render} · {vp.render} · [{adv}{comp.adj}]{ps}"
  | .svPassive subj part pps negated =>
    let ps := String.join (pps.toList.map fun pp => s!" + PP({pp.prep} {pp.np.render})")
    s!"SVPassive{if negated then "(neg)" else ""} {subj.render} · {part}{ps}"
  | .npOnly np => s!"NP {np.render}"
  | .unparsed text => s!"unparsed \"{text}\""

end VeriDNS.RFC.NLP
