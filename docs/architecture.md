# Architecture

## Module Structure

```
VeriDNS/
  RFC/
    Parser.lean          -- RFC text extraction (line ranges, page break stripping)
    Property.lean        -- Sentence splitting and byte-position tracking utilities
    NLP.lean             -- SVO sentence parser, semantic derivation, example analysis
    PropRules.lean       -- Declarative property rule framework (PropSpec expression trees + DSL)
    Macro.lean           -- include_rfc compile-time command macro
    Syntax.lean          -- Code generation: structures, enums, formal Props from RFC text
  Spec/           -- Formal specifications derived from RFC text
    Header.lean   -- RFC 1035 section 4.1.1: DNS header format
    Question.lean -- RFC 1035 section 4.1.2: Question section format
    ResourceRecord.lean -- RFC 1035 section 4.1.3: Resource record format
    Compression.lean    -- RFC 1035 section 4.1.4: Message compression
    DomainName.lean     -- RFC 1035 section 3.1:   Name space definitions
    Message.lean  -- RFC 1035 section 4.1:   Message format (section diagram)
    RRType.lean   -- RFC 1035 section 3.2.2-3: TYPE and QTYPE values
    RRClass.lean  -- RFC 1035 section 3.2.4-5: CLASS and QCLASS values
    RData.lean    -- RFC 1035 sections 3.3-3.4: RDATA formats (16 types)
    Transport.lean -- RFC 1035 section 4.2: UDP/TCP transport constraints
    Cache.lean    -- RFC 1034 §5.3.2 + RFC 1035 §7.4, §6.1.3: Cache constraints + timer
    Resolver.lean -- RFC 1034 §5.3.2-3: Resolver state (glossary) + algorithm (numbered steps) + SlistEntry
    NegativeCache.lean -- RFC 2308: negative caching props + NegativeCacheSpec/NegativeAuthoritySpec
    Credibility.lean   -- RFC 2181 §5.4.1: Trustworthiness enum + TrustworthinessSpec + answerability obligation
    Resilience.lean    -- RFC 5452 §9.1-2: response matching + unpredictability obligations
    Server.lean   -- RFC 1035 §6.2, §7.3: Server query processing + UdpSocket typeclass
  Test/
    Loop.lean     -- Mock-socket compile-time (#guard) verification of serveOne/resolveWithIO
  Impl/
    Parsec.lean         -- DnsParser/DnsSerializer monads + byte-level primitives
    BitPacking.lean     -- Sub-byte field pack/unpack (Header flags)
    Enum.lean           -- Opcode/Rcode/RRType/RRClass/Qtype/Qclass ↔ Nat
    DomainName.lean     -- Domain name decode/encode with compression (§4.1.4)
    Header.lean         -- Header decode/encode (12 fixed bytes)
    Question.lean       -- Question decode/encode
    RData.lean          -- All 16 RDATA types decode/encode
    ResourceRecord.lean -- ResourceRecord decode/encode
    Message.lean        -- Full DNS message decode/encode
    Cache.lean          -- Concrete DnsCache type + CacheSpec instance
    SList.lean          -- Concrete DnsSList type + SlistSpec instance
    Resolver.lean       -- Fuel-bounded resolver with NS walking, delegation (4b), CNAME chasing with chain accumulation (4c)
    UdpSocket.lean      -- @[extern] FFI (socket/bind/sendto/recvfrom) + UdpSocket IO instance
    Server.lean         -- Iterative resolution IO shim, SBELT-based server loop
  Proof/
    Enum.lean           -- Enum roundtrips (by cases; complete)
    BitPacking.lean     -- pack/unpack roundtrip (bv_decide; complete)
    Parsec.lean         -- BitVec ↔ UInt conversion roundtrips (complete)
    Primitives.lean     -- Parser/serializer equational lemmas + byte access helpers (complete)
    DomainName.lean     -- Domain name roundtrip theorems (complete)
    Header.lean         -- Header roundtrip theorem (complete)
    Question.lean       -- Question roundtrip theorem (complete)
    RData.lean          -- RData roundtrip theorems: A, CNAME, HINFO, MX, SOA (complete)
    ResourceRecord.lean -- ResourceRecord roundtrip theorem (complete)
    Message.lean        -- Full message roundtrip theorem (complete; Appends framework + frame lemmas + decodeMany induction)
    Resolver.lean       -- RFC conformance proofs: SBELT fallback, ID match, dispatch, termination, needsIO, step relation soundness, response coverage (all complete)
    Server.lean         -- buildResponse/truncateUdp properties (complete)
  Main.lean       -- Executable entry point (UDP server on port 5300)
```

## include_rfc Pipeline

1. Parser reads raw text from `rfc/rfc-{num}.txt`
2. Extracts lines in the given range
3. Strips page break artifacts (footer, form feed, header, surrounding blanks)
4. Strips trailing whitespace per line
5. Compares normalized text against user-provided block
6. Compile error on mismatch with line-by-line diff

## Diagram Types

The pipeline handles two diagram formats:

- **Bit diagrams** (`+--+--+`): Field-level layouts with precise bit widths.
  Generates structures with `BitVec` fields and inductive types for enums.
  Multiple diagrams in the same section are parsed as separate groups
  (`DiagramGroup`): the first is the definition, subsequent ones are examples.
- **Section diagrams** (`+-----+`): High-level message structure with named
  sections. Generates structures with resolved types (environment lookup) and
  `Array` wrapping via grammatical parsing (NLP.lean). The NLP pipeline parses
  inline descriptions and prose into Subject-Verb-Object clauses, derives
  `SectionProp` values (e.g., `alwaysPresent`, `pluralHead`, `containsPlural`),
  then uses those to decide singular vs. Array wrapping.

## Formal Prop Generation

Properties are generated via a declarative `PropSpec` expression tree system.
Two rule kinds cover all property shapes:

### Field-Level Rules

Field description sentences are NLP-parsed into `Clause` structures, then
matched against registered `field_prop_rule` declarations.

Props are named by clause index (`{field}_prop_{i}` where `i` is the clause
position), not by dense counter. Skipped clauses leave gaps (e.g., `aa_prop_0`,
`aa_prop_2` with no `_1`). This aligns with `pushSentenceHoverInfo`'s
`sentenceIdx` so hover links point to the correct prop.

All generated prop docstrings include the pretty-printed formal Lean term
in a fenced code block for hover display.

```lean
field_prop_rule {
  name := "zero_adj"
  pattern := .adjEquals "zero"
  prop := .forallStruct (.eq .currentField (.lit 0))
}
```

`ClausePattern` variants:
- `.adjEquals adj` — matches `SVAdj` clauses with the given adjective
- `.hasWord word` — matches `npOnly` clauses with word in preAdjs/head
- `.textPrefix pfx` — matches `unparsed` text starting with prefix
- `.textContains word` — substring match across all clause types (unparsed text,
  participle verbs, PP heads, relClause text)

Unmatched clauses are skipped (no `True` props emitted).

`PropSpec` extensions for cross-message properties:
- `.forallPair body` — `∀ (a b : Struct), body` (two-message quantification)
- `FieldRef.pairLeft`/`.pairRight` — project fields from left/right binder

This enables behavioral specs like field copying between query and response:
`∀ (a b : Header), a.qr = 0 ∧ b.qr = 1 → a.id = b.id`

### Cross-Struct Rule Framework

Properties that reference fields across structures (e.g., "QDCOUNT specifying
the number of entries in the question section") are resolved via a declarative
rule system using `SimplePersistentEnvExtension`:

**PropRules.lean** defines:
- `FieldRef` — reference to a value in the generated prop (field projections,
  bound variables, literals, PP resolution, extracted bindings, cross-spec fields)
- `PropSpec` — composable expression tree describing prop shapes (includes
  `.declField` for struct field declarations and `.seq` for sequencing)
- `ParticiplePattern` — declarative match spec: verbs, optional object head,
  required PP (prep, head) patterns
- `ClausePattern` — match spec for field descriptions
- `ProseClausePattern` — match NLP Clause structure (verb, subject, PPs)
  with value extraction via `ValueSlot` / `Extraction`
- `CrossStructRuleEntry` / `FieldPropRuleEntry` / `ProseClauseRuleEntry` — bundle pattern + PropSpec
- `cross_struct_rule` / `field_prop_rule` / `prose_clause_rule` commands — register rules

**Syntax.lean** registers rules and interprets PropSpec trees:
```lean
cross_struct_rule {
  name := "count_entries"
  pattern := { verbs := #["specifying", "specifies"],
               objHead := some #["number"],
               requiredPPs := #[("of", #["entries", "records"])] }
  prop := .forallStruct (.eq (.toNat .matchedSubField) (.size (.resolvedFromPP "in")))
}
```

At elaboration time, `generateCrossStructProps` queries the extension, matches
each sub-struct field's NLP-parsed docstring against registered rules, and
interprets the PropSpec tree into Lean syntax:
- Count props: `∀ (msg : Format), msg.header.qdcount.toNat = msg.question.size`
- Domain name validity: `∀ (msg : Format) (i : Fin ...), ∃ labels, ∀ l ∈ labels, ...`

New property shapes require only new rule declarations — no interpreter changes.

### Structured NLP PostMods

The NLP pipeline parses post-modifiers of noun phrases into typed structures
(`PostMod`) instead of raw strings:

- `PostMod.pp` — prepositional phrases with parsed NP objects
- `PostMod.participle` — participial phrases with verb, object NP, and PP chain
- `PostMod.relClause` — relative clauses with pronoun and clause text
- `PostMod.raw` — unparseable fallback

Cross-struct rules match against `PostMod.participle` structure declaratively
via `ParticiplePattern` rather than hardcoded conditionals.

## Prose-Only Section Derivation

Sections without diagrams (e.g., 3.1 Name space definitions, 4.2 Transport)
go through the full NLP pipeline to derive structure fields and constraints:

1. Parenthetical stripping removes inline clarifications
2. Sentences are tokenized and POS-tagged (lexicon + morphology + disambiguation)
3. Clauses are parsed as SVO, passive (S + copula + participle + PPs), or SVAdj
4. `parseProseClauses` returns raw `Array Clause` (deduplicated, unparsed filtered)
5. `prose_clause_rule` rules match clause structure directly:
   - `ProseClausePattern` specifies verbs, subject head, required PPs
   - `ValueSlot` / `Extraction` extract values (`.ppNumeric`, `.ppBitWidth`, etc.)
   - Output is a unified `PropSpec` tree: `.declField` for struct fields,
     `.forallStruct` for props, `.seq` for both
6. `deriveStructFields` still handles "expressed as sequence of X" → `.structField`
7. Bindings are shared across rules (e.g., size_bound's "value" aliased as "threshold")

Generates structures like `NameSpace { labels : Array ByteArray }` with
element-level bounds, and transport structures like `UdpUsage { data : ByteArray }`
with size constraints and cross-spec reference props.

### Negation and Disjunction

`PropSpec` supports `.neg` (¬) and `.disj` (∨) constructors for cache-style
constraints where RFC prose uses negation ("should not be cached", "should
never be combined") and disjunction ("all or none"). The `ProseClausePattern`
`requireNegation` flag ensures rules only fire on negated passive clauses
(where the VP adverb is "not" or "never"). The NLP `Clause.svPassive`
carries a `negated : Bool` field derived from VP adverb analysis

## Example Sentence Analysis

Example sentences in RFC prose (e.g., "For example, if PROTOCOL=TCP (6),
the 26th bit corresponds to TCP port 25") are parsed into formal `Prop`
definitions via `NLP.analyzeExamples`:

1. Tokenizer splits with offset tracking and abbreviation lookahead ("e.g.", "i.e.")
2. POS tagger adds `discMarker` ("For example") and `subConj` ("if"/"when")
3. Conditional examples are split into antecedent/consequent at comma boundaries
4. Antecedent: `NOUN = NOUN ( NUM )` → `ExamplePred.fieldEq field value`
5. Consequent: field resolution + numeric extraction → `ExamplePred.fieldAccess`

Generated as:
```lean
def wksrdata_example_0 : Prop :=
  ∀ (w : WksRdata) (getBit : ByteArray → Nat → Bool),
    w.protocol = 6 → getBit w.«<bit map>» 25 = true
```

## Example Diagram Generation

Example diagrams (subsequent groups after the definition diagram) are
parsed cell-by-cell into `ByteArray` literals:

- Single-digit cells → numeric byte values (e.g., "1" → 1)
- Single-letter cells → ASCII byte values (e.g., "F" → 0x46)
- Multi-digit cells → numeric values (e.g., "20" → 20)
- Bit markers ("1  1") and empty cells → skipped

Generated as `def {struct}_example_{i} : ByteArray := ⟨#[...]⟩`.

## Glossary Parsing

Sections with glossary-format definitions (e.g., RFC 1034 §5.3.2: `NAME  description`)
use a dedicated parser path:

1. `parseGlossaryList` detects lines where first word is ALL-CAPS, followed by 2+ spaces,
   and second token is NOT a number. Continuation lines at indent ≥ 16.
2. `resolveGlossaryFieldTypes` resolves each description to a Lean type via NLP keyword
   table ("domain name" → `ByteArray`, "QTYPE" → env lookup `Qtype`, "same form as X" →
   cross-reference) and environment lookup.
3. `generateStructure` creates the struct with resolved field types.
4. Intro prose (text before first glossary entry) is parsed via `prose_clause_rule` matching.

### Glossary Typeclass Derivation

Glossary entries whose descriptions say "a structure which stores/describes ..."
are too abstract for concrete struct fields. Instead of falling back to `ByteArray`,
the pipeline derives abstract typeclass specs via full NLP inference — the
grammatical clause structure directly determines method signatures, abstract type
parameters, and axioms.

**Trigger**: glossary description contains "structure which" or "structure that".

**Pipeline**:
1. Description → `NLP.parseProseClauses` → `Array Clause`
2. For `.npOnly` clauses with `.relClause` PostMods → `NLP.reparseRelClause`
   re-parses the relative clause text into proper SVO clauses (prepends implicit
   "it" subject for verb-first text, splits coordinated objects on "and")
3. `inferClassFromClauses` maps each clause to a `MethodSpec`:
   - **SVO → Method**: verb stem = method name, object NP = type parameter or
     arg type, Self-returning vs getter inferred from verb semantics
   - **RelClause → Predicate**: "whose X has Y" → accessor + predicate
   - **Implied pairs**: `store X` → `entries` getter + `store_mem` axiom
4. `ClassSpec` → `generateGlossaryClass` → `class` declaration via
   `elabCommandStr` (string-based code generation for robust `Type` handling)
5. "same form as X" entries share the referenced entry's class
6. Polymorphic parent struct generated with type params + instance binders

**Type resolution** (`resolveNPType`): env lookup first → DNS domain mappings
("domain name" → `ByteArray`, "address" → `BitVec 32`) → abstract type param.

**Method naming** (`deriveMethodName`): verb stemming with multi-word idiom
detection ("keeps track" → `keepTrack`). Deduplication suffixes object noun
when multiple clauses produce the same verb stem.

**Example output** (RFC 1034 §5.3.2):
```lean
class SlistSpec (S : Type) (NS : Type) where
  describeServers : S → Array NS
  describeZone : S → ByteArray
  keepTrack : S → NS → S
  zoneName : S → ByteArray

class CacheSpec (C : Type) (RR : Type) where
  store : C → RR → C
  entries : C → Array RR
  store_mem : Prop

structure Resources (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] where
  sname : ByteArray; stype : Qtype; sclass : Qclass
  slist : S; sbelt : S; cache : C
```

## Algorithm Step Parsing

Sections with numbered algorithm lists (e.g., RFC 1034 §5.3.3) use a dedicated parser path:

1. `parseNumberedAlgorithm` detects top-level (`   N. description`) and sub-level
   (`         a. description`) items. Parsing stops after sub-steps end and prose begins.
2. `deriveConstructorName` extracts verb + object from step descriptions via NLP
   (e.g., "See if the answer..." → `checkAnswer`, "if the response shows a CNAME" →
   `cname`).
3. `generateAlgorithmTypes` creates:
   - `inductive {Name}Step` — one constructor per top-level step
   - `inductive ResponseAction` — one constructor per sub-step
   - `structure Transition` with `from`, `action`, `to` fields
   - `def {name}_transition_{i}` constants from "go to step N" targets
4. Algorithm prose paragraphs are parsed via NLP-driven property derivation.

### Algorithm Property Generation

The algorithm path derives formal `Prop` definitions from detailed prose paragraphs
by parsing them through the NLP pipeline with conditional sentence awareness:

1. `extractAllProse` joins all algorithm paragraph text (past the numbered list).
2. `NLP.parseAlgorithmClauses` splits on ". " and "; ", then for each fragment:
   - Detects `if`/`when` subordinating conjunctions
   - Splits conditionals at comma boundaries (depth-aware) into guard/body pairs
   - Strips leading "then"/"and" connectors from body tokens
   - Handles postposed conditionals ("cache the data if its TTL > 0")
   - Returns `ConditionalClause.conditional guard body` or `.simple clause`
3. `collectContextTypes` gathers all structure/inductive types in the current namespace.
4. `deriveAlgorithmProperty` matches clause structures against patterns:
   - **Copula SVO with comparative**: "X is greater than zero" → `∀ x, x.field > 0`
   - **SVO with "matches" verb + domain guards**: "response matches query using ID"
     → `∀ (a b : Header), a.qr.toNat = 1 ∧ b.qr.toNat = 0 → a.id = b.id`
     (uses `aliasDomainWordGuarded` to distinguish query/response via QR field,
     `pairLeft`/`pairRight` FieldRef constructors to select the correct binder)
   - **SVO with "from" PP**: "initializes SLIST from SBELT"
     → `∀ (S C NS RR : Type) [SlistSpec S NS] [CacheSpec C RR] (x : Resources S C NS RR), x.slist = x.sbelt`
   - **SVAdj with comparative + "than" PP**: numeric comparisons
   - **Conditional**: if guard or body resolves, use the resolved part
5. `resolveNPToField` resolves NP heads to types/fields:
   - ALL-CAPS words → field name search across context types
   - Capitalized words → type name lookup in environment
   - Domain aliases with guards ("response" → `Header` + qr=1, "query" → `Header` + qr=0)
   - General field name search across all context types
6. `walkFieldPath` performs one-level nested field resolution (e.g., `Header.id`
   from `Format.header`).
7. Non-polymorphic types generate syntax-quotation props; polymorphic types
   (like `Resources S C NS RR`) use string-based elaboration via
   `renderPolymorphicPreamble` which extracts type params and instance constraints
   from the `Expr`, resolving de Bruijn indices to parameter names.

**POS tagger enhancements** for algorithm prose:
- Verb `-s` inflection: "matches" → verb (stem + known-root check)
- Comparative adjective `-er`: "greater" → adj (stem in `knownAdjs`)
- `"than"` recognized as preposition for comparative constructions
- Verb-after-determiner disambiguation: "the search" → noun (not verb)
- Pronoun handling: "its" tagged as determiner; compound noun loop breaks on
  pronouns ("it", "they", etc.) so "the query it sent" → NP(head="query")

## Value-List Parsing

Sections with enumeration lists (e.g., TYPE values, CLASS values) use a
dedicated parser path:

1. `parseValueList` detects lines matching `NAME  code  description` patterns
2. `generateValueListType` creates an `inductive` type with one constructor per entry
3. Lean keyword conflicts are avoided: `Type` → `RRType`, `Class` → `RRClass`

## RFC Text Hover Mapping

The `include_rfc` parser (`rfcTextBodyFn` in Macro.lean) segments the verified
RFC text into atoms and idents with `.original` source info at exact byte
positions. Idents receive `TermInfo` entries (via `pushInfoLeaf`) pointing at
generated declarations, so both the editor infoview and SubVerso/Verso HTML
render hovers for RFC text. Split-point detectors per section type:

- **Field names** (`findFieldSplitPoints`): where-block names → struct field
  projections (`pushHoverInfoFromIdents`).
- **Description sentences** (`findSentenceSplitPoints`): ". "/".\n" boundaries
  within field descriptions → clause-indexed props (`pushSentenceHoverInfo`;
  sentence index aligns with `{field}_prop_{i}` clause naming).
- **Glossary entries** (`findGlossarySplitPoints`): entry names → derived
  typeclass or parent struct field (`pushGlossaryHoverInfo`).
- **Value-list entries** (`findValueListSplitPoints`): entry names → enum
  constructors (e.g., `NS` → `RRType.ns`).
- **Prose sentences** (`findProseSentenceSplitPoints`): for sections without a
  where-block, sentences in prose paragraphs become idents. Scanning skips the
  title and diagram-ish lines, never spans blank lines, and stops before the
  first glossary/value-list entry so entry names stay separate idents.
- **Section title / diagram / example triggers**: single idents → the struct.

Overlapping split points are deduplicated by sorted offset (longer preferred
at equal offsets).

Prose-derived props (prose-clause rules, algorithm properties, glossary intro
props) are linked by **source-text matching** rather than index alignment:
`parseProseClausesWithSrc` / `parseAlgorithmClausesWithSrc` pair each clause
with its source sentence fragment, `processRfcText` returns
`(propName × srcSentence)` pairs, and `pushProseHoverInfo` attaches each prop
to the first ident whose normalized text (parentheticals dropped, whitespace
collapsed, lowercased) contains the source fragment. Numeric limit constants
(`extractConstraintValues`) and ranked-list enums + their order relation
record their matched source phrase the same way, including on the
no-struct fallback path.

**One hover per token — claim map.** SubVerso renders exactly one `TermInfo`
per token, so when several definitions derive from the same sentence (a
refined guard and its obligation, `{field}_prop_i` and `{field}_semantics_i`,
a ranked enum and its order relation), only one can own the hover. All
pushers thread a shared `HoverClaims` map (ident byte position → owning
declaration) through `claimHover`: the first definition claims the ident,
and every later definition landing on a claimed ident is appended to the
owner's docstring under "**Also generated from this passage**" with its
pretty-printed form (`ppGeneratedDecl`: zero-binder `Prop` defs show their
body, parameterized defs their type, inductives their constructor list).
Push order = priority: prose props → sentence props → example props →
generic struct/field fallback on unclaimed idents only. Every generated
definition is therefore reachable from some hover on the passage that
produced it.

**Stale-cache warning**: Verso HTML pages reference hover docstrings by
sequential numeric id into a site-wide `-verso-docs.json` table. Pages and the
table must come from the same render: a browser caching one but not the other
(or a partial regeneration over a stale `.lake/build/literate/` cache) shifts
every id, making hovers show neighboring declarations (e.g., QR displaying
`Header.z`). After changing metaprogramming code, delete BOTH
`.lake/build/literate/` and `.lake/build/literate-html/` before
`lake query :literateHtml`, and hard-refresh the browser.

## Bit Width Resolution

When both diagram and where-block specify bit widths, the where-block takes
precedence. This handles cases where the diagram shows a simplified view
(e.g., A record's ADDRESS shown as one 16-bit row but described as "32 bit")
or where `mergeDiagramFields` incorrectly merges unnamed cells (e.g., WKS
PROTOCOL shown as 8 bits but adjacent unnamed cells inflate it).

## Wire-Format Implementation (Impl/)

The `Impl/` layer implements DNS wire-format parsing and serialization against
the Spec types generated by `include_rfc`.

### Parser/Serializer Monads

- **DnsParser**: `ByteArray → Nat → Except String (α × Nat)`.
  A function type (not a monad transformer stack) taking buffer and position,
  returning either an error or the parsed value with the new position. This
  design makes equational reasoning trivial (`DnsParser.run p buf pos = p buf pos`
  by `rfl`). The full message ByteArray is passed for compression pointer
  following (§4.1.4).
- **DnsSerializer**: `StateM ByteArray`. Appends bytes to a growing buffer.

### Domain Name Compression (§4.1.4)

`decodeNameAux` uses fuel-bounded recursion to follow compression pointers.
The top 2 bits of a length byte select: `00` = label, `11` = pointer.
Pointer case records the end position (2 bytes consumed) and follows the
14-bit offset. Fuel is bounded by `buf.size` to prevent infinite loops.

### Bit Packing (Header Flags)

Bytes 2–3 of the DNS header encode 8 sub-byte fields in 16 bits:
`QR(1) OPCODE(4) AA(1) TC(1) RD(1) | RA(1) Z(3) RCODE(4)`.
`packFlags` builds the word with shifts and OR; `unpackFlags` extracts
fields with shifts and truncation.

## Conformance Proofs (Proof/)

Roundtrip theorems state that for each type T:
`DnsParser.run decode (DnsSerializer.runBytes (encode x)) = .ok (x, wireSize x)`

**Complete proofs** (no sorry):
- Enum: all 6 enum types, by `cases`/`rfl`
- BitPacking: `unpack_pack` via `bv_decide` (SAT-based bitvector reasoning)
- Parsec: BitVec ↔ UInt conversion roundtrips via `simp`
- Primitives: read/write roundtrips for BV8, BV16, BV32, UInt16; equational lemmas
  for `DnsParser.run` (bind, pure, map, getPos, setPos, getBuffer, fail);
  composite helpers (`readBV32_at`, `byte_at_suffix`) for multi-field proofs
- DomainName: decode/encode roundtrip via structural induction on labels with
  frame lemma for parsing in the presence of prefix/suffix bytes
- Header: mega-simp proof composing primitive, enum, and bitpacking roundtrips
- Question: domain name frame lemma + BV16 byte access proofs
- RData: A (fixed 4 bytes), CNAME (raw wire format), HINFO (length-prefixed
  strings), MX (BV16 + domain name), SOA (two domain names + 5×BV32 via
  `readBV32_at` + `byte_at_suffix`)
- ResourceRecord: domain name + 10 fixed bytes + variable rdata extract

- Message: full message roundtrip (`decode ∘ encode = id`), complete. The
  implementation's `for` loops were replaced by structurally recursive
  `decodeMany`/`encodeList` (same semantics) so proofs can induct directly.
  Infrastructure:
  - **Appends framework**: `Appends s bytes` states a write-only serializer
    appends a fixed byte string from any initial buffer; compositional via
    `appends_seq`, giving `encode_eq` (encoder output = header bytes ++
    concatenated per-item encodings).
  - **Frame lemmas**: `header_frame` (header decode ignores trailing bytes),
    `question_frame` (question decode at any position via the domain-name
    frame lemma + byte_at_suffix).
  - **Sequential parse induction**: `run_decodeMany` — parsing n items from
    concatenated encodings recovers all items, given a per-item frame property.
  - **Validity hypotheses**: `ValidQuestions` (label decompositions);
    `ValidRRBytes` restated as the canonical fixed-point property
    (`decodeRRCanonical` reproduces the stored bytes exactly) — the previous
    `ResourceRecord.decode`-based statement was too weak because `decode`
    canonicalizes RRs while `encode` writes them raw.

### Resolver RFC Conformance (Proof/Resolver.lean)

Proofs that the fuel-bounded resolver state machine conforms to NLP-generated
algorithm properties from RFC 1034 §5.3.3:

- **SBELT fallback** (`stepFindServers_sbelt_fallback`): when `stepFindServers` falls
  back to SBELT (walkNs returns none), `slist = sbelt`. Weakened from unconditional
  to conditional after NS walking was added. Proof by `unfold`/`split`/`simp`.
- **ID preservation** (`stepAnalyzeResponse_preserves_id`): when `stepAnalyzeResponse`
  returns an answer, its header ID equals the input response's header ID. Handles
  all response branches (4a answer, 4a name error, 4b delegation, 4c CNAME, 4d
  server failure). Proof by nested `split at heq` with `StepResult.answer.injEq`.
- **Step dispatch**: four theorems (`step_*_dispatch`) proving `step` correctly
  dispatches to the corresponding step function based on `currentStep`.
- **Termination** (`resolve_loop_result`): the resolve loop always produces either
  `.ok` or `.error` (never diverges), by induction on fuel.
- **needsIO yield** (`step_sendQueries_needsIO`): stepSendQueries yields `.needsIO`
  when no response is available.
- **Sequential transitions** (`step_seq_checkAnswer`, `step_seq_findServers`):
  sequential steps always transition to the correct next step. `step_seq_findServers`
  now proves existence of a transition (may be `.sendQueries` via NS or SBELT).
- **StepSpec soundness** (`step_implies_spec`): step function only produces
  transitions allowed by StepSpec. Complete: case split on `currentStep`,
  tracing each goto branch to its StepSpec constructor; guard obligations
  discharged from branch conditions (`rcode_eq_of_beq` converts boolean enum
  tests to the guards' propositional equalities; `extractCname = some` implies
  a nonempty answer since `findSome?` on `#[]` is `none`).
- **Response coverage** (`step_analyzeResponse_coverage`): when `responseHandled`
  holds, the resolver does not return the "unhandled response type" error.
  Complete. Required aligning the implementation's 4a condition with
  `guard_answerOrNameError` (see Response Analysis below): at the fallback branch
  all four guards are provably false, contradicting `responseHandled`.

- **CNAME chase obligation** (`step_cname_chase`): when `cnameToChase` fires,
  `stepAnalyzeResponse` MUST transition analyzeResponse → checkAnswer with
  SNAME updated to the canonical name and the chain accumulated. This is the
  *liveness/obligation* direction that the NLP-generated spec cannot express:
  `StepSpec` is an inductive *permission* relation (soundness says every
  transition taken is allowed; an implementation that never chases is
  trivially sound), and the generated `guard_cname` was weakened to
  `answer.size > 0` (the prose "shows a CNAME" has no Format-level meaning
  since answers are opaque ByteArrays, and the qualifier "and that is not the
  answer itself" was dropped), making it identical to the first disjunct of
  `guard_answerOrNameError` — so the spec cannot even distinguish the 4a and 4c
  situations. The obligation is therefore stated manually against the
  implementation-level `cnameToChase` trigger.

All resolver theorems are sorry-free (axioms: `propext`, `Quot.sound`).

## Step Relation and needsIO Yield

### NLP-Derived Guard Derivation

Algorithm sub-step guards (e.g., "if the response answers the question or contains
a name error") are derived entirely via NLP — no hardcoded guard predicates or `True`
placeholders. The pipeline extends the existing NLP infrastructure with:

- **Enum constructor search** (`resolveNPToEnumCtor`): searches all inductives in
  context types for constructors whose name matches the NP head. Multi-word NPs are
  joined to camelCase ("name error" → "nameError"). Two-pass: exact match first,
  then compound substring for multi-word queries.
- **Field chain tracing** (`traceFieldChain`): given a target type (e.g., `Rcode`),
  walks struct fields to find the dotted path from the root struct (`Format`).
  Returns the chain for generating `resp.header.rcode`-style expressions.
- **Verb stem → field match**: when SVO object doesn't resolve, the verb stem is
  tried as a field name ("answers" → "answer" → `Format.answer`). Array fields
  generate `.size > 0` predicates.
- **Coordinated clause splitting**: guard text is split on " or " / " and " into
  sub-clauses, each resolved independently, then combined with `PropSpec.disj`/`.conj`.

Generated guards (in `VeriDNS.Spec`):
- `guard_answerOrNameError`: `resp.answer.size > 0 ∨ resp.header.rcode = Rcode.nameError`
- `guard_delegation`: `resp.authority.size > 0`
- `guard_cname`: `resp.answer.size > 0`
- `guard_serverFailure`: `resp.header.rcode = Rcode.serverFailure`

### Step Relation (`StepSpec`)

`generateStepRelation` (Syntax.lean) emits a formal step relation indexed by
`AlgorithmStep`:

```lean
inductive StepSpec : AlgorithmStep → AlgorithmStep → Prop where
  | seq_checkAnswer_findServers : StepSpec .checkAnswer .findServers
  | seq_findServers_sendQueries : StepSpec .findServers .sendQueries
  | seq_sendQueries_analyzeResponse : StepSpec .sendQueries .analyzeResponse
  | answerOrNameError (resp : Format) : guard_answerOrNameError resp → StepSpec .analyzeResponse .checkAnswer
  | delegation (resp : Format) : guard_delegation resp → StepSpec .analyzeResponse .findServers
  | serverFailure (resp : Format) : guard_serverFailure resp → StepSpec .analyzeResponse .sendQueries
```

Sequential constructors come from adjacent top-level steps; conditional constructors
from sub-steps with `gotoTarget` fields. `StepSpecStar` provides transitive closure.
`isTerminal` identifies terminal sub-steps (answer/name error).

`responseHandled` is the completeness obligation — a disjunction of all sub-step
guards: `guard_answerOrNameError resp ∨ guard_delegation resp ∨ guard_cname resp
∨ guard_serverFailure resp`. This states that the guards cover the full response
space. The NLP pipeline generates soundness (StepSpec: valid transitions) but this
was missing the completeness direction (all cases must be handled). Generated
automatically in `generateStepRelation` after the `isTerminal` block.

### Refined Guards and Obligations (modality + content fidelity)

`StepSpec` and the base guards are *permissions*: soundness proofs cannot
detect an implementation that never takes an allowed transition (this is how
a missing CNAME chase went unnoticed). The base guard derivation also weakens
content: "shows a CNAME" became `answer.size > 0` — identical to the first
disjunct of `guard_answerOrNameError` — because RR sections are opaque ByteArrays
at the Spec level. `generateStepRelation` therefore additionally generates:

- **Refined guards** (`guardRefined_{action}`), parameterized by abstract
  content predicates `answersQuery : Format → Bool` (the "answers the
  question" / "is not the answer itself" prose) and
  `hasRRType : Array ByteArray → BitVec 16 → Bool` (RR-type containment).
  RR-type mentions are resolved through the generated enums: if the enum is
  traceable to a Format field (Rcode, Opcode) a field equation is emitted;
  otherwise (RRType) a `hasRRType` conjunct with the constructor's code from
  `rfcEnumDescriptions` (now a `SimplePersistentEnvExtension` so codes stored
  in Spec/RRType.lean survive into Spec/Resolver.lean). NPs that fail
  name-based resolution fall back to matching the head noun of stored enum
  descriptions ("other servers" → NS via "an authoritative name server").
  `or`-coordination keeps resolved disjuncts; `and`-coordination is
  all-or-nothing (dropping a conjunct would widen the region).
- **Obligations** (`obligation_{action}`), over an abstract transition
  relation `transition : Format → Option AlgorithmStep → Prop`: when exactly
  one refined guard holds (all other refined guards negated — single-guard
  regions, so no priority judgments are needed and the spec stays consistent
  under guard overlap), the sub-step's transition MUST be taken (`none` =
  terminal answer). Generated with hygienic syntax quotations, not strings.

The implementation instantiates `answersQuery`/`hasRRType` with its
parse-based checks (`answersQueryB`, `hasRRTypeIn` in Impl/Resolver.lean) and
`transition` with `stepAnalyzeResponse` (`implTransition`), and proves all
four obligations (`impl_obligation_*` in Proof/Resolver.lean). The old
implementation (returning answers without chasing) is refuted by
`impl_obligation_cname`: a CNAME-bearing, non-answering response in
the single-guard region must transition to checkAnswer.

### Complement-Clause Semantics and Recommendations

Two further rule classes derive specs from sentence shapes the base rules
cannot handle:

- **Complement clauses** (field descriptions, §4.1.1): "specifies/denotes/
  indicates **that/whether** ⟨copular clause⟩" generates
  `{field}_semantics_{i} (emitted : Header → Prop) (⟨isX⟩ : Bool) : Prop`.
  The complement's truth is abstracted as a Bool capability parameter (the
  Spec cannot know the emitter's capability) and quantification is over an
  abstract emission predicate; a "response" mention adds a `qr = 1` guard.
  "that" yields an implication (bit set ⇒ statement); "whether" an iff (bit
  reflects statement). Generated: `aa_semantics_0` (AA=1 ⇒ `isAuthority`),
  `ra_semantics_0` (RA=1 ⇔ `isAvailable` — derived despite the RFC's own
  "this be is set" typo), plus emergent `qr`/`tc` variants. The server
  instantiates `emitted := finalizeForClient`-produced headers,
  `isAuthority := false`, `isAvailable := true` and proves both
  (`server_aa_semantics`, `server_ra_semantics` in Proof/Server.lean) — this
  is what forces the flag hygiene (QR=1, RA=1, AA=0) in `finalizeForClient`.
- **Modal recommendations** (§5.3.3 step 2 prose): "It **may** be the case
  that ⟨C⟩" marks the underlying operation as partial ("may" is now a modal
  in the POS tagger alongside should/must); the following "the **best** is to
  ⟨action⟩" recommends the reaction. C's negated copula over an availability
  adjective and the action's gerund + "for the ⟨obj⟩" become abstract
  predicates over an abstract state σ, generating
  `recommendation_addressesAvailable (σ) (addressesAvailable : σ → Bool)
  (lookAddresses : σ → Prop) : Prop := ∀ s, addressesAvailable s = false →
  lookAddresses s`. The SLIST instantiates it (`slist_recommendation`):
  partiality is `SlistEntry.address : Option`, and when servers exist with
  no known address, `DnsSList.addressTargets` is nonempty — the names the IO
  shim sub-resolves.

### Glueless NS Resolution

`ioResumeLoop` (Impl/Server.lean) implements the recommendation: when
`bestWithAddress` returns `none` (the RFC's "addresses are not available"),
it takes the first `addressTargets` name, sub-resolves its A record from
SBELT (`mkAddressQuery`, full recursive restart of the resolve loop), records
the result via `DnsSList.addAddress`, and retries. Nesting is bounded by a
`depth` parameter (default 3); termination is by lexicographic `(depth, fuel)`.
Failed lookups drop the NS name from the SLIST and try the next target.

### needsIO Yield Pattern

The resolver (Impl/Resolver.lean) is a pure state machine. When step 3 (sendQueries)
has no cached response, it yields `.needsIO` instead of erroring:

- `StepResult.needsIO`: new constructor for IO-requiring states
- `ResolveYield.done`/`.paused`: resolve loop returns either a complete response or
  a paused state waiting for IO
- `resume`: continues a paused resolver with an externally-supplied response

The IO shim (Impl/Server.lean) drives the resolver via `resolveWithIO`:
1. Run pure `resolve` with SBELT → if `.done`, return response
2. If `.paused` → pick best server from SLIST via `DnsSList.bestWithAddress`
3. Build fresh sub-query for current SNAME via `Resolver.buildSubQuery`
4. Convert `BitVec 32` IP to 6-byte FFI addr via `ipv4ToAddr` (port 53)
5. `forwardQuery` → `resume` with response → loop or return
6. On timeout: remove failed server from SLIST, try next best

`serveOne` uses `resolveWithIO` for true iterative resolution per RFC 1034
§5.3.3. The resolver iterates through delegations autonomously: cache →
NS walk → query → analyze → delegation → re-query until answer or error.
Uses separate client socket (no timeout) and upstream socket (2s recv timeout
via `SO_RCVTIMEO`). On upstream timeout, removes the failed server from SLIST
and tries the next best.

### Glue Record Propagation

Delegation (4b) extracts glue A records from the additional section via
`extractGlueRecords` and populates the SLIST with addresses via
`SlistFromNameSpec.setUpAddresses`. `stepFindServers` also looks up cached A records
for NS names to populate addresses when building the SLIST from cached NS records.
Both `lastResponse` clearing (4b/4c) and `currentStep` updating (in `resolve.loop`)
are critical for correct state machine transitions.

### Response Flag Hygiene

`finalizeForClient` (Impl/Server.lean) is applied to every response sent to a
client: QR=1, RA=1 (this server recurses), AA=0 (not an authority), Z=0
(§4.1.1 "must be zero in all ... responses"; also strips an echoed or
upstream AD bit this resolver did not validate, RFC 4035 §3.2.3 —
`finalizeForClient_z`). QR/RA/AA are forced by the instantiated
complement-semantics props (`server_ra_semantics`, `server_aa_semantics`).

### Persistent TTL Cache

The §5.3.2 CACHE glossary prose now generates time-aware operations and real
laws on `CacheSpec`: `storeAt : C → RR → UInt32 → C` (from "convert the
interval ... to some sort of absolute time when the RR is stored"),
`sweep : C → UInt32 → C` (from "discards them during periodic sweeps"), and
law fields `store_mem`/`storeAt_mem` (membership) and `sweep_subset`
(removal-only) — emitted as the law statements themselves, so instances must
prove them (previously `store_mem : Prop` was discharged with `True`).
The manual `CacheLookup` class is gone entirely:

- **`CacheSpec.lookup`** is assembled cross-ENTRY within the §5.3.2 block:
  the intro prose names the operation ("converted to a general LOOKUP
  function" — participle "converted" + "to" PP, the premodifier before
  "function"); the search-state entries supply the key in glossary order
  (an entry whose description uses the "search" lexeme contributes a
  component — ALL-CAPS references resolve through a context struct's wire
  field, "the QTYPE of the search request" → `Question.qtype : BitVec 16`,
  else the entry's own resolved type, SNAME → `ByteArray`); the entry
  whose class already has the temporal store and whose description
  encounters stored items "in the course of a search" hosts the method,
  time-indexed.
- **`TrustworthinessSpec`** (`acceptRrset`, `answers`) is generated
  cross-FILE in Spec/Credibility.lean from the §5.4.1 sentences: the
  deliberated verb + object NP ("whether to ACCEPT an RRSET ... should
  consider the ... trustworthiness") give the ranked store; the possessive
  anaphor "already in ITS CACHE" resolves to the generated `CacheSpec`
  (glossary naming convention), whose keyed time-indexed retrieval — read
  via forall-telescope — fixes the key and time arguments; the negated
  passive's "as" complement ("returned as ANSWERS to a received query")
  names the answer-path accessor. This required flipping the import:
  Spec/Credibility.lean now imports Spec/Resolver.lean (CacheSpec must be
  in the env), and Resolver no longer needs Credibility.
  The RFC 2308 negative-cache operations are also generated — see
  "Negative-Cache Typeclass Generation" below.

`DnsCache` (Impl/Cache.lean) wires the TTL machinery into the instances and
proves all laws; Proof/Cache.lean adds `store_absolute_expiry` (§6.1.3),
`lookup_fresh` and `sweep_removes_expired` (§5.3.2 expiry), `store_replaces`
(§7.4 all-or-none), `truncated_not_cached` (§7.4 partial sets), and
`accept_discard_unrequested` (instantiating the generated
`usingthecache_discard_unrequested` from §7.4's "other than that requested ...
without caching it"). The cache persists across queries: `serveOne` threads
it (final answers stored with TTL at the wall clock from `UdpSocket.now`),
and `State.now` carries the resolution start time for expiry checks.

### Cache-Hit Answers (step 1 obligation)

RFC 1034 §5.3.3 step 1 — "See if the answer is in local information, and
if so return it to the client" — is a top-level step with an anaphoric
conditional, a shape the obligation generator previously never analyzed
(only the 4a–4d sub-steps got guards/obligations), so an implementation
that proceeded to findServers on a positive cache hit satisfied every
generated spec. This was the same root cause as the earlier CNAME miss:
permissions were generated, the MUST direction wasn't.

The pipeline now parses "See if ⟨condition⟩, and if so ⟨action⟩"
(`NLP.parseIfSoStep`: complementizer "if" after the imperative verb,
anaphoric "so", and an object pronoun resolved to the condition's subject
via `parseImperativeClause`) and generates

```lean
def obligation_checkAnswer (σ : Type)
    (answerInLocalInformation returnAnswerToClient : σ → Prop) : Prop :=
  ∀ s, answerInLocalInformation s → returnAnswerToClient s
```

The honest instantiation (`impl_obligation_checkAnswer`,
Proof/Resolver.lean: condition = fresh negative or positive entry for the
query key; action = `stepCheckLocal s = .answer r`) was UNPROVABLE against
the old implementation — both arms of the positive-hit `if` were gotos.
The fix: `RRParse.rrBytes` (canonical re-encoding), `cacheResponse`
(synthesized answer from cached RRs, finalized through `finalizeAnswer`
for CNAME-chain/question restoration), and `DnsCache.lookup` returning
REMAINING TTLs (expiry − now; `lookup_fresh` restated). `DnsCache.store`
replaces same-key entries at RRset granularity (same-batch members share
an expiry, RFC 2181 §5.2, and survive; stale sets are evicted whole —
`store_replaces` restated), so multi-record sets are served intact.

### Bogus-Delegation Gate (RFC 1034 §5.3.3)

From "the resolver should check to see that the delegation is 'closer' to
the answer than the servers in SLIST are ... **If not, the reply is bogus
and should be ignored**", the check-that/if-not rule (the anaphoric "not"
negates the checked condition — the negative twin of step 1's "if so")
generates `obligation_replyIgnored` with the condition predicate named
from the parsed clause (`delegationCloserToAnswerThanServersInSlist`).
Implementation: `bogusDelegationB` (Impl/Server.lean) = delegation-shaped
(NS in authority, non-answering, no name error, no CNAME to chase) ∧ NOT
closer (`delegationMatchCount` — trailing labels shared between SNAME and
the NS owner zone — ≤ the SLIST's match count). The gate sits in
`ioResumeLoop` beside `acceptResponse`: a bogus reply reaches neither
resolution state nor the cache, closing the in-protocol poisoning vector
where a legitimately-queried server injects NS/glue for zones no closer
than where the resolver already is. `shim_obligation_replyIgnored`
instantiates the generated obligation. (`RRParse` gained `rrName` for the
owner-zone extraction.)

### Cached-CNAME Chase at Step 1

`stepCheckLocal` consults the cache through `localAnswer`, a fuel-bounded
local chase: at each name, the negative then positive lookups come FIRST
(so a direct hit is never shadowed), and only on a miss does it follow a
cached CNAME (RFC 1034 §3.6.2's restart at the canonical name),
accumulating the chain. A full chain hit answers entirely from cache; a
partial chase that ends in a miss continues resolution at the canonical
name (SLIST reset — its match count measured the old SNAME). No new step
transition is introduced, so `StepSpec` soundness is untouched, and the
`obligation_checkAnswer` instantiation discharges on the first chase
iteration.

### NXDOMAIN Covers All Types (RFC 2308 §5)

The §5 sentences key NXDOMAIN by `<QNAME, QCLASS>` and NODATA by
`<QNAME, QTYPE, QCLASS>`. The tuple-key rule treats `<...>` as ONE lexical
token (notation, like a numeral — tokenizer + tagger change), finds the
keyed PP grammatically (prep "for" + NP with "same" premodifier and a
tuple-token head), and resolves the answer class through the enum
machinery ("resulted from a name error" → `Rcode.nameError`). Question
fields OMITTED from the tuple render as invariance of an abstract retrieve
function: `cachingnegativeanswers_nameError_retrieval` (qtype-invariance);
the NODATA sentence names all three fields, so nothing is generated for
it. Implementation: `DnsCache.lookupNxdomain` takes no qtype at all
(invariance is definitional — `nxdomain_retrieval_conform`), is consulted
first by `lookupNegative` (`lookupNegative_nxdomain_any_qtype` bridges),
and an NXDOMAIN store replaces all entries for `<QNAME, QCLASS>`. Live: an
NXDOMAIN cached from an A query answers a subsequent AAAA query in 0 ms.

### Periodic Cache Sweep

`serverLoop` sweeps the cache at the wall clock every `sweepInterval`
(64) queries — the §5.3.2 "periodic sweeps to reclaim the memory" whose
operation and laws (`sweep_subset`, `sweep_removes_expired`) were already
generated and proven but never invoked. Between sweeps, expired entries
are already invisible to lookups (`lookup_fresh`).

### Negative Caching (RFC 2308)

`rfc/rfc-2308.txt` is captured in Spec/NegativeCache.lean via three
`include_rfc` blocks, all run through the NLP pipeline (the generator's
section-title and prose-header recognition was extended for RFC 2308's
"N - Title" format):

- §2.2 ("NODATA is indicated by an answer with the RCODE set to NOERROR and
  no relevant answers in the answer section") generates `nodata_indicated`:
  the "is indicated by" rule resolves "RCODE set to NOERROR" to an enum
  equation through the field chain and "no relevant answers" to
  `(Format.answer resp).size = 0`.
- §3 ("the TTL of this record is set to the minimum of the MINIMUM field of
  the SOA record and the TTL of the SOA itself") generates
  `negativeanswersfromauthoritativeservers_negative_ttl`: the
  minimum-of-two-fields rule locates `SoaRdata` (searching nested
  namespaces) and emits the if-form minimum (`BitVec 32` has no `Min`
  instance).
- §5's closing paragraph generates
  `cachingnegativeanswers_limit_negativeresponse_ttl` via the duration-cap
  rule: the capped entity is the object NP of the verb "cache" in the limit
  sentence ("… limit for how long it will cache a negative response …"),
  and the bound is the upper end of a grammatically parsed
  ⟨numeral to numeral time-unit⟩ range (`NLP.parseDurationRange`; word
  numerals are `.quant` tokens) from "Values of one to three hours … would
  make sensible a default" → every stored negative TTL ≤ 10800 s.
- §6 ("it MUST add the cached SOA record to the authority section of the
  response with the TTL decremented by the amount of time it was stored in
  the cache") generates `obligation_addCachedSoaRecordToAuthoritySection`
  via the MUST-add-to rule: the when-clause guard
  (`encountersCachedNegativeResponse`), object NP (`cachedSoaRecord`),
  "to" PP target (`authoritySection`), and "with" PP head-noun + participle
  transform (`withTtlDecremented`) are all read from the parse.

Implementation: `DnsCache.storeNegative`/`lookupNegative` (keyed
`NegativeEntry` array with absolute expiry), `computeNegativeTtl` +
`extractSoaNegative` (SOA scan of the authority section, returning both the
negative TTL and the SOA RR itself), and `negativelyCacheable` (untruncated
NXDOMAIN or NODATA). `serveOne` stores negatives after answering — TTL
capped by `capNegativeTtl` (10800 s) and the SOA RR stored alongside,
carrying the capped TTL; `stepCheckLocal` answers a fresh negative hit
immediately via `negativeResponse`, whose authority section now carries the
cached SOA with the decremented TTL (`NegativeEntry.authority`: remaining
lifetime `expiry − now`, served via `CacheLookup.lookupNegativeSoa`).
Re-storing a cache-served negative is harmless: the served TTL is the
remaining lifetime, so the absolute expiry never extends (no §5 loop).
Conformance proofs: `computeNegativeTtl_conform` (instantiates the
generated TTL law by `rfl`), `negativelyCacheable_nodata` (the NODATA arm
implies the generated `nodata_indicated`), `lookupNegative_fresh` (no
expired entry is ever returned), `capNegativeTtl_conforms` (Proof/Server:
the generated §5 cap), and `negative_soa_in_authority` +
`lookupNegativeSoa_serves_authority` (Proof/Cache: the generated §6
obligation and the lookup serving exactly that authority).

### Negative-Cache Typeclass Generation (RFC 2308 §5/§6)

The manual `CacheLookup.storeNegative`/`lookupNegative`/`lookupNegativeSoa`
methods were replaced by typeclasses generated from the same sentences that
already generated the §5/§6 props:

- **§5 (tuple-key rule, extended)**: the keyed cached/retrieved frame
  ("should be cached such that it can be retrieved and returned ... for the
  same ⟨TUPLE⟩") now also generates `NegativeCacheSpec (C : Type)` with
  `cacheNegative : C → ByteArray → BitVec 16 → BitVec 16 → Rcode → UInt32 → C`
  and `retrieveNegative : ... → Option Rcode`. The store key is the UNION of
  the tuple fields across the keyed sentences (NXDOMAIN names ⟨QNAME,
  QCLASS⟩, NODATA ⟨QNAME, QTYPE, QCLASS⟩); field types come from the
  `Question` struct projections; the answer class is the enum resolved from
  the subject's relative clause ("resulted from a name error" → `Rcode`);
  the operation names come from the passive participles after "be"
  (`participleStem`, with an e-final verb-root lexicon: "cached" → "cache");
  the subject's premodifier supplies the suffix ("a NEGATIVE answer"). The
  TTL-countdown sentence ("This TTL decrements ... upon reaching zero ...
  MUST NOT be used again") adds the absolute-time argument.
- **§6 (MUST-add rule, extended)**: the when-clause's object ("a CACHED
  NEGATIVE response") anaphorically references the §5 class — its
  premodifiers (participle + adjective) reconstruct the class name — so the
  obligation's pieces also generate
  `NegativeAuthoritySpec (C RR : Type) extends NegativeCacheSpec C` with
  `storeSoaRecord` (from "... the amount of time it was STORED in the
  cache") and `authoritySection` (the "to"-PP target served back for the
  same key). The key is read off the parent's store projection via a
  forall-telescope, so the two blocks stay independent.

`DnsCache` instantiates both (`cacheNegative` = `storeNegative` with no SOA;
`storeSoaRecord` = `DnsCache.setNegativeSoa`, attaching the SOA to the
just-stored entry; `authoritySection` = `lookupNegativeSoa`); `localAnswer`
consults the generated methods. The server-side one-shot
`DnsCache.storeNegative` (rcode + SOA in one entry) remains the concrete
composition of the two generated operations.

### Entry-Structure Derivation (SlistEntry)

The manual `ServerEntry` was replaced by `SlistEntry`, generated from the
§5.3.3 algorithm prose by `deriveEntryStructure` (RFC/Syntax.lean), entirely
from grammatical structure:

1. **Membership imperative** — a verb-first clause whose plural object moves
   "into" an ALL-CAPS structure ("Copy the names into SLIST") fixes the
   entry identity → field `name : ByteArray`.
2. **Possessive-anaphor imperative** — "Set up THEIR addresses ..." (the
   determiner "their" refers to the just-established entries) → per-entry
   field `address : BitVec 32`.
3. **Modal partiality** — "It may be the case that the addresses are not
   available" ("may" + expletive copula + "case" head with a that-relClause
   negating an adjectival predication over a known field's plural) → the
   field wraps in `Option`.
4. **Keep-track purpose** — "keep track of previous transmissions" (token
   level: purpose-infinitive coordination is lossy at clause level) →
   `transmissionCount : Nat`.

The per-entry `matchCount` of the old manual struct was dropped: §5.3.2 ties
the match count to the SLIST itself (it remains on `DnsSList` and
`SlistFromNameSpec.matchCount`). Supporting NLP fixes: "their" joined the
determiner lexicon, `parseImperativeClause` absorbs verb particles ("Set up"),
the det-adj-verb sequence retags as a noun ("a negative ANSWER"), and
`stripPlural` only strips "-es" after sibilant stems ("names" → "name",
"addresses" → "address").

### Cache Bounds (FIFO eviction)

Both cache sections are bounded by `DnsCache.capacity` (4096): `store` and
`storeNegative` run `boundFifo`, which drops oldest-inserted entries to make
room before pushing (arrays append on store, so index 0 is oldest).
`store_bounded`/`storeNegative_bounded` (Proof/Cache.lean) prove the bound
holds after every store, unconditionally; `mem_of_mem_boundFifo` keeps the
§7.4 `store_replaces` proof intact through the eviction.

### Total Query Deadline

`resolveWithIO` takes a `budget` (default 5 s) and computes an absolute
deadline; `ioResumeLoop` checks `UdpSocket.now` against it on every
iteration (RFC 1035 §7.2's per-request bound on total work). This caps
wall-clock time independently of the 2 s per-exchange timeout and the
fuel/depth bounds — e.g. a long SLIST of unresponsive servers times out at
the deadline rather than at (servers × 2 s).

### Retransmission and Server Selection (RFC 1035 §7.2)

`rfc/rfc-1035.txt` §7.2 is captured in Spec/Resolver.lean. From "Each time
an address is chosen and the state should be altered to prevent its
selection again until all other addresses have been tried", a new prose
rule (passive event clause + "to prevent ⟨possessive-anaphor⟩
⟨nominalization⟩ again") generates `sendingthequeries_prevent_selection`:
after `addressChosen`, `selection` of the same item is false.
`slist_prevent_selection` (Proof/Server.lean) instantiates it:
`bestWithAddress` is least-queried-first (`bestWithAddress_min`, a foldl
invariant over the named `pickBest` step — which also fixed a latent bug
pairing the kept entry with the wrong address), `markQueried` is the state
alteration, and a full cycle of equal counts is the "until all other
addresses have been tried" escape. Behaviorally: a timed-out server is no
longer removed — it is only count-deprioritized, so every less-tried
address is preferred before it is retransmitted to, with total work
bounded by fuel and the deadline. Servers are removed only for bizarre
responses (4d) or failed glueless resolution.

### Query Hygiene (RFC 1035 §4.1.1 RCODE semantics)

Where-block enum value descriptions are now joined across wrapped lines
(previously truncated at the first line), and values whose description is
a negated-capability clause generate use-condition semantics
(`generateNegatedCapabilitySemantics`; the POS tagger learned "unable" as
adjective and verb retagging after "unable to"/"does not"):

- RCODE 1 "The name server was unable to interpret the query" →
  `rcode_formatError_semantics` (capability `interpretQuery`)
- RCODE 4 "The name server does not support the requested kind of query" →
  `rcode_notImplemented_semantics` (capability `supportRequestedKindOfQuery`)
- RCODE 5 "The name server refuses to perform the specified operation for
  policy reasons" → `rcode_refused_semantics` (capability
  `performSpecifiedOperationForPolicyReasons`; the negated-capability
  frame was extended with "refuses to ⟨verb⟩" — a refusal is the
  willingness-capability failing — plus verb retagging after "refuses to")

`serveOne` screens requests before resolution: undecodable datagrams get a
minimal raw FORMERR (ID echoed; dropped if under 12 bytes), `queryProblem`
classifies decoded queries (≠1 question → FORMERR; opcode ≠ QUERY →
NOTIMP; RD=0 → REFUSED, since iterative service is the one operation this
recursive-only server refuses to perform). `hygiene_formatError` /
`hygiene_notImplemented` / `hygiene_refused` (Proof/Server) instantiate the
generated semantics (each over the subtype that passed the earlier
checks — an uninterpretable query has no judgeable kind).

### TTL Sanity (RFC 1035 §7.3)

From "If a RR has an excessively long TTL, say greater than 1 week, either
discard the whole response, or limit all TTLs in the response to 1 week"
(already-included §7.3 text), an either/or prose rule (imperative or-arm
parsed with `parseImperativeClause`; duration from a numeral + time-unit
pair) generates `processingresponses_limit_ttls`: a processed response is
either discarded (`none`) or every parsed RR carries TTL ≤ 604800, over
all `Array ByteArray` sections of `Format` (discovered from the struct).
The implementation takes the DISCARD arm (`sanitizeTtls` in
`forwardQuery`; the limit arm would need decode-side label-validity lemmas
for the re-encode roundtrip): an offending response is dropped like any
bogus response. `sanitize_limit_ttls` proves conformance. Note
Spec/Server.lean now imports Spec.Message — without `Format` in scope the
prose rules silently no-op.

### Case-Insensitive Name Comparison (RFC 1035 §3.1 / §2.3.3)

The §3.1 block in Spec/DomainName.lean (already verified text) generates
three props via the insensitive-comparison rule — all read from the parse
of "Name servers and resolvers must compare labels in a case-insensitive
manner (i.e., A=a), assuming ASCII with zero parity.  Non-alphabetic codes
must match exactly.":

- `namespace_compare_caseinsensitive` — the manner-PP frame (verb
  "compare" + "in a ⟨X⟩-insensitive manner"; X read from the hyphenated
  adjective, which is a single token since '-' is not punctuation): values
  identified by an abstract `foldCase` compare equal.
- `namespace_compare_example` — the "i.e."-marked `A=a` pair (two
  single-letter tokens differing only in case around "=", scanned in the
  ORIGINAL-case sentence; "assuming ASCII" in the same sentence sanctions
  numeric codes): `compare 65 97 = true`.
- `namespace_nonalphabetic_match_exactly` — the exactness sentence
  (negated-adjective plural subject headed "codes" + MUST + "match" +
  adverb "exactly"): outside the `alphabetic` range the byte comparison is
  exact equality.

Implementation (Impl/DomainName.lean): `foldCaseByte` (A–Z → +32, all
else fixed), `foldNameCase`, and `nameEqCI`; every protocol-level name
comparison routes through it — cache keying (store/storeChecked/
storeNegative/lookup/answerableEntry/lookupNxdomain/lookupNegative/
findNegative), `questionMatches` (response acceptance — an upstream that
echoes the QNAME in different case, e.g. 0x20-randomizing, still matches),
`suffixMatchCount` and `matchCountLabels` (SLIST closeness / delegation
match counts). Wire-format length bytes are ≤ 63 < 'A', so folding whole
wire names only touches label content. Conformance (Proof/DomainName.lean):
`nameEqCI_conforms`, `foldCaseByte_example_conforms`,
`foldCaseByte_nonalphabetic_exact`; end-to-end (Proof/Cache.lean):
`lookup_caseInsensitive` / `lookupAnswerable_caseInsensitive` /
`lookupNegative_caseInsensitive` — lookups are invariant under the case of
the queried name, so `EXAMPLE.COM` hits the `example.com` entry (verified
live: second query 0 ms from cache, including negative entries).

### SLIST Closeness (truncated referrals)

§7.4 forbids caching truncated responses, but a truncated referral is still
usable for the immediate step: 4b installs the response-derived SLIST, and
`stepFindServers` now keeps the current SLIST whenever it is strictly closer
than the cache walk's result — using §5.3.2's own semantics ("a match count
... this is used as a measure of how 'close' the resolver is to SNAME"),
exposed via the generated `SlistFromNameSpec.matchCount`/`searchFails`. Without this,
a truncated (hence uncached) referral caused a re-query loop. Dually, the
CNAME chase (4c) resets the SLIST: its match count measured closeness to the
OLD SNAME ("change the SNAME ... and go to step 1" = fresh context).

### RFC 5452 Resilience

`rfc/rfc-5452.txt` §9.1–9.2 are captured in Spec/Resilience.lean. The §9.1
MUST-match bullet list generates `querymatchingrules_match_obligation` (one
abstract matcher per bullet); `acceptResponse` (ID + question echo, applied
before `resume` so spoofed responses never reach the resolver or cache)
instantiates it (`accept_match_obligation`). The three address/port matchers
are socket-layer attributes enforced below the gate: every upstream query
runs on its own per-exchange socket (`UdpSocket.exchange`, FFI
`veri_dns_exchange`) that is `connect(2)`-ed to the queried server, so the
kernel discards datagrams from non-matching source address/port, and the
fresh ephemeral local port per query is unpredictable (§9.2's port
randomization for free). §9.2's unpredictable query IDs are implemented by
`UdpSocket.randomId` (arc4random FFI) + `withRandomId`; `serveOne` restores
the client's ID on the final response. `UdpSocket` also has `now` (clock)
and a defaulted `log` diagnostic hook (IO instance: stderr).

### SBELT Initialization

RFC 1034 §5.3.2: SBELT is "initialized from a configuration file" with root
server entries at match count -1 (represented as 0 since `Nat` can't be
negative). `DnsSList.mkSbelt` builds the initial SLIST from `(name, IPv4)`
pairs. Main.lean configures 5 root servers (a-e.root-servers.net).

### Soundness Proofs

- `step_sendQueries_needsIO`: stepSendQueries yields `.needsIO` when no response exists
- `step_seq_checkAnswer`: checkAnswer either proceeds to findServers or answers
  immediately (a fresh negative-cache hit, RFC 2308)
- `step_seq_findServers`: sequential steps always transition correctly
- `resolve_loop_result`: fuel-bounded loop always terminates (extended for needsIO branch)
- `step_implies_spec`: step function only produces StepSpec-allowed transitions
- `step_analyzeResponse_coverage`: `responseHandled` implies no fallback error

## #naturallanguage: NLP Pipeline Inspector

`#naturallanguage { ⟨prose⟩ }` (Macro.lean) runs the pipeline on arbitrary
text and reports what comes out:

1. **NLP trace** — per sentence, the POS-tagged tokens (`word/TAG`, short
   tags from `POS.short`) and every clause the chunker parses (compact
   `Clause.render` notation: `SVO ⟨subj⟩ · verb · ⟨obj⟩ + PP(...)`).
2. **Generated declarations** — the text is fed through the SAME
   generation pipeline `include_rfc` runs after verifying its text (so
   structures, classes, enums, and props are really elaborated into the
   current namespace, with editor hovers on the block), and the report
   lists every new declaration; defs concluding in `Prop` print their
   value. "no declarations generated" is itself informative: it usually
   means the text took a different generator path than expected
   (diagram / glossary / algorithm / value-list / prose-only).

Use it inside a scratch `namespace` to avoid name collisions with the
real specs.

## Key Design Decisions

- **Grammar over string anchors**: rules read RFC text through the
  tokenizer/POS-tagger/chunker, never by matching literal phrases.
  Notation (tuples, numerals, durations) is tokenized; frames are
  detected over tagged tokens (assertive verb + complementizer for
  "specifies that/whether", "same ⟨form⟩ as ⟨REF⟩" structural-identity
  references, quantifier-partitive "some of which are ⟨adj⟩",
  conjunction-token object coordination); content words come from parsed
  NPs/clauses. Closed-class lexicons (determiners, particles, verb roots,
  time units) are the only word lists.
- **Line ranges over section numbers**: Line numbers are unambiguous and
  don't require section header parsing. If the RFC were re-formatted, line
  numbers would change but so would any other reference.
- **Raw text blocks**: The `{ }` syntax uses a custom parser that reads
  everything between balanced braces as raw text, avoiding string escaping.
- **Page break stripping**: Old RFCs (1034, 1035) have page breaks with
  `[Page N]` footers and form feeds. Modern RFCs (9606) don't. The stripper
  handles both.
- **Batteries dependency**: Used for standard library extensions.

## RR Decompression and Resolver Typeclasses

### Canonical RR Decoding (`decodeRRCanonical`)

DNS message sections (answer, authority, additional) store resource records as
`Array ByteArray`. Originally `decodeRRAsBytes` extracted raw byte slices from
the message buffer, but these could contain compression pointers (§4.1.4)
referencing positions in the original buffer, making standalone parsing fail.

`decodeRRCanonical` replaces this by decoding the RR (resolving compression via
`decodeName` which has the full buffer), then re-encoding uncompressed. For
domain-name rdata types (NS=2, CNAME=5, PTR=12), the rdata is also decompressed,
and SOA (6) rdata has MNAME/RNAME decompressed before its fixed 20-byte tail —
AWS name servers compress SOA rdata names, which silently broke RFC 2308
negative-TTL extraction from authority sections until canonicalized.
After this, all `ByteArray` values in `Format.answer/authority/additional` are
self-contained and can be parsed independently.

### Resolver Typeclasses

The resolver is parametric over `{S C NS RR : Type}` with typeclass constraints.
Two new typeclasses bridge the abstraction gap between `Format` (which stores
`Array ByteArray`) and the parametric types:

- **`SlistFromNameSpec S NS`** (extends `SlistSpec S NS`): batch SLIST
  creation from an array of NS name wire bytes and a match count.
  GENERATED by the operations reading of the same §5.3.3 imperatives the
  entry structure reads as fields: "Copy the names into SLIST" →
  `copyNames`, "Set up their addresses" → `setUpAddresses` (the possessive
  anaphor pairs each address with its name), "comparing the match count in
  SLIST with that computed from SNAME and the NS RRs" → `matchCount` plus
  the construction-time `Nat` argument, and "If the search for NS RRs
  fails, then the resolver initializes SLIST from ... SBELT" →
  `searchFails` (the emptiness test; the former manual `hasServers`,
  polarity inverted). The class extends the glossary-generated `SlistSpec`
  (the ⟨Entry⟩Spec naming convention the anaphor rules use), with binder
  names read from its Π-type. Used by `stepFindServers` (NS walking) and
  `stepAnalyzeResponse` (4b delegation).

- **`RRParse RR`**: parsing canonical wire bytes into `RR` values and extracting
  type/rdata fields. Methods: `parseRaw : ByteArray → Option RR`,
  `rrType : RR → BitVec 16`, `rrRdata : RR → ByteArray`. Used by helper
  functions `extractNsNames`, `extractCname`, and `cacheRRs`.

### NS Walking (Step 2)

`stepFindServers` now walks SNAME labels looking for NS records in cache,
following RFC 1034 §5.3.3 step 2: start at SNAME, then parent, grandparent,
up to the root. Uses `DomainName.parentDomainWire` to strip labels and
`CacheLookup.lookup` to query the cache. Falls back to SBELT only when no
cached NS records are found. Fuel-bounded to prevent infinite loops.

### Response Analysis (Step 4)

`stepAnalyzeResponse` now handles all four sub-cases from RFC 1034 §5.3.3,
checking 4c first per the RFC's qualifier:

- **4c**: CNAME redirect, checked before 4a ("if the response shows a CNAME
  **and that is not the answer itself**"). The trigger `cnameToChase` fires
  when the answer contains a CNAME but no RR of the queried type (and the
  query was not for CNAME records). On chase: cache the answer, set SNAME to
  the canonical name, append the answer RRs to `State.cnameChain`, goto
  step 1. The obligation direction is proved (`step_cname_chase`).
- **4a**: Answer (non-empty answer section) or name error → return
  `finalizeAnswer s resp`: the accumulated CNAME chain is prepended to the
  answer (ANCOUNT updated) and the **original client question is restored** —
  after chasing, the last sub-query's question names the canonical name, and
  stub resolvers silently discard responses whose question section does not
  match what they asked (this manifests as a client-side timeout, not an
  error). The branch condition matches the NLP-generated `guard_answerOrNameError`
  (`answer.size > 0 ∨ rcode = nameError`) exactly, so that `responseHandled`
  covers the branch space (`step_analyzeResponse_coverage`).
- **4b**: Delegation (empty answer, non-empty authority with NS records) →
  cache authority RRs, build new SLIST from NS names (match count =
  trailing labels the delegation zone shares with SNAME — the §5.3.2
  closeness measure, previously mis-set to SNAME's full label count),
  goto step 2. A NOT-closer delegation is bogus and never reaches resume:
  see "Bogus-Delegation Gate" below.
- **4c**: CNAME redirect (answer contains CNAME record) → cache answer RRs,
  update SNAME to canonical name, goto step 1
- **4d**: Server failure **or other bizarre contents** → clear the response
  and retry with step 3. The NLP rule for "or other ⟨adj⟩ ⟨noun⟩"
  disjuncts renders the complement class: the base `guard_serverFailure`
  gains `∨ (¬guard_answerOrNameError ∧ ¬guard_delegation ∧ ¬guard_cname)`
  (making `responseHandled` total — `step_analyzeResponse_coverage` is now
  unconditional and the fallback error is provably dead), and the refined
  guards gain a uniform abstract `handled : Format → Bool` parameter with
  4d's guard becoming `rcode = serverFailure ∨ handled resp = false`,
  instantiated by `classifiableB` (which includes the RFC 2308 NODATA and
  TC handling RFC 1034's enumeration doesn't know about). Behaviorally: a
  REFUSED or odd-rcode response no longer aborts resolution — the server
  is removed (shim-side, §7.2) and the next candidate tried. This also
  fixed a live bug: 4d previously kept `lastResponse`, so an upstream
  SERVFAIL ping-ponged between steps 3 and 4 until fuel ran out.

## UDP Server Architecture

### UdpSocket Typeclass

The `UdpSocket` typeclass (Spec/Server.lean) abstracts socket operations over
a monad `M`, socket type `Sock`, and address type `Addr`. This follows the
`CacheLookup` pattern: a manually defined typeclass extending NLP-generated
transport specs. The abstraction enables:

- **Proofs about server logic** without IO dependencies (pure `M`)
- **Testing** with mock sockets
- **IO instantiation** via Impl/UdpSocket.lean

### FFI Approach (Impl/UdpSocket.lean)

Self-contained C FFI in `ffi/recvfrom.c` providing the UDP operations:
`socket()`, `bind()`, `sendto()`, `recvfrom()`, plus `veri_dns_exchange`
(one connected query exchange: fresh socket → `connect` → `send` → `recv`
with 2s timeout → `close`, returning `Option ByteArray`; `none` on timeout),
`veri_dns_now` (wall clock) and `veri_dns_random_u16` (arc4random). Each is
exposed via `@[extern]` with simple Lean types (`UInt32` for fd, `ByteArray`
for 6-byte encoded addresses). No external socket library dependency —
avoids Alloy/socket.lean version incompatibility with Lean 4.31.

### IO-Shim Verification (Test/Loop.lean)

`serveOne`/`resolveWithIO`/`ioResumeLoop` are parametric over `UdpSocket`,
so the full serving loop runs in pure `StateM MockState` over a scripted
mock socket (per-exchange handlers `ByteArray → Option ByteArray`; an
exhausted script is a timeout). Five end-to-end behaviors are checked by
`#guard` AT COMPILE TIME — the build fails on regression:

1. **Direct answer**: exactly one datagram to the client, client's ID
   restored, QR=1/RA=1/AA=0/Z=0, the answer delivered, question echoed.
2. **RFC 5452 spoof rejection**: a forged-ID response never reaches the
   client (no answer data; non-NOERROR after the script runs dry).
3. **Iterative delegation**: a referral (NS + glue, closer match count) is
   chased — two upstream exchanges, final answer correct.
4. **RFC 2308 negative caching**: NXDOMAIN cached from an A query answers
   a subsequent AAAA query with an EMPTY script (qtype invariance, no
   upstream), the §6 SOA served in the authority both times.
5. **Query hygiene**: RD=0 is REFUSED before any upstream work.

Only the C FFI layer (ffi/recvfrom.c) sits outside this boundary; it is
exercised live with `dig`.

### Server Proofs (Proof/Server.lean)

- **buildResponse properties**: ID preservation, QR=1, rcode propagation, question
  preservation — all by `unfold`/`rfl` (struct field projection through `with` update)
- **truncateUdp_no_trunc**: non-truncation case by `simp` on the size guard

All theorems are sorry-free.
