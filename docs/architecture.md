# Architecture

## Module Structure

```
VeriDNS/
  RFC/
    Parser.lean   -- RFC text extraction (line ranges, page break stripping)
    Property.lean -- DescProp AST and parser for field description properties
    NLP.lean      -- SVO sentence parser, semantic derivation, prose structure extraction
    Macro.lean    -- include_rfc compile-time command macro
    Syntax.lean   -- Code generation: structures, enums, formal Props from RFC text
  Spec/           -- Formal specifications derived from RFC text
    Header.lean   -- RFC 1035 section 4.1.1: DNS header format
    Question.lean -- RFC 1035 section 4.1.2: Question section format
    ResourceRecord.lean -- RFC 1035 section 4.1.3: Resource record format
    Compression.lean    -- RFC 1035 section 4.1.4: Message compression
    DomainName.lean     -- RFC 1035 section 3.1:   Name space definitions
    Message.lean  -- RFC 1035 section 4.1:   Message format (section diagram)
  Impl/           -- Concrete implementation
  Proof/          -- Conformance proofs (Spec <-> Impl)
  Main.lean       -- Executable entry point
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

Field description properties are generated as formal `Prop` definitions
instead of uninterpreted `DescProp` values:

- `.mustBeZero` / `.reserved` → `∀ (h : T), T.field h = 0`
- `.copiedTo _`, `.countsEntriesIn _`, `.validIn _`, `.setIn _` → `True`
  (cross-struct or contextual, deferred as placeholders)
- `.raw text` → `True` (fallback)

## Prose-Only Section Derivation

Sections without diagrams (e.g., 3.1 Name space definitions) use NLP
pattern matching to derive structure fields and constraints:

1. `deriveStructFields`: scans for "sequence of X" → `Array ByteArray` field
2. `deriveConstraints`: scans for "limit/restricted to N octets/bits" → `∀` props

Generates structures like `NameSpace { labels : Array ByteArray }` with
element-level bounds: `∀ (ns : NameSpace) (l : ByteArray), l ∈ ns.labels → l.size ≤ 63`

## Example Diagram Generation

Example diagrams (subsequent groups after the definition diagram) are
parsed cell-by-cell into `ByteArray` literals:

- Single-digit cells → numeric byte values (e.g., "1" → 1)
- Single-letter cells → ASCII byte values (e.g., "F" → 0x46)
- Multi-digit cells → numeric values (e.g., "20" → 20)
- Bit markers ("1  1") and empty cells → skipped

Generated as `def {struct}_example_{i} : ByteArray := ⟨#[...]⟩`.

## Key Design Decisions

- **Line ranges over section numbers**: Line numbers are unambiguous and
  don't require section header parsing. If the RFC were re-formatted, line
  numbers would change but so would any other reference.
- **Raw text blocks**: The `{ }` syntax uses a custom parser that reads
  everything between balanced braces as raw text, avoiding string escaping.
- **Page break stripping**: Old RFCs (1034, 1035) have page breaks with
  `[Page N]` footers and form feeds. Modern RFCs (9606) don't. The stripper
  handles both.
- **Batteries dependency**: Used for standard library extensions.
