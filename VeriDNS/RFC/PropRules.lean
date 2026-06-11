/-
  Declarative property rule framework for generating formal Prop definitions
  from RFC prose. Rules are composable expression trees (PropSpec) that
  describe prop shapes, interpreted by a single generic function.

  Three rule kinds:
  - Cross-struct rules: match participial post-modifiers, generate props
    spanning multiple struct fields (e.g., count fields, domain name validity)
  - Field-level rules: match clause patterns in field descriptions, generate
    props for individual fields (e.g., "must be zero", "reserved")
  - Prose-clause rules: match NLP Clause structure (verb, subject, PPs)
    in prose-only sections, generate struct fields and/or props

  All are stored in `SimplePersistentEnvExtension`s and registered
  declaratively via `cross_struct_rule`, `field_prop_rule`, and
  `prose_clause_rule` commands.
-/
import Lean

open Lean Elab Command Meta

set_option autoImplicit false

namespace VeriDNS.RFC.PropRules

-- ============================================================
-- FieldRef: reference to a value in the generated prop
-- ============================================================

/-- Reference to a value in the generated prop expression. -/
inductive FieldRef where
  /-- Field being processed (field-level rules) -/
  | currentField
  /-- Sub-field that matched (cross-struct rules) -/
  | matchedSubField
  /-- Explicit struct field by name -/
  | namedField (name : String)
  /-- Resolve PP object NP to struct field at match time -/
  | resolvedFromPP (prep : String)
  /-- Project from first binder of forallPair -/
  | pairLeft (inner : FieldRef)
  /-- Project from second binder of forallPair -/
  | pairRight (inner : FieldRef)
  /-- BitVec.toNat of a ref -/
  | toNat (ref : FieldRef)
  /-- Array.size / ByteArray.size of a ref -/
  | size (ref : FieldRef)
  /-- Numeric literal -/
  | lit (n : Nat)
  /-- De Bruijn index (0 = innermost binder) -/
  | bound (idx : Nat)
  /-- Value extracted from clause binding (substituted at match time) -/
  | extractedNat (bindingName : String)
  /-- Cross-spec field: resolve location to type, fieldName to field -/
  | resolvedExtField (locationBinding : String) (fieldBinding : String)
  /-- Resolved field path: structName.fieldName, looked up at interpretation time -/
  | fieldPath (structName : String) (fieldName : String)
  deriving Repr, Inhabited, BEq

-- ============================================================
-- PropSpec: declarative specification of a Prop shape
-- ============================================================

/-- Declarative specification of a Prop shape.
    Interpreted by a single generic function to produce Lean syntax. -/
inductive PropSpec where
  /-- ∀ (msg : Struct), body -/
  | forallStruct (body : PropSpec)
  /-- ∀ (a b : Struct), body -/
  | forallPair (body : PropSpec)
  /-- If Array: ∀ (i : Fin), body; else: body -/
  | forallMatchedIndex (body : PropSpec)
  /-- ∃ (x : T), body -/
  | existsTyped (typeName : String) (body : PropSpec)
  /-- ∀ (x), x ∈ container → body -/
  | forallElem (container : FieldRef) (body : PropSpec)
  /-- lhs = rhs -/
  | eq (lhs rhs : FieldRef)
  /-- lhs < rhs -/
  | lt (lhs rhs : FieldRef)
  /-- lhs ≤ rhs -/
  | le (lhs rhs : FieldRef)
  /-- lhs > rhs -/
  | gt (lhs rhs : FieldRef)
  /-- ante → body -/
  | implies (ante body : PropSpec)
  /-- a ∧ b -/
  | conj (a b : PropSpec)
  /-- True -/
  | trivial
  /-- Declare a struct field: name, bitWidth. Interpreter adds to struct. -/
  | declField (name : String) (bitWidth : FieldRef)
  /-- Sequence two specs: both get processed. -/
  | seq (a b : PropSpec)
  /-- ¬ body -/
  | neg (body : PropSpec)
  /-- a ∨ b -/
  | disj (a b : PropSpec)
  /-- ∀ (x : T), body. T is a type name resolved from the environment. -/
  | forallNamed (typeName : String) (body : PropSpec)
  /-- ∀ (a b : T), body. Two variables of the same type. -/
  | forallNamedPair (typeName : String) (body : PropSpec)
  deriving Repr, Inhabited, BEq

-- ============================================================
-- Cross-struct rules (match participial post-modifiers)
-- ============================================================

/-- Pattern for matching participial post-modifiers in NP-only clauses.
    Each rule declaratively specifies what verb and PP structure to match. -/
structure ParticiplePattern where
  /-- Acceptable participle verbs (lowercase) -/
  verbs : Array String
  /-- If some, require object NP with head in this list (lowercase).
      If none, match regardless of object presence. -/
  objHead : Option (Array String) := none
  /-- Required PP patterns: (preposition, acceptable head nouns).
      ALL patterns must match for the rule to fire. -/
  requiredPPs : Array (String × Array String) := #[]
  deriving Repr, Inhabited, BEq

/-- A declarative cross-struct rule: match a participial pattern, emit a prop. -/
structure CrossStructRuleEntry where
  name : String
  pattern : ParticiplePattern
  prop : PropSpec
  deriving Repr, Inhabited, BEq

/-- Persistent environment extension for cross-struct rules. -/
initialize crossStructRuleExt :
    SimplePersistentEnvExtension CrossStructRuleEntry (Array CrossStructRuleEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr entry => arr.push entry
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

private unsafe def evalCrossStructRuleUnsafe (e : Expr) : MetaM CrossStructRuleEntry :=
  evalExpr CrossStructRuleEntry (mkConst ``CrossStructRuleEntry) e

@[implemented_by evalCrossStructRuleUnsafe]
private opaque evalCrossStructRule' (e : Expr) : MetaM CrossStructRuleEntry

/-- Register a cross-struct rule declaratively. Argument is a `CrossStructRuleEntry` literal. -/
elab "cross_struct_rule " t:term : command => do
  let entry ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``CrossStructRuleEntry))
    evalCrossStructRule' e
  modifyEnv fun env => crossStructRuleExt.addEntry env entry

-- ============================================================
-- Field-level rules (match clause patterns in descriptions)
-- ============================================================

/-- Pattern for matching NLP clauses in field descriptions. -/
inductive ClausePattern where
  /-- svAdj with this adjective (case-insensitive) -/
  | adjEquals (adj : String)
  /-- npOnly with word in preAdjs or head (case-insensitive) -/
  | hasWord (word : String)
  /-- unparsed text starting with given prefix (case-insensitive) -/
  | textPrefix (pfx : String)
  /-- matches unparsed text containing substring (case-insensitive) -/
  | textContains (word : String)
  deriving Repr, Inhabited, BEq

/-- A declarative field-level rule: match a clause pattern, emit a prop. -/
structure FieldPropRuleEntry where
  name : String
  pattern : ClausePattern
  prop : PropSpec
  deriving Repr, Inhabited, BEq

/-- Persistent environment extension for field-level rules. -/
initialize fieldPropRuleExt :
    SimplePersistentEnvExtension FieldPropRuleEntry (Array FieldPropRuleEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr entry => arr.push entry
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

private unsafe def evalFieldPropRuleUnsafe (e : Expr) : MetaM FieldPropRuleEntry :=
  evalExpr FieldPropRuleEntry (mkConst ``FieldPropRuleEntry) e

@[implemented_by evalFieldPropRuleUnsafe]
private opaque evalFieldPropRule' (e : Expr) : MetaM FieldPropRuleEntry

/-- Register a field-level rule declaratively. Argument is a `FieldPropRuleEntry` literal. -/
elab "field_prop_rule " t:term : command => do
  let entry ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``FieldPropRuleEntry))
    evalFieldPropRule' e
  modifyEnv fun env => fieldPropRuleExt.addEntry env entry

-- ============================================================
-- Prose-clause rules (match NLP Clause structure directly)
-- ============================================================

/-- Where in a matched clause to extract a value. -/
inductive ValueSlot where
  /-- First numeric in PP's NP preAdjs -/
  | ppNumeric (prep : String)
  /-- Head noun of PP -/
  | ppHead (prep : String)
  /-- Word-to-number from PP's full NP text -/
  | ppBitWidth (prep : String)
  /-- Subject preAdjs concatenated (lowercased) -/
  | subjPreAdjs
  /-- Protocol qualifier from subject postMods -/
  | subjQualifier
  /-- Head noun of PP (for cross-spec resolution) -/
  | ppLocation (prep : String)
  deriving Repr, Inhabited, BEq

/-- A named binding extracted from a slot in a matched clause. -/
structure Extraction where
  name : String
  slot : ValueSlot
  required : Bool := true
  deriving Repr, Inhabited, BEq

/-- Pattern for matching NLP Clause structure (verb, subject, PPs). -/
structure ProseClausePattern where
  /-- Acceptable participles/verbs -/
  verbs : Array String
  /-- Optional subject head filter -/
  subjHead : Option (Array String) := none
  /-- Required PP patterns: (prep, optional head nouns) -/
  requiredPPs : Array (String × Array String) := #[]
  /-- Values to extract from matched clause -/
  extractions : Array Extraction := #[]
  /-- Also match Clause.svo? -/
  matchActive : Bool := false
  /-- Require negation (e.g., "should not be cached") -/
  requireNegation : Bool := false
  deriving Repr, Inhabited, BEq

/-- A declarative prose-clause rule: match clause structure, emit a unified PropSpec. -/
structure ProseClauseRuleEntry where
  name : String
  pattern : ProseClausePattern
  output : PropSpec
  deriving Repr, Inhabited, BEq

/-- Persistent environment extension for prose-clause rules. -/
initialize proseClauseRuleExt :
    SimplePersistentEnvExtension ProseClauseRuleEntry (Array ProseClauseRuleEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr entry => arr.push entry
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

private unsafe def evalProseClauseRuleUnsafe (e : Expr) : MetaM ProseClauseRuleEntry :=
  evalExpr ProseClauseRuleEntry (mkConst ``ProseClauseRuleEntry) e

@[implemented_by evalProseClauseRuleUnsafe]
private opaque evalProseClauseRule' (e : Expr) : MetaM ProseClauseRuleEntry

/-- Register a prose-clause rule declaratively. Argument is a `ProseClauseRuleEntry` literal. -/
elab "prose_clause_rule " t:term : command => do
  let entry ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``ProseClauseRuleEntry))
    evalProseClauseRule' e
  modifyEnv fun env => proseClauseRuleExt.addEntry env entry

end VeriDNS.RFC.PropRules
