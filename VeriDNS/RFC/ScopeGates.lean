import Lean
import Pseudoprint

/-!
# Scope-gate census and lint

The top correctness capstones of the verified resolver each carry a list of `∀`-binders.
Some are genuine facts about the running system (the `Prog.run` witness, cache
well-formedness the resolver actually maintains). Others are *scope gates*: hypotheses that
narrow the theorem to a sub-domain of queries, topologies, cache shapes, or adversaries. Per
`docs/model-strengthening-plan-2.md` a scope gate is "a door left open, and each open door is a
class of bug". The programme is to enumerate and shut every door; the enforcement spine here
makes that mechanical.

This module provides:

* `scope_census [thm, …]` — resolves each capstone in the `Environment`, walks its type's
  `∀`-binders, classifies each by pretty-printed pattern into a ledger **row**, and logs the
  census. `#eval`-free: it runs at command-elaboration time so it sees the real olean types.
* `justified_scope <thm> "<reason>"` — annotate a gate as intrinsic (a genuine below-boundary
  premise), with a reason string.
* `open_scope <thm> <row> "<note>"` — annotate a gate as a known-open door tracked in the
  ledger, slated to close, pointing at its plan-2 ledger row.
* `scope_gate_lint [thm, …]` — **fails elaboration** if any capstone carries a scope-gate
  hypothesis that is neither `justified_scope`- nor `open_scope`-annotated. This is what breaks
  the build when a new unannotated door opens.
* `generate_scope_ledger [thm, …] to "<path>"` — writes the mechanically-generated
  escape-hatch ledger (`docs/scope-gates.md`) from the actual signatures.

## The row taxonomy and its patterns

Classification is by substring of the pretty-printed binder type (the plan states this is
"acceptable and simplest"). Each row corresponds to a `docs/model-strengthening-plan-2.md`
escape-hatch-ledger row.

| Row (`ScopeRow`) | Matched patterns (substring of the pretty-printed binder type) | plan-2 hatch |
|---|---|---|
| `queryShape` | `toNat ≠ 255`, `qclass`, `RRClass.in`, `.rd = false`, `InScope` (which demands both) | Query shape |
| `topology`   | `SlistShape`, `SlistShape'` | Topology |
| `cacheState` | `DnsCache.empty` (assumes an empty rather than a maintained cache) | State |
| `adversary`  | `WorldModels`, `WorldModelsTcp`, `CooperativeNetwork` | Adversary model |
| `rcodeScope` | `Rcode.`, `RCode.` on a specific rcode | (query/direction-adjacent) |

`direction` is not a binder pattern — a soundness-only capstone is one lacking a paired
adequacy/`HasVerdictAt`-iff dual; it is annotated at the capstone level via `open_scope … direction`.

`behaviour` is likewise not a binder pattern — it records a *behavioural deviation from the RFCs
or from unbound parity* triaged from an external review finding (docs/latest-report.md), attached
at the capstone level: `justified_scope … behaviour` for a deliberate, RFC-argued deviation, and
`open_scope … behaviour` for a door slated to close. Each `behaviour` annotation names its finding
number, the exact RFC clause, and (where one exists) the Test/Loop `#guard` documenting today's
behavior.

A binder that matches no pattern is **not** a scope gate (it is a fact about the running system:
`Prog.run … = some …`, `CacheWf`, `net.WF`, …) and needs no annotation.
-/

open Lean Elab Command Meta

namespace VeriDNS.RFC

/-- The escape-hatch ledger rows from `docs/model-strengthening-plan-2.md`. Each scope-gate
hypothesis is classified into exactly one row. -/
inductive ScopeRow where
  | queryShape
  | topology
  | cacheState
  | adversary
  | rcodeScope
  | direction
  | behaviour
  deriving DecidableEq, Repr, BEq

namespace ScopeRow

def name : ScopeRow → String
  | .queryShape => "query-shape"
  | .topology   => "topology"
  | .cacheState => "cache-state"
  | .adversary  => "adversary"
  | .rcodeScope => "rcode-scope"
  | .direction  => "direction"
  | .behaviour  => "behaviour"

/-- The plan-2 ledger hatch this row belongs to. -/
def hatch : ScopeRow → String
  | .queryShape => "Query shape"
  | .topology   => "Topology"
  | .cacheState => "State"
  | .adversary  => "Adversary model"
  | .rcodeScope => "Query shape (rcode)"
  | .direction  => "Direction"
  | .behaviour  => "Behaviour deviations"

def ofName? (s : String) : Option ScopeRow :=
  match s with
  | "query-shape" | "queryShape" | "query" => some .queryShape
  | "topology"    => some .topology
  | "cache-state" | "cacheState" | "cache" => some .cacheState
  | "adversary"   => some .adversary
  | "rcode-scope" | "rcodeScope" | "rcode" => some .rcodeScope
  | "direction"   => some .direction
  | "behaviour" | "behavior" => some .behaviour
  | _ => none

end ScopeRow

/-- The annotation kind attached to a scope gate. -/
inductive Annotation where
  /-- A genuinely intrinsic gate (a below-boundary premise); `reason` justifies it. -/
  | justified (reason : String)
  /-- A known-open door tracked in the ledger, `row` names its plan-2 ledger row. -/
  | open (row : ScopeRow) (note : String)
  deriving Repr

/-- Registry key: a `(capstone, row)` pair. We annotate a whole row of a capstone at once,
because several binders can express the same door (e.g. `qtype`, `qclass`, `rd` are all
query-shape). This keeps the seed list short and matches the ledger's row granularity. -/
structure GateKey where
  capstone : Name
  row : ScopeRow
  deriving DecidableEq, BEq, Repr

instance : Hashable GateKey where
  hash k := mixHash (hash k.capstone) (hash k.row.name)

/-- Persistent registry of scope-gate annotations, keyed by `(capstone, row)`. -/
initialize scopeAnnotationExt :
    SimplePersistentEnvExtension (GateKey × Annotation) (Std.HashMap GateKey Annotation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, a) => m.insert k a
    addImportedFn := fun arrs =>
      arrs.foldl (fun acc inner =>
        inner.foldl (fun m (k, a) => m.insert k a) acc) {}
  }

def registerAnnotation (k : GateKey) (a : Annotation) : CoreM Unit := do
  modifyEnv fun env => scopeAnnotationExt.addEntry env (k, a)

def annotationFor (env : Environment) (k : GateKey) : Option Annotation :=
  (scopeAnnotationExt.getState env)[k]?

/-! ## Classification -/

/-- Does the pretty-printed binder type `s` express a scope gate, and if so which row?
Matching is by substring of the pretty-printed type — the plan states this is acceptable and
simplest. Returns `none` for a genuine fact about the running system. -/
def classifyBinder (s : String) : Option ScopeRow :=
  let has (sub : String) : Bool := (s.splitOn sub).length > 1
  -- Adversary model: the world-model / cooperative-network premises.
  if has "WorldModelsTcp" || has "WorldModels" || has "CooperativeNetwork" then
    some .adversary
  -- Topology: single-NS slist shape.
  else if has "SlistShape" then
    some .topology
  -- Cache state: assumes an *empty* cache rather than the maintained invariants.
  else if has "DnsCache.empty" then
    some .cacheState
  -- Query shape. Match only the *restricting* equations, not any mention of a query field:
  --   * `qtype.toNat ≠ 255`  — ANY excluded
  --   * an equation pinning `qclass` to IN (`= some RRClass.in` / `= RRClass.in`)
  --   * `rd = false`
  --   * the `InScope` predicate, which bundles the qtype/qclass restrictions.
  -- A hypothesis that merely *mentions* qclass without restricting it (e.g. the cache
  -- invariant `CacheNegWf cache qu.qclass`, or an abstraction-consistency premise
  -- `αClass qu.qclass = some q.qclass`) is a fact about the running system, not a door,
  -- so it is deliberately NOT matched here.
  else if has "toNat ≠ 255" || has "InScope"
        || has "RRClass.in"
        || has ".rd = false" || has "rd = false" then
    some .queryShape
  -- Rcode scope: a hypothesis pinning a specific rcode.
  else if has "Rcode." || has "RCode." then
    some .rcodeScope
  else
    none

/-- A single classified scope-gate hypothesis found on a capstone. -/
structure GateHit where
  binderName : Name
  ppType : String
  row : ScopeRow
  deriving Repr

/-- Walk `thm`'s type binders and return every binder that classifies as a scope gate. Runs in
`MetaM` so `forallTelescopeReducing` and `ppExpr` see the real elaborated type. -/
def censusOne (thm : Name) : MetaM (Array GateHit) := do
  let some ci := (← getEnv).find? thm
    | throwError "scope census: `{thm}` is not in the environment"
  forallTelescopeReducing ci.type fun xs _ => do
    let mut hits : Array GateHit := #[]
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      let fmt ← ppExpr ldecl.type
      let s := fmt.pretty
      match classifyBinder s with
      | some row => hits := hits.push { binderName := ldecl.userName, ppType := s, row }
      | none => pure ()
    return hits

/-- The rows a capstone gates on, deduplicated and ordered. -/
def rowsOf (hits : Array GateHit) : Array ScopeRow := Id.run do
  let mut seen : Array ScopeRow := #[]
  for h in hits do
    if !seen.contains h.row then seen := seen.push h.row
  return seen

/-! ## The capstone list

The enforced set of top-level correctness capstones. Names that are not yet in the environment
(in-flight capstones from plan-2, e.g. `serveSeq_total_primed`) are silently skipped by the
census and lint until they land — at which point they are linted automatically. -/

def capstones : List Name :=
  [ `serveSeq_total
  , `serveSeq_total_mkSbelt
  , `serveSeq_total_primed
  , `serveDatagram_verdict_sound
  , `serveDatagram_total
  , `serveTcpDatagram_total
  , `resolveWithIO_verdict_sound
  , `ioResumeLoop_sound
  , `VeriDNS.Proof.Adequacy.resolveWithIO_spine_adequate_warm
  , `VeriDNS.Proof.Adequacy.serveDatagram_depth1_adequate ]

/-- Present capstones (those actually in the environment). -/
def presentCapstones (env : Environment) (ns : List Name) : List Name :=
  ns.filter (fun n => env.contains n)

/-! ## Commands -/

/-- `scope_census` — log the census over the default capstone list. -/
syntax (name := scopeCensus) "scope_census" : command

@[command_elab scopeCensus]
def elabScopeCensus : CommandElab := fun _ => do
  let env ← getEnv
  let present := presentCapstones env capstones
  for thm in present do
    let hits ← liftTermElabM <| censusOne thm
    if hits.isEmpty then
      logInfo m!"{thm}: no scope gates"
    else
      let mut msg := m!"{thm}:"
      for h in hits do
        let ann := annotationFor env { capstone := thm, row := h.row }
        let status := match ann with
          | some (.justified _) => "justified"
          | some (.open _ _) => "open"
          | none => "UNANNOTATED"
        msg := msg ++ m!"\n  [{h.row.name}] ({status}) {h.binderName} : {h.ppType}"
      logInfo msg
  let missing := capstones.filter (fun n => !env.contains n)
  unless missing.isEmpty do
    logInfo m!"not yet present (in-flight): {missing}"

/-- `justified_scope <thm> <row> "<reason>"` — register a genuinely intrinsic scope gate. `<row>`
is a string literal naming the ledger row (`"query-shape"`, `"topology"`, `"cache-state"`,
`"adversary"`, `"rcode-scope"`, `"direction"`). -/
syntax (name := justifiedScope)
  "justified_scope" ident str str : command

@[command_elab justifiedScope]
def elabJustifiedScope : CommandElab := fun stx => do
  match stx with
  | `(justified_scope $t:ident $r:str $reason:str) =>
    let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    let some row := ScopeRow.ofName? r.getString
      | throwError "justified_scope: `{r.getString}` is not a scope row \
          (query-shape | topology | cache-state | adversary | rcode-scope | direction)"
    liftCoreM <| registerAnnotation { capstone := thm, row } (.justified reason.getString)
  | _ => throwUnsupportedSyntax

/-- `open_scope <thm> <row> "<note>"` — register a known-open door slated to close. `<row>` is a
string literal naming the ledger row (see `justified_scope`). -/
syntax (name := openScope)
  "open_scope" ident str str : command

@[command_elab openScope]
def elabOpenScope : CommandElab := fun stx => do
  match stx with
  | `(open_scope $t:ident $r:str $note:str) =>
    let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    let some row := ScopeRow.ofName? r.getString
      | throwError "open_scope: `{r.getString}` is not a scope row \
          (query-shape | topology | cache-state | adversary | rcode-scope | direction)"
    liftCoreM <| registerAnnotation { capstone := thm, row } (.open row note.getString)
  | _ => throwUnsupportedSyntax

/-- THE LINT. `scope_gate_lint` fails elaboration if any *present* capstone carries a scope-gate
hypothesis whose row is neither `justified_scope`- nor `open_scope`-annotated. -/
syntax (name := scopeGateLint) "scope_gate_lint" : command

@[command_elab scopeGateLint]
def elabScopeGateLint : CommandElab := fun _ => do
  let env ← getEnv
  let present := presentCapstones env capstones
  let mut unannotated : Array (Name × ScopeRow × Name × String) := #[]
  for thm in present do
    let hits ← liftTermElabM <| censusOne thm
    for h in hits do
      match annotationFor env { capstone := thm, row := h.row } with
      | some _ => pure ()
      | none => unannotated := unannotated.push (thm, h.row, h.binderName, h.ppType)
  unless unannotated.isEmpty do
    let mut msg := m!"scope_gate_lint: {unannotated.size} unannotated scope gate(s). \
      Every scope-narrowing hypothesis must carry a `justified_scope` or `open_scope` \
      annotation (see docs/model-strengthening-plan-2.md). Add one for each:"
    for (thm, row, bn, ty) in unannotated do
      msg := msg ++ m!"\n  {thm}  [{row.name}]  {bn} : {ty}\
        \n    → open_scope {thm} {row.name} \"<ledger note>\"  (or justified_scope …)"
    throwError msg

/-! ## Ledger generation

The escape-hatch ledger (`docs/scope-gates.md`) is generated *from the theorem signatures*, not
hand-maintained. `generate_scope_ledger` writes it, mirroring the file IO in `RFC/Check.lean`
(`findProjectRoot` + `IO.FS.readFile/writeFile`). -/

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

/-- Collapse all runs of whitespace (including the newlines the pretty-printer inserts) to a
single space, so a binder type renders on one Markdown table row. -/
private def collapseWs (s : String) : String := Id.run do
  let mut out := ""
  let mut prevSpace := true
  for c in s.toList do
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      if !prevSpace then out := out.push ' '
      prevSpace := true
    else
      out := out.push c
      prevSpace := false
  return out.trim

/-- Escape one Markdown table cell (pipes, backslashes) and collapse whitespace. -/
private def mdCell (s : String) : String :=
  (collapseWs s).replace "\\" "\\\\" |>.replace "|" "\\|"

/-- Render the full census as the Markdown ledger body. -/
def renderLedger
    (rows : Array (Name × Array (GateHit × Option Annotation)))
    (missing : List Name) : String := Id.run do
  let mut out :=
    "# Scope-gate ledger (generated)\n\n\
     <!-- GENERATED by `generate_scope_ledger` in VeriDNS/RFC/ScopeGates.lean. Do not edit by \
     hand: it is derived from the actual capstone theorem signatures. Regenerate by rebuilding, \
     or by running the command. -->\n\n\
     This is the mechanically-generated escape-hatch ledger of \
     `docs/model-strengthening-plan-2.md`. Each row is a scope-gate hypothesis on a top capstone \
     — a door the top correctness theorem leaves open — read directly off the theorem's \
     `∀`-binders and classified by pattern. Status is `justified` (an intrinsic below-boundary \
     premise), `open` (a known door tracked in the ledger, slated to close), or **`UNANNOTATED`** \
     (a door that opened silently — the `scope_gate_lint` command fails the build on any of \
     these).\n\n\
     The lint that keeps this honest lives in `VeriDNS/RFC/ScopeGates.lean` and runs at the end \
     of that file. See `docs/architecture.md`.\n\n"
  for (thm, hits) in rows do
    out := out ++ s!"## `{thm}`\n\n"
    if hits.isEmpty then
      out := out ++ "No scope gates: this capstone's hypotheses are all facts about the running \
        system.\n\n"
    else
      out := out ++ "| Row | plan-2 hatch | Binder | Type | Status | Note |\n\
        |---|---|---|---|---|---|\n"
      for (h, ann) in hits do
        let (status, note) := match ann with
          | some (.justified reason) => ("justified", reason)
          | some (.open _ note) => ("open", note)
          | none => ("**UNANNOTATED**", "")
        out := out ++ s!"| {h.row.name} | {h.row.hatch} | `{mdCell h.binderName.toString}` \
          | `{mdCell h.ppType}` | {status} | {mdCell note} |\n"
      out := out ++ "\n"
  unless missing.isEmpty do
    out := out ++ "## Not yet present (in-flight)\n\n\
      These capstones are named in the plan but not yet landed in this tree; they are linted \
      automatically once they exist:\n\n"
    for m in missing do
      out := out ++ s!"- `{m}`\n"
    out := out ++ "\n"
  return out

/-- `generate_scope_ledger` — write `docs/scope-gates.md` from the live capstone signatures. -/
syntax (name := generateScopeLedger) "generate_scope_ledger" : command

@[command_elab generateScopeLedger]
def elabGenerateScopeLedger : CommandElab := fun _ => do
  let env ← getEnv
  let present := presentCapstones env capstones
  let mut rows : Array (Name × Array (GateHit × Option Annotation)) := #[]
  for thm in present do
    let hits ← liftTermElabM <| censusOne thm
    let annotated := hits.map fun h =>
      (h, annotationFor env { capstone := thm, row := h.row })
    rows := rows.push (thm, annotated)
  let missing := capstones.filter (fun n => !env.contains n)
  let body := renderLedger rows missing
  let srcDir := System.FilePath.mk (← getFileName) |>.parent |>.getD "."
  let root ← findProjectRoot srcDir
  let path := root / "docs" / "scope-gates.md"
  IO.FS.writeFile path body
  logInfo m!"generate_scope_ledger: wrote {path} ({present.length} present capstones, \
    {missing.length} in-flight)"

end VeriDNS.RFC
