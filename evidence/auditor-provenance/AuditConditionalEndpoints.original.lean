/- SPDX-License-Identifier: Apache-2.0
Inactive conditional endpoint contract auditor. Official Lean core imports only.
Never imports project modules at elaboration time, runs project code, inserts declarations,
or proves ParentOccurrenceTheorem. main loads serialized data with loadExts := false.
A passing contract audit is NOT independent kernel checking or fresh-source provenance.
The external replay gate must establish ordinary source compilation of these exact objects.
-/
module
public import Lean.Environment
public import Lean.Data.Json
@[expose] public section
open Lean
namespace ConditionalEndpointAudit

def parentType : Name :=
  `SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem

def endpointModule (fourD : Bool) : Name :=
  if fourD then `NativeFinalAssembly.KeyedProductOfParent
  else `NativeFinalAssembly.CurvedOfParent

def target (fourD : Bool) : Name :=
  if fourD then `NativeFinalAssembly.keyed_product_monotile_of_parent
  else `NativeFinalAssembly.curved_monotile_of_parent

def permittedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- These numeral terms intentionally preserve the accepted raw encoding. -/
def natTerm (n : Nat) : Expr :=
  mkApp3 (mkConst `OfNat.ofNat [.zero]) (mkConst `Nat [])
    (mkRawNatLit n) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit n))

def euclidean (dimension : Expr) : Expr :=
  mkApp2 (mkConst `EuclideanSpace [.zero, .zero]) (mkConst `Real [])
    (mkApp (mkConst `Fin []) dimension)

def topology (dimension : Expr) : Expr := Id.run do
  let z := Level.zero
  let fin := mkApp (mkConst `Fin []) dimension
  let ennreal := mkConst `ENNReal []
  let natCast := mkApp2 (mkConst `AddMonoidWithOne.toNatCast [z]) ennreal
    (mkApp2 (mkConst `AddCommMonoidWithOne.toAddMonoidWithOne [z]) ennreal
      (mkConst `ENNReal.instAddCommMonoidWithOne []))
  let ennTwo := mkApp3 (mkConst `OfNat.ofNat [z]) ennreal (mkRawNatLit 2)
    (mkApp4 (mkConst `instOfNatAtLeastTwo [z]) ennreal (mkRawNatLit 2) natCast
      (mkConst `PiLp.innerProductSpace._proof_1 []))
  let realTopology := mkApp2 (mkConst `UniformSpace.toTopologicalSpace [z])
    (mkConst `Real [])
    (mkApp2 (mkConst `PseudoMetricSpace.toUniformSpace [z])
      (mkConst `Real []) (mkConst `Real.pseudoMetricSpace []))
  let indexName := Name.mkNum (Name.mkStr (Name.mkStr
    (Name.mkNum `x.«_@».Mathlib.Analysis.InnerProductSpace.PiL2 209079104)
    "_hygCtx") "_hyg") 45
  return mkApp4 (mkConst `PiLp.topologicalSpace [z, z]) ennTwo fin
    (mkLambda indexName .default fin (mkConst `Real []))
    (mkLambda `i .default fin realTopology)

/-- Exact historical conclusion transcription. It is used only under the explicit C binder. -/
def expectedConclusion (fourD : Bool) : Expr := Id.run do
  let dimension := natTerm (if fourD then 4 else 2)
  let space := mkConst (if fourD then `SpectreGeometry.EFour else `SpectreGeometry.EPlane) []
  let body := mkConst (if fourD then `SpectreGeometry.polygonProductKeyBody
    else `LiteralPlanar.FanBounds.curvedBody) []
  let hi := mkApp2 (mkConst `Set.Nonempty [.zero]) space
    (mkApp3 (mkConst `interior [.zero]) space (topology dimension) body)
  let monotile := mkApp2 (mkConst `SparseMonotiles.IsAperiodicMonotile []) dimension body
  return mkApp2 (mkConst `And []) hi monotile

def expectedConditionalType (fourD : Bool) : Expr :=
  mkForall `C .default (mkConst parentType []) (expectedConclusion fourD)

def closed (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && !e.hasLevelParam

/-- Binder names are intentionally not part of this source-derived C shape;
visibility, arity, types, indices, radius, family, and constants are fixed. -/
def expandedParentMatches (value : Expr) : Bool :=
  match value with
  | .forallE _ (.forallE _ position state .default)
      (.forallE _ premise conclusion .default) .default =>
    position.equal (mkConst `SpectreFinite.HexSearch.Position []) &&
    state.equal (mkConst `SpectreFinite.HexSearch.State []) &&
    premise.equal (mkApp (mkConst `SpectreFinite.HexSearch.GloballyLegal []) (.bvar 0)) &&
    conclusion.equal (mkApp3 (mkConst `SpectreFinite.HexSearch.OccurrenceComplete [])
      (.bvar 1) (mkApp (mkConst `SpectreFinite.HexSearch.hexRegion []) (mkNatLit 5))
      (mkConst `SpectreFinite.HexSearch.ParentOwnership.certifiedParentFamily []))
  | _ => false

def require (ok : Bool) (message : String) : Except String Unit :=
  if ok then pure () else throw message

def validateTheorem (fourD : Bool) (ci : ConstantInfo) : Except String TheoremVal := do
  let .thmInfo v := ci | throw "Absent or non-theorem endpoint"
  require (v.name == target fourD) "Endpoint declaration name mismatch"
  require v.levelParams.isEmpty "Endpoint universe parameters must be []"
  require (closed v.type && closed v.value) "Open endpoint type or proof"
  -- Expr.equal deliberately checks binder names and annotations; Expr BEq does not.
  require (v.type.equal (expectedConditionalType fourD)) "Exact conditional raw type mismatch"
  let .forallE binder domain tail .default := v.type | throw "Missing explicit C binder"
  require (binder == `C && domain.equal (mkConst parentType []) && !tail.isForall)
    "Expected exactly one explicit named C binder"
  return v

def validateParent (ci : ConstantInfo) : Except String Unit := do
  let .defnInfo v := ci | throw "C must be a definition, never an axiom or theorem"
  require (v.name == parentType && v.levelParams.isEmpty && v.safety == .safe)
    "C definition name, universe, or safety mismatch"
  require (closed v.type && closed v.value) "Open C definition"
  require (v.type.equal (mkSort .zero) && expandedParentMatches v.value)
    "C differs from the exact occurrence-completeness expansion"

def definition (env : Environment) (name : Name) : Except String DefinitionVal := do
  let some (.defnInfo ci) := env.checked.get.find? name
    | throw s!"Absent or non-definition semantic anchor: {name}"
  require (ci.levelParams.isEmpty && ci.safety == .safe) s!"Unsafe/polymorphic anchor: {name}"
  require (closed ci.type && closed ci.value) s!"Open semantic anchor: {name}"
  return ci

/-- Small independently transcribed anchors. This is NOT the full physical model
or body audit. The missing exact value references are listed in the packet. -/
def simpleAnchors (env : Environment) (fourD : Bool) : Except String Unit := do
  let spaceName := if fourD then `SpectreGeometry.EFour else `SpectreGeometry.EPlane
  let space ← definition env spaceName
  require (space.type.equal (mkSort (.succ .zero)) &&
    space.value.equal (euclidean (natTerm (if fourD then 4 else 2))))
    "Space alias changed dimension or Euclidean model"
  let point ← definition env `SparseMonotiles.Point
  require (point.type.equal (mkForall `d .default (mkConst `Nat []) (mkSort (.succ .zero))) &&
    point.value.equal (mkLambda `d .default (mkConst `Nat []) (euclidean (.bvar 0))))
    "Point definition differs from exact EuclideanSpace Real (Fin d)"
  let pointAt := fun d => mkApp (mkConst `SparseMonotiles.Point []) d
  let setOf := fun t => mkApp (mkConst `Set [.zero]) t
  let predicateType := mkForall `d .implicit (mkConst `Nat [])
    (mkForall `T .default (setOf (pointAt (.bvar 0))) (mkSort .zero))
  let mkPrefix := fun body => mkLambda `d .implicit (mkConst `Nat [])
    (mkLambda `T .default (setOf (pointAt (.bvar 0))) body)
  let hasTiling ← definition env `SparseMonotiles.HasTiling
  let hasValue := mkPrefix (mkApp2 (mkConst `Exists [.zero])
    (setOf (setOf (pointAt (.bvar 1))))
    (mkLambda `tiles .default (setOf (setOf (pointAt (.bvar 1))))
      (mkApp3 (mkConst `SparseMonotiles.IsTiling []) (.bvar 2) (.bvar 1) (.bvar 0))))
  require (hasTiling.type.equal predicateType && hasTiling.value.equal hasValue)
    "HasTiling definition changed the existential physical tile collection"
  let model ← definition env `SparseMonotiles.IsAperiodicMonotile
  let compact := mkApp3 (mkConst `IsCompact [.zero]) (pointAt (.bvar 1))
    (topology (.bvar 1)) (.bvar 0)
  let existence := mkApp2 (mkConst `SparseMonotiles.HasTiling []) (.bvar 1) (.bvar 0)
  let aperiodic := mkApp2 (mkConst `SparseMonotiles.IsAperiodic []) (.bvar 1) (.bvar 0)
  let conjunction := mkApp2 (mkConst `And []) compact
    (mkApp2 (mkConst `And []) existence aperiodic)
  require (model.type.equal predicateType && model.value.equal (mkPrefix conjunction))
    "Monotile definition changed compactness, tiling, or aperiodicity conjunction"
  let bodyName := if fourD then `SpectreGeometry.polygonProductKeyBody
    else `LiteralPlanar.FanBounds.curvedBody
  let body ← definition env bodyName
  require (body.type.equal (setOf (mkConst spaceName []))) "Body type changed its space"
  -- The body VALUE and remaining model definitions are not authenticated here.


/-- Strict exact endpoint module set. Auxiliary declarations are not silently allowed.
Both the module payload and ownership map must contain only the named endpoint.
The first fresh compilation may expose legitimate generated helpers; any such mismatch
requires review and a new pinned allowlist, never automatic acceptance. -/
def validateOwnedNames (actual expected : Array Name) : Except String Unit := do
  require (actual.size == expected.size &&
    (actual.qsort Name.lt) == (expected.qsort Name.lt))
    s!"Exact module-owned declaration set mismatch: got {actual}, expected {expected}"

def checkModuleOwned (env : Environment) (moduleName : Name) (expected : Array Name) :
    Except String Unit := do
  let names := env.header.moduleNames
  let some idx := names.findIdx? (· == moduleName) | throw s!"Missing module: {moduleName}"
  let some data := env.header.moduleData[idx]? | throw "Missing module payload"
  require (data.constNames.size == data.constants.size) "Malformed module declaration payload"
  validateOwnedNames data.constNames expected
  for n in expected do
    let some modIdx := env.getModuleIdxFor? n | throw s!"No module owner: {n}"
    require (modIdx.toNat == idx) s!"Wrong module owner: {n}"
  let owned := env.const2ModIdx.toArray.filterMap fun (n, modIdx) =>
    if modIdx.toNat == idx then some n else none
  validateOwnedNames owned expected

def validateAxioms (axioms : Array Name) : Except String Unit := do
  for a in axioms do
    require (permittedAxioms.contains a) s!"Nonstandard transitive axiom: {a}"

/-- Inspect serialized constants without persistent-extension caches or project evaluation.
Unlike collectAxioms, missing referenced declarations fail closed. Includes types, all
available bodies, recursor rule bodies, and inductive constructor types. -/
def targetAxioms (env : Environment) (name : Name) : Except String (Array Name) := do
  let mut pending := #[name]
  let mut seen : Std.HashSet Name := {}
  let mut axioms := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | throw s!"Missing transitive dependency: {n}"
    require (!ci.isUnsafe && !ci.isPartial) s!"Unsafe/partial transitive dependency: {n}"
    pending := pending ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
    match ci with
    | .axiomInfo _ => axioms := axioms.push n
    | .inductInfo v => pending := pending ++ v.ctors.toArray
    | .recInfo v =>
      for rule in v.rules do pending := pending ++ rule.rhs.getUsedConstants
    | _ => pure ()
  let sortedAxioms := axioms.qsort Name.lt
  validateAxioms sortedAxioms
  return sortedAxioms

def audit (env : Environment) (fourD : Bool) : Except String (Array Name) := do
  require (env.header.trustLevel == 0) "Import trust level must be zero"
  checkModuleOwned env (endpointModule fourD) #[target fourD]
  let some ci := env.checked.get.find? (target fourD) | throw "Missing conditional endpoint"
  let _ ← validateTheorem fourD ci
  let some c := env.checked.get.find? parentType | throw "Missing C definition"
  validateParent c
  simpleAnchors env fourD
  targetAxioms env (target fourD)

end ConditionalEndpointAudit

/-- This helper must itself be compiled/run with only official Lean core on LEAN_PATH.
At runtime LEAN_PATH may contain only freshly staged project objects plus pinned official
and dependency objects. It never enables initializers or loads project plugins. -/
def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do throw <| IO.userError "No arguments: audit both fixed conditional endpoints"
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `NativeFinalAssembly.CurvedOfParent },
    { module := `NativeFinalAssembly.KeyedProductOfParent }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  for fourD in [false, true] do
    match ConditionalEndpointAudit.audit env fourD with
    | .error message => throw <| IO.userError message
    | .ok axioms =>
      let receipt := Json.mkObj [
        ("status", .str "CONDITIONAL_ENDPOINT_PASSED"),
        ("theorem", .str (ConditionalEndpointAudit.target fourD).toString),
        ("module", .str (ConditionalEndpointAudit.endpointModule fourD).toString),
        ("universe_parameters", .arr #[]),
        ("explicit_C_binders", toJson (1 : Nat)),
        ("C_type", .str ConditionalEndpointAudit.parentType.toString),
        ("exact_raw_type", .bool true), ("closed_type_and_proof", .bool true),
        ("C_definition_expansion", .bool true), ("exact_module_owned_set", .bool true),
        ("small_semantic_anchors_only", .bool true),
        ("transitive_axioms", .arr (axioms.map fun n => .str n.toString))]
      IO.println receipt.compress
  IO.println "CONDITIONAL_ENDPOINT_AUDIT_PASSED"
  return 0
