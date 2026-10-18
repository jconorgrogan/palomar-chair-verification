/- SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan. AI assistance: OpenAI assistant.
Unelaborated source proposal. Core-only serialized-data inspector. The three
explicit modes are separate future gates, never an assertion that they ran.
No project proof imports, extension initialization, project evaluation, added
axioms or declarations. Source provenance and kernel checking remain external.
-/
module
public import Lean.Environment
public import Lean.Data.Json
@[expose] public section
open Lean
namespace UniformPhysicalAudit

def referenceModule : Name := `UniformPhysicalReference
def nativeModelModule : Name := `SparseMonotiles.Model
def conditionalModule : Name := `NativeFinalAssembly.AllDimensionsOfParent
def closedModule : Name := `NativeFinalAssembly.AllDimensions
def challengeModule : Name := `PalomarAllDimensionsChallenge
def solutionModule : Name := `PalomarAllDimensionsSolution
def parentModule : Name := `SpectreFinite.NativeCoarsening
def parentType : Name := `SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem
def parentProofModule : Name := `SpectreFinite.RadiusFivePruningHierarchy
def parentProof : Name := `SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem

def conditionalModel : Name := `NativeFinalAssembly.exists_model_monotile_in_every_dimension_ge_two_of_parent
def conditionalExpanded : Name := `NativeFinalAssembly.exists_physical_aperiodic_monotile_in_every_dimension_ge_two_of_parent
def closedExpanded : Name := `NativeFinalAssembly.exists_physical_aperiodic_monotile_in_every_dimension_ge_two
def registrationTarget : Name := `PalomarAllDimensions.aperiodic_monotile_in_every_dimension

def nativeMap : Array (Name × Name) := #[
  (`UniformPhysicalReference.Point, `SparseMonotiles.Point),
  (`UniformPhysicalReference.IsTiling, `SparseMonotiles.IsTiling),
  (`UniformPhysicalReference.translate, `SparseMonotiles.translate),
  (`UniformPhysicalReference.IsPeriod, `SparseMonotiles.IsPeriod),
  (`UniformPhysicalReference.HasTiling, `SparseMonotiles.HasTiling),
  (`UniformPhysicalReference.IsAperiodic, `SparseMonotiles.IsAperiodic),
  (`UniformPhysicalReference.IsAperiodicMonotile, `SparseMonotiles.IsAperiodicMonotile)]

def registrationMap : Array (Name × Name) := #[
  (`UniformPhysicalReference.Point, `PalomarAllDimensions.Point),
  (`UniformPhysicalReference.IsTiling, `PalomarAllDimensions.IsTiling),
  (`UniformPhysicalReference.translate, `PalomarAllDimensions.translate),
  (`UniformPhysicalReference.IsPeriod, `PalomarAllDimensions.IsPeriod),
  (`UniformPhysicalReference.HasTiling, `PalomarAllDimensions.HasTiling),
  (`UniformPhysicalReference.IsAperiodic, `PalomarAllDimensions.IsAperiodic)]

def templates : Array Name := #[`UniformPhysicalReference.ExpectedConditionalModel,
  `UniformPhysicalReference.ExpectedConditionalExpanded, `UniformPhysicalReference.ExpectedClosedExpanded,
  `UniformPhysicalReference.ExpectedRegistration]

def permittedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]
def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then pure () else throw message

def closed (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && !e.hasLevelParam

/-- Only two fixed injective namespace maps are supported. No general reduction,
alpha-equivalence, coercion insertion, or arbitrary renaming is accepted. -/
def mappedReference (registration : Bool) (e : Expr) : Except String Expr := do
  let pairs := if registration then registrationMap else nativeMap
  for n in e.getUsedConstants do
    if referenceModule.isPrefixOf n then
      require (pairs.any fun pair => pair.1 == n) s!"Unmapped independent constant: {n}"
  return e.replace fun part => match part with
    | .const n us =>
      match pairs.find? (fun pair => pair.1 == n) with
      | some pair => some (.const pair.2 us)
      | none => none
    | _ => none

def definition (env : Environment) (name : Name) : Except String DefinitionVal := do
  let some (.defnInfo value) := env.checked.get.find? name | throw s!"Missing definition: {name}"
  require (value.name == name && value.levelParams.isEmpty && value.safety == .safe &&
    closed value.type && closed value.value) s!"Unsafe, open, or polymorphic definition: {name}"
  return value

def checkOwner (env : Environment) (moduleName declaration : Name) : Except String Unit := do
  let some index := env.header.moduleNames.findIdx? (· == moduleName) | throw s!"Missing owner: {moduleName}"
  let some payload := env.header.moduleData[index]? | throw "Missing module payload"
  require (payload.constNames.size == payload.constants.size && payload.constNames.contains declaration)
    "Malformed owner payload or missing declaration"
  let some actual := env.getModuleIdxFor? declaration | throw "Missing declaration owner"
  require (actual.toNat == index) "Declaration ownership mismatch"

def checkOwnedSet (env : Environment) (moduleName : Name) (expected : Array Name) : Except String Unit := do
  let some index := env.header.moduleNames.findIdx? (· == moduleName) | throw "Missing exact owner module"
  let some payload := env.header.moduleData[index]? | throw "Missing exact owner payload"
  let actual := env.const2ModIdx.toArray.filterMap fun (n, i) => if i.toNat == index then some n else none
  require (payload.constNames.size == payload.constants.size && payload.constNames.size == expected.size &&
    actual.size == expected.size && payload.constNames.qsort Name.lt == expected.qsort Name.lt &&
    actual.qsort Name.lt == expected.qsort Name.lt) "Exact module-owned declaration set mismatch"
  for n in expected do checkOwner env moduleName n

def auditReference (env : Environment) : Except String Unit := do
  require (env.header.trustLevel == 0) "Reference trust must be zero"
  checkOwnedSet env referenceModule ((nativeMap.map Prod.fst) ++ templates)
  for moduleName in env.header.moduleNames do
    require (!(#[`SparseMonotiles, `SpectreFinite, `SpectreGeometry, `LiteralPlanar,
      `ClarkSeed, `NativeFinalAssembly, `PalomarAllDimensionsChallenge,
      `PalomarAllDimensionsSolution].any fun ns => ns.isPrefixOf moduleName))
      "Reference imports research semantics or proof"

def validateDefinitionPair (registration : Bool) (reference native : DefinitionVal) : Except String Unit := do
  let pairs := if registration then registrationMap else nativeMap
  require (pairs.contains (reference.name, native.name)) "Model name pair mismatch"
  require (reference.levelParams.isEmpty && native.levelParams.isEmpty &&
    reference.safety == .safe && native.safety == .safe && closed reference.type &&
    closed reference.value && closed native.type && closed native.value) "Invalid model definition"
  let expectedType ← mappedReference registration reference.type
  let expectedValue ← mappedReference registration reference.value
  require (native.type.equal expectedType && native.value.equal expectedValue) "Exact raw model mismatch"

def auditModel (reference project : Environment) (registration : Bool) (owner : Name) : Except String Unit := do
  require (project.header.trustLevel == 0) "Project import trust must be zero"
  let pairs := if registration then registrationMap else nativeMap
  for pair in pairs do
    checkOwner project owner pair.2
    validateDefinitionPair registration (← definition reference pair.1) (← definition project pair.2)

/-- Source-derived exact C expansion, retaining the previously accepted binder-
name-independent shape but fixing all binder visibility, domains and indices. -/
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

def auditParent (project : Environment) : Except String Unit := do
  checkOwner project parentModule parentType
  let value ← definition project parentType
  require (value.type.equal (mkSort .zero) && expandedParentMatches value.value)
    "ParentOccurrenceTheorem is not the exact independently specified C definition"

/-- One explicitly specified capture-safe substitution. CType is bound data, not
an axiom. No general beta/delta reduction is permitted. -/
def instantiateConditional (value : Expr) : Except String Expr := do
  let .lam name domain body .default := value | throw "Missing bound CType parameter"
  require (name == `CType && domain.equal (mkSort .zero) && closed value) "Changed CType parameter"
  let result := body.instantiate1 (mkConst parentType [])
  require (closed result) "C substitution left an open expression"
  return result

def expectedType (reference : Environment) (template : Name) : Except String Expr := do
  require (templates.contains template) "Unreviewed reference template"
  let value ← definition reference template
  let conditional := template == `UniformPhysicalReference.ExpectedConditionalModel ||
    template == `UniformPhysicalReference.ExpectedConditionalExpanded
  let registration := template == `UniformPhysicalReference.ExpectedRegistration
  let shape := if conditional then mkForall `CType .default (mkSort .zero) (mkSort .zero) else mkSort .zero
  require (value.type.equal shape) "Reference template type changed"
  let result ← if conditional then instantiateConditional value.value else pure value.value
  mappedReference registration result

def validateTheorem (target : Name) (expected : Expr) (ci : ConstantInfo) : Except String TheoremVal := do
  require ((#[conditionalModel, conditionalExpanded, closedExpanded, registrationTarget, parentProof]).contains target)
    "Unreviewed target"
  let .thmInfo value := ci | throw "Target is not a theorem"
  require (value.name == target && value.levelParams.isEmpty && closed value.type && closed value.value &&
    value.type.equal expected) "Exact theorem name, universes, closedness or raw type mismatch"
  return value

def validateAxioms (challenge : Bool) (axioms : Array Name) : Except String Unit := do
  for n in axioms do require (permittedAxioms.contains n || (challenge && n == `sorryAx)) s!"Unpermitted axiom: {n}"
  if challenge then require (axioms.contains `sorryAx) "Challenge hole unexpectedly absent"

def targetAxioms (env : Environment) (target : Name) (challenge : Bool := false) : Except String (Array Name) := do
  let mut pending := #[target]
  let mut seen : Std.HashSet Name := {}
  let mut axioms := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | throw s!"Missing transitive dependency: {n}"
    require (!ci.isUnsafe && !ci.isPartial) s!"Unsafe/partial dependency: {n}"
    pending := pending ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then pending := pending ++ value.getUsedConstants
    match ci with
    | .axiomInfo _ => axioms := axioms.push n
    | .inductInfo value => pending := pending ++ value.ctors.toArray
    | .recInfo value =>
      for rule in value.rules do pending := pending ++ rule.rhs.getUsedConstants
    | _ => pure ()
  let result := axioms.qsort Name.lt
  validateAxioms challenge result
  return result

def auditEndpoint (reference project : Environment) (owner template target : Name) : Except String (Array Name) := do
  require ((#[( `UniformPhysicalReference.ExpectedConditionalModel, conditionalModel),
    (`UniformPhysicalReference.ExpectedConditionalExpanded, conditionalExpanded),
    (`UniformPhysicalReference.ExpectedClosedExpanded, closedExpanded)]).contains (template, target))
    "Template/target pairing changed"
  checkOwner project owner target
  let some value := project.checked.get.find? target | throw "Missing endpoint"
  let _ ← validateTheorem target (← expectedType reference template) value
  targetAxioms project target

/-- The closed native proof must be the explicit application of the accepted
conditional theorem to the exact checked C theorem, then d and hd. -/
def expectedClosedProof (type : Expr) : Except String Expr := do
  let .forallE d dType (.forallE hd hdType _ .default) .default := type | throw "Closed theorem binder shape changed"
  require (d == `d && hd == `hd) "Closed theorem binder names changed"
  return mkLambda d .default dType (mkLambda hd .default hdType
    (mkApp3 (mkConst conditionalExpanded []) (mkConst parentProof []) (.bvar 1) (.bvar 0)))

def auditClosedApplication (project : Environment) : Except String Unit := do
  checkOwner project parentProofModule parentProof
  let some c := project.checked.get.find? parentProof | throw "Missing checked C theorem"
  let _ ← validateTheorem parentProof (mkConst parentType []) c
  let some (.thmInfo value) := project.checked.get.find? closedExpanded | throw "Missing closed theorem"
  require (value.value.equal (← expectedClosedProof value.type)) "Closed theorem is not the exact C application"

end UniformPhysicalAudit

def loadData (moduleName : Name) : IO Environment :=
  importModules #[{module := moduleName}] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)

def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

def emit (mode : String) (target : Name) (axioms : Array Name) (cBinders : Nat) : IO Unit :=
  IO.println (Json.mkObj [
    ("schema", .str "uniform-physical-endpoint-audit-v1"), ("status", .str "pass"),
    ("mode", .str mode), ("target", .str target.toString),
    ("reference_module", .str "UniformPhysicalReference"), ("level_params", .arr #[]),
    ("axioms", .arr (axioms.map fun n => .str n.toString)), ("explicit_C_binders", toJson cBinders),
    ("raw_type_equal", .bool true), ("raw_model_equal", .bool true),
    ("closed_type_and_proof", .bool true), ("endpoint_module_owned_set", .bool true),
    ("trust_level", toJson (0 : Nat)), ("plugins_enabled", .bool false),
    ("extensions_loaded", .bool false)]).compress

def main (args : List String) : IO UInt32 := do
  let [mode] := args | throw <| IO.userError "One explicit mode required: conditional, closed, registration"
  unless ["conditional", "closed", "registration"].contains mode do throw <| IO.userError "Unknown mode"
  initSearchPath (← findSysroot)
  let reference ← loadData `UniformPhysicalReference
  checked (UniformPhysicalAudit.auditReference reference)
  if mode == "conditional" || mode == "closed" then
    let project ← loadData (if mode == "conditional" then `NativeFinalAssembly.AllDimensionsOfParent else `NativeFinalAssembly.AllDimensions)
    checked (UniformPhysicalAudit.auditModel reference project false `SparseMonotiles.Model)
    checked (UniformPhysicalAudit.auditParent project)
    checked (UniformPhysicalAudit.checkOwnedSet project `NativeFinalAssembly.AllDimensionsOfParent
      #[UniformPhysicalAudit.conditionalModel, UniformPhysicalAudit.conditionalExpanded])
    for pair in #[(`UniformPhysicalReference.ExpectedConditionalModel, UniformPhysicalAudit.conditionalModel),
                  (`UniformPhysicalReference.ExpectedConditionalExpanded, UniformPhysicalAudit.conditionalExpanded)] do
      let axioms ← checked (UniformPhysicalAudit.auditEndpoint reference project `NativeFinalAssembly.AllDimensionsOfParent pair.1 pair.2)
      emit mode pair.2 axioms 1
    if mode == "closed" then
      checked (UniformPhysicalAudit.checkOwnedSet project `NativeFinalAssembly.AllDimensions #[UniformPhysicalAudit.closedExpanded])
      checked (UniformPhysicalAudit.auditClosedApplication project)
      let axioms ← checked (UniformPhysicalAudit.auditEndpoint reference project `NativeFinalAssembly.AllDimensions
        `UniformPhysicalReference.ExpectedClosedExpanded UniformPhysicalAudit.closedExpanded)
      emit mode UniformPhysicalAudit.closedExpanded axioms 0
  else
    let challenge ← loadData `PalomarAllDimensionsChallenge
    let solution ← loadData `PalomarAllDimensionsSolution
    for moduleName in challenge.header.moduleNames do
      unless !(#[`SparseMonotiles, `SpectreFinite, `SpectreGeometry, `LiteralPlanar,
        `ClarkSeed, `NativeFinalAssembly, `PalomarAllDimensionsSolution].any fun ns => ns.isPrefixOf moduleName) do
        throw <| IO.userError "Independent Challenge imported research semantics or proof"
    unless !(solution.header.moduleNames.contains `PalomarAllDimensionsChallenge) do
      throw <| IO.userError "Solution imported the Challenge hole"
    for pair in #[(challenge, `PalomarAllDimensionsChallenge), (solution, `PalomarAllDimensionsSolution)] do
      checked (UniformPhysicalAudit.auditModel reference pair.1 true pair.2)
      checked (UniformPhysicalAudit.checkOwnedSet pair.1 pair.2
        ((UniformPhysicalAudit.registrationMap.map Prod.snd).push UniformPhysicalAudit.registrationTarget))
      let expected ← checked (UniformPhysicalAudit.expectedType reference `UniformPhysicalReference.ExpectedRegistration)
      let some value := pair.1.checked.get.find? UniformPhysicalAudit.registrationTarget
        | throw <| IO.userError "Missing independent registration statement"
      let _ ← checked (UniformPhysicalAudit.validateTheorem UniformPhysicalAudit.registrationTarget expected value)
    let challengeAxioms ← checked (UniformPhysicalAudit.targetAxioms challenge UniformPhysicalAudit.registrationTarget true)
    let solutionAxioms ← checked (UniformPhysicalAudit.targetAxioms solution UniformPhysicalAudit.registrationTarget)
    IO.println (Json.mkObj [("schema", .str "uniform-challenge-statement-audit-v1"),
      ("status", .str "statement_only_intentional_hole"), ("proof_pass_claimed", .bool false),
      ("axioms", .arr (challengeAxioms.map fun n => .str n.toString)), ("raw_type_equal", .bool true),
      ("raw_model_equal", .bool true), ("exact_module_owned_set", .bool true)]).compress
    emit "registration" UniformPhysicalAudit.registrationTarget solutionAxioms 0
  IO.println s!"UNIFORM_PHYSICAL_ENDPOINT_AUDIT_PASSED {mode}"
  return 0
