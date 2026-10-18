/- SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan. AI assistance: OpenAI assistant.
Draft, unelaborated. Core-only serialized-data inspector for two fixed higher
endpoints. No project imports, plugins, extension initializers or project execution.
A pass establishes exact statement/model agreement and an axiom inventory only;
fresh source provenance and independent kernel checking remain external gates.
-/
module
public import Lean.Environment
public import Lean.Data.Json
@[expose] public section
open Lean
namespace HigherPhysicalAudit

def referenceModule : Name := `HigherPhysicalReference
def modelModule : Name := `SparseMonotiles.Model
def targetModule : Name := `ClarkSeed.PhysicalDimensions

def modelMap : Array (Name × Name) := #[
  (`HigherPhysicalReference.Point, `SparseMonotiles.Point),
  (`HigherPhysicalReference.IsTiling, `SparseMonotiles.IsTiling),
  (`HigherPhysicalReference.translate, `SparseMonotiles.translate),
  (`HigherPhysicalReference.IsPeriod, `SparseMonotiles.IsPeriod),
  (`HigherPhysicalReference.HasTiling, `SparseMonotiles.HasTiling),
  (`HigherPhysicalReference.IsAperiodic, `SparseMonotiles.IsAperiodic),
  (`HigherPhysicalReference.IsAperiodicMonotile, `SparseMonotiles.IsAperiodicMonotile)]

def targets : Array (Name × Name) := #[
  (`HigherPhysicalReference.ExpectedGeFive,
    `ClarkSeed.exists_physical_aperiodic_monotile_of_ge_five),
  (`HigherPhysicalReference.ExpectedGeThreeNeFour,
    `ClarkSeed.exists_physical_aperiodic_monotile_of_ge_three_ne_four)]

def permittedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then pure () else throw message

def closed (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && !e.hasLevelParam

/-- The only allowed expression transformation is this fixed injective constant
renaming. Binder names/annotations, universes and every other node are retained.
Unknown reference-local constants cannot silently become new model assumptions. -/
def mappedReference (e : Expr) : Except String Expr := do
  for n in e.getUsedConstants do
    if referenceModule.isPrefixOf n then
      require (modelMap.any fun pair => pair.1 == n)
        s!"Unmapped reference model constant: {n}"
  return e.replace fun part => match part with
    | .const n us =>
      match modelMap.find? (fun pair => pair.1 == n) with
      | some pair => some (.const pair.2 us)
      | none => none
    | _ => none

def validateDefinitionPair (reference native : DefinitionVal) : Except String Unit := do
  require (modelMap.contains (reference.name, native.name)) "Model declaration name pair mismatch"
  require (reference.levelParams.isEmpty && native.levelParams.isEmpty)
    "Model universe parameters must be []"
  require (reference.safety == .safe && native.safety == .safe) "Unsafe model definition"
  require (closed reference.type && closed reference.value && closed native.type && closed native.value)
    "Open model definition"
  let expectedType ← mappedReference reference.type
  let expectedValue ← mappedReference reference.value
  require (native.type.equal expectedType) s!"Raw model type mismatch: {native.name}"
  require (native.value.equal expectedValue) s!"Raw model value mismatch: {native.name}"

def definition (env : Environment) (name : Name) : Except String DefinitionVal := do
  let some (.defnInfo value) := env.checked.get.find? name
    | throw s!"Missing or non-definition reference/model declaration: {name}"
  return value

def checkOwner (env : Environment) (moduleName declaration : Name) : Except String Unit := do
  let some index := env.header.moduleNames.findIdx? (· == moduleName)
    | throw s!"Missing owner module: {moduleName}"
  let some moduleData := env.header.moduleData[index]? | throw "Missing owner module payload"
  require (moduleData.constNames.size == moduleData.constants.size) "Malformed owner module payload"
  require (moduleData.constNames.contains declaration) s!"Declaration absent from owner payload: {declaration}"
  let some actual := env.getModuleIdxFor? declaration | throw s!"Missing declaration owner: {declaration}"
  require (actual.toNat == index) s!"Wrong declaration owner: {declaration}"

/-- Only the independent reference has a complete owned-name allowlist. The
research modules legitimately contain other geometry and proof declarations. -/
def checkReferenceOwnedSet (env : Environment) : Except String Unit := do
  let expected := (modelMap.map Prod.fst) ++ (targets.map Prod.fst)
  let some index := env.header.moduleNames.findIdx? (· == referenceModule)
    | throw "Missing independent reference module"
  let some data := env.header.moduleData[index]? | throw "Missing independent reference payload"
  require (data.constNames.size == data.constants.size) "Malformed reference payload"
  let actual := env.const2ModIdx.toArray.filterMap fun (n, i) =>
    if i.toNat == index then some n else none
  require (data.constNames.size == expected.size && actual.size == expected.size &&
    data.constNames.qsort Name.lt == expected.qsort Name.lt &&
    actual.qsort Name.lt == expected.qsort Name.lt) "Exact independent reference owned set mismatch"
  require (!(env.header.moduleNames.contains modelModule) &&
    !(env.header.moduleNames.contains targetModule)) "Reference imported project semantics or proof"
  for n in expected do checkOwner env referenceModule n

def expectedType (env : Environment) (template : Name) : Except String Expr := do
  require (targets.any fun pair => pair.1 == template) "Unknown reference template"
  let value ← definition env template
  require (value.name == template && value.levelParams.isEmpty && value.safety == .safe &&
    value.type.equal (mkSort .zero) && closed value.value) "Invalid proposition-valued reference template"
  mappedReference value.value

def validateTheorem (target : Name) (expected : Expr) (info : ConstantInfo) : Except String Unit := do
  let .thmInfo value := info | throw "Missing or non-theorem higher endpoint"
  require (targets.any fun pair => pair.2 == target) "Unknown higher endpoint"
  require (value.name == target && value.levelParams.isEmpty) "Endpoint name/universes differ"
  require (closed value.type && closed value.value) "Open endpoint type or proof"
  -- Expr.equal includes binder names and annotations. Expr BEq does not.
  require (value.type.equal expected) "Exact quantified higher endpoint raw type mismatch"

def validateAxioms (axioms : Array Name) : Except String Unit := do
  for name in axioms do
    require (permittedAxioms.contains name) s!"Nonstandard transitive axiom: {name}"

def targetAxioms (env : Environment) (target : Name) : Except String (Array Name) := do
  let mut pending := #[target]
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
    | .inductInfo value => pending := pending ++ value.ctors.toArray
    | .recInfo value =>
      for rule in value.rules do pending := pending ++ rule.rhs.getUsedConstants
    | _ => pure ()
  let result := axioms.qsort Name.lt
  validateAxioms result
  return result

def auditModel (reference project : Environment) : Except String Unit := do
  require (reference.header.trustLevel == 0 && project.header.trustLevel == 0)
    "Both serialized imports require trust zero"
  checkReferenceOwnedSet reference
  for pair in modelMap do
    checkOwner project modelModule pair.2
    validateDefinitionPair (← definition reference pair.1) (← definition project pair.2)

def auditEndpoint (reference project : Environment) (template target : Name) :
    Except String (Array Name) := do
  require (targets.contains (template, target)) "Template/target pairing changed"
  checkOwner project targetModule target
  let expected ← expectedType reference template
  let some value := project.checked.get.find? target | throw "Missing higher endpoint"
  validateTheorem target expected value
  targetAxioms project target

end HigherPhysicalAudit

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do throw <| IO.userError "No arguments: audit both fixed higher-only endpoints"
  IO.println "HIGHER_AUDIT_PHASE entry"
  initSearchPath (← findSysroot)
  let reference ← importModules #[{module := `HigherPhysicalReference}] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  IO.println "HIGHER_AUDIT_PHASE reference_import_returned"
  let project ← importModules #[{module := `ClarkSeed.PhysicalDimensions}] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  IO.println "HIGHER_AUDIT_PHASE project_import_returned"
  match HigherPhysicalAudit.auditModel reference project with
  | .error message => throw <| IO.userError message
  | .ok () => pure ()
  IO.println "HIGHER_AUDIT_PHASE model_checked"
  for pair in HigherPhysicalAudit.targets do
    match HigherPhysicalAudit.auditEndpoint reference project pair.1 pair.2 with
    | .error message => throw <| IO.userError message
    | .ok axioms =>
      let second := pair.1 == `HigherPhysicalReference.ExpectedGeThreeNeFour
      IO.println (Json.mkObj [
        ("schema", .str "higher-physical-endpoint-audit-v1"), ("status", .str "pass"),
        ("mode", .str "higher-only"), ("target", .str pair.2.toString),
        ("module", .str HigherPhysicalAudit.targetModule.toString),
        ("reference_module", .str HigherPhysicalAudit.referenceModule.toString),
        ("reference_template", .str pair.1.toString),
        ("model_module", .str HigherPhysicalAudit.modelModule.toString),
        ("model_definitions", .arr (HigherPhysicalAudit.modelMap.map fun p => .str p.2.toString)),
        ("level_params", .arr #[]), ("axioms", .arr (axioms.map fun n => .str n.toString)),
        ("explicit_binders", .arr ((if second then #["d", "hd", "hne"] else #["d", "hd"]).map Json.str)),
        ("explicit_hypotheses", .arr ((if second then #["3 ≤ d", "d ≠ 4"] else #["5 ≤ d"]).map Json.str)),
        ("raw_type_equal", .bool true), ("raw_model_equal", .bool true),
        ("closed_type_and_proof", .bool true), ("selected_declaration_ownership", .bool true),
        ("exact_reference_owned_set", .bool true),
        ("trust_level", toJson (0 : Nat)), ("plugins_enabled", .bool false),
        ("extensions_loaded", .bool false)]).compress
      IO.println "HIGHER_AUDIT_PHASE endpoint_checked"
  IO.println "HIGHER_PHYSICAL_ENDPOINT_AUDIT_PASSED"
  return 0
