/- SPDX-License-Identifier: Apache-2.0
Core-only, read-only auditor for the unchanged finite metric certificate module.
The target is imported dynamically with no plugins and no extension initializers.
Public theorem inventory means module-owned theorem constants whose names are not
private names. The exact eight-name set is fixed below; private generated helpers
are separately inventoried. Every module-owned declaration is a raw dependency
root, so an unused local custom axiom is also rejected.

Six simple statement types are reconstructed independently and compared with
Expr.equal, including binder names and annotations. The two rational-binding
statement types are emitted raw but are not independently reconstructed. No proof
term identity, rational-coordinate recomputation, geometric identification,
hierarchy, endpoint, or final aperiodicity theorem is claimed. This auditor does
not replace the separately required official leanchecker pass. -/
module
public import Lean.Environment
public import Lean.CoreM
public import Lean.Util.CollectAxioms
public import Lean.PrivateName
public section
open Lean

private def targetModule : Name :=
  `SpectreGeometry.PolygonProductKeyReferenceFinite

private def expectedPublicTheorems : Array Name := #[
  `SpectreGeometry.ProductKeyReference.reference1_rational_binding,
  `SpectreGeometry.ProductKeyReference.reference1_fingerprint,
  `SpectreGeometry.ProductKeyReference.reference1_fingerprint_injective,
  `SpectreGeometry.ProductKeyReference.reference1_integerFingerprint_injective,
  `SpectreGeometry.ProductKeyReference.reference2_rational_binding,
  `SpectreGeometry.ProductKeyReference.reference2_fingerprint,
  `SpectreGeometry.ProductKeyReference.reference2_fingerprint_injective,
  `SpectreGeometry.ProductKeyReference.reference2_integerFingerprint_injective]

private def permittedAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def sorted (xs : Array Name) : Array Name := xs.qsort Name.lt

private def theoremInfo (env : Environment) (n : Name) : IO TheoremVal := do
  let some (.thmInfo v) := env.checked.get.find? n
    | throw <| IO.userError s!"NOT_RAW_THEOREM: {n}"
  return v

/-- Traverse actual raw constant bodies; do not trust an axiom-summary extension.
Unknown dependencies and an excessive graph fail closed. The graph cap bounds
only audit work and never permits acceptance of a truncated dependency graph. -/
private def rawAxioms (env : Environment) (roots : Array Name) : IO (Array Name) := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut visited := 0
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      visited := visited + 1
      require (visited ≤ 1000000) "RAW_DEPENDENCY_GRAPH_CAP_EXCEEDED"
      let some c := env.checked.get.find? n
        | throw <| IO.userError s!"MISSING_RAW_DEPENDENCY: {n}"
      let mut deps := c.type.getUsedConstants
      match c with
      | .axiomInfo _ =>
        require (permittedAxiom n) s!"FORBIDDEN_RAW_AXIOM: {n}"
        axioms := axioms.push n
      | .defnInfo v => deps := deps ++ v.value.getUsedConstants
      | .thmInfo v => deps := deps ++ v.value.getUsedConstants
      | .opaqueInfo v => deps := deps ++ v.value.getUsedConstants
      | .inductInfo v => deps := deps ++ v.ctors.toArray
      | _ => pure ()
      pending := deps.toList ++ pending
  return sorted axioms

private def moduleInventory (env : Environment) : IO (Array Name × Array Name) := do
  let some idx := env.header.moduleNames.findIdx? (· == targetModule)
    | throw <| IO.userError "TARGET_MODULE_MISSING"
  let some data := env.header.moduleData[idx]?
    | throw <| IO.userError "TARGET_MODULE_PAYLOAD_MISSING"
  require (data.constNames.size == data.constants.size) "MALFORMED_MODULE_PAYLOAD"
  let mut publicTheorems : Array Name := #[]
  let mut privateTheorems : Array Name := #[]
  for n in data.constNames, c in data.constants do
    require (n == c.name) s!"PAYLOAD_NAME_MISMATCH: {n}"
    let some owner := env.getModuleIdxFor? n
      | throw <| IO.userError s!"MODULE_OWNER_MISSING: {n}"
    require (owner.toNat == idx) s!"WRONG_MODULE_OWNER: {n}"
    let some raw := env.checked.get.find? n
      | throw <| IO.userError s!"PAYLOAD_CONSTANT_MISSING: {n}"
    require (raw.type.equal c.type) s!"PAYLOAD_RAW_TYPE_MISMATCH: {n}"
    match raw with
    | .axiomInfo _ => throw <| IO.userError s!"TARGET_OWNS_AXIOM: {n}"
    | .thmInfo _ =>
      if isPrivateName n then
        privateTheorems := privateTheorems.push n
      else
        publicTheorems := publicTheorems.push n
    | _ => pure ()
  require (sorted publicTheorems == sorted expectedPublicTheorems)
    s!"PUBLIC_THEOREM_SET_MISMATCH: got {sorted publicTheorems}; expected {sorted expectedPublicTheorems}"
  let mapTheorems := env.const2ModIdx.toArray.filterMap fun (n, owner) =>
    if owner.toNat == idx then
      match env.checked.get.find? n with
      | some (.thmInfo _) => if isPrivateName n then none else some n
      | _ => none
    else none
  require (sorted mapTheorems == sorted expectedPublicTheorems)
    s!"OWNERSHIP_MAP_THEOREM_SET_MISMATCH: {sorted mapTheorems}"
  IO.println s!"EXACT_MODULE_PUBLIC_THEOREMS: {sorted publicTheorems}"
  IO.println s!"PRIVATE_GENERATED_THEOREM_NAMES: {sorted privateTheorems}"
  IO.println s!"MODULE_RAW_CONSTANT_COUNT: {data.constNames.size}"
  return (data.constNames, sorted publicTheorems)

private def exactType (env : Environment) (name : Name) (expected : Expr) : IO Unit := do
  let got ← theoremInfo env name
  require got.levelParams.isEmpty s!"UNEXPECTED_THEOREM_UNIVERSES: {name}"
  require (!expected.hasLooseBVars && !expected.hasMVar && !expected.hasFVar)
    s!"OPEN_EXPECTED_TYPE: {name}"
  require (got.type.equal expected)
    s!"EXACT_RAW_TYPE_MISMATCH: {name}\nEXPECTED: {reprStr expected}\nACTUAL: {reprStr got.type}"
  IO.println s!"EXACT_RAW_TYPE_AND_UNIVERSES: {name}"

private def checkSimpleTypes (env : Environment) : IO Unit := do
  let fin9 := mkApp (mkConst `Fin []) (mkNatLit 9)
  let int := mkConst `Int []
  let one := Level.succ Level.zero
  let intFingerprint := mkConst `SpectreGeometry.ProductKeyReference.integerFingerprint []
  let injective := mkApp2 (mkConst `Function.Injective [one, one]) fin9 int
  let variants : Array (Name × Name × Name × Name × Name) := #[
    (`SpectreGeometry.ProductKeyReference.referenceVertices1,
     `SpectreGeometry.ProductKeyReference.referenceFingerprint1,
     `SpectreGeometry.ProductKeyReference.reference1_fingerprint,
     `SpectreGeometry.ProductKeyReference.reference1_fingerprint_injective,
     `SpectreGeometry.ProductKeyReference.reference1_integerFingerprint_injective),
    (`SpectreGeometry.ProductKeyReference.referenceVertices2,
     `SpectreGeometry.ProductKeyReference.referenceFingerprint2,
     `SpectreGeometry.ProductKeyReference.reference2_fingerprint,
     `SpectreGeometry.ProductKeyReference.reference2_fingerprint_injective,
     `SpectreGeometry.ProductKeyReference.reference2_integerFingerprint_injective)]
  for (verticesName, fingerprintName, equalityName, injectionName, derivedName) in variants do
    let fingerprint := mkConst fingerprintName []
    let calculated := mkApp intFingerprint (mkConst verticesName [])
    let equality := mkApp3 (mkConst `Eq [one]) int
      (mkApp calculated (mkBVar 0)) (mkApp fingerprint (mkBVar 0))
    exactType env equalityName (mkForall `i .default fin9 equality)
    exactType env injectionName (mkApp injective fingerprint)
    exactType env derivedName (mkApp injective calculated)

/-- Execute only after independently checked artifacts are selected by LEAN_PATH. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := targetModule }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  require (env.header.trustLevel == 0) "NONZERO_IMPORT_TRUST_LEVEL"
  let (allOwned, publicTheorems) ← moduleInventory env
  let allAxioms ← rawAxioms env allOwned
  IO.println s!"ALL_MODULE_OWNED_RAW_DEPENDENCY_AXIOMS: {allAxioms}"
  let mut renderedChars := 0
  for name in publicTheorems do
    let thm ← theoremInfo env name
    require thm.levelParams.isEmpty s!"UNEXPECTED_PUBLIC_THEOREM_UNIVERSES: {name}"
    require (!thm.type.hasLooseBVars && !thm.type.hasMVar && !thm.type.hasFVar)
      s!"OPEN_RAW_THEOREM_TYPE: {name}"
    let rawType := reprStr thm.type
    renderedChars := renderedChars + rawType.length
    require (rawType.length ≤ 65536 && renderedChars ≤ 262144) "RAW_TYPE_OUTPUT_CAP_EXCEEDED"
    let axs ← rawAxioms env #[name]
    let (officialAxioms, _) ← (collectAxioms name : CoreM (Array Name)).toIO
      { fileName := "<async-target-audit>", fileMap := default } { env := env }
    require (sorted officialAxioms == axs) s!"AXIOM_COLLECTOR_DISAGREEMENT: {name}"
    IO.println s!"PUBLIC_THEOREM: {name}"
    IO.println s!"RAW_UNIVERSES: {thm.levelParams}"
    IO.println s!"RAW_TYPE: {rawType}"
    IO.println s!"RAW_TRANSITIVE_AXIOMS: {axs}"
  checkSimpleTypes env
  IO.println "RATIONAL_BINDING_TYPES: RAW_INVENTORY_ONLY_NO_INDEPENDENT_TYPE_RECONSTRUCTION"
  IO.println "AUDIT_SCOPE: FINITE_METRIC_CERTIFICATES_ONLY_NO_FINAL_GEOMETRY_OR_APERIODICITY_THEOREM"
  IO.println "ASYNC_TARGET_RAW_AUDIT_PASSED_NO_FINAL_THEOREM"
  return 0
