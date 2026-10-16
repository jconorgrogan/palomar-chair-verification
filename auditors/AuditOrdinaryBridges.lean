/- SPDX-License-Identifier: Apache-2.0
Source audit helper; no proof generation. Research use remains pending.
Checks preserved builder contract plus exact module ownership.
Hardened variant adds ownership checks and uses Expr.equal for raw types/proofs/domains.
All original expression construction logic is preserved.
This variant explicitly fixes plugins := #[] and level := .private. -/
module
public import Lean.Environment
public import Lean.CoreM
public import Lean.Util.CollectAxioms
public section
open Lean

private def theoremInfo (env : Environment) (n : Name) : IO TheoremVal := do
  let some (.thmInfo v) := env.find? n | throw <| IO.userError s!"Not a theorem: {n}"
  return v

private def check (env : Environment) (n : Name) (us : List Name)
    (ty val : Expr) : IO Unit := do
  let got ← theoremInfo env n
  unless got.levelParams == us do throw <| IO.userError s!"Universe mismatch: {n}: {got.levelParams} expected {us}"
  unless got.type.equal ty do throw <| IO.userError s!"RAW TYPE MISMATCH: {n}"
  unless got.value.equal val do throw <| IO.userError s!"RAW PROOF MISMATCH: {n}\nGot: {reprStr got.value}\nExpected: {reprStr val}"
  unless !ty.hasLooseBVars && !ty.hasMVar && !ty.hasFVar &&
      !val.hasLooseBVars && !val.hasMVar && !val.hasFVar do
    throw <| IO.userError s!"Open expression: {n}"
  let (axs, _) ← (collectAxioms n : CoreM (Array Name)).toIO
    { fileName := "<ordinary-bridge-audit>", fileMap := default } { env := env }
  for a in axs do
    unless a == `propext || a == `Classical.choice || a == `Quot.sound do
      throw <| IO.userError s!"Nonstandard axiom: {a}"
  IO.println s!"EXACT_RAW_TYPE_PROOF_UNIVERSES_AXIOMS: {n}"

private def application (env : Environment) (seed transfer target : Name) : IO Unit := do
  let s ← theoremInfo env seed
  let t ← theoremInfo env transfer
  unless s.levelParams.isEmpty && t.levelParams.isEmpty do throw <| IO.userError "Unexpected application universes"
  let .forallE _ domain tail _ := t.type | throw <| IO.userError "Missing seed binder"
  unless domain.equal s.type do throw <| IO.userError "Seed raw type changed"
  check env target [] tail (mkApp (mkConst transfer []) (mkConst seed []))

private def curved (env : Environment) : IO Unit := do
  let seed := `SpectreGeometry.ReversePhysicalClusterCharts.exists_homochiral_P_tiling
  let reduction := `LiteralPlanar.Forward.curved_period_eq_zero_of_seed_and_planar_rigidity
  let planar := `SpectreGeometry.homochiral_physical_period_eq_zero_of_parent
  let parent := mkConst `SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem []
  let r ← theoremInfo env reduction
  let p ← theoremInfo env planar
  unless r.levelParams.length == 1 && p.levelParams.length == 1 do throw <| IO.userError "Curved universe count"
  let levels := r.levelParams.map Level.param
  let .forallE _ _ (.forallE _ _ tail _) _ := r.type | throw <| IO.userError "Curved reduction binders"
  let ty := mkForall `C .default parent tail
  let val := mkLambda `C .default parent
    (mkApp (mkApp (mkConst reduction levels) (mkConst seed []))
      (mkApp (mkConst planar levels) (mkBVar 0)))
  check env `KernelCurvedParentPilot.curved_period_eq_zero_of_parent r.levelParams ty val

private def product (env : Environment) : IO Unit := do
  let reduction := `SpectreGeometry.physical_polygon_product_period_eq_zero_of_planar_rigidity
  let planar := `SpectreGeometry.homochiral_physical_period_eq_zero_of_parent
  let parent := mkConst `SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem []
  let r ← theoremInfo env reduction
  let p ← theoremInfo env planar
  unless r.levelParams.length == 1 && p.levelParams.length == 1 do throw <| IO.userError "Product universe count"
  let levels := r.levelParams.map Level.param
  let .forallE _ _ tail _ := r.type | throw <| IO.userError "Product reduction binders"
  let ty := mkForall `C .default parent tail
  let val := mkLambda `C .default parent
    (mkApp (mkConst reduction levels) (mkApp (mkConst planar [.zero]) (mkBVar 0)))
  check env `KernelParentPilot.physical_polygon_product_period_eq_zero_of_parent r.levelParams ty val

namespace ExactModuleOwnership

private def require (ok : Bool) (message : String) : Except String Unit :=
  if ok then pure () else throw message

/-- Strict exact endpoint module set. Auxiliary declarations are not silently allowed.
Both the module payload and ownership map must contain only the named endpoint.
The first fresh compilation may expose legitimate generated helpers; any such mismatch
requires review and a new pinned allowlist, never automatic acceptance. -/
private def validateOwnedNames (actual expected : Array Name) : Except String Unit := do
  require (actual.size == expected.size &&
    (actual.qsort Name.lt) == (expected.qsort Name.lt))
    s!"Exact module-owned declaration set mismatch: got {actual}, expected {expected}"

private def checkModuleOwned (env : Environment) (moduleName : Name) (expected : Array Name) :
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

private def checkBridge (env : Environment) (moduleName name : Name) : IO Unit := do
  match checkModuleOwned env moduleName #[name] with
  | .ok _ => IO.println s!"EXACT_MODULE_OWNED_SET: {moduleName}: {name}"
  | .error error => throw <| IO.userError error

end ExactModuleOwnership

/-- Requires exactly the four freshly built ordinary modules on LEAN_PATH. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `KernelCurvedPilot.CurvedGeometryAndTiling },
    { module := `KernelCurvedParentPilot.CurvedPeriodFromParent },
    { module := `KernelSeedPilot.ProductPhysicalExistence },
    { module := `KernelParentPilot.ProductAperiodicityFromParent }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  ExactModuleOwnership.checkBridge env `KernelCurvedPilot.CurvedGeometryAndTiling
    `KernelCurvedPilot.existing_curved_geometry_and_tiling
  ExactModuleOwnership.checkBridge env `KernelCurvedParentPilot.CurvedPeriodFromParent
    `KernelCurvedParentPilot.curved_period_eq_zero_of_parent
  ExactModuleOwnership.checkBridge env `KernelSeedPilot.ProductPhysicalExistence
    `KernelSeedPilot.existing_physical_product_tiling
  ExactModuleOwnership.checkBridge env `KernelParentPilot.ProductAperiodicityFromParent
    `KernelParentPilot.physical_polygon_product_period_eq_zero_of_parent
  let seed := `SpectreGeometry.ReversePhysicalClusterCharts.exists_homochiral_P_tiling
  application env seed `LiteralPlanar.Forward.curved_geometry_and_tiling_of_original_seed
    `KernelCurvedPilot.existing_curved_geometry_and_tiling
  application env seed `SpectreGeometry.exists_physical_product_tiling_of_planar_seed
    `KernelSeedPilot.existing_physical_product_tiling
  curved env
  product env
  IO.println "ALL_FOUR_EXACT_RAW_BRIDGE_CONTRACTS_PASSED"
  return 0

