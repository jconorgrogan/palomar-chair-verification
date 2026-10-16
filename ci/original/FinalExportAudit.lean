/-
A trusted audit helper for the pinned hierarchy-C export contract.
This module imports only official toolchain libraries. It never imports project
objects or runs project elaborators. This file itself is not a proof of C.
-/
import Lake.Check.Axioms

open Lean

private def target : Name :=
  `SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem

private def expectedType : Name :=
  `SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem

private def permittedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

/-- Exact expanded contract of the named proposition. Binder names are irrelevant,
    but arity, binder visibility, named primitives, radius, and family are exact. -/
private def expandedContractMatches (value : Expr) : Bool :=
  match value with
  | .forallE _ (.forallE _ position state .default)
      (.forallE _ premise conclusion .default) .default =>
    position == mkConst `SpectreFinite.HexSearch.Position &&
    state == mkConst `SpectreFinite.HexSearch.State &&
    premise == mkApp (mkConst `SpectreFinite.HexSearch.GloballyLegal) (.bvar 0) &&
    conclusion == mkApp3 (mkConst `SpectreFinite.HexSearch.OccurrenceComplete)
      (.bvar 1) (mkApp (mkConst `SpectreFinite.HexSearch.hexRegion) (mkNatLit 5))
      (mkConst `SpectreFinite.HexSearch.ParentOwnership.certifiedParentFamily)
  | _ => false

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw <| IO.userError "Expected exactly one fresh NDJSON export path"
  let exported ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk path .read)
  let some info := exported.constMap[target]?
    | throw <| IO.userError "Required theorem is absent from export"
  let .thmInfo theoremInfo := info
    | throw <| IO.userError "Required declaration is not a theorem"
  unless theoremInfo.levelParams.isEmpty do
    throw <| IO.userError "Unexpected universe parameters"
  unless theoremInfo.type == mkConst expectedType do
    throw <| IO.userError "Exported theorem does not have the exact required named type"
  let some (.defnInfo propositionInfo) := exported.constMap[expectedType]?
    | throw <| IO.userError "Required named proposition is not an exported definition"
  unless propositionInfo.levelParams.isEmpty && propositionInfo.type == mkSort .zero &&
      expandedContractMatches propositionInfo.value do
    throw <| IO.userError "Named proposition differs from the exact expanded occurrence-completeness contract"
  match Lake.Check.checkAxioms exported #[target] #[] permittedAxioms with
  | .error message => throw <| IO.userError message
  | .ok () => pure ()
  IO.println "EXPORT_CONTRACT_AUDIT_PASSED"
  return 0
