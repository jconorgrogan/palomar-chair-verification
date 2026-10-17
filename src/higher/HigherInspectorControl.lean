/- SPDX-License-Identifier: Apache-2.0
Core-only controls for the inspector's exact expression/name/axiom gates.
Synthetic Expr records are data, never admitted as declarations. This is not a
physical model elaboration, kernel check, or proof of either target theorem.
-/
module
import Lean.Elab.BuiltinEvalCommand
import AuditHigherPhysicalEndpoints
meta import AuditHigherPhysicalEndpoints
meta import Lean.Elab.Command
open Lean Elab Command
open HigherPhysicalAudit

namespace HigherInspectorControl

def refPoint (d : Expr) : Expr := mkApp (mkConst `HigherPhysicalReference.Point []) d
def setOf (type : Expr) : Expr := mkApp (mkConst `Set [.zero]) type

def hasTilingValue : Expr :=
  mkLambda `d .implicit (mkConst `Nat [])
    (mkLambda `T .default (setOf (refPoint (.bvar 0)))
      (mkApp2 (mkConst `Exists [.succ .zero]) (setOf (setOf (refPoint (.bvar 1))))
        (mkLambda `tiles .default (setOf (setOf (refPoint (.bvar 1))))
          (mkApp3 (mkConst `HigherPhysicalReference.IsTiling []) (.bvar 2) (.bvar 1) (.bvar 0)))))

def refDefinition : DefinitionVal := {
  name := `HigherPhysicalReference.HasTiling, levelParams := [],
  type := mkForall `d .implicit (mkConst `Nat [])
    (mkForall `T .default (setOf (refPoint (.bvar 0))) (mkSort .zero)),
  value := hasTilingValue, hints := .abbrev, safety := .safe }

def mutateConstant (e : Expr) (before after : Name) : Expr :=
  e.replace fun part => match part with
    | .const n us => if n == before then some (.const after us) else none
    | _ => none

def expected : Expr :=
  mkForall `d .default (mkConst `Nat [])
    (mkForall `hd .default (mkApp2 (mkConst `Nat.le []) (mkNatLit 5) (.bvar 0))
      (mkApp2 (mkConst `Exists [.succ .zero])
        (setOf (mkApp (mkConst `SparseMonotiles.Point []) (.bvar 1)))
        (mkLambda `T .default (setOf (mkApp (mkConst `SparseMonotiles.Point []) (.bvar 1)))
          (mkApp2 (mkConst `SparseMonotiles.IsAperiodicMonotile []) (.bvar 2) (.bvar 0)))))

def theoremValue (type : Expr) : ConstantInfo := .thmInfo {
  name := `ClarkSeed.exists_physical_aperiodic_monotile_of_ge_five,
  levelParams := [], type := type, value := mkConst `True.intro [] }

def assertTrue (condition : Bool) (label : String) : CommandElabM Unit := do
  unless condition do throwError "Control failed: {label}"
  liftIO <| IO.println s!"PASS {label}"

def succeeds {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

run_cmd do
  let .ok mappedType := mappedReference refDefinition.type | throwError "reference type mapping failed"
  let .ok mappedValue := mappedReference refDefinition.value | throwError "reference value mapping failed"
  let native := { refDefinition with
    name := `SparseMonotiles.HasTiling,
    type := mappedType, value := mappedValue }
  assertTrue (succeeds (validateDefinitionPair refDefinition native)) "exact mapped model definition"
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with
    name := `SparseMonotiles.RenamedHasTiling})) "renamed native model constant rejected"
  assertTrue (!succeeds (mappedReference (mkConst `HigherPhysicalReference.Extra [])))
    "extra reference model constant rejected"
  assertTrue (!succeeds (mappedReference (mkConst `HigherPhysicalReference.HasTiling.Extra [])))
    "nested extra reference model constant rejected"
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with
    value := mutateConstant native.value `SparseMonotiles.IsTiling `SparseMonotiles.OtherIsTiling}))
    "changed HasTiling predicate rejected"
  let wrongUniverse := native.value.replace fun e => match e with
    | .const n _ => if n == `Exists then some (.const n [.zero]) else none
    | _ => none
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with value := wrongUniverse}))
    "changed HasTiling existential universe rejected"
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with value := mkConst `True []}))
    "missing HasTiling existential rejected"
  let periodReference : DefinitionVal := { refDefinition with
    name := `HigherPhysicalReference.IsPeriod,
    value := mkApp2 (mkConst `Iff []) (mkConst `CollectionMembership [])
      (mkApp (mkConst `HigherPhysicalReference.translate []) (mkConst `Tile [])) }
  let .ok periodValue := mappedReference periodReference.value | throwError "period mapping failed"
  let periodNative := {native with name := `SparseMonotiles.IsPeriod, value := periodValue}
  assertTrue (succeeds (validateDefinitionPair periodReference periodNative)) "exact collection-period surrogate"
  assertTrue (!succeeds (validateDefinitionPair periodReference {periodNative with
    value := mutateConstant periodNative.value `CollectionMembership `UnionMembership}))
    "collection period changed to union period rejected"
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with levelParams := [`u]}))
    "model extra universe rejected"
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with safety := .unsafe}))
    "unsafe model rejected"
  assertTrue (!succeeds (validateDefinitionPair refDefinition {native with value := .bvar 0}))
    "open model body rejected"
  let target := `ClarkSeed.exists_physical_aperiodic_monotile_of_ge_five
  assertTrue (succeeds (validateTheorem target expected (theoremValue expected))) "exact quantified endpoint surrogate"
  let .forallE d domain tail bi := expected | throwError "fixture missing dimension"
  assertTrue (!succeeds (validateTheorem target expected (theoremValue tail))) "dimension quantifier removed rejected"
  assertTrue (!succeeds (validateTheorem target expected (theoremValue (.forallE `other domain tail bi))))
    "dimension binder renamed rejected"
  assertTrue (!succeeds (validateTheorem target expected (theoremValue (.forallE d domain tail .implicit))))
    "dimension binder visibility changed rejected"
  let changedDimension := expected.replace fun e => if e.equal (mkNatLit 5) then some (mkNatLit 4) else none
  assertTrue (!succeeds (validateTheorem target expected (theoremValue changedDimension)))
    "dimension lower bound changed rejected"
  let extraHypothesis := mkForall `C .default (mkConst `True []) expected
  assertTrue (!succeeds (validateTheorem target expected (theoremValue extraHypothesis)))
    "extra hypothesis rejected"
  assertTrue (!succeeds (validateTheorem target expected (.axiomInfo {
    name := target, levelParams := [], type := expected, isUnsafe := false })))
    "axiom substituted for theorem rejected"
  assertTrue (succeeds (validateAxioms #[`propext, `Classical.choice, `Quot.sound]))
    "three standard axioms accepted"
  assertTrue (!succeeds (validateAxioms #[`sorryAx])) "sorryAx rejected"
  assertTrue (!succeeds (validateAxioms #[`PhysicalAssumption])) "extra axiom rejected"
  assertTrue (modelMap.size == 7 && targets.size == 2) "fixed seven model names and two endpoints"
  liftIO <| IO.println "HIGHER_INSPECTOR_CORE_CONTROL_PASSED"
end HigherInspectorControl
