/- SPDX-License-Identifier: Apache-2.0
Core-only controls for the inspector's exact expression/name/axiom gates.
Synthetic Expr records are data, never admitted as declarations. This is not a
physical model elaboration, kernel check, or proof of either target theorem.
-/
module
import Lean.Elab.BuiltinEvalCommand
import AuditUniformPhysicalEndpoints
meta import AuditUniformPhysicalEndpoints
meta import Lean.Elab.Command
open Lean Elab Command
open UniformPhysicalAudit

namespace UniformInspectorControl

def refPoint (d : Expr) : Expr := mkApp (mkConst `UniformPhysicalReference.Point []) d
def setOf (type : Expr) : Expr := mkApp (mkConst `Set [.zero]) type

def hasTilingValue : Expr :=
  mkLambda `d .implicit (mkConst `Nat [])
    (mkLambda `T .default (setOf (refPoint (.bvar 0)))
      (mkApp2 (mkConst `Exists [.succ .zero]) (setOf (setOf (refPoint (.bvar 1))))
        (mkLambda `tiles .default (setOf (setOf (refPoint (.bvar 1))))
          (mkApp3 (mkConst `UniformPhysicalReference.IsTiling []) (.bvar 2) (.bvar 1) (.bvar 0)))))

def refDefinition : DefinitionVal := {
  name := `UniformPhysicalReference.HasTiling, levelParams := [],
  type := mkForall `d .implicit (mkConst `Nat [])
    (mkForall `T .default (setOf (refPoint (.bvar 0))) (mkSort .zero)),
  value := hasTilingValue, hints := .abbrev, safety := .safe }

def mutateConstant (e : Expr) (before after : Name) : Expr :=
  e.replace fun part => match part with
    | .const n us => if n == before then some (.const after us) else none
    | _ => none

def expected : Expr :=
  mkForall `d .default (mkConst `Nat [])
    (mkForall `hd .default (mkApp2 (mkConst `Nat.le []) (mkNatLit 2) (.bvar 0))
      (mkApp2 (mkConst `Exists [.succ .zero])
        (setOf (mkApp (mkConst `SparseMonotiles.Point []) (.bvar 1)))
        (mkLambda `T .default (setOf (mkApp (mkConst `SparseMonotiles.Point []) (.bvar 1)))
          (mkApp2 (mkConst `SparseMonotiles.IsAperiodicMonotile []) (.bvar 2) (.bvar 0)))))

def theoremValue (type : Expr) : ConstantInfo := .thmInfo {
  name := `NativeFinalAssembly.exists_physical_aperiodic_monotile_in_every_dimension_ge_two,
  levelParams := [], type := type, value := mkConst `True.intro [] }

def assertTrue (condition : Bool) (label : String) : CommandElabM Unit := do
  unless condition do throwError "Control failed: {label}"
  liftIO <| IO.println s!"PASS {label}"

def succeeds {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

run_cmd do
  let .ok mappedType := mappedReference false refDefinition.type | throwError "reference type mapping failed"
  let .ok mappedValue := mappedReference false refDefinition.value | throwError "reference value mapping failed"
  let native := { refDefinition with
    name := `SparseMonotiles.HasTiling,
    type := mappedType, value := mappedValue }
  assertTrue (succeeds (validateDefinitionPair false refDefinition native)) "exact mapped model definition"
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with
    name := `SparseMonotiles.RenamedHasTiling})) "renamed native model constant rejected"
  assertTrue (!succeeds (mappedReference false (mkConst `UniformPhysicalReference.Extra [])))
    "extra reference model constant rejected"
  assertTrue (!succeeds (mappedReference false (mkConst `UniformPhysicalReference.HasTiling.Extra [])))
    "nested extra reference model constant rejected"
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with
    value := mutateConstant native.value `SparseMonotiles.IsTiling `SparseMonotiles.OtherIsTiling}))
    "changed HasTiling predicate rejected"
  let wrongUniverse := native.value.replace fun e => match e with
    | .const n _ => if n == `Exists then some (.const n [.zero]) else none
    | _ => none
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with value := wrongUniverse}))
    "changed HasTiling existential universe rejected"
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with value := mkConst `True []}))
    "missing HasTiling existential rejected"
  let periodReference : DefinitionVal := { refDefinition with
    name := `UniformPhysicalReference.IsPeriod,
    value := mkApp2 (mkConst `Iff []) (mkConst `CollectionMembership [])
      (mkApp (mkConst `UniformPhysicalReference.translate []) (mkConst `Tile [])) }
  let .ok periodValue := mappedReference false periodReference.value | throwError "period mapping failed"
  let periodNative := {native with name := `SparseMonotiles.IsPeriod, value := periodValue}
  assertTrue (succeeds (validateDefinitionPair false periodReference periodNative)) "exact collection-period surrogate"
  assertTrue (!succeeds (validateDefinitionPair false periodReference {periodNative with
    value := mutateConstant periodNative.value `CollectionMembership `UnionMembership}))
    "collection period changed to union period rejected"
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with levelParams := [`u]}))
    "model extra universe rejected"
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with safety := .unsafe}))
    "unsafe model rejected"
  assertTrue (!succeeds (validateDefinitionPair false refDefinition {native with value := .bvar 0}))
    "open model body rejected"
  let target := `NativeFinalAssembly.exists_physical_aperiodic_monotile_in_every_dimension_ge_two
  assertTrue (succeeds (validateTheorem target expected (theoremValue expected))) "exact quantified endpoint surrogate"
  let .forallE d domain tail bi := expected | throwError "fixture missing dimension"
  assertTrue (!succeeds (validateTheorem target expected (theoremValue tail))) "dimension quantifier removed rejected"
  assertTrue (!succeeds (validateTheorem target expected (theoremValue (.forallE `other domain tail bi))))
    "dimension binder renamed rejected"
  assertTrue (!succeeds (validateTheorem target expected (theoremValue (.forallE d domain tail .implicit))))
    "dimension binder visibility changed rejected"
  let changedDimension := expected.replace fun e => if e.equal (mkNatLit 2) then some (mkNatLit 3) else none
  assertTrue (!succeeds (validateTheorem target expected (theoremValue changedDimension)))
    "dimension lower bound changed rejected"
  let extraHypothesis := mkForall `C .default (mkConst `True []) expected
  assertTrue (!succeeds (validateTheorem target expected (theoremValue extraHypothesis)))
    "extra hypothesis rejected"
  assertTrue (!succeeds (validateTheorem target expected (.axiomInfo {
    name := target, levelParams := [], type := expected, isUnsafe := false })))
    "axiom substituted for theorem rejected"
  assertTrue (succeeds (validateAxioms false #[`propext, `Classical.choice, `Quot.sound]))
    "three standard axioms accepted"
  assertTrue (!succeeds (validateAxioms false #[`sorryAx])) "sorryAx rejected"
  assertTrue (!succeeds (validateAxioms false #[`PhysicalAssumption])) "extra axiom rejected"
  assertTrue (nativeMap.size == 7 && registrationMap.size == 6 && templates.size == 4) "fixed model maps and four templates"
  let conditionalTemplate := mkLambda `CType .default (mkSort .zero)
    (mkForall `C .default (.bvar 0) expected)
  let .ok conditionalType := instantiateConditional conditionalTemplate | throwError "C substitution failed"
  assertTrue (conditionalType.equal (mkForall `C .default (mkConst parentType []) expected))
    "one capture-safe bound CType substitution"
  let dependentTemplate := mkLambda `CType .default (mkSort .zero)
    (mkForall `C .default (.bvar 0) (mkForall `D .default (.bvar 1) (mkConst `True [])))
  let .ok dependentType := instantiateConditional dependentTemplate | throwError "nested C substitution failed"
  assertTrue (dependentType.equal (mkForall `C .default (mkConst parentType [])
    (mkForall `D .default (mkConst parentType []) (mkConst `True []))))
    "C substitution preserves binding depth"
  assertTrue (!succeeds (instantiateConditional (mkConst `CType []))) "unbound CType axiom rejected"
  assertTrue (!succeeds (instantiateConditional (mkLambda `other .default (mkSort .zero) (mkConst `True []))))
    "renamed CType binder rejected"
  assertTrue (!succeeds (instantiateConditional (mkLambda `CType .implicit (mkSort .zero) (mkConst `True []))))
    "implicit CType binder rejected"
  assertTrue (!succeeds (instantiateConditional (mkLambda `CType .default (mkSort (.succ .zero)) (mkConst `True []))))
    "CType not Prop rejected"
  let condValue : ConstantInfo := .thmInfo { name := conditionalModel, levelParams := [],
    type := conditionalType, value := mkConst `True.intro [] }
  assertTrue (succeeds (validateTheorem conditionalModel conditionalType condValue)) "exact one-C conditional surrogate"
  assertTrue (!succeeds (validateTheorem conditionalModel conditionalType (.thmInfo {
    name := conditionalModel, levelParams := [], type := expected, value := mkConst `True.intro [] })))
    "conditional C binder removed rejected"
  assertTrue (!succeeds (validateTheorem conditionalModel conditionalType (.thmInfo {
    name := conditionalModel, levelParams := [], type := mkForall `C .default (mkConst `True []) expected,
    value := mkConst `True.intro [] }))) "wrong C proposition rejected"
  assertTrue (!succeeds (validateTheorem target expected (.thmInfo { name := target, levelParams := [],
    type := conditionalType, value := mkConst `True.intro [] }))) "C left on closed target rejected"
  let .ok proof := expectedClosedProof expected | throwError "closed application template failed"
  let expectedProof := mkLambda `d .default domain (mkLambda `hd .default
    (mkApp2 (mkConst `Nat.le []) (mkNatLit 2) (.bvar 0))
    (mkApp3 (mkConst conditionalExpanded []) (mkConst parentProof []) (.bvar 1) (.bvar 0)))
  assertTrue (proof.equal expectedProof) "exact closed C theorem application"
  assertTrue (!(proof.equal (mutateConstant proof parentProof `WrongParentProof))) "changed C proof application rejected"
  assertTrue (!(proof.equal (mutateConstant proof conditionalExpanded conditionalModel))) "changed conditional application rejected"
  assertTrue (succeeds (validateAxioms true #[`sorryAx])) "Challenge hole explicitly labeled"
  assertTrue (!succeeds (validateAxioms true #[`sorryAx, `ExtraAssumption])) "Challenge extra axiom rejected"
  assertTrue (!succeeds (validateAxioms true #[`propext])) "Challenge expected hole missing rejected"
  let .ok regType := mappedReference true refDefinition.type | throwError "registration type mapping failed"
  let .ok regValue := mappedReference true refDefinition.value | throwError "registration body mapping failed"
  let reg := {refDefinition with name := `PalomarAllDimensions.HasTiling, type := regType, value := regValue}
  assertTrue (succeeds (validateDefinitionPair true refDefinition reg)) "independent registration model equality"
  assertTrue (!succeeds (mappedReference true (mkConst `UniformPhysicalReference.IsAperiodicMonotile [])))
    "registration extra model constant rejected"
  let parentValue := mkForall `f .default
    (mkForall `x .default (mkConst `SpectreFinite.HexSearch.Position []) (mkConst `SpectreFinite.HexSearch.State []))
    (mkForall `legal .default (mkApp (mkConst `SpectreFinite.HexSearch.GloballyLegal []) (.bvar 0))
      (mkApp3 (mkConst `SpectreFinite.HexSearch.OccurrenceComplete []) (.bvar 1)
        (mkApp (mkConst `SpectreFinite.HexSearch.hexRegion []) (mkNatLit 5))
        (mkConst `SpectreFinite.HexSearch.ParentOwnership.certifiedParentFamily [])))
  assertTrue (expandedParentMatches parentValue) "exact ParentOccurrence expansion"
  let wrongRadius := parentValue.replace fun e => if e.equal (mkNatLit 5) then some (mkNatLit 4) else none
  assertTrue (!expandedParentMatches wrongRadius) "C radius changed rejected"
  assertTrue (!expandedParentMatches (mutateConstant parentValue
    `SpectreFinite.HexSearch.ParentOwnership.certifiedParentFamily `OtherFamily)) "C family changed rejected"
  assertTrue (!expandedParentMatches (mkForall `extra .default (mkConst `True []) parentValue))
    "C extra hypothesis rejected"
  liftIO <| IO.println "UNIFORM_INSPECTOR_CORE_CONTROL_PASSED"
end UniformInspectorControl
