/- SPDX-License-Identifier: Apache-2.0
LOCAL SOURCE-ONLY DRAFT. Pure data controls, never research declarations.
Synthetic ConstantInfo values are not admitted to any kernel environment.
-/
module
import Lean
import C087RawContract
meta import C087RawContract
meta import Lean.Elab.Command
@[expose] public section
open Lean Elab Command C087RawAudit
namespace C087NegativeControls

def succeeds {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

def check (value : Bool) (label : String) : CommandElabM Unit := do
  unless value do throwError "CONTROL_FAILED: {label}"
  liftIO <| IO.println s!"PASS {label}"

def fixture (name : Name) (type value : Expr) : TheoremVal :=
  { name := name, levelParams := [], type := type, value := value }

def replaceConst (e : Expr) (before after : Name) : Expr :=
  e.replace fun part => match part with
    | .const n levels => if n == before then some (.const after levels) else none
    | _ => none

def syntheticAxiom (name : Name) : ConstantInfo := .axiomInfo {
  name := name, levelParams := [], type := mkSort .zero, isUnsafe := false }

def syntheticDefinition (name : Name) (value : Expr) : ConstantInfo := .defnInfo {
  name := name, levelParams := [], type := mkSort .zero, value := value,
  hints := .abbrev, safety := .safe }

def lookup (data : Array ConstantInfo) (name : Name) : Option ConstantInfo :=
  data.find? (fun ci => ci.name == name)

run_cmd do
  for name in targets do
    let .ok (type, proof) := expected name | throwError "Missing fixture expectation"
    let good := fixture name type proof
    check (succeeds (validateTheorem name (.thmInfo good))) "exact synthetic raw pair accepted"
    check (!succeeds (validateTheorem name (.thmInfo { good with levelParams := [`u] })))
      "nonempty declaration universes rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with name := `Other })))
      "wrong declaration name rejected"
    check (!succeeds (validateTheorem name (syntheticAxiom name))) "axiom endpoint rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with value := .bvar 0 })))
      "open proof rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with type := .sort (.param `u) })))
      "open type universe rejected"
    let .forallE f domain body bi := type | throwError "Missing f binder"
    check (!succeeds (validateTheorem name (.thmInfo { good with
      type := .forallE `renamed domain body bi }))) "alpha-renamed binder rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with
      type := .forallE f domain body .implicit }))) "implicit f binder rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with
      type := .forallE f (mkForall .anonymous .default position state) body bi })))
      "anonymous arrow binder rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with
      type := type.replace (fun e => if e.equal radiusFive then some (mkNatLit 4) else none) })))
      "wrong radius rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with
      type := type.replace (fun e => if e.equal radiusFive then some (mkRawNatLit 5) else none) })))
      "raw-literal replacement rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with
      type := replaceConst type `SpectreFinite.HexSearch.RadiusFivePruning.certifiedFamily `OtherFamily })))
      "changed certified family rejected"
    check (!succeeds (validateTheorem name (.thmInfo { good with value := mkConst `True.intro [] })))
      "unrelated closed proof rejected"
  let good := fixture completeName completeType completeProof
  check (!succeeds (validateTheorem completeName (.thmInfo { good with
    value := replaceConst completeProof
      `SpectreFinite.HexSearch.RadiusFive.allTurnFamily_occurrenceComplete `OtherPremise })))
    "changed source proof dependency rejected"
  let extractGood := fixture extractName extractType extractProof
  check (!succeeds (validateTheorem extractName (.thmInfo { extractGood with
    type := replaceConst extractType `List.instMembership `OtherMembership })))
    "changed membership dictionary rejected"
  check (succeeds (validateOwnedNames targets)) "exact owned-name set accepted"
  check (!succeeds (validateOwnedNames #[completeName])) "missing module theorem rejected"
  check (!succeeds (validateOwnedNames #[completeName, completeName])) "duplicate owner rejected"
  check (!succeeds (validateOwnedNames (targets.push `GeneratedExtra))) "extra declaration rejected"
  check (succeeds (validateAxioms #[])) "empty axiom set accepted"
  check (succeeds (validateAxioms permittedAxioms)) "three standard axiom names accepted"
  check (!succeeds (validateAxioms #[`sorryAx])) "sorryAx rejected"
  check (!succeeds (validateAxioms #[`Lean.ofReduceBool])) "native-reduction axiom rejected"
  let evil := syntheticAxiom `CustomAxiom
  let root := syntheticDefinition `Root (mkConst `CustomAxiom [])
  check (!succeeds (walkAxioms (lookup #[root, evil]) #[`Root])) "hidden value axiom rejected"
  check (!succeeds (walkAxioms (lookup #[root]) #[`Root])) "missing dependency rejected"
  check (!succeeds (walkAxioms (lookup #[]) #[`Root])) "missing root rejected"
  let standard := syntheticAxiom `propext
  check (succeeds (walkAxioms (lookup #[standard]) #[`propext])) "standard axiom walk accepted"
  check (!succeeds (walkAxioms (lookup #[standard]) #[`propext] 0)) "graph-cap failure rejected"
  let partialRoot : ConstantInfo := .defnInfo {
    name := `Root, levelParams := [], type := mkSort .zero, value := mkSort .zero,
    hints := .abbrev, safety := .partial }
  check (!succeeds (walkAxioms (lookup #[partialRoot]) #[`Root])) "partial dependency rejected"
  let opaqueRoot : ConstantInfo := .opaqueInfo {
    name := `Root, levelParams := [], type := mkSort .zero,
    value := mkConst `CustomAxiom [], isUnsafe := false, all := [`Root] }
  check (!succeeds (walkAxioms (lookup #[opaqueRoot, evil]) #[`Root])) "opaque value axiom rejected"
  let recRoot : ConstantInfo := .recInfo { (default : RecursorVal) with
    name := `Root, type := mkSort .zero, all := [], isUnsafe := false,
    rules := [{ ctor := `Ctor, nfields := 0, rhs := mkConst `CustomAxiom [] }] }
  let ctor : ConstantInfo := .ctorInfo { (default : ConstructorVal) with
    name := `Ctor, type := mkSort .zero, induct := `Ind, isUnsafe := false }
  let ind : ConstantInfo := .inductInfo { (default : InductiveVal) with
    name := `Ind, type := mkSort .zero, all := [`Ind], ctors := [`Ctor], isUnsafe := false }
  check (!succeeds (walkAxioms (lookup #[recRoot, ctor, ind, evil]) #[`Root]))
    "recursor rule RHS axiom rejected"
  let poisonedCtor : ConstantInfo := .ctorInfo { (default : ConstructorVal) with
    name := `Ctor, type := mkConst `CustomAxiom [], induct := `Ind, isUnsafe := false }
  check (!succeeds (walkAxioms (lookup #[ind, poisonedCtor, evil]) #[`Ind]))
    "inductive constructor type axiom rejected"
  liftIO <| IO.println "C087_NEGATIVE_CONTROLS_PASSED"
end C087NegativeControls
