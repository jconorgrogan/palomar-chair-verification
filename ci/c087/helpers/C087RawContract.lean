/- SPDX-License-Identifier: Apache-2.0
LOCAL SOURCE-ONLY DRAFT. No compilation or execution is claimed.
Official core imports only. Project names below occur only as raw Expr data.
Exact statements and direct proof applications are independently transcribed
from the pinned RadiusFivePruningCertified source. No normalization, alpha
renaming, unfolding, metadata removal, or candidate-derived expectations occur.
The external gate must freshly compile/check the actual project module and
pin its dependency closure; this data audit does not replace a kernel check.
-/
module
public import Lean.Environment
public import Lean.Data.Json
@[expose] public section
open Lean
namespace C087RawAudit

def targetModule : Name := `SpectreFinite.RadiusFivePruningCertified

def completeName : Name :=
  `SpectreFinite.HexSearch.RadiusFivePruning.certifiedFamily_occurrenceComplete

def extractName : Name :=
  `SpectreFinite.HexSearch.RadiusFivePruning.extract_mem_certifiedFamily

def targets : Array Name := #[completeName, extractName]

def permittedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def position : Expr := mkConst `SpectreFinite.HexSearch.Position []
def state : Expr := mkConst `SpectreFinite.HexSearch.State []
def patch : Expr := mkConst `SpectreFinite.HexSearch.Patch []

/-- Exact Lean.Elab.Term.elabArrow name in the pinned native Binders.lean. -/
def arrowBinder : Name := addMacroScope `_internal `a reservedMacroScope

def fieldType : Expr := mkForall arrowBinder .default position state

def legal (f : Expr) : Expr :=
  mkApp (mkConst `SpectreFinite.HexSearch.GloballyLegal []) f

/-- Preserve frontend OfNat encoding, not just raw literal 5. -/
def radiusFive : Expr := mkApp3 (mkConst `OfNat.ofNat [.zero])
  (mkConst `Nat []) (mkRawNatLit 5)
  (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 5))

def region : Expr := mkApp (mkConst `SpectreFinite.HexSearch.hexRegion []) radiusFive

def family : Expr := mkConst `SpectreFinite.HexSearch.RadiusFivePruning.certifiedFamily []

def occurrence (f : Expr) : Expr :=
  mkApp3 (mkConst `SpectreFinite.HexSearch.OccurrenceComplete []) f region family

/-- Membership.mem has container before element, with the explicit inferred
Patch and List Patch types and List.instMembership.{0} Patch dictionary. -/
def membership (f center : Expr) : Expr :=
  mkApp5 (mkConst `Membership.mem [.zero, .zero]) patch
    (mkApp (mkConst `List [.zero]) patch)
    (mkApp (mkConst `List.instMembership [.zero]) patch)
    family (mkApp3 (mkConst `SpectreFinite.HexSearch.extract []) f center region)

def completeType : Expr :=
  mkForall `f .default fieldType
    (mkForall `hf .default (legal (.bvar 0)) (occurrence (.bvar 1)))

def extractType : Expr :=
  mkForall `f .default fieldType
    (mkForall `hf .default (legal (.bvar 0))
      (mkForall `center .default position (membership (.bvar 2) (.bvar 0))))

/-- Exact source term: fun f hf => rounds_occurrenceComplete f
    (RadiusFive.allTurnFamily_occurrenceComplete f hf). -/
def completeProof : Expr :=
  mkLambda `f .default fieldType
    (mkLambda `hf .default (legal (.bvar 0))
      (mkApp2 (mkConst `SpectreFinite.HexSearch.RadiusFivePruning.rounds_occurrenceComplete [])
        (.bvar 1)
        (mkApp2 (mkConst `SpectreFinite.HexSearch.RadiusFive.allTurnFamily_occurrenceComplete [])
          (.bvar 1) (.bvar 0))))

/-- Exact source term: fun f hf center =>
    certifiedFamily_occurrenceComplete f hf center. -/
def extractProof : Expr :=
  mkLambda `f .default fieldType
    (mkLambda `hf .default (legal (.bvar 0))
      (mkLambda `center .default position
        (mkApp3 (mkConst completeName []) (.bvar 2) (.bvar 1) (.bvar 0))))

def closed (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && !e.hasLevelParam

def require (ok : Bool) (message : String) : Except String Unit :=
  if ok then pure () else throw message

def expected (name : Name) : Except String (Expr × Expr) := do
  if name == completeName then return (completeType, completeProof)
  if name == extractName then return (extractType, extractProof)
  throw s!"UNEXPECTED_TARGET: {name}"

def validateTheorem (name : Name) (ci : ConstantInfo) : Except String TheoremVal := do
  let .thmInfo v := ci | throw s!"NOT_A_THEOREM: {name}"
  require (v.name == name) s!"DECLARATION_NAME_MISMATCH: {name}"
  require v.levelParams.isEmpty s!"NONEMPTY_UNIVERSE_PARAMETERS: {name}"
  let (type, proof) ← expected name
  require (closed type && closed proof) s!"OPEN_AUDITOR_EXPECTATION: {name}"
  require (closed v.type && closed v.value) s!"OPEN_TARGET_TYPE_OR_PROOF: {name}"
  require (v.type.equal type)
    s!"EXACT_RAW_TYPE_MISMATCH: {name}\nEXPECTED: {reprStr type}\nACTUAL: {reprStr v.type}"
  require (v.value.equal proof)
    s!"EXACT_RAW_PROOF_MISMATCH: {name}\nEXPECTED: {reprStr proof}\nACTUAL: {reprStr v.value}"
  return v

def validateOwnedNames (actual : Array Name) : Except String Unit :=
  require (actual.size == targets.size && actual.qsort Name.lt == targets.qsort Name.lt)
    s!"EXACT_MODULE_OWNED_SET_MISMATCH: {actual}"

/-- Exactly two theorem declarations in both serialized module payload and
ownership map. Even otherwise harmless generated extras fail pending review. -/
def checkModuleOwned (env : Environment) : Except String Unit := do
  let some idx := env.header.moduleNames.findIdx? (· == targetModule)
    | throw "TARGET_MODULE_MISSING"
  let some data := env.header.moduleData[idx]? | throw "TARGET_MODULE_PAYLOAD_MISSING"
  require (data.constNames.size == data.constants.size) "MALFORMED_MODULE_PAYLOAD"
  validateOwnedNames data.constNames
  for n in data.constNames, ci in data.constants do
    require (n == ci.name) s!"PAYLOAD_NAME_MISMATCH: {n}"
    let _ ← validateTheorem n ci
    let some owner := env.getModuleIdxFor? n | throw s!"MODULE_OWNER_MISSING: {n}"
    require (owner.toNat == idx) s!"WRONG_MODULE_OWNER: {n}"
    let some raw := env.checked.get.find? n | throw s!"CHECKED_CONSTANT_MISSING: {n}"
    let _ ← validateTheorem n raw
  let owned := env.const2ModIdx.toArray.filterMap fun (n, owner) =>
    if owner.toNat == idx then some n else none
  validateOwnedNames owned

def validateAxioms (axioms : Array Name) : Except String Unit := do
  for n in axioms do
    require (permittedAxioms.contains n) s!"NONSTANDARD_TRANSITIVE_AXIOM: {n}"

structure WalkResult where
  axioms : Array Name
  visited : Nat
  deriving Inhabited

/-- Complete raw closure, with no extension-based cache. Every type, available
value (including opaque values), mutual-inductive member, constructor, recursor
family/constructor and rule RHS is followed. The explicit lookup makes pure
negative controls possible without admitting synthetic constants to a kernel.
A resource cap is a failure, never a truncated acceptance. -/
def walkAxioms (lookup : Name → Option ConstantInfo) (roots : Array Name)
    (maxVisited : Nat := 1000000) : Except String WalkResult := do
  let mut pending := roots
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Array Name := #[]
  let mut visited := 0
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    visited := visited + 1
    require (visited ≤ maxVisited) "RAW_DEPENDENCY_GRAPH_CAP_EXCEEDED"
    let some ci := lookup n | throw s!"MISSING_TRANSITIVE_DEPENDENCY: {n}"
    require (ci.name == n) s!"TRANSITIVE_LOOKUP_NAME_MISMATCH: {n}"
    require (!ci.isUnsafe && !ci.isPartial) s!"UNSAFE_OR_PARTIAL_DEPENDENCY: {n}"
    pending := pending ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
    match ci with
    | .axiomInfo _ =>
      validateAxioms #[n]
      axioms := axioms.push n
    | .inductInfo v => pending := pending ++ v.all.toArray ++ v.ctors.toArray
    | .ctorInfo v => pending := pending.push v.induct
    | .recInfo v =>
      pending := pending ++ v.all.toArray
      for rule in v.rules do
        pending := pending.push rule.ctor ++ rule.rhs.getUsedConstants
    | _ => pure ()
  return { axioms := axioms.qsort Name.lt, visited := visited }

def audit (env : Environment) : Except String WalkResult := do
  require (env.header.trustLevel == 0) "NONZERO_IMPORT_TRUST_LEVEL"
  checkModuleOwned env
  walkAxioms (fun n => env.checked.get.find? n) targets

end C087RawAudit
