/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Adapted used-constant traversal from Lake.Check.Util by Henrik Böving.
Released under Apache 2.0 license. Test-only loading pattern adapted from
Lean checker by Kim Morrison and Sebastian Ullrich (Apache 2.0).
-/
import Lean.Environment
import Lean.Util.FoldConsts

open Lean

/- All comparison identities remain Lean Names. Printed names are explanatory only.
   Regions stay live until this short-lived process exits; freeRegions is not called
   while any cross-context ConstantInfo or Expr reference can remain live. -/
def require (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw <| IO.userError why

def kind : ConstantInfo → String
  | .axiomInfo .. => "axiom"
  | .defnInfo .. => "def"
  | .thmInfo .. => "theorem"
  | .opaqueInfo .. => "opaque"
  | .quotInfo .. => "quot"
  | .inductInfo .. => "inductive"
  | .ctorInfo .. => "constructor"
  | .recInfo .. => "recursor"

def exactInfo (a b : ConstantInfo) : Bool := Id.run do
  -- Derived BEq covers every constructor and every non-Expr field. Its Expr
  -- comparison is alpha equivalence, so strengthen every Expr-bearing field.
  if a != b || !Expr.equal a.type b.type then return false
  match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
  | some x, some y => if !Expr.equal x y then return false
  | none, none => pure ()
  | _, _ => return false
  match a, b with
  | .recInfo x, .recInfo y =>
    if x.rules.length != y.rules.length then return false
    for xr in x.rules, yr in y.rules do
      if !Expr.equal xr.rhs yr.rhs then return false
  | _, _ => pure ()
  return true

-- Diagnostics identify fields only; they do not pretend to preserve entire differing expressions.
def differingFields (a b : ConstantInfo) : Array String := Id.run do
  let mut fields := #[]
  if a.name != b.name then fields := fields.push "name"
  if kind a != kind b then fields := fields.push "kind"
  if a.levelParams != b.levelParams then fields := fields.push "levelParams"
  if !Expr.equal a.type b.type then fields := fields.push "type"
  match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
  | some x, some y => if !Expr.equal x y then fields := fields.push "value_or_proof"
  | none, none => pure ()
  | _, _ => fields := fields.push "value_or_proof_availability"
  match a, b with
  | .axiomInfo x, .axiomInfo y =>
    if x.isUnsafe != y.isUnsafe then fields := fields.push "axiom.isUnsafe"
  | .defnInfo x, .defnInfo y =>
    if x.hints != y.hints then fields := fields.push "definition.hints"
    if x.safety != y.safety then fields := fields.push "definition.safety"
    if x.all != y.all then fields := fields.push "definition.all"
  | .thmInfo x, .thmInfo y =>
    if x.all != y.all then fields := fields.push "theorem.all"
  | .opaqueInfo x, .opaqueInfo y =>
    if x.isUnsafe != y.isUnsafe then fields := fields.push "opaque.isUnsafe"
    if x.all != y.all then fields := fields.push "opaque.all"
  | .quotInfo x, .quotInfo y =>
    if x.kind != y.kind then fields := fields.push "quotient.kind"
  | .inductInfo x, .inductInfo y =>
    if x.numParams != y.numParams then fields := fields.push "inductive.numParams"
    if x.numIndices != y.numIndices then fields := fields.push "inductive.numIndices"
    if x.all != y.all then fields := fields.push "inductive.all"
    if x.ctors != y.ctors then fields := fields.push "inductive.ctors"
    if x.numNested != y.numNested then fields := fields.push "inductive.numNested"
    if x.isRec != y.isRec then fields := fields.push "inductive.isRec"
    if x.isUnsafe != y.isUnsafe then fields := fields.push "inductive.isUnsafe"
    if x.isReflexive != y.isReflexive then fields := fields.push "inductive.isReflexive"
  | .ctorInfo x, .ctorInfo y =>
    if x.induct != y.induct then fields := fields.push "constructor.induct"
    if x.cidx != y.cidx then fields := fields.push "constructor.cidx"
    if x.numParams != y.numParams then fields := fields.push "constructor.numParams"
    if x.numFields != y.numFields then fields := fields.push "constructor.numFields"
    if x.isUnsafe != y.isUnsafe then fields := fields.push "constructor.isUnsafe"
  | .recInfo x, .recInfo y =>
    if x.all != y.all then fields := fields.push "recursor.all"
    if x.numParams != y.numParams then fields := fields.push "recursor.numParams"
    if x.numIndices != y.numIndices then fields := fields.push "recursor.numIndices"
    if x.numMotives != y.numMotives then fields := fields.push "recursor.numMotives"
    if x.numMinors != y.numMinors then fields := fields.push "recursor.numMinors"
    if x.k != y.k then fields := fields.push "recursor.k"
    if x.isUnsafe != y.isUnsafe then fields := fields.push "recursor.isUnsafe"
    if x.rules.length != y.rules.length then fields := fields.push "recursor.rules.length"
    let mut index := 0
    for xr in x.rules, yr in y.rules do
      if xr.ctor != yr.ctor then fields := fields.push s!"recursor.rules[{index}].ctor"
      if xr.nfields != yr.nfields then fields := fields.push s!"recursor.rules[{index}].nfields"
      if !Expr.equal xr.rhs yr.rhs then fields := fields.push s!"recursor.rules[{index}].rhs"
      index := index + 1
  | _, _ => pure ()
  return fields

-- This traversal is copied in substance from pinned Lake.Check.Util.
def references (info : ConstantInfo) : Array Name := Id.run do
  let mut out := info.type.getUsedConstants
  if let some v := info.value? (allowOpaque := true) then
    out := out ++ v.getUsedConstants
  match info with
  | .axiomInfo .. | .quotInfo .. | .defnInfo .. | .thmInfo .. | .opaqueInfo .. => pure ()
  | .inductInfo i => out := out ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => out := out.push i.induct
  | .recInfo i =>
    for r in i.rules do out := (out.push r.ctor) ++ r.rhs.getUsedConstants
  return out

partial def usedAxioms (env : Environment) (start : Name) : IO (Array Name) := do
  let mut todo := #[start]
  let mut seen : Std.HashSet Name := {}
  let mut axioms := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      seen := seen.insert n
      let some ci := env.constants.find? n
        | throw <| IO.userError s!"MISSING_REFERENCED_DECLARATION {n}"
      if let .axiomInfo _ := ci then axioms := axioms.push n
      todo := todo ++ references ci
  return axioms.qsort (fun a b => a.quickCmp b == .lt)

def legalAxioms : Array Name := #[`propext, `Quot.sound, `Classical.choice]

def checkAxioms (xs : Array Name) : IO Unit := do
  for n in xs do require (legalAxioms.contains n) s!"UNPERMITTED_AXIOM {n}"

structure Loaded where
  before : Environment
  after : Environment
  introduced : Array (Name × ConstantInfo)
  extras : Array Name

unsafe def load (root runtime : System.FilePath) (moduleName : Name) : IO Loaded := do
  searchPathRef.set [root, runtime / "lib" / "lean"]
  let mFile ← findOLean moduleName
  require (mFile == root / (moduleName.toString.replace "." "/" ++ ".olean")) "WRONG_MODULE_PROVIDER"
  let fnames := #[mFile, OLeanLevel.server.adjustFileName mFile, OLeanLevel.private.adjustFileName mFile]
  for p in fnames do require (← p.pathExists) s!"MISSING_PRIVATE_COMPANION {p}"
  let parts ← readModuleDataParts fnames
  require (parts.size == 3) "MISSING_MODULE_PART"
  let publicData := parts[0]!.1
  let privateData := parts[2]!.1
  require (privateData.constNames.size == privateData.constants.size) "MALFORMED_PRIVATE_INVENTORY"
  let before ← importModules publicData.imports {} (loadExts := false) (level := .private)
  let after ← importModules #[{module := moduleName}] {} (loadExts := false) (level := .private)
  let delta := (after.constants.toList.toArray.filter fun p => !before.constants.contains p.1).qsort
    (fun a b => a.1.quickCmp b.1 == .lt)
  let raw := (privateData.constNames.zip privateData.constants).qsort
    (fun a b => a.1.quickCmp b.1 == .lt)
  require (delta.size == raw.size) "ENVIRONMENT_SUBTRACTION_SIZE"
  for d in delta, r in raw do
    require (d.1 == r.1 && r.1 == r.2.name && exactInfo d.2 r.2) "ENVIRONMENT_SUBTRACTION_MISMATCH"
  for n in privateData.extraConstNames do
    require (after.constants.contains n) s!"UNAVAILABLE_GENERATED_DECLARATION {n}"
  for (n, ci) in before.constants.toList do
    let some ci' := after.constants.find? n | throw <| IO.userError s!"IMPORTED_DECLARATION_LOST {n}"
    require (exactInfo ci ci') s!"IMPORTED_DECLARATION_CHANGED {n}"
  return {before, after, introduced := delta, extras := privateData.extraConstNames}

unsafe def compare (left right runtime : System.FilePath) (moduleName : Name) (emit := true) : IO Unit := do
  let a ← load left runtime moduleName
  let b ← load right runtime moduleName
  require (a.introduced.size == b.introduced.size)
    s!"INTRODUCED_INVENTORY_DIFFERS original_count={a.introduced.size} candidate_count={b.introduced.size} original_first16={a.introduced.toList.take 16 |>.map (fun p => p.1)} candidate_first16={b.introduced.toList.take 16 |>.map (fun p => p.1)}"
  require ((a.extras.qsort (fun a b => a.quickCmp b == .lt)) ==
    (b.extras.qsort (fun a b => a.quickCmp b == .lt))) "GENERATED_IDENTITY_DIFFERS"
  for x in a.introduced, y in b.introduced do
    require (x.1 == y.1) s!"INTRODUCED_INVENTORY_DIFFERS original={x.1} candidate={y.1}"
    require (kind x.2 == kind y.2 && x.2.levelParams == y.2.levelParams && Expr.equal x.2.type y.2.type)
      s!"TYPE_OR_KIND_DIFFERS {x.1} fields={differingFields x.2 y.2}"
    require (exactInfo x.2 y.2) s!"DECLARATION_FIELDS_DIFFER {x.1} fields={differingFields x.2 y.2}"
    let ax ← usedAxioms a.after x.1
    let bx ← usedAxioms b.after y.1
    require (ax == bx) s!"USED_AXIOMS_DIFFER {x.1} original={ax} candidate={bx}"
    checkAxioms ax
    if emit then IO.println s!"DECL\t{x.1}\t{kind x.2}\t{String.intercalate "," (ax.toList.map Name.toString)}"
  if emit then
    for n in a.before.header.moduleNames do IO.println s!"LOADED_ORIGINAL\t{n}"
    for n in b.before.header.moduleNames do IO.println s!"LOADED_CANDIDATE\t{n}"
    for n in a.extras do IO.println s!"GENERATED\t{n}"
    IO.println s!"PART32_EXACT_COMPARISON_PASSED\t{a.introduced.size}"

unsafe def coverAxioms (root runtime : System.FilePath) : IO Unit := do
  let moduleName := `SpectreFinite.RadiusFiveRoot7Cover
  let c ← load root runtime moduleName
  for (n, ci) in c.introduced do
    let ax ← usedAxioms c.after n
    checkAxioms ax
    IO.println s!"COVER_DECL\t{n}\t{kind ci}\t{String.intercalate "," (ax.toList.map Name.toString)}"
  require (!c.introduced.isEmpty) "EMPTY_COVER"
  IO.println s!"COVER_AXIOMS_PASSED\t{c.introduced.size}"

unsafe def fixtures (root runtime : System.FilePath) : IO Unit := do
  compare (root / "baseline") (root / "identical") runtime `Fixture false
  for (variant, expected) in [("value", "DECLARATION_FIELDS_DIFFER"), ("type", "TYPE_OR_KIND_DIFFERS"),
      ("inventory", "INTRODUCED_INVENTORY_DIFFERS")] do
    let mut rejected := false
    try compare (root / "baseline") (root / variant) runtime `Fixture false
    catch e =>
      require (((toString e).splitOn expected).length > 1) s!"WRONG_FIXTURE_REJECTION {variant}: {e}"
      rejected := true
    require rejected s!"NEGATIVE_FIXTURE_PASSED {variant}"
  let bad ← load (root / "axiom") runtime `Fixture
  let ax ← usedAxioms bad.after `fixtureTheorem
  require (ax.contains `fixtureAssumption) "AXIOM_FIXTURE_NOT_TRAVERSED"
  let mut rejected := false
  try checkAxioms ax
  catch e =>
    require (((toString e).splitOn "UNPERMITTED_AXIOM").length > 1) "WRONG_AXIOM_REJECTION"
    rejected := true
  require rejected "AXIOM_FIXTURE_PASSED"
  IO.println "SOURCE_FIXTURES_PASSED\t1-positive-4-negative"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["self-test"] =>
    require (!(Expr.equal (mkConst `A) (mkConst `B))) "CHANGED_CONSTANT_REFERENCE_IGNORED"
    require (!(Expr.equal (mkLambda `x .default (mkSort .zero) (mkBVar 0))
      (mkLambda `y .default (mkSort .zero) (mkBVar 0)))) "BINDER_NAME_IGNORED"
    let plain := mkLambda `x .default (mkSort .zero) (mkBVar 0)
    let implicitBinder := mkLambda `x .implicit (mkSort .zero) (mkBVar 0)
    let dv : DefinitionVal := {
      name := `TestDef,
      levelParams := [],
      type := mkSort .zero,
      value := plain,
      hints := .opaque,
      safety := .safe
    }
    let ca : ConstantInfo := .defnInfo dv
    let cb : ConstantInfo := .defnInfo {dv with value := implicitBinder}
    require (ca == cb && !exactInfo ca cb) "BINDER_ANNOTATION_CONTROL_FAILED"
    let rv : RecursorVal := {
      name := `TestRec,
      levelParams := [],
      type := mkSort .zero,
      all := [],
      numParams := 0,
      numIndices := 0,
      numMotives := 0,
      numMinors := 0,
      rules := [{ctor := `TestCtor, nfields := 0, rhs := plain}],
      k := false,
      isUnsafe := false
    }
    let ra : ConstantInfo := .recInfo rv
    let rb : ConstantInfo := .recInfo {rv with rules := [{ctor := `TestCtor, nfields := 0, rhs := implicitBinder}]}
    require (ra == rb && !exactInfo ra rb) "RECURSOR_RHS_CONTROL_FAILED"
    require ((differingFields ca cb).contains "value_or_proof" &&
      (differingFields ra rb).contains "recursor.rules[0].rhs") "FIELD_DIAGNOSTIC_CONTROL_FAILED"
    IO.println "INTERFACE_API_SELF_TEST_PASSED"
  | ["fixtures", root, runtime] => fixtures root runtime
  | ["compare", left, right, runtime] => compare left right runtime `SpectreFinite.RadiusFiveRoot7Part32
  | ["cover", root, runtime] => coverAxioms root runtime
  | _ => throw <| IO.userError "unsupported finite interface-tool mode"
  return 0
