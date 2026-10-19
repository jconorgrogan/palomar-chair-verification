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

-- ModuleData.extraConstNames are code-generator metadata, not an inventory of
-- ConstantInfo values. Classify from the actual kernel map, never a name suffix.
-- The imported ownership map must account for every entry in this module.
def generatedClass (moduleName n : Name) (knownBefore kernelPresent privatePresent : Bool)
    (owner : Option Name) : IO String := do
  require (!knownBefore) s!"GENERATED_NAME_ALREADY_IMPORTED {n}"
  require (owner == some moduleName) s!"GENERATED_MODULE_OWNERSHIP_DIFFERS {n}"
  require (!kernelPresent || privatePresent) s!"GENERATED_KERNEL_NOT_IN_PRIVATE_INVENTORY {n}"
  return if kernelPresent then "kernel" else "native_only"

def accountGenerated (before after : Environment) (moduleName : Name)
    (privateNames extras : Array Name) : IO (Array (Name × String)) := do
  let mut seen : Std.HashSet Name := {}
  let mut entries := #[]
  for n in extras do
    require (!seen.contains n) s!"DUPLICATE_GENERATED_NAME {n}"
    seen := seen.insert n
    let owner := (after.getModuleIdxFor? n).bind fun idx => after.header.moduleNames[idx.toNat]?
    let classification ← generatedClass moduleName n (before.const2ModIdx.contains n)
      (after.constants.contains n) (privateNames.contains n) owner
    entries := entries.push (n, classification)
  return entries.qsort (fun a b => a.1.quickCmp b.1 == .lt)

def checkKernelInventory (delta raw : Array (Name × ConstantInfo)) : IO Unit := do
  require (delta.size == raw.size) "ENVIRONMENT_SUBTRACTION_SIZE"
  for d in delta, r in raw do
    require (d.1 == r.1 && r.1 == r.2.name && exactInfo d.2 r.2) "ENVIRONMENT_SUBTRACTION_MISMATCH"

structure Loaded where
  before : Environment
  after : Environment
  introduced : Array (Name × ConstantInfo)
  extras : Array (Name × String)

def fixturePhase (traceFixtures : Bool) (stage : String) : IO Unit := do
  if traceFixtures then IO.println s!"FIXTURE_PHASE\t{stage}"

unsafe def load (root runtime : System.FilePath) (moduleName : Name) (traceFixtures : Bool := false) : IO Loaded := do
  fixturePhase traceFixtures "LOAD_BEGIN"
  searchPathRef.set [root, runtime / "lib" / "lean"]
  let mFile ← findOLean moduleName
  require (mFile == root / (moduleName.toString.replace "." "/" ++ ".olean")) "WRONG_MODULE_PROVIDER"
  let fnames := #[mFile, OLeanLevel.server.adjustFileName mFile, OLeanLevel.private.adjustFileName mFile]
  for p in fnames do require (← p.pathExists) s!"MISSING_PRIVATE_COMPANION {p}"
  let parts ← readModuleDataParts fnames
  require (parts.size == 3) "MISSING_MODULE_PART"
  let some publicData := parts[0]?.map (·.1)
    | throw <| IO.userError "MISSING_MODULE_PART"
  let some privateData := parts[2]?.map (·.1)
    | throw <| IO.userError "MISSING_MODULE_PART"
  require (privateData.constNames.size == privateData.constants.size) "MALFORMED_PRIVATE_INVENTORY"
  fixturePhase traceFixtures "PARTS_READY"
  fixturePhase traceFixtures "BEFORE_IMPORT_BEGIN"
  let before ← importModules publicData.imports {} (loadExts := false) (level := .private)
  fixturePhase traceFixtures "BEFORE_IMPORT_DONE"
  fixturePhase traceFixtures "AFTER_IMPORT_BEGIN"
  let after ← importModules #[{module := moduleName}] {} (loadExts := false) (level := .private)
  fixturePhase traceFixtures "AFTER_IMPORT_DONE"
  let delta := (after.constants.toList.toArray.filter fun p => !before.constants.contains p.1).qsort
    (fun a b => a.1.quickCmp b.1 == .lt)
  let raw := (privateData.constNames.zip privateData.constants).qsort
    (fun a b => a.1.quickCmp b.1 == .lt)
  checkKernelInventory delta raw
  let extras ← accountGenerated before after moduleName privateData.constNames privateData.extraConstNames
  for (n, ci) in before.constants.toList do
    let some ci' := after.constants.find? n | throw <| IO.userError s!"IMPORTED_DECLARATION_LOST {n}"
    require (exactInfo ci ci') s!"IMPORTED_DECLARATION_CHANGED {n}"
  fixturePhase traceFixtures "LOAD_CHECKED"
  return {before, after, introduced := delta, extras}

def regularHintHeights (a b : ConstantInfo) : Option (UInt32 × UInt32) :=
  match a, b with
  | .defnInfo x, .defnInfo y =>
    match x.hints, y.hints with
    | .regular oldHeight, .regular newHeight => some (oldHeight, newHeight)
    | _, _ => none
  | _, _ => none

-- Scoped semantic pilot. All source-declared interfaces and axioms are compared.
-- Generated/private inventories are fully loaded, kernel-checked and reported;
-- their identities/bodies intentionally need not be equal after removing a match.
unsafe def comparePublic (left right runtime : System.FilePath) (moduleName fastName : Name)
    (expected : Array (Name × String)) : IO Unit := do
  let a ← load left runtime moduleName
  let b ← load right runtime moduleName
  for (n, expectedKind) in expected do
    let some x := a.after.constants.find? n | throw <| IO.userError s!"MISSING_ORIGINAL_PUBLIC {n}"
    let some y := b.after.constants.find? n | throw <| IO.userError s!"MISSING_CANDIDATE_PUBLIC {n}"
    require ((a.introduced.any fun p => p.1 == n) && (b.introduced.any fun p => p.1 == n)) s!"PUBLIC_NOT_OWNED {n}"
    require (kind x == expectedKind && kind y == expectedKind && x.levelParams == y.levelParams && Expr.equal x.type y.type) s!"PUBLIC_TYPE_OR_KIND_DIFFERS {n}"
    let fields := differingFields x y
    let allowedBodyChange := n == fastName || expectedKind == "theorem"
    let heights := regularHintHeights x y
    let allowedHeightChange := n == fastName && heights.isSome
    require (fields.all fun f => (allowedBodyChange && f == "value_or_proof") ||
      (allowedHeightChange && f == "definition.hints")) s!"UNPERMITTED_PUBLIC_FIELD_CHANGE {n} {fields}"
    if n == fastName then
      let some (oldHeight, newHeight) := heights | throw <| IO.userError "FAST_HINT_KIND_CHANGED"
      IO.println s!"FAST_HEIGHT\t{n}\t{oldHeight.toNat}\t{newHeight.toNat}"
    let ax ← usedAxioms a.after n
    let bx ← usedAxioms b.after n
    require (ax == bx) s!"PUBLIC_AXIOMS_DIFFER {n} {ax} {bx}"
    checkAxioms ax
    IO.println s!"PUBLIC\t{n}\t{expectedKind}\t{String.intercalate "," (ax.toList.map Name.toString)}"
  for (side, ctx) in [("original", a), ("candidate", b)] do
    for (n, ci) in ctx.introduced do
      let owner := (ctx.after.getModuleIdxFor? n).bind fun idx => ctx.after.header.moduleNames[idx.toNat]?
      require (owner == some moduleName) s!"KERNEL_OWNER_DIFFERS {n}"
      let ax ← usedAxioms ctx.after n
      checkAxioms ax
      IO.println s!"KERNEL\t{side}\t{n}\t{kind ci}\t{String.intercalate "," (ax.toList.map Name.toString)}"
    for (n, classification) in ctx.extras do
      IO.println s!"GENERATED\t{side}\t{n}\t{classification}\t{moduleName}"
    for n in ctx.before.header.moduleNames do IO.println s!"LOADED\t{side}\t{n}"
  IO.println s!"PUBLIC_INTERFACE_AXIOMS_PASSED\t{expected.size}"

unsafe def auditBridge (root runtime : System.FilePath) (bridgeName : Name) : IO Unit := do
  let ctx ← load root runtime `PilotBridge
  require (ctx.introduced.any fun p => p.1 == bridgeName && kind p.2 == "theorem") "MISSING_BRIDGE"
  for (n, ci) in ctx.introduced do
    let ax ← usedAxioms ctx.after n
    checkAxioms ax
    IO.println s!"BRIDGE_DECL\t{n}\t{kind ci}\t{String.intercalate "," (ax.toList.map Name.toString)}"
  IO.println s!"BRIDGE_AXIOMS_PASSED\t{bridgeName}"

def smallDeclarations : Array (Name × String) := #[
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Domains4, "def"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Domains4Fast, "def"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Domains4_fast_eq, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk0_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk0_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk0_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk0_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk0_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk0_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk1_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk1_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk1_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk1_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk1_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk1_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk2_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk2_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk2_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk2_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk2_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk2_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk3_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk3_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk3_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk3_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk3_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk3_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk4_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk4_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk4_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk4_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk4_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk4_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk5_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk5_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk5_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk5_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk5_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk5_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk6_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk6_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk6_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk6_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk6_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk6_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk7_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk7_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk7_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk7_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk7_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk7_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk8_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk8_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk8_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk8_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk8_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4Chunk8_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Step4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusThree.root2Node0Leaf_checked, "theorem")
]

def stressDeclarations : Array (Name × String) := #[
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Domains3, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Domains3Fast, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Domains3_fast_eq, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk0_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk0_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk0_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk0_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk0_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk0_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk1_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk1_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk1_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk1_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk1_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk1_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk2_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk2_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk2_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk2_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk2_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk2_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk3_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk3_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk3_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk3_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk3_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk3_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk4_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk4_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk4_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk4_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk4_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk4_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk5_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk5_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk5_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk5_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk5_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk5_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk6_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk6_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk6_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk6_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk6_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk6_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk7_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk7_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk7_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk7_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk7_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk7_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk8_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk8_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk8_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk8_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk8_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Chunk8_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3Narrowing_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Step3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node109Leaf_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains0, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains0Fast, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains0_fast_eq, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains1, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains1Fast, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains1_fast_eq, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk0_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk0_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk0_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk0_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk0_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk0_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk1_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk1_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk1_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk1_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk1_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk1_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk2_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk2_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk2_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk2_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk2_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk2_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk3_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk3_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk3_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk3_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk3_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk3_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk4_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk4_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk4_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk4_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk4_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk4_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk5_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk5_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk5_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk5_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk5_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk5_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk6_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk6_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk6_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk6_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk6_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk6_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk7_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk7_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk7_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk7_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk7_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk7_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk8_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk8_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk8_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk8_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk8_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Chunk8_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1Narrowing_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains2, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains2Fast, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains2_fast_eq, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk0_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk0_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk0_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk0_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk0_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk0_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk1_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk1_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk1_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk1_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk1_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk1_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk2_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk2_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk2_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk2_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk2_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk2_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk3_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk3_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk3_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk3_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk3_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk3_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk4_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk4_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk4_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk4_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk4_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk4_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk5_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk5_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk5_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk5_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk5_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk5_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk6_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk6_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk6_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk6_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk6_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk6_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk7_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk7_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk7_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk7_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk7_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk7_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk8_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk8_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk8_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk8_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk8_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Chunk8_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2Narrowing_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains3, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains3Fast, "def"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Domains3_fast_eq, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk0_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk0_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk0_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk0_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk0_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk0_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk1_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk1_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk1_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk1_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk1_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk1_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk2_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk2_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk2_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk2_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk2_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk2_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk3_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk3_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk3_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk3_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk3_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk3_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk4_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk4_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk4_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk4_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk4_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk4_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk5_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk5_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk5_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk5_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk5_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk5_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk6_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk6_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk6_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk6_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk6_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk6_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk7_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk7_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk7_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk7_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk7_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk7_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk8_0_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk8_1_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk8_2_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk8_3_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk8_4_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Chunk8_5_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3Narrowing_checked, "theorem"),
  (`SpectreFinite.HexSearch.RadiusFive.root7Node110Step3_checked, "theorem")
]

def fixtureDeclarations : Array (Name × String) := #[(`DomainAliasFixture.Domains, "def"), (`DomainAliasFixture.Fast, "def"), (`DomainAliasFixture.fast_eq, "theorem")]

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
    require ((← generatedClass `Fixture `generated false false false (some `Fixture)) == "native_only")
      "NATIVE_CLASSIFICATION_CONTROL_FAILED"
    require ((← generatedClass `Fixture `generated false true true (some `Fixture)) == "kernel")
      "KERNEL_CLASSIFICATION_CONTROL_FAILED"
    for (knownBefore, kernelPresent, privatePresent, owner) in
        [(true, false, false, some `Fixture), (false, false, false, none),
         (false, false, false, some `Other), (false, true, false, some `Fixture)] do
      let mut rejected := false
      try
        let _ ← generatedClass `Fixture `generated knownBefore kernelPresent privatePresent owner
        pure ()
      catch _ => rejected := true
      require rejected "INVALID_GENERATED_METADATA_CONTROL_PASSED"
    let heightA : ConstantInfo := .defnInfo {dv with hints := .regular 1}
    let heightB : ConstantInfo := .defnInfo {dv with hints := .regular 2}
    let opaqueHint : ConstantInfo := .defnInfo {dv with hints := .opaque}
    let abbrevHint : ConstantInfo := .defnInfo {dv with hints := .abbrev}
    require (regularHintHeights heightA heightB == some (1, 2)) "REGULAR_HEIGHT_CONTROL_FAILED"
    require ((regularHintHeights heightA opaqueHint).isNone &&
      (regularHintHeights heightA abbrevHint).isNone) "HINT_KIND_TRANSITION_ACCEPTED"
    IO.println "INTERFACE_API_SELF_TEST_PASSED"
  | ["compare", "small", left, right, runtime] => comparePublic left right runtime `SpectreFinite.RadiusThreeRoot2Part1 `SpectreFinite.HexSearch.RadiusThree.root2Node0Domains4Fast smallDeclarations
  | ["bridge", "small", root, runtime] => auditBridge root runtime `SpectreFinite.HexSearch.RadiusThree.DomainAliasPilot.original_fast_equals_actual
  | ["compare", "stress", left, right, runtime] => comparePublic left right runtime `SpectreFinite.RadiusFiveRoot7Part43 `SpectreFinite.HexSearch.RadiusFive.root7Node110Domains1Fast stressDeclarations
  | ["bridge", "stress", root, runtime] => auditBridge root runtime `SpectreFinite.HexSearch.RadiusFive.DomainAliasPilot.original_fast_equals_actual
  | ["compare", "fixture", left, right, runtime] => comparePublic left right runtime `Fixture `DomainAliasFixture.Fast fixtureDeclarations
  | ["bridge", "fixture", root, runtime] => auditBridge root runtime `DomainAliasFixture.original_fast_equals_actual
  | _ => throw <| IO.userError "unsupported finite pilot-tool mode"
  return 0
