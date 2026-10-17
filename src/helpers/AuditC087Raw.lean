/- SPDX-License-Identifier: Apache-2.0
LOCAL SOURCE-ONLY DRAFT. Compile this helper and C087RawContract using only
pinned official Lean core and this new helper directory. No research import
is present during helper compilation. During the separate authorized runtime
step the exact project .olean closure is loaded as data, at trust0 with no
plugins and extension loading disabled. This is not independent kernel checking.
-/
module
import C087RawContract
meta import C087RawContract
open Lean C087RawAudit

public def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do throw <| IO.userError "No arguments: fixed C087 target only"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := targetModule }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let result ← match audit env with
    | .error message => throw <| IO.userError message
    | .ok value => pure value
  for name in targets do
    let some ci := env.checked.get.find? name | throw <| IO.userError "TARGET_DISAPPEARED"
    let thm ← match validateTheorem name ci with
      | .error message => throw <| IO.userError message
      | .ok value => pure value
    let receipt := Json.mkObj [
      ("status", .str "C087_EXACT_RAW_THEOREM_CONTRACT_PASSED"),
      ("module", .str targetModule.toString), ("theorem", .str name.toString),
      ("universe_parameters", .arr #[]),
      ("exact_raw_type", .bool true), ("exact_raw_source_proof", .bool true),
      ("closed_type_and_proof", .bool true), ("exact_module_owned_set", .bool true),
      ("raw_type", .str (reprStr thm.type)), ("raw_proof", .str (reprStr thm.value)),
      ("all_owned_transitive_axioms", .arr (result.axioms.map fun n => .str n.toString)),
      ("visited_raw_dependencies", toJson result.visited),
      ("independent_kernel_check_claimed", .bool false),
      ("fresh_source_provenance_claimed", .bool false)]
    IO.println receipt.compress
  IO.println "C087_RAW_CONTRACT_PASSED"
  return 0
