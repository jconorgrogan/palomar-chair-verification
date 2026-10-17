/- SPDX-License-Identifier: Apache-2.0
Core-only CLI option control. Compile without any Elab.async override.
The command reads the actual frontend options, not a fresh Options value.
Its success marker is required in addition to exit 0 and a fresh leanchecker pass.
No target-module proof or final geometry theorem is asserted here. -/
module
public import Lean

open Lean

run_cmd do
  let actual := Lean.Elab.async.get (← getOptions)
  unless actual == true do
    throwError "ASYNC_OPTION_CONTROL_DEFAULT_MISMATCH: expected true, got {actual}"
  Lean.Elab.Command.liftIO (IO.println "ASYNC_OPTION_CONTROL_DEFAULT_TRUE")

namespace AsyncDiagnostic.DefaultControl
public theorem optionControlKernelWitness : True := True.intro
end AsyncDiagnostic.DefaultControl
