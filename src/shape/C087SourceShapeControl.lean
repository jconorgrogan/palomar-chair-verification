/- SPDX-License-Identifier: Apache-2.0
LOCAL SOURCE-ONLY DRAFT. CORE-ONLY SYNTHETIC ELABORATION FIXTURE.
These deliberately tiny surrogate definitions reuse project declaration names
only inside this isolated control module. They are NOT research objects or
proof provenance and MUST NOT be staged with the real project object closure.
The exact two endpoint source lines are copied unchanged. Their native-elaborated
raw types/proofs must equal the independent contract before the real audit runs.
-/
module
import Lean
import C087RawContract
meta import C087RawContract
meta import Lean.Elab.Command
@[expose] public section

namespace SpectreFinite.HexSearch
abbrev Position := Nat
abbrev State := Bool
abbrev Patch := List (Position × State)
def hexRegion (n : Nat) : List Position := [n]
def extract (f : Position → State) (center : Position) (domain : List Position) : Patch :=
  domain.map (fun p => (p, f center))
def OccurrenceComplete (f : Position → State) (domain : List Position)
    (family : List Patch) : Prop :=
  ∀ center : Position, extract f center domain ∈ family
def GloballyLegal (f : Position → State) : Prop :=
  OccurrenceComplete f (hexRegion 5) []
namespace RadiusFive
def allTurnFamily : List Patch := []
theorem allTurnFamily_occurrenceComplete (f : Position → State)
    (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) allTurnFamily := hf
end RadiusFive
namespace RadiusFivePruning
def certifiedFamily : List Patch := []
theorem rounds_occurrenceComplete (f : Position → State)
    (hf : OccurrenceComplete f (hexRegion 5) RadiusFive.allTurnFamily) :
    OccurrenceComplete f (hexRegion 5) certifiedFamily := hf
-- The following two source lines are exact copies from the pinned target.
theorem certifiedFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) certifiedFamily := rounds_occurrenceComplete f (RadiusFive.allTurnFamily_occurrenceComplete f hf)
theorem extract_mem_certifiedFamily (f : Position → State) (hf : GloballyLegal f) (center : Position) : extract f center (hexRegion 5) ∈ certifiedFamily := certifiedFamily_occurrenceComplete f hf center
end RadiusFivePruning
end SpectreFinite.HexSearch

open Lean Elab Command C087RawAudit
run_cmd do
  let explicitArrowName := Name.mkNum
    (Name.mkStr (Name.mkStr (Name.mkStr `a "_@") "_internal") "_hyg") 0
  unless arrowBinder == explicitArrowName do throwError "ARROW_HYGIENE_NAME_MISMATCH"
  let env ← getEnv
  for name in targets do
    let some ci := env.find? name | throwError "Missing synthetic source endpoint: {name}"
    match validateTheorem name ci with
    | .error message => throwError "{message}"
    | .ok _ => liftIO <| IO.println s!"C087_SYNTHETIC_SOURCE_SHAPE_PASSED: {name}"
  liftIO <| IO.println "C087_SOURCE_SHAPE_CONTROL_PASSED"
