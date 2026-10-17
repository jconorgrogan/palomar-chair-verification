/- SPDX-License-Identifier: Apache-2.0
CORE-ONLY SYNTHETIC FIXTURE. This model deliberately differs from the research
model. Its objects must remain physically isolated from every research root.
-/
module
public import Init
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
end RadiusFive
end SpectreFinite.HexSearch
