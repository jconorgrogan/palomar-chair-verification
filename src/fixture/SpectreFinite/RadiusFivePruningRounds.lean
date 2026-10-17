/- SPDX-License-Identifier: Apache-2.0
CORE-ONLY SYNTHETIC DEPENDENCY. Never research proof provenance.
-/
module
public import C087SerializedFixture.Model
@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
def certifiedFamily : List Patch := []
theorem rounds_occurrenceComplete (f : Position → State)
    (hf : OccurrenceComplete f (hexRegion 5) RadiusFive.allTurnFamily) :
    OccurrenceComplete f (hexRegion 5) certifiedFamily := hf
end SpectreFinite.HexSearch.RadiusFivePruning
