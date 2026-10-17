/- SPDX-License-Identifier: Apache-2.0
CORE-ONLY SYNTHETIC DEPENDENCY. Never research proof provenance.
-/
module
public import C087SerializedFixture.Model
@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
theorem allTurnFamily_occurrenceComplete (f : Position → State)
    (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) allTurnFamily := hf
end SpectreFinite.HexSearch.RadiusFive
