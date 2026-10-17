/- SPDX-License-Identifier: Apache-2.0
CORE-ONLY SERIALIZED TARGET FIXTURE. The two declaration lines below are exact
copies from the original target, but their separately compiled dependencies
are synthetic. This file is NOT the original research source or its provenance.
No other declarations, meta commands, private-proof imports or code generators.
-/
module
public import SpectreFinite.RadiusFivePruningRounds
public import SpectreFinite.RadiusFiveCertified
@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
theorem certifiedFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) certifiedFamily := rounds_occurrenceComplete f (RadiusFive.allTurnFamily_occurrenceComplete f hf)
theorem extract_mem_certifiedFamily (f : Position → State) (hf : GloballyLegal f) (center : Position) : extract f center (hexRegion 5) ∈ certifiedFamily := certifiedFamily_occurrenceComplete f hf center
end SpectreFinite.HexSearch.RadiusFivePruning
