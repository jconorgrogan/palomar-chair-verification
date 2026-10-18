module

public import SpectreFinite.RadiusFivePruningRounds
public import SpectreFinite.RadiusFiveCertified

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem certifiedFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) certifiedFamily := rounds_occurrenceComplete f (RadiusFive.allTurnFamily_occurrenceComplete f hf)
theorem extract_mem_certifiedFamily (f : Position → State) (hf : GloballyLegal f) (center : Position) : extract f center (hexRegion 5) ∈ certifiedFamily := certifiedFamily_occurrenceComplete f hf center
#print axioms certifiedFamily_occurrenceComplete

end SpectreFinite.HexSearch.RadiusFivePruning
