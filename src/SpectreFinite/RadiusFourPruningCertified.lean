module

public import SpectreFinite.RadiusFourPruningRounds
public import SpectreFinite.RadiusFourCertified

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem certifiedFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 4) certifiedFamily := rounds_occurrenceComplete f (RadiusFour.allTurnFamily_occurrenceComplete f hf)
theorem extract_mem_certifiedFamily (f : Position → State) (hf : GloballyLegal f) (center : Position) : extract f center (hexRegion 4) ∈ certifiedFamily := certifiedFamily_occurrenceComplete f hf center
#print axioms certifiedFamily_occurrenceComplete

end SpectreFinite.HexSearch.RadiusFourPruning
