module

public import SpectreFinite.RadiusFiveParentBinding
public import SpectreFinite.RadiusFivePruningCertified

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) ParentOwnership.certifiedParentFamily := occurrenceComplete_transfer f (RadiusFivePruning.certifiedFamily_occurrenceComplete f hf)
#print axioms parentFamily_occurrenceComplete

end SpectreFinite.HexSearch.RadiusFiveParentBinding
