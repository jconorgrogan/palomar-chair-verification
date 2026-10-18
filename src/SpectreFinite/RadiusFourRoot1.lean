module

public import SpectreFinite.RadiusFourRoot1Cover
public import SpectreFinite.RadiusThreePruningCertified

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem extract_mem_root1Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (1,0)) :
    extract f center (hexRegion 4) ∈ root1Family := by
  have h := extract_mem_of_table_cover positions (hexRegion 3)
    RadiusThreePruning.certifiedFamily (1,0) (hexRegion 4) root1Outputs
    root1_table_cover f (RadiusThreePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root1Family] using h
#print axioms extract_mem_root1Family
end SpectreFinite.HexSearch.RadiusFour
