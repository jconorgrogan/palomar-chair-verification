module

public import SpectreFinite.RadiusThreeRoot5Cover
public import SpectreFinite.RadiusTwoPruningCertified

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem extract_mem_root5Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (5,0)) :
    extract f center (hexRegion 3) ∈ root5Family := by
  have h := extract_mem_of_table_cover positions (hexRegion 2)
    RadiusTwoPruning.certifiedFamily (5,0) (hexRegion 3) root5Outputs
    root5_table_cover f (RadiusTwoPruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root5Family] using h
#print axioms extract_mem_root5Family
end SpectreFinite.HexSearch.RadiusThree
