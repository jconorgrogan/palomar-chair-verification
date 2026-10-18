module

public import SpectreFinite.RadiusFiveRoot0Cover
public import SpectreFinite.RadiusFourPruningCertified

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem extract_mem_root0Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (0,0)) :
    extract f center (hexRegion 5) ∈ root0Family := by
  have h := extract_mem_of_table_cover positions (hexRegion 4)
    RadiusFourPruning.certifiedFamily (0,0) (hexRegion 5) root0Outputs
    root0_table_cover f (RadiusFourPruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root0Family] using h
#print axioms extract_mem_root0Family
end SpectreFinite.HexSearch.RadiusFive
