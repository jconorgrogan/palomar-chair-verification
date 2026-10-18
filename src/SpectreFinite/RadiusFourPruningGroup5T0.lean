module

public import SpectreFinite.RadiusFourPruningBlock5T0C0
public import SpectreFinite.RadiusFourPruningBlock5T0C1
public import SpectreFinite.RadiusFourPruningBlock5T0C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_0 : List (Verdict 6) := [rows0_5_0_0, rows0_5_0_1, rows0_5_0_2].flatten
theorem check0_5_0 : checkRows direction samples0 trees0 rows0_5_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_5_0_0, check0_5_0_1, check0_5_0_2, Bool.true_and]
theorem initial5_0 : (RadiusFour.familyForKind 5).map (rotatePatch 0 (hexRegion 4)) = rows0_5_0.map Verdict.patch := by
  symm
  simp only [rows0_5_0, List.map_flatten, List.map_cons, List.map_nil, ← initial5_0_0, ← initial5_0_1, ← initial5_0_2]
  change ([source5_0, source5_1, source5_2].map (List.map (rotatePatch 0 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source5_split]

end SpectreFinite.HexSearch.RadiusFourPruning
