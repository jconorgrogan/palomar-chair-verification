module

public import SpectreFinite.RadiusFourPruningBlock0T2C0
public import SpectreFinite.RadiusFourPruningBlock0T2C1
public import SpectreFinite.RadiusFourPruningBlock0T2C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_2 : List (Verdict 6) := [rows0_0_2_0, rows0_0_2_1, rows0_0_2_2].flatten
theorem check0_0_2 : checkRows direction samples0 trees0 rows0_0_2 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_0_2_0, check0_0_2_1, check0_0_2_2, Bool.true_and]
theorem initial0_2 : (RadiusFour.familyForKind 0).map (rotatePatch 2 (hexRegion 4)) = rows0_0_2.map Verdict.patch := by
  symm
  simp only [rows0_0_2, List.map_flatten, List.map_cons, List.map_nil, ← initial0_2_0, ← initial0_2_1, ← initial0_2_2]
  change ([source0_0, source0_1, source0_2].map (List.map (rotatePatch 2 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source0_split]

end SpectreFinite.HexSearch.RadiusFourPruning
