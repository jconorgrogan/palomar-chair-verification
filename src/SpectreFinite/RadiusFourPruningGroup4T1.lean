module

public import SpectreFinite.RadiusFourPruningBlock4T1C0
public import SpectreFinite.RadiusFourPruningBlock4T1C1
public import SpectreFinite.RadiusFourPruningBlock4T1C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_1 : List (Verdict 6) := [rows0_4_1_0, rows0_4_1_1, rows0_4_1_2].flatten
theorem check0_4_1 : checkRows direction samples0 trees0 rows0_4_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_4_1_0, check0_4_1_1, check0_4_1_2, Bool.true_and]
theorem initial4_1 : (RadiusFour.familyForKind 4).map (rotatePatch 1 (hexRegion 4)) = rows0_4_1.map Verdict.patch := by
  symm
  simp only [rows0_4_1, List.map_flatten, List.map_cons, List.map_nil, ← initial4_1_0, ← initial4_1_1, ← initial4_1_2]
  change ([source4_0, source4_1, source4_2].map (List.map (rotatePatch 1 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source4_split]

end SpectreFinite.HexSearch.RadiusFourPruning
