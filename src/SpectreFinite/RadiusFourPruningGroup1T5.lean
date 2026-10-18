module

public import SpectreFinite.RadiusFourPruningBlock1T5C0
public import SpectreFinite.RadiusFourPruningBlock1T5C1
public import SpectreFinite.RadiusFourPruningBlock1T5C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_5 : List (Verdict 6) := [rows0_1_5_0, rows0_1_5_1, rows0_1_5_2].flatten
theorem check0_1_5 : checkRows direction samples0 trees0 rows0_1_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_1_5_0, check0_1_5_1, check0_1_5_2, Bool.true_and]
theorem initial1_5 : (RadiusFour.familyForKind 1).map (rotatePatch 5 (hexRegion 4)) = rows0_1_5.map Verdict.patch := by
  symm
  simp only [rows0_1_5, List.map_flatten, List.map_cons, List.map_nil, ← initial1_5_0, ← initial1_5_1, ← initial1_5_2]
  change ([source1_0, source1_1, source1_2].map (List.map (rotatePatch 5 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source1_split]

end SpectreFinite.HexSearch.RadiusFourPruning
