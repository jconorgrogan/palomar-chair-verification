module

public import SpectreFinite.RadiusFourPruningBlock1T1C0
public import SpectreFinite.RadiusFourPruningBlock1T1C1
public import SpectreFinite.RadiusFourPruningBlock1T1C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_1 : List (Verdict 6) := [rows0_1_1_0, rows0_1_1_1, rows0_1_1_2].flatten
theorem check0_1_1 : checkRows direction samples0 trees0 rows0_1_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_1_1_0, check0_1_1_1, check0_1_1_2, Bool.true_and]
theorem initial1_1 : (RadiusFour.familyForKind 1).map (rotatePatch 1 (hexRegion 4)) = rows0_1_1.map Verdict.patch := by
  symm
  simp only [rows0_1_1, List.map_flatten, List.map_cons, List.map_nil, ← initial1_1_0, ← initial1_1_1, ← initial1_1_2]
  change ([source1_0, source1_1, source1_2].map (List.map (rotatePatch 1 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source1_split]

end SpectreFinite.HexSearch.RadiusFourPruning
