module

public import SpectreFinite.RadiusFourPruningBlock6T1C0
public import SpectreFinite.RadiusFourPruningBlock6T1C1
public import SpectreFinite.RadiusFourPruningBlock6T1C2
public import SpectreFinite.RadiusFourPruningBlock6T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_1 : List (Verdict 6) := [rows0_6_1_0, rows0_6_1_1, rows0_6_1_2, rows0_6_1_3].flatten
theorem check0_6_1 : checkRows direction samples0 trees0 rows0_6_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_6_1_0, check0_6_1_1, check0_6_1_2, check0_6_1_3, Bool.true_and]
theorem initial6_1 : (RadiusFour.familyForKind 6).map (rotatePatch 1 (hexRegion 4)) = rows0_6_1.map Verdict.patch := by
  symm
  simp only [rows0_6_1, List.map_flatten, List.map_cons, List.map_nil, ← initial6_1_0, ← initial6_1_1, ← initial6_1_2, ← initial6_1_3]
  change ([source6_0, source6_1, source6_2, source6_3].map (List.map (rotatePatch 1 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source6_split]

end SpectreFinite.HexSearch.RadiusFourPruning
