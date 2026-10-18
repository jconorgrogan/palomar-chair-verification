module

public import SpectreFinite.RadiusFourPruningBlock6T2C0
public import SpectreFinite.RadiusFourPruningBlock6T2C1
public import SpectreFinite.RadiusFourPruningBlock6T2C2
public import SpectreFinite.RadiusFourPruningBlock6T2C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_2 : List (Verdict 6) := [rows0_6_2_0, rows0_6_2_1, rows0_6_2_2, rows0_6_2_3].flatten
theorem check0_6_2 : checkRows direction samples0 trees0 rows0_6_2 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_6_2_0, check0_6_2_1, check0_6_2_2, check0_6_2_3, Bool.true_and]
theorem initial6_2 : (RadiusFour.familyForKind 6).map (rotatePatch 2 (hexRegion 4)) = rows0_6_2.map Verdict.patch := by
  symm
  simp only [rows0_6_2, List.map_flatten, List.map_cons, List.map_nil, ← initial6_2_0, ← initial6_2_1, ← initial6_2_2, ← initial6_2_3]
  change ([source6_0, source6_1, source6_2, source6_3].map (List.map (rotatePatch 2 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source6_split]

end SpectreFinite.HexSearch.RadiusFourPruning
