module

public import SpectreFinite.RadiusFourPruningBlock7T3C0
public import SpectreFinite.RadiusFourPruningBlock7T3C1
public import SpectreFinite.RadiusFourPruningBlock7T3C2
public import SpectreFinite.RadiusFourPruningBlock7T3C3
public import SpectreFinite.RadiusFourPruningBlock7T3C4
public import SpectreFinite.RadiusFourPruningBlock7T3C5
public import SpectreFinite.RadiusFourPruningBlock7T3C6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_3 : List (Verdict 6) := [rows0_7_3_0, rows0_7_3_1, rows0_7_3_2, rows0_7_3_3, rows0_7_3_4, rows0_7_3_5, rows0_7_3_6].flatten
theorem check0_7_3 : checkRows direction samples0 trees0 rows0_7_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_7_3_0, check0_7_3_1, check0_7_3_2, check0_7_3_3, check0_7_3_4, check0_7_3_5, check0_7_3_6, Bool.true_and]
theorem initial7_3 : (RadiusFour.familyForKind 7).map (rotatePatch 3 (hexRegion 4)) = rows0_7_3.map Verdict.patch := by
  symm
  simp only [rows0_7_3, List.map_flatten, List.map_cons, List.map_nil, ← initial7_3_0, ← initial7_3_1, ← initial7_3_2, ← initial7_3_3, ← initial7_3_4, ← initial7_3_5, ← initial7_3_6]
  change ([source7_0, source7_1, source7_2, source7_3, source7_4, source7_5, source7_6].map (List.map (rotatePatch 3 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source7_split]

end SpectreFinite.HexSearch.RadiusFourPruning
