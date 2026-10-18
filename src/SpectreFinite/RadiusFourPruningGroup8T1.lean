module

public import SpectreFinite.RadiusFourPruningBlock8T1C0
public import SpectreFinite.RadiusFourPruningBlock8T1C1
public import SpectreFinite.RadiusFourPruningBlock8T1C2
public import SpectreFinite.RadiusFourPruningBlock8T1C3
public import SpectreFinite.RadiusFourPruningBlock8T1C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_1 : List (Verdict 6) := [rows0_8_1_0, rows0_8_1_1, rows0_8_1_2, rows0_8_1_3, rows0_8_1_4].flatten
theorem check0_8_1 : checkRows direction samples0 trees0 rows0_8_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_8_1_0, check0_8_1_1, check0_8_1_2, check0_8_1_3, check0_8_1_4, Bool.true_and]
theorem initial8_1 : (RadiusFour.familyForKind 8).map (rotatePatch 1 (hexRegion 4)) = rows0_8_1.map Verdict.patch := by
  symm
  simp only [rows0_8_1, List.map_flatten, List.map_cons, List.map_nil, ← initial8_1_0, ← initial8_1_1, ← initial8_1_2, ← initial8_1_3, ← initial8_1_4]
  change ([source8_0, source8_1, source8_2, source8_3, source8_4].map (List.map (rotatePatch 1 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source8_split]

end SpectreFinite.HexSearch.RadiusFourPruning
