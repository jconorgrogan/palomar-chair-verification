module

public import SpectreFinite.RadiusFourPruningBlock7T0C0
public import SpectreFinite.RadiusFourPruningBlock7T0C1
public import SpectreFinite.RadiusFourPruningBlock7T0C2
public import SpectreFinite.RadiusFourPruningBlock7T0C3
public import SpectreFinite.RadiusFourPruningBlock7T0C4
public import SpectreFinite.RadiusFourPruningBlock7T0C5
public import SpectreFinite.RadiusFourPruningBlock7T0C6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_0 : List (Verdict 6) := [rows0_7_0_0, rows0_7_0_1, rows0_7_0_2, rows0_7_0_3, rows0_7_0_4, rows0_7_0_5, rows0_7_0_6].flatten
theorem check0_7_0 : checkRows direction samples0 trees0 rows0_7_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_7_0_0, check0_7_0_1, check0_7_0_2, check0_7_0_3, check0_7_0_4, check0_7_0_5, check0_7_0_6, Bool.true_and]
theorem initial7_0 : (RadiusFour.familyForKind 7).map (rotatePatch 0 (hexRegion 4)) = rows0_7_0.map Verdict.patch := by
  symm
  simp only [rows0_7_0, List.map_flatten, List.map_cons, List.map_nil, ← initial7_0_0, ← initial7_0_1, ← initial7_0_2, ← initial7_0_3, ← initial7_0_4, ← initial7_0_5, ← initial7_0_6]
  change ([source7_0, source7_1, source7_2, source7_3, source7_4, source7_5, source7_6].map (List.map (rotatePatch 0 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source7_split]

end SpectreFinite.HexSearch.RadiusFourPruning
