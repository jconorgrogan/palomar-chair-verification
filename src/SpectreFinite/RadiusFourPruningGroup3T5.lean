module

public import SpectreFinite.RadiusFourPruningBlock3T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_5 : List (Verdict 6) := [rows0_3_5_0].flatten
theorem check0_3_5 : checkRows direction samples0 trees0 rows0_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_3_5_0, Bool.true_and]
theorem initial3_5 : (RadiusFour.familyForKind 3).map (rotatePatch 5 (hexRegion 4)) = rows0_3_5.map Verdict.patch := by
  symm
  simp only [rows0_3_5, List.map_flatten, List.map_cons, List.map_nil, ← initial3_5_0]
  change ([source3_0].map (List.map (rotatePatch 5 (hexRegion 4)))).flatten = _
  rw [← List.map_flatten, source3_split]

end SpectreFinite.HexSearch.RadiusFourPruning
