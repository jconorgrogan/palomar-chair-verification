module

public import SpectreFinite.RadiusThreePruningBlock8T3C0
public import SpectreFinite.RadiusThreePruningBlock8T3C1
public import SpectreFinite.RadiusThreePruningBlock8T3C2
public import SpectreFinite.RadiusThreePruningBlock8T3C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_3 : List (Verdict 6) := [rows0_8_3_0, rows0_8_3_1, rows0_8_3_2, rows0_8_3_3].flatten
theorem check0_8_3 : checkRows direction samples0 trees0 rows0_8_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_8_3_0, check0_8_3_1, check0_8_3_2, check0_8_3_3, Bool.true_and]
def rows1_8_3 : List (Verdict 6) := [rows1_8_3_0, rows1_8_3_1, rows1_8_3_2, rows1_8_3_3].flatten
theorem check1_8_3 : checkRows direction samples1 trees1 rows1_8_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_8_3_0, check1_8_3_1, check1_8_3_2, check1_8_3_3, Bool.true_and]
theorem link1_8_3 : rows1_8_3.map Verdict.patch = rows0_8_3.filterMap Verdict.kept := by
  simp only [rows1_8_3, rows0_8_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_8_3_0, link1_8_3_1, link1_8_3_2, link1_8_3_3]
def rows2_8_3 : List (Verdict 6) := [rows2_8_3_0, rows2_8_3_1, rows2_8_3_2, rows2_8_3_3].flatten
theorem check2_8_3 : checkRows direction samples2 trees2 rows2_8_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_8_3_0, check2_8_3_1, check2_8_3_2, check2_8_3_3, Bool.true_and]
theorem link2_8_3 : rows2_8_3.map Verdict.patch = rows1_8_3.filterMap Verdict.kept := by
  simp only [rows2_8_3, rows1_8_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_8_3_0, link2_8_3_1, link2_8_3_2, link2_8_3_3]
theorem initial8_3 : (RadiusThree.familyForKind 8).map (rotatePatch 3 (hexRegion 3)) = rows0_8_3.map Verdict.patch := by
  symm
  simp only [rows0_8_3, List.map_flatten, List.map_cons, List.map_nil, ← initial8_3_0, ← initial8_3_1, ← initial8_3_2, ← initial8_3_3]
  change ([source8_0, source8_1, source8_2, source8_3].map (List.map (rotatePatch 3 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source8_split]

end SpectreFinite.HexSearch.RadiusThreePruning
