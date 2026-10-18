module

public import SpectreFinite.RadiusThreePruningBlock8T5C0
public import SpectreFinite.RadiusThreePruningBlock8T5C1
public import SpectreFinite.RadiusThreePruningBlock8T5C2
public import SpectreFinite.RadiusThreePruningBlock8T5C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_5 : List (Verdict 6) := [rows0_8_5_0, rows0_8_5_1, rows0_8_5_2, rows0_8_5_3].flatten
theorem check0_8_5 : checkRows direction samples0 trees0 rows0_8_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_8_5_0, check0_8_5_1, check0_8_5_2, check0_8_5_3, Bool.true_and]
def rows1_8_5 : List (Verdict 6) := [rows1_8_5_0, rows1_8_5_1, rows1_8_5_2, rows1_8_5_3].flatten
theorem check1_8_5 : checkRows direction samples1 trees1 rows1_8_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_8_5_0, check1_8_5_1, check1_8_5_2, check1_8_5_3, Bool.true_and]
theorem link1_8_5 : rows1_8_5.map Verdict.patch = rows0_8_5.filterMap Verdict.kept := by
  simp only [rows1_8_5, rows0_8_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_8_5_0, link1_8_5_1, link1_8_5_2, link1_8_5_3]
def rows2_8_5 : List (Verdict 6) := [rows2_8_5_0, rows2_8_5_1, rows2_8_5_2, rows2_8_5_3].flatten
theorem check2_8_5 : checkRows direction samples2 trees2 rows2_8_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_8_5_0, check2_8_5_1, check2_8_5_2, check2_8_5_3, Bool.true_and]
theorem link2_8_5 : rows2_8_5.map Verdict.patch = rows1_8_5.filterMap Verdict.kept := by
  simp only [rows2_8_5, rows1_8_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_8_5_0, link2_8_5_1, link2_8_5_2, link2_8_5_3]
theorem initial8_5 : (RadiusThree.familyForKind 8).map (rotatePatch 5 (hexRegion 3)) = rows0_8_5.map Verdict.patch := by
  symm
  simp only [rows0_8_5, List.map_flatten, List.map_cons, List.map_nil, ← initial8_5_0, ← initial8_5_1, ← initial8_5_2, ← initial8_5_3]
  change ([source8_0, source8_1, source8_2, source8_3].map (List.map (rotatePatch 5 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source8_split]

end SpectreFinite.HexSearch.RadiusThreePruning
