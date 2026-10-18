module

public import SpectreFinite.RadiusThreePruningBlock5T5C0
public import SpectreFinite.RadiusThreePruningBlock5T5C1
public import SpectreFinite.RadiusThreePruningBlock5T5C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_5 : List (Verdict 6) := [rows0_5_5_0, rows0_5_5_1, rows0_5_5_2].flatten
theorem check0_5_5 : checkRows direction samples0 trees0 rows0_5_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_5_5_0, check0_5_5_1, check0_5_5_2, Bool.true_and]
def rows1_5_5 : List (Verdict 6) := [rows1_5_5_0, rows1_5_5_1, rows1_5_5_2].flatten
theorem check1_5_5 : checkRows direction samples1 trees1 rows1_5_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_5_5_0, check1_5_5_1, check1_5_5_2, Bool.true_and]
theorem link1_5_5 : rows1_5_5.map Verdict.patch = rows0_5_5.filterMap Verdict.kept := by
  simp only [rows1_5_5, rows0_5_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_5_5_0, link1_5_5_1, link1_5_5_2]
def rows2_5_5 : List (Verdict 6) := [rows2_5_5_0, rows2_5_5_1, rows2_5_5_2].flatten
theorem check2_5_5 : checkRows direction samples2 trees2 rows2_5_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_5_5_0, check2_5_5_1, check2_5_5_2, Bool.true_and]
theorem link2_5_5 : rows2_5_5.map Verdict.patch = rows1_5_5.filterMap Verdict.kept := by
  simp only [rows2_5_5, rows1_5_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_5_5_0, link2_5_5_1, link2_5_5_2]
theorem initial5_5 : (RadiusThree.familyForKind 5).map (rotatePatch 5 (hexRegion 3)) = rows0_5_5.map Verdict.patch := by
  symm
  simp only [rows0_5_5, List.map_flatten, List.map_cons, List.map_nil, ← initial5_5_0, ← initial5_5_1, ← initial5_5_2]
  change ([source5_0, source5_1, source5_2].map (List.map (rotatePatch 5 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source5_split]

end SpectreFinite.HexSearch.RadiusThreePruning
