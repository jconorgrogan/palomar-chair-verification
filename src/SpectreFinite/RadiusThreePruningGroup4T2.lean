module

public import SpectreFinite.RadiusThreePruningBlock4T2C0
public import SpectreFinite.RadiusThreePruningBlock4T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_2 : List (Verdict 6) := [rows0_4_2_0, rows0_4_2_1].flatten
theorem check0_4_2 : checkRows direction samples0 trees0 rows0_4_2 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_4_2_0, check0_4_2_1, Bool.true_and]
def rows1_4_2 : List (Verdict 6) := [rows1_4_2_0, rows1_4_2_1].flatten
theorem check1_4_2 : checkRows direction samples1 trees1 rows1_4_2 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_4_2_0, check1_4_2_1, Bool.true_and]
theorem link1_4_2 : rows1_4_2.map Verdict.patch = rows0_4_2.filterMap Verdict.kept := by
  simp only [rows1_4_2, rows0_4_2, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_4_2_0, link1_4_2_1]
def rows2_4_2 : List (Verdict 6) := [rows2_4_2_0, rows2_4_2_1].flatten
theorem check2_4_2 : checkRows direction samples2 trees2 rows2_4_2 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_4_2_0, check2_4_2_1, Bool.true_and]
theorem link2_4_2 : rows2_4_2.map Verdict.patch = rows1_4_2.filterMap Verdict.kept := by
  simp only [rows2_4_2, rows1_4_2, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_4_2_0, link2_4_2_1]
theorem initial4_2 : (RadiusThree.familyForKind 4).map (rotatePatch 2 (hexRegion 3)) = rows0_4_2.map Verdict.patch := by
  symm
  simp only [rows0_4_2, List.map_flatten, List.map_cons, List.map_nil, ← initial4_2_0, ← initial4_2_1]
  change ([source4_0, source4_1].map (List.map (rotatePatch 2 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source4_split]

end SpectreFinite.HexSearch.RadiusThreePruning
