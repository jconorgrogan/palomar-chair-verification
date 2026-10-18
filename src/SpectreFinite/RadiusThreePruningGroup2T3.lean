module

public import SpectreFinite.RadiusThreePruningBlock2T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_3 : List (Verdict 6) := [rows0_2_3_0].flatten
theorem check0_2_3 : checkRows direction samples0 trees0 rows0_2_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_2_3_0, Bool.true_and]
def rows1_2_3 : List (Verdict 6) := [rows1_2_3_0].flatten
theorem check1_2_3 : checkRows direction samples1 trees1 rows1_2_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_2_3_0, Bool.true_and]
theorem link1_2_3 : rows1_2_3.map Verdict.patch = rows0_2_3.filterMap Verdict.kept := by
  simp only [rows1_2_3, rows0_2_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_2_3_0]
def rows2_2_3 : List (Verdict 6) := [rows2_2_3_0].flatten
theorem check2_2_3 : checkRows direction samples2 trees2 rows2_2_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_2_3_0, Bool.true_and]
theorem link2_2_3 : rows2_2_3.map Verdict.patch = rows1_2_3.filterMap Verdict.kept := by
  simp only [rows2_2_3, rows1_2_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_2_3_0]
theorem initial2_3 : (RadiusThree.familyForKind 2).map (rotatePatch 3 (hexRegion 3)) = rows0_2_3.map Verdict.patch := by
  symm
  simp only [rows0_2_3, List.map_flatten, List.map_cons, List.map_nil, ← initial2_3_0]
  change ([source2_0].map (List.map (rotatePatch 3 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source2_split]

end SpectreFinite.HexSearch.RadiusThreePruning
