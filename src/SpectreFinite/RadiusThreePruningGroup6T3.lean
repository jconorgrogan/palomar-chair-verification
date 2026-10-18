module

public import SpectreFinite.RadiusThreePruningBlock6T3C0
public import SpectreFinite.RadiusThreePruningBlock6T3C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_3 : List (Verdict 6) := [rows0_6_3_0, rows0_6_3_1].flatten
theorem check0_6_3 : checkRows direction samples0 trees0 rows0_6_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_6_3_0, check0_6_3_1, Bool.true_and]
def rows1_6_3 : List (Verdict 6) := [rows1_6_3_0, rows1_6_3_1].flatten
theorem check1_6_3 : checkRows direction samples1 trees1 rows1_6_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_6_3_0, check1_6_3_1, Bool.true_and]
theorem link1_6_3 : rows1_6_3.map Verdict.patch = rows0_6_3.filterMap Verdict.kept := by
  simp only [rows1_6_3, rows0_6_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_6_3_0, link1_6_3_1]
def rows2_6_3 : List (Verdict 6) := [rows2_6_3_0, rows2_6_3_1].flatten
theorem check2_6_3 : checkRows direction samples2 trees2 rows2_6_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_6_3_0, check2_6_3_1, Bool.true_and]
theorem link2_6_3 : rows2_6_3.map Verdict.patch = rows1_6_3.filterMap Verdict.kept := by
  simp only [rows2_6_3, rows1_6_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_6_3_0, link2_6_3_1]
theorem initial6_3 : (RadiusThree.familyForKind 6).map (rotatePatch 3 (hexRegion 3)) = rows0_6_3.map Verdict.patch := by
  symm
  simp only [rows0_6_3, List.map_flatten, List.map_cons, List.map_nil, ← initial6_3_0, ← initial6_3_1]
  change ([source6_0, source6_1].map (List.map (rotatePatch 3 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source6_split]

end SpectreFinite.HexSearch.RadiusThreePruning
