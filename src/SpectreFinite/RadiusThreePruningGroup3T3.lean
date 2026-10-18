module

public import SpectreFinite.RadiusThreePruningBlock3T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_3 : List (Verdict 6) := [rows0_3_3_0].flatten
theorem check0_3_3 : checkRows direction samples0 trees0 rows0_3_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_3_3_0, Bool.true_and]
def rows1_3_3 : List (Verdict 6) := [rows1_3_3_0].flatten
theorem check1_3_3 : checkRows direction samples1 trees1 rows1_3_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_3_3_0, Bool.true_and]
theorem link1_3_3 : rows1_3_3.map Verdict.patch = rows0_3_3.filterMap Verdict.kept := by
  simp only [rows1_3_3, rows0_3_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_3_3_0]
def rows2_3_3 : List (Verdict 6) := [rows2_3_3_0].flatten
theorem check2_3_3 : checkRows direction samples2 trees2 rows2_3_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_3_3_0, Bool.true_and]
theorem link2_3_3 : rows2_3_3.map Verdict.patch = rows1_3_3.filterMap Verdict.kept := by
  simp only [rows2_3_3, rows1_3_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_3_3_0]
theorem initial3_3 : (RadiusThree.familyForKind 3).map (rotatePatch 3 (hexRegion 3)) = rows0_3_3.map Verdict.patch := by
  symm
  simp only [rows0_3_3, List.map_flatten, List.map_cons, List.map_nil, ← initial3_3_0]
  change ([source3_0].map (List.map (rotatePatch 3 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source3_split]

end SpectreFinite.HexSearch.RadiusThreePruning
