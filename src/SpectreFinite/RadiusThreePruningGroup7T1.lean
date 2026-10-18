module

public import SpectreFinite.RadiusThreePruningBlock7T1C0
public import SpectreFinite.RadiusThreePruningBlock7T1C1
public import SpectreFinite.RadiusThreePruningBlock7T1C2
public import SpectreFinite.RadiusThreePruningBlock7T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_1 : List (Verdict 6) := [rows0_7_1_0, rows0_7_1_1, rows0_7_1_2, rows0_7_1_3].flatten
theorem check0_7_1 : checkRows direction samples0 trees0 rows0_7_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_7_1_0, check0_7_1_1, check0_7_1_2, check0_7_1_3, Bool.true_and]
def rows1_7_1 : List (Verdict 6) := [rows1_7_1_0, rows1_7_1_1, rows1_7_1_2, rows1_7_1_3].flatten
theorem check1_7_1 : checkRows direction samples1 trees1 rows1_7_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_7_1_0, check1_7_1_1, check1_7_1_2, check1_7_1_3, Bool.true_and]
theorem link1_7_1 : rows1_7_1.map Verdict.patch = rows0_7_1.filterMap Verdict.kept := by
  simp only [rows1_7_1, rows0_7_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_7_1_0, link1_7_1_1, link1_7_1_2, link1_7_1_3]
def rows2_7_1 : List (Verdict 6) := [rows2_7_1_0, rows2_7_1_1, rows2_7_1_2, rows2_7_1_3].flatten
theorem check2_7_1 : checkRows direction samples2 trees2 rows2_7_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_7_1_0, check2_7_1_1, check2_7_1_2, check2_7_1_3, Bool.true_and]
theorem link2_7_1 : rows2_7_1.map Verdict.patch = rows1_7_1.filterMap Verdict.kept := by
  simp only [rows2_7_1, rows1_7_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_7_1_0, link2_7_1_1, link2_7_1_2, link2_7_1_3]
theorem initial7_1 : (RadiusThree.familyForKind 7).map (rotatePatch 1 (hexRegion 3)) = rows0_7_1.map Verdict.patch := by
  symm
  simp only [rows0_7_1, List.map_flatten, List.map_cons, List.map_nil, ← initial7_1_0, ← initial7_1_1, ← initial7_1_2, ← initial7_1_3]
  change ([source7_0, source7_1, source7_2, source7_3].map (List.map (rotatePatch 1 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source7_split]

end SpectreFinite.HexSearch.RadiusThreePruning
