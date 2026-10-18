module

public import SpectreFinite.RadiusThreePruningBlock0T0C0
public import SpectreFinite.RadiusThreePruningBlock0T0C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_0 : List (Verdict 6) := [rows0_0_0_0, rows0_0_0_1].flatten
theorem check0_0_0 : checkRows direction samples0 trees0 rows0_0_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_0_0_0, check0_0_0_1, Bool.true_and]
def rows1_0_0 : List (Verdict 6) := [rows1_0_0_0, rows1_0_0_1].flatten
theorem check1_0_0 : checkRows direction samples1 trees1 rows1_0_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_0_0_0, check1_0_0_1, Bool.true_and]
theorem link1_0_0 : rows1_0_0.map Verdict.patch = rows0_0_0.filterMap Verdict.kept := by
  simp only [rows1_0_0, rows0_0_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_0_0_0, link1_0_0_1]
def rows2_0_0 : List (Verdict 6) := [rows2_0_0_0, rows2_0_0_1].flatten
theorem check2_0_0 : checkRows direction samples2 trees2 rows2_0_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_0_0_0, check2_0_0_1, Bool.true_and]
theorem link2_0_0 : rows2_0_0.map Verdict.patch = rows1_0_0.filterMap Verdict.kept := by
  simp only [rows2_0_0, rows1_0_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_0_0_0, link2_0_0_1]
theorem initial0_0 : (RadiusThree.familyForKind 0).map (rotatePatch 0 (hexRegion 3)) = rows0_0_0.map Verdict.patch := by
  symm
  simp only [rows0_0_0, List.map_flatten, List.map_cons, List.map_nil, ← initial0_0_0, ← initial0_0_1]
  change ([source0_0, source0_1].map (List.map (rotatePatch 0 (hexRegion 3)))).flatten = _
  rw [← List.map_flatten, source0_split]

end SpectreFinite.HexSearch.RadiusThreePruning
