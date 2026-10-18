module

public import SpectreFinite.RadiusFivePruningBlock1T4C0
public import SpectreFinite.RadiusFivePruningBlock1T4C1
public import SpectreFinite.RadiusFivePruningBlock1T4C2
public import SpectreFinite.RadiusFivePruningBlock1T4C3
public import SpectreFinite.RadiusFivePruningBlock1T4C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_4 : List (Verdict 6) := [rows0_1_4_0, rows0_1_4_1, rows0_1_4_2, rows0_1_4_3, rows0_1_4_4].flatten
theorem check0_1_4 : checkRows direction samples0 trees0 rows0_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_1_4_0, check0_1_4_1, check0_1_4_2, check0_1_4_3, check0_1_4_4, Bool.true_and]
def rows1_1_4 : List (Verdict 6) := [rows1_1_4_0, rows1_1_4_1, rows1_1_4_2, rows1_1_4_3, rows1_1_4_4].flatten
theorem check1_1_4 : checkRows direction samples1 trees1 rows1_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_1_4_0, check1_1_4_1, check1_1_4_2, check1_1_4_3, check1_1_4_4, Bool.true_and]
theorem link1_1_4 : rows1_1_4.map Verdict.patch = rows0_1_4.filterMap Verdict.kept := by
  simp only [rows1_1_4, rows0_1_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_1_4_0, link1_1_4_1, link1_1_4_2, link1_1_4_3, link1_1_4_4]
def rows2_1_4 : List (Verdict 6) := [rows2_1_4_0, rows2_1_4_1, rows2_1_4_2, rows2_1_4_3, rows2_1_4_4].flatten
theorem check2_1_4 : checkRows direction samples2 trees2 rows2_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_1_4_0, check2_1_4_1, check2_1_4_2, check2_1_4_3, check2_1_4_4, Bool.true_and]
theorem link2_1_4 : rows2_1_4.map Verdict.patch = rows1_1_4.filterMap Verdict.kept := by
  simp only [rows2_1_4, rows1_1_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_1_4_0, link2_1_4_1, link2_1_4_2, link2_1_4_3, link2_1_4_4]
def rows3_1_4 : List (Verdict 6) := [rows3_1_4_0, rows3_1_4_1, rows3_1_4_2, rows3_1_4_3, rows3_1_4_4].flatten
theorem check3_1_4 : checkRows direction samples3 trees3 rows3_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_1_4_0, check3_1_4_1, check3_1_4_2, check3_1_4_3, check3_1_4_4, Bool.true_and]
theorem link3_1_4 : rows3_1_4.map Verdict.patch = rows2_1_4.filterMap Verdict.kept := by
  simp only [rows3_1_4, rows2_1_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_1_4_0, link3_1_4_1, link3_1_4_2, link3_1_4_3, link3_1_4_4]
def rows4_1_4 : List (Verdict 6) := [rows4_1_4_0, rows4_1_4_1, rows4_1_4_2, rows4_1_4_3, rows4_1_4_4].flatten
theorem check4_1_4 : checkRows direction samples4 trees4 rows4_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_1_4_0, check4_1_4_1, check4_1_4_2, check4_1_4_3, check4_1_4_4, Bool.true_and]
theorem link4_1_4 : rows4_1_4.map Verdict.patch = rows3_1_4.filterMap Verdict.kept := by
  simp only [rows4_1_4, rows3_1_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_1_4_0, link4_1_4_1, link4_1_4_2, link4_1_4_3, link4_1_4_4]
def rows5_1_4 : List (Verdict 6) := [rows5_1_4_0, rows5_1_4_1, rows5_1_4_2, rows5_1_4_3, rows5_1_4_4].flatten
theorem check5_1_4 : checkRows direction samples5 trees5 rows5_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_1_4_0, check5_1_4_1, check5_1_4_2, check5_1_4_3, check5_1_4_4, Bool.true_and]
theorem link5_1_4 : rows5_1_4.map Verdict.patch = rows4_1_4.filterMap Verdict.kept := by
  simp only [rows5_1_4, rows4_1_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_1_4_0, link5_1_4_1, link5_1_4_2, link5_1_4_3, link5_1_4_4]
def rows6_1_4 : List (Verdict 6) := [rows6_1_4_0, rows6_1_4_1, rows6_1_4_2, rows6_1_4_3, rows6_1_4_4].flatten
theorem check6_1_4 : checkRows direction samples6 trees6 rows6_1_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_1_4_0, check6_1_4_1, check6_1_4_2, check6_1_4_3, check6_1_4_4, Bool.true_and]
theorem link6_1_4 : rows6_1_4.map Verdict.patch = rows5_1_4.filterMap Verdict.kept := by
  simp only [rows6_1_4, rows5_1_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_1_4_0, link6_1_4_1, link6_1_4_2, link6_1_4_3, link6_1_4_4]
theorem initial1_4 : (RadiusFive.familyForKind 1).map (rotatePatch 4 (hexRegion 5)) = rows0_1_4.map Verdict.patch := by
  symm
  simp only [rows0_1_4, List.map_flatten, List.map_cons, List.map_nil, ← initial1_4_0, ← initial1_4_1, ← initial1_4_2, ← initial1_4_3, ← initial1_4_4]
  change ([source1_0, source1_1, source1_2, source1_3, source1_4].map (List.map (rotatePatch 4 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source1_split]

end SpectreFinite.HexSearch.RadiusFivePruning
