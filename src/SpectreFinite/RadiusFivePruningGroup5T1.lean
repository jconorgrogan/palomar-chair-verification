module

public import SpectreFinite.RadiusFivePruningBlock5T1C0
public import SpectreFinite.RadiusFivePruningBlock5T1C1
public import SpectreFinite.RadiusFivePruningBlock5T1C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_1 : List (Verdict 6) := [rows0_5_1_0, rows0_5_1_1, rows0_5_1_2].flatten
theorem check0_5_1 : checkRows direction samples0 trees0 rows0_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_5_1_0, check0_5_1_1, check0_5_1_2, Bool.true_and]
def rows1_5_1 : List (Verdict 6) := [rows1_5_1_0, rows1_5_1_1, rows1_5_1_2].flatten
theorem check1_5_1 : checkRows direction samples1 trees1 rows1_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_5_1_0, check1_5_1_1, check1_5_1_2, Bool.true_and]
theorem link1_5_1 : rows1_5_1.map Verdict.patch = rows0_5_1.filterMap Verdict.kept := by
  simp only [rows1_5_1, rows0_5_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_5_1_0, link1_5_1_1, link1_5_1_2]
def rows2_5_1 : List (Verdict 6) := [rows2_5_1_0, rows2_5_1_1, rows2_5_1_2].flatten
theorem check2_5_1 : checkRows direction samples2 trees2 rows2_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_5_1_0, check2_5_1_1, check2_5_1_2, Bool.true_and]
theorem link2_5_1 : rows2_5_1.map Verdict.patch = rows1_5_1.filterMap Verdict.kept := by
  simp only [rows2_5_1, rows1_5_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_5_1_0, link2_5_1_1, link2_5_1_2]
def rows3_5_1 : List (Verdict 6) := [rows3_5_1_0, rows3_5_1_1, rows3_5_1_2].flatten
theorem check3_5_1 : checkRows direction samples3 trees3 rows3_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_5_1_0, check3_5_1_1, check3_5_1_2, Bool.true_and]
theorem link3_5_1 : rows3_5_1.map Verdict.patch = rows2_5_1.filterMap Verdict.kept := by
  simp only [rows3_5_1, rows2_5_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_5_1_0, link3_5_1_1, link3_5_1_2]
def rows4_5_1 : List (Verdict 6) := [rows4_5_1_0, rows4_5_1_1, rows4_5_1_2].flatten
theorem check4_5_1 : checkRows direction samples4 trees4 rows4_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_5_1_0, check4_5_1_1, check4_5_1_2, Bool.true_and]
theorem link4_5_1 : rows4_5_1.map Verdict.patch = rows3_5_1.filterMap Verdict.kept := by
  simp only [rows4_5_1, rows3_5_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_5_1_0, link4_5_1_1, link4_5_1_2]
def rows5_5_1 : List (Verdict 6) := [rows5_5_1_0, rows5_5_1_1, rows5_5_1_2].flatten
theorem check5_5_1 : checkRows direction samples5 trees5 rows5_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_5_1_0, check5_5_1_1, check5_5_1_2, Bool.true_and]
theorem link5_5_1 : rows5_5_1.map Verdict.patch = rows4_5_1.filterMap Verdict.kept := by
  simp only [rows5_5_1, rows4_5_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_5_1_0, link5_5_1_1, link5_5_1_2]
def rows6_5_1 : List (Verdict 6) := [rows6_5_1_0, rows6_5_1_1, rows6_5_1_2].flatten
theorem check6_5_1 : checkRows direction samples6 trees6 rows6_5_1 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_5_1_0, check6_5_1_1, check6_5_1_2, Bool.true_and]
theorem link6_5_1 : rows6_5_1.map Verdict.patch = rows5_5_1.filterMap Verdict.kept := by
  simp only [rows6_5_1, rows5_5_1, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_5_1_0, link6_5_1_1, link6_5_1_2]
theorem initial5_1 : (RadiusFive.familyForKind 5).map (rotatePatch 1 (hexRegion 5)) = rows0_5_1.map Verdict.patch := by
  symm
  simp only [rows0_5_1, List.map_flatten, List.map_cons, List.map_nil, ← initial5_1_0, ← initial5_1_1, ← initial5_1_2]
  change ([source5_0, source5_1, source5_2].map (List.map (rotatePatch 1 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source5_split]

end SpectreFinite.HexSearch.RadiusFivePruning
