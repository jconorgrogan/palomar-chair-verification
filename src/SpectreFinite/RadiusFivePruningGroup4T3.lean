module

public import SpectreFinite.RadiusFivePruningBlock4T3C0
public import SpectreFinite.RadiusFivePruningBlock4T3C1
public import SpectreFinite.RadiusFivePruningBlock4T3C2
public import SpectreFinite.RadiusFivePruningBlock4T3C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_3 : List (Verdict 6) := [rows0_4_3_0, rows0_4_3_1, rows0_4_3_2, rows0_4_3_3].flatten
theorem check0_4_3 : checkRows direction samples0 trees0 rows0_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_4_3_0, check0_4_3_1, check0_4_3_2, check0_4_3_3, Bool.true_and]
def rows1_4_3 : List (Verdict 6) := [rows1_4_3_0, rows1_4_3_1, rows1_4_3_2, rows1_4_3_3].flatten
theorem check1_4_3 : checkRows direction samples1 trees1 rows1_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_4_3_0, check1_4_3_1, check1_4_3_2, check1_4_3_3, Bool.true_and]
theorem link1_4_3 : rows1_4_3.map Verdict.patch = rows0_4_3.filterMap Verdict.kept := by
  simp only [rows1_4_3, rows0_4_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_4_3_0, link1_4_3_1, link1_4_3_2, link1_4_3_3]
def rows2_4_3 : List (Verdict 6) := [rows2_4_3_0, rows2_4_3_1, rows2_4_3_2, rows2_4_3_3].flatten
theorem check2_4_3 : checkRows direction samples2 trees2 rows2_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_4_3_0, check2_4_3_1, check2_4_3_2, check2_4_3_3, Bool.true_and]
theorem link2_4_3 : rows2_4_3.map Verdict.patch = rows1_4_3.filterMap Verdict.kept := by
  simp only [rows2_4_3, rows1_4_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_4_3_0, link2_4_3_1, link2_4_3_2, link2_4_3_3]
def rows3_4_3 : List (Verdict 6) := [rows3_4_3_0, rows3_4_3_1, rows3_4_3_2, rows3_4_3_3].flatten
theorem check3_4_3 : checkRows direction samples3 trees3 rows3_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_4_3_0, check3_4_3_1, check3_4_3_2, check3_4_3_3, Bool.true_and]
theorem link3_4_3 : rows3_4_3.map Verdict.patch = rows2_4_3.filterMap Verdict.kept := by
  simp only [rows3_4_3, rows2_4_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_4_3_0, link3_4_3_1, link3_4_3_2, link3_4_3_3]
def rows4_4_3 : List (Verdict 6) := [rows4_4_3_0, rows4_4_3_1, rows4_4_3_2, rows4_4_3_3].flatten
theorem check4_4_3 : checkRows direction samples4 trees4 rows4_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_4_3_0, check4_4_3_1, check4_4_3_2, check4_4_3_3, Bool.true_and]
theorem link4_4_3 : rows4_4_3.map Verdict.patch = rows3_4_3.filterMap Verdict.kept := by
  simp only [rows4_4_3, rows3_4_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_4_3_0, link4_4_3_1, link4_4_3_2, link4_4_3_3]
def rows5_4_3 : List (Verdict 6) := [rows5_4_3_0, rows5_4_3_1, rows5_4_3_2, rows5_4_3_3].flatten
theorem check5_4_3 : checkRows direction samples5 trees5 rows5_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_4_3_0, check5_4_3_1, check5_4_3_2, check5_4_3_3, Bool.true_and]
theorem link5_4_3 : rows5_4_3.map Verdict.patch = rows4_4_3.filterMap Verdict.kept := by
  simp only [rows5_4_3, rows4_4_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_4_3_0, link5_4_3_1, link5_4_3_2, link5_4_3_3]
def rows6_4_3 : List (Verdict 6) := [rows6_4_3_0, rows6_4_3_1, rows6_4_3_2, rows6_4_3_3].flatten
theorem check6_4_3 : checkRows direction samples6 trees6 rows6_4_3 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_4_3_0, check6_4_3_1, check6_4_3_2, check6_4_3_3, Bool.true_and]
theorem link6_4_3 : rows6_4_3.map Verdict.patch = rows5_4_3.filterMap Verdict.kept := by
  simp only [rows6_4_3, rows5_4_3, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_4_3_0, link6_4_3_1, link6_4_3_2, link6_4_3_3]
theorem initial4_3 : (RadiusFive.familyForKind 4).map (rotatePatch 3 (hexRegion 5)) = rows0_4_3.map Verdict.patch := by
  symm
  simp only [rows0_4_3, List.map_flatten, List.map_cons, List.map_nil, ← initial4_3_0, ← initial4_3_1, ← initial4_3_2, ← initial4_3_3]
  change ([source4_0, source4_1, source4_2, source4_3].map (List.map (rotatePatch 3 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source4_split]

end SpectreFinite.HexSearch.RadiusFivePruning
