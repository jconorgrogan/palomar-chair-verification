module

public import SpectreFinite.RadiusFivePruningBlock6T0C0
public import SpectreFinite.RadiusFivePruningBlock6T0C1
public import SpectreFinite.RadiusFivePruningBlock6T0C2
public import SpectreFinite.RadiusFivePruningBlock6T0C3
public import SpectreFinite.RadiusFivePruningBlock6T0C4
public import SpectreFinite.RadiusFivePruningBlock6T0C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_0 : List (Verdict 6) := [rows0_6_0_0, rows0_6_0_1, rows0_6_0_2, rows0_6_0_3, rows0_6_0_4, rows0_6_0_5].flatten
theorem check0_6_0 : checkRows direction samples0 trees0 rows0_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_6_0_0, check0_6_0_1, check0_6_0_2, check0_6_0_3, check0_6_0_4, check0_6_0_5, Bool.true_and]
def rows1_6_0 : List (Verdict 6) := [rows1_6_0_0, rows1_6_0_1, rows1_6_0_2, rows1_6_0_3, rows1_6_0_4, rows1_6_0_5].flatten
theorem check1_6_0 : checkRows direction samples1 trees1 rows1_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_6_0_0, check1_6_0_1, check1_6_0_2, check1_6_0_3, check1_6_0_4, check1_6_0_5, Bool.true_and]
theorem link1_6_0 : rows1_6_0.map Verdict.patch = rows0_6_0.filterMap Verdict.kept := by
  simp only [rows1_6_0, rows0_6_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_6_0_0, link1_6_0_1, link1_6_0_2, link1_6_0_3, link1_6_0_4, link1_6_0_5]
def rows2_6_0 : List (Verdict 6) := [rows2_6_0_0, rows2_6_0_1, rows2_6_0_2, rows2_6_0_3, rows2_6_0_4, rows2_6_0_5].flatten
theorem check2_6_0 : checkRows direction samples2 trees2 rows2_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_6_0_0, check2_6_0_1, check2_6_0_2, check2_6_0_3, check2_6_0_4, check2_6_0_5, Bool.true_and]
theorem link2_6_0 : rows2_6_0.map Verdict.patch = rows1_6_0.filterMap Verdict.kept := by
  simp only [rows2_6_0, rows1_6_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_6_0_0, link2_6_0_1, link2_6_0_2, link2_6_0_3, link2_6_0_4, link2_6_0_5]
def rows3_6_0 : List (Verdict 6) := [rows3_6_0_0, rows3_6_0_1, rows3_6_0_2, rows3_6_0_3, rows3_6_0_4, rows3_6_0_5].flatten
theorem check3_6_0 : checkRows direction samples3 trees3 rows3_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_6_0_0, check3_6_0_1, check3_6_0_2, check3_6_0_3, check3_6_0_4, check3_6_0_5, Bool.true_and]
theorem link3_6_0 : rows3_6_0.map Verdict.patch = rows2_6_0.filterMap Verdict.kept := by
  simp only [rows3_6_0, rows2_6_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_6_0_0, link3_6_0_1, link3_6_0_2, link3_6_0_3, link3_6_0_4, link3_6_0_5]
def rows4_6_0 : List (Verdict 6) := [rows4_6_0_0, rows4_6_0_1, rows4_6_0_2, rows4_6_0_3, rows4_6_0_4, rows4_6_0_5].flatten
theorem check4_6_0 : checkRows direction samples4 trees4 rows4_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_6_0_0, check4_6_0_1, check4_6_0_2, check4_6_0_3, check4_6_0_4, check4_6_0_5, Bool.true_and]
theorem link4_6_0 : rows4_6_0.map Verdict.patch = rows3_6_0.filterMap Verdict.kept := by
  simp only [rows4_6_0, rows3_6_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_6_0_0, link4_6_0_1, link4_6_0_2, link4_6_0_3, link4_6_0_4, link4_6_0_5]
def rows5_6_0 : List (Verdict 6) := [rows5_6_0_0, rows5_6_0_1, rows5_6_0_2, rows5_6_0_3, rows5_6_0_4, rows5_6_0_5].flatten
theorem check5_6_0 : checkRows direction samples5 trees5 rows5_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_6_0_0, check5_6_0_1, check5_6_0_2, check5_6_0_3, check5_6_0_4, check5_6_0_5, Bool.true_and]
theorem link5_6_0 : rows5_6_0.map Verdict.patch = rows4_6_0.filterMap Verdict.kept := by
  simp only [rows5_6_0, rows4_6_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_6_0_0, link5_6_0_1, link5_6_0_2, link5_6_0_3, link5_6_0_4, link5_6_0_5]
def rows6_6_0 : List (Verdict 6) := [rows6_6_0_0, rows6_6_0_1, rows6_6_0_2, rows6_6_0_3, rows6_6_0_4, rows6_6_0_5].flatten
theorem check6_6_0 : checkRows direction samples6 trees6 rows6_6_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_6_0_0, check6_6_0_1, check6_6_0_2, check6_6_0_3, check6_6_0_4, check6_6_0_5, Bool.true_and]
theorem link6_6_0 : rows6_6_0.map Verdict.patch = rows5_6_0.filterMap Verdict.kept := by
  simp only [rows6_6_0, rows5_6_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_6_0_0, link6_6_0_1, link6_6_0_2, link6_6_0_3, link6_6_0_4, link6_6_0_5]
theorem initial6_0 : (RadiusFive.familyForKind 6).map (rotatePatch 0 (hexRegion 5)) = rows0_6_0.map Verdict.patch := by
  symm
  simp only [rows0_6_0, List.map_flatten, List.map_cons, List.map_nil, ← initial6_0_0, ← initial6_0_1, ← initial6_0_2, ← initial6_0_3, ← initial6_0_4, ← initial6_0_5]
  change ([source6_0, source6_1, source6_2, source6_3, source6_4, source6_5].map (List.map (rotatePatch 0 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source6_split]

end SpectreFinite.HexSearch.RadiusFivePruning
