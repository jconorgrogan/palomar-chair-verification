module

public import SpectreFinite.RadiusFivePruningBlock8T0C0
public import SpectreFinite.RadiusFivePruningBlock8T0C1
public import SpectreFinite.RadiusFivePruningBlock8T0C2
public import SpectreFinite.RadiusFivePruningBlock8T0C3
public import SpectreFinite.RadiusFivePruningBlock8T0C4
public import SpectreFinite.RadiusFivePruningBlock8T0C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_0 : List (Verdict 6) := [rows0_8_0_0, rows0_8_0_1, rows0_8_0_2, rows0_8_0_3, rows0_8_0_4, rows0_8_0_5].flatten
theorem check0_8_0 : checkRows direction samples0 trees0 rows0_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_8_0_0, check0_8_0_1, check0_8_0_2, check0_8_0_3, check0_8_0_4, check0_8_0_5, Bool.true_and]
def rows1_8_0 : List (Verdict 6) := [rows1_8_0_0, rows1_8_0_1, rows1_8_0_2, rows1_8_0_3, rows1_8_0_4, rows1_8_0_5].flatten
theorem check1_8_0 : checkRows direction samples1 trees1 rows1_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_8_0_0, check1_8_0_1, check1_8_0_2, check1_8_0_3, check1_8_0_4, check1_8_0_5, Bool.true_and]
theorem link1_8_0 : rows1_8_0.map Verdict.patch = rows0_8_0.filterMap Verdict.kept := by
  simp only [rows1_8_0, rows0_8_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_8_0_0, link1_8_0_1, link1_8_0_2, link1_8_0_3, link1_8_0_4, link1_8_0_5]
def rows2_8_0 : List (Verdict 6) := [rows2_8_0_0, rows2_8_0_1, rows2_8_0_2, rows2_8_0_3, rows2_8_0_4, rows2_8_0_5].flatten
theorem check2_8_0 : checkRows direction samples2 trees2 rows2_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_8_0_0, check2_8_0_1, check2_8_0_2, check2_8_0_3, check2_8_0_4, check2_8_0_5, Bool.true_and]
theorem link2_8_0 : rows2_8_0.map Verdict.patch = rows1_8_0.filterMap Verdict.kept := by
  simp only [rows2_8_0, rows1_8_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_8_0_0, link2_8_0_1, link2_8_0_2, link2_8_0_3, link2_8_0_4, link2_8_0_5]
def rows3_8_0 : List (Verdict 6) := [rows3_8_0_0, rows3_8_0_1, rows3_8_0_2, rows3_8_0_3, rows3_8_0_4, rows3_8_0_5].flatten
theorem check3_8_0 : checkRows direction samples3 trees3 rows3_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_8_0_0, check3_8_0_1, check3_8_0_2, check3_8_0_3, check3_8_0_4, check3_8_0_5, Bool.true_and]
theorem link3_8_0 : rows3_8_0.map Verdict.patch = rows2_8_0.filterMap Verdict.kept := by
  simp only [rows3_8_0, rows2_8_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_8_0_0, link3_8_0_1, link3_8_0_2, link3_8_0_3, link3_8_0_4, link3_8_0_5]
def rows4_8_0 : List (Verdict 6) := [rows4_8_0_0, rows4_8_0_1, rows4_8_0_2, rows4_8_0_3, rows4_8_0_4, rows4_8_0_5].flatten
theorem check4_8_0 : checkRows direction samples4 trees4 rows4_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_8_0_0, check4_8_0_1, check4_8_0_2, check4_8_0_3, check4_8_0_4, check4_8_0_5, Bool.true_and]
theorem link4_8_0 : rows4_8_0.map Verdict.patch = rows3_8_0.filterMap Verdict.kept := by
  simp only [rows4_8_0, rows3_8_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_8_0_0, link4_8_0_1, link4_8_0_2, link4_8_0_3, link4_8_0_4, link4_8_0_5]
def rows5_8_0 : List (Verdict 6) := [rows5_8_0_0, rows5_8_0_1, rows5_8_0_2, rows5_8_0_3, rows5_8_0_4, rows5_8_0_5].flatten
theorem check5_8_0 : checkRows direction samples5 trees5 rows5_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_8_0_0, check5_8_0_1, check5_8_0_2, check5_8_0_3, check5_8_0_4, check5_8_0_5, Bool.true_and]
theorem link5_8_0 : rows5_8_0.map Verdict.patch = rows4_8_0.filterMap Verdict.kept := by
  simp only [rows5_8_0, rows4_8_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_8_0_0, link5_8_0_1, link5_8_0_2, link5_8_0_3, link5_8_0_4, link5_8_0_5]
def rows6_8_0 : List (Verdict 6) := [rows6_8_0_0, rows6_8_0_1, rows6_8_0_2, rows6_8_0_3, rows6_8_0_4, rows6_8_0_5].flatten
theorem check6_8_0 : checkRows direction samples6 trees6 rows6_8_0 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_8_0_0, check6_8_0_1, check6_8_0_2, check6_8_0_3, check6_8_0_4, check6_8_0_5, Bool.true_and]
theorem link6_8_0 : rows6_8_0.map Verdict.patch = rows5_8_0.filterMap Verdict.kept := by
  simp only [rows6_8_0, rows5_8_0, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_8_0_0, link6_8_0_1, link6_8_0_2, link6_8_0_3, link6_8_0_4, link6_8_0_5]
theorem initial8_0 : (RadiusFive.familyForKind 8).map (rotatePatch 0 (hexRegion 5)) = rows0_8_0.map Verdict.patch := by
  symm
  simp only [rows0_8_0, List.map_flatten, List.map_cons, List.map_nil, ← initial8_0_0, ← initial8_0_1, ← initial8_0_2, ← initial8_0_3, ← initial8_0_4, ← initial8_0_5]
  change ([source8_0, source8_1, source8_2, source8_3, source8_4, source8_5].map (List.map (rotatePatch 0 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source8_split]

end SpectreFinite.HexSearch.RadiusFivePruning
