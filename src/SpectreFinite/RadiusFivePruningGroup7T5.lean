module

public import SpectreFinite.RadiusFivePruningBlock7T5C0
public import SpectreFinite.RadiusFivePruningBlock7T5C1
public import SpectreFinite.RadiusFivePruningBlock7T5C2
public import SpectreFinite.RadiusFivePruningBlock7T5C3
public import SpectreFinite.RadiusFivePruningBlock7T5C4
public import SpectreFinite.RadiusFivePruningBlock7T5C5
public import SpectreFinite.RadiusFivePruningBlock7T5C6
public import SpectreFinite.RadiusFivePruningBlock7T5C7
public import SpectreFinite.RadiusFivePruningBlock7T5C8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_5 : List (Verdict 6) := [rows0_7_5_0, rows0_7_5_1, rows0_7_5_2, rows0_7_5_3, rows0_7_5_4, rows0_7_5_5, rows0_7_5_6, rows0_7_5_7, rows0_7_5_8].flatten
theorem check0_7_5 : checkRows direction samples0 trees0 rows0_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_7_5_0, check0_7_5_1, check0_7_5_2, check0_7_5_3, check0_7_5_4, check0_7_5_5, check0_7_5_6, check0_7_5_7, check0_7_5_8, Bool.true_and]
def rows1_7_5 : List (Verdict 6) := [rows1_7_5_0, rows1_7_5_1, rows1_7_5_2, rows1_7_5_3, rows1_7_5_4, rows1_7_5_5, rows1_7_5_6, rows1_7_5_7, rows1_7_5_8].flatten
theorem check1_7_5 : checkRows direction samples1 trees1 rows1_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_7_5_0, check1_7_5_1, check1_7_5_2, check1_7_5_3, check1_7_5_4, check1_7_5_5, check1_7_5_6, check1_7_5_7, check1_7_5_8, Bool.true_and]
theorem link1_7_5 : rows1_7_5.map Verdict.patch = rows0_7_5.filterMap Verdict.kept := by
  simp only [rows1_7_5, rows0_7_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_7_5_0, link1_7_5_1, link1_7_5_2, link1_7_5_3, link1_7_5_4, link1_7_5_5, link1_7_5_6, link1_7_5_7, link1_7_5_8]
def rows2_7_5 : List (Verdict 6) := [rows2_7_5_0, rows2_7_5_1, rows2_7_5_2, rows2_7_5_3, rows2_7_5_4, rows2_7_5_5, rows2_7_5_6, rows2_7_5_7, rows2_7_5_8].flatten
theorem check2_7_5 : checkRows direction samples2 trees2 rows2_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_7_5_0, check2_7_5_1, check2_7_5_2, check2_7_5_3, check2_7_5_4, check2_7_5_5, check2_7_5_6, check2_7_5_7, check2_7_5_8, Bool.true_and]
theorem link2_7_5 : rows2_7_5.map Verdict.patch = rows1_7_5.filterMap Verdict.kept := by
  simp only [rows2_7_5, rows1_7_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_7_5_0, link2_7_5_1, link2_7_5_2, link2_7_5_3, link2_7_5_4, link2_7_5_5, link2_7_5_6, link2_7_5_7, link2_7_5_8]
def rows3_7_5 : List (Verdict 6) := [rows3_7_5_0, rows3_7_5_1, rows3_7_5_2, rows3_7_5_3, rows3_7_5_4, rows3_7_5_5, rows3_7_5_6, rows3_7_5_7, rows3_7_5_8].flatten
theorem check3_7_5 : checkRows direction samples3 trees3 rows3_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_7_5_0, check3_7_5_1, check3_7_5_2, check3_7_5_3, check3_7_5_4, check3_7_5_5, check3_7_5_6, check3_7_5_7, check3_7_5_8, Bool.true_and]
theorem link3_7_5 : rows3_7_5.map Verdict.patch = rows2_7_5.filterMap Verdict.kept := by
  simp only [rows3_7_5, rows2_7_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_7_5_0, link3_7_5_1, link3_7_5_2, link3_7_5_3, link3_7_5_4, link3_7_5_5, link3_7_5_6, link3_7_5_7, link3_7_5_8]
def rows4_7_5 : List (Verdict 6) := [rows4_7_5_0, rows4_7_5_1, rows4_7_5_2, rows4_7_5_3, rows4_7_5_4, rows4_7_5_5, rows4_7_5_6, rows4_7_5_7, rows4_7_5_8].flatten
theorem check4_7_5 : checkRows direction samples4 trees4 rows4_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_7_5_0, check4_7_5_1, check4_7_5_2, check4_7_5_3, check4_7_5_4, check4_7_5_5, check4_7_5_6, check4_7_5_7, check4_7_5_8, Bool.true_and]
theorem link4_7_5 : rows4_7_5.map Verdict.patch = rows3_7_5.filterMap Verdict.kept := by
  simp only [rows4_7_5, rows3_7_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_7_5_0, link4_7_5_1, link4_7_5_2, link4_7_5_3, link4_7_5_4, link4_7_5_5, link4_7_5_6, link4_7_5_7, link4_7_5_8]
def rows5_7_5 : List (Verdict 6) := [rows5_7_5_0, rows5_7_5_1, rows5_7_5_2, rows5_7_5_3, rows5_7_5_4, rows5_7_5_5, rows5_7_5_6, rows5_7_5_7, rows5_7_5_8].flatten
theorem check5_7_5 : checkRows direction samples5 trees5 rows5_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_7_5_0, check5_7_5_1, check5_7_5_2, check5_7_5_3, check5_7_5_4, check5_7_5_5, check5_7_5_6, check5_7_5_7, check5_7_5_8, Bool.true_and]
theorem link5_7_5 : rows5_7_5.map Verdict.patch = rows4_7_5.filterMap Verdict.kept := by
  simp only [rows5_7_5, rows4_7_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_7_5_0, link5_7_5_1, link5_7_5_2, link5_7_5_3, link5_7_5_4, link5_7_5_5, link5_7_5_6, link5_7_5_7, link5_7_5_8]
def rows6_7_5 : List (Verdict 6) := [rows6_7_5_0, rows6_7_5_1, rows6_7_5_2, rows6_7_5_3, rows6_7_5_4, rows6_7_5_5, rows6_7_5_6, rows6_7_5_7, rows6_7_5_8].flatten
theorem check6_7_5 : checkRows direction samples6 trees6 rows6_7_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_7_5_0, check6_7_5_1, check6_7_5_2, check6_7_5_3, check6_7_5_4, check6_7_5_5, check6_7_5_6, check6_7_5_7, check6_7_5_8, Bool.true_and]
theorem link6_7_5 : rows6_7_5.map Verdict.patch = rows5_7_5.filterMap Verdict.kept := by
  simp only [rows6_7_5, rows5_7_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_7_5_0, link6_7_5_1, link6_7_5_2, link6_7_5_3, link6_7_5_4, link6_7_5_5, link6_7_5_6, link6_7_5_7, link6_7_5_8]
theorem initial7_5 : (RadiusFive.familyForKind 7).map (rotatePatch 5 (hexRegion 5)) = rows0_7_5.map Verdict.patch := by
  symm
  simp only [rows0_7_5, List.map_flatten, List.map_cons, List.map_nil, ← initial7_5_0, ← initial7_5_1, ← initial7_5_2, ← initial7_5_3, ← initial7_5_4, ← initial7_5_5, ← initial7_5_6, ← initial7_5_7, ← initial7_5_8]
  change ([source7_0, source7_1, source7_2, source7_3, source7_4, source7_5, source7_6, source7_7, source7_8].map (List.map (rotatePatch 5 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source7_split]

end SpectreFinite.HexSearch.RadiusFivePruning
