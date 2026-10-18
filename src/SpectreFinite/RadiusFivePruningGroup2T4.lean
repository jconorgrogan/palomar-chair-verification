module

public import SpectreFinite.RadiusFivePruningBlock2T4C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_4 : List (Verdict 6) := [rows0_2_4_0].flatten
theorem check0_2_4 : checkRows direction samples0 trees0 rows0_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_2_4_0, Bool.true_and]
def rows1_2_4 : List (Verdict 6) := [rows1_2_4_0].flatten
theorem check1_2_4 : checkRows direction samples1 trees1 rows1_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_2_4_0, Bool.true_and]
theorem link1_2_4 : rows1_2_4.map Verdict.patch = rows0_2_4.filterMap Verdict.kept := by
  simp only [rows1_2_4, rows0_2_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_2_4_0]
def rows2_2_4 : List (Verdict 6) := [rows2_2_4_0].flatten
theorem check2_2_4 : checkRows direction samples2 trees2 rows2_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_2_4_0, Bool.true_and]
theorem link2_2_4 : rows2_2_4.map Verdict.patch = rows1_2_4.filterMap Verdict.kept := by
  simp only [rows2_2_4, rows1_2_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_2_4_0]
def rows3_2_4 : List (Verdict 6) := [rows3_2_4_0].flatten
theorem check3_2_4 : checkRows direction samples3 trees3 rows3_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_2_4_0, Bool.true_and]
theorem link3_2_4 : rows3_2_4.map Verdict.patch = rows2_2_4.filterMap Verdict.kept := by
  simp only [rows3_2_4, rows2_2_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_2_4_0]
def rows4_2_4 : List (Verdict 6) := [rows4_2_4_0].flatten
theorem check4_2_4 : checkRows direction samples4 trees4 rows4_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_2_4_0, Bool.true_and]
theorem link4_2_4 : rows4_2_4.map Verdict.patch = rows3_2_4.filterMap Verdict.kept := by
  simp only [rows4_2_4, rows3_2_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_2_4_0]
def rows5_2_4 : List (Verdict 6) := [rows5_2_4_0].flatten
theorem check5_2_4 : checkRows direction samples5 trees5 rows5_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_2_4_0, Bool.true_and]
theorem link5_2_4 : rows5_2_4.map Verdict.patch = rows4_2_4.filterMap Verdict.kept := by
  simp only [rows5_2_4, rows4_2_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_2_4_0]
def rows6_2_4 : List (Verdict 6) := [rows6_2_4_0].flatten
theorem check6_2_4 : checkRows direction samples6 trees6 rows6_2_4 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_2_4_0, Bool.true_and]
theorem link6_2_4 : rows6_2_4.map Verdict.patch = rows5_2_4.filterMap Verdict.kept := by
  simp only [rows6_2_4, rows5_2_4, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_2_4_0]
theorem initial2_4 : (RadiusFive.familyForKind 2).map (rotatePatch 4 (hexRegion 5)) = rows0_2_4.map Verdict.patch := by
  symm
  simp only [rows0_2_4, List.map_flatten, List.map_cons, List.map_nil, ← initial2_4_0]
  change ([source2_0].map (List.map (rotatePatch 4 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source2_split]

end SpectreFinite.HexSearch.RadiusFivePruning
