module

public import SpectreFinite.RadiusFivePruningBlock3T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_5 : List (Verdict 6) := [rows0_3_5_0].flatten
theorem check0_3_5 : checkRows direction samples0 trees0 rows0_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check0_3_5_0, Bool.true_and]
def rows1_3_5 : List (Verdict 6) := [rows1_3_5_0].flatten
theorem check1_3_5 : checkRows direction samples1 trees1 rows1_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check1_3_5_0, Bool.true_and]
theorem link1_3_5 : rows1_3_5.map Verdict.patch = rows0_3_5.filterMap Verdict.kept := by
  simp only [rows1_3_5, rows0_3_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link1_3_5_0]
def rows2_3_5 : List (Verdict 6) := [rows2_3_5_0].flatten
theorem check2_3_5 : checkRows direction samples2 trees2 rows2_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check2_3_5_0, Bool.true_and]
theorem link2_3_5 : rows2_3_5.map Verdict.patch = rows1_3_5.filterMap Verdict.kept := by
  simp only [rows2_3_5, rows1_3_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link2_3_5_0]
def rows3_3_5 : List (Verdict 6) := [rows3_3_5_0].flatten
theorem check3_3_5 : checkRows direction samples3 trees3 rows3_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check3_3_5_0, Bool.true_and]
theorem link3_3_5 : rows3_3_5.map Verdict.patch = rows2_3_5.filterMap Verdict.kept := by
  simp only [rows3_3_5, rows2_3_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link3_3_5_0]
def rows4_3_5 : List (Verdict 6) := [rows4_3_5_0].flatten
theorem check4_3_5 : checkRows direction samples4 trees4 rows4_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check4_3_5_0, Bool.true_and]
theorem link4_3_5 : rows4_3_5.map Verdict.patch = rows3_3_5.filterMap Verdict.kept := by
  simp only [rows4_3_5, rows3_3_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link4_3_5_0]
def rows5_3_5 : List (Verdict 6) := [rows5_3_5_0].flatten
theorem check5_3_5 : checkRows direction samples5 trees5 rows5_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check5_3_5_0, Bool.true_and]
theorem link5_3_5 : rows5_3_5.map Verdict.patch = rows4_3_5.filterMap Verdict.kept := by
  simp only [rows5_3_5, rows4_3_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link5_3_5_0]
def rows6_3_5 : List (Verdict 6) := [rows6_3_5_0].flatten
theorem check6_3_5 : checkRows direction samples6 trees6 rows6_3_5 = true := by
  apply checkRows_flatten
  simp only [List.all_cons, List.all_nil, check6_3_5_0, Bool.true_and]
theorem link6_3_5 : rows6_3_5.map Verdict.patch = rows5_3_5.filterMap Verdict.kept := by
  simp only [rows6_3_5, rows5_3_5, List.map_flatten, List.filterMap_flatten, List.map_cons, List.map_nil, link6_3_5_0]
theorem initial3_5 : (RadiusFive.familyForKind 3).map (rotatePatch 5 (hexRegion 5)) = rows0_3_5.map Verdict.patch := by
  symm
  simp only [rows0_3_5, List.map_flatten, List.map_cons, List.map_nil, ← initial3_5_0]
  change ([source3_0].map (List.map (rotatePatch 5 (hexRegion 5)))).flatten = _
  rw [← List.map_flatten, source3_split]

end SpectreFinite.HexSearch.RadiusFivePruning
