module

public import SpectreFinite.RadiusFivePruningLiteral
public import SpectreFinite.RadiusFivePruningGroup0T0
public import SpectreFinite.RadiusFivePruningGroup0T1
public import SpectreFinite.RadiusFivePruningGroup0T2
public import SpectreFinite.RadiusFivePruningGroup0T3
public import SpectreFinite.RadiusFivePruningGroup0T4
public import SpectreFinite.RadiusFivePruningGroup0T5
public import SpectreFinite.RadiusFivePruningGroup1T0
public import SpectreFinite.RadiusFivePruningGroup1T1
public import SpectreFinite.RadiusFivePruningGroup1T2
public import SpectreFinite.RadiusFivePruningGroup1T3
public import SpectreFinite.RadiusFivePruningGroup1T4
public import SpectreFinite.RadiusFivePruningGroup1T5
public import SpectreFinite.RadiusFivePruningGroup2T0
public import SpectreFinite.RadiusFivePruningGroup2T1
public import SpectreFinite.RadiusFivePruningGroup2T2
public import SpectreFinite.RadiusFivePruningGroup2T3
public import SpectreFinite.RadiusFivePruningGroup2T4
public import SpectreFinite.RadiusFivePruningGroup2T5
public import SpectreFinite.RadiusFivePruningGroup3T0
public import SpectreFinite.RadiusFivePruningGroup3T1
public import SpectreFinite.RadiusFivePruningGroup3T2
public import SpectreFinite.RadiusFivePruningGroup3T3
public import SpectreFinite.RadiusFivePruningGroup3T4
public import SpectreFinite.RadiusFivePruningGroup3T5
public import SpectreFinite.RadiusFivePruningGroup4T0
public import SpectreFinite.RadiusFivePruningGroup4T1
public import SpectreFinite.RadiusFivePruningGroup4T2
public import SpectreFinite.RadiusFivePruningGroup4T3
public import SpectreFinite.RadiusFivePruningGroup4T4
public import SpectreFinite.RadiusFivePruningGroup4T5
public import SpectreFinite.RadiusFivePruningGroup5T0
public import SpectreFinite.RadiusFivePruningGroup5T1
public import SpectreFinite.RadiusFivePruningGroup5T2
public import SpectreFinite.RadiusFivePruningGroup5T3
public import SpectreFinite.RadiusFivePruningGroup5T4
public import SpectreFinite.RadiusFivePruningGroup5T5
public import SpectreFinite.RadiusFivePruningGroup6T0
public import SpectreFinite.RadiusFivePruningGroup6T1
public import SpectreFinite.RadiusFivePruningGroup6T2
public import SpectreFinite.RadiusFivePruningGroup6T3
public import SpectreFinite.RadiusFivePruningGroup6T4
public import SpectreFinite.RadiusFivePruningGroup6T5
public import SpectreFinite.RadiusFivePruningGroup7T0
public import SpectreFinite.RadiusFivePruningGroup7T1
public import SpectreFinite.RadiusFivePruningGroup7T2
public import SpectreFinite.RadiusFivePruningGroup7T3
public import SpectreFinite.RadiusFivePruningGroup7T4
public import SpectreFinite.RadiusFivePruningGroup7T5
public import SpectreFinite.RadiusFivePruningGroup8T0
public import SpectreFinite.RadiusFivePruningGroup8T1
public import SpectreFinite.RadiusFivePruningGroup8T2
public import SpectreFinite.RadiusFivePruningGroup8T3
public import SpectreFinite.RadiusFivePruningGroup8T4
public import SpectreFinite.RadiusFivePruningGroup8T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def chunks0 : List (List (Verdict 6)) := [rows0_0_0, rows0_0_1, rows0_0_2, rows0_0_3, rows0_0_4, rows0_0_5, rows0_1_0, rows0_1_1, rows0_1_2, rows0_1_3, rows0_1_4, rows0_1_5, rows0_2_0, rows0_2_1, rows0_2_2, rows0_2_3, rows0_2_4, rows0_2_5, rows0_3_0, rows0_3_1, rows0_3_2, rows0_3_3, rows0_3_4, rows0_3_5, rows0_4_0, rows0_4_1, rows0_4_2, rows0_4_3, rows0_4_4, rows0_4_5, rows0_5_0, rows0_5_1, rows0_5_2, rows0_5_3, rows0_5_4, rows0_5_5, rows0_6_0, rows0_6_1, rows0_6_2, rows0_6_3, rows0_6_4, rows0_6_5, rows0_7_0, rows0_7_1, rows0_7_2, rows0_7_3, rows0_7_4, rows0_7_5, rows0_8_0, rows0_8_1, rows0_8_2, rows0_8_3, rows0_8_4, rows0_8_5]
def rows0 : List (Verdict 6) := chunks0.flatten
theorem checked0 : checkRows direction samples0 trees0 rows0 = true := by
  apply checkRows_flatten
  simp only [chunks0, List.all_cons, List.all_nil, check0_0_0, check0_0_1, check0_0_2, check0_0_3, check0_0_4, check0_0_5, check0_1_0, check0_1_1, check0_1_2, check0_1_3, check0_1_4, check0_1_5, check0_2_0, check0_2_1, check0_2_2, check0_2_3, check0_2_4, check0_2_5, check0_3_0, check0_3_1, check0_3_2, check0_3_3, check0_3_4, check0_3_5, check0_4_0, check0_4_1, check0_4_2, check0_4_3, check0_4_4, check0_4_5, check0_5_0, check0_5_1, check0_5_2, check0_5_3, check0_5_4, check0_5_5, check0_6_0, check0_6_1, check0_6_2, check0_6_3, check0_6_4, check0_6_5, check0_7_0, check0_7_1, check0_7_2, check0_7_3, check0_7_4, check0_7_5, check0_8_0, check0_8_1, check0_8_2, check0_8_3, check0_8_4, check0_8_5, Bool.true_and]
def chunks1 : List (List (Verdict 6)) := [rows1_0_0, rows1_0_1, rows1_0_2, rows1_0_3, rows1_0_4, rows1_0_5, rows1_1_0, rows1_1_1, rows1_1_2, rows1_1_3, rows1_1_4, rows1_1_5, rows1_2_0, rows1_2_1, rows1_2_2, rows1_2_3, rows1_2_4, rows1_2_5, rows1_3_0, rows1_3_1, rows1_3_2, rows1_3_3, rows1_3_4, rows1_3_5, rows1_4_0, rows1_4_1, rows1_4_2, rows1_4_3, rows1_4_4, rows1_4_5, rows1_5_0, rows1_5_1, rows1_5_2, rows1_5_3, rows1_5_4, rows1_5_5, rows1_6_0, rows1_6_1, rows1_6_2, rows1_6_3, rows1_6_4, rows1_6_5, rows1_7_0, rows1_7_1, rows1_7_2, rows1_7_3, rows1_7_4, rows1_7_5, rows1_8_0, rows1_8_1, rows1_8_2, rows1_8_3, rows1_8_4, rows1_8_5]
def rows1 : List (Verdict 6) := chunks1.flatten
theorem checked1 : checkRows direction samples1 trees1 rows1 = true := by
  apply checkRows_flatten
  simp only [chunks1, List.all_cons, List.all_nil, check1_0_0, check1_0_1, check1_0_2, check1_0_3, check1_0_4, check1_0_5, check1_1_0, check1_1_1, check1_1_2, check1_1_3, check1_1_4, check1_1_5, check1_2_0, check1_2_1, check1_2_2, check1_2_3, check1_2_4, check1_2_5, check1_3_0, check1_3_1, check1_3_2, check1_3_3, check1_3_4, check1_3_5, check1_4_0, check1_4_1, check1_4_2, check1_4_3, check1_4_4, check1_4_5, check1_5_0, check1_5_1, check1_5_2, check1_5_3, check1_5_4, check1_5_5, check1_6_0, check1_6_1, check1_6_2, check1_6_3, check1_6_4, check1_6_5, check1_7_0, check1_7_1, check1_7_2, check1_7_3, check1_7_4, check1_7_5, check1_8_0, check1_8_1, check1_8_2, check1_8_3, check1_8_4, check1_8_5, Bool.true_and]
theorem link1 : rows1.map Verdict.patch = rows0.filterMap Verdict.kept := by
  simp only [rows1, rows0, List.map_flatten, List.filterMap_flatten, chunks1, chunks0, List.map_cons, List.map_nil, link1_0_0, link1_0_1, link1_0_2, link1_0_3, link1_0_4, link1_0_5, link1_1_0, link1_1_1, link1_1_2, link1_1_3, link1_1_4, link1_1_5, link1_2_0, link1_2_1, link1_2_2, link1_2_3, link1_2_4, link1_2_5, link1_3_0, link1_3_1, link1_3_2, link1_3_3, link1_3_4, link1_3_5, link1_4_0, link1_4_1, link1_4_2, link1_4_3, link1_4_4, link1_4_5, link1_5_0, link1_5_1, link1_5_2, link1_5_3, link1_5_4, link1_5_5, link1_6_0, link1_6_1, link1_6_2, link1_6_3, link1_6_4, link1_6_5, link1_7_0, link1_7_1, link1_7_2, link1_7_3, link1_7_4, link1_7_5, link1_8_0, link1_8_1, link1_8_2, link1_8_3, link1_8_4, link1_8_5]
def chunks2 : List (List (Verdict 6)) := [rows2_0_0, rows2_0_1, rows2_0_2, rows2_0_3, rows2_0_4, rows2_0_5, rows2_1_0, rows2_1_1, rows2_1_2, rows2_1_3, rows2_1_4, rows2_1_5, rows2_2_0, rows2_2_1, rows2_2_2, rows2_2_3, rows2_2_4, rows2_2_5, rows2_3_0, rows2_3_1, rows2_3_2, rows2_3_3, rows2_3_4, rows2_3_5, rows2_4_0, rows2_4_1, rows2_4_2, rows2_4_3, rows2_4_4, rows2_4_5, rows2_5_0, rows2_5_1, rows2_5_2, rows2_5_3, rows2_5_4, rows2_5_5, rows2_6_0, rows2_6_1, rows2_6_2, rows2_6_3, rows2_6_4, rows2_6_5, rows2_7_0, rows2_7_1, rows2_7_2, rows2_7_3, rows2_7_4, rows2_7_5, rows2_8_0, rows2_8_1, rows2_8_2, rows2_8_3, rows2_8_4, rows2_8_5]
def rows2 : List (Verdict 6) := chunks2.flatten
theorem checked2 : checkRows direction samples2 trees2 rows2 = true := by
  apply checkRows_flatten
  simp only [chunks2, List.all_cons, List.all_nil, check2_0_0, check2_0_1, check2_0_2, check2_0_3, check2_0_4, check2_0_5, check2_1_0, check2_1_1, check2_1_2, check2_1_3, check2_1_4, check2_1_5, check2_2_0, check2_2_1, check2_2_2, check2_2_3, check2_2_4, check2_2_5, check2_3_0, check2_3_1, check2_3_2, check2_3_3, check2_3_4, check2_3_5, check2_4_0, check2_4_1, check2_4_2, check2_4_3, check2_4_4, check2_4_5, check2_5_0, check2_5_1, check2_5_2, check2_5_3, check2_5_4, check2_5_5, check2_6_0, check2_6_1, check2_6_2, check2_6_3, check2_6_4, check2_6_5, check2_7_0, check2_7_1, check2_7_2, check2_7_3, check2_7_4, check2_7_5, check2_8_0, check2_8_1, check2_8_2, check2_8_3, check2_8_4, check2_8_5, Bool.true_and]
theorem link2 : rows2.map Verdict.patch = rows1.filterMap Verdict.kept := by
  simp only [rows2, rows1, List.map_flatten, List.filterMap_flatten, chunks2, chunks1, List.map_cons, List.map_nil, link2_0_0, link2_0_1, link2_0_2, link2_0_3, link2_0_4, link2_0_5, link2_1_0, link2_1_1, link2_1_2, link2_1_3, link2_1_4, link2_1_5, link2_2_0, link2_2_1, link2_2_2, link2_2_3, link2_2_4, link2_2_5, link2_3_0, link2_3_1, link2_3_2, link2_3_3, link2_3_4, link2_3_5, link2_4_0, link2_4_1, link2_4_2, link2_4_3, link2_4_4, link2_4_5, link2_5_0, link2_5_1, link2_5_2, link2_5_3, link2_5_4, link2_5_5, link2_6_0, link2_6_1, link2_6_2, link2_6_3, link2_6_4, link2_6_5, link2_7_0, link2_7_1, link2_7_2, link2_7_3, link2_7_4, link2_7_5, link2_8_0, link2_8_1, link2_8_2, link2_8_3, link2_8_4, link2_8_5]
def chunks3 : List (List (Verdict 6)) := [rows3_0_0, rows3_0_1, rows3_0_2, rows3_0_3, rows3_0_4, rows3_0_5, rows3_1_0, rows3_1_1, rows3_1_2, rows3_1_3, rows3_1_4, rows3_1_5, rows3_2_0, rows3_2_1, rows3_2_2, rows3_2_3, rows3_2_4, rows3_2_5, rows3_3_0, rows3_3_1, rows3_3_2, rows3_3_3, rows3_3_4, rows3_3_5, rows3_4_0, rows3_4_1, rows3_4_2, rows3_4_3, rows3_4_4, rows3_4_5, rows3_5_0, rows3_5_1, rows3_5_2, rows3_5_3, rows3_5_4, rows3_5_5, rows3_6_0, rows3_6_1, rows3_6_2, rows3_6_3, rows3_6_4, rows3_6_5, rows3_7_0, rows3_7_1, rows3_7_2, rows3_7_3, rows3_7_4, rows3_7_5, rows3_8_0, rows3_8_1, rows3_8_2, rows3_8_3, rows3_8_4, rows3_8_5]
def rows3 : List (Verdict 6) := chunks3.flatten
theorem checked3 : checkRows direction samples3 trees3 rows3 = true := by
  apply checkRows_flatten
  simp only [chunks3, List.all_cons, List.all_nil, check3_0_0, check3_0_1, check3_0_2, check3_0_3, check3_0_4, check3_0_5, check3_1_0, check3_1_1, check3_1_2, check3_1_3, check3_1_4, check3_1_5, check3_2_0, check3_2_1, check3_2_2, check3_2_3, check3_2_4, check3_2_5, check3_3_0, check3_3_1, check3_3_2, check3_3_3, check3_3_4, check3_3_5, check3_4_0, check3_4_1, check3_4_2, check3_4_3, check3_4_4, check3_4_5, check3_5_0, check3_5_1, check3_5_2, check3_5_3, check3_5_4, check3_5_5, check3_6_0, check3_6_1, check3_6_2, check3_6_3, check3_6_4, check3_6_5, check3_7_0, check3_7_1, check3_7_2, check3_7_3, check3_7_4, check3_7_5, check3_8_0, check3_8_1, check3_8_2, check3_8_3, check3_8_4, check3_8_5, Bool.true_and]
theorem link3 : rows3.map Verdict.patch = rows2.filterMap Verdict.kept := by
  simp only [rows3, rows2, List.map_flatten, List.filterMap_flatten, chunks3, chunks2, List.map_cons, List.map_nil, link3_0_0, link3_0_1, link3_0_2, link3_0_3, link3_0_4, link3_0_5, link3_1_0, link3_1_1, link3_1_2, link3_1_3, link3_1_4, link3_1_5, link3_2_0, link3_2_1, link3_2_2, link3_2_3, link3_2_4, link3_2_5, link3_3_0, link3_3_1, link3_3_2, link3_3_3, link3_3_4, link3_3_5, link3_4_0, link3_4_1, link3_4_2, link3_4_3, link3_4_4, link3_4_5, link3_5_0, link3_5_1, link3_5_2, link3_5_3, link3_5_4, link3_5_5, link3_6_0, link3_6_1, link3_6_2, link3_6_3, link3_6_4, link3_6_5, link3_7_0, link3_7_1, link3_7_2, link3_7_3, link3_7_4, link3_7_5, link3_8_0, link3_8_1, link3_8_2, link3_8_3, link3_8_4, link3_8_5]
def chunks4 : List (List (Verdict 6)) := [rows4_0_0, rows4_0_1, rows4_0_2, rows4_0_3, rows4_0_4, rows4_0_5, rows4_1_0, rows4_1_1, rows4_1_2, rows4_1_3, rows4_1_4, rows4_1_5, rows4_2_0, rows4_2_1, rows4_2_2, rows4_2_3, rows4_2_4, rows4_2_5, rows4_3_0, rows4_3_1, rows4_3_2, rows4_3_3, rows4_3_4, rows4_3_5, rows4_4_0, rows4_4_1, rows4_4_2, rows4_4_3, rows4_4_4, rows4_4_5, rows4_5_0, rows4_5_1, rows4_5_2, rows4_5_3, rows4_5_4, rows4_5_5, rows4_6_0, rows4_6_1, rows4_6_2, rows4_6_3, rows4_6_4, rows4_6_5, rows4_7_0, rows4_7_1, rows4_7_2, rows4_7_3, rows4_7_4, rows4_7_5, rows4_8_0, rows4_8_1, rows4_8_2, rows4_8_3, rows4_8_4, rows4_8_5]
def rows4 : List (Verdict 6) := chunks4.flatten
theorem checked4 : checkRows direction samples4 trees4 rows4 = true := by
  apply checkRows_flatten
  simp only [chunks4, List.all_cons, List.all_nil, check4_0_0, check4_0_1, check4_0_2, check4_0_3, check4_0_4, check4_0_5, check4_1_0, check4_1_1, check4_1_2, check4_1_3, check4_1_4, check4_1_5, check4_2_0, check4_2_1, check4_2_2, check4_2_3, check4_2_4, check4_2_5, check4_3_0, check4_3_1, check4_3_2, check4_3_3, check4_3_4, check4_3_5, check4_4_0, check4_4_1, check4_4_2, check4_4_3, check4_4_4, check4_4_5, check4_5_0, check4_5_1, check4_5_2, check4_5_3, check4_5_4, check4_5_5, check4_6_0, check4_6_1, check4_6_2, check4_6_3, check4_6_4, check4_6_5, check4_7_0, check4_7_1, check4_7_2, check4_7_3, check4_7_4, check4_7_5, check4_8_0, check4_8_1, check4_8_2, check4_8_3, check4_8_4, check4_8_5, Bool.true_and]
theorem link4 : rows4.map Verdict.patch = rows3.filterMap Verdict.kept := by
  simp only [rows4, rows3, List.map_flatten, List.filterMap_flatten, chunks4, chunks3, List.map_cons, List.map_nil, link4_0_0, link4_0_1, link4_0_2, link4_0_3, link4_0_4, link4_0_5, link4_1_0, link4_1_1, link4_1_2, link4_1_3, link4_1_4, link4_1_5, link4_2_0, link4_2_1, link4_2_2, link4_2_3, link4_2_4, link4_2_5, link4_3_0, link4_3_1, link4_3_2, link4_3_3, link4_3_4, link4_3_5, link4_4_0, link4_4_1, link4_4_2, link4_4_3, link4_4_4, link4_4_5, link4_5_0, link4_5_1, link4_5_2, link4_5_3, link4_5_4, link4_5_5, link4_6_0, link4_6_1, link4_6_2, link4_6_3, link4_6_4, link4_6_5, link4_7_0, link4_7_1, link4_7_2, link4_7_3, link4_7_4, link4_7_5, link4_8_0, link4_8_1, link4_8_2, link4_8_3, link4_8_4, link4_8_5]
def chunks5 : List (List (Verdict 6)) := [rows5_0_0, rows5_0_1, rows5_0_2, rows5_0_3, rows5_0_4, rows5_0_5, rows5_1_0, rows5_1_1, rows5_1_2, rows5_1_3, rows5_1_4, rows5_1_5, rows5_2_0, rows5_2_1, rows5_2_2, rows5_2_3, rows5_2_4, rows5_2_5, rows5_3_0, rows5_3_1, rows5_3_2, rows5_3_3, rows5_3_4, rows5_3_5, rows5_4_0, rows5_4_1, rows5_4_2, rows5_4_3, rows5_4_4, rows5_4_5, rows5_5_0, rows5_5_1, rows5_5_2, rows5_5_3, rows5_5_4, rows5_5_5, rows5_6_0, rows5_6_1, rows5_6_2, rows5_6_3, rows5_6_4, rows5_6_5, rows5_7_0, rows5_7_1, rows5_7_2, rows5_7_3, rows5_7_4, rows5_7_5, rows5_8_0, rows5_8_1, rows5_8_2, rows5_8_3, rows5_8_4, rows5_8_5]
def rows5 : List (Verdict 6) := chunks5.flatten
theorem checked5 : checkRows direction samples5 trees5 rows5 = true := by
  apply checkRows_flatten
  simp only [chunks5, List.all_cons, List.all_nil, check5_0_0, check5_0_1, check5_0_2, check5_0_3, check5_0_4, check5_0_5, check5_1_0, check5_1_1, check5_1_2, check5_1_3, check5_1_4, check5_1_5, check5_2_0, check5_2_1, check5_2_2, check5_2_3, check5_2_4, check5_2_5, check5_3_0, check5_3_1, check5_3_2, check5_3_3, check5_3_4, check5_3_5, check5_4_0, check5_4_1, check5_4_2, check5_4_3, check5_4_4, check5_4_5, check5_5_0, check5_5_1, check5_5_2, check5_5_3, check5_5_4, check5_5_5, check5_6_0, check5_6_1, check5_6_2, check5_6_3, check5_6_4, check5_6_5, check5_7_0, check5_7_1, check5_7_2, check5_7_3, check5_7_4, check5_7_5, check5_8_0, check5_8_1, check5_8_2, check5_8_3, check5_8_4, check5_8_5, Bool.true_and]
theorem link5 : rows5.map Verdict.patch = rows4.filterMap Verdict.kept := by
  simp only [rows5, rows4, List.map_flatten, List.filterMap_flatten, chunks5, chunks4, List.map_cons, List.map_nil, link5_0_0, link5_0_1, link5_0_2, link5_0_3, link5_0_4, link5_0_5, link5_1_0, link5_1_1, link5_1_2, link5_1_3, link5_1_4, link5_1_5, link5_2_0, link5_2_1, link5_2_2, link5_2_3, link5_2_4, link5_2_5, link5_3_0, link5_3_1, link5_3_2, link5_3_3, link5_3_4, link5_3_5, link5_4_0, link5_4_1, link5_4_2, link5_4_3, link5_4_4, link5_4_5, link5_5_0, link5_5_1, link5_5_2, link5_5_3, link5_5_4, link5_5_5, link5_6_0, link5_6_1, link5_6_2, link5_6_3, link5_6_4, link5_6_5, link5_7_0, link5_7_1, link5_7_2, link5_7_3, link5_7_4, link5_7_5, link5_8_0, link5_8_1, link5_8_2, link5_8_3, link5_8_4, link5_8_5]
def chunks6 : List (List (Verdict 6)) := [rows6_0_0, rows6_0_1, rows6_0_2, rows6_0_3, rows6_0_4, rows6_0_5, rows6_1_0, rows6_1_1, rows6_1_2, rows6_1_3, rows6_1_4, rows6_1_5, rows6_2_0, rows6_2_1, rows6_2_2, rows6_2_3, rows6_2_4, rows6_2_5, rows6_3_0, rows6_3_1, rows6_3_2, rows6_3_3, rows6_3_4, rows6_3_5, rows6_4_0, rows6_4_1, rows6_4_2, rows6_4_3, rows6_4_4, rows6_4_5, rows6_5_0, rows6_5_1, rows6_5_2, rows6_5_3, rows6_5_4, rows6_5_5, rows6_6_0, rows6_6_1, rows6_6_2, rows6_6_3, rows6_6_4, rows6_6_5, rows6_7_0, rows6_7_1, rows6_7_2, rows6_7_3, rows6_7_4, rows6_7_5, rows6_8_0, rows6_8_1, rows6_8_2, rows6_8_3, rows6_8_4, rows6_8_5]
def rows6 : List (Verdict 6) := chunks6.flatten
theorem checked6 : checkRows direction samples6 trees6 rows6 = true := by
  apply checkRows_flatten
  simp only [chunks6, List.all_cons, List.all_nil, check6_0_0, check6_0_1, check6_0_2, check6_0_3, check6_0_4, check6_0_5, check6_1_0, check6_1_1, check6_1_2, check6_1_3, check6_1_4, check6_1_5, check6_2_0, check6_2_1, check6_2_2, check6_2_3, check6_2_4, check6_2_5, check6_3_0, check6_3_1, check6_3_2, check6_3_3, check6_3_4, check6_3_5, check6_4_0, check6_4_1, check6_4_2, check6_4_3, check6_4_4, check6_4_5, check6_5_0, check6_5_1, check6_5_2, check6_5_3, check6_5_4, check6_5_5, check6_6_0, check6_6_1, check6_6_2, check6_6_3, check6_6_4, check6_6_5, check6_7_0, check6_7_1, check6_7_2, check6_7_3, check6_7_4, check6_7_5, check6_8_0, check6_8_1, check6_8_2, check6_8_3, check6_8_4, check6_8_5, Bool.true_and]
theorem link6 : rows6.map Verdict.patch = rows5.filterMap Verdict.kept := by
  simp only [rows6, rows5, List.map_flatten, List.filterMap_flatten, chunks6, chunks5, List.map_cons, List.map_nil, link6_0_0, link6_0_1, link6_0_2, link6_0_3, link6_0_4, link6_0_5, link6_1_0, link6_1_1, link6_1_2, link6_1_3, link6_1_4, link6_1_5, link6_2_0, link6_2_1, link6_2_2, link6_2_3, link6_2_4, link6_2_5, link6_3_0, link6_3_1, link6_3_2, link6_3_3, link6_3_4, link6_3_5, link6_4_0, link6_4_1, link6_4_2, link6_4_3, link6_4_4, link6_4_5, link6_5_0, link6_5_1, link6_5_2, link6_5_3, link6_5_4, link6_5_5, link6_6_0, link6_6_1, link6_6_2, link6_6_3, link6_6_4, link6_6_5, link6_7_0, link6_7_1, link6_7_2, link6_7_3, link6_7_4, link6_7_5, link6_8_0, link6_8_1, link6_8_2, link6_8_3, link6_8_4, link6_8_5]
theorem initial : rows0.map Verdict.patch = RadiusFive.allTurnFamily := by
  simp only [rows0, List.map_flatten, chunks0, List.map_cons, List.map_nil, ← initial0_0, ← initial0_1, ← initial0_2, ← initial0_3, ← initial0_4, ← initial0_5, ← initial1_0, ← initial1_1, ← initial1_2, ← initial1_3, ← initial1_4, ← initial1_5, ← initial2_0, ← initial2_1, ← initial2_2, ← initial2_3, ← initial2_4, ← initial2_5, ← initial3_0, ← initial3_1, ← initial3_2, ← initial3_3, ← initial3_4, ← initial3_5, ← initial4_0, ← initial4_1, ← initial4_2, ← initial4_3, ← initial4_4, ← initial4_5, ← initial5_0, ← initial5_1, ← initial5_2, ← initial5_3, ← initial5_4, ← initial5_5, ← initial6_0, ← initial6_1, ← initial6_2, ← initial6_3, ← initial6_4, ← initial6_5, ← initial7_0, ← initial7_1, ← initial7_2, ← initial7_3, ← initial7_4, ← initial7_5, ← initial8_0, ← initial8_1, ← initial8_2, ← initial8_3, ← initial8_4, ← initial8_5]
  rfl
theorem certifiedFamily_eq : certifiedFamily = rows6.filterMap Verdict.kept := by
  simp only [certifiedFamily, finalChunks, rows6, chunks6, rows6_0_0, final0_0, rows6_0_1, final0_1, rows6_0_2, final0_2, rows6_0_3, final0_3, rows6_0_4, final0_4, rows6_0_5, final0_5, rows6_1_0, final1_0, rows6_1_1, final1_1, rows6_1_2, final1_2, rows6_1_3, final1_3, rows6_1_4, final1_4, rows6_1_5, final1_5, rows6_2_0, final2_0, rows6_2_1, final2_1, rows6_2_2, final2_2, rows6_2_3, final2_3, rows6_2_4, final2_4, rows6_2_5, final2_5, rows6_3_0, final3_0, rows6_3_1, final3_1, rows6_3_2, final3_2, rows6_3_3, final3_3, rows6_3_4, final3_4, rows6_3_5, final3_5, rows6_4_0, final4_0, rows6_4_1, final4_1, rows6_4_2, final4_2, rows6_4_3, final4_3, rows6_4_4, final4_4, rows6_4_5, final4_5, rows6_5_0, final5_0, rows6_5_1, final5_1, rows6_5_2, final5_2, rows6_5_3, final5_3, rows6_5_4, final5_4, rows6_5_5, final5_5, rows6_6_0, final6_0, rows6_6_1, final6_1, rows6_6_2, final6_2, rows6_6_3, final6_3, rows6_6_4, final6_4, rows6_6_5, final6_5, rows6_7_0, final7_0, rows6_7_1, final7_1, rows6_7_2, final7_2, rows6_7_3, final7_3, rows6_7_4, final7_4, rows6_7_5, final7_5, rows6_8_0, final8_0, rows6_8_1, final8_1, rows6_8_2, final8_2, rows6_8_3, final8_3, rows6_8_4, final8_4, rows6_8_5, final8_5, List.filterMap_flatten, List.map_cons, List.map_nil, final_eq0_0_0, final_eq0_0_1, final_eq0_0_2, final_eq0_0_3, final_eq0_0_4, final_eq0_1_0, final_eq0_1_1, final_eq0_1_2, final_eq0_1_3, final_eq0_1_4, final_eq0_2_0, final_eq0_2_1, final_eq0_2_2, final_eq0_2_3, final_eq0_2_4, final_eq0_3_0, final_eq0_3_1, final_eq0_3_2, final_eq0_3_3, final_eq0_3_4, final_eq0_4_0, final_eq0_4_1, final_eq0_4_2, final_eq0_4_3, final_eq0_4_4, final_eq0_5_0, final_eq0_5_1, final_eq0_5_2, final_eq0_5_3, final_eq0_5_4, final_eq1_0_0, final_eq1_0_1, final_eq1_0_2, final_eq1_0_3, final_eq1_0_4, final_eq1_1_0, final_eq1_1_1, final_eq1_1_2, final_eq1_1_3, final_eq1_1_4, final_eq1_2_0, final_eq1_2_1, final_eq1_2_2, final_eq1_2_3, final_eq1_2_4, final_eq1_3_0, final_eq1_3_1, final_eq1_3_2, final_eq1_3_3, final_eq1_3_4, final_eq1_4_0, final_eq1_4_1, final_eq1_4_2, final_eq1_4_3, final_eq1_4_4, final_eq1_5_0, final_eq1_5_1, final_eq1_5_2, final_eq1_5_3, final_eq1_5_4, final_eq2_0_0, final_eq2_1_0, final_eq2_2_0, final_eq2_3_0, final_eq2_4_0, final_eq2_5_0, final_eq3_0_0, final_eq3_1_0, final_eq3_2_0, final_eq3_3_0, final_eq3_4_0, final_eq3_5_0, final_eq4_0_0, final_eq4_0_1, final_eq4_0_2, final_eq4_0_3, final_eq4_1_0, final_eq4_1_1, final_eq4_1_2, final_eq4_1_3, final_eq4_2_0, final_eq4_2_1, final_eq4_2_2, final_eq4_2_3, final_eq4_3_0, final_eq4_3_1, final_eq4_3_2, final_eq4_3_3, final_eq4_4_0, final_eq4_4_1, final_eq4_4_2, final_eq4_4_3, final_eq4_5_0, final_eq4_5_1, final_eq4_5_2, final_eq4_5_3, final_eq5_0_0, final_eq5_0_1, final_eq5_0_2, final_eq5_1_0, final_eq5_1_1, final_eq5_1_2, final_eq5_2_0, final_eq5_2_1, final_eq5_2_2, final_eq5_3_0, final_eq5_3_1, final_eq5_3_2, final_eq5_4_0, final_eq5_4_1, final_eq5_4_2, final_eq5_5_0, final_eq5_5_1, final_eq5_5_2, final_eq6_0_0, final_eq6_0_1, final_eq6_0_2, final_eq6_0_3, final_eq6_0_4, final_eq6_0_5, final_eq6_1_0, final_eq6_1_1, final_eq6_1_2, final_eq6_1_3, final_eq6_1_4, final_eq6_1_5, final_eq6_2_0, final_eq6_2_1, final_eq6_2_2, final_eq6_2_3, final_eq6_2_4, final_eq6_2_5, final_eq6_3_0, final_eq6_3_1, final_eq6_3_2, final_eq6_3_3, final_eq6_3_4, final_eq6_3_5, final_eq6_4_0, final_eq6_4_1, final_eq6_4_2, final_eq6_4_3, final_eq6_4_4, final_eq6_4_5, final_eq6_5_0, final_eq6_5_1, final_eq6_5_2, final_eq6_5_3, final_eq6_5_4, final_eq6_5_5, final_eq7_0_0, final_eq7_0_1, final_eq7_0_2, final_eq7_0_3, final_eq7_0_4, final_eq7_0_5, final_eq7_0_6, final_eq7_0_7, final_eq7_0_8, final_eq7_1_0, final_eq7_1_1, final_eq7_1_2, final_eq7_1_3, final_eq7_1_4, final_eq7_1_5, final_eq7_1_6, final_eq7_1_7, final_eq7_1_8, final_eq7_2_0, final_eq7_2_1, final_eq7_2_2, final_eq7_2_3, final_eq7_2_4, final_eq7_2_5, final_eq7_2_6, final_eq7_2_7, final_eq7_2_8, final_eq7_3_0, final_eq7_3_1, final_eq7_3_2, final_eq7_3_3, final_eq7_3_4, final_eq7_3_5, final_eq7_3_6, final_eq7_3_7, final_eq7_3_8, final_eq7_4_0, final_eq7_4_1, final_eq7_4_2, final_eq7_4_3, final_eq7_4_4, final_eq7_4_5, final_eq7_4_6, final_eq7_4_7, final_eq7_4_8, final_eq7_5_0, final_eq7_5_1, final_eq7_5_2, final_eq7_5_3, final_eq7_5_4, final_eq7_5_5, final_eq7_5_6, final_eq7_5_7, final_eq7_5_8, final_eq8_0_0, final_eq8_0_1, final_eq8_0_2, final_eq8_0_3, final_eq8_0_4, final_eq8_0_5, final_eq8_1_0, final_eq8_1_1, final_eq8_1_2, final_eq8_1_3, final_eq8_1_4, final_eq8_1_5, final_eq8_2_0, final_eq8_2_1, final_eq8_2_2, final_eq8_2_3, final_eq8_2_4, final_eq8_2_5, final_eq8_3_0, final_eq8_3_1, final_eq8_3_2, final_eq8_3_3, final_eq8_3_4, final_eq8_3_5, final_eq8_4_0, final_eq8_4_1, final_eq8_4_2, final_eq8_4_3, final_eq8_4_4, final_eq8_4_5, final_eq8_5_0, final_eq8_5_1, final_eq8_5_2, final_eq8_5_3, final_eq8_5_4, final_eq8_5_5]
theorem round_counts : [rows0.length, rows1.length, rows2.length, rows3.length, rows4.length, rows5.length, rows6.length, certifiedFamily.length] = [2724, 2682, 2616, 2520, 2364, 2244, 2172, 2112] := by decide
theorem rounds_occurrenceComplete (f : Position → State) (hf : OccurrenceComplete f (hexRegion 5) RadiusFive.allTurnFamily) : OccurrenceComplete f (hexRegion 5) certifiedFamily := by
  have h0 : OccurrenceComplete f (hexRegion 5) (rows0.map Verdict.patch) := by
    rw [initial]
    exact hf
  have h1 := certified_round (hexRegion 5) direction samples0 samples0_shared trees0 rows0 checked0 f h0
  have h2 : OccurrenceComplete f (hexRegion 5) (rows1.map Verdict.patch) := by
    rw [link1]
    exact h1
  have h3 := certified_round (hexRegion 5) direction samples1 samples1_shared trees1 rows1 checked1 f h2
  have h4 : OccurrenceComplete f (hexRegion 5) (rows2.map Verdict.patch) := by
    rw [link2]
    exact h3
  have h5 := certified_round (hexRegion 5) direction samples2 samples2_shared trees2 rows2 checked2 f h4
  have h6 : OccurrenceComplete f (hexRegion 5) (rows3.map Verdict.patch) := by
    rw [link3]
    exact h5
  have h7 := certified_round (hexRegion 5) direction samples3 samples3_shared trees3 rows3 checked3 f h6
  have h8 : OccurrenceComplete f (hexRegion 5) (rows4.map Verdict.patch) := by
    rw [link4]
    exact h7
  have h9 := certified_round (hexRegion 5) direction samples4 samples4_shared trees4 rows4 checked4 f h8
  have h10 : OccurrenceComplete f (hexRegion 5) (rows5.map Verdict.patch) := by
    rw [link5]
    exact h9
  have h11 := certified_round (hexRegion 5) direction samples5 samples5_shared trees5 rows5 checked5 f h10
  have h12 : OccurrenceComplete f (hexRegion 5) (rows6.map Verdict.patch) := by
    rw [link6]
    exact h11
  have h13 := certified_round (hexRegion 5) direction samples6 samples6_shared trees6 rows6 checked6 f h12
  rw [certifiedFamily_eq]
  exact h13
#print axioms rounds_occurrenceComplete

end SpectreFinite.HexSearch.RadiusFivePruning
