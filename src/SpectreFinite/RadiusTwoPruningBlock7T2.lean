module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock7T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_2 : List (Verdict 6) := [
  .keep patch7_2_0,
  .keep patch7_2_1,
  .keep patch7_2_2,
  .keep patch7_2_3,
  .reject patch7_2_4 1,
  .keep patch7_2_5,
  .keep patch7_2_6,
  .keep patch7_2_7,
  .keep patch7_2_8,
  .keep patch7_2_9,
  .keep patch7_2_10,
  .keep patch7_2_11,
  .keep patch7_2_12,
  .keep patch7_2_13,
  .keep patch7_2_14,
  .keep patch7_2_15,
  .reject patch7_2_16 2,
  .reject patch7_2_17 2,
  .keep patch7_2_18,
  .keep patch7_2_19,
  .keep patch7_2_20,
  .keep patch7_2_21,
  .keep patch7_2_22,
  .keep patch7_2_23,
  .keep patch7_2_24,
  .keep patch7_2_25,
  .keep patch7_2_26,
  .keep patch7_2_27,
  .keep patch7_2_28,
  .keep patch7_2_29]
theorem check0_7_2 : checkRows direction samples trees0 rows0_7_2 = true := by decide
def rows1_7_2 : List (Verdict 6) := [
  .keep patch7_2_0,
  .keep patch7_2_1,
  .keep patch7_2_2,
  .keep patch7_2_3,
  .reject patch7_2_5 3,
  .keep patch7_2_6,
  .keep patch7_2_7,
  .keep patch7_2_8,
  .keep patch7_2_9,
  .keep patch7_2_10,
  .keep patch7_2_11,
  .keep patch7_2_12,
  .keep patch7_2_13,
  .keep patch7_2_14,
  .keep patch7_2_15,
  .keep patch7_2_18,
  .reject patch7_2_19 0,
  .reject patch7_2_20 3,
  .keep patch7_2_21,
  .keep patch7_2_22,
  .keep patch7_2_23,
  .keep patch7_2_24,
  .keep patch7_2_25,
  .keep patch7_2_26,
  .keep patch7_2_27,
  .keep patch7_2_28,
  .keep patch7_2_29]
theorem check1_7_2 : checkRows direction samples trees1 rows1_7_2 = true := by decide
theorem link1_7_2 : rows1_7_2.map Verdict.patch = rows0_7_2.filterMap Verdict.kept := by rfl
def rows2_7_2 : List (Verdict 6) := [
  .keep patch7_2_0,
  .keep patch7_2_1,
  .keep patch7_2_2,
  .keep patch7_2_3,
  .keep patch7_2_6,
  .keep patch7_2_7,
  .keep patch7_2_8,
  .keep patch7_2_9,
  .keep patch7_2_10,
  .keep patch7_2_11,
  .keep patch7_2_12,
  .keep patch7_2_13,
  .keep patch7_2_14,
  .keep patch7_2_15,
  .keep patch7_2_18,
  .keep patch7_2_21,
  .keep patch7_2_22,
  .keep patch7_2_23,
  .keep patch7_2_24,
  .keep patch7_2_25,
  .keep patch7_2_26,
  .keep patch7_2_27,
  .keep patch7_2_28,
  .keep patch7_2_29]
theorem check2_7_2 : checkRows direction samples trees2 rows2_7_2 = true := by decide
theorem link2_7_2 : rows2_7_2.map Verdict.patch = rows1_7_2.filterMap Verdict.kept := by rfl
theorem final_eq7_2 : final7_2 = rows2_7_2.filterMap Verdict.kept := by rfl
theorem initial7_2 : (RadiusTwo.familyForKind 7).map (rotatePatch 2 (hexRegion 2)) = rows0_7_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
