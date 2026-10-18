module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock7T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_1 : List (Verdict 6) := [
  .keep patch7_1_0,
  .keep patch7_1_1,
  .keep patch7_1_2,
  .keep patch7_1_3,
  .reject patch7_1_4 0,
  .keep patch7_1_5,
  .keep patch7_1_6,
  .keep patch7_1_7,
  .keep patch7_1_8,
  .keep patch7_1_9,
  .keep patch7_1_10,
  .keep patch7_1_11,
  .keep patch7_1_12,
  .keep patch7_1_13,
  .keep patch7_1_14,
  .keep patch7_1_15,
  .reject patch7_1_16 1,
  .reject patch7_1_17 1,
  .keep patch7_1_18,
  .keep patch7_1_19,
  .keep patch7_1_20,
  .keep patch7_1_21,
  .keep patch7_1_22,
  .keep patch7_1_23,
  .keep patch7_1_24,
  .keep patch7_1_25,
  .keep patch7_1_26,
  .keep patch7_1_27,
  .keep patch7_1_28,
  .keep patch7_1_29]
theorem check0_7_1 : checkRows direction samples trees0 rows0_7_1 = true := by decide
def rows1_7_1 : List (Verdict 6) := [
  .keep patch7_1_0,
  .keep patch7_1_1,
  .keep patch7_1_2,
  .keep patch7_1_3,
  .reject patch7_1_5 2,
  .keep patch7_1_6,
  .keep patch7_1_7,
  .keep patch7_1_8,
  .keep patch7_1_9,
  .keep patch7_1_10,
  .keep patch7_1_11,
  .keep patch7_1_12,
  .keep patch7_1_13,
  .keep patch7_1_14,
  .keep patch7_1_15,
  .keep patch7_1_18,
  .reject patch7_1_19 0,
  .reject patch7_1_20 2,
  .keep patch7_1_21,
  .keep patch7_1_22,
  .keep patch7_1_23,
  .keep patch7_1_24,
  .keep patch7_1_25,
  .keep patch7_1_26,
  .keep patch7_1_27,
  .keep patch7_1_28,
  .keep patch7_1_29]
theorem check1_7_1 : checkRows direction samples trees1 rows1_7_1 = true := by decide
theorem link1_7_1 : rows1_7_1.map Verdict.patch = rows0_7_1.filterMap Verdict.kept := by rfl
def rows2_7_1 : List (Verdict 6) := [
  .keep patch7_1_0,
  .keep patch7_1_1,
  .keep patch7_1_2,
  .keep patch7_1_3,
  .keep patch7_1_6,
  .keep patch7_1_7,
  .keep patch7_1_8,
  .keep patch7_1_9,
  .keep patch7_1_10,
  .keep patch7_1_11,
  .keep patch7_1_12,
  .keep patch7_1_13,
  .keep patch7_1_14,
  .keep patch7_1_15,
  .keep patch7_1_18,
  .keep patch7_1_21,
  .keep patch7_1_22,
  .keep patch7_1_23,
  .keep patch7_1_24,
  .keep patch7_1_25,
  .keep patch7_1_26,
  .keep patch7_1_27,
  .keep patch7_1_28,
  .keep patch7_1_29]
theorem check2_7_1 : checkRows direction samples trees2 rows2_7_1 = true := by decide
theorem link2_7_1 : rows2_7_1.map Verdict.patch = rows1_7_1.filterMap Verdict.kept := by rfl
theorem final_eq7_1 : final7_1 = rows2_7_1.filterMap Verdict.kept := by rfl
theorem initial7_1 : (RadiusTwo.familyForKind 7).map (rotatePatch 1 (hexRegion 2)) = rows0_7_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
