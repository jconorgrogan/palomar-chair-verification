module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock7T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_3 : List (Verdict 6) := [
  .keep patch7_3_0,
  .keep patch7_3_1,
  .keep patch7_3_2,
  .keep patch7_3_3,
  .reject patch7_3_4 2,
  .keep patch7_3_5,
  .keep patch7_3_6,
  .keep patch7_3_7,
  .keep patch7_3_8,
  .keep patch7_3_9,
  .keep patch7_3_10,
  .keep patch7_3_11,
  .keep patch7_3_12,
  .keep patch7_3_13,
  .keep patch7_3_14,
  .keep patch7_3_15,
  .reject patch7_3_16 3,
  .reject patch7_3_17 3,
  .keep patch7_3_18,
  .keep patch7_3_19,
  .keep patch7_3_20,
  .keep patch7_3_21,
  .keep patch7_3_22,
  .keep patch7_3_23,
  .keep patch7_3_24,
  .keep patch7_3_25,
  .keep patch7_3_26,
  .keep patch7_3_27,
  .keep patch7_3_28,
  .keep patch7_3_29]
theorem check0_7_3 : checkRows direction samples trees0 rows0_7_3 = true := by decide
def rows1_7_3 : List (Verdict 6) := [
  .keep patch7_3_0,
  .keep patch7_3_1,
  .keep patch7_3_2,
  .keep patch7_3_3,
  .reject patch7_3_5 4,
  .keep patch7_3_6,
  .keep patch7_3_7,
  .keep patch7_3_8,
  .keep patch7_3_9,
  .keep patch7_3_10,
  .keep patch7_3_11,
  .keep patch7_3_12,
  .keep patch7_3_13,
  .keep patch7_3_14,
  .keep patch7_3_15,
  .keep patch7_3_18,
  .reject patch7_3_19 1,
  .reject patch7_3_20 4,
  .keep patch7_3_21,
  .keep patch7_3_22,
  .keep patch7_3_23,
  .keep patch7_3_24,
  .keep patch7_3_25,
  .keep patch7_3_26,
  .keep patch7_3_27,
  .keep patch7_3_28,
  .keep patch7_3_29]
theorem check1_7_3 : checkRows direction samples trees1 rows1_7_3 = true := by decide
theorem link1_7_3 : rows1_7_3.map Verdict.patch = rows0_7_3.filterMap Verdict.kept := by rfl
def rows2_7_3 : List (Verdict 6) := [
  .keep patch7_3_0,
  .keep patch7_3_1,
  .keep patch7_3_2,
  .keep patch7_3_3,
  .keep patch7_3_6,
  .keep patch7_3_7,
  .keep patch7_3_8,
  .keep patch7_3_9,
  .keep patch7_3_10,
  .keep patch7_3_11,
  .keep patch7_3_12,
  .keep patch7_3_13,
  .keep patch7_3_14,
  .keep patch7_3_15,
  .keep patch7_3_18,
  .keep patch7_3_21,
  .keep patch7_3_22,
  .keep patch7_3_23,
  .keep patch7_3_24,
  .keep patch7_3_25,
  .keep patch7_3_26,
  .keep patch7_3_27,
  .keep patch7_3_28,
  .keep patch7_3_29]
theorem check2_7_3 : checkRows direction samples trees2 rows2_7_3 = true := by decide
theorem link2_7_3 : rows2_7_3.map Verdict.patch = rows1_7_3.filterMap Verdict.kept := by rfl
theorem final_eq7_3 : final7_3 = rows2_7_3.filterMap Verdict.kept := by rfl
theorem initial7_3 : (RadiusTwo.familyForKind 7).map (rotatePatch 3 (hexRegion 2)) = rows0_7_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
