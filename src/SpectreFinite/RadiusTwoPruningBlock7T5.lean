module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock7T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_5 : List (Verdict 6) := [
  .keep patch7_5_0,
  .keep patch7_5_1,
  .keep patch7_5_2,
  .keep patch7_5_3,
  .reject patch7_5_4 4,
  .keep patch7_5_5,
  .keep patch7_5_6,
  .keep patch7_5_7,
  .keep patch7_5_8,
  .keep patch7_5_9,
  .keep patch7_5_10,
  .keep patch7_5_11,
  .keep patch7_5_12,
  .keep patch7_5_13,
  .keep patch7_5_14,
  .keep patch7_5_15,
  .reject patch7_5_16 5,
  .reject patch7_5_17 5,
  .keep patch7_5_18,
  .keep patch7_5_19,
  .keep patch7_5_20,
  .keep patch7_5_21,
  .keep patch7_5_22,
  .keep patch7_5_23,
  .keep patch7_5_24,
  .keep patch7_5_25,
  .keep patch7_5_26,
  .keep patch7_5_27,
  .keep patch7_5_28,
  .keep patch7_5_29]
theorem check0_7_5 : checkRows direction samples trees0 rows0_7_5 = true := by decide
def rows1_7_5 : List (Verdict 6) := [
  .keep patch7_5_0,
  .keep patch7_5_1,
  .keep patch7_5_2,
  .keep patch7_5_3,
  .reject patch7_5_5 0,
  .keep patch7_5_6,
  .keep patch7_5_7,
  .keep patch7_5_8,
  .keep patch7_5_9,
  .keep patch7_5_10,
  .keep patch7_5_11,
  .keep patch7_5_12,
  .keep patch7_5_13,
  .keep patch7_5_14,
  .keep patch7_5_15,
  .keep patch7_5_18,
  .reject patch7_5_19 3,
  .reject patch7_5_20 0,
  .keep patch7_5_21,
  .keep patch7_5_22,
  .keep patch7_5_23,
  .keep patch7_5_24,
  .keep patch7_5_25,
  .keep patch7_5_26,
  .keep patch7_5_27,
  .keep patch7_5_28,
  .keep patch7_5_29]
theorem check1_7_5 : checkRows direction samples trees1 rows1_7_5 = true := by decide
theorem link1_7_5 : rows1_7_5.map Verdict.patch = rows0_7_5.filterMap Verdict.kept := by rfl
def rows2_7_5 : List (Verdict 6) := [
  .keep patch7_5_0,
  .keep patch7_5_1,
  .keep patch7_5_2,
  .keep patch7_5_3,
  .keep patch7_5_6,
  .keep patch7_5_7,
  .keep patch7_5_8,
  .keep patch7_5_9,
  .keep patch7_5_10,
  .keep patch7_5_11,
  .keep patch7_5_12,
  .keep patch7_5_13,
  .keep patch7_5_14,
  .keep patch7_5_15,
  .keep patch7_5_18,
  .keep patch7_5_21,
  .keep patch7_5_22,
  .keep patch7_5_23,
  .keep patch7_5_24,
  .keep patch7_5_25,
  .keep patch7_5_26,
  .keep patch7_5_27,
  .keep patch7_5_28,
  .keep patch7_5_29]
theorem check2_7_5 : checkRows direction samples trees2 rows2_7_5 = true := by decide
theorem link2_7_5 : rows2_7_5.map Verdict.patch = rows1_7_5.filterMap Verdict.kept := by rfl
theorem final_eq7_5 : final7_5 = rows2_7_5.filterMap Verdict.kept := by rfl
theorem initial7_5 : (RadiusTwo.familyForKind 7).map (rotatePatch 5 (hexRegion 2)) = rows0_7_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
