module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock7T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_4 : List (Verdict 6) := [
  .keep patch7_4_0,
  .keep patch7_4_1,
  .keep patch7_4_2,
  .keep patch7_4_3,
  .reject patch7_4_4 3,
  .keep patch7_4_5,
  .keep patch7_4_6,
  .keep patch7_4_7,
  .keep patch7_4_8,
  .keep patch7_4_9,
  .keep patch7_4_10,
  .keep patch7_4_11,
  .keep patch7_4_12,
  .keep patch7_4_13,
  .keep patch7_4_14,
  .keep patch7_4_15,
  .reject patch7_4_16 4,
  .reject patch7_4_17 4,
  .keep patch7_4_18,
  .keep patch7_4_19,
  .keep patch7_4_20,
  .keep patch7_4_21,
  .keep patch7_4_22,
  .keep patch7_4_23,
  .keep patch7_4_24,
  .keep patch7_4_25,
  .keep patch7_4_26,
  .keep patch7_4_27,
  .keep patch7_4_28,
  .keep patch7_4_29]
theorem check0_7_4 : checkRows direction samples trees0 rows0_7_4 = true := by decide
def rows1_7_4 : List (Verdict 6) := [
  .keep patch7_4_0,
  .keep patch7_4_1,
  .keep patch7_4_2,
  .keep patch7_4_3,
  .reject patch7_4_5 5,
  .keep patch7_4_6,
  .keep patch7_4_7,
  .keep patch7_4_8,
  .keep patch7_4_9,
  .keep patch7_4_10,
  .keep patch7_4_11,
  .keep patch7_4_12,
  .keep patch7_4_13,
  .keep patch7_4_14,
  .keep patch7_4_15,
  .keep patch7_4_18,
  .reject patch7_4_19 2,
  .reject patch7_4_20 5,
  .keep patch7_4_21,
  .keep patch7_4_22,
  .keep patch7_4_23,
  .keep patch7_4_24,
  .keep patch7_4_25,
  .keep patch7_4_26,
  .keep patch7_4_27,
  .keep patch7_4_28,
  .keep patch7_4_29]
theorem check1_7_4 : checkRows direction samples trees1 rows1_7_4 = true := by decide
theorem link1_7_4 : rows1_7_4.map Verdict.patch = rows0_7_4.filterMap Verdict.kept := by rfl
def rows2_7_4 : List (Verdict 6) := [
  .keep patch7_4_0,
  .keep patch7_4_1,
  .keep patch7_4_2,
  .keep patch7_4_3,
  .keep patch7_4_6,
  .keep patch7_4_7,
  .keep patch7_4_8,
  .keep patch7_4_9,
  .keep patch7_4_10,
  .keep patch7_4_11,
  .keep patch7_4_12,
  .keep patch7_4_13,
  .keep patch7_4_14,
  .keep patch7_4_15,
  .keep patch7_4_18,
  .keep patch7_4_21,
  .keep patch7_4_22,
  .keep patch7_4_23,
  .keep patch7_4_24,
  .keep patch7_4_25,
  .keep patch7_4_26,
  .keep patch7_4_27,
  .keep patch7_4_28,
  .keep patch7_4_29]
theorem check2_7_4 : checkRows direction samples trees2 rows2_7_4 = true := by decide
theorem link2_7_4 : rows2_7_4.map Verdict.patch = rows1_7_4.filterMap Verdict.kept := by rfl
theorem final_eq7_4 : final7_4 = rows2_7_4.filterMap Verdict.kept := by rfl
theorem initial7_4 : (RadiusTwo.familyForKind 7).map (rotatePatch 4 (hexRegion 2)) = rows0_7_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
