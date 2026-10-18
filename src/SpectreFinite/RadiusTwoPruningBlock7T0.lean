module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock7T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_7_0 : List (Verdict 6) := [
  .keep patch7_0_0,
  .keep patch7_0_1,
  .keep patch7_0_2,
  .keep patch7_0_3,
  .reject patch7_0_4 5,
  .keep patch7_0_5,
  .keep patch7_0_6,
  .keep patch7_0_7,
  .keep patch7_0_8,
  .keep patch7_0_9,
  .keep patch7_0_10,
  .keep patch7_0_11,
  .keep patch7_0_12,
  .keep patch7_0_13,
  .keep patch7_0_14,
  .keep patch7_0_15,
  .reject patch7_0_16 0,
  .reject patch7_0_17 0,
  .keep patch7_0_18,
  .keep patch7_0_19,
  .keep patch7_0_20,
  .keep patch7_0_21,
  .keep patch7_0_22,
  .keep patch7_0_23,
  .keep patch7_0_24,
  .keep patch7_0_25,
  .keep patch7_0_26,
  .keep patch7_0_27,
  .keep patch7_0_28,
  .keep patch7_0_29]
theorem check0_7_0 : checkRows direction samples trees0 rows0_7_0 = true := by decide
def rows1_7_0 : List (Verdict 6) := [
  .keep patch7_0_0,
  .keep patch7_0_1,
  .keep patch7_0_2,
  .keep patch7_0_3,
  .reject patch7_0_5 1,
  .keep patch7_0_6,
  .keep patch7_0_7,
  .keep patch7_0_8,
  .keep patch7_0_9,
  .keep patch7_0_10,
  .keep patch7_0_11,
  .keep patch7_0_12,
  .keep patch7_0_13,
  .keep patch7_0_14,
  .keep patch7_0_15,
  .keep patch7_0_18,
  .reject patch7_0_19 4,
  .reject patch7_0_20 1,
  .keep patch7_0_21,
  .keep patch7_0_22,
  .keep patch7_0_23,
  .keep patch7_0_24,
  .keep patch7_0_25,
  .keep patch7_0_26,
  .keep patch7_0_27,
  .keep patch7_0_28,
  .keep patch7_0_29]
theorem check1_7_0 : checkRows direction samples trees1 rows1_7_0 = true := by decide
theorem link1_7_0 : rows1_7_0.map Verdict.patch = rows0_7_0.filterMap Verdict.kept := by rfl
def rows2_7_0 : List (Verdict 6) := [
  .keep patch7_0_0,
  .keep patch7_0_1,
  .keep patch7_0_2,
  .keep patch7_0_3,
  .keep patch7_0_6,
  .keep patch7_0_7,
  .keep patch7_0_8,
  .keep patch7_0_9,
  .keep patch7_0_10,
  .keep patch7_0_11,
  .keep patch7_0_12,
  .keep patch7_0_13,
  .keep patch7_0_14,
  .keep patch7_0_15,
  .keep patch7_0_18,
  .keep patch7_0_21,
  .keep patch7_0_22,
  .keep patch7_0_23,
  .keep patch7_0_24,
  .keep patch7_0_25,
  .keep patch7_0_26,
  .keep patch7_0_27,
  .keep patch7_0_28,
  .keep patch7_0_29]
theorem check2_7_0 : checkRows direction samples trees2 rows2_7_0 = true := by decide
theorem link2_7_0 : rows2_7_0.map Verdict.patch = rows1_7_0.filterMap Verdict.kept := by rfl
theorem final_eq7_0 : final7_0 = rows2_7_0.filterMap Verdict.kept := by rfl
theorem initial7_0 : (RadiusTwo.familyForKind 7).map (rotatePatch 0 (hexRegion 2)) = rows0_7_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
