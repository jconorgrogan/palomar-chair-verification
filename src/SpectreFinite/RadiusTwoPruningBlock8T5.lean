module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock8T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_5 : List (Verdict 6) := [
  .reject patch8_5_0 2,
  .keep patch8_5_1,
  .keep patch8_5_2,
  .keep patch8_5_3,
  .reject patch8_5_4 2,
  .keep patch8_5_5,
  .keep patch8_5_6,
  .keep patch8_5_7,
  .reject patch8_5_8 2,
  .keep patch8_5_9,
  .keep patch8_5_10,
  .keep patch8_5_11,
  .keep patch8_5_12,
  .keep patch8_5_13,
  .reject patch8_5_14 2,
  .keep patch8_5_15,
  .keep patch8_5_16,
  .keep patch8_5_17,
  .reject patch8_5_18 2,
  .keep patch8_5_19,
  .keep patch8_5_20,
  .keep patch8_5_21]
theorem check0_8_5 : checkRows direction samples trees0 rows0_8_5 = true := by decide
def rows1_8_5 : List (Verdict 6) := [
  .keep patch8_5_1,
  .keep patch8_5_2,
  .keep patch8_5_3,
  .keep patch8_5_5,
  .keep patch8_5_6,
  .keep patch8_5_7,
  .keep patch8_5_9,
  .keep patch8_5_10,
  .keep patch8_5_11,
  .keep patch8_5_12,
  .keep patch8_5_13,
  .keep patch8_5_15,
  .keep patch8_5_16,
  .keep patch8_5_17,
  .keep patch8_5_19,
  .keep patch8_5_20,
  .keep patch8_5_21]
theorem check1_8_5 : checkRows direction samples trees1 rows1_8_5 = true := by decide
theorem link1_8_5 : rows1_8_5.map Verdict.patch = rows0_8_5.filterMap Verdict.kept := by rfl
def rows2_8_5 : List (Verdict 6) := [
  .keep patch8_5_1,
  .keep patch8_5_2,
  .keep patch8_5_3,
  .keep patch8_5_5,
  .keep patch8_5_6,
  .keep patch8_5_7,
  .keep patch8_5_9,
  .keep patch8_5_10,
  .keep patch8_5_11,
  .keep patch8_5_12,
  .keep patch8_5_13,
  .keep patch8_5_15,
  .keep patch8_5_16,
  .keep patch8_5_17,
  .keep patch8_5_19,
  .keep patch8_5_20,
  .keep patch8_5_21]
theorem check2_8_5 : checkRows direction samples trees2 rows2_8_5 = true := by decide
theorem link2_8_5 : rows2_8_5.map Verdict.patch = rows1_8_5.filterMap Verdict.kept := by rfl
theorem final_eq8_5 : final8_5 = rows2_8_5.filterMap Verdict.kept := by rfl
theorem initial8_5 : (RadiusTwo.familyForKind 8).map (rotatePatch 5 (hexRegion 2)) = rows0_8_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
