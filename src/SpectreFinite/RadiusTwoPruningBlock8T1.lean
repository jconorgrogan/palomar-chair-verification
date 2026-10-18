module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock8T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_1 : List (Verdict 6) := [
  .reject patch8_1_0 4,
  .keep patch8_1_1,
  .keep patch8_1_2,
  .keep patch8_1_3,
  .reject patch8_1_4 4,
  .keep patch8_1_5,
  .keep patch8_1_6,
  .keep patch8_1_7,
  .reject patch8_1_8 4,
  .keep patch8_1_9,
  .keep patch8_1_10,
  .keep patch8_1_11,
  .keep patch8_1_12,
  .keep patch8_1_13,
  .reject patch8_1_14 4,
  .keep patch8_1_15,
  .keep patch8_1_16,
  .keep patch8_1_17,
  .reject patch8_1_18 4,
  .keep patch8_1_19,
  .keep patch8_1_20,
  .keep patch8_1_21]
theorem check0_8_1 : checkRows direction samples trees0 rows0_8_1 = true := by decide
def rows1_8_1 : List (Verdict 6) := [
  .keep patch8_1_1,
  .keep patch8_1_2,
  .keep patch8_1_3,
  .keep patch8_1_5,
  .keep patch8_1_6,
  .keep patch8_1_7,
  .keep patch8_1_9,
  .keep patch8_1_10,
  .keep patch8_1_11,
  .keep patch8_1_12,
  .keep patch8_1_13,
  .keep patch8_1_15,
  .keep patch8_1_16,
  .keep patch8_1_17,
  .keep patch8_1_19,
  .keep patch8_1_20,
  .keep patch8_1_21]
theorem check1_8_1 : checkRows direction samples trees1 rows1_8_1 = true := by decide
theorem link1_8_1 : rows1_8_1.map Verdict.patch = rows0_8_1.filterMap Verdict.kept := by rfl
def rows2_8_1 : List (Verdict 6) := [
  .keep patch8_1_1,
  .keep patch8_1_2,
  .keep patch8_1_3,
  .keep patch8_1_5,
  .keep patch8_1_6,
  .keep patch8_1_7,
  .keep patch8_1_9,
  .keep patch8_1_10,
  .keep patch8_1_11,
  .keep patch8_1_12,
  .keep patch8_1_13,
  .keep patch8_1_15,
  .keep patch8_1_16,
  .keep patch8_1_17,
  .keep patch8_1_19,
  .keep patch8_1_20,
  .keep patch8_1_21]
theorem check2_8_1 : checkRows direction samples trees2 rows2_8_1 = true := by decide
theorem link2_8_1 : rows2_8_1.map Verdict.patch = rows1_8_1.filterMap Verdict.kept := by rfl
theorem final_eq8_1 : final8_1 = rows2_8_1.filterMap Verdict.kept := by rfl
theorem initial8_1 : (RadiusTwo.familyForKind 8).map (rotatePatch 1 (hexRegion 2)) = rows0_8_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
