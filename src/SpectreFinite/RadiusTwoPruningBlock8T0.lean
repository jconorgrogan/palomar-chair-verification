module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock8T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_0 : List (Verdict 6) := [
  .reject patch8_0_0 3,
  .keep patch8_0_1,
  .keep patch8_0_2,
  .keep patch8_0_3,
  .reject patch8_0_4 3,
  .keep patch8_0_5,
  .keep patch8_0_6,
  .keep patch8_0_7,
  .reject patch8_0_8 3,
  .keep patch8_0_9,
  .keep patch8_0_10,
  .keep patch8_0_11,
  .keep patch8_0_12,
  .keep patch8_0_13,
  .reject patch8_0_14 3,
  .keep patch8_0_15,
  .keep patch8_0_16,
  .keep patch8_0_17,
  .reject patch8_0_18 3,
  .keep patch8_0_19,
  .keep patch8_0_20,
  .keep patch8_0_21]
theorem check0_8_0 : checkRows direction samples trees0 rows0_8_0 = true := by decide
def rows1_8_0 : List (Verdict 6) := [
  .keep patch8_0_1,
  .keep patch8_0_2,
  .keep patch8_0_3,
  .keep patch8_0_5,
  .keep patch8_0_6,
  .keep patch8_0_7,
  .keep patch8_0_9,
  .keep patch8_0_10,
  .keep patch8_0_11,
  .keep patch8_0_12,
  .keep patch8_0_13,
  .keep patch8_0_15,
  .keep patch8_0_16,
  .keep patch8_0_17,
  .keep patch8_0_19,
  .keep patch8_0_20,
  .keep patch8_0_21]
theorem check1_8_0 : checkRows direction samples trees1 rows1_8_0 = true := by decide
theorem link1_8_0 : rows1_8_0.map Verdict.patch = rows0_8_0.filterMap Verdict.kept := by rfl
def rows2_8_0 : List (Verdict 6) := [
  .keep patch8_0_1,
  .keep patch8_0_2,
  .keep patch8_0_3,
  .keep patch8_0_5,
  .keep patch8_0_6,
  .keep patch8_0_7,
  .keep patch8_0_9,
  .keep patch8_0_10,
  .keep patch8_0_11,
  .keep patch8_0_12,
  .keep patch8_0_13,
  .keep patch8_0_15,
  .keep patch8_0_16,
  .keep patch8_0_17,
  .keep patch8_0_19,
  .keep patch8_0_20,
  .keep patch8_0_21]
theorem check2_8_0 : checkRows direction samples trees2 rows2_8_0 = true := by decide
theorem link2_8_0 : rows2_8_0.map Verdict.patch = rows1_8_0.filterMap Verdict.kept := by rfl
theorem final_eq8_0 : final8_0 = rows2_8_0.filterMap Verdict.kept := by rfl
theorem initial8_0 : (RadiusTwo.familyForKind 8).map (rotatePatch 0 (hexRegion 2)) = rows0_8_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
