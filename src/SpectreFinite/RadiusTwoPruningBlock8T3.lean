module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock8T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_3 : List (Verdict 6) := [
  .reject patch8_3_0 0,
  .keep patch8_3_1,
  .keep patch8_3_2,
  .keep patch8_3_3,
  .reject patch8_3_4 0,
  .keep patch8_3_5,
  .keep patch8_3_6,
  .keep patch8_3_7,
  .reject patch8_3_8 0,
  .keep patch8_3_9,
  .keep patch8_3_10,
  .keep patch8_3_11,
  .keep patch8_3_12,
  .keep patch8_3_13,
  .reject patch8_3_14 0,
  .keep patch8_3_15,
  .keep patch8_3_16,
  .keep patch8_3_17,
  .reject patch8_3_18 0,
  .keep patch8_3_19,
  .keep patch8_3_20,
  .keep patch8_3_21]
theorem check0_8_3 : checkRows direction samples trees0 rows0_8_3 = true := by decide
def rows1_8_3 : List (Verdict 6) := [
  .keep patch8_3_1,
  .keep patch8_3_2,
  .keep patch8_3_3,
  .keep patch8_3_5,
  .keep patch8_3_6,
  .keep patch8_3_7,
  .keep patch8_3_9,
  .keep patch8_3_10,
  .keep patch8_3_11,
  .keep patch8_3_12,
  .keep patch8_3_13,
  .keep patch8_3_15,
  .keep patch8_3_16,
  .keep patch8_3_17,
  .keep patch8_3_19,
  .keep patch8_3_20,
  .keep patch8_3_21]
theorem check1_8_3 : checkRows direction samples trees1 rows1_8_3 = true := by decide
theorem link1_8_3 : rows1_8_3.map Verdict.patch = rows0_8_3.filterMap Verdict.kept := by rfl
def rows2_8_3 : List (Verdict 6) := [
  .keep patch8_3_1,
  .keep patch8_3_2,
  .keep patch8_3_3,
  .keep patch8_3_5,
  .keep patch8_3_6,
  .keep patch8_3_7,
  .keep patch8_3_9,
  .keep patch8_3_10,
  .keep patch8_3_11,
  .keep patch8_3_12,
  .keep patch8_3_13,
  .keep patch8_3_15,
  .keep patch8_3_16,
  .keep patch8_3_17,
  .keep patch8_3_19,
  .keep patch8_3_20,
  .keep patch8_3_21]
theorem check2_8_3 : checkRows direction samples trees2 rows2_8_3 = true := by decide
theorem link2_8_3 : rows2_8_3.map Verdict.patch = rows1_8_3.filterMap Verdict.kept := by rfl
theorem final_eq8_3 : final8_3 = rows2_8_3.filterMap Verdict.kept := by rfl
theorem initial8_3 : (RadiusTwo.familyForKind 8).map (rotatePatch 3 (hexRegion 2)) = rows0_8_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
