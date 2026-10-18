module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock8T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_4 : List (Verdict 6) := [
  .reject patch8_4_0 1,
  .keep patch8_4_1,
  .keep patch8_4_2,
  .keep patch8_4_3,
  .reject patch8_4_4 1,
  .keep patch8_4_5,
  .keep patch8_4_6,
  .keep patch8_4_7,
  .reject patch8_4_8 1,
  .keep patch8_4_9,
  .keep patch8_4_10,
  .keep patch8_4_11,
  .keep patch8_4_12,
  .keep patch8_4_13,
  .reject patch8_4_14 1,
  .keep patch8_4_15,
  .keep patch8_4_16,
  .keep patch8_4_17,
  .reject patch8_4_18 1,
  .keep patch8_4_19,
  .keep patch8_4_20,
  .keep patch8_4_21]
theorem check0_8_4 : checkRows direction samples trees0 rows0_8_4 = true := by decide
def rows1_8_4 : List (Verdict 6) := [
  .keep patch8_4_1,
  .keep patch8_4_2,
  .keep patch8_4_3,
  .keep patch8_4_5,
  .keep patch8_4_6,
  .keep patch8_4_7,
  .keep patch8_4_9,
  .keep patch8_4_10,
  .keep patch8_4_11,
  .keep patch8_4_12,
  .keep patch8_4_13,
  .keep patch8_4_15,
  .keep patch8_4_16,
  .keep patch8_4_17,
  .keep patch8_4_19,
  .keep patch8_4_20,
  .keep patch8_4_21]
theorem check1_8_4 : checkRows direction samples trees1 rows1_8_4 = true := by decide
theorem link1_8_4 : rows1_8_4.map Verdict.patch = rows0_8_4.filterMap Verdict.kept := by rfl
def rows2_8_4 : List (Verdict 6) := [
  .keep patch8_4_1,
  .keep patch8_4_2,
  .keep patch8_4_3,
  .keep patch8_4_5,
  .keep patch8_4_6,
  .keep patch8_4_7,
  .keep patch8_4_9,
  .keep patch8_4_10,
  .keep patch8_4_11,
  .keep patch8_4_12,
  .keep patch8_4_13,
  .keep patch8_4_15,
  .keep patch8_4_16,
  .keep patch8_4_17,
  .keep patch8_4_19,
  .keep patch8_4_20,
  .keep patch8_4_21]
theorem check2_8_4 : checkRows direction samples trees2 rows2_8_4 = true := by decide
theorem link2_8_4 : rows2_8_4.map Verdict.patch = rows1_8_4.filterMap Verdict.kept := by rfl
theorem final_eq8_4 : final8_4 = rows2_8_4.filterMap Verdict.kept := by rfl
theorem initial8_4 : (RadiusTwo.familyForKind 8).map (rotatePatch 4 (hexRegion 2)) = rows0_8_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
