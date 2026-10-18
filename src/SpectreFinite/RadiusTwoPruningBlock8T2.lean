module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock8T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_8_2 : List (Verdict 6) := [
  .reject patch8_2_0 0,
  .keep patch8_2_1,
  .keep patch8_2_2,
  .keep patch8_2_3,
  .reject patch8_2_4 0,
  .keep patch8_2_5,
  .keep patch8_2_6,
  .keep patch8_2_7,
  .reject patch8_2_8 0,
  .keep patch8_2_9,
  .keep patch8_2_10,
  .keep patch8_2_11,
  .keep patch8_2_12,
  .keep patch8_2_13,
  .reject patch8_2_14 0,
  .keep patch8_2_15,
  .keep patch8_2_16,
  .keep patch8_2_17,
  .reject patch8_2_18 0,
  .keep patch8_2_19,
  .keep patch8_2_20,
  .keep patch8_2_21]
theorem check0_8_2 : checkRows direction samples trees0 rows0_8_2 = true := by decide
def rows1_8_2 : List (Verdict 6) := [
  .keep patch8_2_1,
  .keep patch8_2_2,
  .keep patch8_2_3,
  .keep patch8_2_5,
  .keep patch8_2_6,
  .keep patch8_2_7,
  .keep patch8_2_9,
  .keep patch8_2_10,
  .keep patch8_2_11,
  .keep patch8_2_12,
  .keep patch8_2_13,
  .keep patch8_2_15,
  .keep patch8_2_16,
  .keep patch8_2_17,
  .keep patch8_2_19,
  .keep patch8_2_20,
  .keep patch8_2_21]
theorem check1_8_2 : checkRows direction samples trees1 rows1_8_2 = true := by decide
theorem link1_8_2 : rows1_8_2.map Verdict.patch = rows0_8_2.filterMap Verdict.kept := by rfl
def rows2_8_2 : List (Verdict 6) := [
  .keep patch8_2_1,
  .keep patch8_2_2,
  .keep patch8_2_3,
  .keep patch8_2_5,
  .keep patch8_2_6,
  .keep patch8_2_7,
  .keep patch8_2_9,
  .keep patch8_2_10,
  .keep patch8_2_11,
  .keep patch8_2_12,
  .keep patch8_2_13,
  .keep patch8_2_15,
  .keep patch8_2_16,
  .keep patch8_2_17,
  .keep patch8_2_19,
  .keep patch8_2_20,
  .keep patch8_2_21]
theorem check2_8_2 : checkRows direction samples trees2 rows2_8_2 = true := by decide
theorem link2_8_2 : rows2_8_2.map Verdict.patch = rows1_8_2.filterMap Verdict.kept := by rfl
theorem final_eq8_2 : final8_2 = rows2_8_2.filterMap Verdict.kept := by rfl
theorem initial8_2 : (RadiusTwo.familyForKind 8).map (rotatePatch 2 (hexRegion 2)) = rows0_8_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
