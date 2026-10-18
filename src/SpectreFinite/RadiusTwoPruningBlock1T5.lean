module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock1T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_5 : List (Verdict 6) := [
  .keep patch1_5_0,
  .keep patch1_5_1,
  .keep patch1_5_2,
  .keep patch1_5_3,
  .reject patch1_5_4 4,
  .reject patch1_5_5 5,
  .reject patch1_5_6 5,
  .keep patch1_5_7,
  .keep patch1_5_8,
  .keep patch1_5_9,
  .keep patch1_5_10,
  .keep patch1_5_11,
  .keep patch1_5_12,
  .keep patch1_5_13,
  .keep patch1_5_14,
  .reject patch1_5_15 5,
  .reject patch1_5_16 5,
  .reject patch1_5_17 5,
  .keep patch1_5_18,
  .keep patch1_5_19,
  .keep patch1_5_20]
theorem check0_1_5 : checkRows direction samples trees0 rows0_1_5 = true := by decide
def rows1_1_5 : List (Verdict 6) := [
  .keep patch1_5_0,
  .keep patch1_5_1,
  .reject patch1_5_2 0,
  .reject patch1_5_3 0,
  .keep patch1_5_7,
  .keep patch1_5_8,
  .keep patch1_5_9,
  .keep patch1_5_10,
  .keep patch1_5_11,
  .keep patch1_5_12,
  .keep patch1_5_13,
  .keep patch1_5_14,
  .keep patch1_5_18,
  .keep patch1_5_19,
  .keep patch1_5_20]
theorem check1_1_5 : checkRows direction samples trees1 rows1_1_5 = true := by decide
theorem link1_1_5 : rows1_1_5.map Verdict.patch = rows0_1_5.filterMap Verdict.kept := by rfl
def rows2_1_5 : List (Verdict 6) := [
  .keep patch1_5_0,
  .keep patch1_5_1,
  .keep patch1_5_7,
  .keep patch1_5_8,
  .keep patch1_5_9,
  .keep patch1_5_10,
  .keep patch1_5_11,
  .keep patch1_5_12,
  .keep patch1_5_13,
  .keep patch1_5_14,
  .keep patch1_5_18,
  .keep patch1_5_19,
  .keep patch1_5_20]
theorem check2_1_5 : checkRows direction samples trees2 rows2_1_5 = true := by decide
theorem link2_1_5 : rows2_1_5.map Verdict.patch = rows1_1_5.filterMap Verdict.kept := by rfl
theorem final_eq1_5 : final1_5 = rows2_1_5.filterMap Verdict.kept := by rfl
theorem initial1_5 : (RadiusTwo.familyForKind 1).map (rotatePatch 5 (hexRegion 2)) = rows0_1_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
