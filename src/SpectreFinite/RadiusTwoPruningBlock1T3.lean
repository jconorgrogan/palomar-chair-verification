module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock1T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_3 : List (Verdict 6) := [
  .keep patch1_3_0,
  .keep patch1_3_1,
  .keep patch1_3_2,
  .keep patch1_3_3,
  .reject patch1_3_4 2,
  .reject patch1_3_5 3,
  .reject patch1_3_6 3,
  .keep patch1_3_7,
  .keep patch1_3_8,
  .keep patch1_3_9,
  .keep patch1_3_10,
  .keep patch1_3_11,
  .keep patch1_3_12,
  .keep patch1_3_13,
  .keep patch1_3_14,
  .reject patch1_3_15 3,
  .reject patch1_3_16 3,
  .reject patch1_3_17 3,
  .keep patch1_3_18,
  .keep patch1_3_19,
  .keep patch1_3_20]
theorem check0_1_3 : checkRows direction samples trees0 rows0_1_3 = true := by decide
def rows1_1_3 : List (Verdict 6) := [
  .keep patch1_3_0,
  .keep patch1_3_1,
  .reject patch1_3_2 3,
  .reject patch1_3_3 3,
  .keep patch1_3_7,
  .keep patch1_3_8,
  .keep patch1_3_9,
  .keep patch1_3_10,
  .keep patch1_3_11,
  .keep patch1_3_12,
  .keep patch1_3_13,
  .keep patch1_3_14,
  .keep patch1_3_18,
  .keep patch1_3_19,
  .keep patch1_3_20]
theorem check1_1_3 : checkRows direction samples trees1 rows1_1_3 = true := by decide
theorem link1_1_3 : rows1_1_3.map Verdict.patch = rows0_1_3.filterMap Verdict.kept := by rfl
def rows2_1_3 : List (Verdict 6) := [
  .keep patch1_3_0,
  .keep patch1_3_1,
  .keep patch1_3_7,
  .keep patch1_3_8,
  .keep patch1_3_9,
  .keep patch1_3_10,
  .keep patch1_3_11,
  .keep patch1_3_12,
  .keep patch1_3_13,
  .keep patch1_3_14,
  .keep patch1_3_18,
  .keep patch1_3_19,
  .keep patch1_3_20]
theorem check2_1_3 : checkRows direction samples trees2 rows2_1_3 = true := by decide
theorem link2_1_3 : rows2_1_3.map Verdict.patch = rows1_1_3.filterMap Verdict.kept := by rfl
theorem final_eq1_3 : final1_3 = rows2_1_3.filterMap Verdict.kept := by rfl
theorem initial1_3 : (RadiusTwo.familyForKind 1).map (rotatePatch 3 (hexRegion 2)) = rows0_1_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
