module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock1T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_2 : List (Verdict 6) := [
  .keep patch1_2_0,
  .keep patch1_2_1,
  .keep patch1_2_2,
  .keep patch1_2_3,
  .reject patch1_2_4 1,
  .reject patch1_2_5 2,
  .reject patch1_2_6 2,
  .keep patch1_2_7,
  .keep patch1_2_8,
  .keep patch1_2_9,
  .keep patch1_2_10,
  .keep patch1_2_11,
  .keep patch1_2_12,
  .keep patch1_2_13,
  .keep patch1_2_14,
  .reject patch1_2_15 2,
  .reject patch1_2_16 2,
  .reject patch1_2_17 2,
  .keep patch1_2_18,
  .keep patch1_2_19,
  .keep patch1_2_20]
theorem check0_1_2 : checkRows direction samples trees0 rows0_1_2 = true := by decide
def rows1_1_2 : List (Verdict 6) := [
  .keep patch1_2_0,
  .keep patch1_2_1,
  .reject patch1_2_2 2,
  .reject patch1_2_3 2,
  .keep patch1_2_7,
  .keep patch1_2_8,
  .keep patch1_2_9,
  .keep patch1_2_10,
  .keep patch1_2_11,
  .keep patch1_2_12,
  .keep patch1_2_13,
  .keep patch1_2_14,
  .keep patch1_2_18,
  .keep patch1_2_19,
  .keep patch1_2_20]
theorem check1_1_2 : checkRows direction samples trees1 rows1_1_2 = true := by decide
theorem link1_1_2 : rows1_1_2.map Verdict.patch = rows0_1_2.filterMap Verdict.kept := by rfl
def rows2_1_2 : List (Verdict 6) := [
  .keep patch1_2_0,
  .keep patch1_2_1,
  .keep patch1_2_7,
  .keep patch1_2_8,
  .keep patch1_2_9,
  .keep patch1_2_10,
  .keep patch1_2_11,
  .keep patch1_2_12,
  .keep patch1_2_13,
  .keep patch1_2_14,
  .keep patch1_2_18,
  .keep patch1_2_19,
  .keep patch1_2_20]
theorem check2_1_2 : checkRows direction samples trees2 rows2_1_2 = true := by decide
theorem link2_1_2 : rows2_1_2.map Verdict.patch = rows1_1_2.filterMap Verdict.kept := by rfl
theorem final_eq1_2 : final1_2 = rows2_1_2.filterMap Verdict.kept := by rfl
theorem initial1_2 : (RadiusTwo.familyForKind 1).map (rotatePatch 2 (hexRegion 2)) = rows0_1_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
