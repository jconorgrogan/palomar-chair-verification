module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock1T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_0 : List (Verdict 6) := [
  .keep patch1_0_0,
  .keep patch1_0_1,
  .keep patch1_0_2,
  .keep patch1_0_3,
  .reject patch1_0_4 0,
  .reject patch1_0_5 0,
  .reject patch1_0_6 0,
  .keep patch1_0_7,
  .keep patch1_0_8,
  .keep patch1_0_9,
  .keep patch1_0_10,
  .keep patch1_0_11,
  .keep patch1_0_12,
  .keep patch1_0_13,
  .keep patch1_0_14,
  .reject patch1_0_15 0,
  .reject patch1_0_16 0,
  .reject patch1_0_17 0,
  .keep patch1_0_18,
  .keep patch1_0_19,
  .keep patch1_0_20]
theorem check0_1_0 : checkRows direction samples trees0 rows0_1_0 = true := by decide
def rows1_1_0 : List (Verdict 6) := [
  .keep patch1_0_0,
  .keep patch1_0_1,
  .reject patch1_0_2 0,
  .reject patch1_0_3 0,
  .keep patch1_0_7,
  .keep patch1_0_8,
  .keep patch1_0_9,
  .keep patch1_0_10,
  .keep patch1_0_11,
  .keep patch1_0_12,
  .keep patch1_0_13,
  .keep patch1_0_14,
  .keep patch1_0_18,
  .keep patch1_0_19,
  .keep patch1_0_20]
theorem check1_1_0 : checkRows direction samples trees1 rows1_1_0 = true := by decide
theorem link1_1_0 : rows1_1_0.map Verdict.patch = rows0_1_0.filterMap Verdict.kept := by rfl
def rows2_1_0 : List (Verdict 6) := [
  .keep patch1_0_0,
  .keep patch1_0_1,
  .keep patch1_0_7,
  .keep patch1_0_8,
  .keep patch1_0_9,
  .keep patch1_0_10,
  .keep patch1_0_11,
  .keep patch1_0_12,
  .keep patch1_0_13,
  .keep patch1_0_14,
  .keep patch1_0_18,
  .keep patch1_0_19,
  .keep patch1_0_20]
theorem check2_1_0 : checkRows direction samples trees2 rows2_1_0 = true := by decide
theorem link2_1_0 : rows2_1_0.map Verdict.patch = rows1_1_0.filterMap Verdict.kept := by rfl
theorem final_eq1_0 : final1_0 = rows2_1_0.filterMap Verdict.kept := by rfl
theorem initial1_0 : (RadiusTwo.familyForKind 1).map (rotatePatch 0 (hexRegion 2)) = rows0_1_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
