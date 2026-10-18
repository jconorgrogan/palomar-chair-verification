module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock1T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_4 : List (Verdict 6) := [
  .keep patch1_4_0,
  .keep patch1_4_1,
  .keep patch1_4_2,
  .keep patch1_4_3,
  .reject patch1_4_4 3,
  .reject patch1_4_5 4,
  .reject patch1_4_6 4,
  .keep patch1_4_7,
  .keep patch1_4_8,
  .keep patch1_4_9,
  .keep patch1_4_10,
  .keep patch1_4_11,
  .keep patch1_4_12,
  .keep patch1_4_13,
  .keep patch1_4_14,
  .reject patch1_4_15 4,
  .reject patch1_4_16 4,
  .reject patch1_4_17 4,
  .keep patch1_4_18,
  .keep patch1_4_19,
  .keep patch1_4_20]
theorem check0_1_4 : checkRows direction samples trees0 rows0_1_4 = true := by decide
def rows1_1_4 : List (Verdict 6) := [
  .keep patch1_4_0,
  .keep patch1_4_1,
  .reject patch1_4_2 4,
  .reject patch1_4_3 4,
  .keep patch1_4_7,
  .keep patch1_4_8,
  .keep patch1_4_9,
  .keep patch1_4_10,
  .keep patch1_4_11,
  .keep patch1_4_12,
  .keep patch1_4_13,
  .keep patch1_4_14,
  .keep patch1_4_18,
  .keep patch1_4_19,
  .keep patch1_4_20]
theorem check1_1_4 : checkRows direction samples trees1 rows1_1_4 = true := by decide
theorem link1_1_4 : rows1_1_4.map Verdict.patch = rows0_1_4.filterMap Verdict.kept := by rfl
def rows2_1_4 : List (Verdict 6) := [
  .keep patch1_4_0,
  .keep patch1_4_1,
  .keep patch1_4_7,
  .keep patch1_4_8,
  .keep patch1_4_9,
  .keep patch1_4_10,
  .keep patch1_4_11,
  .keep patch1_4_12,
  .keep patch1_4_13,
  .keep patch1_4_14,
  .keep patch1_4_18,
  .keep patch1_4_19,
  .keep patch1_4_20]
theorem check2_1_4 : checkRows direction samples trees2 rows2_1_4 = true := by decide
theorem link2_1_4 : rows2_1_4.map Verdict.patch = rows1_1_4.filterMap Verdict.kept := by rfl
theorem final_eq1_4 : final1_4 = rows2_1_4.filterMap Verdict.kept := by rfl
theorem initial1_4 : (RadiusTwo.familyForKind 1).map (rotatePatch 4 (hexRegion 2)) = rows0_1_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
