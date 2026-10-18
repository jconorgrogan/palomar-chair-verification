module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock1T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_1_1 : List (Verdict 6) := [
  .keep patch1_1_0,
  .keep patch1_1_1,
  .keep patch1_1_2,
  .keep patch1_1_3,
  .reject patch1_1_4 0,
  .reject patch1_1_5 1,
  .reject patch1_1_6 1,
  .keep patch1_1_7,
  .keep patch1_1_8,
  .keep patch1_1_9,
  .keep patch1_1_10,
  .keep patch1_1_11,
  .keep patch1_1_12,
  .keep patch1_1_13,
  .keep patch1_1_14,
  .reject patch1_1_15 1,
  .reject patch1_1_16 1,
  .reject patch1_1_17 1,
  .keep patch1_1_18,
  .keep patch1_1_19,
  .keep patch1_1_20]
theorem check0_1_1 : checkRows direction samples trees0 rows0_1_1 = true := by decide
def rows1_1_1 : List (Verdict 6) := [
  .keep patch1_1_0,
  .keep patch1_1_1,
  .reject patch1_1_2 1,
  .reject patch1_1_3 1,
  .keep patch1_1_7,
  .keep patch1_1_8,
  .keep patch1_1_9,
  .keep patch1_1_10,
  .keep patch1_1_11,
  .keep patch1_1_12,
  .keep patch1_1_13,
  .keep patch1_1_14,
  .keep patch1_1_18,
  .keep patch1_1_19,
  .keep patch1_1_20]
theorem check1_1_1 : checkRows direction samples trees1 rows1_1_1 = true := by decide
theorem link1_1_1 : rows1_1_1.map Verdict.patch = rows0_1_1.filterMap Verdict.kept := by rfl
def rows2_1_1 : List (Verdict 6) := [
  .keep patch1_1_0,
  .keep patch1_1_1,
  .keep patch1_1_7,
  .keep patch1_1_8,
  .keep patch1_1_9,
  .keep patch1_1_10,
  .keep patch1_1_11,
  .keep patch1_1_12,
  .keep patch1_1_13,
  .keep patch1_1_14,
  .keep patch1_1_18,
  .keep patch1_1_19,
  .keep patch1_1_20]
theorem check2_1_1 : checkRows direction samples trees2 rows2_1_1 = true := by decide
theorem link2_1_1 : rows2_1_1.map Verdict.patch = rows1_1_1.filterMap Verdict.kept := by rfl
theorem final_eq1_1 : final1_1 = rows2_1_1.filterMap Verdict.kept := by rfl
theorem initial1_1 : (RadiusTwo.familyForKind 1).map (rotatePatch 1 (hexRegion 2)) = rows0_1_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
