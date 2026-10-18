module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock0T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_1 : List (Verdict 6) := [
  .keep patch0_1_0,
  .reject patch0_1_1 0,
  .keep patch0_1_2,
  .reject patch0_1_3 1,
  .keep patch0_1_4,
  .keep patch0_1_5,
  .keep patch0_1_6,
  .keep patch0_1_7,
  .keep patch0_1_8,
  .keep patch0_1_9,
  .keep patch0_1_10,
  .keep patch0_1_11,
  .keep patch0_1_12,
  .keep patch0_1_13,
  .keep patch0_1_14,
  .keep patch0_1_15,
  .keep patch0_1_16,
  .keep patch0_1_17,
  .keep patch0_1_18,
  .keep patch0_1_19,
  .keep patch0_1_20,
  .keep patch0_1_21]
theorem check0_0_1 : checkRows direction samples trees0 rows0_0_1 = true := by decide
def rows1_0_1 : List (Verdict 6) := [
  .keep patch0_1_0,
  .keep patch0_1_2,
  .keep patch0_1_4,
  .keep patch0_1_5,
  .keep patch0_1_6,
  .keep patch0_1_7,
  .keep patch0_1_8,
  .keep patch0_1_9,
  .keep patch0_1_10,
  .keep patch0_1_11,
  .keep patch0_1_12,
  .keep patch0_1_13,
  .keep patch0_1_14,
  .keep patch0_1_15,
  .keep patch0_1_16,
  .reject patch0_1_17 1,
  .keep patch0_1_18,
  .keep patch0_1_19,
  .keep patch0_1_20,
  .keep patch0_1_21]
theorem check1_0_1 : checkRows direction samples trees1 rows1_0_1 = true := by decide
theorem link1_0_1 : rows1_0_1.map Verdict.patch = rows0_0_1.filterMap Verdict.kept := by rfl
def rows2_0_1 : List (Verdict 6) := [
  .keep patch0_1_0,
  .keep patch0_1_2,
  .keep patch0_1_4,
  .keep patch0_1_5,
  .keep patch0_1_6,
  .keep patch0_1_7,
  .keep patch0_1_8,
  .keep patch0_1_9,
  .keep patch0_1_10,
  .keep patch0_1_11,
  .keep patch0_1_12,
  .reject patch0_1_13 5,
  .keep patch0_1_14,
  .keep patch0_1_15,
  .keep patch0_1_16,
  .keep patch0_1_18,
  .keep patch0_1_19,
  .keep patch0_1_20,
  .keep patch0_1_21]
theorem check2_0_1 : checkRows direction samples trees2 rows2_0_1 = true := by decide
theorem link2_0_1 : rows2_0_1.map Verdict.patch = rows1_0_1.filterMap Verdict.kept := by rfl
theorem final_eq0_1 : final0_1 = rows2_0_1.filterMap Verdict.kept := by rfl
theorem initial0_1 : (RadiusTwo.familyForKind 0).map (rotatePatch 1 (hexRegion 2)) = rows0_0_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
