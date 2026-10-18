module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock0T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_5 : List (Verdict 6) := [
  .keep patch0_5_0,
  .reject patch0_5_1 4,
  .keep patch0_5_2,
  .reject patch0_5_3 5,
  .keep patch0_5_4,
  .keep patch0_5_5,
  .keep patch0_5_6,
  .keep patch0_5_7,
  .keep patch0_5_8,
  .keep patch0_5_9,
  .keep patch0_5_10,
  .keep patch0_5_11,
  .keep patch0_5_12,
  .keep patch0_5_13,
  .keep patch0_5_14,
  .keep patch0_5_15,
  .keep patch0_5_16,
  .keep patch0_5_17,
  .keep patch0_5_18,
  .keep patch0_5_19,
  .keep patch0_5_20,
  .keep patch0_5_21]
theorem check0_0_5 : checkRows direction samples trees0 rows0_0_5 = true := by decide
def rows1_0_5 : List (Verdict 6) := [
  .keep patch0_5_0,
  .keep patch0_5_2,
  .keep patch0_5_4,
  .keep patch0_5_5,
  .keep patch0_5_6,
  .keep patch0_5_7,
  .keep patch0_5_8,
  .keep patch0_5_9,
  .keep patch0_5_10,
  .keep patch0_5_11,
  .keep patch0_5_12,
  .keep patch0_5_13,
  .keep patch0_5_14,
  .keep patch0_5_15,
  .keep patch0_5_16,
  .reject patch0_5_17 5,
  .keep patch0_5_18,
  .keep patch0_5_19,
  .keep patch0_5_20,
  .keep patch0_5_21]
theorem check1_0_5 : checkRows direction samples trees1 rows1_0_5 = true := by decide
theorem link1_0_5 : rows1_0_5.map Verdict.patch = rows0_0_5.filterMap Verdict.kept := by rfl
def rows2_0_5 : List (Verdict 6) := [
  .keep patch0_5_0,
  .keep patch0_5_2,
  .keep patch0_5_4,
  .keep patch0_5_5,
  .keep patch0_5_6,
  .keep patch0_5_7,
  .keep patch0_5_8,
  .keep patch0_5_9,
  .keep patch0_5_10,
  .keep patch0_5_11,
  .keep patch0_5_12,
  .reject patch0_5_13 3,
  .keep patch0_5_14,
  .keep patch0_5_15,
  .keep patch0_5_16,
  .keep patch0_5_18,
  .keep patch0_5_19,
  .keep patch0_5_20,
  .keep patch0_5_21]
theorem check2_0_5 : checkRows direction samples trees2 rows2_0_5 = true := by decide
theorem link2_0_5 : rows2_0_5.map Verdict.patch = rows1_0_5.filterMap Verdict.kept := by rfl
theorem final_eq0_5 : final0_5 = rows2_0_5.filterMap Verdict.kept := by rfl
theorem initial0_5 : (RadiusTwo.familyForKind 0).map (rotatePatch 5 (hexRegion 2)) = rows0_0_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
