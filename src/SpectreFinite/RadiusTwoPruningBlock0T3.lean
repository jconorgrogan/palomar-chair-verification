module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock0T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_3 : List (Verdict 6) := [
  .keep patch0_3_0,
  .reject patch0_3_1 2,
  .keep patch0_3_2,
  .reject patch0_3_3 3,
  .keep patch0_3_4,
  .keep patch0_3_5,
  .keep patch0_3_6,
  .keep patch0_3_7,
  .keep patch0_3_8,
  .keep patch0_3_9,
  .keep patch0_3_10,
  .keep patch0_3_11,
  .keep patch0_3_12,
  .keep patch0_3_13,
  .keep patch0_3_14,
  .keep patch0_3_15,
  .keep patch0_3_16,
  .keep patch0_3_17,
  .keep patch0_3_18,
  .keep patch0_3_19,
  .keep patch0_3_20,
  .keep patch0_3_21]
theorem check0_0_3 : checkRows direction samples trees0 rows0_0_3 = true := by decide
def rows1_0_3 : List (Verdict 6) := [
  .keep patch0_3_0,
  .keep patch0_3_2,
  .keep patch0_3_4,
  .keep patch0_3_5,
  .keep patch0_3_6,
  .keep patch0_3_7,
  .keep patch0_3_8,
  .keep patch0_3_9,
  .keep patch0_3_10,
  .keep patch0_3_11,
  .keep patch0_3_12,
  .keep patch0_3_13,
  .keep patch0_3_14,
  .keep patch0_3_15,
  .keep patch0_3_16,
  .reject patch0_3_17 3,
  .keep patch0_3_18,
  .keep patch0_3_19,
  .keep patch0_3_20,
  .keep patch0_3_21]
theorem check1_0_3 : checkRows direction samples trees1 rows1_0_3 = true := by decide
theorem link1_0_3 : rows1_0_3.map Verdict.patch = rows0_0_3.filterMap Verdict.kept := by rfl
def rows2_0_3 : List (Verdict 6) := [
  .keep patch0_3_0,
  .keep patch0_3_2,
  .keep patch0_3_4,
  .keep patch0_3_5,
  .keep patch0_3_6,
  .keep patch0_3_7,
  .keep patch0_3_8,
  .keep patch0_3_9,
  .keep patch0_3_10,
  .keep patch0_3_11,
  .keep patch0_3_12,
  .reject patch0_3_13 1,
  .keep patch0_3_14,
  .keep patch0_3_15,
  .keep patch0_3_16,
  .keep patch0_3_18,
  .keep patch0_3_19,
  .keep patch0_3_20,
  .keep patch0_3_21]
theorem check2_0_3 : checkRows direction samples trees2 rows2_0_3 = true := by decide
theorem link2_0_3 : rows2_0_3.map Verdict.patch = rows1_0_3.filterMap Verdict.kept := by rfl
theorem final_eq0_3 : final0_3 = rows2_0_3.filterMap Verdict.kept := by rfl
theorem initial0_3 : (RadiusTwo.familyForKind 0).map (rotatePatch 3 (hexRegion 2)) = rows0_0_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
