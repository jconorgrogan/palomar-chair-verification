module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock0T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_2 : List (Verdict 6) := [
  .keep patch0_2_0,
  .reject patch0_2_1 1,
  .keep patch0_2_2,
  .reject patch0_2_3 2,
  .keep patch0_2_4,
  .keep patch0_2_5,
  .keep patch0_2_6,
  .keep patch0_2_7,
  .keep patch0_2_8,
  .keep patch0_2_9,
  .keep patch0_2_10,
  .keep patch0_2_11,
  .keep patch0_2_12,
  .keep patch0_2_13,
  .keep patch0_2_14,
  .keep patch0_2_15,
  .keep patch0_2_16,
  .keep patch0_2_17,
  .keep patch0_2_18,
  .keep patch0_2_19,
  .keep patch0_2_20,
  .keep patch0_2_21]
theorem check0_0_2 : checkRows direction samples trees0 rows0_0_2 = true := by decide
def rows1_0_2 : List (Verdict 6) := [
  .keep patch0_2_0,
  .keep patch0_2_2,
  .keep patch0_2_4,
  .keep patch0_2_5,
  .keep patch0_2_6,
  .keep patch0_2_7,
  .keep patch0_2_8,
  .keep patch0_2_9,
  .keep patch0_2_10,
  .keep patch0_2_11,
  .keep patch0_2_12,
  .keep patch0_2_13,
  .keep patch0_2_14,
  .keep patch0_2_15,
  .keep patch0_2_16,
  .reject patch0_2_17 2,
  .keep patch0_2_18,
  .keep patch0_2_19,
  .keep patch0_2_20,
  .keep patch0_2_21]
theorem check1_0_2 : checkRows direction samples trees1 rows1_0_2 = true := by decide
theorem link1_0_2 : rows1_0_2.map Verdict.patch = rows0_0_2.filterMap Verdict.kept := by rfl
def rows2_0_2 : List (Verdict 6) := [
  .keep patch0_2_0,
  .keep patch0_2_2,
  .keep patch0_2_4,
  .keep patch0_2_5,
  .keep patch0_2_6,
  .keep patch0_2_7,
  .keep patch0_2_8,
  .keep patch0_2_9,
  .keep patch0_2_10,
  .keep patch0_2_11,
  .keep patch0_2_12,
  .reject patch0_2_13 0,
  .keep patch0_2_14,
  .keep patch0_2_15,
  .keep patch0_2_16,
  .keep patch0_2_18,
  .keep patch0_2_19,
  .keep patch0_2_20,
  .keep patch0_2_21]
theorem check2_0_2 : checkRows direction samples trees2 rows2_0_2 = true := by decide
theorem link2_0_2 : rows2_0_2.map Verdict.patch = rows1_0_2.filterMap Verdict.kept := by rfl
theorem final_eq0_2 : final0_2 = rows2_0_2.filterMap Verdict.kept := by rfl
theorem initial0_2 : (RadiusTwo.familyForKind 0).map (rotatePatch 2 (hexRegion 2)) = rows0_0_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
