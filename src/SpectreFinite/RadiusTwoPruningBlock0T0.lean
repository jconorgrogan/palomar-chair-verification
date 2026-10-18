module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock0T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_0 : List (Verdict 6) := [
  .keep patch0_0_0,
  .reject patch0_0_1 0,
  .keep patch0_0_2,
  .reject patch0_0_3 0,
  .keep patch0_0_4,
  .keep patch0_0_5,
  .keep patch0_0_6,
  .keep patch0_0_7,
  .keep patch0_0_8,
  .keep patch0_0_9,
  .keep patch0_0_10,
  .keep patch0_0_11,
  .keep patch0_0_12,
  .keep patch0_0_13,
  .keep patch0_0_14,
  .keep patch0_0_15,
  .keep patch0_0_16,
  .keep patch0_0_17,
  .keep patch0_0_18,
  .keep patch0_0_19,
  .keep patch0_0_20,
  .keep patch0_0_21]
theorem check0_0_0 : checkRows direction samples trees0 rows0_0_0 = true := by decide
def rows1_0_0 : List (Verdict 6) := [
  .keep patch0_0_0,
  .keep patch0_0_2,
  .keep patch0_0_4,
  .keep patch0_0_5,
  .keep patch0_0_6,
  .keep patch0_0_7,
  .keep patch0_0_8,
  .keep patch0_0_9,
  .keep patch0_0_10,
  .keep patch0_0_11,
  .keep patch0_0_12,
  .keep patch0_0_13,
  .keep patch0_0_14,
  .keep patch0_0_15,
  .keep patch0_0_16,
  .reject patch0_0_17 0,
  .keep patch0_0_18,
  .keep patch0_0_19,
  .keep patch0_0_20,
  .keep patch0_0_21]
theorem check1_0_0 : checkRows direction samples trees1 rows1_0_0 = true := by decide
theorem link1_0_0 : rows1_0_0.map Verdict.patch = rows0_0_0.filterMap Verdict.kept := by rfl
def rows2_0_0 : List (Verdict 6) := [
  .keep patch0_0_0,
  .keep patch0_0_2,
  .keep patch0_0_4,
  .keep patch0_0_5,
  .keep patch0_0_6,
  .keep patch0_0_7,
  .keep patch0_0_8,
  .keep patch0_0_9,
  .keep patch0_0_10,
  .keep patch0_0_11,
  .keep patch0_0_12,
  .reject patch0_0_13 4,
  .keep patch0_0_14,
  .keep patch0_0_15,
  .keep patch0_0_16,
  .keep patch0_0_18,
  .keep patch0_0_19,
  .keep patch0_0_20,
  .keep patch0_0_21]
theorem check2_0_0 : checkRows direction samples trees2 rows2_0_0 = true := by decide
theorem link2_0_0 : rows2_0_0.map Verdict.patch = rows1_0_0.filterMap Verdict.kept := by rfl
theorem final_eq0_0 : final0_0 = rows2_0_0.filterMap Verdict.kept := by rfl
theorem initial0_0 : (RadiusTwo.familyForKind 0).map (rotatePatch 0 (hexRegion 2)) = rows0_0_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
