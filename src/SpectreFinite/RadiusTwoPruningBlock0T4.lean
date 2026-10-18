module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock0T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_0_4 : List (Verdict 6) := [
  .keep patch0_4_0,
  .reject patch0_4_1 3,
  .keep patch0_4_2,
  .reject patch0_4_3 4,
  .keep patch0_4_4,
  .keep patch0_4_5,
  .keep patch0_4_6,
  .keep patch0_4_7,
  .keep patch0_4_8,
  .keep patch0_4_9,
  .keep patch0_4_10,
  .keep patch0_4_11,
  .keep patch0_4_12,
  .keep patch0_4_13,
  .keep patch0_4_14,
  .keep patch0_4_15,
  .keep patch0_4_16,
  .keep patch0_4_17,
  .keep patch0_4_18,
  .keep patch0_4_19,
  .keep patch0_4_20,
  .keep patch0_4_21]
theorem check0_0_4 : checkRows direction samples trees0 rows0_0_4 = true := by decide
def rows1_0_4 : List (Verdict 6) := [
  .keep patch0_4_0,
  .keep patch0_4_2,
  .keep patch0_4_4,
  .keep patch0_4_5,
  .keep patch0_4_6,
  .keep patch0_4_7,
  .keep patch0_4_8,
  .keep patch0_4_9,
  .keep patch0_4_10,
  .keep patch0_4_11,
  .keep patch0_4_12,
  .keep patch0_4_13,
  .keep patch0_4_14,
  .keep patch0_4_15,
  .keep patch0_4_16,
  .reject patch0_4_17 4,
  .keep patch0_4_18,
  .keep patch0_4_19,
  .keep patch0_4_20,
  .keep patch0_4_21]
theorem check1_0_4 : checkRows direction samples trees1 rows1_0_4 = true := by decide
theorem link1_0_4 : rows1_0_4.map Verdict.patch = rows0_0_4.filterMap Verdict.kept := by rfl
def rows2_0_4 : List (Verdict 6) := [
  .keep patch0_4_0,
  .keep patch0_4_2,
  .keep patch0_4_4,
  .keep patch0_4_5,
  .keep patch0_4_6,
  .keep patch0_4_7,
  .keep patch0_4_8,
  .keep patch0_4_9,
  .keep patch0_4_10,
  .keep patch0_4_11,
  .keep patch0_4_12,
  .reject patch0_4_13 2,
  .keep patch0_4_14,
  .keep patch0_4_15,
  .keep patch0_4_16,
  .keep patch0_4_18,
  .keep patch0_4_19,
  .keep patch0_4_20,
  .keep patch0_4_21]
theorem check2_0_4 : checkRows direction samples trees2 rows2_0_4 = true := by decide
theorem link2_0_4 : rows2_0_4.map Verdict.patch = rows1_0_4.filterMap Verdict.kept := by rfl
theorem final_eq0_4 : final0_4 = rows2_0_4.filterMap Verdict.kept := by rfl
theorem initial0_4 : (RadiusTwo.familyForKind 0).map (rotatePatch 4 (hexRegion 2)) = rows0_0_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
