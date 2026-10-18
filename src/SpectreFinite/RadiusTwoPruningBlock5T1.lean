module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock5T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_1 : List (Verdict 6) := [
  .reject patch5_1_0 1,
  .reject patch5_1_1 1,
  .reject patch5_1_2 1,
  .keep patch5_1_3,
  .keep patch5_1_4,
  .reject patch5_1_5 0,
  .keep patch5_1_6,
  .keep patch5_1_7,
  .reject patch5_1_8 1,
  .keep patch5_1_9,
  .keep patch5_1_10,
  .reject patch5_1_11 1,
  .keep patch5_1_12,
  .keep patch5_1_13,
  .keep patch5_1_14,
  .keep patch5_1_15,
  .keep patch5_1_16]
theorem check0_5_1 : checkRows direction samples trees0 rows0_5_1 = true := by decide
def rows1_5_1 : List (Verdict 6) := [
  .keep patch5_1_3,
  .keep patch5_1_4,
  .keep patch5_1_6,
  .keep patch5_1_7,
  .keep patch5_1_9,
  .keep patch5_1_10,
  .keep patch5_1_12,
  .keep patch5_1_13,
  .keep patch5_1_14,
  .keep patch5_1_15,
  .keep patch5_1_16]
theorem check1_5_1 : checkRows direction samples trees1 rows1_5_1 = true := by decide
theorem link1_5_1 : rows1_5_1.map Verdict.patch = rows0_5_1.filterMap Verdict.kept := by rfl
def rows2_5_1 : List (Verdict 6) := [
  .keep patch5_1_3,
  .keep patch5_1_4,
  .keep patch5_1_6,
  .keep patch5_1_7,
  .keep patch5_1_9,
  .keep patch5_1_10,
  .keep patch5_1_12,
  .keep patch5_1_13,
  .keep patch5_1_14,
  .keep patch5_1_15,
  .keep patch5_1_16]
theorem check2_5_1 : checkRows direction samples trees2 rows2_5_1 = true := by decide
theorem link2_5_1 : rows2_5_1.map Verdict.patch = rows1_5_1.filterMap Verdict.kept := by rfl
theorem final_eq5_1 : final5_1 = rows2_5_1.filterMap Verdict.kept := by rfl
theorem initial5_1 : (RadiusTwo.familyForKind 5).map (rotatePatch 1 (hexRegion 2)) = rows0_5_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
