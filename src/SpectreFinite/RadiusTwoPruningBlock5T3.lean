module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock5T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_3 : List (Verdict 6) := [
  .reject patch5_3_0 0,
  .reject patch5_3_1 3,
  .reject patch5_3_2 3,
  .keep patch5_3_3,
  .keep patch5_3_4,
  .reject patch5_3_5 0,
  .keep patch5_3_6,
  .keep patch5_3_7,
  .reject patch5_3_8 0,
  .keep patch5_3_9,
  .keep patch5_3_10,
  .reject patch5_3_11 3,
  .keep patch5_3_12,
  .keep patch5_3_13,
  .keep patch5_3_14,
  .keep patch5_3_15,
  .keep patch5_3_16]
theorem check0_5_3 : checkRows direction samples trees0 rows0_5_3 = true := by decide
def rows1_5_3 : List (Verdict 6) := [
  .keep patch5_3_3,
  .keep patch5_3_4,
  .keep patch5_3_6,
  .keep patch5_3_7,
  .keep patch5_3_9,
  .keep patch5_3_10,
  .keep patch5_3_12,
  .keep patch5_3_13,
  .keep patch5_3_14,
  .keep patch5_3_15,
  .keep patch5_3_16]
theorem check1_5_3 : checkRows direction samples trees1 rows1_5_3 = true := by decide
theorem link1_5_3 : rows1_5_3.map Verdict.patch = rows0_5_3.filterMap Verdict.kept := by rfl
def rows2_5_3 : List (Verdict 6) := [
  .keep patch5_3_3,
  .keep patch5_3_4,
  .keep patch5_3_6,
  .keep patch5_3_7,
  .keep patch5_3_9,
  .keep patch5_3_10,
  .keep patch5_3_12,
  .keep patch5_3_13,
  .keep patch5_3_14,
  .keep patch5_3_15,
  .keep patch5_3_16]
theorem check2_5_3 : checkRows direction samples trees2 rows2_5_3 = true := by decide
theorem link2_5_3 : rows2_5_3.map Verdict.patch = rows1_5_3.filterMap Verdict.kept := by rfl
theorem final_eq5_3 : final5_3 = rows2_5_3.filterMap Verdict.kept := by rfl
theorem initial5_3 : (RadiusTwo.familyForKind 5).map (rotatePatch 3 (hexRegion 2)) = rows0_5_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
