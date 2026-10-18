module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock5T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_2 : List (Verdict 6) := [
  .reject patch5_2_0 2,
  .reject patch5_2_1 2,
  .reject patch5_2_2 2,
  .keep patch5_2_3,
  .keep patch5_2_4,
  .reject patch5_2_5 1,
  .keep patch5_2_6,
  .keep patch5_2_7,
  .reject patch5_2_8 2,
  .keep patch5_2_9,
  .keep patch5_2_10,
  .reject patch5_2_11 2,
  .keep patch5_2_12,
  .keep patch5_2_13,
  .keep patch5_2_14,
  .keep patch5_2_15,
  .keep patch5_2_16]
theorem check0_5_2 : checkRows direction samples trees0 rows0_5_2 = true := by decide
def rows1_5_2 : List (Verdict 6) := [
  .keep patch5_2_3,
  .keep patch5_2_4,
  .keep patch5_2_6,
  .keep patch5_2_7,
  .keep patch5_2_9,
  .keep patch5_2_10,
  .keep patch5_2_12,
  .keep patch5_2_13,
  .keep patch5_2_14,
  .keep patch5_2_15,
  .keep patch5_2_16]
theorem check1_5_2 : checkRows direction samples trees1 rows1_5_2 = true := by decide
theorem link1_5_2 : rows1_5_2.map Verdict.patch = rows0_5_2.filterMap Verdict.kept := by rfl
def rows2_5_2 : List (Verdict 6) := [
  .keep patch5_2_3,
  .keep patch5_2_4,
  .keep patch5_2_6,
  .keep patch5_2_7,
  .keep patch5_2_9,
  .keep patch5_2_10,
  .keep patch5_2_12,
  .keep patch5_2_13,
  .keep patch5_2_14,
  .keep patch5_2_15,
  .keep patch5_2_16]
theorem check2_5_2 : checkRows direction samples trees2 rows2_5_2 = true := by decide
theorem link2_5_2 : rows2_5_2.map Verdict.patch = rows1_5_2.filterMap Verdict.kept := by rfl
theorem final_eq5_2 : final5_2 = rows2_5_2.filterMap Verdict.kept := by rfl
theorem initial5_2 : (RadiusTwo.familyForKind 5).map (rotatePatch 2 (hexRegion 2)) = rows0_5_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
