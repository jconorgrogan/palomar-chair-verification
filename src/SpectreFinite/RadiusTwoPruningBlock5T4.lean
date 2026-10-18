module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock5T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_4 : List (Verdict 6) := [
  .reject patch5_4_0 1,
  .reject patch5_4_1 4,
  .reject patch5_4_2 4,
  .keep patch5_4_3,
  .keep patch5_4_4,
  .reject patch5_4_5 1,
  .keep patch5_4_6,
  .keep patch5_4_7,
  .reject patch5_4_8 1,
  .keep patch5_4_9,
  .keep patch5_4_10,
  .reject patch5_4_11 4,
  .keep patch5_4_12,
  .keep patch5_4_13,
  .keep patch5_4_14,
  .keep patch5_4_15,
  .keep patch5_4_16]
theorem check0_5_4 : checkRows direction samples trees0 rows0_5_4 = true := by decide
def rows1_5_4 : List (Verdict 6) := [
  .keep patch5_4_3,
  .keep patch5_4_4,
  .keep patch5_4_6,
  .keep patch5_4_7,
  .keep patch5_4_9,
  .keep patch5_4_10,
  .keep patch5_4_12,
  .keep patch5_4_13,
  .keep patch5_4_14,
  .keep patch5_4_15,
  .keep patch5_4_16]
theorem check1_5_4 : checkRows direction samples trees1 rows1_5_4 = true := by decide
theorem link1_5_4 : rows1_5_4.map Verdict.patch = rows0_5_4.filterMap Verdict.kept := by rfl
def rows2_5_4 : List (Verdict 6) := [
  .keep patch5_4_3,
  .keep patch5_4_4,
  .keep patch5_4_6,
  .keep patch5_4_7,
  .keep patch5_4_9,
  .keep patch5_4_10,
  .keep patch5_4_12,
  .keep patch5_4_13,
  .keep patch5_4_14,
  .keep patch5_4_15,
  .keep patch5_4_16]
theorem check2_5_4 : checkRows direction samples trees2 rows2_5_4 = true := by decide
theorem link2_5_4 : rows2_5_4.map Verdict.patch = rows1_5_4.filterMap Verdict.kept := by rfl
theorem final_eq5_4 : final5_4 = rows2_5_4.filterMap Verdict.kept := by rfl
theorem initial5_4 : (RadiusTwo.familyForKind 5).map (rotatePatch 4 (hexRegion 2)) = rows0_5_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
