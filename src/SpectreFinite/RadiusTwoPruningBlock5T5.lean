module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock5T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_5 : List (Verdict 6) := [
  .reject patch5_5_0 2,
  .reject patch5_5_1 5,
  .reject patch5_5_2 5,
  .keep patch5_5_3,
  .keep patch5_5_4,
  .reject patch5_5_5 2,
  .keep patch5_5_6,
  .keep patch5_5_7,
  .reject patch5_5_8 2,
  .keep patch5_5_9,
  .keep patch5_5_10,
  .reject patch5_5_11 5,
  .keep patch5_5_12,
  .keep patch5_5_13,
  .keep patch5_5_14,
  .keep patch5_5_15,
  .keep patch5_5_16]
theorem check0_5_5 : checkRows direction samples trees0 rows0_5_5 = true := by decide
def rows1_5_5 : List (Verdict 6) := [
  .keep patch5_5_3,
  .keep patch5_5_4,
  .keep patch5_5_6,
  .keep patch5_5_7,
  .keep patch5_5_9,
  .keep patch5_5_10,
  .keep patch5_5_12,
  .keep patch5_5_13,
  .keep patch5_5_14,
  .keep patch5_5_15,
  .keep patch5_5_16]
theorem check1_5_5 : checkRows direction samples trees1 rows1_5_5 = true := by decide
theorem link1_5_5 : rows1_5_5.map Verdict.patch = rows0_5_5.filterMap Verdict.kept := by rfl
def rows2_5_5 : List (Verdict 6) := [
  .keep patch5_5_3,
  .keep patch5_5_4,
  .keep patch5_5_6,
  .keep patch5_5_7,
  .keep patch5_5_9,
  .keep patch5_5_10,
  .keep patch5_5_12,
  .keep patch5_5_13,
  .keep patch5_5_14,
  .keep patch5_5_15,
  .keep patch5_5_16]
theorem check2_5_5 : checkRows direction samples trees2 rows2_5_5 = true := by decide
theorem link2_5_5 : rows2_5_5.map Verdict.patch = rows1_5_5.filterMap Verdict.kept := by rfl
theorem final_eq5_5 : final5_5 = rows2_5_5.filterMap Verdict.kept := by rfl
theorem initial5_5 : (RadiusTwo.familyForKind 5).map (rotatePatch 5 (hexRegion 2)) = rows0_5_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
