module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock5T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_5_0 : List (Verdict 6) := [
  .reject patch5_0_0 0,
  .reject patch5_0_1 0,
  .reject patch5_0_2 0,
  .keep patch5_0_3,
  .keep patch5_0_4,
  .reject patch5_0_5 0,
  .keep patch5_0_6,
  .keep patch5_0_7,
  .reject patch5_0_8 0,
  .keep patch5_0_9,
  .keep patch5_0_10,
  .reject patch5_0_11 0,
  .keep patch5_0_12,
  .keep patch5_0_13,
  .keep patch5_0_14,
  .keep patch5_0_15,
  .keep patch5_0_16]
theorem check0_5_0 : checkRows direction samples trees0 rows0_5_0 = true := by decide
def rows1_5_0 : List (Verdict 6) := [
  .keep patch5_0_3,
  .keep patch5_0_4,
  .keep patch5_0_6,
  .keep patch5_0_7,
  .keep patch5_0_9,
  .keep patch5_0_10,
  .keep patch5_0_12,
  .keep patch5_0_13,
  .keep patch5_0_14,
  .keep patch5_0_15,
  .keep patch5_0_16]
theorem check1_5_0 : checkRows direction samples trees1 rows1_5_0 = true := by decide
theorem link1_5_0 : rows1_5_0.map Verdict.patch = rows0_5_0.filterMap Verdict.kept := by rfl
def rows2_5_0 : List (Verdict 6) := [
  .keep patch5_0_3,
  .keep patch5_0_4,
  .keep patch5_0_6,
  .keep patch5_0_7,
  .keep patch5_0_9,
  .keep patch5_0_10,
  .keep patch5_0_12,
  .keep patch5_0_13,
  .keep patch5_0_14,
  .keep patch5_0_15,
  .keep patch5_0_16]
theorem check2_5_0 : checkRows direction samples trees2 rows2_5_0 = true := by decide
theorem link2_5_0 : rows2_5_0.map Verdict.patch = rows1_5_0.filterMap Verdict.kept := by rfl
theorem final_eq5_0 : final5_0 = rows2_5_0.filterMap Verdict.kept := by rfl
theorem initial5_0 : (RadiusTwo.familyForKind 5).map (rotatePatch 0 (hexRegion 2)) = rows0_5_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
