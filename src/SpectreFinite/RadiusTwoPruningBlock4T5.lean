module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock4T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_5 : List (Verdict 6) := [
  .reject patch4_5_0 0,
  .reject patch4_5_1 2,
  .keep patch4_5_2,
  .reject patch4_5_3 2,
  .keep patch4_5_4,
  .reject patch4_5_5 0,
  .keep patch4_5_6,
  .keep patch4_5_7,
  .reject patch4_5_8 2,
  .keep patch4_5_9,
  .keep patch4_5_10,
  .reject patch4_5_11 2,
  .keep patch4_5_12,
  .keep patch4_5_13,
  .reject patch4_5_14 2,
  .keep patch4_5_15,
  .keep patch4_5_16,
  .reject patch4_5_17 2]
theorem check0_4_5 : checkRows direction samples trees0 rows0_4_5 = true := by decide
def rows1_4_5 : List (Verdict 6) := [
  .keep patch4_5_2,
  .keep patch4_5_4,
  .keep patch4_5_6,
  .keep patch4_5_7,
  .keep patch4_5_9,
  .keep patch4_5_10,
  .reject patch4_5_12 0,
  .keep patch4_5_13,
  .keep patch4_5_15,
  .keep patch4_5_16]
theorem check1_4_5 : checkRows direction samples trees1 rows1_4_5 = true := by decide
theorem link1_4_5 : rows1_4_5.map Verdict.patch = rows0_4_5.filterMap Verdict.kept := by rfl
def rows2_4_5 : List (Verdict 6) := [
  .keep patch4_5_2,
  .keep patch4_5_4,
  .keep patch4_5_6,
  .reject patch4_5_7 3,
  .keep patch4_5_9,
  .keep patch4_5_10,
  .keep patch4_5_13,
  .keep patch4_5_15,
  .keep patch4_5_16]
theorem check2_4_5 : checkRows direction samples trees2 rows2_4_5 = true := by decide
theorem link2_4_5 : rows2_4_5.map Verdict.patch = rows1_4_5.filterMap Verdict.kept := by rfl
theorem final_eq4_5 : final4_5 = rows2_4_5.filterMap Verdict.kept := by rfl
theorem initial4_5 : (RadiusTwo.familyForKind 4).map (rotatePatch 5 (hexRegion 2)) = rows0_4_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
