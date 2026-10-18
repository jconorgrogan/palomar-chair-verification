module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock4T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_1 : List (Verdict 6) := [
  .reject patch4_1_0 2,
  .reject patch4_1_1 4,
  .keep patch4_1_2,
  .reject patch4_1_3 4,
  .keep patch4_1_4,
  .reject patch4_1_5 2,
  .keep patch4_1_6,
  .keep patch4_1_7,
  .reject patch4_1_8 4,
  .keep patch4_1_9,
  .keep patch4_1_10,
  .reject patch4_1_11 4,
  .keep patch4_1_12,
  .keep patch4_1_13,
  .reject patch4_1_14 4,
  .keep patch4_1_15,
  .keep patch4_1_16,
  .reject patch4_1_17 4]
theorem check0_4_1 : checkRows direction samples trees0 rows0_4_1 = true := by decide
def rows1_4_1 : List (Verdict 6) := [
  .keep patch4_1_2,
  .keep patch4_1_4,
  .keep patch4_1_6,
  .keep patch4_1_7,
  .keep patch4_1_9,
  .keep patch4_1_10,
  .reject patch4_1_12 2,
  .keep patch4_1_13,
  .keep patch4_1_15,
  .keep patch4_1_16]
theorem check1_4_1 : checkRows direction samples trees1 rows1_4_1 = true := by decide
theorem link1_4_1 : rows1_4_1.map Verdict.patch = rows0_4_1.filterMap Verdict.kept := by rfl
def rows2_4_1 : List (Verdict 6) := [
  .keep patch4_1_2,
  .keep patch4_1_4,
  .keep patch4_1_6,
  .reject patch4_1_7 5,
  .keep patch4_1_9,
  .keep patch4_1_10,
  .keep patch4_1_13,
  .keep patch4_1_15,
  .keep patch4_1_16]
theorem check2_4_1 : checkRows direction samples trees2 rows2_4_1 = true := by decide
theorem link2_4_1 : rows2_4_1.map Verdict.patch = rows1_4_1.filterMap Verdict.kept := by rfl
theorem final_eq4_1 : final4_1 = rows2_4_1.filterMap Verdict.kept := by rfl
theorem initial4_1 : (RadiusTwo.familyForKind 4).map (rotatePatch 1 (hexRegion 2)) = rows0_4_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
