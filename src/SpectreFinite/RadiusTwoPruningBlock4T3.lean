module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock4T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_3 : List (Verdict 6) := [
  .reject patch4_3_0 4,
  .reject patch4_3_1 0,
  .keep patch4_3_2,
  .reject patch4_3_3 0,
  .keep patch4_3_4,
  .reject patch4_3_5 0,
  .keep patch4_3_6,
  .keep patch4_3_7,
  .reject patch4_3_8 0,
  .keep patch4_3_9,
  .keep patch4_3_10,
  .reject patch4_3_11 0,
  .keep patch4_3_12,
  .keep patch4_3_13,
  .reject patch4_3_14 0,
  .keep patch4_3_15,
  .keep patch4_3_16,
  .reject patch4_3_17 0]
theorem check0_4_3 : checkRows direction samples trees0 rows0_4_3 = true := by decide
def rows1_4_3 : List (Verdict 6) := [
  .keep patch4_3_2,
  .keep patch4_3_4,
  .keep patch4_3_6,
  .keep patch4_3_7,
  .keep patch4_3_9,
  .keep patch4_3_10,
  .reject patch4_3_12 4,
  .keep patch4_3_13,
  .keep patch4_3_15,
  .keep patch4_3_16]
theorem check1_4_3 : checkRows direction samples trees1 rows1_4_3 = true := by decide
theorem link1_4_3 : rows1_4_3.map Verdict.patch = rows0_4_3.filterMap Verdict.kept := by rfl
def rows2_4_3 : List (Verdict 6) := [
  .keep patch4_3_2,
  .keep patch4_3_4,
  .keep patch4_3_6,
  .reject patch4_3_7 1,
  .keep patch4_3_9,
  .keep patch4_3_10,
  .keep patch4_3_13,
  .keep patch4_3_15,
  .keep patch4_3_16]
theorem check2_4_3 : checkRows direction samples trees2 rows2_4_3 = true := by decide
theorem link2_4_3 : rows2_4_3.map Verdict.patch = rows1_4_3.filterMap Verdict.kept := by rfl
theorem final_eq4_3 : final4_3 = rows2_4_3.filterMap Verdict.kept := by rfl
theorem initial4_3 : (RadiusTwo.familyForKind 4).map (rotatePatch 3 (hexRegion 2)) = rows0_4_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
