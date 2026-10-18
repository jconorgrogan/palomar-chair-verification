module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock4T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_4 : List (Verdict 6) := [
  .reject patch4_4_0 0,
  .reject patch4_4_1 1,
  .keep patch4_4_2,
  .reject patch4_4_3 1,
  .keep patch4_4_4,
  .reject patch4_4_5 1,
  .keep patch4_4_6,
  .keep patch4_4_7,
  .reject patch4_4_8 1,
  .keep patch4_4_9,
  .keep patch4_4_10,
  .reject patch4_4_11 1,
  .keep patch4_4_12,
  .keep patch4_4_13,
  .reject patch4_4_14 1,
  .keep patch4_4_15,
  .keep patch4_4_16,
  .reject patch4_4_17 1]
theorem check0_4_4 : checkRows direction samples trees0 rows0_4_4 = true := by decide
def rows1_4_4 : List (Verdict 6) := [
  .keep patch4_4_2,
  .keep patch4_4_4,
  .keep patch4_4_6,
  .keep patch4_4_7,
  .keep patch4_4_9,
  .keep patch4_4_10,
  .reject patch4_4_12 0,
  .keep patch4_4_13,
  .keep patch4_4_15,
  .keep patch4_4_16]
theorem check1_4_4 : checkRows direction samples trees1 rows1_4_4 = true := by decide
theorem link1_4_4 : rows1_4_4.map Verdict.patch = rows0_4_4.filterMap Verdict.kept := by rfl
def rows2_4_4 : List (Verdict 6) := [
  .keep patch4_4_2,
  .keep patch4_4_4,
  .keep patch4_4_6,
  .reject patch4_4_7 2,
  .keep patch4_4_9,
  .keep patch4_4_10,
  .keep patch4_4_13,
  .keep patch4_4_15,
  .keep patch4_4_16]
theorem check2_4_4 : checkRows direction samples trees2 rows2_4_4 = true := by decide
theorem link2_4_4 : rows2_4_4.map Verdict.patch = rows1_4_4.filterMap Verdict.kept := by rfl
theorem final_eq4_4 : final4_4 = rows2_4_4.filterMap Verdict.kept := by rfl
theorem initial4_4 : (RadiusTwo.familyForKind 4).map (rotatePatch 4 (hexRegion 2)) = rows0_4_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
