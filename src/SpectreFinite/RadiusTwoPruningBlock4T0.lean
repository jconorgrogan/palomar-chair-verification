module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock4T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_0 : List (Verdict 6) := [
  .reject patch4_0_0 1,
  .reject patch4_0_1 3,
  .keep patch4_0_2,
  .reject patch4_0_3 3,
  .keep patch4_0_4,
  .reject patch4_0_5 1,
  .keep patch4_0_6,
  .keep patch4_0_7,
  .reject patch4_0_8 3,
  .keep patch4_0_9,
  .keep patch4_0_10,
  .reject patch4_0_11 3,
  .keep patch4_0_12,
  .keep patch4_0_13,
  .reject patch4_0_14 3,
  .keep patch4_0_15,
  .keep patch4_0_16,
  .reject patch4_0_17 3]
theorem check0_4_0 : checkRows direction samples trees0 rows0_4_0 = true := by decide
def rows1_4_0 : List (Verdict 6) := [
  .keep patch4_0_2,
  .keep patch4_0_4,
  .keep patch4_0_6,
  .keep patch4_0_7,
  .keep patch4_0_9,
  .keep patch4_0_10,
  .reject patch4_0_12 1,
  .keep patch4_0_13,
  .keep patch4_0_15,
  .keep patch4_0_16]
theorem check1_4_0 : checkRows direction samples trees1 rows1_4_0 = true := by decide
theorem link1_4_0 : rows1_4_0.map Verdict.patch = rows0_4_0.filterMap Verdict.kept := by rfl
def rows2_4_0 : List (Verdict 6) := [
  .keep patch4_0_2,
  .keep patch4_0_4,
  .keep patch4_0_6,
  .reject patch4_0_7 4,
  .keep patch4_0_9,
  .keep patch4_0_10,
  .keep patch4_0_13,
  .keep patch4_0_15,
  .keep patch4_0_16]
theorem check2_4_0 : checkRows direction samples trees2 rows2_4_0 = true := by decide
theorem link2_4_0 : rows2_4_0.map Verdict.patch = rows1_4_0.filterMap Verdict.kept := by rfl
theorem final_eq4_0 : final4_0 = rows2_4_0.filterMap Verdict.kept := by rfl
theorem initial4_0 : (RadiusTwo.familyForKind 4).map (rotatePatch 0 (hexRegion 2)) = rows0_4_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
