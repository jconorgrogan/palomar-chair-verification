module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock4T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_4_2 : List (Verdict 6) := [
  .reject patch4_2_0 3,
  .reject patch4_2_1 0,
  .keep patch4_2_2,
  .reject patch4_2_3 0,
  .keep patch4_2_4,
  .reject patch4_2_5 0,
  .keep patch4_2_6,
  .keep patch4_2_7,
  .reject patch4_2_8 0,
  .keep patch4_2_9,
  .keep patch4_2_10,
  .reject patch4_2_11 0,
  .keep patch4_2_12,
  .keep patch4_2_13,
  .reject patch4_2_14 0,
  .keep patch4_2_15,
  .keep patch4_2_16,
  .reject patch4_2_17 0]
theorem check0_4_2 : checkRows direction samples trees0 rows0_4_2 = true := by decide
def rows1_4_2 : List (Verdict 6) := [
  .keep patch4_2_2,
  .keep patch4_2_4,
  .keep patch4_2_6,
  .keep patch4_2_7,
  .keep patch4_2_9,
  .keep patch4_2_10,
  .reject patch4_2_12 3,
  .keep patch4_2_13,
  .keep patch4_2_15,
  .keep patch4_2_16]
theorem check1_4_2 : checkRows direction samples trees1 rows1_4_2 = true := by decide
theorem link1_4_2 : rows1_4_2.map Verdict.patch = rows0_4_2.filterMap Verdict.kept := by rfl
def rows2_4_2 : List (Verdict 6) := [
  .keep patch4_2_2,
  .keep patch4_2_4,
  .keep patch4_2_6,
  .reject patch4_2_7 0,
  .keep patch4_2_9,
  .keep patch4_2_10,
  .keep patch4_2_13,
  .keep patch4_2_15,
  .keep patch4_2_16]
theorem check2_4_2 : checkRows direction samples trees2 rows2_4_2 = true := by decide
theorem link2_4_2 : rows2_4_2.map Verdict.patch = rows1_4_2.filterMap Verdict.kept := by rfl
theorem final_eq4_2 : final4_2 = rows2_4_2.filterMap Verdict.kept := by rfl
theorem initial4_2 : (RadiusTwo.familyForKind 4).map (rotatePatch 2 (hexRegion 2)) = rows0_4_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
