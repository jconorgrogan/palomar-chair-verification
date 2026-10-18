module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock3T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_5 : List (Verdict 6) := [
  .reject patch3_5_0 5,
  .keep patch3_5_1,
  .reject patch3_5_2 1,
  .reject patch3_5_3 1]
theorem check0_3_5 : checkRows direction samples trees0 rows0_3_5 = true := by decide
def rows1_3_5 : List (Verdict 6) := [
  .keep patch3_5_1]
theorem check1_3_5 : checkRows direction samples trees1 rows1_3_5 = true := by decide
theorem link1_3_5 : rows1_3_5.map Verdict.patch = rows0_3_5.filterMap Verdict.kept := by rfl
def rows2_3_5 : List (Verdict 6) := [
  .keep patch3_5_1]
theorem check2_3_5 : checkRows direction samples trees2 rows2_3_5 = true := by decide
theorem link2_3_5 : rows2_3_5.map Verdict.patch = rows1_3_5.filterMap Verdict.kept := by rfl
theorem final_eq3_5 : final3_5 = rows2_3_5.filterMap Verdict.kept := by rfl
theorem initial3_5 : (RadiusTwo.familyForKind 3).map (rotatePatch 5 (hexRegion 2)) = rows0_3_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
