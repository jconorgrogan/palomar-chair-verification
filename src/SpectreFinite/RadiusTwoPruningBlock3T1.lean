module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock3T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_1 : List (Verdict 6) := [
  .reject patch3_1_0 1,
  .keep patch3_1_1,
  .reject patch3_1_2 1,
  .reject patch3_1_3 3]
theorem check0_3_1 : checkRows direction samples trees0 rows0_3_1 = true := by decide
def rows1_3_1 : List (Verdict 6) := [
  .keep patch3_1_1]
theorem check1_3_1 : checkRows direction samples trees1 rows1_3_1 = true := by decide
theorem link1_3_1 : rows1_3_1.map Verdict.patch = rows0_3_1.filterMap Verdict.kept := by rfl
def rows2_3_1 : List (Verdict 6) := [
  .keep patch3_1_1]
theorem check2_3_1 : checkRows direction samples trees2 rows2_3_1 = true := by decide
theorem link2_3_1 : rows2_3_1.map Verdict.patch = rows1_3_1.filterMap Verdict.kept := by rfl
theorem final_eq3_1 : final3_1 = rows2_3_1.filterMap Verdict.kept := by rfl
theorem initial3_1 : (RadiusTwo.familyForKind 3).map (rotatePatch 1 (hexRegion 2)) = rows0_3_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
