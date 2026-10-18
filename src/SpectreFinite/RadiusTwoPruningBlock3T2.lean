module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock3T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_2 : List (Verdict 6) := [
  .reject patch3_2_0 2,
  .keep patch3_2_1,
  .reject patch3_2_2 0,
  .reject patch3_2_3 0]
theorem check0_3_2 : checkRows direction samples trees0 rows0_3_2 = true := by decide
def rows1_3_2 : List (Verdict 6) := [
  .keep patch3_2_1]
theorem check1_3_2 : checkRows direction samples trees1 rows1_3_2 = true := by decide
theorem link1_3_2 : rows1_3_2.map Verdict.patch = rows0_3_2.filterMap Verdict.kept := by rfl
def rows2_3_2 : List (Verdict 6) := [
  .keep patch3_2_1]
theorem check2_3_2 : checkRows direction samples trees2 rows2_3_2 = true := by decide
theorem link2_3_2 : rows2_3_2.map Verdict.patch = rows1_3_2.filterMap Verdict.kept := by rfl
theorem final_eq3_2 : final3_2 = rows2_3_2.filterMap Verdict.kept := by rfl
theorem initial3_2 : (RadiusTwo.familyForKind 3).map (rotatePatch 2 (hexRegion 2)) = rows0_3_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
