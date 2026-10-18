module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock3T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_4 : List (Verdict 6) := [
  .reject patch3_4_0 4,
  .keep patch3_4_1,
  .reject patch3_4_2 0,
  .reject patch3_4_3 0]
theorem check0_3_4 : checkRows direction samples trees0 rows0_3_4 = true := by decide
def rows1_3_4 : List (Verdict 6) := [
  .keep patch3_4_1]
theorem check1_3_4 : checkRows direction samples trees1 rows1_3_4 = true := by decide
theorem link1_3_4 : rows1_3_4.map Verdict.patch = rows0_3_4.filterMap Verdict.kept := by rfl
def rows2_3_4 : List (Verdict 6) := [
  .keep patch3_4_1]
theorem check2_3_4 : checkRows direction samples trees2 rows2_3_4 = true := by decide
theorem link2_3_4 : rows2_3_4.map Verdict.patch = rows1_3_4.filterMap Verdict.kept := by rfl
theorem final_eq3_4 : final3_4 = rows2_3_4.filterMap Verdict.kept := by rfl
theorem initial3_4 : (RadiusTwo.familyForKind 3).map (rotatePatch 4 (hexRegion 2)) = rows0_3_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
