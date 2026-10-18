module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock3T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_0 : List (Verdict 6) := [
  .reject patch3_0_0 0,
  .keep patch3_0_1,
  .reject patch3_0_2 0,
  .reject patch3_0_3 2]
theorem check0_3_0 : checkRows direction samples trees0 rows0_3_0 = true := by decide
def rows1_3_0 : List (Verdict 6) := [
  .keep patch3_0_1]
theorem check1_3_0 : checkRows direction samples trees1 rows1_3_0 = true := by decide
theorem link1_3_0 : rows1_3_0.map Verdict.patch = rows0_3_0.filterMap Verdict.kept := by rfl
def rows2_3_0 : List (Verdict 6) := [
  .keep patch3_0_1]
theorem check2_3_0 : checkRows direction samples trees2 rows2_3_0 = true := by decide
theorem link2_3_0 : rows2_3_0.map Verdict.patch = rows1_3_0.filterMap Verdict.kept := by rfl
theorem final_eq3_0 : final3_0 = rows2_3_0.filterMap Verdict.kept := by rfl
theorem initial3_0 : (RadiusTwo.familyForKind 3).map (rotatePatch 0 (hexRegion 2)) = rows0_3_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
