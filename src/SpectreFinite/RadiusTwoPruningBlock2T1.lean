module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock2T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_1 : List (Verdict 6) := [
  .keep patch2_1_0]
theorem check0_2_1 : checkRows direction samples trees0 rows0_2_1 = true := by decide
def rows1_2_1 : List (Verdict 6) := [
  .keep patch2_1_0]
theorem check1_2_1 : checkRows direction samples trees1 rows1_2_1 = true := by decide
theorem link1_2_1 : rows1_2_1.map Verdict.patch = rows0_2_1.filterMap Verdict.kept := by rfl
def rows2_2_1 : List (Verdict 6) := [
  .keep patch2_1_0]
theorem check2_2_1 : checkRows direction samples trees2 rows2_2_1 = true := by decide
theorem link2_2_1 : rows2_2_1.map Verdict.patch = rows1_2_1.filterMap Verdict.kept := by rfl
theorem final_eq2_1 : final2_1 = rows2_2_1.filterMap Verdict.kept := by rfl
theorem initial2_1 : (RadiusTwo.familyForKind 2).map (rotatePatch 1 (hexRegion 2)) = rows0_2_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
