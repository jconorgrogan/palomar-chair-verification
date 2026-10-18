module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock2T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_0 : List (Verdict 6) := [
  .keep patch2_0_0]
theorem check0_2_0 : checkRows direction samples trees0 rows0_2_0 = true := by decide
def rows1_2_0 : List (Verdict 6) := [
  .keep patch2_0_0]
theorem check1_2_0 : checkRows direction samples trees1 rows1_2_0 = true := by decide
theorem link1_2_0 : rows1_2_0.map Verdict.patch = rows0_2_0.filterMap Verdict.kept := by rfl
def rows2_2_0 : List (Verdict 6) := [
  .keep patch2_0_0]
theorem check2_2_0 : checkRows direction samples trees2 rows2_2_0 = true := by decide
theorem link2_2_0 : rows2_2_0.map Verdict.patch = rows1_2_0.filterMap Verdict.kept := by rfl
theorem final_eq2_0 : final2_0 = rows2_2_0.filterMap Verdict.kept := by rfl
theorem initial2_0 : (RadiusTwo.familyForKind 2).map (rotatePatch 0 (hexRegion 2)) = rows0_2_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
