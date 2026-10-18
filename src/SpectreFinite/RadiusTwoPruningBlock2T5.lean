module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock2T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_5 : List (Verdict 6) := [
  .keep patch2_5_0]
theorem check0_2_5 : checkRows direction samples trees0 rows0_2_5 = true := by decide
def rows1_2_5 : List (Verdict 6) := [
  .keep patch2_5_0]
theorem check1_2_5 : checkRows direction samples trees1 rows1_2_5 = true := by decide
theorem link1_2_5 : rows1_2_5.map Verdict.patch = rows0_2_5.filterMap Verdict.kept := by rfl
def rows2_2_5 : List (Verdict 6) := [
  .keep patch2_5_0]
theorem check2_2_5 : checkRows direction samples trees2 rows2_2_5 = true := by decide
theorem link2_2_5 : rows2_2_5.map Verdict.patch = rows1_2_5.filterMap Verdict.kept := by rfl
theorem final_eq2_5 : final2_5 = rows2_2_5.filterMap Verdict.kept := by rfl
theorem initial2_5 : (RadiusTwo.familyForKind 2).map (rotatePatch 5 (hexRegion 2)) = rows0_2_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
