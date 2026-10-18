module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock6T2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_2 : List (Verdict 6) := [
  .keep patch6_2_0,
  .keep patch6_2_1,
  .keep patch6_2_2,
  .keep patch6_2_3,
  .keep patch6_2_4,
  .keep patch6_2_5,
  .keep patch6_2_6,
  .keep patch6_2_7,
  .keep patch6_2_8,
  .keep patch6_2_9,
  .keep patch6_2_10,
  .keep patch6_2_11,
  .keep patch6_2_12,
  .keep patch6_2_13,
  .keep patch6_2_14,
  .keep patch6_2_15,
  .keep patch6_2_16,
  .keep patch6_2_17]
theorem check0_6_2 : checkRows direction samples trees0 rows0_6_2 = true := by decide
def rows1_6_2 : List (Verdict 6) := [
  .keep patch6_2_0,
  .keep patch6_2_1,
  .keep patch6_2_2,
  .reject patch6_2_3 0,
  .reject patch6_2_4 0,
  .keep patch6_2_5,
  .keep patch6_2_6,
  .reject patch6_2_7 1,
  .reject patch6_2_8 1,
  .keep patch6_2_9,
  .keep patch6_2_10,
  .keep patch6_2_11,
  .keep patch6_2_12,
  .keep patch6_2_13,
  .keep patch6_2_14,
  .keep patch6_2_15,
  .keep patch6_2_16,
  .keep patch6_2_17]
theorem check1_6_2 : checkRows direction samples trees1 rows1_6_2 = true := by decide
theorem link1_6_2 : rows1_6_2.map Verdict.patch = rows0_6_2.filterMap Verdict.kept := by rfl
def rows2_6_2 : List (Verdict 6) := [
  .keep patch6_2_0,
  .keep patch6_2_1,
  .keep patch6_2_2,
  .keep patch6_2_5,
  .keep patch6_2_6,
  .reject patch6_2_9 3,
  .keep patch6_2_10,
  .keep patch6_2_11,
  .keep patch6_2_12,
  .keep patch6_2_13,
  .keep patch6_2_14,
  .keep patch6_2_15,
  .keep patch6_2_16,
  .keep patch6_2_17]
theorem check2_6_2 : checkRows direction samples trees2 rows2_6_2 = true := by decide
theorem link2_6_2 : rows2_6_2.map Verdict.patch = rows1_6_2.filterMap Verdict.kept := by rfl
theorem final_eq6_2 : final6_2 = rows2_6_2.filterMap Verdict.kept := by rfl
theorem initial6_2 : (RadiusTwo.familyForKind 6).map (rotatePatch 2 (hexRegion 2)) = rows0_6_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
