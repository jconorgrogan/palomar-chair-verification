module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock6T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_5 : List (Verdict 6) := [
  .keep patch6_5_0,
  .keep patch6_5_1,
  .keep patch6_5_2,
  .keep patch6_5_3,
  .keep patch6_5_4,
  .keep patch6_5_5,
  .keep patch6_5_6,
  .keep patch6_5_7,
  .keep patch6_5_8,
  .keep patch6_5_9,
  .keep patch6_5_10,
  .keep patch6_5_11,
  .keep patch6_5_12,
  .keep patch6_5_13,
  .keep patch6_5_14,
  .keep patch6_5_15,
  .keep patch6_5_16,
  .keep patch6_5_17]
theorem check0_6_5 : checkRows direction samples trees0 rows0_6_5 = true := by decide
def rows1_6_5 : List (Verdict 6) := [
  .keep patch6_5_0,
  .keep patch6_5_1,
  .keep patch6_5_2,
  .reject patch6_5_3 3,
  .reject patch6_5_4 3,
  .keep patch6_5_5,
  .keep patch6_5_6,
  .reject patch6_5_7 4,
  .reject patch6_5_8 4,
  .keep patch6_5_9,
  .keep patch6_5_10,
  .keep patch6_5_11,
  .keep patch6_5_12,
  .keep patch6_5_13,
  .keep patch6_5_14,
  .keep patch6_5_15,
  .keep patch6_5_16,
  .keep patch6_5_17]
theorem check1_6_5 : checkRows direction samples trees1 rows1_6_5 = true := by decide
theorem link1_6_5 : rows1_6_5.map Verdict.patch = rows0_6_5.filterMap Verdict.kept := by rfl
def rows2_6_5 : List (Verdict 6) := [
  .keep patch6_5_0,
  .keep patch6_5_1,
  .keep patch6_5_2,
  .keep patch6_5_5,
  .keep patch6_5_6,
  .reject patch6_5_9 0,
  .keep patch6_5_10,
  .keep patch6_5_11,
  .keep patch6_5_12,
  .keep patch6_5_13,
  .keep patch6_5_14,
  .keep patch6_5_15,
  .keep patch6_5_16,
  .keep patch6_5_17]
theorem check2_6_5 : checkRows direction samples trees2 rows2_6_5 = true := by decide
theorem link2_6_5 : rows2_6_5.map Verdict.patch = rows1_6_5.filterMap Verdict.kept := by rfl
theorem final_eq6_5 : final6_5 = rows2_6_5.filterMap Verdict.kept := by rfl
theorem initial6_5 : (RadiusTwo.familyForKind 6).map (rotatePatch 5 (hexRegion 2)) = rows0_6_5.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
