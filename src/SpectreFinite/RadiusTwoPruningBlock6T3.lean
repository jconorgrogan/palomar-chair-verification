module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock6T3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_3 : List (Verdict 6) := [
  .keep patch6_3_0,
  .keep patch6_3_1,
  .keep patch6_3_2,
  .keep patch6_3_3,
  .keep patch6_3_4,
  .keep patch6_3_5,
  .keep patch6_3_6,
  .keep patch6_3_7,
  .keep patch6_3_8,
  .keep patch6_3_9,
  .keep patch6_3_10,
  .keep patch6_3_11,
  .keep patch6_3_12,
  .keep patch6_3_13,
  .keep patch6_3_14,
  .keep patch6_3_15,
  .keep patch6_3_16,
  .keep patch6_3_17]
theorem check0_6_3 : checkRows direction samples trees0 rows0_6_3 = true := by decide
def rows1_6_3 : List (Verdict 6) := [
  .keep patch6_3_0,
  .keep patch6_3_1,
  .keep patch6_3_2,
  .reject patch6_3_3 1,
  .reject patch6_3_4 1,
  .keep patch6_3_5,
  .keep patch6_3_6,
  .reject patch6_3_7 2,
  .reject patch6_3_8 2,
  .keep patch6_3_9,
  .keep patch6_3_10,
  .keep patch6_3_11,
  .keep patch6_3_12,
  .keep patch6_3_13,
  .keep patch6_3_14,
  .keep patch6_3_15,
  .keep patch6_3_16,
  .keep patch6_3_17]
theorem check1_6_3 : checkRows direction samples trees1 rows1_6_3 = true := by decide
theorem link1_6_3 : rows1_6_3.map Verdict.patch = rows0_6_3.filterMap Verdict.kept := by rfl
def rows2_6_3 : List (Verdict 6) := [
  .keep patch6_3_0,
  .keep patch6_3_1,
  .keep patch6_3_2,
  .keep patch6_3_5,
  .keep patch6_3_6,
  .reject patch6_3_9 4,
  .keep patch6_3_10,
  .keep patch6_3_11,
  .keep patch6_3_12,
  .keep patch6_3_13,
  .keep patch6_3_14,
  .keep patch6_3_15,
  .keep patch6_3_16,
  .keep patch6_3_17]
theorem check2_6_3 : checkRows direction samples trees2 rows2_6_3 = true := by decide
theorem link2_6_3 : rows2_6_3.map Verdict.patch = rows1_6_3.filterMap Verdict.kept := by rfl
theorem final_eq6_3 : final6_3 = rows2_6_3.filterMap Verdict.kept := by rfl
theorem initial6_3 : (RadiusTwo.familyForKind 6).map (rotatePatch 3 (hexRegion 2)) = rows0_6_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
