module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock6T1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_1 : List (Verdict 6) := [
  .keep patch6_1_0,
  .keep patch6_1_1,
  .keep patch6_1_2,
  .keep patch6_1_3,
  .keep patch6_1_4,
  .keep patch6_1_5,
  .keep patch6_1_6,
  .keep patch6_1_7,
  .keep patch6_1_8,
  .keep patch6_1_9,
  .keep patch6_1_10,
  .keep patch6_1_11,
  .keep patch6_1_12,
  .keep patch6_1_13,
  .keep patch6_1_14,
  .keep patch6_1_15,
  .keep patch6_1_16,
  .keep patch6_1_17]
theorem check0_6_1 : checkRows direction samples trees0 rows0_6_1 = true := by decide
def rows1_6_1 : List (Verdict 6) := [
  .keep patch6_1_0,
  .keep patch6_1_1,
  .keep patch6_1_2,
  .reject patch6_1_3 0,
  .reject patch6_1_4 0,
  .keep patch6_1_5,
  .keep patch6_1_6,
  .reject patch6_1_7 0,
  .reject patch6_1_8 0,
  .keep patch6_1_9,
  .keep patch6_1_10,
  .keep patch6_1_11,
  .keep patch6_1_12,
  .keep patch6_1_13,
  .keep patch6_1_14,
  .keep patch6_1_15,
  .keep patch6_1_16,
  .keep patch6_1_17]
theorem check1_6_1 : checkRows direction samples trees1 rows1_6_1 = true := by decide
theorem link1_6_1 : rows1_6_1.map Verdict.patch = rows0_6_1.filterMap Verdict.kept := by rfl
def rows2_6_1 : List (Verdict 6) := [
  .keep patch6_1_0,
  .keep patch6_1_1,
  .keep patch6_1_2,
  .keep patch6_1_5,
  .keep patch6_1_6,
  .reject patch6_1_9 2,
  .keep patch6_1_10,
  .keep patch6_1_11,
  .keep patch6_1_12,
  .keep patch6_1_13,
  .keep patch6_1_14,
  .keep patch6_1_15,
  .keep patch6_1_16,
  .keep patch6_1_17]
theorem check2_6_1 : checkRows direction samples trees2 rows2_6_1 = true := by decide
theorem link2_6_1 : rows2_6_1.map Verdict.patch = rows1_6_1.filterMap Verdict.kept := by rfl
theorem final_eq6_1 : final6_1 = rows2_6_1.filterMap Verdict.kept := by rfl
theorem initial6_1 : (RadiusTwo.familyForKind 6).map (rotatePatch 1 (hexRegion 2)) = rows0_6_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
