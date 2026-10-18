module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock6T4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_4 : List (Verdict 6) := [
  .keep patch6_4_0,
  .keep patch6_4_1,
  .keep patch6_4_2,
  .keep patch6_4_3,
  .keep patch6_4_4,
  .keep patch6_4_5,
  .keep patch6_4_6,
  .keep patch6_4_7,
  .keep patch6_4_8,
  .keep patch6_4_9,
  .keep patch6_4_10,
  .keep patch6_4_11,
  .keep patch6_4_12,
  .keep patch6_4_13,
  .keep patch6_4_14,
  .keep patch6_4_15,
  .keep patch6_4_16,
  .keep patch6_4_17]
theorem check0_6_4 : checkRows direction samples trees0 rows0_6_4 = true := by decide
def rows1_6_4 : List (Verdict 6) := [
  .keep patch6_4_0,
  .keep patch6_4_1,
  .keep patch6_4_2,
  .reject patch6_4_3 2,
  .reject patch6_4_4 2,
  .keep patch6_4_5,
  .keep patch6_4_6,
  .reject patch6_4_7 3,
  .reject patch6_4_8 3,
  .keep patch6_4_9,
  .keep patch6_4_10,
  .keep patch6_4_11,
  .keep patch6_4_12,
  .keep patch6_4_13,
  .keep patch6_4_14,
  .keep patch6_4_15,
  .keep patch6_4_16,
  .keep patch6_4_17]
theorem check1_6_4 : checkRows direction samples trees1 rows1_6_4 = true := by decide
theorem link1_6_4 : rows1_6_4.map Verdict.patch = rows0_6_4.filterMap Verdict.kept := by rfl
def rows2_6_4 : List (Verdict 6) := [
  .keep patch6_4_0,
  .keep patch6_4_1,
  .keep patch6_4_2,
  .keep patch6_4_5,
  .keep patch6_4_6,
  .reject patch6_4_9 5,
  .keep patch6_4_10,
  .keep patch6_4_11,
  .keep patch6_4_12,
  .keep patch6_4_13,
  .keep patch6_4_14,
  .keep patch6_4_15,
  .keep patch6_4_16,
  .keep patch6_4_17]
theorem check2_6_4 : checkRows direction samples trees2 rows2_6_4 = true := by decide
theorem link2_6_4 : rows2_6_4.map Verdict.patch = rows1_6_4.filterMap Verdict.kept := by rfl
theorem final_eq6_4 : final6_4 = rows2_6_4.filterMap Verdict.kept := by rfl
theorem initial6_4 : (RadiusTwo.familyForKind 6).map (rotatePatch 4 (hexRegion 2)) = rows0_6_4.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
