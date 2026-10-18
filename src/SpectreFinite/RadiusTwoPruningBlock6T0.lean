module

public import SpectreFinite.RadiusTwoPruningTrees
public import SpectreFinite.RadiusTwoCertified
public import SpectreFinite.RadiusTwoPruningLiteralBlock6T0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_6_0 : List (Verdict 6) := [
  .keep patch6_0_0,
  .keep patch6_0_1,
  .keep patch6_0_2,
  .keep patch6_0_3,
  .keep patch6_0_4,
  .keep patch6_0_5,
  .keep patch6_0_6,
  .keep patch6_0_7,
  .keep patch6_0_8,
  .keep patch6_0_9,
  .keep patch6_0_10,
  .keep patch6_0_11,
  .keep patch6_0_12,
  .keep patch6_0_13,
  .keep patch6_0_14,
  .keep patch6_0_15,
  .keep patch6_0_16,
  .keep patch6_0_17]
theorem check0_6_0 : checkRows direction samples trees0 rows0_6_0 = true := by decide
def rows1_6_0 : List (Verdict 6) := [
  .keep patch6_0_0,
  .keep patch6_0_1,
  .keep patch6_0_2,
  .reject patch6_0_3 4,
  .reject patch6_0_4 4,
  .keep patch6_0_5,
  .keep patch6_0_6,
  .reject patch6_0_7 5,
  .reject patch6_0_8 5,
  .keep patch6_0_9,
  .keep patch6_0_10,
  .keep patch6_0_11,
  .keep patch6_0_12,
  .keep patch6_0_13,
  .keep patch6_0_14,
  .keep patch6_0_15,
  .keep patch6_0_16,
  .keep patch6_0_17]
theorem check1_6_0 : checkRows direction samples trees1 rows1_6_0 = true := by decide
theorem link1_6_0 : rows1_6_0.map Verdict.patch = rows0_6_0.filterMap Verdict.kept := by rfl
def rows2_6_0 : List (Verdict 6) := [
  .keep patch6_0_0,
  .keep patch6_0_1,
  .keep patch6_0_2,
  .keep patch6_0_5,
  .keep patch6_0_6,
  .reject patch6_0_9 1,
  .keep patch6_0_10,
  .keep patch6_0_11,
  .keep patch6_0_12,
  .keep patch6_0_13,
  .keep patch6_0_14,
  .keep patch6_0_15,
  .keep patch6_0_16,
  .keep patch6_0_17]
theorem check2_6_0 : checkRows direction samples trees2 rows2_6_0 = true := by decide
theorem link2_6_0 : rows2_6_0.map Verdict.patch = rows1_6_0.filterMap Verdict.kept := by rfl
theorem final_eq6_0 : final6_0 = rows2_6_0.filterMap Verdict.kept := by rfl
theorem initial6_0 : (RadiusTwo.familyForKind 6).map (rotatePatch 0 (hexRegion 2)) = rows0_6_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
