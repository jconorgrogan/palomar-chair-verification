module

public import SpectreFinite.RadiusOneDeltaStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock1T0
public import SpectreFinite.RadiusOnePruningBlock1T1
public import SpectreFinite.RadiusOnePruningBlock1T2
public import SpectreFinite.RadiusOnePruningBlock1T3
public import SpectreFinite.RadiusOnePruningBlock1T4
public import SpectreFinite.RadiusOnePruningBlock1T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial1_0 : RadiusOne.deltaStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_1_0.map Verdict.window).map windowPatch := by decide
theorem initial1_1 : RadiusOne.deltaStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_1_1.map Verdict.window).map windowPatch := by decide
theorem initial1_2 : RadiusOne.deltaStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_1_2.map Verdict.window).map windowPatch := by decide
theorem initial1_3 : RadiusOne.deltaStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_1_3.map Verdict.window).map windowPatch := by decide
theorem initial1_4 : RadiusOne.deltaStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_1_4.map Verdict.window).map windowPatch := by decide
theorem initial1_5 : RadiusOne.deltaStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_1_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
