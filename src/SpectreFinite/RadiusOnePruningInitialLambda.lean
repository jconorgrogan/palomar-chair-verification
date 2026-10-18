module

public import SpectreFinite.RadiusOneLambdaStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock3T0
public import SpectreFinite.RadiusOnePruningBlock3T1
public import SpectreFinite.RadiusOnePruningBlock3T2
public import SpectreFinite.RadiusOnePruningBlock3T3
public import SpectreFinite.RadiusOnePruningBlock3T4
public import SpectreFinite.RadiusOnePruningBlock3T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial3_0 : RadiusOne.lambdaStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_3_0.map Verdict.window).map windowPatch := by decide
theorem initial3_1 : RadiusOne.lambdaStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_3_1.map Verdict.window).map windowPatch := by decide
theorem initial3_2 : RadiusOne.lambdaStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_3_2.map Verdict.window).map windowPatch := by decide
theorem initial3_3 : RadiusOne.lambdaStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_3_3.map Verdict.window).map windowPatch := by decide
theorem initial3_4 : RadiusOne.lambdaStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_3_4.map Verdict.window).map windowPatch := by decide
theorem initial3_5 : RadiusOne.lambdaStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_3_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
