module

public import SpectreFinite.RadiusOneThetaStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock2T0
public import SpectreFinite.RadiusOnePruningBlock2T1
public import SpectreFinite.RadiusOnePruningBlock2T2
public import SpectreFinite.RadiusOnePruningBlock2T3
public import SpectreFinite.RadiusOnePruningBlock2T4
public import SpectreFinite.RadiusOnePruningBlock2T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial2_0 : RadiusOne.thetaStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_2_0.map Verdict.window).map windowPatch := by decide
theorem initial2_1 : RadiusOne.thetaStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_2_1.map Verdict.window).map windowPatch := by decide
theorem initial2_2 : RadiusOne.thetaStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_2_2.map Verdict.window).map windowPatch := by decide
theorem initial2_3 : RadiusOne.thetaStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_2_3.map Verdict.window).map windowPatch := by decide
theorem initial2_4 : RadiusOne.thetaStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_2_4.map Verdict.window).map windowPatch := by decide
theorem initial2_5 : RadiusOne.thetaStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_2_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
