module

public import SpectreFinite.RadiusOneGammaStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock0T0
public import SpectreFinite.RadiusOnePruningBlock0T1
public import SpectreFinite.RadiusOnePruningBlock0T2
public import SpectreFinite.RadiusOnePruningBlock0T3
public import SpectreFinite.RadiusOnePruningBlock0T4
public import SpectreFinite.RadiusOnePruningBlock0T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial0_0 : RadiusOne.gammaStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_0_0.map Verdict.window).map windowPatch := by decide
theorem initial0_1 : RadiusOne.gammaStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_0_1.map Verdict.window).map windowPatch := by decide
theorem initial0_2 : RadiusOne.gammaStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_0_2.map Verdict.window).map windowPatch := by decide
theorem initial0_3 : RadiusOne.gammaStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_0_3.map Verdict.window).map windowPatch := by decide
theorem initial0_4 : RadiusOne.gammaStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_0_4.map Verdict.window).map windowPatch := by decide
theorem initial0_5 : RadiusOne.gammaStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_0_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
