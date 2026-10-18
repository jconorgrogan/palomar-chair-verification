module

public import SpectreFinite.RadiusOneSigmaStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock6T0
public import SpectreFinite.RadiusOnePruningBlock6T1
public import SpectreFinite.RadiusOnePruningBlock6T2
public import SpectreFinite.RadiusOnePruningBlock6T3
public import SpectreFinite.RadiusOnePruningBlock6T4
public import SpectreFinite.RadiusOnePruningBlock6T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial6_0 : RadiusOne.sigmaStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_6_0.map Verdict.window).map windowPatch := by decide
theorem initial6_1 : RadiusOne.sigmaStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_6_1.map Verdict.window).map windowPatch := by decide
theorem initial6_2 : RadiusOne.sigmaStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_6_2.map Verdict.window).map windowPatch := by decide
theorem initial6_3 : RadiusOne.sigmaStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_6_3.map Verdict.window).map windowPatch := by decide
theorem initial6_4 : RadiusOne.sigmaStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_6_4.map Verdict.window).map windowPatch := by decide
theorem initial6_5 : RadiusOne.sigmaStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_6_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
