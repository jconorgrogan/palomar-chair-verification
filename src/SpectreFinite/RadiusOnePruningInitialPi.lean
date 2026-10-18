module

public import SpectreFinite.RadiusOnePiStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock5T0
public import SpectreFinite.RadiusOnePruningBlock5T1
public import SpectreFinite.RadiusOnePruningBlock5T2
public import SpectreFinite.RadiusOnePruningBlock5T3
public import SpectreFinite.RadiusOnePruningBlock5T4
public import SpectreFinite.RadiusOnePruningBlock5T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial5_0 : RadiusOne.piStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_5_0.map Verdict.window).map windowPatch := by decide
theorem initial5_1 : RadiusOne.piStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_5_1.map Verdict.window).map windowPatch := by decide
theorem initial5_2 : RadiusOne.piStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_5_2.map Verdict.window).map windowPatch := by decide
theorem initial5_3 : RadiusOne.piStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_5_3.map Verdict.window).map windowPatch := by decide
theorem initial5_4 : RadiusOne.piStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_5_4.map Verdict.window).map windowPatch := by decide
theorem initial5_5 : RadiusOne.piStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_5_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
