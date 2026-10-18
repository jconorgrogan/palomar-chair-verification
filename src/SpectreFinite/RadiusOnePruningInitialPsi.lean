module

public import SpectreFinite.RadiusOnePsiStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock8T0
public import SpectreFinite.RadiusOnePruningBlock8T1
public import SpectreFinite.RadiusOnePruningBlock8T2
public import SpectreFinite.RadiusOnePruningBlock8T3
public import SpectreFinite.RadiusOnePruningBlock8T4
public import SpectreFinite.RadiusOnePruningBlock8T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial8_0 : RadiusOne.psiStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_8_0.map Verdict.window).map windowPatch := by decide
theorem initial8_1 : RadiusOne.psiStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_8_1.map Verdict.window).map windowPatch := by decide
theorem initial8_2 : RadiusOne.psiStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_8_2.map Verdict.window).map windowPatch := by decide
theorem initial8_3 : RadiusOne.psiStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_8_3.map Verdict.window).map windowPatch := by decide
theorem initial8_4 : RadiusOne.psiStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_8_4.map Verdict.window).map windowPatch := by decide
theorem initial8_5 : RadiusOne.psiStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_8_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
