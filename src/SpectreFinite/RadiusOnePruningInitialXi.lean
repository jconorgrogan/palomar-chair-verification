module

public import SpectreFinite.RadiusOneXiStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock4T0
public import SpectreFinite.RadiusOnePruningBlock4T1
public import SpectreFinite.RadiusOnePruningBlock4T2
public import SpectreFinite.RadiusOnePruningBlock4T3
public import SpectreFinite.RadiusOnePruningBlock4T4
public import SpectreFinite.RadiusOnePruningBlock4T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial4_0 : RadiusOne.xiStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_4_0.map Verdict.window).map windowPatch := by decide
theorem initial4_1 : RadiusOne.xiStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_4_1.map Verdict.window).map windowPatch := by decide
theorem initial4_2 : RadiusOne.xiStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_4_2.map Verdict.window).map windowPatch := by decide
theorem initial4_3 : RadiusOne.xiStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_4_3.map Verdict.window).map windowPatch := by decide
theorem initial4_4 : RadiusOne.xiStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_4_4.map Verdict.window).map windowPatch := by decide
theorem initial4_5 : RadiusOne.xiStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_4_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
