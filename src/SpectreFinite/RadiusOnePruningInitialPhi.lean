module

public import SpectreFinite.RadiusOnePhiStage6
public import SpectreFinite.RotatedWindows
public import SpectreFinite.RadiusOnePruningBlock7T0
public import SpectreFinite.RadiusOnePruningBlock7T1
public import SpectreFinite.RadiusOnePruningBlock7T2
public import SpectreFinite.RadiusOnePruningBlock7T3
public import SpectreFinite.RadiusOnePruningBlock7T4
public import SpectreFinite.RadiusOnePruningBlock7T5

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initial7_0 : RadiusOne.phiStage6.map (rotatePatch 0 RadiusOne.positions) = (rows0_7_0.map Verdict.window).map windowPatch := by decide
theorem initial7_1 : RadiusOne.phiStage6.map (rotatePatch 1 RadiusOne.positions) = (rows0_7_1.map Verdict.window).map windowPatch := by decide
theorem initial7_2 : RadiusOne.phiStage6.map (rotatePatch 2 RadiusOne.positions) = (rows0_7_2.map Verdict.window).map windowPatch := by decide
theorem initial7_3 : RadiusOne.phiStage6.map (rotatePatch 3 RadiusOne.positions) = (rows0_7_3.map Verdict.window).map windowPatch := by decide
theorem initial7_4 : RadiusOne.phiStage6.map (rotatePatch 4 RadiusOne.positions) = (rows0_7_4.map Verdict.window).map windowPatch := by decide
theorem initial7_5 : RadiusOne.phiStage6.map (rotatePatch 5 RadiusOne.positions) = (rows0_7_5.map Verdict.window).map windowPatch := by decide
end SpectreFinite.HexSearch.SignaturePruning
