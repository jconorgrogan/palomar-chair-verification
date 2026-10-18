module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def psiStage0 : List (List (Position × State)) := [[((0,0),(8,0))]]
theorem psiStage0_exact : Search.enumerate (choices (8,0)) Matches [(0,0)] = psiStage0 := by decide
#print axioms psiStage0_exact
end SpectreFinite.HexSearch.RadiusOne
