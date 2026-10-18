module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def sigmaStage0 : List (List (Position × State)) := [[((0,0),(6,0))]]
theorem sigmaStage0_exact : Search.enumerate (choices (6,0)) Matches [(0,0)] = sigmaStage0 := by decide
#print axioms sigmaStage0_exact
end SpectreFinite.HexSearch.RadiusOne
