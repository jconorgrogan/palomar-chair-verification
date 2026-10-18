module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piStage0 : List (List (Position × State)) := [[((0,0),(5,0))]]
theorem piStage0_exact : Search.enumerate (choices (5,0)) Matches [(0,0)] = piStage0 := by decide
#print axioms piStage0_exact
end SpectreFinite.HexSearch.RadiusOne
