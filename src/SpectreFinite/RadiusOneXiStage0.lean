module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def xiStage0 : List (List (Position × State)) := [[((0,0),(4,0))]]
theorem xiStage0_exact : Search.enumerate (choices (4,0)) Matches [(0,0)] = xiStage0 := by decide
#print axioms xiStage0_exact
end SpectreFinite.HexSearch.RadiusOne
