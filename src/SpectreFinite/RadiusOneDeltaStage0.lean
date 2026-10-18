module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def deltaStage0 : List (List (Position × State)) := [[((0,0),(1,0))]]
theorem deltaStage0_exact : Search.enumerate (choices (1,0)) Matches [(0,0)] = deltaStage0 := by decide
#print axioms deltaStage0_exact
end SpectreFinite.HexSearch.RadiusOne
