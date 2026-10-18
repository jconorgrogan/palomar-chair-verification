module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lambdaStage0 : List (List (Position × State)) := [[((0,0),(3,0))]]
theorem lambdaStage0_exact : Search.enumerate (choices (3,0)) Matches [(0,0)] = lambdaStage0 := by decide
#print axioms lambdaStage0_exact
end SpectreFinite.HexSearch.RadiusOne
