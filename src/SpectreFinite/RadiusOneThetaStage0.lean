module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def thetaStage0 : List (List (Position × State)) := [[((0,0),(2,0))]]
theorem thetaStage0_exact : Search.enumerate (choices (2,0)) Matches [(0,0)] = thetaStage0 := by decide
#print axioms thetaStage0_exact
end SpectreFinite.HexSearch.RadiusOne
