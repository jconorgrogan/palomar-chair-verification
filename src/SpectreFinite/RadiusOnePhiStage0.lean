module

public import SpectreFinite.RadiusOneRootCertificates

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def phiStage0 : List (List (Position × State)) := [[((0,0),(7,0))]]
theorem phiStage0_exact : Search.enumerate (choices (7,0)) Matches [(0,0)] = phiStage0 := by decide
#print axioms phiStage0_exact
end SpectreFinite.HexSearch.RadiusOne
