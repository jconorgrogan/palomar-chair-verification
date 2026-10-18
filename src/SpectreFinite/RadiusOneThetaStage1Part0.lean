module

public import SpectreFinite.RadiusOneThetaStage0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem theta_extend_1_0 : extendRoot (2,0) (-1,0) [((0,0),(2,0))] = [[((-1,0),(0,1)),((0,0),(2,0))],[((-1,0),(1,5)),((0,0),(2,0))],[((-1,0),(6,5)),((0,0),(2,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
