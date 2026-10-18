module

public import SpectreFinite.RadiusOnePhiStage0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem phi_extend_1_0 : extendRoot (7,0) (-1,0) [((0,0),(7,0))] = [[((-1,0),(0,1)),((0,0),(7,0))],[((-1,0),(1,5)),((0,0),(7,0))],[((-1,0),(6,5)),((0,0),(7,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
