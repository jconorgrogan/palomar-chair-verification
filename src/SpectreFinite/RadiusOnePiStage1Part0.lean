module

public import SpectreFinite.RadiusOnePiStage0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem pi_extend_1_0 : extendRoot (5,0) (-1,0) [((0,0),(5,0))] = [[((-1,0),(0,2)),((0,0),(5,0))],[((-1,0),(1,0)),((0,0),(5,0))],[((-1,0),(3,0)),((0,0),(5,0))],[((-1,0),(5,0)),((0,0),(5,0))],[((-1,0),(6,0)),((0,0),(5,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
