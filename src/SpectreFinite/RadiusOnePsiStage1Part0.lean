module

public import SpectreFinite.RadiusOnePsiStage0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem psi_extend_1_0 : extendRoot (8,0) (-1,0) [((0,0),(8,0))] = [[((-1,0),(0,2)),((0,0),(8,0))],[((-1,0),(1,0)),((0,0),(8,0))],[((-1,0),(3,0)),((0,0),(8,0))],[((-1,0),(5,0)),((0,0),(8,0))],[((-1,0),(6,0)),((0,0),(8,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
