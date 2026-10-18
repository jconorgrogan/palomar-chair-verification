module

public import SpectreFinite.RadiusOneSigmaStage0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sigma_extend_1_0 : extendRoot (6,0) (-1,0) [((0,0),(6,0))] = [[((-1,0),(1,4)),((0,0),(6,0))]] := by decide
end SpectreFinite.HexSearch.RadiusOne
