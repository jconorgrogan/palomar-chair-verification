module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot2DataChunk0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root2Outputs : List (List State) := [root2OutputChunk0].flatten
def root2Family : List Patch := rowsToPatches positions root2Outputs
end SpectreFinite.HexSearch.RadiusFive
