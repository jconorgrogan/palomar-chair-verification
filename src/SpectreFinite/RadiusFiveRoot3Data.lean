module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot3DataChunk0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root3Outputs : List (List State) := [root3OutputChunk0].flatten
def root3Family : List Patch := rowsToPatches positions root3Outputs
end SpectreFinite.HexSearch.RadiusFive
