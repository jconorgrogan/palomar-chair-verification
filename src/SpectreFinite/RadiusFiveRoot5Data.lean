module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot5DataChunk0
public import SpectreFinite.RadiusFiveRoot5DataChunk1
public import SpectreFinite.RadiusFiveRoot5DataChunk2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root5Outputs : List (List State) := [root5OutputChunk0,root5OutputChunk1,root5OutputChunk2].flatten
def root5Family : List Patch := rowsToPatches positions root5Outputs
end SpectreFinite.HexSearch.RadiusFive
