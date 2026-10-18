module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot4DataChunk0
public import SpectreFinite.RadiusFiveRoot4DataChunk1
public import SpectreFinite.RadiusFiveRoot4DataChunk2
public import SpectreFinite.RadiusFiveRoot4DataChunk3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Outputs : List (List State) := [root4OutputChunk0,root4OutputChunk1,root4OutputChunk2,root4OutputChunk3].flatten
def root4Family : List Patch := rowsToPatches positions root4Outputs
end SpectreFinite.HexSearch.RadiusFive
