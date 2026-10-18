module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot1DataChunk0
public import SpectreFinite.RadiusFiveRoot1DataChunk1
public import SpectreFinite.RadiusFiveRoot1DataChunk2
public import SpectreFinite.RadiusFiveRoot1DataChunk3
public import SpectreFinite.RadiusFiveRoot1DataChunk4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Outputs : List (List State) := [root1OutputChunk0,root1OutputChunk1,root1OutputChunk2,root1OutputChunk3,root1OutputChunk4].flatten
def root1Family : List Patch := rowsToPatches positions root1Outputs
end SpectreFinite.HexSearch.RadiusFive
