module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot6DataChunk0
public import SpectreFinite.RadiusFiveRoot6DataChunk1
public import SpectreFinite.RadiusFiveRoot6DataChunk2
public import SpectreFinite.RadiusFiveRoot6DataChunk3
public import SpectreFinite.RadiusFiveRoot6DataChunk4
public import SpectreFinite.RadiusFiveRoot6DataChunk5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Outputs : List (List State) := [root6OutputChunk0,root6OutputChunk1,root6OutputChunk2,root6OutputChunk3,root6OutputChunk4,root6OutputChunk5].flatten
def root6Family : List Patch := rowsToPatches positions root6Outputs
end SpectreFinite.HexSearch.RadiusFive
