module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot8DataChunk0
public import SpectreFinite.RadiusFiveRoot8DataChunk1
public import SpectreFinite.RadiusFiveRoot8DataChunk2
public import SpectreFinite.RadiusFiveRoot8DataChunk3
public import SpectreFinite.RadiusFiveRoot8DataChunk4
public import SpectreFinite.RadiusFiveRoot8DataChunk5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Outputs : List (List State) := [root8OutputChunk0,root8OutputChunk1,root8OutputChunk2,root8OutputChunk3,root8OutputChunk4,root8OutputChunk5].flatten
def root8Family : List Patch := rowsToPatches positions root8Outputs
end SpectreFinite.HexSearch.RadiusFive
