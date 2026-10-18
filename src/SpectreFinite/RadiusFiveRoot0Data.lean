module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot0DataChunk0
public import SpectreFinite.RadiusFiveRoot0DataChunk1
public import SpectreFinite.RadiusFiveRoot0DataChunk2
public import SpectreFinite.RadiusFiveRoot0DataChunk3
public import SpectreFinite.RadiusFiveRoot0DataChunk4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Outputs : List (List State) := [root0OutputChunk0,root0OutputChunk1,root0OutputChunk2,root0OutputChunk3,root0OutputChunk4].flatten
def root0Family : List Patch := rowsToPatches positions root0Outputs
end SpectreFinite.HexSearch.RadiusFive
