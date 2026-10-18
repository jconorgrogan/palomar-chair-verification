module

public import SpectreFinite.RadiusFiveModel
public import SpectreFinite.RadiusFiveRoot7DataChunk0
public import SpectreFinite.RadiusFiveRoot7DataChunk1
public import SpectreFinite.RadiusFiveRoot7DataChunk2
public import SpectreFinite.RadiusFiveRoot7DataChunk3
public import SpectreFinite.RadiusFiveRoot7DataChunk4
public import SpectreFinite.RadiusFiveRoot7DataChunk5
public import SpectreFinite.RadiusFiveRoot7DataChunk6
public import SpectreFinite.RadiusFiveRoot7DataChunk7
public import SpectreFinite.RadiusFiveRoot7DataChunk8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Outputs : List (List State) := [root7OutputChunk0,root7OutputChunk1,root7OutputChunk2,root7OutputChunk3,root7OutputChunk4,root7OutputChunk5,root7OutputChunk6,root7OutputChunk7,root7OutputChunk8].flatten
def root7Family : List Patch := rowsToPatches positions root7Outputs
end SpectreFinite.HexSearch.RadiusFive
