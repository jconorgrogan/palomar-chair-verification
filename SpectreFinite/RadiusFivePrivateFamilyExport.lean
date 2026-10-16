module

public import SpectreFinite.RadiusFiveFamilyData
meta import SpectreFinite.RadiusFiveFamilyData

@[expose] public section

open SpectreFinite.HexSearch
#eval RadiusFive.allTurnFamily.map (fun p => p.map (fun a => 6 * a.2.1.val + a.2.2.val))
