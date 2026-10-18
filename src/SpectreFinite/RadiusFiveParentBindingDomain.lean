module

public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.ParentOwnershipEncodingBridge

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem literalDomain_eq_hexRegion : RadiusFivePruning.literalDomain = hexRegion 5 := by decide

end SpectreFinite.HexSearch.RadiusFiveParentBinding
