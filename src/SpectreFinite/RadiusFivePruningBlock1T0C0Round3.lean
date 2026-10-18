module

public import SpectreFinite.RadiusFivePruningBlock1T0C0Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check3_1_0_0 : checkRows direction samples3 trees3 rows3_1_0_0 = true := by
  rw [rows3_1_0_0, checkRows_materialize literalDomain direction samples3 leftIndices3 rightIndices3 leftSignature_index3 rightSignature_index3 trees3 indexedRows3_1_0_0]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
