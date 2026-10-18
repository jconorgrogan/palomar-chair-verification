module

public import SpectreFinite.RadiusFivePruningBlock7T0C1Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check3_7_0_1 : checkRows direction samples3 trees3 rows3_7_0_1 = true := by
  rw [rows3_7_0_1, checkRows_materialize literalDomain direction samples3 leftIndices3 rightIndices3 leftSignature_index3 rightSignature_index3 trees3 indexedRows3_7_0_1]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
