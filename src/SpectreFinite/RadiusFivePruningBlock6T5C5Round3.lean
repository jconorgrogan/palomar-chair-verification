module

public import SpectreFinite.RadiusFivePruningBlock6T5C5Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check3_6_5_5 : checkRows direction samples3 trees3 rows3_6_5_5 = true := by
  rw [rows3_6_5_5, checkRows_materialize literalDomain direction samples3 leftIndices3 rightIndices3 leftSignature_index3 rightSignature_index3 trees3 indexedRows3_6_5_5]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
