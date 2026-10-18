module

public import SpectreFinite.RadiusFivePruningBlock8T2C3Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check3_8_2_3 : checkRows direction samples3 trees3 rows3_8_2_3 = true := by
  rw [rows3_8_2_3, checkRows_materialize literalDomain direction samples3 leftIndices3 rightIndices3 leftSignature_index3 rightSignature_index3 trees3 indexedRows3_8_2_3]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
