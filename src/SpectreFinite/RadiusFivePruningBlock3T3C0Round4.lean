module

public import SpectreFinite.RadiusFivePruningBlock3T3C0Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check4_3_3_0 : checkRows direction samples4 trees4 rows4_3_3_0 = true := by
  rw [rows4_3_3_0, checkRows_materialize literalDomain direction samples4 leftIndices4 rightIndices4 leftSignature_index4 rightSignature_index4 trees4 indexedRows4_3_3_0]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
