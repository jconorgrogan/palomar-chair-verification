module

public import SpectreFinite.RadiusFivePruningBlock7T3C6Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check0_7_3_6 : checkRows direction samples0 trees0 rows0_7_3_6 = true := by
  rw [rows0_7_3_6, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_3_6]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
