module

public import SpectreFinite.RadiusFivePruningBlock7T5C6Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check1_7_5_6 : checkRows direction samples1 trees1 rows1_7_5_6 = true := by
  rw [rows1_7_5_6, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_7_5_6]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
