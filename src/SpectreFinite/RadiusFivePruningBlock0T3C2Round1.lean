module

public import SpectreFinite.RadiusFivePruningBlock0T3C2Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check1_0_3_2 : checkRows direction samples1 trees1 rows1_0_3_2 = true := by
  rw [rows1_0_3_2, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_0_3_2]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
