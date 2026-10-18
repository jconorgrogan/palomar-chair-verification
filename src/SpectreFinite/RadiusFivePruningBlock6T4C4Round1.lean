module

public import SpectreFinite.RadiusFivePruningBlock6T4C4Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check1_6_4_4 : checkRows direction samples1 trees1 rows1_6_4_4 = true := by
  rw [rows1_6_4_4, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_6_4_4]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
