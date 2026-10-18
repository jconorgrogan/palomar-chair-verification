module

public import SpectreFinite.RadiusFivePruningBlock1T0C2Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check0_1_0_2 : checkRows direction samples0 trees0 rows0_1_0_2 = true := by
  rw [rows0_1_0_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_1_0_2]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
