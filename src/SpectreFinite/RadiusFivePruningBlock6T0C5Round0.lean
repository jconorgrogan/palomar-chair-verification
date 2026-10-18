module

public import SpectreFinite.RadiusFivePruningBlock6T0C5Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check0_6_0_5 : checkRows direction samples0 trees0 rows0_6_0_5 = true := by
  rw [rows0_6_0_5, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_6_0_5]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
