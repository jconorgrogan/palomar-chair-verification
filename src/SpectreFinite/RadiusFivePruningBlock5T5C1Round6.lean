module

public import SpectreFinite.RadiusFivePruningBlock5T5C1Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check6_5_5_1 : checkRows direction samples6 trees6 rows6_5_5_1 = true := by
  rw [rows6_5_5_1, checkRows_materialize literalDomain direction samples6 leftIndices6 rightIndices6 leftSignature_index6 rightSignature_index6 trees6 indexedRows6_5_5_1]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
