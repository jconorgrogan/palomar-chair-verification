module

public import SpectreFinite.RadiusFivePruningBlock0T5C0Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check6_0_5_0 : checkRows direction samples6 trees6 rows6_0_5_0 = true := by
  rw [rows6_0_5_0, checkRows_materialize literalDomain direction samples6 leftIndices6 rightIndices6 leftSignature_index6 rightSignature_index6 trees6 indexedRows6_0_5_0]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
