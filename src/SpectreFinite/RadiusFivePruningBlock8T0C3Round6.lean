module

public import SpectreFinite.RadiusFivePruningBlock8T0C3Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check6_8_0_3 : checkRows direction samples6 trees6 rows6_8_0_3 = true := by
  rw [rows6_8_0_3, checkRows_materialize literalDomain direction samples6 leftIndices6 rightIndices6 leftSignature_index6 rightSignature_index6 trees6 indexedRows6_8_0_3]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
