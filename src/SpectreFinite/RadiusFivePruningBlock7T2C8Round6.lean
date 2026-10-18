module

public import SpectreFinite.RadiusFivePruningBlock7T2C8Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check6_7_2_8 : checkRows direction samples6 trees6 rows6_7_2_8 = true := by
  rw [rows6_7_2_8, checkRows_materialize literalDomain direction samples6 leftIndices6 rightIndices6 leftSignature_index6 rightSignature_index6 trees6 indexedRows6_7_2_8]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
