module

public import SpectreFinite.RadiusFivePruningBlock0T3C4Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check2_0_3_4 : checkRows direction samples2 trees2 rows2_0_3_4 = true := by
  rw [rows2_0_3_4, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_0_3_4]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
