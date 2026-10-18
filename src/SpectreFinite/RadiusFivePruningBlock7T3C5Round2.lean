module

public import SpectreFinite.RadiusFivePruningBlock7T3C5Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check2_7_3_5 : checkRows direction samples2 trees2 rows2_7_3_5 = true := by
  rw [rows2_7_3_5, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_7_3_5]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
