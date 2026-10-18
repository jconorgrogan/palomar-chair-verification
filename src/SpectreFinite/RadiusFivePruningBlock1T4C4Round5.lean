module

public import SpectreFinite.RadiusFivePruningBlock1T4C4Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check5_1_4_4 : checkRows direction samples5 trees5 rows5_1_4_4 = true := by
  rw [rows5_1_4_4, checkRows_materialize literalDomain direction samples5 leftIndices5 rightIndices5 leftSignature_index5 rightSignature_index5 trees5 indexedRows5_1_4_4]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
