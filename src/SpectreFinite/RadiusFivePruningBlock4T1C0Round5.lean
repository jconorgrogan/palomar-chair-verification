module

public import SpectreFinite.RadiusFivePruningBlock4T1C0Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check5_4_1_0 : checkRows direction samples5 trees5 rows5_4_1_0 = true := by
  rw [rows5_4_1_0, checkRows_materialize literalDomain direction samples5 leftIndices5 rightIndices5 leftSignature_index5 rightSignature_index5 trees5 indexedRows5_4_1_0]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
