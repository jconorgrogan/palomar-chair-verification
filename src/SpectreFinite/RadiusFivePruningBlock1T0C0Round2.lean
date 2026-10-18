module

public import SpectreFinite.RadiusFivePruningBlock1T0C0Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check2_1_0_0 : checkRows direction samples2 trees2 rows2_1_0_0 = true := by
  rw [rows2_1_0_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_1_0_0]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
