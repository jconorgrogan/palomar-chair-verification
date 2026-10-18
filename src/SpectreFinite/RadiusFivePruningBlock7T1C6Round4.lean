module

public import SpectreFinite.RadiusFivePruningBlock7T1C6Data
public import SpectreFinite.RadiusFivePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem check4_7_1_6 : checkRows direction samples4 trees4 rows4_7_1_6 = true := by
  rw [rows4_7_1_6, checkRows_materialize literalDomain direction samples4 leftIndices4 rightIndices4 leftSignature_index4 rightSignature_index4 trees4 indexedRows4_7_1_6]
  decide

end SpectreFinite.HexSearch.RadiusFivePruning
