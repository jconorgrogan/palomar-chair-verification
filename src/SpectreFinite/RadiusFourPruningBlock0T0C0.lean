module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningLiteralBlock0T0C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_2, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_7, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows0_0_0_0 : List (Verdict 6) := indexedRows0_0_0_0.map (materialize literalDomain)
theorem check0_0_0_0 : checkRows direction samples0 trees0 rows0_0_0_0 = true := by
  rw [rows0_0_0_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_0_0]
  decide
theorem final_eq0_0_0 : final0_0_0 = rows0_0_0_0.filterMap Verdict.kept := by rfl
theorem initial0_0_0 : (source0_0).map (rotatePatch 0 (hexRegion 4)) = rows0_0_0_0.map Verdict.patch := by
  rw [sourceStates0_0, rotateCanonical_map0]
  decide

end SpectreFinite.HexSearch.RadiusFourPruning
