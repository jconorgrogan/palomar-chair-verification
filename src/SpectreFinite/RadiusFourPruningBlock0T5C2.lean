module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock0T5C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_0_5_2 : List (RowVerdict 6) := [.keep stateRow0_5_2_0, .keep stateRow0_5_2_1, .keep stateRow0_5_2_2, .keep stateRow0_5_2_3, .keep stateRow0_5_2_4, .keep stateRow0_5_2_5, .keep stateRow0_5_2_6, .keep stateRow0_5_2_7, .keep stateRow0_5_2_8, .keep stateRow0_5_2_9, .keep stateRow0_5_2_10, .keep stateRow0_5_2_11]
def rows0_0_5_2 : List (Verdict 6) := indexedRows0_0_5_2.map (materialize literalDomain)
theorem check0_0_5_2 : checkRows direction samples0 trees0 rows0_0_5_2 = true := by
  rw [rows0_0_5_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_5_2]
  decide
theorem final_eq0_5_2 : final0_5_2 = rows0_0_5_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation0_5_2_0 : rotatedStateRow5 sourceState0_2_0 = stateRow0_5_2_0 := by decide
theorem sourceRowRotation0_5_2_1 : rotatedStateRow5 sourceState0_2_1 = stateRow0_5_2_1 := by decide
theorem sourceRowRotation0_5_2_2 : rotatedStateRow5 sourceState0_2_2 = stateRow0_5_2_2 := by decide
theorem sourceRowRotation0_5_2_3 : rotatedStateRow5 sourceState0_2_3 = stateRow0_5_2_3 := by decide
theorem sourceRowRotation0_5_2_4 : rotatedStateRow5 sourceState0_2_4 = stateRow0_5_2_4 := by decide
theorem sourceRowRotation0_5_2_5 : rotatedStateRow5 sourceState0_2_5 = stateRow0_5_2_5 := by decide
theorem sourceRowRotation0_5_2_6 : rotatedStateRow5 sourceState0_2_6 = stateRow0_5_2_6 := by decide
theorem sourceRowRotation0_5_2_7 : rotatedStateRow5 sourceState0_2_7 = stateRow0_5_2_7 := by decide
theorem sourceRowRotation0_5_2_8 : rotatedStateRow5 sourceState0_2_8 = stateRow0_5_2_8 := by decide
theorem sourceRowRotation0_5_2_9 : rotatedStateRow5 sourceState0_2_9 = stateRow0_5_2_9 := by decide
theorem sourceRowRotation0_5_2_10 : rotatedStateRow5 sourceState0_2_10 = stateRow0_5_2_10 := by decide
theorem sourceRowRotation0_5_2_11 : rotatedStateRow5 sourceState0_2_11 = stateRow0_5_2_11 := by decide
theorem initial0_5_2 : (source0_2).map (rotatePatch 5 (hexRegion 4)) = rows0_0_5_2.map Verdict.patch := by
  rw [sourceStates0_2, sourceStateSplit0_2, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_5_2_0, sourceRowRotation0_5_2_1, sourceRowRotation0_5_2_2, sourceRowRotation0_5_2_3, sourceRowRotation0_5_2_4, sourceRowRotation0_5_2_5, sourceRowRotation0_5_2_6, sourceRowRotation0_5_2_7, sourceRowRotation0_5_2_8, sourceRowRotation0_5_2_9, sourceRowRotation0_5_2_10, sourceRowRotation0_5_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
