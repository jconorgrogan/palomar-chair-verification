module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock0T5C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_0_5_1 : List (RowVerdict 6) := [.keep stateRow0_5_1_0, .keep stateRow0_5_1_1, .keep stateRow0_5_1_2, .keep stateRow0_5_1_3, .keep stateRow0_5_1_4, .keep stateRow0_5_1_5, .keep stateRow0_5_1_6, .keep stateRow0_5_1_7, .keep stateRow0_5_1_8, .keep stateRow0_5_1_9, .keep stateRow0_5_1_10, .keep stateRow0_5_1_11]
def rows0_0_5_1 : List (Verdict 6) := indexedRows0_0_5_1.map (materialize literalDomain)
theorem check0_0_5_1 : checkRows direction samples0 trees0 rows0_0_5_1 = true := by
  rw [rows0_0_5_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_5_1]
  decide
theorem final_eq0_5_1 : final0_5_1 = rows0_0_5_1.filterMap Verdict.kept := by rfl
theorem sourceRowRotation0_5_1_0 : rotatedStateRow5 sourceState0_1_0 = stateRow0_5_1_0 := by decide
theorem sourceRowRotation0_5_1_1 : rotatedStateRow5 sourceState0_1_1 = stateRow0_5_1_1 := by decide
theorem sourceRowRotation0_5_1_2 : rotatedStateRow5 sourceState0_1_2 = stateRow0_5_1_2 := by decide
theorem sourceRowRotation0_5_1_3 : rotatedStateRow5 sourceState0_1_3 = stateRow0_5_1_3 := by decide
theorem sourceRowRotation0_5_1_4 : rotatedStateRow5 sourceState0_1_4 = stateRow0_5_1_4 := by decide
theorem sourceRowRotation0_5_1_5 : rotatedStateRow5 sourceState0_1_5 = stateRow0_5_1_5 := by decide
theorem sourceRowRotation0_5_1_6 : rotatedStateRow5 sourceState0_1_6 = stateRow0_5_1_6 := by decide
theorem sourceRowRotation0_5_1_7 : rotatedStateRow5 sourceState0_1_7 = stateRow0_5_1_7 := by decide
theorem sourceRowRotation0_5_1_8 : rotatedStateRow5 sourceState0_1_8 = stateRow0_5_1_8 := by decide
theorem sourceRowRotation0_5_1_9 : rotatedStateRow5 sourceState0_1_9 = stateRow0_5_1_9 := by decide
theorem sourceRowRotation0_5_1_10 : rotatedStateRow5 sourceState0_1_10 = stateRow0_5_1_10 := by decide
theorem sourceRowRotation0_5_1_11 : rotatedStateRow5 sourceState0_1_11 = stateRow0_5_1_11 := by decide
theorem initial0_5_1 : (source0_1).map (rotatePatch 5 (hexRegion 4)) = rows0_0_5_1.map Verdict.patch := by
  rw [sourceStates0_1, sourceStateSplit0_1, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_5_1_0, sourceRowRotation0_5_1_1, sourceRowRotation0_5_1_2, sourceRowRotation0_5_1_3, sourceRowRotation0_5_1_4, sourceRowRotation0_5_1_5, sourceRowRotation0_5_1_6, sourceRowRotation0_5_1_7, sourceRowRotation0_5_1_8, sourceRowRotation0_5_1_9, sourceRowRotation0_5_1_10, sourceRowRotation0_5_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
