module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock5T5C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_5_5_1 : List (RowVerdict 6) := [.keep stateRow5_5_1_0, .keep stateRow5_5_1_1, .keep stateRow5_5_1_2, .keep stateRow5_5_1_3, .keep stateRow5_5_1_4, .keep stateRow5_5_1_5, .keep stateRow5_5_1_6, .keep stateRow5_5_1_7, .keep stateRow5_5_1_8, .keep stateRow5_5_1_9, .keep stateRow5_5_1_10, .keep stateRow5_5_1_11]
def rows0_5_5_1 : List (Verdict 6) := indexedRows0_5_5_1.map (materialize literalDomain)
theorem check0_5_5_1 : checkRows direction samples0 trees0 rows0_5_5_1 = true := by
  rw [rows0_5_5_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_5_5_1]
  decide
theorem final_eq5_5_1 : final5_5_1 = rows0_5_5_1.filterMap Verdict.kept := by rfl
theorem sourceRowRotation5_5_1_0 : rotatedStateRow5 sourceState5_1_0 = stateRow5_5_1_0 := by decide
theorem sourceRowRotation5_5_1_1 : rotatedStateRow5 sourceState5_1_1 = stateRow5_5_1_1 := by decide
theorem sourceRowRotation5_5_1_2 : rotatedStateRow5 sourceState5_1_2 = stateRow5_5_1_2 := by decide
theorem sourceRowRotation5_5_1_3 : rotatedStateRow5 sourceState5_1_3 = stateRow5_5_1_3 := by decide
theorem sourceRowRotation5_5_1_4 : rotatedStateRow5 sourceState5_1_4 = stateRow5_5_1_4 := by decide
theorem sourceRowRotation5_5_1_5 : rotatedStateRow5 sourceState5_1_5 = stateRow5_5_1_5 := by decide
theorem sourceRowRotation5_5_1_6 : rotatedStateRow5 sourceState5_1_6 = stateRow5_5_1_6 := by decide
theorem sourceRowRotation5_5_1_7 : rotatedStateRow5 sourceState5_1_7 = stateRow5_5_1_7 := by decide
theorem sourceRowRotation5_5_1_8 : rotatedStateRow5 sourceState5_1_8 = stateRow5_5_1_8 := by decide
theorem sourceRowRotation5_5_1_9 : rotatedStateRow5 sourceState5_1_9 = stateRow5_5_1_9 := by decide
theorem sourceRowRotation5_5_1_10 : rotatedStateRow5 sourceState5_1_10 = stateRow5_5_1_10 := by decide
theorem sourceRowRotation5_5_1_11 : rotatedStateRow5 sourceState5_1_11 = stateRow5_5_1_11 := by decide
theorem initial5_5_1 : (source5_1).map (rotatePatch 5 (hexRegion 4)) = rows0_5_5_1.map Verdict.patch := by
  rw [sourceStates5_1, sourceStateSplit5_1, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation5_5_1_0, sourceRowRotation5_5_1_1, sourceRowRotation5_5_1_2, sourceRowRotation5_5_1_3, sourceRowRotation5_5_1_4, sourceRowRotation5_5_1_5, sourceRowRotation5_5_1_6, sourceRowRotation5_5_1_7, sourceRowRotation5_5_1_8, sourceRowRotation5_5_1_9, sourceRowRotation5_5_1_10, sourceRowRotation5_5_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
