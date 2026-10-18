module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock5T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_5_3_0 : List (RowVerdict 6) := [.keep stateRow5_3_0_0, .keep stateRow5_3_0_1, .keep stateRow5_3_0_2, .keep stateRow5_3_0_3, .keep stateRow5_3_0_4, .keep stateRow5_3_0_5, .keep stateRow5_3_0_6, .keep stateRow5_3_0_7, .keep stateRow5_3_0_8, .keep stateRow5_3_0_9, .keep stateRow5_3_0_10, .keep stateRow5_3_0_11]
def rows0_5_3_0 : List (Verdict 6) := indexedRows0_5_3_0.map (materialize literalDomain)
theorem check0_5_3_0 : checkRows direction samples0 trees0 rows0_5_3_0 = true := by
  rw [rows0_5_3_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_5_3_0]
  decide
theorem final_eq5_3_0 : final5_3_0 = rows0_5_3_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation5_3_0_0 : rotatedStateRow3 sourceState5_0_0 = stateRow5_3_0_0 := by decide
theorem sourceRowRotation5_3_0_1 : rotatedStateRow3 sourceState5_0_1 = stateRow5_3_0_1 := by decide
theorem sourceRowRotation5_3_0_2 : rotatedStateRow3 sourceState5_0_2 = stateRow5_3_0_2 := by decide
theorem sourceRowRotation5_3_0_3 : rotatedStateRow3 sourceState5_0_3 = stateRow5_3_0_3 := by decide
theorem sourceRowRotation5_3_0_4 : rotatedStateRow3 sourceState5_0_4 = stateRow5_3_0_4 := by decide
theorem sourceRowRotation5_3_0_5 : rotatedStateRow3 sourceState5_0_5 = stateRow5_3_0_5 := by decide
theorem sourceRowRotation5_3_0_6 : rotatedStateRow3 sourceState5_0_6 = stateRow5_3_0_6 := by decide
theorem sourceRowRotation5_3_0_7 : rotatedStateRow3 sourceState5_0_7 = stateRow5_3_0_7 := by decide
theorem sourceRowRotation5_3_0_8 : rotatedStateRow3 sourceState5_0_8 = stateRow5_3_0_8 := by decide
theorem sourceRowRotation5_3_0_9 : rotatedStateRow3 sourceState5_0_9 = stateRow5_3_0_9 := by decide
theorem sourceRowRotation5_3_0_10 : rotatedStateRow3 sourceState5_0_10 = stateRow5_3_0_10 := by decide
theorem sourceRowRotation5_3_0_11 : rotatedStateRow3 sourceState5_0_11 = stateRow5_3_0_11 := by decide
theorem initial5_3_0 : (source5_0).map (rotatePatch 3 (hexRegion 4)) = rows0_5_3_0.map Verdict.patch := by
  rw [sourceStates5_0, sourceStateSplit5_0, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation5_3_0_0, sourceRowRotation5_3_0_1, sourceRowRotation5_3_0_2, sourceRowRotation5_3_0_3, sourceRowRotation5_3_0_4, sourceRowRotation5_3_0_5, sourceRowRotation5_3_0_6, sourceRowRotation5_3_0_7, sourceRowRotation5_3_0_8, sourceRowRotation5_3_0_9, sourceRowRotation5_3_0_10, sourceRowRotation5_3_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
