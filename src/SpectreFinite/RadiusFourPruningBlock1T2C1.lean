module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock1T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_1_2_1 : List (RowVerdict 6) := [.keep stateRow1_2_1_0, .keep stateRow1_2_1_1, .keep stateRow1_2_1_2, .keep stateRow1_2_1_3, .keep stateRow1_2_1_4, .keep stateRow1_2_1_5, .keep stateRow1_2_1_6, .keep stateRow1_2_1_7, .keep stateRow1_2_1_8, .keep stateRow1_2_1_9, .keep stateRow1_2_1_10, .keep stateRow1_2_1_11]
def rows0_1_2_1 : List (Verdict 6) := indexedRows0_1_2_1.map (materialize literalDomain)
theorem check0_1_2_1 : checkRows direction samples0 trees0 rows0_1_2_1 = true := by
  rw [rows0_1_2_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_1_2_1]
  decide
theorem final_eq1_2_1 : final1_2_1 = rows0_1_2_1.filterMap Verdict.kept := by rfl
theorem sourceRowRotation1_2_1_0 : rotatedStateRow2 sourceState1_1_0 = stateRow1_2_1_0 := by decide
theorem sourceRowRotation1_2_1_1 : rotatedStateRow2 sourceState1_1_1 = stateRow1_2_1_1 := by decide
theorem sourceRowRotation1_2_1_2 : rotatedStateRow2 sourceState1_1_2 = stateRow1_2_1_2 := by decide
theorem sourceRowRotation1_2_1_3 : rotatedStateRow2 sourceState1_1_3 = stateRow1_2_1_3 := by decide
theorem sourceRowRotation1_2_1_4 : rotatedStateRow2 sourceState1_1_4 = stateRow1_2_1_4 := by decide
theorem sourceRowRotation1_2_1_5 : rotatedStateRow2 sourceState1_1_5 = stateRow1_2_1_5 := by decide
theorem sourceRowRotation1_2_1_6 : rotatedStateRow2 sourceState1_1_6 = stateRow1_2_1_6 := by decide
theorem sourceRowRotation1_2_1_7 : rotatedStateRow2 sourceState1_1_7 = stateRow1_2_1_7 := by decide
theorem sourceRowRotation1_2_1_8 : rotatedStateRow2 sourceState1_1_8 = stateRow1_2_1_8 := by decide
theorem sourceRowRotation1_2_1_9 : rotatedStateRow2 sourceState1_1_9 = stateRow1_2_1_9 := by decide
theorem sourceRowRotation1_2_1_10 : rotatedStateRow2 sourceState1_1_10 = stateRow1_2_1_10 := by decide
theorem sourceRowRotation1_2_1_11 : rotatedStateRow2 sourceState1_1_11 = stateRow1_2_1_11 := by decide
theorem initial1_2_1 : (source1_1).map (rotatePatch 2 (hexRegion 4)) = rows0_1_2_1.map Verdict.patch := by
  rw [sourceStates1_1, sourceStateSplit1_1, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_2_1_0, sourceRowRotation1_2_1_1, sourceRowRotation1_2_1_2, sourceRowRotation1_2_1_3, sourceRowRotation1_2_1_4, sourceRowRotation1_2_1_5, sourceRowRotation1_2_1_6, sourceRowRotation1_2_1_7, sourceRowRotation1_2_1_8, sourceRowRotation1_2_1_9, sourceRowRotation1_2_1_10, sourceRowRotation1_2_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
