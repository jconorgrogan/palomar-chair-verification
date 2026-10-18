module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock1T3C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_1_3_2 : List (RowVerdict 6) := [.keep stateRow1_3_2_0, .keep stateRow1_3_2_1, .keep stateRow1_3_2_2, .keep stateRow1_3_2_3, .keep stateRow1_3_2_4, .keep stateRow1_3_2_5, .keep stateRow1_3_2_6, .keep stateRow1_3_2_7, .keep stateRow1_3_2_8]
def rows0_1_3_2 : List (Verdict 6) := indexedRows0_1_3_2.map (materialize literalDomain)
theorem check0_1_3_2 : checkRows direction samples0 trees0 rows0_1_3_2 = true := by
  rw [rows0_1_3_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_1_3_2]
  decide
theorem final_eq1_3_2 : final1_3_2 = rows0_1_3_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation1_3_2_0 : rotatedStateRow3 sourceState1_2_0 = stateRow1_3_2_0 := by decide
theorem sourceRowRotation1_3_2_1 : rotatedStateRow3 sourceState1_2_1 = stateRow1_3_2_1 := by decide
theorem sourceRowRotation1_3_2_2 : rotatedStateRow3 sourceState1_2_2 = stateRow1_3_2_2 := by decide
theorem sourceRowRotation1_3_2_3 : rotatedStateRow3 sourceState1_2_3 = stateRow1_3_2_3 := by decide
theorem sourceRowRotation1_3_2_4 : rotatedStateRow3 sourceState1_2_4 = stateRow1_3_2_4 := by decide
theorem sourceRowRotation1_3_2_5 : rotatedStateRow3 sourceState1_2_5 = stateRow1_3_2_5 := by decide
theorem sourceRowRotation1_3_2_6 : rotatedStateRow3 sourceState1_2_6 = stateRow1_3_2_6 := by decide
theorem sourceRowRotation1_3_2_7 : rotatedStateRow3 sourceState1_2_7 = stateRow1_3_2_7 := by decide
theorem sourceRowRotation1_3_2_8 : rotatedStateRow3 sourceState1_2_8 = stateRow1_3_2_8 := by decide
theorem initial1_3_2 : (source1_2).map (rotatePatch 3 (hexRegion 4)) = rows0_1_3_2.map Verdict.patch := by
  rw [sourceStates1_2, sourceStateSplit1_2, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation1_3_2_0, sourceRowRotation1_3_2_1, sourceRowRotation1_3_2_2, sourceRowRotation1_3_2_3, sourceRowRotation1_3_2_4, sourceRowRotation1_3_2_5, sourceRowRotation1_3_2_6, sourceRowRotation1_3_2_7, sourceRowRotation1_3_2_8] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
