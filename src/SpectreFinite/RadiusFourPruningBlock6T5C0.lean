module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock6T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_6_5_0 : List (RowVerdict 6) := [.keep stateRow6_5_0_0, .keep stateRow6_5_0_1, .keep stateRow6_5_0_2, .keep stateRow6_5_0_3, .keep stateRow6_5_0_4, .keep stateRow6_5_0_5, .keep stateRow6_5_0_6, .keep stateRow6_5_0_7, .keep stateRow6_5_0_8, .keep stateRow6_5_0_9, .keep stateRow6_5_0_10, .keep stateRow6_5_0_11]
def rows0_6_5_0 : List (Verdict 6) := indexedRows0_6_5_0.map (materialize literalDomain)
theorem check0_6_5_0 : checkRows direction samples0 trees0 rows0_6_5_0 = true := by
  rw [rows0_6_5_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_6_5_0]
  decide
theorem final_eq6_5_0 : final6_5_0 = rows0_6_5_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation6_5_0_0 : rotatedStateRow5 sourceState6_0_0 = stateRow6_5_0_0 := by decide
theorem sourceRowRotation6_5_0_1 : rotatedStateRow5 sourceState6_0_1 = stateRow6_5_0_1 := by decide
theorem sourceRowRotation6_5_0_2 : rotatedStateRow5 sourceState6_0_2 = stateRow6_5_0_2 := by decide
theorem sourceRowRotation6_5_0_3 : rotatedStateRow5 sourceState6_0_3 = stateRow6_5_0_3 := by decide
theorem sourceRowRotation6_5_0_4 : rotatedStateRow5 sourceState6_0_4 = stateRow6_5_0_4 := by decide
theorem sourceRowRotation6_5_0_5 : rotatedStateRow5 sourceState6_0_5 = stateRow6_5_0_5 := by decide
theorem sourceRowRotation6_5_0_6 : rotatedStateRow5 sourceState6_0_6 = stateRow6_5_0_6 := by decide
theorem sourceRowRotation6_5_0_7 : rotatedStateRow5 sourceState6_0_7 = stateRow6_5_0_7 := by decide
theorem sourceRowRotation6_5_0_8 : rotatedStateRow5 sourceState6_0_8 = stateRow6_5_0_8 := by decide
theorem sourceRowRotation6_5_0_9 : rotatedStateRow5 sourceState6_0_9 = stateRow6_5_0_9 := by decide
theorem sourceRowRotation6_5_0_10 : rotatedStateRow5 sourceState6_0_10 = stateRow6_5_0_10 := by decide
theorem sourceRowRotation6_5_0_11 : rotatedStateRow5 sourceState6_0_11 = stateRow6_5_0_11 := by decide
theorem initial6_5_0 : (source6_0).map (rotatePatch 5 (hexRegion 4)) = rows0_6_5_0.map Verdict.patch := by
  rw [sourceStates6_0, sourceStateSplit6_0, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_5_0_0, sourceRowRotation6_5_0_1, sourceRowRotation6_5_0_2, sourceRowRotation6_5_0_3, sourceRowRotation6_5_0_4, sourceRowRotation6_5_0_5, sourceRowRotation6_5_0_6, sourceRowRotation6_5_0_7, sourceRowRotation6_5_0_8, sourceRowRotation6_5_0_9, sourceRowRotation6_5_0_10, sourceRowRotation6_5_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
