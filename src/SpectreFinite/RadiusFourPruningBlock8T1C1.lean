module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock8T1C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_1_1 : List (RowVerdict 6) := [.keep stateRow8_1_1_0, .keep stateRow8_1_1_1, .keep stateRow8_1_1_2, .keep stateRow8_1_1_3, .keep stateRow8_1_1_4, .keep stateRow8_1_1_5, .keep stateRow8_1_1_6, .keep stateRow8_1_1_7, .keep stateRow8_1_1_8, .keep stateRow8_1_1_9, .keep stateRow8_1_1_10, .keep stateRow8_1_1_11]
def rows0_8_1_1 : List (Verdict 6) := indexedRows0_8_1_1.map (materialize literalDomain)
theorem check0_8_1_1 : checkRows direction samples0 trees0 rows0_8_1_1 = true := by
  rw [rows0_8_1_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_1_1]
  decide
theorem final_eq8_1_1 : final8_1_1 = rows0_8_1_1.filterMap Verdict.kept := by rfl
theorem sourceRowRotation8_1_1_0 : rotatedStateRow1 sourceState8_1_0 = stateRow8_1_1_0 := by decide
theorem sourceRowRotation8_1_1_1 : rotatedStateRow1 sourceState8_1_1 = stateRow8_1_1_1 := by decide
theorem sourceRowRotation8_1_1_2 : rotatedStateRow1 sourceState8_1_2 = stateRow8_1_1_2 := by decide
theorem sourceRowRotation8_1_1_3 : rotatedStateRow1 sourceState8_1_3 = stateRow8_1_1_3 := by decide
theorem sourceRowRotation8_1_1_4 : rotatedStateRow1 sourceState8_1_4 = stateRow8_1_1_4 := by decide
theorem sourceRowRotation8_1_1_5 : rotatedStateRow1 sourceState8_1_5 = stateRow8_1_1_5 := by decide
theorem sourceRowRotation8_1_1_6 : rotatedStateRow1 sourceState8_1_6 = stateRow8_1_1_6 := by decide
theorem sourceRowRotation8_1_1_7 : rotatedStateRow1 sourceState8_1_7 = stateRow8_1_1_7 := by decide
theorem sourceRowRotation8_1_1_8 : rotatedStateRow1 sourceState8_1_8 = stateRow8_1_1_8 := by decide
theorem sourceRowRotation8_1_1_9 : rotatedStateRow1 sourceState8_1_9 = stateRow8_1_1_9 := by decide
theorem sourceRowRotation8_1_1_10 : rotatedStateRow1 sourceState8_1_10 = stateRow8_1_1_10 := by decide
theorem sourceRowRotation8_1_1_11 : rotatedStateRow1 sourceState8_1_11 = stateRow8_1_1_11 := by decide
theorem initial8_1_1 : (source8_1).map (rotatePatch 1 (hexRegion 4)) = rows0_8_1_1.map Verdict.patch := by
  rw [sourceStates8_1, sourceStateSplit8_1, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_1_1_0, sourceRowRotation8_1_1_1, sourceRowRotation8_1_1_2, sourceRowRotation8_1_1_3, sourceRowRotation8_1_1_4, sourceRowRotation8_1_1_5, sourceRowRotation8_1_1_6, sourceRowRotation8_1_1_7, sourceRowRotation8_1_1_8, sourceRowRotation8_1_1_9, sourceRowRotation8_1_1_10, sourceRowRotation8_1_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
