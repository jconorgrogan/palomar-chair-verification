module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock8T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_1_0 : List (RowVerdict 6) := [.keep stateRow8_1_0_0, .keep stateRow8_1_0_1, .keep stateRow8_1_0_2, .keep stateRow8_1_0_3, .keep stateRow8_1_0_4, .keep stateRow8_1_0_5, .keep stateRow8_1_0_6, .keep stateRow8_1_0_7, .keep stateRow8_1_0_8, .keep stateRow8_1_0_9, .keep stateRow8_1_0_10, .keep stateRow8_1_0_11]
def rows0_8_1_0 : List (Verdict 6) := indexedRows0_8_1_0.map (materialize literalDomain)
theorem check0_8_1_0 : checkRows direction samples0 trees0 rows0_8_1_0 = true := by
  rw [rows0_8_1_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_1_0]
  decide
theorem final_eq8_1_0 : final8_1_0 = rows0_8_1_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation8_1_0_0 : rotatedStateRow1 sourceState8_0_0 = stateRow8_1_0_0 := by decide
theorem sourceRowRotation8_1_0_1 : rotatedStateRow1 sourceState8_0_1 = stateRow8_1_0_1 := by decide
theorem sourceRowRotation8_1_0_2 : rotatedStateRow1 sourceState8_0_2 = stateRow8_1_0_2 := by decide
theorem sourceRowRotation8_1_0_3 : rotatedStateRow1 sourceState8_0_3 = stateRow8_1_0_3 := by decide
theorem sourceRowRotation8_1_0_4 : rotatedStateRow1 sourceState8_0_4 = stateRow8_1_0_4 := by decide
theorem sourceRowRotation8_1_0_5 : rotatedStateRow1 sourceState8_0_5 = stateRow8_1_0_5 := by decide
theorem sourceRowRotation8_1_0_6 : rotatedStateRow1 sourceState8_0_6 = stateRow8_1_0_6 := by decide
theorem sourceRowRotation8_1_0_7 : rotatedStateRow1 sourceState8_0_7 = stateRow8_1_0_7 := by decide
theorem sourceRowRotation8_1_0_8 : rotatedStateRow1 sourceState8_0_8 = stateRow8_1_0_8 := by decide
theorem sourceRowRotation8_1_0_9 : rotatedStateRow1 sourceState8_0_9 = stateRow8_1_0_9 := by decide
theorem sourceRowRotation8_1_0_10 : rotatedStateRow1 sourceState8_0_10 = stateRow8_1_0_10 := by decide
theorem sourceRowRotation8_1_0_11 : rotatedStateRow1 sourceState8_0_11 = stateRow8_1_0_11 := by decide
theorem initial8_1_0 : (source8_0).map (rotatePatch 1 (hexRegion 4)) = rows0_8_1_0.map Verdict.patch := by
  rw [sourceStates8_0, sourceStateSplit8_0, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_1_0_0, sourceRowRotation8_1_0_1, sourceRowRotation8_1_0_2, sourceRowRotation8_1_0_3, sourceRowRotation8_1_0_4, sourceRowRotation8_1_0_5, sourceRowRotation8_1_0_6, sourceRowRotation8_1_0_7, sourceRowRotation8_1_0_8, sourceRowRotation8_1_0_9, sourceRowRotation8_1_0_10, sourceRowRotation8_1_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
