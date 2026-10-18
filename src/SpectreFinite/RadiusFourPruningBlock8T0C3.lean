module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock8T0C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_0_3 : List (RowVerdict 6) := [.keep stateRow8_0_3_0, .keep stateRow8_0_3_1, .keep stateRow8_0_3_2, .keep stateRow8_0_3_3, .keep stateRow8_0_3_4, .keep stateRow8_0_3_5, .keep stateRow8_0_3_6, .keep stateRow8_0_3_7, .keep stateRow8_0_3_8, .keep stateRow8_0_3_9, .keep stateRow8_0_3_10, .keep stateRow8_0_3_11]
def rows0_8_0_3 : List (Verdict 6) := indexedRows0_8_0_3.map (materialize literalDomain)
theorem check0_8_0_3 : checkRows direction samples0 trees0 rows0_8_0_3 = true := by
  rw [rows0_8_0_3, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_0_3]
  decide
theorem final_eq8_0_3 : final8_0_3 = rows0_8_0_3.filterMap Verdict.kept := by rfl
theorem sourceRowRotation8_0_3_0 : rotatedStateRow0 sourceState8_3_0 = stateRow8_0_3_0 := by decide
theorem sourceRowRotation8_0_3_1 : rotatedStateRow0 sourceState8_3_1 = stateRow8_0_3_1 := by decide
theorem sourceRowRotation8_0_3_2 : rotatedStateRow0 sourceState8_3_2 = stateRow8_0_3_2 := by decide
theorem sourceRowRotation8_0_3_3 : rotatedStateRow0 sourceState8_3_3 = stateRow8_0_3_3 := by decide
theorem sourceRowRotation8_0_3_4 : rotatedStateRow0 sourceState8_3_4 = stateRow8_0_3_4 := by decide
theorem sourceRowRotation8_0_3_5 : rotatedStateRow0 sourceState8_3_5 = stateRow8_0_3_5 := by decide
theorem sourceRowRotation8_0_3_6 : rotatedStateRow0 sourceState8_3_6 = stateRow8_0_3_6 := by decide
theorem sourceRowRotation8_0_3_7 : rotatedStateRow0 sourceState8_3_7 = stateRow8_0_3_7 := by decide
theorem sourceRowRotation8_0_3_8 : rotatedStateRow0 sourceState8_3_8 = stateRow8_0_3_8 := by decide
theorem sourceRowRotation8_0_3_9 : rotatedStateRow0 sourceState8_3_9 = stateRow8_0_3_9 := by decide
theorem sourceRowRotation8_0_3_10 : rotatedStateRow0 sourceState8_3_10 = stateRow8_0_3_10 := by decide
theorem sourceRowRotation8_0_3_11 : rotatedStateRow0 sourceState8_3_11 = stateRow8_0_3_11 := by decide
theorem initial8_0_3 : (source8_3).map (rotatePatch 0 (hexRegion 4)) = rows0_8_0_3.map Verdict.patch := by
  rw [sourceStates8_3, sourceStateSplit8_3, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_0_3_0, sourceRowRotation8_0_3_1, sourceRowRotation8_0_3_2, sourceRowRotation8_0_3_3, sourceRowRotation8_0_3_4, sourceRowRotation8_0_3_5, sourceRowRotation8_0_3_6, sourceRowRotation8_0_3_7, sourceRowRotation8_0_3_8, sourceRowRotation8_0_3_9, sourceRowRotation8_0_3_10, sourceRowRotation8_0_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
