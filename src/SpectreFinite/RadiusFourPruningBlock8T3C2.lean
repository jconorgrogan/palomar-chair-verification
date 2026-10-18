module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock8T3C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_1, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows0_8_3_2 : List (Verdict 6) := indexedRows0_8_3_2.map (materialize literalDomain)
theorem check0_8_3_2 : checkRows direction samples0 trees0 rows0_8_3_2 = true := by
  rw [rows0_8_3_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_3_2]
  decide
theorem final_eq8_3_2 : final8_3_2 = rows0_8_3_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation8_3_2_0 : rotatedStateRow3 sourceState8_2_0 = stateRow8_3_2_0 := by decide
theorem sourceRowRotation8_3_2_1 : rotatedStateRow3 sourceState8_2_1 = stateRow8_3_2_1 := by decide
theorem sourceRowRotation8_3_2_2 : rotatedStateRow3 sourceState8_2_2 = stateRow8_3_2_2 := by decide
theorem sourceRowRotation8_3_2_3 : rotatedStateRow3 sourceState8_2_3 = stateRow8_3_2_3 := by decide
theorem sourceRowRotation8_3_2_4 : rotatedStateRow3 sourceState8_2_4 = stateRow8_3_2_4 := by decide
theorem sourceRowRotation8_3_2_5 : rotatedStateRow3 sourceState8_2_5 = stateRow8_3_2_5 := by decide
theorem sourceRowRotation8_3_2_6 : rotatedStateRow3 sourceState8_2_6 = stateRow8_3_2_6 := by decide
theorem sourceRowRotation8_3_2_7 : rotatedStateRow3 sourceState8_2_7 = stateRow8_3_2_7 := by decide
theorem sourceRowRotation8_3_2_8 : rotatedStateRow3 sourceState8_2_8 = stateRow8_3_2_8 := by decide
theorem sourceRowRotation8_3_2_9 : rotatedStateRow3 sourceState8_2_9 = stateRow8_3_2_9 := by decide
theorem sourceRowRotation8_3_2_10 : rotatedStateRow3 sourceState8_2_10 = stateRow8_3_2_10 := by decide
theorem sourceRowRotation8_3_2_11 : rotatedStateRow3 sourceState8_2_11 = stateRow8_3_2_11 := by decide
theorem initial8_3_2 : (source8_2).map (rotatePatch 3 (hexRegion 4)) = rows0_8_3_2.map Verdict.patch := by
  rw [sourceStates8_2, sourceStateSplit8_2, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_3_2_0, sourceRowRotation8_3_2_1, sourceRowRotation8_3_2_2, sourceRowRotation8_3_2_3, sourceRowRotation8_3_2_4, sourceRowRotation8_3_2_5, sourceRowRotation8_3_2_6, sourceRowRotation8_3_2_7, sourceRowRotation8_3_2_8, sourceRowRotation8_3_2_9, sourceRowRotation8_3_2_10, sourceRowRotation8_3_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
