module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock7T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_4, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows0_7_1_3 : List (Verdict 6) := indexedRows0_7_1_3.map (materialize literalDomain)
theorem check0_7_1_3 : checkRows direction samples0 trees0 rows0_7_1_3 = true := by
  rw [rows0_7_1_3, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_1_3]
  decide
theorem final_eq7_1_3 : final7_1_3 = rows0_7_1_3.filterMap Verdict.kept := by rfl
theorem sourceRowRotation7_1_3_0 : rotatedStateRow1 sourceState7_3_0 = stateRow7_1_3_0 := by decide
theorem sourceRowRotation7_1_3_1 : rotatedStateRow1 sourceState7_3_1 = stateRow7_1_3_1 := by decide
theorem sourceRowRotation7_1_3_2 : rotatedStateRow1 sourceState7_3_2 = stateRow7_1_3_2 := by decide
theorem sourceRowRotation7_1_3_3 : rotatedStateRow1 sourceState7_3_3 = stateRow7_1_3_3 := by decide
theorem sourceRowRotation7_1_3_4 : rotatedStateRow1 sourceState7_3_4 = stateRow7_1_3_4 := by decide
theorem sourceRowRotation7_1_3_5 : rotatedStateRow1 sourceState7_3_5 = stateRow7_1_3_5 := by decide
theorem sourceRowRotation7_1_3_6 : rotatedStateRow1 sourceState7_3_6 = stateRow7_1_3_6 := by decide
theorem sourceRowRotation7_1_3_7 : rotatedStateRow1 sourceState7_3_7 = stateRow7_1_3_7 := by decide
theorem sourceRowRotation7_1_3_8 : rotatedStateRow1 sourceState7_3_8 = stateRow7_1_3_8 := by decide
theorem sourceRowRotation7_1_3_9 : rotatedStateRow1 sourceState7_3_9 = stateRow7_1_3_9 := by decide
theorem sourceRowRotation7_1_3_10 : rotatedStateRow1 sourceState7_3_10 = stateRow7_1_3_10 := by decide
theorem sourceRowRotation7_1_3_11 : rotatedStateRow1 sourceState7_3_11 = stateRow7_1_3_11 := by decide
theorem initial7_1_3 : (source7_3).map (rotatePatch 1 (hexRegion 4)) = rows0_7_1_3.map Verdict.patch := by
  rw [sourceStates7_3, sourceStateSplit7_3, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_1_3_0, sourceRowRotation7_1_3_1, sourceRowRotation7_1_3_2, sourceRowRotation7_1_3_3, sourceRowRotation7_1_3_4, sourceRowRotation7_1_3_5, sourceRowRotation7_1_3_6, sourceRowRotation7_1_3_7, sourceRowRotation7_1_3_8, sourceRowRotation7_1_3_9, sourceRowRotation7_1_3_10, sourceRowRotation7_1_3_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
