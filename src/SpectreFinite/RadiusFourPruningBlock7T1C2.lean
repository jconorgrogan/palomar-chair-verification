module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock7T1C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_7_1_2 : List (RowVerdict 6) := [.keep stateRow7_1_2_0, .keep stateRow7_1_2_1, .keep stateRow7_1_2_2, .keep stateRow7_1_2_3, .keep stateRow7_1_2_4, .keep stateRow7_1_2_5, .keep stateRow7_1_2_6, .keep stateRow7_1_2_7, .keep stateRow7_1_2_8, .keep stateRow7_1_2_9, .keep stateRow7_1_2_10, .keep stateRow7_1_2_11]
def rows0_7_1_2 : List (Verdict 6) := indexedRows0_7_1_2.map (materialize literalDomain)
theorem check0_7_1_2 : checkRows direction samples0 trees0 rows0_7_1_2 = true := by
  rw [rows0_7_1_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_1_2]
  decide
theorem final_eq7_1_2 : final7_1_2 = rows0_7_1_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation7_1_2_0 : rotatedStateRow1 sourceState7_2_0 = stateRow7_1_2_0 := by decide
theorem sourceRowRotation7_1_2_1 : rotatedStateRow1 sourceState7_2_1 = stateRow7_1_2_1 := by decide
theorem sourceRowRotation7_1_2_2 : rotatedStateRow1 sourceState7_2_2 = stateRow7_1_2_2 := by decide
theorem sourceRowRotation7_1_2_3 : rotatedStateRow1 sourceState7_2_3 = stateRow7_1_2_3 := by decide
theorem sourceRowRotation7_1_2_4 : rotatedStateRow1 sourceState7_2_4 = stateRow7_1_2_4 := by decide
theorem sourceRowRotation7_1_2_5 : rotatedStateRow1 sourceState7_2_5 = stateRow7_1_2_5 := by decide
theorem sourceRowRotation7_1_2_6 : rotatedStateRow1 sourceState7_2_6 = stateRow7_1_2_6 := by decide
theorem sourceRowRotation7_1_2_7 : rotatedStateRow1 sourceState7_2_7 = stateRow7_1_2_7 := by decide
theorem sourceRowRotation7_1_2_8 : rotatedStateRow1 sourceState7_2_8 = stateRow7_1_2_8 := by decide
theorem sourceRowRotation7_1_2_9 : rotatedStateRow1 sourceState7_2_9 = stateRow7_1_2_9 := by decide
theorem sourceRowRotation7_1_2_10 : rotatedStateRow1 sourceState7_2_10 = stateRow7_1_2_10 := by decide
theorem sourceRowRotation7_1_2_11 : rotatedStateRow1 sourceState7_2_11 = stateRow7_1_2_11 := by decide
theorem initial7_1_2 : (source7_2).map (rotatePatch 1 (hexRegion 4)) = rows0_7_1_2.map Verdict.patch := by
  rw [sourceStates7_2, sourceStateSplit7_2, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_1_2_0, sourceRowRotation7_1_2_1, sourceRowRotation7_1_2_2, sourceRowRotation7_1_2_3, sourceRowRotation7_1_2_4, sourceRowRotation7_1_2_5, sourceRowRotation7_1_2_6, sourceRowRotation7_1_2_7, sourceRowRotation7_1_2_8, sourceRowRotation7_1_2_9, sourceRowRotation7_1_2_10, sourceRowRotation7_1_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
