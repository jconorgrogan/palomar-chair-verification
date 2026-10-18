module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock7T0C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_7_0_1 : List (RowVerdict 6) := [.keep stateRow7_0_1_0, .keep stateRow7_0_1_1, .keep stateRow7_0_1_2, .keep stateRow7_0_1_3, .keep stateRow7_0_1_4, .keep stateRow7_0_1_5, .keep stateRow7_0_1_6, .keep stateRow7_0_1_7, .keep stateRow7_0_1_8, .keep stateRow7_0_1_9, .keep stateRow7_0_1_10, .keep stateRow7_0_1_11]
def rows0_7_0_1 : List (Verdict 6) := indexedRows0_7_0_1.map (materialize literalDomain)
theorem check0_7_0_1 : checkRows direction samples0 trees0 rows0_7_0_1 = true := by
  rw [rows0_7_0_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_0_1]
  decide
theorem final_eq7_0_1 : final7_0_1 = rows0_7_0_1.filterMap Verdict.kept := by rfl
theorem sourceRowRotation7_0_1_0 : rotatedStateRow0 sourceState7_1_0 = stateRow7_0_1_0 := by decide
theorem sourceRowRotation7_0_1_1 : rotatedStateRow0 sourceState7_1_1 = stateRow7_0_1_1 := by decide
theorem sourceRowRotation7_0_1_2 : rotatedStateRow0 sourceState7_1_2 = stateRow7_0_1_2 := by decide
theorem sourceRowRotation7_0_1_3 : rotatedStateRow0 sourceState7_1_3 = stateRow7_0_1_3 := by decide
theorem sourceRowRotation7_0_1_4 : rotatedStateRow0 sourceState7_1_4 = stateRow7_0_1_4 := by decide
theorem sourceRowRotation7_0_1_5 : rotatedStateRow0 sourceState7_1_5 = stateRow7_0_1_5 := by decide
theorem sourceRowRotation7_0_1_6 : rotatedStateRow0 sourceState7_1_6 = stateRow7_0_1_6 := by decide
theorem sourceRowRotation7_0_1_7 : rotatedStateRow0 sourceState7_1_7 = stateRow7_0_1_7 := by decide
theorem sourceRowRotation7_0_1_8 : rotatedStateRow0 sourceState7_1_8 = stateRow7_0_1_8 := by decide
theorem sourceRowRotation7_0_1_9 : rotatedStateRow0 sourceState7_1_9 = stateRow7_0_1_9 := by decide
theorem sourceRowRotation7_0_1_10 : rotatedStateRow0 sourceState7_1_10 = stateRow7_0_1_10 := by decide
theorem sourceRowRotation7_0_1_11 : rotatedStateRow0 sourceState7_1_11 = stateRow7_0_1_11 := by decide
theorem initial7_0_1 : (source7_1).map (rotatePatch 0 (hexRegion 4)) = rows0_7_0_1.map Verdict.patch := by
  rw [sourceStates7_1, sourceStateSplit7_1, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_0_1_0, sourceRowRotation7_0_1_1, sourceRowRotation7_0_1_2, sourceRowRotation7_0_1_3, sourceRowRotation7_0_1_4, sourceRowRotation7_0_1_5, sourceRowRotation7_0_1_6, sourceRowRotation7_0_1_7, sourceRowRotation7_0_1_8, sourceRowRotation7_0_1_9, sourceRowRotation7_0_1_10, sourceRowRotation7_0_1_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
