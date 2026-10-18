module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock7T0C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_7_0_5 : List (RowVerdict 6) := [.keep stateRow7_0_5_0, .keep stateRow7_0_5_1, .keep stateRow7_0_5_2, .keep stateRow7_0_5_3, .keep stateRow7_0_5_4, .keep stateRow7_0_5_5, .keep stateRow7_0_5_6, .keep stateRow7_0_5_7, .keep stateRow7_0_5_8, .keep stateRow7_0_5_9, .keep stateRow7_0_5_10, .keep stateRow7_0_5_11]
def rows0_7_0_5 : List (Verdict 6) := indexedRows0_7_0_5.map (materialize literalDomain)
theorem check0_7_0_5 : checkRows direction samples0 trees0 rows0_7_0_5 = true := by
  rw [rows0_7_0_5, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_0_5]
  decide
theorem final_eq7_0_5 : final7_0_5 = rows0_7_0_5.filterMap Verdict.kept := by rfl
theorem sourceRowRotation7_0_5_0 : rotatedStateRow0 sourceState7_5_0 = stateRow7_0_5_0 := by decide
theorem sourceRowRotation7_0_5_1 : rotatedStateRow0 sourceState7_5_1 = stateRow7_0_5_1 := by decide
theorem sourceRowRotation7_0_5_2 : rotatedStateRow0 sourceState7_5_2 = stateRow7_0_5_2 := by decide
theorem sourceRowRotation7_0_5_3 : rotatedStateRow0 sourceState7_5_3 = stateRow7_0_5_3 := by decide
theorem sourceRowRotation7_0_5_4 : rotatedStateRow0 sourceState7_5_4 = stateRow7_0_5_4 := by decide
theorem sourceRowRotation7_0_5_5 : rotatedStateRow0 sourceState7_5_5 = stateRow7_0_5_5 := by decide
theorem sourceRowRotation7_0_5_6 : rotatedStateRow0 sourceState7_5_6 = stateRow7_0_5_6 := by decide
theorem sourceRowRotation7_0_5_7 : rotatedStateRow0 sourceState7_5_7 = stateRow7_0_5_7 := by decide
theorem sourceRowRotation7_0_5_8 : rotatedStateRow0 sourceState7_5_8 = stateRow7_0_5_8 := by decide
theorem sourceRowRotation7_0_5_9 : rotatedStateRow0 sourceState7_5_9 = stateRow7_0_5_9 := by decide
theorem sourceRowRotation7_0_5_10 : rotatedStateRow0 sourceState7_5_10 = stateRow7_0_5_10 := by decide
theorem sourceRowRotation7_0_5_11 : rotatedStateRow0 sourceState7_5_11 = stateRow7_0_5_11 := by decide
theorem initial7_0_5 : (source7_5).map (rotatePatch 0 (hexRegion 4)) = rows0_7_0_5.map Verdict.patch := by
  rw [sourceStates7_5, sourceStateSplit7_5, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_0_5_0, sourceRowRotation7_0_5_1, sourceRowRotation7_0_5_2, sourceRowRotation7_0_5_3, sourceRowRotation7_0_5_4, sourceRowRotation7_0_5_5, sourceRowRotation7_0_5_6, sourceRowRotation7_0_5_7, sourceRowRotation7_0_5_8, sourceRowRotation7_0_5_9, sourceRowRotation7_0_5_10, sourceRowRotation7_0_5_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
