module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock7T2C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_4_5 : List State := [(8,3),(5,5),(3,0),(2,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(5,3),(8,5),(7,0),(8,3),(8,5),(7,0),(4,3),(6,3),(7,2),(7,4),(6,3),(7,2),(7,4),(1,1),(4,1),(0,2),(1,1),(8,1)]
def indexedRows0_7_2_4 : List (RowVerdict 6) := [.keep stateRow7_2_4_0, .keep stateRow7_2_4_1, .keep stateRow7_2_4_2, .keep stateRow7_2_4_3, .keep stateRow7_2_4_4, .reject stateRow7_2_4_5 3, .keep stateRow7_2_4_6, .keep stateRow7_2_4_7, .keep stateRow7_2_4_8, .keep stateRow7_2_4_9, .keep stateRow7_2_4_10, .keep stateRow7_2_4_11]
def rows0_7_2_4 : List (Verdict 6) := indexedRows0_7_2_4.map (materialize literalDomain)
theorem check0_7_2_4 : checkRows direction samples0 trees0 rows0_7_2_4 = true := by
  rw [rows0_7_2_4, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_2_4]
  decide
theorem final_eq7_2_4 : final7_2_4 = rows0_7_2_4.filterMap Verdict.kept := by rfl
theorem sourceRowRotation7_2_4_0 : rotatedStateRow2 sourceState7_4_0 = stateRow7_2_4_0 := by decide
theorem sourceRowRotation7_2_4_1 : rotatedStateRow2 sourceState7_4_1 = stateRow7_2_4_1 := by decide
theorem sourceRowRotation7_2_4_2 : rotatedStateRow2 sourceState7_4_2 = stateRow7_2_4_2 := by decide
theorem sourceRowRotation7_2_4_3 : rotatedStateRow2 sourceState7_4_3 = stateRow7_2_4_3 := by decide
theorem sourceRowRotation7_2_4_4 : rotatedStateRow2 sourceState7_4_4 = stateRow7_2_4_4 := by decide
theorem sourceRowRotation7_2_4_5 : rotatedStateRow2 sourceState7_4_5 = stateRow7_2_4_5 := by decide
theorem sourceRowRotation7_2_4_6 : rotatedStateRow2 sourceState7_4_6 = stateRow7_2_4_6 := by decide
theorem sourceRowRotation7_2_4_7 : rotatedStateRow2 sourceState7_4_7 = stateRow7_2_4_7 := by decide
theorem sourceRowRotation7_2_4_8 : rotatedStateRow2 sourceState7_4_8 = stateRow7_2_4_8 := by decide
theorem sourceRowRotation7_2_4_9 : rotatedStateRow2 sourceState7_4_9 = stateRow7_2_4_9 := by decide
theorem sourceRowRotation7_2_4_10 : rotatedStateRow2 sourceState7_4_10 = stateRow7_2_4_10 := by decide
theorem sourceRowRotation7_2_4_11 : rotatedStateRow2 sourceState7_4_11 = stateRow7_2_4_11 := by decide
theorem initial7_2_4 : (source7_4).map (rotatePatch 2 (hexRegion 4)) = rows0_7_2_4.map Verdict.patch := by
  rw [sourceStates7_4, sourceStateSplit7_4, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_2_4_0, sourceRowRotation7_2_4_1, sourceRowRotation7_2_4_2, sourceRowRotation7_2_4_3, sourceRowRotation7_2_4_4, sourceRowRotation7_2_4_5, sourceRowRotation7_2_4_6, sourceRowRotation7_2_4_7, sourceRowRotation7_2_4_8, sourceRowRotation7_2_4_9, sourceRowRotation7_2_4_10, sourceRowRotation7_2_4_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
