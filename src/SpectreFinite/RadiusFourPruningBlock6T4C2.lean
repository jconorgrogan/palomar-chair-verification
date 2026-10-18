module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock6T4C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_4_2_11 : List State := [(8,0),(8,3),(5,5),(7,0),(4,3),(8,4),(1,4),(0,5),(4,4),(1,4),(0,5),(7,1),(7,5),(6,0),(7,1),(7,5),(6,0),(3,1),(4,0),(7,3),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(7,5),(0,3),(4,1),(0,2),(1,1)]
def indexedRows0_6_4_2 : List (RowVerdict 6) := [.keep stateRow6_4_2_0, .keep stateRow6_4_2_1, .keep stateRow6_4_2_2, .keep stateRow6_4_2_3, .keep stateRow6_4_2_4, .keep stateRow6_4_2_5, .keep stateRow6_4_2_6, .keep stateRow6_4_2_7, .keep stateRow6_4_2_8, .keep stateRow6_4_2_9, .keep stateRow6_4_2_10, .reject stateRow6_4_2_11 1]
def rows0_6_4_2 : List (Verdict 6) := indexedRows0_6_4_2.map (materialize literalDomain)
theorem check0_6_4_2 : checkRows direction samples0 trees0 rows0_6_4_2 = true := by
  rw [rows0_6_4_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_6_4_2]
  decide
theorem final_eq6_4_2 : final6_4_2 = rows0_6_4_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation6_4_2_0 : rotatedStateRow4 sourceState6_2_0 = stateRow6_4_2_0 := by decide
theorem sourceRowRotation6_4_2_1 : rotatedStateRow4 sourceState6_2_1 = stateRow6_4_2_1 := by decide
theorem sourceRowRotation6_4_2_2 : rotatedStateRow4 sourceState6_2_2 = stateRow6_4_2_2 := by decide
theorem sourceRowRotation6_4_2_3 : rotatedStateRow4 sourceState6_2_3 = stateRow6_4_2_3 := by decide
theorem sourceRowRotation6_4_2_4 : rotatedStateRow4 sourceState6_2_4 = stateRow6_4_2_4 := by decide
theorem sourceRowRotation6_4_2_5 : rotatedStateRow4 sourceState6_2_5 = stateRow6_4_2_5 := by decide
theorem sourceRowRotation6_4_2_6 : rotatedStateRow4 sourceState6_2_6 = stateRow6_4_2_6 := by decide
theorem sourceRowRotation6_4_2_7 : rotatedStateRow4 sourceState6_2_7 = stateRow6_4_2_7 := by decide
theorem sourceRowRotation6_4_2_8 : rotatedStateRow4 sourceState6_2_8 = stateRow6_4_2_8 := by decide
theorem sourceRowRotation6_4_2_9 : rotatedStateRow4 sourceState6_2_9 = stateRow6_4_2_9 := by decide
theorem sourceRowRotation6_4_2_10 : rotatedStateRow4 sourceState6_2_10 = stateRow6_4_2_10 := by decide
theorem sourceRowRotation6_4_2_11 : rotatedStateRow4 sourceState6_2_11 = stateRow6_4_2_11 := by decide
theorem initial6_4_2 : (source6_2).map (rotatePatch 4 (hexRegion 4)) = rows0_6_4_2.map Verdict.patch := by
  rw [sourceStates6_2, sourceStateSplit6_2, rotateCanonical_map4]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_4_2_0, sourceRowRotation6_4_2_1, sourceRowRotation6_4_2_2, sourceRowRotation6_4_2_3, sourceRowRotation6_4_2_4, sourceRowRotation6_4_2_5, sourceRowRotation6_4_2_6, sourceRowRotation6_4_2_7, sourceRowRotation6_4_2_8, sourceRowRotation6_4_2_9, sourceRowRotation6_4_2_10, sourceRowRotation6_4_2_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
