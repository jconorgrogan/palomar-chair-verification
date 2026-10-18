module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock6T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_1_3_7 : List State := [(1,4),(0,5),(4,4),(0,0),(7,2),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,5),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(1,5),(6,1),(4,1),(0,2),(1,1),(8,1),(2,0),(7,3),(5,2),(8,0),(8,3)]
def indexedRows0_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_2, .keep stateRow6_1_3_3, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .reject stateRow6_1_3_7 4]
def rows0_6_1_3 : List (Verdict 6) := indexedRows0_6_1_3.map (materialize literalDomain)
theorem check0_6_1_3 : checkRows direction samples0 trees0 rows0_6_1_3 = true := by
  rw [rows0_6_1_3, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_6_1_3]
  decide
theorem final_eq6_1_3 : final6_1_3 = rows0_6_1_3.filterMap Verdict.kept := by rfl
theorem sourceRowRotation6_1_3_0 : rotatedStateRow1 sourceState6_3_0 = stateRow6_1_3_0 := by decide
theorem sourceRowRotation6_1_3_1 : rotatedStateRow1 sourceState6_3_1 = stateRow6_1_3_1 := by decide
theorem sourceRowRotation6_1_3_2 : rotatedStateRow1 sourceState6_3_2 = stateRow6_1_3_2 := by decide
theorem sourceRowRotation6_1_3_3 : rotatedStateRow1 sourceState6_3_3 = stateRow6_1_3_3 := by decide
theorem sourceRowRotation6_1_3_4 : rotatedStateRow1 sourceState6_3_4 = stateRow6_1_3_4 := by decide
theorem sourceRowRotation6_1_3_5 : rotatedStateRow1 sourceState6_3_5 = stateRow6_1_3_5 := by decide
theorem sourceRowRotation6_1_3_6 : rotatedStateRow1 sourceState6_3_6 = stateRow6_1_3_6 := by decide
theorem sourceRowRotation6_1_3_7 : rotatedStateRow1 sourceState6_3_7 = stateRow6_1_3_7 := by decide
theorem initial6_1_3 : (source6_3).map (rotatePatch 1 (hexRegion 4)) = rows0_6_1_3.map Verdict.patch := by
  rw [sourceStates6_3, sourceStateSplit6_3, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation6_1_3_0, sourceRowRotation6_1_3_1, sourceRowRotation6_1_3_2, sourceRowRotation6_1_3_3, sourceRowRotation6_1_3_4, sourceRowRotation6_1_3_5, sourceRowRotation6_1_3_6, sourceRowRotation6_1_3_7] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
