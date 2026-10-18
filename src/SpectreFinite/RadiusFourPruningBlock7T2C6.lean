module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock7T2C6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_6_3 : List State := [(8,3),(5,5),(3,0),(2,5),(6,0),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(6,1),(4,1),(0,2),(1,1),(8,1)]
def indexedRows0_7_2_6 : List (RowVerdict 6) := [.keep stateRow7_2_6_0, .keep stateRow7_2_6_1, .keep stateRow7_2_6_2, .reject stateRow7_2_6_3 3, .keep stateRow7_2_6_4, .keep stateRow7_2_6_5, .keep stateRow7_2_6_6, .keep stateRow7_2_6_7]
def rows0_7_2_6 : List (Verdict 6) := indexedRows0_7_2_6.map (materialize literalDomain)
theorem check0_7_2_6 : checkRows direction samples0 trees0 rows0_7_2_6 = true := by
  rw [rows0_7_2_6, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_2_6]
  decide
theorem final_eq7_2_6 : final7_2_6 = rows0_7_2_6.filterMap Verdict.kept := by rfl
theorem sourceRowRotation7_2_6_0 : rotatedStateRow2 sourceState7_6_0 = stateRow7_2_6_0 := by decide
theorem sourceRowRotation7_2_6_1 : rotatedStateRow2 sourceState7_6_1 = stateRow7_2_6_1 := by decide
theorem sourceRowRotation7_2_6_2 : rotatedStateRow2 sourceState7_6_2 = stateRow7_2_6_2 := by decide
theorem sourceRowRotation7_2_6_3 : rotatedStateRow2 sourceState7_6_3 = stateRow7_2_6_3 := by decide
theorem sourceRowRotation7_2_6_4 : rotatedStateRow2 sourceState7_6_4 = stateRow7_2_6_4 := by decide
theorem sourceRowRotation7_2_6_5 : rotatedStateRow2 sourceState7_6_5 = stateRow7_2_6_5 := by decide
theorem sourceRowRotation7_2_6_6 : rotatedStateRow2 sourceState7_6_6 = stateRow7_2_6_6 := by decide
theorem sourceRowRotation7_2_6_7 : rotatedStateRow2 sourceState7_6_7 = stateRow7_2_6_7 := by decide
theorem initial7_2_6 : (source7_6).map (rotatePatch 2 (hexRegion 4)) = rows0_7_2_6.map Verdict.patch := by
  rw [sourceStates7_6, sourceStateSplit7_6, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation7_2_6_0, sourceRowRotation7_2_6_1, sourceRowRotation7_2_6_2, sourceRowRotation7_2_6_3, sourceRowRotation7_2_6_4, sourceRowRotation7_2_6_5, sourceRowRotation7_2_6_6, sourceRowRotation7_2_6_7] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
