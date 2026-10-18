module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock2T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_3_0_0 : List State := [(0,4),(5,4),(6,4),(1,2),(8,4),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(7,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,4),(1,2),(7,4),(6,3),(7,2)]
def stateRow2_3_0_1 : List State := [(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(7,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,4),(1,2),(7,4),(6,3),(7,2)]
def stateRow2_3_0_3 : List State := [(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,4),(1,2),(7,4),(6,3),(7,2)]
def stateRow2_3_0_5 : List State := [(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(6,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(7,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,4),(1,2),(7,4),(1,3),(8,2)]
def indexedRows0_2_3_0 : List (RowVerdict 6) := [.reject stateRow2_3_0_0 1, .reject stateRow2_3_0_1 0, .keep stateRow2_3_0_2, .reject stateRow2_3_0_3 3, .keep stateRow2_3_0_4, .reject stateRow2_3_0_5 0, .keep stateRow2_3_0_6, .keep stateRow2_3_0_7]
def rows0_2_3_0 : List (Verdict 6) := indexedRows0_2_3_0.map (materialize literalDomain)
theorem check0_2_3_0 : checkRows direction samples0 trees0 rows0_2_3_0 = true := by
  rw [rows0_2_3_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_2_3_0]
  decide
theorem final_eq2_3_0 : final2_3_0 = rows0_2_3_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation2_3_0_0 : rotatedStateRow3 sourceState2_0_0 = stateRow2_3_0_0 := by decide
theorem sourceRowRotation2_3_0_1 : rotatedStateRow3 sourceState2_0_1 = stateRow2_3_0_1 := by decide
theorem sourceRowRotation2_3_0_2 : rotatedStateRow3 sourceState2_0_2 = stateRow2_3_0_2 := by decide
theorem sourceRowRotation2_3_0_3 : rotatedStateRow3 sourceState2_0_3 = stateRow2_3_0_3 := by decide
theorem sourceRowRotation2_3_0_4 : rotatedStateRow3 sourceState2_0_4 = stateRow2_3_0_4 := by decide
theorem sourceRowRotation2_3_0_5 : rotatedStateRow3 sourceState2_0_5 = stateRow2_3_0_5 := by decide
theorem sourceRowRotation2_3_0_6 : rotatedStateRow3 sourceState2_0_6 = stateRow2_3_0_6 := by decide
theorem sourceRowRotation2_3_0_7 : rotatedStateRow3 sourceState2_0_7 = stateRow2_3_0_7 := by decide
theorem initial2_3_0 : (source2_0).map (rotatePatch 3 (hexRegion 4)) = rows0_2_3_0.map Verdict.patch := by
  rw [sourceStates2_0, sourceStateSplit2_0, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation2_3_0_0, sourceRowRotation2_3_0_1, sourceRowRotation2_3_0_2, sourceRowRotation2_3_0_3, sourceRowRotation2_3_0_4, sourceRowRotation2_3_0_5, sourceRowRotation2_3_0_6, sourceRowRotation2_3_0_7] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
