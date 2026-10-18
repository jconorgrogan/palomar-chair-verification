module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock4T2C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_4_2_0 : List (RowVerdict 6) := [.keep stateRow4_2_0_0, .keep stateRow4_2_0_1, .keep stateRow4_2_0_2, .keep stateRow4_2_0_3, .keep stateRow4_2_0_4, .keep stateRow4_2_0_5, .keep stateRow4_2_0_6, .keep stateRow4_2_0_7, .keep stateRow4_2_0_8, .keep stateRow4_2_0_9, .keep stateRow4_2_0_10, .keep stateRow4_2_0_11]
def rows0_4_2_0 : List (Verdict 6) := indexedRows0_4_2_0.map (materialize literalDomain)
theorem check0_4_2_0 : checkRows direction samples0 trees0 rows0_4_2_0 = true := by
  rw [rows0_4_2_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_4_2_0]
  decide
theorem final_eq4_2_0 : final4_2_0 = rows0_4_2_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation4_2_0_0 : rotatedStateRow2 sourceState4_0_0 = stateRow4_2_0_0 := by decide
theorem sourceRowRotation4_2_0_1 : rotatedStateRow2 sourceState4_0_1 = stateRow4_2_0_1 := by decide
theorem sourceRowRotation4_2_0_2 : rotatedStateRow2 sourceState4_0_2 = stateRow4_2_0_2 := by decide
theorem sourceRowRotation4_2_0_3 : rotatedStateRow2 sourceState4_0_3 = stateRow4_2_0_3 := by decide
theorem sourceRowRotation4_2_0_4 : rotatedStateRow2 sourceState4_0_4 = stateRow4_2_0_4 := by decide
theorem sourceRowRotation4_2_0_5 : rotatedStateRow2 sourceState4_0_5 = stateRow4_2_0_5 := by decide
theorem sourceRowRotation4_2_0_6 : rotatedStateRow2 sourceState4_0_6 = stateRow4_2_0_6 := by decide
theorem sourceRowRotation4_2_0_7 : rotatedStateRow2 sourceState4_0_7 = stateRow4_2_0_7 := by decide
theorem sourceRowRotation4_2_0_8 : rotatedStateRow2 sourceState4_0_8 = stateRow4_2_0_8 := by decide
theorem sourceRowRotation4_2_0_9 : rotatedStateRow2 sourceState4_0_9 = stateRow4_2_0_9 := by decide
theorem sourceRowRotation4_2_0_10 : rotatedStateRow2 sourceState4_0_10 = stateRow4_2_0_10 := by decide
theorem sourceRowRotation4_2_0_11 : rotatedStateRow2 sourceState4_0_11 = stateRow4_2_0_11 := by decide
theorem initial4_2_0 : (source4_0).map (rotatePatch 2 (hexRegion 4)) = rows0_4_2_0.map Verdict.patch := by
  rw [sourceStates4_0, sourceStateSplit4_0, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation4_2_0_0, sourceRowRotation4_2_0_1, sourceRowRotation4_2_0_2, sourceRowRotation4_2_0_3, sourceRowRotation4_2_0_4, sourceRowRotation4_2_0_5, sourceRowRotation4_2_0_6, sourceRowRotation4_2_0_7, sourceRowRotation4_2_0_8, sourceRowRotation4_2_0_9, sourceRowRotation4_2_0_10, sourceRowRotation4_2_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
