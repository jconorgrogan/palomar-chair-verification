module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock4T2C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_4_2_2 : List (RowVerdict 6) := [.keep stateRow4_2_2_0, .keep stateRow4_2_2_1, .keep stateRow4_2_2_2, .keep stateRow4_2_2_3]
def rows0_4_2_2 : List (Verdict 6) := indexedRows0_4_2_2.map (materialize literalDomain)
theorem check0_4_2_2 : checkRows direction samples0 trees0 rows0_4_2_2 = true := by
  rw [rows0_4_2_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_4_2_2]
  decide
theorem final_eq4_2_2 : final4_2_2 = rows0_4_2_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation4_2_2_0 : rotatedStateRow2 sourceState4_2_0 = stateRow4_2_2_0 := by decide
theorem sourceRowRotation4_2_2_1 : rotatedStateRow2 sourceState4_2_1 = stateRow4_2_2_1 := by decide
theorem sourceRowRotation4_2_2_2 : rotatedStateRow2 sourceState4_2_2 = stateRow4_2_2_2 := by decide
theorem sourceRowRotation4_2_2_3 : rotatedStateRow2 sourceState4_2_3 = stateRow4_2_2_3 := by decide
theorem initial4_2_2 : (source4_2).map (rotatePatch 2 (hexRegion 4)) = rows0_4_2_2.map Verdict.patch := by
  rw [sourceStates4_2, sourceStateSplit4_2, rotateCanonical_map2]
  simp only [List.map_cons, List.map_nil, sourceRowRotation4_2_2_0, sourceRowRotation4_2_2_1, sourceRowRotation4_2_2_2, sourceRowRotation4_2_2_3] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
