module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock5T0C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_5_0_2 : List (RowVerdict 6) := [.keep stateRow5_0_2_0, .keep stateRow5_0_2_1, .keep stateRow5_0_2_2, .keep stateRow5_0_2_3, .keep stateRow5_0_2_4, .keep stateRow5_0_2_5]
def rows0_5_0_2 : List (Verdict 6) := indexedRows0_5_0_2.map (materialize literalDomain)
theorem check0_5_0_2 : checkRows direction samples0 trees0 rows0_5_0_2 = true := by
  rw [rows0_5_0_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_5_0_2]
  decide
theorem final_eq5_0_2 : final5_0_2 = rows0_5_0_2.filterMap Verdict.kept := by rfl
theorem sourceRowRotation5_0_2_0 : rotatedStateRow0 sourceState5_2_0 = stateRow5_0_2_0 := by decide
theorem sourceRowRotation5_0_2_1 : rotatedStateRow0 sourceState5_2_1 = stateRow5_0_2_1 := by decide
theorem sourceRowRotation5_0_2_2 : rotatedStateRow0 sourceState5_2_2 = stateRow5_0_2_2 := by decide
theorem sourceRowRotation5_0_2_3 : rotatedStateRow0 sourceState5_2_3 = stateRow5_0_2_3 := by decide
theorem sourceRowRotation5_0_2_4 : rotatedStateRow0 sourceState5_2_4 = stateRow5_0_2_4 := by decide
theorem sourceRowRotation5_0_2_5 : rotatedStateRow0 sourceState5_2_5 = stateRow5_0_2_5 := by decide
theorem initial5_0_2 : (source5_2).map (rotatePatch 0 (hexRegion 4)) = rows0_5_0_2.map Verdict.patch := by
  rw [sourceStates5_2, sourceStateSplit5_2, rotateCanonical_map0]
  simp only [List.map_cons, List.map_nil, sourceRowRotation5_0_2_0, sourceRowRotation5_0_2_1, sourceRowRotation5_0_2_2, sourceRowRotation5_0_2_3, sourceRowRotation5_0_2_4, sourceRowRotation5_0_2_5] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
