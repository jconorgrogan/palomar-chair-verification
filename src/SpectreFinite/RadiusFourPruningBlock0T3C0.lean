module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock0T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_0_3_0 : List (RowVerdict 6) := [.keep stateRow0_3_0_0, .keep stateRow0_3_0_1, .keep stateRow0_3_0_2, .keep stateRow0_3_0_3, .keep stateRow0_3_0_4, .keep stateRow0_3_0_5, .keep stateRow0_3_0_6, .keep stateRow0_3_0_7, .keep stateRow0_3_0_8, .keep stateRow0_3_0_9, .keep stateRow0_3_0_10, .keep stateRow0_3_0_11]
def rows0_0_3_0 : List (Verdict 6) := indexedRows0_0_3_0.map (materialize literalDomain)
theorem check0_0_3_0 : checkRows direction samples0 trees0 rows0_0_3_0 = true := by
  rw [rows0_0_3_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_3_0]
  decide
theorem final_eq0_3_0 : final0_3_0 = rows0_0_3_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation0_3_0_0 : rotatedStateRow3 sourceState0_0_0 = stateRow0_3_0_0 := by decide
theorem sourceRowRotation0_3_0_1 : rotatedStateRow3 sourceState0_0_1 = stateRow0_3_0_1 := by decide
theorem sourceRowRotation0_3_0_2 : rotatedStateRow3 sourceState0_0_2 = stateRow0_3_0_2 := by decide
theorem sourceRowRotation0_3_0_3 : rotatedStateRow3 sourceState0_0_3 = stateRow0_3_0_3 := by decide
theorem sourceRowRotation0_3_0_4 : rotatedStateRow3 sourceState0_0_4 = stateRow0_3_0_4 := by decide
theorem sourceRowRotation0_3_0_5 : rotatedStateRow3 sourceState0_0_5 = stateRow0_3_0_5 := by decide
theorem sourceRowRotation0_3_0_6 : rotatedStateRow3 sourceState0_0_6 = stateRow0_3_0_6 := by decide
theorem sourceRowRotation0_3_0_7 : rotatedStateRow3 sourceState0_0_7 = stateRow0_3_0_7 := by decide
theorem sourceRowRotation0_3_0_8 : rotatedStateRow3 sourceState0_0_8 = stateRow0_3_0_8 := by decide
theorem sourceRowRotation0_3_0_9 : rotatedStateRow3 sourceState0_0_9 = stateRow0_3_0_9 := by decide
theorem sourceRowRotation0_3_0_10 : rotatedStateRow3 sourceState0_0_10 = stateRow0_3_0_10 := by decide
theorem sourceRowRotation0_3_0_11 : rotatedStateRow3 sourceState0_0_11 = stateRow0_3_0_11 := by decide
theorem initial0_3_0 : (source0_0).map (rotatePatch 3 (hexRegion 4)) = rows0_0_3_0.map Verdict.patch := by
  rw [sourceStates0_0, sourceStateSplit0_0, rotateCanonical_map3]
  simp only [List.map_cons, List.map_nil, sourceRowRotation0_3_0_0, sourceRowRotation0_3_0_1, sourceRowRotation0_3_0_2, sourceRowRotation0_3_0_3, sourceRowRotation0_3_0_4, sourceRowRotation0_3_0_5, sourceRowRotation0_3_0_6, sourceRowRotation0_3_0_7, sourceRowRotation0_3_0_8, sourceRowRotation0_3_0_9, sourceRowRotation0_3_0_10, sourceRowRotation0_3_0_11] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
