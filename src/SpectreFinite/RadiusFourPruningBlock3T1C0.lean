module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock3T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_3_1_0 : List (RowVerdict 6) := [.keep stateRow3_1_0_0, .keep stateRow3_1_0_1, .keep stateRow3_1_0_2]
def rows0_3_1_0 : List (Verdict 6) := indexedRows0_3_1_0.map (materialize literalDomain)
theorem check0_3_1_0 : checkRows direction samples0 trees0 rows0_3_1_0 = true := by
  rw [rows0_3_1_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_3_1_0]
  decide
theorem final_eq3_1_0 : final3_1_0 = rows0_3_1_0.filterMap Verdict.kept := by rfl
theorem sourceRowRotation3_1_0_0 : rotatedStateRow1 sourceState3_0_0 = stateRow3_1_0_0 := by decide
theorem sourceRowRotation3_1_0_1 : rotatedStateRow1 sourceState3_0_1 = stateRow3_1_0_1 := by decide
theorem sourceRowRotation3_1_0_2 : rotatedStateRow1 sourceState3_0_2 = stateRow3_1_0_2 := by decide
theorem initial3_1_0 : (source3_0).map (rotatePatch 1 (hexRegion 4)) = rows0_3_1_0.map Verdict.patch := by
  rw [sourceStates3_0, sourceStateSplit3_0, rotateCanonical_map1]
  simp only [List.map_cons, List.map_nil, sourceRowRotation3_1_0_0, sourceRowRotation3_1_0_1, sourceRowRotation3_1_0_2] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
